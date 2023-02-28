#![feature(path_file_prefix)]
use byteorder::{ByteOrder, LittleEndian, WriteBytesExt};
use clap::{Parser, Subcommand};
use fhe::bfv::{Ciphertext, Plaintext};
use fhe_math::zq::Modulus;
use itertools::Itertools;
use omr::{
    client::*,
    fhe::bfv::{BfvParametersBuilder, Encoding, SecretKey},
    fhe_traits::*,
    pvw::{PvwCiphertext, PvwParameters, PvwPublicKey, PvwSecretKey},
    server::*,
    utils::*,
    DEGREE, GAMMA, K, M, MODULI_OMR, MODULI_OMR_PT, M_ROW_SPAN, OMR_S_SIZES, SET_SIZE,
};
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaChaRng;
use rayon::{
    prelude::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSlice,
};
use std::{
    collections::{HashMap, HashSet},
    fmt::format,
    io::Write,
    path::{Path, PathBuf},
    str::FromStr,
    sync::Arc,
};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    StartOMR {
        #[arg(short, long)]
        detection_key: PathBuf,

        #[arg(short, long)]
        clues: PathBuf,

        #[arg(short, long)]
        output_dir: PathBuf,
    },
    CreateDigest1 {
        #[arg(short, long)]
        messages: std::path::PathBuf,

        #[arg(short, long)]
        pertinency_cts: std::path::PathBuf,

        #[arg(short, long)]
        output_dir: PathBuf,

        #[arg(short, long)]
        first_tx: usize,

        #[arg(short, long)]
        last_tx: usize,
    },
    CreateDigest2 {
        #[arg(short, long)]
        messages: std::path::PathBuf,

        #[arg(short, long)]
        pertinency_cts: std::path::PathBuf,

        #[arg(short, long)]
        output_dir: PathBuf,

        #[arg(short, long)]
        first_tx: usize,

        #[arg(short, long)]
        last_tx: usize,

        #[arg(short, long)]
        k: usize,
    },
}

fn start_omr(detection_key: PathBuf, clues: PathBuf, output_dir: PathBuf) {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );

    let fake_bfv_sk = SecretKey::random(&bfv_params, &mut rng);

    let detection_key = std::fs::read(detection_key).expect("Detection key read failed");
    let detection_key = deserialize_detection_key(&bfv_params, &detection_key);

    // load bfv parameters
    let pvw_params = Arc::new(PvwParameters::default());
    let fake_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let fake_pk = fake_sk.public_key(&mut rng);
    let fake_clue = fake_pk.encrypt(&[0, 0, 0, 0], &mut rng);

    let multiplicators = map_rlks_to_multiplicators(&detection_key.rlk_keys);

    std::fs::create_dir_all(&output_dir).expect("Failed to setup output directory");

    std::fs::read_dir(clues)
        .unwrap()
        .collect_vec()
        .par_chunks(1 << 15)
        .enumerate()
        .for_each(|(batch_index, files)| {
            println!("Process clue batch: {batch_index}");

            let file_paths = files
                .iter()
                .filter(|f| f.is_ok())
                .map(|f| f.as_ref().unwrap().path())
                .collect_vec();

            let clues = file_paths
                .iter()
                .map(|path| match std::fs::read(path) {
                    Ok(clue) => match PvwCiphertext::from_bytes(&clue, &pvw_params) {
                        Some(clue) => clue,
                        None => {
                            eprintln!("Incorrect encoding of clue at: {path:?}");
                            fake_clue.clone()
                        }
                    },
                    Err(e) => {
                        eprintln!("Failed to read clue at: {path:?} due to error: {e:?}",);
                        fake_clue.clone()
                    }
                })
                .collect_vec();

            println!("Decrypt_pvw of batch: {batch_index}");
            let decrypted_clues = decrypt_pvw(
                &bfv_params,
                &pvw_params,
                detection_key.pvw_sk_cts.to_vec(),
                &detection_key.ek1,
                &clues,
                &fake_bfv_sk,
            );

            println!("Range_fn of batch: {batch_index}");
            let mut ranged_decrypted_clues = decrypted_clues
                .iter()
                .map(|ct| range_fn(&bfv_params, ct, &multiplicators, 1, &fake_bfv_sk))
                .collect_vec();

            println!("Mul_many of batch: {batch_index}");
            mul_many(&mut ranged_decrypted_clues, &multiplicators, 10);

            let left_rot_key = &detection_key.ek2;
            let inner_sum_key = &detection_key.ek3;
            let mut pertinency_ct = ranged_decrypted_clues[0].clone();
            let mut select = vec![0u64; bfv_params.degree()];
            select[0] = 1;
            let select_pt =
                Plaintext::try_encode(&select, Encoding::simd_at_level(11), &bfv_params).unwrap();

            file_paths.iter().enumerate().for_each(|(index, path)| {
                // println!("Processing inner sum for {index}");
                if index != 0 {
                    if index == bfv_params.degree() / 2 {
                        pertinency_ct = left_rot_key.rotates_rows(&pertinency_ct).unwrap();
                    }
                    pertinency_ct = left_rot_key.rotates_columns_by(&pertinency_ct, 1).unwrap()
                }
                let mut p_ct = &pertinency_ct * &select_pt;
                p_ct.mod_switch_to_next_level();
                p_ct.mod_switch_to_next_level();
                let p_ct = inner_sum_key.computes_inner_sum(&p_ct).unwrap();

                // save pertinency ciphertext
                let name = path.file_name().unwrap().to_str().unwrap();
                let mut file_path = output_dir.clone();
                file_path.push(format!("{name}"));

                match std::fs::File::create(file_path.clone())
                    .and_then(|mut f| f.write_all(p_ct.to_bytes().as_slice()))
                {
                    Ok(_) => {
                        eprintln!("Pertinency Ct write to {file_path:?} success");
                    }
                    Err(e) => {
                        eprintln!("Pertinency Ct write to {file_path:?} failed with error: {e}");
                    }
                }
            });
        });
}

fn create_digest2(
    messages: PathBuf,
    pertinency_cts: PathBuf,
    mut output_dir: PathBuf,
    first_tx: usize,
    last_tx: usize,
    max_txs: usize,
) {
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );

    let mut tx_hashes = get_mapping(messages.clone(), first_tx, last_tx);
    // let tx_hashes = { (0usize..(1 << 15)).into_iter().collect_vec() };

    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);

    let msg_ct_count = ((max_txs as f64) / 64.0).ceil() as usize;
    let max_txs = msg_ct_count * 64;
    let (k, m, gamma) = gen_srlc_params(max_txs);
    let message_size = 512;
    let bucket_row_span = 256;
    let (assigned_buckets, assigned_weights) =
        assign_buckets(m, gamma, MODULI_OMR_PT[0], tx_hashes.len(), &mut rng);
    let q_mod = Modulus::new(MODULI_OMR_PT[0]).unwrap();

    let mut msg_cts = vec![Ciphertext::zero(&bfv_params); msg_ct_count];

    // let pertinency_cts_path = PathBuf::from_str("generated/o1").unwrap();
    // let messages = PathBuf::from_str("generated/messages").unwrap();
    tx_hashes
        .iter()
        .enumerate()
        .for_each(|(index, (tx_file_name, tx_hash))| {
            let mut p_ct_path = pertinency_cts.clone();
            p_ct_path.push(format!("{tx_hash}"));
            if let Ok(p_ct) = std::fs::read(p_ct_path) {
                if let Ok(mut p_ct) = Ciphertext::from_bytes(&p_ct, &bfv_params) {
                    let tx = {
                        let mut m_path = messages.clone();
                        m_path.push(format!("{tx_file_name}"));
                        let mut tx = std::fs::read(m_path)
                            .unwrap()
                            .chunks(2)
                            .map(|two_bytes| {
                                if two_bytes.len() == 1 {
                                    (two_bytes[0] as u64)
                                } else {
                                    (two_bytes[0] as u64) + ((two_bytes[1] as u64) << 8)
                                }
                            })
                            .collect_vec();

                        // fill in empty bytes till len isn't equal to 512/2
                        while tx.len() != 256 {
                            tx.push(0);
                        }
                        tx
                    };

                    // add message
                    let mut m_pts = vec![vec![0u64; bfv_params.degree()]; msg_ct_count];
                    for i in 0..gamma {
                        let bucket = assigned_buckets[index][i];
                        let weight = assigned_weights[index][i];

                        let row = bucket_row_span * bucket;
                        for j in row..(row + bucket_row_span) {
                            m_pts[j / bfv_params.degree()][j % bfv_params.degree()] =
                                q_mod.mul(tx[j - row], weight);
                        }
                    }
                    let m_pts = m_pts.iter().map(|pt| {
                        Plaintext::try_encode(pt, Encoding::simd_at_level(13), &bfv_params).unwrap()
                    });

                    msg_cts
                        .iter_mut()
                        .zip(m_pts)
                        .enumerate()
                        .for_each(|(i, (c, pt))| {
                            if i == msg_ct_count - 1 {
                                p_ct *= &pt;
                                *c += &p_ct;
                            } else {
                                *c += &(&p_ct * &pt);
                            }
                        });
                } else {
                    eprintln!("Skipping tx hash: {tx_hash} due malformed p_ct file");
                }
            } else {
                eprintln!("Skipping tx hash: {tx_hash} due to missing p_ct file");
            }
        });

    msg_cts.iter_mut().for_each(|ct| {
        ct.mod_switch_to_last_level();
    });

    let digest = Digest2 { seed, cts: msg_cts };

    std::fs::create_dir_all(&output_dir).expect("Output directory should exist");
    output_dir.push(format!("digest2-{first_tx}-{last_tx}"));
    let mut file = std::fs::File::create(&output_dir)
        .expect("File creation for storing digest one should succeed");
    file.write_all(&serialize_digest2(&digest))
        .expect("Writing digest buffer to digest file should succeed");

    println!("{}", output_dir.to_str().unwrap());
}

fn create_digest1(
    messages: PathBuf,
    pertinency_cts: PathBuf,
    mut output_dir: PathBuf,
    first_tx: usize,
    last_tx: usize,
) {
    let tx_hashes = get_mapping(messages, first_tx, last_tx);
    // let tx_hashes = { (0usize..(1 << 15)).into_iter().collect_vec() };

    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );

    let mut pv_ct = Ciphertext::zero(&bfv_params);

    // let pertinency_cts_path = PathBuf::from_str("generated/o1").unwrap();

    // read p_ct and build pv_ct
    tx_hashes
        .iter()
        .enumerate()
        .for_each(|(index, (_, tx_hash))| {
            let mut p_ct_path = pertinency_cts.clone();
            p_ct_path.push(format!("{tx_hash}"));
            // let now = std::time::Instant::now();
            if let Ok(p_ct) = std::fs::read(p_ct_path) {
                if let Ok(mut p_ct) = Ciphertext::from_bytes(&p_ct, &bfv_params) {
                    // add pertinency bit
                    let mut pt = vec![0u64; bfv_params.degree()];
                    pt[index / 16] = 1u64 << (index % 16);
                    let pt = Plaintext::try_encode(&pt, Encoding::simd_at_level(13), &bfv_params)
                        .unwrap();
                    p_ct *= &pt;
                    pv_ct += &p_ct;
                } else {
                    eprintln!("Skipping tx hash: {tx_hash} due malformed p_ct file");
                }
            } else {
                eprintln!("Skipping tx hash: {tx_hash} due to missing p_ct file");
            }
            // println!("time: {:?}", now.elapsed());
        });

    pv_ct.mod_switch_to_last_level();

    let pv_ct_byes = pv_ct.to_bytes();

    // {
    //     let key: Vec<i64> =
    //         bincode::deserialize(&std::fs::read("generated/keys/bfvPrivKey").unwrap()).unwrap();
    //     let sk = SecretKey::new(key, &bfv_params);
    //     let values = pv_decompress(
    //         &Vec::<u64>::try_decode(&sk.try_decrypt(&pv_ct).unwrap(), Encoding::simd()).unwrap(),
    //         16,
    //     );
    //     let mut detected_indices = vec![];
    //     values.iter().enumerate().for_each(|(index, v)| {
    //         if *v == 1 {
    //             detected_indices.push(index);
    //         }
    //     });
    //     dbg!(detected_indices);
    // }

    std::fs::create_dir_all(&output_dir).expect("Output directory should exist");
    output_dir.push(format!("digest1-{first_tx}-{last_tx}"));
    let mut file = std::fs::File::create(&output_dir)
        .expect("File creation for storing digest one should succeed");
    file.write_all(&pv_ct_byes)
        .expect("Writing digest buffer to digest file should succeed");

    println!("{}", output_dir.to_str().unwrap());
}

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::StartOMR {
            detection_key,
            clues,
            output_dir,
        } => start_omr(detection_key, clues, output_dir),
        Command::CreateDigest1 {
            messages,
            pertinency_cts,
            output_dir,
            first_tx,
            last_tx,
        } => {
            create_digest1(messages, pertinency_cts, output_dir, first_tx, last_tx);
        }
        Command::CreateDigest2 {
            messages,
            pertinency_cts,
            output_dir,
            first_tx,
            last_tx,
            k: max_txs,
        } => create_digest2(
            messages,
            pertinency_cts,
            output_dir,
            first_tx,
            last_tx,
            max_txs,
        ),
    }
}
