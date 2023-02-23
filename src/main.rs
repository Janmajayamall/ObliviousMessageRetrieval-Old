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
    prelude::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator},
    slice::ParallelSlice,
};
use std::{
    collections::HashSet,
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
                            println!("Incorrect encoding of clue at: {path:?}");
                            fake_clue.clone()
                        }
                    },
                    Err(e) => {
                        println!("Failed to read clue at: {path:?} due to error: {e:?}",);
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
                        println!("Pertinency Ct write to {file_path:?} success");
                    }
                    Err(e) => {
                        println!("Pertinency Ct write to {file_path:?} failed with error: {e}");
                    }
                }
            });
        });
}

fn create_digest2(
    messages: PathBuf,
    pertinency_cts: PathBuf,
    output_dir: PathBuf,
    from_tx: usize,
    last_tx: usize,
    k: usize,
) {
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli_sizes(OMR_S_SIZES)
            .build()
            .unwrap(),
    );

    let mut pv_ct = Ciphertext::zero(&bfv_params);
    let mut msg_ct = Ciphertext::zero(&bfv_params);

    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);

    let k = 50;
    let m = k * 2;
    let gamma = 5;
    let message_size = 512;
    let bucket_row_span = 256;
    let (assigned_buckets, assigned_weights) =
        assign_buckets(m, gamma, MODULI_OMR_PT[0], last_tx - from_tx, &mut rng);
    let q_mod = Modulus::new(MODULI_OMR_PT[0]).unwrap();

    (from_tx..from_tx + last_tx).into_iter().for_each(|index| {
        let mut path = pertinency_cts.clone();
        path.push(format!("{index}"));
        match std::fs::read(path) {
            Ok(p_bytes) => match Ciphertext::from_bytes(&p_bytes, &bfv_params) {
                Ok(mut pertinency_ct) => {
                    // read message
                    let mut msg_path = messages.clone();
                    msg_path.push(format!("{index}"));
                    match std::fs::read(msg_path) {
                        Ok(mut message_bytes) => {
                            // pad message bytes
                            while message_bytes.len() < message_size {
                                message_bytes.push(0u8);
                            }

                            // change to base 16
                            let message_bytes = message_bytes
                                .chunks(2)
                                .map(|two_bytes| {
                                    (two_bytes[0] as u64) + ((two_bytes[1] as u64) << 16)
                                })
                                .collect_vec();

                            // change bit in pv_ct
                            let mut pt = vec![0u64; bfv_params.degree()];
                            pt[(index - from_tx) / 16] = 1u64 << ((index - from_tx) % 16);
                            let pt = Plaintext::try_encode(
                                &pt,
                                Encoding::simd_at_level(13),
                                &bfv_params,
                            )
                            .unwrap();

                            // add to pv
                            pv_ct += &(&pertinency_ct * &pt);

                            // add to msg_ct
                            let mut m_pt = vec![0u64; bfv_params.degree()];
                            (0..gamma).into_iter().for_each(|i| {
                                let bucket = assigned_buckets[index - from_tx][i];
                                let weight = assigned_weights[index - from_tx][i];
                                let row_offset = bucket * bucket_row_span;
                                (0..bucket_row_span).into_iter().for_each(|j| {
                                    m_pt[row_offset + j] = q_mod.mul(weight, message_bytes[j]);
                                });
                            });
                            let m_pt = Plaintext::try_encode(
                                &m_pt,
                                Encoding::simd_at_level(13),
                                &bfv_params,
                            )
                            .unwrap();
                            pertinency_ct *= &m_pt;
                            msg_ct += &pertinency_ct;
                        }
                        Err(e) => {}
                    }
                }
                Err(e) => {}
            },
            Err(e) => {}
        }
    });

    pv_ct.mod_switch_to_last_level();
    msg_ct.mod_switch_to_last_level();

    let digest = MessageDigest {
        pv: pv_ct,
        msgs: vec![msg_ct],
        seed,
    };

    //TODO: serialize and store message digest.
}

/// returns tx_hash array sorted by corresponding tx_index
fn determine_mapping() -> Vec<u8> {
    todo!()
}

fn create_digest1(pertinency_cts: PathBuf, output_dir: PathBuf, first_tx: usize, last_tx: usize) {
    let tx_hashes = determine_mapping();

    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );

    let mut pv_ct = Ciphertext::zero(&bfv_params);

    let pertinency_cts_path = PathBuf::from_str("generated/outputs/pertinencyCts").unwrap();

    // read p_ct and build pv_ct
    tx_hashes.iter().enumerate().for_each(|(index, tx_hash)| {
        let mut p_ct_path = pertinency_cts_path.clone();
        if let Ok(p_ct) = std::fs::read(p_ct_path) {
            if let Ok(mut p_ct) = Ciphertext::from_bytes(&p_ct, &bfv_params) {
                // add pertinency bit
                let mut pt = vec![0u64; bfv_params.degree()];
                pt[index / 16] = 1u64 << (index % 16);
                let pt =
                    Plaintext::try_encode(&pt, Encoding::simd_at_level(13), &bfv_params).unwrap();
                p_ct *= &pt;
                pv_ct += &p_ct;
            } else {
                println!("Skipping tx hash: {tx_hash} due malformed p_ct file");
            }
        } else {
            println!("Skipping tx hash: {tx_hash} due to missing p_ct file");
        }
    });

    let pv_ct_byes = pv_ct.to_bytes();

    std::fs::create_dir_all(output_dir).expect("Output directory should exist");
    let mut file = std::fs::File::create(format!("digest1-{first_tx}-{last_tx}"))
        .expect("File creation for storing digest one should succeed");
    file.write_all(&pv_ct_byes)
        .expect("Writing digest buffer to digest file should succeed");
}

fn dir_trial() {
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli_sizes(OMR_S_SIZES)
            .build()
            .unwrap(),
    );

    let index_set: HashSet<String> = HashSet::from_iter((0..4645usize).map(|v| v.to_string()));

    let mut tx_hashes = vec![];
    let mut tx_data = vec![];
    for entry in walkdir::WalkDir::new("generated/outputs/pertinencyCts/").max_depth(1) {
        let file_name = entry.unwrap();
        let splits = file_name
            .file_name()
            .to_str()
            .unwrap()
            .to_string()
            .split('_')
            .map(|v| v.to_string())
            .collect_vec();

        if splits.len() == 1 && index_set.contains(&splits[0]) {
            tx_hashes.push(splits[0].clone());
            let tx = std::fs::read(file_name.path()).unwrap_or_else(|_| {
                panic!("Failed to read transaction at: {:?}", file_name.path())
            });
            tx_data.push(tx);
        }
    }

    let mut pv_ct = Ciphertext::zero(&bfv_params);
    let mut msg_ct = Ciphertext::zero(&bfv_params);

    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);

    let k = 50;
    let m = k * 2;
    let gamma = 5;
    let message_size = 512;
    let bucket_row_span = 256;
    let (assigned_buckets, assigned_weights) =
        assign_buckets(m, gamma, MODULI_OMR_PT[0], tx_hashes.len(), &mut rng);
    let q_mod = Modulus::new(MODULI_OMR_PT[0]).unwrap();

    let pertinency_cts_path = PathBuf::from_str("generated/outputs/pertinencyCts").unwrap();
    // read p_ct and the payloads
    tx_hashes.iter().enumerate().for_each(|(index, tx_hash)| {
        let mut p_ct_path = pertinency_cts_path.clone();
        p_ct_path.push(tx_hash);
        if let Ok(p_ct) = std::fs::read(p_ct_path) {
            if let Ok(mut p_ct) = Ciphertext::from_bytes(&p_ct, &bfv_params) {
                let tx = tx_data[index].clone();

                // add pertinency bit
                let mut pt = vec![0u64; bfv_params.degree()];
                pt[index / 16] = 1u64 << (index % 16);
                let pt =
                    Plaintext::try_encode(&pt, Encoding::simd_at_level(13), &bfv_params).unwrap();
                pv_ct += &(&p_ct * &pt);

                // add message
                let mut m_pt = vec![0u64; bfv_params.degree()];
                for i in 0..gamma {
                    let bucket = assigned_buckets[index][i];
                    let weight = assigned_weights[index][i];

                    let start_row = bucket_row_span * bucket;
                    for j in start_row..start_row + bucket_row_span {
                        // m_pt[j] = q_mod.mul(&tx[j], weight);
                    }
                }
                let m_pt =
                    Plaintext::try_encode(&m_pt, Encoding::simd_at_level(13), &bfv_params).unwrap();
                p_ct *= &m_pt;
                msg_ct += &p_ct;
            } else {
                println!("Skipping tx hash: {tx_hash} due malformed p_ct file");
            }
        } else {
            println!("Skipping tx hash: {tx_hash} due to missing p_ct file");
        }
    });
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
            pertinency_cts,
            output_dir,
            first_tx,
            last_tx,
        } => {
            println!("{first_tx}-{last_tx}");
            // let bfv_params = Arc::new(
            //     BfvParametersBuilder::new()
            //         .set_degree(DEGREE)
            //         .set_plaintext_modulus(MODULI_OMR_PT[0])
            //         .set_moduli_sizes(OMR_S_SIZES)
            //         .build()
            //         .unwrap(),
            // );
            // let mut rng = thread_rng();
            // let mut select = vec![0u64; bfv_params.degree()];
            // select[0] = 1;
            // let select_pt: Plaintext =
            //     Plaintext::try_encode(&select, Encoding::simd_at_level(11), &bfv_params).unwrap();

            // let sk = SecretKey::random(&bfv_params, &mut rng);
        }
        Command::CreateDigest2 {
            messages,
            pertinency_cts,
            output_dir,
            first_tx,
            last_tx,
            k,
        } => {
            println!("{first_tx}-{last_tx}");
            // create_digest2(messages, pertinency_cts, output_dir, from_tx, last_tx, k);
        }
    }
}
