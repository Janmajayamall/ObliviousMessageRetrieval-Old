use clap::{Parser, Subcommand};
use itertools::Itertools;
use omr::{
    client::*,
    fhe::bfv::{BfvParametersBuilder, Encoding, SecretKey},
    fhe_traits::*,
    pvw::{PvwParameters, PvwPublicKey, PvwSecretKey},
    server::*,
    utils::*,
    DEGREE, GAMMA, K, M, MODULI_OMR, MODULI_OMR_PT, M_ROW_SPAN, OMR_S_SIZES, SET_SIZE,
};
use rand::{thread_rng, SeedableRng};
use rand_chacha::ChaChaRng;
use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

#[derive(Parser)]
struct Cli {
    #[command(subcommand)]
    run: Run,
}

#[derive(Subcommand)]
enum Run {
    Phase1 {
        #[arg(short, long)]
        detection_key: PathBuf,
        #[arg(short, long)]
        mappings: PathBuf,
        #[arg(short, long)]
        output_dir: PathBuf,
    },
    Phase2 {
        #[arg(short, long)]
        start_range: usize,
        #[arg(short, long)]
        end_range: usize,
        #[arg(short, long)]
        detection_key: PathBuf,
        #[arg(short, long)]
        output_dir: PathBuf,
    },
}

fn run() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1) as usize;
    let pvw_params = Arc::new(PvwParameters::default());

    // CLIENT SETUP //
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    // pvw secret key encrypted under bfv
    println!("Generating client keys");
    let d_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
    let multiplicators = map_rlks_to_multiplicators(&d_key.rlk_keys);

    let mut pertinent_indices = gen_pertinent_indices(50, SET_SIZE);
    pertinent_indices.sort();
    println!("Pertinent indices: {:?}", pertinent_indices);
    let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, SET_SIZE);
    let payloads = gen_paylods(SET_SIZE);

    let mut pertinent_payloads = vec![];
    (0..SET_SIZE)
        .zip(payloads.iter())
        .for_each(|(index, load)| {
            if pertinent_indices.contains(&index) {
                pertinent_payloads.push(load.clone());
            }
        });

    // SERVER SIDE //
    println!("Server: Starting OMR...");
    let now = std::time::Instant::now();
    let message_digest = server_process(&bfv_params, &clues, &payloads, &d_key, &multiplicators);
    println!("Total server time: {:?}", now.elapsed());

    // CLIENT SIDE //
    println!("Client: Processing digest");
    let now = std::time::Instant::now();

    let pt = bfv_sk.try_decrypt(&message_digest.pv).unwrap();
    let pv_values = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
    let pv = pv_decompress(&pv_values, pt_bits);
    // {
    //     let mut res_indices = vec![];
    //     pv.iter().enumerate().for_each(|(index, bit)| {
    //         if *bit == 1 {
    //             res_indices.push(index);
    //         }
    //     });
    //     pertinent_indices.sort();
    //     assert_eq!(pertinent_indices, res_indices);
    //     // println!("Expected indices {:?}", pertinent_indices);
    //     // println!("Res indices      {:?}", res_indices);
    //     // assert!(false);
    // }
    let mut rng = ChaChaRng::from_seed(message_digest.seed);
    let (assigned_buckets, assigned_weights) =
        assign_buckets(M, GAMMA, MODULI_OMR_PT[0], SET_SIZE, &mut rng);
    let lhs = construct_lhs(
        &pv,
        assigned_buckets,
        assigned_weights,
        M,
        K,
        GAMMA,
        SET_SIZE,
    );

    let m_rows = message_digest
        .msgs
        .iter()
        .flat_map(|m| {
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(m).unwrap(), Encoding::simd()).unwrap()
        })
        .collect_vec();
    let rhs = construct_rhs(&m_rows, M, M_ROW_SPAN, MODULI_OMR_PT[0]);
    let res_payloads = solve_equations(lhs, rhs, MODULI_OMR_PT[0]);
    println!("Total client time: {:?}", now.elapsed());

    assert_eq!(pertinent_payloads, res_payloads);
}

fn main() {
    let cli = Cli::parse();
    match cli.run {
        Run::Phase1 {
            detection_key,
            mappings,
            output_dir,
        } => {}
        Run::Phase2 {
            start_range,
            end_range,
            detection_key,
            output_dir,
        } => {}
    }
    // let val = std::env::args().nth(1).map(|v| {
    //     v.as_str()
    //         .parse::<usize>()
    //         .expect("Choose 1 to run demo. Choose 2 to display detection key size")
    // });

    // match val {
    //     Some(1) => run(),
    //     Some(2) => calculate_detection_key_size(),
    //     _ => {
    //         println!("Choose 1 to run demo. Choose 2 to display detection key size")
    //     }
    // }
}
