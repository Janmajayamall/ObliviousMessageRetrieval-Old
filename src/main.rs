use client::gen_pvw_sk_cts;
use fhe::bfv::{BfvParametersBuilder, Encoding, EvaluationKeyBuilder, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, Serialize};
use itertools::Itertools;
use omr::utils::{deserialize_detection_key, gen_detection_key, serialize_detection_key};
use protobuf::{Message, MessageDyn};
use rand::{distributions::Uniform, prelude::Distribution, thread_rng};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use std::io::Write;
use std::sync::Arc;
use std::vec;

mod client;
mod pvw;
mod server;
mod utils;

use crate::client::{construct_lhs, construct_rhs, pv_decompress};
use crate::utils::{assign_buckets, solve_equations};
use pvw::{PVWCiphertext, PVWParameters, PVWSecretKey, PublicKey};
use server::{phase1, phase2};

const MODULI_OMR: &[u64; 15] = &[
    268369921,
    549755486209,
    1152921504606584833,
    1152921504598720513,
    1152921504597016577,
    1152921504595968001,
    1152921504595640321,
    1152921504593412097,
    1152921504592822273,
    1152921504592429057,
    1152921504589938689,
    1152921504586530817,
    4293918721,
    1073479681,
    1152921504585547777,
];
const DEGREE: usize = 1 << 11;
const MODULI_OMR_PT: &[u64; 1] = &[65537];
const SET_SIZE: usize = 1 << 14;
const VARIANCE: usize = 10;

// SRLC params
const K: usize = 50;
const M: usize = 100;
const DATA_SIZE: usize = 256;
// m_row_span = 256 bytes / 2 bytes
// since each row can store upto 2 bytes
// of data.
const M_ROW_SPAN: usize = 128;
const GAMMA: usize = 5;
// no of cts required to accomodate all
// rows of buckets; = CEIL((M * M_ROW_SPACE) / DEGREE)
const CT_SPAN_COUNT: usize = 7;

pub fn gen_data(
    set_size: usize,
    pvw_params: &Arc<PVWParameters>,
    pvw_pk: &PublicKey,
) -> (Vec<PVWCiphertext>, Vec<Vec<u8>>) {
    println!("Generating clues and messages...");

    assert!(set_size > 50);
    let mut rng = thread_rng();

    let tmp = Uniform::new(0, set_size);
    let mut pertinent_indices = vec![];
    // 50 messages are pertinent
    while pertinent_indices.len() != 50 {
        let v = tmp.sample(&mut rng);
        if !pertinent_indices.contains(&v) {
            pertinent_indices.push(v);
        }
    }

    // create dir
    std::fs::create_dir_all("target/omr").unwrap();

    // store pertinent indices for later
    {
        std::fs::File::create("target/omr/pertinent-indices.bin")
            .unwrap()
            .write_all(&bincode::serialize(&pertinent_indices).unwrap())
            .unwrap();
    }

    let payload_distr = Uniform::new(0u8, u8::MAX);

    // let other = {
    //     let tmp_sk = PVWSecretKey::random(&pvw_params, &mut rng);
    //     tmp_sk.public_key(&mut rng).encrypt(&[0, 0, 0, 0], &mut rng)
    // };
    let data: (Vec<PVWCiphertext>, Vec<Vec<u8>>) = (0..set_size)
        .map(|index| {
            let clue = if pertinent_indices.contains(&index) {
                pvw_pk.encrypt(&[0, 0, 0, 0], &mut rng)
            } else {
                let tmp_sk = PVWSecretKey::random(&pvw_params, &mut rng);
                tmp_sk.public_key(&mut rng).encrypt(&[0, 0, 0, 0], &mut rng)
            };
            let payload = payload_distr
                .sample_iter(rng.clone())
                .take(256)
                .collect_vec();
            (clue, payload)

            // let clue_buff = bincode::serialize(&clue).unwrap();
            // std::fs::File::create(format!("target/omr/clue-{index}.bin"))
            //     .unwrap()
            //     .write_all(&clue_buff)
            //     .unwrap();
            // std::fs::File::create(format!("target/omr/payload-{index}.bin"))
            //     .unwrap()
            //     .write_all(&payload)
            //     .unwrap();
        })
        .unzip();
    data
}

fn calculate_detection_key_size() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let key = gen_detection_key(&bfv_params, &bfv_sk, &mut rng);
    let s = serialize_detection_key(&key);
    println!("Detection key size: {}MB", s.len() as f64 / 1000000.0)
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
    let pvw_params = Arc::new(PVWParameters::default());

    // CLIENT SETUP //
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PVWSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    // pvw secret key encrypted under bfv
    println!("Generating client keys");
    let ct_pvw_sk = gen_pvw_sk_cts(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk);

    let d_key = gen_detection_key(&bfv_params, &bfv_sk, &mut rng);
    let d_key_serialized = serialize_detection_key(&d_key);

    // Generate sample data //
    let data = gen_data(SET_SIZE, &pvw_params, &pvw_pk);

    let mut pertinent_indices: Vec<usize> = bincode::deserialize(
        &std::fs::read("target/omr/pertinent-indices.bin")
            .expect("Indices file missing! Run with -g flag."),
    )
    .unwrap();
    println!("Pertinent indices: {pertinent_indices:?}");

    // let data: (Vec<PVWCiphertext>, Vec<Vec<u64>>) = (0..SET_SIZE)
    //     .map(|index| {
    //         let clue: PVWCiphertext = bincode::deserialize(
    //             &std::fs::read(format!("target/omr/clue-{index}.bin")).expect("Clue file missing!"),
    //         )
    //         .expect("Invalid clue file!");
    //         // change payload from bytes to collection of two bytes
    //         let payload: Vec<u64> = std::fs::read(format!("target/omr/payload-{index}.bin"))
    //             .expect("Payload file missing!")
    //             .chunks(2)
    //             .map(|v| (v[0] as u64) + ((v[1] as u64) << 8))
    //             .collect();
    //         assert!(payload.len() == 128);

    //         (clue, payload)
    //     })
    //     .unzip();
    let clues = data.0;
    let payloads = data.1;
    let payloads = payloads
        .iter()
        .map(|pl| {
            pl.chunks(2)
                .map(|v| (v[0] as u64) + ((v[1] as u64) << 8))
                .collect()
        })
        .collect::<Vec<Vec<u64>>>();

    let mut pertinent_payloads = vec![];
    (0..SET_SIZE)
        .zip(payloads.iter())
        .for_each(|(index, load)| {
            if pertinent_indices.contains(&index) {
                pertinent_payloads.push(load.clone());
            }
        });

    // SERVER SIDE //
    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);

    let d_key = deserialize_detection_key(&bfv_params, &d_key_serialized);

    let (assigned_buckets, assigned_weights) =
        assign_buckets(M, GAMMA, MODULI_OMR_PT[0], SET_SIZE, &mut rng);
    println!("Server: Running phase1");
    let now = std::time::Instant::now();
    let mut pertinency_cts = phase1(
        &bfv_params,
        &pvw_params,
        &ct_pvw_sk,
        &d_key.ek1,
        &d_key.rlk_keys,
        &clues,
        &bfv_sk,
        SET_SIZE,
        DEGREE,
    );
    let phase1_time = now.elapsed();
    println!("Server: Running phase2");
    let (compressed_pv, msg_cts) = phase2(
        &assigned_buckets,
        &assigned_weights,
        &bfv_params,
        &d_key.ek2,
        &d_key.ek3,
        &mut pertinency_cts,
        &payloads,
        32,
        DEGREE,
        10,
        SET_SIZE,
        GAMMA,
        CT_SPAN_COUNT,
        M_ROW_SPAN,
        &bfv_sk,
    );
    let phase2_time = now.elapsed() - phase1_time;
    let total_time = now.elapsed();
    println!("Server: Phase1 took: {phase1_time:?}; Phase2 took: {phase2_time:?}");
    println!("Server: Total server time: {total_time:?}");

    // CLIENT SIDE //
    println!("Client: Processing digest");
    let now = std::time::Instant::now();

    let pt = bfv_sk.try_decrypt(&compressed_pv).unwrap();
    let pv_values = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
    let pv = pv_decompress(&pv_values, pt_bits);
    {
        let mut res_indices = vec![];
        pv.iter().enumerate().for_each(|(index, bit)| {
            if *bit == 1 {
                res_indices.push(index);
            }
        });
        pertinent_indices.sort();
        assert_eq!(pertinent_indices, res_indices);
        // println!("Expected indices {:?}", pertinent_indices);
        // println!("Res indices      {:?}", res_indices);
        // assert!(false);
    }
    let lhs = construct_lhs(
        &pv,
        assigned_buckets,
        assigned_weights,
        M,
        K,
        GAMMA,
        SET_SIZE,
    );
    let m_rows = msg_cts
        .iter()
        .flat_map(|m| {
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(m).unwrap(), Encoding::simd()).unwrap()
        })
        .collect_vec();
    let rhs = construct_rhs(&m_rows, M, M_ROW_SPAN, MODULI_OMR_PT[0]);
    let res_payloads = solve_equations(lhs, rhs, MODULI_OMR_PT[0]);
    println!("Client: Total client time: {:?}", now.elapsed());

    assert_eq!(pertinent_payloads, res_payloads);
}

fn main() {
    let val = std::env::args().nth(1).map(|v| {
        v.as_str()
            .parse::<usize>()
            .expect("Choose 1 to run demo. Choose 2 to display detection key size")
    });

    match val {
        Some(1) => run(),
        Some(2) => calculate_detection_key_size(),
        _ => {
            println!("Choose 1 to run demo. Choose 2 to display detection key size")
        }
    }
}
