use itertools::Itertools;
use omr::{
    client::*,
    fhe::bfv::{BfvParametersBuilder, Encoding, SecretKey},
    fhe_traits::*,
    pvw::{PvwCiphertext, PvwParameters, PvwPublicKey, PvwSecretKey},
    server::*,
    utils::*,
};
use rand::thread_rng;
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use std::vec;
use std::{io::Write, sync::Arc};

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
    let pvw_params = Arc::new(PvwParameters::default());
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
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
    let pvw_params = Arc::new(PvwParameters::default());

    // CLIENT SETUP //
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    // pvw secret key encrypted under bfv
    println!("Generating client keys");
    let d_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
    let d_key_serialized = serialize_detection_key(&d_key);

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
    let message_digest_bytes = server_process(&clues, &payloads, &d_key_serialized);
    println!("Server time: {:?}", now.elapsed());

    let message_digest = deserialize_message_digest(&bfv_params, &message_digest_bytes);

    // CLIENT SIDE //
    println!("Client: Processing digest");
    let now = std::time::Instant::now();

    let pt = bfv_sk.try_decrypt(&message_digest.pv).unwrap();
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
