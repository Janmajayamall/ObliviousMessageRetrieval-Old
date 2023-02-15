use itertools::Itertools;
use omr::{
    client::*,
    fhe::bfv::{BfvParametersBuilder, Encoding, SecretKey},
    fhe_traits::*,
    pvw::{PvwParameters, PvwPublicKey, PvwSecretKey},
    server::*,
    utils::*,
    DEGREE, GAMMA, K, M, MODULI_OMR, MODULI_OMR_PT, M_ROW_SPAN, SET_SIZE,
};
use rand::{thread_rng, SeedableRng};
use rand_chacha::ChaChaRng;
use std::sync::Arc;
use std::vec;

fn calculate_detection_key_size() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(1 << 15)
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
            .set_moduli_sizes(&[50, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60])
            .build()
            .unwrap(),
    );
    let pvw_params = Arc::new(PvwParameters::default());

    // CLIENT SETUP //
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    // pvw secret key encrypted under bfv
    println!("Generating client keys");
    let d_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
    let multiplicators = map_rlks_to_multiplicators(&d_key.rlk_keys);

    let mut pertinent_indices = gen_pertinent_indices(100, SET_SIZE);
    pertinent_indices.sort();
    println!("Pertinent indices: {:?}", pertinent_indices);

    let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, SET_SIZE);

    // SERVER SIDE //
    println!("Server: Starting OMR...");
    let now = std::time::Instant::now();
    let mut phase1_res = phase1(
        &bfv_params,
        &pvw_params,
        &d_key.pvw_sk_cts,
        &d_key.ek1,
        &multiplicators,
        &clues,
        &bfv_sk,
    );
    let res = phase2_omd(&mut phase1_res, &bfv_params, 11, &bfv_sk);
    println!("Total server time: {:?}", now.elapsed());

    // CLIENT SIDE //
    println!("Client: Processing digest");
    let now = std::time::Instant::now();
    let mut indices = process_digest_omd(res, &bfv_sk, &bfv_params);
    println!("Total client time: {:?}", now.elapsed());

    indices.sort();

    assert_eq!(pertinent_indices, indices);
}

fn main() {
    run();
}
