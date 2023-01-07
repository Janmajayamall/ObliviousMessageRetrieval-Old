pub mod client;
pub mod pvw;
pub mod server;
pub mod utils;
pub use fhe;
pub use fhe_traits;

use fhe::bfv::{BfvParametersBuilder, SecretKey};
use pvw::PvwCiphertext;
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaChaRng;
use server::DetectionKey;
use std::sync::Arc;

use crate::{
    server::{phase1, phase2, MessageDigest},
    utils::{assign_buckets, serialize_message_digest},
};

pub const MODULI_OMR: &[u64; 15] = &[
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
pub const DEGREE: usize = 1 << 11;
pub const MODULI_OMR_PT: &[u64; 1] = &[65537];
pub const SET_SIZE: usize = 1 << 14;
pub const VARIANCE: usize = 10;

// SRLC params
pub const K: usize = 50;
pub const M: usize = 100;
pub const DATA_SIZE: usize = 256;
// m_row_span = 256 bytes / 2 bytes
// since each row can store upto 2 bytes
// of data.
pub const M_ROW_SPAN: usize = 128;
pub const GAMMA: usize = 5;
// no of cts required to accomodate all
// rows of buckets; = CEIL((M * M_ROW_SPACE) / DEGREE)
pub const CT_SPAN_COUNT: usize = 7;

pub fn server_process(
    clues: &[PvwCiphertext],
    messages: &[Vec<u64>],
    detection_key: &DetectionKey,
) -> Vec<u8> {
    debug_assert!(clues.len() == messages.len());

    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1) as usize;
    let pvw_params = Arc::new(pvw::PvwParameters::default());

    // FIXME: REMOVE THIS
    let mut rng = thread_rng();
    let dummy_bfv_sk = SecretKey::random(&bfv_params, &mut rng);

    // phase 1
    dbg!("Phase 1");
    let mut pertinency_cts = phase1(
        &bfv_params,
        &pvw_params,
        &detection_key.pvw_sk_cts,
        &detection_key.ek1,
        &detection_key.rlk_keys,
        clues,
        &dummy_bfv_sk,
    );
    dbg!("Phase 1 end");
    // seeded rng for buckets
    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);
    let (assigned_buckets, assigned_weights) =
        assign_buckets(M, GAMMA, MODULI_OMR_PT[0], SET_SIZE, &mut rng);

    dbg!("Phase 2");
    let (pv_ct, msg_cts) = phase2(
        &assigned_buckets,
        &assigned_weights,
        &bfv_params,
        &detection_key.ek2,
        &detection_key.ek3,
        &mut pertinency_cts,
        messages,
        32,
        DEGREE,
        10,
        SET_SIZE,
        GAMMA,
        CT_SPAN_COUNT,
        M,
        M_ROW_SPAN,
        &dummy_bfv_sk,
    );
    dbg!("Phase 2 end");

    let message_digest = MessageDigest {
        seed,
        pv: pv_ct,
        msgs: msg_cts,
    };

    serialize_message_digest(&message_digest)
}

#[cfg(test)]
mod tests {
    use crate::{
        pvw::{PvwParameters, PvwSecretKey},
        utils::{gen_clues, gen_detection_key, gen_paylods, gen_pertinent_indices},
    };

    use super::*;

    #[test]
    fn server_process_test() {
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

        // CLIENT SETUP //
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
        let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
        let pvw_pk = pvw_sk.public_key(&mut rng);
        let d_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);

        // gen clues

        let mut pertinent_indices = gen_pertinent_indices(50, SET_SIZE);
        pertinent_indices.sort();
        println!("Pertinent indices: {:?}", pertinent_indices);

        let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, SET_SIZE);
        let payloads = gen_paylods(SET_SIZE);
        println!("Clues generated");

        server_process(&clues, &payloads, &d_key);
    }
}
