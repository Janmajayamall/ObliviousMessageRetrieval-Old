use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use client::gen_pvw_sk_cts;
use fhe::bfv::{
    self, BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, GaloisKey, Multiplicator,
    Plaintext, RelinearizationKey, SecretKey,
};
use fhe_math::rq::traits::TryConvertFrom;
use fhe_math::rq::Representation;
use fhe_math::{
    rq::{Context, Poly},
    zq::Modulus,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use fhe_util::{div_ceil, ilog2, sample_vec_cbd};
use itertools::Itertools;
use rand::{distributions::Uniform, prelude::Distribution, thread_rng};
use rand::{Rng, RngCore};
use std::collections::HashMap;
use std::sync::Arc;
use std::vec;

mod client;
mod pvw;
mod server;
mod utils;

use pvw::{PVWCiphertext, PVWParameters, PVWSecretKey};
use server::{decrypt_pvw, powers_of_x, pv_compress, pv_weights, range_fn};

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
const DEGREE: usize = 32768;
const MODULI_OMR_PT: &[u64; 1] = &[65537];

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
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

    let pvw_params = Arc::new(PVWParameters {
        n: 450,
        m: 100,
        ell: 4,
        variance: 2,
        q: 65537,
    });
    let pvw_sk = PVWSecretKey::gen_sk(&pvw_params);
    let pvw_pk = pvw_sk.public_key();

    // gen clues
    let N = DEGREE;
    let tmp = Uniform::new(0, N);
    let mut pertinent_indices = vec![];
    while pertinent_indices.len() != 50 {
        let v = tmp.sample(&mut rng);
        if !pertinent_indices.contains(&v) {
            pertinent_indices.push(v);
        }
    }
    pertinent_indices.sort();
    println!("Pertinent indices {:?}", pertinent_indices);

    dbg!("Generating clues");
    let clues = (0..N)
        .map(|index| {
            if pertinent_indices.contains(&index) {
                pvw_pk.encrypt(vec![1, 1, 1, 1])
            } else {
                let tmp_sk = PVWSecretKey::gen_sk(&pvw_params);
                let tmp_pk = tmp_sk.public_key();
                pvw_pk.encrypt(vec![0, 0, 0, 0])
            }
        })
        .collect_vec();

    let ct_pvw_sk = gen_pvw_sk_cts(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk);
    let top_rot_key = GaloisKey::new(&bfv_sk, 3, 0, 0, &mut rng).unwrap();

    // run detection
    dbg!("Running decrypt_pvw");
    let mut decrypted_clues = decrypt_pvw(&bfv_params, &pvw_params, ct_pvw_sk, top_rot_key, clues);

    for _ in 0..3 {}

    // relinearization keys at all levels
    dbg!("Generating rlk keys");
    let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
    for i in 0..bfv_params.max_level() {
        let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
        rlk_keys.insert(i, rlk);
    }

    unsafe {
        dbg!("Noise:", bfv_sk.measure_noise(&decrypted_clues[0]));
    }

    dbg!("Evaluating range_fn");
    // let range_res = range_fn(&bfv_params, &decrypted_clues[0], &rlk_keys);
    let range_res_pt = bfv_sk.try_decrypt(&decrypted_clues[0]).unwrap();
    let range_res = Vec::<u64>::try_decode(&range_res_pt, Encoding::simd()).unwrap();
    let mut res_indices = vec![];
    range_res.iter().enumerate().for_each(|(index, bit)| {
        if *bit >= 32768 {
            res_indices.push(index);
        }
    });

    println!("{:?}", pertinent_indices);
    println!("{:?}", res_indices);

    // assert!(pertinent_indices == res_indices);
}

fn main() {
    run();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run() {
        run();
    }
}
