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
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs::DirBuilder;
use std::sync::Arc;
use std::vec;

mod client;
mod pvw;
mod server;
mod utils;

use pvw::{PVWCiphertext, PVWParameters, PVWSecretKey};
use server::{decrypt_pvw, powers_of_x, pv_compress, pv_weights, range_fn};

use crate::client::{construct_lhs, construct_rhs, pv_decompress};
use crate::server::{finalise_combinations, mul_many, pv_unpack};
use crate::utils::{assign_buckets, gen_rlk_keys, gen_rot_keys, random_data, solve_equations};

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
        variance: 1.3,
        q: 65537,
    });
    let pvw_sk = PVWSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    let mut level_offset = 0;

    // in bits
    let data_size = 256 * 8;
    let payload_size = data_size / 16;

    // for SRLC
    let k = 50;
    let m = k * 2;
    let gamma = 5;

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
    // let mut pertinent_indices = vec![2, 4, 6];
    println!("Degree: {}; N: {}; Payload size: {}", DEGREE, N, data_size);
    println!("Pertinent indices {:?}", pertinent_indices);

    println!("Generating clues");
    let mut now = std::time::SystemTime::now();
    let rows: (Vec<PVWCiphertext>, Vec<Vec<u64>>) = (0..N)
        .map(|index| {
            if pertinent_indices.contains(&index) {
                (
                    pvw_pk.encrypt(&[0, 0, 0, 0], &mut rng),
                    random_data(data_size),
                )
            } else {
                let tmp_sk = PVWSecretKey::random(&pvw_params, &mut rng);
                let tmp_pk = tmp_sk.public_key(&mut rng);
                (
                    tmp_pk.encrypt(&[0, 0, 0, 0], &mut rng),
                    random_data(data_size),
                )
            }
        })
        .unzip();
    println!("Generating clues took: {:?}", now.elapsed().unwrap());

    let ct_pvw_sk = gen_pvw_sk_cts(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk);
    let top_rot_key = GaloisKey::new(&bfv_sk, 3, 0, 0, &mut rng).unwrap();

    // relinearization keys at all levels
    println!("Generating rlk keys");
    let rlk_keys = gen_rlk_keys(&bfv_params, &bfv_sk);

    // rotation keys
    let rot_keys = gen_rot_keys(&bfv_params, &bfv_sk, 10, 9);
    let inner_sum_rot_keys = gen_rot_keys(&bfv_params, &bfv_sk, 12, 11);

    println!("///////// SERVER SIDE //////////");
    let server_time = std::time::SystemTime::now();

    // run detection
    println!("Running decrypt_pvw");
    let mut decrypted_clues = decrypt_pvw(
        &bfv_params,
        &pvw_params,
        ct_pvw_sk.clone(),
        &top_rot_key,
        &rows.0,
        &bfv_sk,
    );
    // unsafe {
    //     println!(
    //         "Noise in decrypted_clues[0]: {}",
    //         bfv_sk.measure_noise(&decrypted_clues[0]).unwrap()
    //     );
    // }
    // because of decrypt
    level_offset += 1;

    println!("Evaluating range_fn for all ells");
    let mut range_res_cts = vec![];
    for i in 0..pvw_params.ell {
        now = std::time::SystemTime::now();
        let range_res = range_fn(
            &bfv_params,
            &decrypted_clues[i],
            &rlk_keys,
            &bfv_sk,
            level_offset,
            "params_850.bin",
        );
        println!(
            "Range fn for ell index {} took {:?}",
            i,
            now.elapsed().unwrap()
        );
        range_res_cts.push(range_res);
    }

    // range fn consumes additional 8 levels
    level_offset += 8; // 9

    println!("Multiplying all Range res cts to get one");
    now = std::time::SystemTime::now();
    mul_many(&mut range_res_cts, &rlk_keys, level_offset);
    println!("Multiplication took {:?}", now.elapsed().unwrap());
    // assert!(range_res_cts.len() == 1);

    // {
    //     // Checking ct encoding pv is correct (i.e. Phase 1)
    //     let pv = bfv_sk.try_decrypt(&range_res_cts[0]).unwrap();
    //     let pv = Vec::<u64>::try_decode(&pv, Encoding::simd()).unwrap();
    //     let mut res_indices = vec![];
    //     pv.iter().enumerate().for_each(|(index, bit)| {
    //         if *bit == 1 {
    //             res_indices.push(index);
    //         }
    //     });
    //     println!("Expected indices {:?}", pertinent_indices);
    //     println!("Res indices      {:?}", res_indices);
    //     assert!(false);
    // }

    // since length of range_res_cts = 4, mul_many
    // only consumes one level
    level_offset += 1; // 10

    // unsafe {
    //     println!(
    //         "Noise in ct: {}",
    //         bfv_sk.measure_noise(&range_res_cts[0]).unwrap()
    //     );
    // }

    let mut ct = range_res_cts[0].clone();
    let mut compressed_pv_ct = Ciphertext::zero(&bfv_params);

    let msg_digest_ct_span = ((m * payload_size) as f64 / (DEGREE as f64)).ceil() as usize;
    let mut rhs_ct = vec![Ciphertext::zero(&bfv_params); msg_digest_ct_span];

    // process rest of the operations in batches
    println!("Unpacking and compressing pv");
    let batch_size = 32;
    let mut offset = 0;

    let (assigned_buckets, assigned_bucket_weights) =
        assign_buckets(m, gamma, bfv_params.plaintext(), N);

    for i in 0..N / batch_size {
        println!("Processing batch: {}", i);
        now = std::time::SystemTime::now();
        let unpacked_cts = pv_unpack(
            &bfv_params,
            &rot_keys,
            &inner_sum_rot_keys,
            &mut ct,
            batch_size,
            offset,
            &bfv_sk,
            level_offset,
        );
        println!("batch {} unpacking took {:?}", i, now.elapsed().unwrap());

        now = std::time::SystemTime::now();
        pv_compress(
            &bfv_params,
            &unpacked_cts,
            level_offset + 2,
            batch_size,
            offset,
            &mut compressed_pv_ct,
        );
        println!("batch {} compress took {:?}", i, now.elapsed().unwrap());

        now = std::time::SystemTime::now();
        // pertinency_value * bucket_weights
        let pv_by_weights = pv_weights(
            &assigned_buckets,
            &assigned_bucket_weights,
            &unpacked_cts,
            &rows.1,
            payload_size,
            &bfv_params,
            batch_size,
            msg_digest_ct_span,
            gamma,
            offset,
            level_offset + 2,
            DEGREE,
        );

        finalise_combinations(
            pv_by_weights.as_slice(),
            &mut rhs_ct,
            m,
            DEGREE,
            payload_size,
        );
        println!("batch {} combinations took {:?}", i, now.elapsed().unwrap());

        offset += batch_size;
    }
    let server_time = server_time.elapsed().unwrap();
    level_offset += 2;

    unsafe {
        dbg!(bfv_sk.measure_noise(&rhs_ct[0])).unwrap();
    }

    compressed_pv_ct.mod_switch_to_last_level();
    for ct in &mut rhs_ct {
        ct.mod_switch_to_last_level();
    }

    println!("///////// CLIENT SIDE //////////");
    let client_time = std::time::SystemTime::now();

    let pv = pv_decompress(&bfv_params, &compressed_pv_ct, &bfv_sk);

    // let mut res_indices = vec![];
    // pv.iter().enumerate().for_each(|(index, bit)| {
    //     if *bit == 1 {
    //         res_indices.push(index);
    //     }
    // });
    // println!("Expected indices {:?}", pertinent_indices);
    // println!("Res indices      {:?}", res_indices);

    // let rhs_vals = bfv_sk.try_decrypt(&rhs_ct).unwrap();
    // let rhs_vals = Vec::<u64>::try_decode(&rhs_vals, Encoding::simd()).unwrap();

    // // solve linear equations
    // let lhs = construct_lhs(
    //     &pv,
    //     assigned_buckets,
    //     assigned_bucket_weights,
    //     m,
    //     k,
    //     gamma,
    //     N,
    // );
    // let rhs = construct_rhs(rhs_vals, m, payload_size, bfv_params.plaintext());
    // let vals = solve_equations(lhs, rhs, bfv_params.plaintext());

    // let client_time = client_time.elapsed().unwrap();

    // let mut expected_dataset = HashSet::new();
    // pertinent_indices.iter().for_each(|i| {
    //     expected_dataset.insert(rows.1[*i].clone());
    // });

    // let mut res_dataset = HashSet::new();
    // vals.iter().for_each(|val| {
    //     if *val != vec![0; payload_size] {
    //         res_dataset.insert(val.clone());
    //     }
    // });

    // assert_eq!(expected_dataset, res_dataset);
    // println!("OMR works!");
    // println!(
    //     "Server took: {:?}; Client took: {:?}",
    //     server_time, client_time
    // );
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
