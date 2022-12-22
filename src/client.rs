use crate::pvw::{PVWParameters, PVWSecretKey};
use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
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
use std::{fs::File, io::Write, path::Path, vec};

pub fn gen_pvw_sk_cts(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &PVWParameters,
    bfv_sk: &SecretKey,
    pvw_sk: &PVWSecretKey,
) -> Vec<Ciphertext> {
    debug_assert!(pvw_sk.key.dim().0 == pvw_params.ell);

    let mut rng = thread_rng();

    let sec_len = pvw_params.n.next_power_of_two();
    pvw_sk
        .key
        .outer_iter()
        .map(|ell_n| {
            let mut values = vec![0u64; bfv_params.degree()];
            for j in 0..bfv_params.degree() {
                let index = j % sec_len;
                if index < pvw_params.n {
                    // fixme
                    values[j] = ell_n[index];
                }
            }
            let values_pt = Plaintext::try_encode(&values, Encoding::simd(), bfv_params).unwrap();
            bfv_sk.try_encrypt(&values_pt, &mut rng).unwrap()
        })
        .collect_vec()
}

pub fn pv_decompress(
    bfv_params: &Arc<BfvParameters>,
    pv_ct: &Ciphertext,
    sk: &SecretKey,
) -> Vec<u64> {
    let pt = sk.try_decrypt(pv_ct).unwrap();
    let values = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();

    let coeff_size = 64 - bfv_params.plaintext().leading_zeros() - 1;
    let mut pv = vec![];
    values.into_iter().for_each(|mut v| {
        for _ in 0..coeff_size {
            pv.push(v & 1);
            v >>= 1;
        }
    });
    pv
}

pub fn construct_lhs(
    pv: &[u64],
    assigned_buckets: Vec<Vec<usize>>,
    assigned_weights: Vec<Vec<u64>>,
    m: usize,
    k: usize,
    gamma: usize,
    set_size: usize,
) -> Vec<Vec<u64>> {
    let mut lhs = vec![vec![0u64; k]; m];

    let mut overflow_counter = 0;
    for i in 0..set_size {
        if pv[i] == 1 {
            if overflow_counter < k {
                for j in 0..gamma {
                    let cmb_i = assigned_buckets[i][j];
                    lhs[cmb_i][overflow_counter] = assigned_weights[i][j];
                }
            }
            overflow_counter += 1;
        }
    }

    if overflow_counter > k {
        println!("OVERFLOW!");
    }

    lhs
}

pub fn construct_rhs(values: &[u64], m: usize, m_row_span: usize, q_mod: u64) -> Vec<Vec<u64>> {
    values[..m * m_row_span]
        .chunks(m_row_span)
        .map(|bucket| bucket.to_vec())
        .collect()
}

mod tests {
    use super::*;
    use crate::utils::{assign_buckets, solve_equations};

    #[test]
    fn test_assign_buckets() {
        let rng = thread_rng();
        let k = 50;
        let m = k * 2;
        let gamma = 5;
        let q_mod = 65537;

        let (buckets, weights) = assign_buckets(m, gamma, q_mod, k);

        // let's generate k random values
        let values = rng
            .sample_iter(Uniform::new(0u64, q_mod))
            .take(k)
            .collect_vec();

        let modulus = Modulus::new(q_mod).unwrap();

        let mut comb = vec![0u64; m];
        for i in 0..k {
            for j in 0..gamma {
                let cmb_i = buckets[i][j];
                comb[cmb_i] = modulus.add(modulus.mul(values[i], weights[i][j]), comb[cmb_i]);
            }
        }
        let rhs = comb.iter().map(|c| vec![*c]).collect_vec();

        // construct LHS
        let mut lhs = vec![vec![0u64; k]; m];
        for i in 0..k {
            for j in 0..gamma {
                let cmb_i = buckets[i][j];
                lhs[cmb_i][i] = weights[i][j];
            }
        }

        let sols = solve_equations(lhs, rhs, q_mod)
            .iter()
            .map(|v| v[0])
            .collect_vec();
        assert_eq!(sols, values);
    }
}
