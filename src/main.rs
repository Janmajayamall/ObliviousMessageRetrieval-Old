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
            .set_degree(1024)
            .set_plaintext_modulus(65537)
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
    let N = 2;
    let mut clues = vec![];
    for i in 0..N {
        clues.push(pvw_pk.encrypt(vec![0, 1, 1, 0]));
    }

    let mut ct_pvw_sk = vec![Ciphertext::zero(&bfv_params); pvw_params.ell];
    for l_i in 0..pvw_params.ell {
        let mut values = vec![0u64; bfv_params.degree()];
        // make sure `n` < `D` (tbh should be way smaller)
        for n_i in 0..bfv_params.degree() {
            values[n_i] = pvw_sk.key[l_i][n_i % pvw_params.n];
        }
        let pt = Plaintext::try_encode(&values, Encoding::simd(), &bfv_params).unwrap();
        ct_pvw_sk[l_i] = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();
    }

    let top_rot_key = GaloisKey::new(&bfv_sk, 3, 0, 0, &mut rng).unwrap();

    let d = decrypt_pvw(&bfv_params, &pvw_params, &ct_pvw_sk, top_rot_key, clues);

    // relinearization keys at all levels
    let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
    for i in 0..bfv_params.max_level() {
        let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
        rlk_keys.insert(i, rlk);
    }

    let mut d_checked = vec![Ciphertext::zero(&bfv_params); pvw_params.ell];
    for i in 0..pvw_params.ell {
        d_checked[i] = range_fn(&bfv_params, &d[i], &rlk_keys);
    }

    for i in 0..pvw_params.ell {
        let d_el = bfv_sk.try_decrypt(&d_checked[i]).unwrap();
        let d_el = Vec::<u64>::try_decode(&d_el, Encoding::simd()).unwrap();
        // let v = d_el
        //     .iter()
        //     .map(|v| (*v >= pvw_params.q / 2) as u64)
        //     .collect_vec();
        dbg!(&d_el[..20]);
    }

    // let rlk = RelinearizationKey::new(&bfv_sk, &mut rng).unwrap();

    // for i in 0..pvw_params.ell {
    //     let d_ct = range_fn(&bfv_params, &h_d[i], &rlk);
    //     let d = bfv_sk.try_decrypt(&d_ct).unwrap();
    //     let v = Vec::<u64>::try_decode(&d, Encoding::simd()).unwrap();
    //     dbg!(v);
    //     // dbg!(((v[0] + (pvw_params.q / 4)) / (pvw_params.q / 2)) % 2);
    //     // dbg!(v[0]);
    // }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_run() {
        run();
    }
}
