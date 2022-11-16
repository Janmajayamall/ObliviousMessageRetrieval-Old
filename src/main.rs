use core::num;
use std::collections::HashMap;
use std::{fs::File, io::Write, path::Path, vec};

use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use fhe::bfv::{
    self, BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, Multiplicator, Plaintext,
    RelinearizationKey, SecretKey,
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
use std::sync::Arc;

mod pvw;
use pvw::{PVWCiphertext, PVWParameters, PVWSecretKey, PublicKey};

mod utils;
use utils::{precompute_range_coeffs, read_range_coeffs};

/// test fn that simulates powers_of_x on plaintext
/// for debugging
fn powers_of_x_poly(
    ctx: &Arc<Context>,
    input: &Poly,
    // k_degree
    degree: usize,
) -> Vec<Poly> {
    let mut outputs = vec![Poly::zero(&ctx, Representation::PowerBasis); degree];
    let mut calculated = vec![0usize; degree];

    let mut num_mod = vec![0usize; degree];

    for i in (0..degree + 1).rev() {
        let mut curr_deg = i;
        let mut base = input.clone();
        let mut res = Poly::zero(&ctx, Representation::PowerBasis);
        let mut base_deg = 1;
        let mut res_deg = 0;
        while curr_deg > 0 {
            if (curr_deg & 1) == 1 {
                curr_deg -= 1;
                res_deg = res_deg + base_deg;

                if calculated[res_deg - 1] == 1 {
                    res = outputs[res_deg - 1].clone();
                } else {
                    if res_deg == base_deg {
                        res = base.clone();
                    } else {
                        num_mod[res_deg - 1] = num_mod[base_deg - 1];
                        res = &res * &base;

                        while num_mod[res_deg - 1]
                            < ((res_deg as f32).log2() / 2f32).ceil() as usize
                        {
                            num_mod[res_deg - 1] += 1;
                        }
                        // dbg!(num_mod[base_deg - 1], res_deg);
                    }
                    outputs[res_deg - 1] = res.clone();
                    calculated[res_deg - 1] = 1;
                }
            } else {
                curr_deg /= 2;
                base_deg *= 2;

                if calculated[base_deg - 1] == 1 {
                    base = outputs[base_deg - 1].clone();
                } else {
                    num_mod[base_deg - 1] = num_mod[base_deg / 2 - 1];

                    base = &base * &base;
                    outputs[base_deg - 1] = base.clone();
                    calculated[base_deg - 1] = 1;

                    while num_mod[base_deg - 1] < ((base_deg as f32).log2() / 2f32).ceil() as usize
                    {
                        num_mod[base_deg - 1] += 1;
                    }
                    // dbg!(num_mod[base_deg - 1], base_deg);
                }
            }
        }
    }

    outputs
}

fn powers_of_x(
    input: &Ciphertext,
    degree: usize,
    params: &Arc<BfvParameters>,
    rlk_keys: &HashMap<usize, RelinearizationKey>,
    mod_offset: usize,
) -> Vec<Ciphertext> {
    let mut outputs = vec![Ciphertext::zero(&params); degree];
    let mut calculated = vec![0usize; degree];
    let mut num_mod = vec![0usize; degree];

    for i in (0..degree + 1).rev() {
        let mut curr_deg = i;
        let mut base = input.clone();
        let mut res = Ciphertext::zero(&params);
        let mut base_deg = 1;
        let mut res_deg = 0;

        while curr_deg > 0 {
            if (curr_deg & 1) == 1 {
                curr_deg -= 1;

                let prev_res_deg = res_deg;
                res_deg += base_deg;

                if calculated[res_deg - 1] == 1 {
                    res = outputs[res_deg - 1].clone();
                } else {
                    if res_deg == base_deg {
                        res = base.clone();
                    } else {
                        // make modulus level at `res_deg` equal to `res`
                        num_mod[res_deg - 1] = num_mod[prev_res_deg - 1];
                        while num_mod[res_deg - 1] < num_mod[base_deg - 1] {
                            res.mod_switch_to_next_level();
                            num_mod[res_deg - 1] += 1;
                        }
                        res = &res * &base;
                        let rlk_level =
                            rlk_keys.get(&(num_mod[base_deg - 1] + mod_offset)).unwrap();
                        rlk_level.relinearizes(&mut res).unwrap();

                        while num_mod[res_deg - 1]
                            < ((res_deg as f32).log2() / 2f32).ceil() as usize
                        {
                            res.mod_switch_to_next_level();
                            num_mod[res_deg - 1] += 1;
                        }
                    }
                    outputs[res_deg - 1] = res.clone();
                    calculated[res_deg - 1] = 1;
                }
            } else {
                curr_deg /= 2;
                base_deg *= 2;

                if calculated[base_deg - 1] == 1 {
                    base = outputs[base_deg - 1].clone();
                } else {
                    num_mod[base_deg - 1] = num_mod[base_deg / 2 - 1];
                    base = &base * &base;

                    let rlk_level = rlk_keys.get(&(num_mod[base_deg - 1] + mod_offset)).unwrap();
                    rlk_level.relinearizes(&mut base).unwrap();

                    while num_mod[base_deg - 1] < ((base_deg as f32).log2() / 2f32).ceil() as usize
                    {
                        base.mod_switch_to_next_level();
                        num_mod[base_deg - 1] += 1;
                    }
                    outputs[base_deg - 1] = base.clone();
                    calculated[base_deg - 1] = 1;
                }
            }
        }
    }
    // match modulus
    let depth = num_mod[outputs.len() - 1];
    for i in 0..outputs.len() - 1 {
        while num_mod[i] < depth {
            outputs[i].mod_switch_to_next_level();
            num_mod[i] += 1;
        }
    }

    outputs
}

fn range_fn_poly(ctx: &Arc<Context>, input: &Poly, poly_degree: usize) -> Poly {
    // read coeffs
    let coeffs = read_range_coeffs("params.bin");
    let k_degree = 256;
    let mut k_powers_of_x: Vec<Poly> = powers_of_x_poly(&ctx, &input, k_degree);
    // M = x^256
    let mut k_powers_of_m: Vec<Poly> = powers_of_x_poly(&ctx, &k_powers_of_x[255], k_degree);

    let mut total_sum = Poly::zero(&ctx, Representation::Ntt);
    for i in 0..256 {
        let mut sum = Poly::zero(&ctx, Representation::Ntt);
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            let c = vec![c; poly_degree];
            let c_poly = Poly::try_convert_from(c, &ctx, false, Representation::Ntt).unwrap();
            let scalar_product = &k_powers_of_x[j - 1] * &c_poly;
            sum += &scalar_product;
        }

        if i == 0 {
            total_sum = sum;
        } else {
            let p = &k_powers_of_m[i - 1] * &sum;
            total_sum += &p;
        }
    }
    total_sum = -total_sum;

    total_sum
}

fn range_fn(
    bfv_params: &Arc<BfvParameters>,
    input: &Ciphertext,
    rlk_keys: &HashMap<usize, RelinearizationKey>,
) -> Ciphertext {
    // all k_powers_of_x are at level 4
    let k_powers_of_x = powers_of_x(input, 256, bfv_params, rlk_keys, 0);
    // m = x^256
    // all k_powers_of_m are at level 8
    let k_powers_of_m = powers_of_x(&k_powers_of_x[255], 256, bfv_params, rlk_keys, 4);

    let coeffs = read_range_coeffs("params.bin");

    let mut total = Ciphertext::zero(bfv_params);
    for i in 0..256 {
        let mut sum: Ciphertext = Ciphertext::zero(bfv_params);
        let mut flag = false;
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            let c_pt = Plaintext::try_encode(
                &vec![c; bfv_params.degree()],
                Encoding::simd_at_level(4),
                bfv_params,
            )
            .unwrap();
            let scalar_product = &k_powers_of_x[j - 1] * &c_pt;

            if !flag {
                sum = scalar_product;
                flag = true;
            } else {
                sum += &scalar_product;
            }
        }

        // match modulus
        for _ in 0..4 {
            sum.mod_switch_to_next_level();
        }

        if i != 0 {
            // mul and add
            let mut p = &k_powers_of_m[i - 1] * &sum;
            let rlk = rlk_keys.get(&8).unwrap();
            rlk.relinearizes(&mut p).unwrap();

            total += &p
        } else {
            total = sum;
        }
    }

    total = -total;
    // total.mod_switch_to_next_level();

    total
}

fn prep_sk() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(8)
            .set_plaintext_modulus(65537)
            .set_moduli_sizes(&vec![62usize; 3])
            .build()
            .unwrap(),
    );
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

    let pvw_params = PVWParameters {
        n: 450,
        m: 100,
        ell: 4,
        variance: 2,
        q: 65537,
    };
    let pvw_sk = PVWSecretKey::gen_sk(&pvw_params);
    let pvw_pk = pvw_sk.public_key();

    let mut h_pvw_sk = vec![vec![Ciphertext::zero(&bfv_params); pvw_params.n]; pvw_params.ell];
    for l_i in 0..pvw_params.ell {
        for n_i in 0..pvw_params.n {
            let element = pvw_sk.key[l_i][n_i];
            let element_arr = vec![element; bfv_params.degree()];
            let pt = Plaintext::try_encode(&element_arr, Encoding::simd(), &bfv_params).unwrap();
            let ct = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();
            h_pvw_sk[l_i][n_i] = ct;
        }
    }

    // generate 2 PVW cts
    let p_c1 = pvw_pk.encrypt(vec![1, 0, 0, 0]);
    let p_c2 = pvw_pk.encrypt(vec![1, 1, 0, 1]);

    // Encode pvw cts into simd vecs.
    // Each SIMD pt consists of nth `a` element
    // al pvw cts
    let mut h_a = vec![Ciphertext::zero(&bfv_params); pvw_params.n];
    for n_i in 0..pvw_params.n {
        let pt = Plaintext::try_encode(&[p_c1.a[n_i], p_c2.a[n_i]], Encoding::simd(), &bfv_params)
            .unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();
        h_a[n_i] = ct;
    }

    let mut h_b = vec![Ciphertext::zero(&bfv_params); pvw_params.ell];
    for ell_i in 0..pvw_params.ell {
        let pt = Plaintext::try_encode(
            &[p_c1.b[ell_i], p_c2.b[ell_i]],
            Encoding::simd(),
            &bfv_params,
        )
        .unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();
        h_b[ell_i] = ct;
    }

    let rlk = RelinearizationKey::new(&bfv_sk, &mut rng).unwrap();
    let multiplicator = Multiplicator::default(&rlk).unwrap();

    // sk * a (homomorphically)
    let mut h_ska = vec![Ciphertext::zero(&bfv_params); pvw_params.ell];
    for el_i in 0..pvw_params.ell {
        let mut sum = Ciphertext::zero(&bfv_params);
        for n_i in 0..pvw_params.n {
            let product = multiplicator
                .multiply(&h_pvw_sk[el_i][n_i], &h_a[n_i])
                .unwrap();
            sum = &sum + &product;
        }
        h_ska[el_i] = sum;
    }

    // now perform b-sa
    let mut h_d = vec![Ciphertext::zero(&bfv_params); pvw_params.ell];
    for ell_i in 0..pvw_params.ell {
        h_d[ell_i] = &h_b[ell_i] - &h_ska[ell_i];
    }

    // for i in 0..pvw_params.ell {
    //     let d_ct = range_fn(&bfv_params, &h_d[i], &rlk);
    //     let d = bfv_sk.try_decrypt(&d_ct).unwrap();
    //     let v = Vec::<u64>::try_decode(&d, Encoding::simd()).unwrap();
    //     dbg!(v);
    //     // dbg!(((v[0] + (pvw_params.q / 4)) / (pvw_params.q / 2)) % 2);
    //     // dbg!(v[0]);
    // }
}

#[cfg(test)]
mod tests {
    use itertools::izip;

    use super::*;

    #[test]
    fn trial() {
        // range_fn_poly();
        // powers_of_x_poly();
        // precompute_range_coeffs();
        // read_range_coeffs("params.bin");
        // prep_sk();
        // range_fn();
        // trickle();
        // sq_mul();
    }

    #[test]
    fn test_range_fn() {
        let mut rng = thread_rng();
        let poly_degree = 8;
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(poly_degree)
                .set_plaintext_modulus(65537)
                .set_moduli_sizes(&vec![62usize; 14])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
        let t_ctx = Arc::new(Context::new(&[65537], 8).unwrap());

        let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
        for i in 0..bfv_params.max_level() {
            let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
            rlk_keys.insert(i, rlk);
        }

        let dist = Uniform::new(0u64, 65536);
        let X = dist.sample_iter(rng.clone()).take(8).collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd(), &bfv_params).unwrap();
        let pt_poly = Poly::try_convert_from(&X, &t_ctx, false, Representation::Ntt).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let res_poly = range_fn_poly(&t_ctx, &pt_poly, poly_degree);

        let res_ct = range_fn(&bfv_params, &ct, &rlk_keys);
        let res_pt = bfv_sk.try_decrypt(&res_ct).unwrap();

        assert_eq!(
            Vec::<u64>::try_decode(&res_pt, Encoding::simd()).unwrap(),
            res_poly.coefficients().to_slice().unwrap()
        );
    }

    #[test]
    fn power_of_x() {
        let mut rng = thread_rng();
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(8)
                .set_plaintext_modulus(65537)
                .set_moduli_sizes(&vec![62usize; 8])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
        let t_ctx = Arc::new(Context::new(&[65537], 8).unwrap());

        let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
        for i in 0..bfv_params.max_level() {
            let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
            rlk_keys.insert(i, rlk);
        }

        let X = vec![2u64, 3, 4, 3, 4, 1, 3, 4];
        let pt = Plaintext::try_encode(&X, Encoding::simd(), &bfv_params).unwrap();
        let pt_poly = Poly::try_convert_from(&X, &t_ctx, false, Representation::Ntt).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let k_degree = 256;

        let powers = powers_of_x_poly(&t_ctx, &pt_poly, k_degree);
        let powers_ct = powers_of_x(&ct, k_degree, &bfv_params, &rlk_keys, 0);

        izip!(powers.iter(), powers_ct.iter()).for_each(|(p, ct)| {
            let pt = bfv_sk.try_decrypt(ct).unwrap();
            let pt = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(pt, p.coefficients().to_slice().unwrap());
        })
    }
}

fn main() {
    println!("Hello, world!");
}
