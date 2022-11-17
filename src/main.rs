use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use core::num;
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
use std::collections::HashMap;
use std::sync::Arc;
use std::{fs::File, io::Write, path::Path, vec};

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
    let mut count = 0;
    for i in 0..256 {
        let mut sum: Ciphertext = Ciphertext::zero(bfv_params);
        let mut flag = false;
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            if c < 1 {
                count += 1;
            }
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
    dbg!(count);
    total = -total;
    // total.mod_switch_to_next_level();

    total
}

fn pv_unpack(
    bfv_params: &Arc<BfvParameters>,
    rot_keys: &HashMap<usize, GaloisKey>,
    pv_ct: &Ciphertext,
) -> Vec<Ciphertext> {
    let mut selected_vals = vec![Ciphertext::zero(&bfv_params); bfv_params.degree()];
    for i in 0..bfv_params.degree() {
        let mut select = vec![0u64; bfv_params.degree()];
        select[i] = 1;
        let pt = Plaintext::try_encode(&select, Encoding::simd(), bfv_params).unwrap();
        selected_vals[i] = pv_ct * &pt;
    }

    let mut pv = vec![Ciphertext::zero(&bfv_params); bfv_params.degree()];
    for index in 0..selected_vals.len() {
        let mut i = 1usize;
        let mut res = selected_vals[index].clone();
        while i < bfv_params.degree() / 2 {
            res = &res + &rot_keys.get(&i).unwrap().relinearize(&res).unwrap();
            i *= 2;
        }
        res = &res
            + &rot_keys
                .get(&(bfv_params.degree() * 2 - 1))
                .unwrap()
                .relinearize(&res)
                .unwrap();

        pv[index] = res;
    }

    pv
}

// decrypt pvw cts
fn decrypt_pvw(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &Arc<PVWParameters>,
    ct_pvw_sk: &Vec<Ciphertext>,
    rotation_key: GaloisKey,
    clues: Vec<PVWCiphertext>,
) -> Vec<Ciphertext> {
    debug_assert!(ct_pvw_sk.len() == pvw_params.ell);

    // encrypts sk * a for N clues
    let mut sk_a = vec![Ciphertext::zero(bfv_params); pvw_params.ell];
    for ell_index in 0..pvw_params.ell {
        let mut sk = ct_pvw_sk[ell_index].clone();
        for i in 0..pvw_params.n {
            let mut values = vec![0u64; bfv_params.degree()];
            for j in 0..clues.len() {
                let index = (i + j) % pvw_params.n;
                values[j] = clues[j].a[index];
            }

            let values_pt = Plaintext::try_encode(&values, Encoding::simd(), bfv_params).unwrap();
            let product = &sk * &values_pt;
            sk_a[ell_index] = &sk_a[ell_index] + &product;

            // rotate left by 1
            sk = rotation_key.relinearize(&sk).unwrap();
        }
    }

    // d = b-sa
    let mut d = vec![Ciphertext::zero(bfv_params); pvw_params.ell];
    for ell_index in 0..pvw_params.ell {
        // we assume that N <= D
        let mut b_ell = vec![0u64; bfv_params.degree()];
        for i in 0..clues.len() {
            b_ell[i] = clues[i].b[ell_index];
        }
        let b_ell = Plaintext::try_encode(&b_ell, Encoding::simd(), bfv_params).unwrap();

        d[ell_index] = &(-&sk_a[ell_index]) + &b_ell;
    }

    d
}

fn pv_compress(bfv_params: &Arc<BfvParameters>, pv: &Vec<Ciphertext>, level: usize) -> Ciphertext {
    let mut compressed_pv = Ciphertext::zero(&bfv_params);
    let log_t = 64 - bfv_params.plaintext().leading_zeros();
    for i in 0..pv.len() {
        let index = (i as f32 / log_t as f32).floor() as usize;
        let bit_index = (i as u32) % log_t;

        let mut select = vec![0u64; bfv_params.degree()];
        select[index] = 2u64.pow(bit_index);
        let select_pt =
            Plaintext::try_encode(&select, Encoding::simd_at_level(level), &bfv_params).unwrap();

        // pv_i * select_i
        let product = &pv[i] * &select_pt;

        compressed_pv = &compressed_pv + &product;
    }

    compressed_pv
}

fn run() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(1024)
            .set_plaintext_modulus(65537)
            .set_moduli_sizes(&vec![62usize; 14])
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

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use itertools::izip;

    use crate::utils::rot_to_exponent;

    use super::*;

    #[test]
    fn test_run() {
        run();
    }

    #[test]
    fn rotations() {
        let degree = 8;
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(65537)
                .set_moduli_sizes(&[62; 3])
                .build()
                .unwrap(),
        );
        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let mut t = vec![0u64; degree];
        t[0] = 121;
        t[3] = 623;

        let pt = Plaintext::try_encode(&t, Encoding::simd(), &params).unwrap();
        let ct: Ciphertext = sk.try_encrypt(&pt, &mut rng).unwrap();

        let rot_key = GaloisKey::new(&sk, 3, 0, 0, &mut rng).unwrap();

        let mut rotated_ct = ct.clone();
        // rotated_ct = rot_key.relinearize(&rotated_ct).unwrap();
        for i in 0..1 {
            rotated_ct = rot_key.relinearize(&rotated_ct).unwrap();
        }

        let rotated_pt = sk.try_decrypt(&rotated_ct).unwrap();
        println!(
            "{:?}",
            Vec::<u64>::try_decode(&rotated_pt, Encoding::simd()).unwrap()
        );
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

    #[test]
    fn test_pv_unpack() {
        let mut rng = thread_rng();
        let degree = 8;
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(65537)
                .set_moduli_sizes(&vec![62usize; 3])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        // rotation keys
        let mut rot_keys = HashMap::<usize, GaloisKey>::new();
        let mut i = 1;
        while i < bfv_params.degree() / 2 {
            let exponent = rot_to_exponent(i as u64, &bfv_params);
            rot_keys.insert(
                i,
                GaloisKey::new(&bfv_sk, exponent, 0, 0, &mut rng).unwrap(),
            );
            i *= 2;
        }

        rot_keys.insert(
            bfv_params.degree() * 2 - 1,
            GaloisKey::new(&bfv_sk, bfv_params.degree() * 2 - 1, 0, 0, &mut rng).unwrap(),
        );

        let distr = Uniform::new(0u64, 65537);
        let values = distr.sample_iter(rng.clone()).take(degree).collect_vec();
        let pt = Plaintext::try_encode(&values, Encoding::simd(), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let unpacked_cts = pv_unpack(&bfv_params, &rot_keys, &ct);
        unpacked_cts.iter().enumerate().for_each(|(index, u_ct)| {
            let pt = bfv_sk.try_decrypt(&u_ct).unwrap();
            let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(v, vec![values[index]; degree]);
        });
    }

    #[test]
    fn test_pv_compress() {
        let mut rng = thread_rng();
        let degree = 8;
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(65537)
                .set_moduli_sizes(&vec![62usize; 8])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        let mut rot_keys = HashMap::<usize, GaloisKey>::new();
        let mut i = 1;
        while i < degree / 2 {
            let exponent = rot_to_exponent(i as u64, &bfv_params);
            rot_keys.insert(
                i,
                GaloisKey::new(&bfv_sk, exponent, 0, 0, &mut rng).unwrap(),
            );
            i *= 2;
        }
        rot_keys.insert(
            degree * 2 - 1,
            GaloisKey::new(&bfv_sk, degree * 2 - 1, 0, 0, &mut rng).unwrap(),
        );

        // Packing capacity in bits: log_t * D
        // so let's try packing entire ct with pv
        // values. Note that we will need log_t pertinency
        // vector ciphertexts to fully cover a single
        // compressed pv ct.
        // let ct_capacity = (degree as u32) * (16);
        let ct_capacity = 5 * 16;

        // generate log_t * D {0,1} values
        let pv = Uniform::new(0u64, 2)
            .sample_iter(rng.clone())
            .take(ct_capacity as usize)
            .collect_vec();

        // calculate log_t * D enc({0,1}) values
        let pv_cts = pv
            .chunks(bfv_params.degree())
            .flat_map(|vals| {
                let pt = Plaintext::try_encode(vals, Encoding::simd(), &bfv_params).unwrap();
                let pv_ct = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

                // unpack
                pv_unpack(&bfv_params, &rot_keys, &pv_ct)
            })
            .collect_vec();

        let pv_compressed = pv_compress(&bfv_params, &pv_cts, 0);
        let pv_compressed = bfv_sk.try_decrypt(&pv_compressed).unwrap();
        let mut pv_compressed = Vec::<u64>::try_decode(&pv_compressed, Encoding::simd()).unwrap();
        dbg!(&pv_compressed);
        let final_vals = pv_compressed
            .iter_mut()
            .flat_map(|v| {
                let mut bits = vec![];
                for _ in 0..17 {
                    bits.push(*v & 1);
                    *v >>= 1;
                }
                bits
            })
            .collect_vec();

        println!("{:?}", final_vals[..pv.len()].to_vec());
        println!("{:?}", pv);

        assert_eq!(final_vals[..pv.len()], pv);
    }
}

fn main() {
    println!("Hello, world!");
}
