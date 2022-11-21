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

use crate::pvw::{PVWCiphertext, PVWParameters, PVWSecretKey, PublicKey};
use crate::utils::read_range_coeffs;

pub fn powers_of_x(
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
            let mut now = std::time::SystemTime::now();
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

                        // now = std::time::SystemTime::now();
                        while num_mod[res_deg - 1]
                            < ((res_deg as f32).log2() / 2f32).ceil() as usize
                        {
                            res.mod_switch_to_next_level();
                            num_mod[res_deg - 1] += 1;
                        }
                        // println!(
                        //     "Mod level {} {:?}",
                        //     num_mod[res_deg - 1],
                        //     now.elapsed().unwrap()
                        // );
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
                        now = std::time::SystemTime::now();

                        base.mod_switch_to_next_level();
                        num_mod[base_deg - 1] += 1;

                        println!(
                            "Mod level {} {:?}",
                            num_mod[base_deg - 1],
                            now.elapsed().unwrap()
                        );
                    }

                    outputs[base_deg - 1] = base.clone();
                    calculated[base_deg - 1] = 1;
                }
            }
            // println!("Degree {} {:?}", curr_deg, now.elapsed().unwrap());
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

pub fn range_fn(
    bfv_params: &Arc<BfvParameters>,
    input: &Ciphertext,
    rlk_keys: &HashMap<usize, RelinearizationKey>,
) -> Ciphertext {
    let mut now = std::time::SystemTime::now();
    // all k_powers_of_x are at level 4
    let k_powers_of_x = powers_of_x(input, 256, bfv_params, rlk_keys, 0);
    println!(" k_powers_of_x {:?}", now.elapsed().unwrap());

    now = std::time::SystemTime::now();
    // m = x^256
    // all k_powers_of_m are at level 8
    let k_powers_of_m = powers_of_x(&k_powers_of_x[255], 256, bfv_params, rlk_keys, 4);
    println!(" k_powers_of_m {:?}", now.elapsed().unwrap());

    let coeffs = read_range_coeffs("params.bin");

    let mut total = Ciphertext::zero(bfv_params);
    let mut count = 0;
    for i in 0..256 {
        let mut sum: Ciphertext = Ciphertext::zero(bfv_params);
        let mut flag = false;

        now = std::time::SystemTime::now();
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
        println!(" sum for index {} {:?}", i, now.elapsed().unwrap());

        now = std::time::SystemTime::now();
        // match modulus
        for _ in 0..4 {
            sum.mod_switch_to_next_level();
        }
        println!(
            " switching down by 4 mods {} {:?}",
            i,
            now.elapsed().unwrap()
        );

        now = std::time::SystemTime::now();
        if i != 0 {
            // mul and add
            let mut p = &k_powers_of_m[i - 1] * &sum;
            let rlk = rlk_keys.get(&8).unwrap();
            rlk.relinearizes(&mut p).unwrap();

            total += &p
        } else {
            total = sum;
        }
        println!(" total calc {} {:?}", i, now.elapsed().unwrap());
    }

    total = -total;
    // total.mod_switch_to_next_level();

    total
}

/// decrypt pvw cts
///
/// TODO: Replace `pvw_params.n` with value, where
/// log(value) = ceil(log(pvw_params.n))
pub fn decrypt_pvw(
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

pub fn pv_unpack(
    bfv_params: &Arc<BfvParameters>,
    rot_keys: &HashMap<usize, GaloisKey>,
    pv_ct: &Ciphertext,
) -> Vec<Ciphertext> {
    // let mut now = std::time::SystemTime::now();

    let mut pv = vec![];
    for i in 0..bfv_params.degree() {
        let mut select = vec![0u64; bfv_params.degree()];
        select[i] = 1;
        let pt = Plaintext::try_encode(&select, Encoding::simd(), bfv_params).unwrap();
        let mut value_vec = pv_ct * &pt;

        // Inner sum over value_vec to go from
        // [0,0,0,0...,value,0,0,0...] to [value, value,...]
        let mut i = 1usize;
        while i < bfv_params.degree() / 2 {
            value_vec = &value_vec + &rot_keys.get(&i).unwrap().relinearize(&value_vec).unwrap();
            i *= 2;
        }
        value_vec = &value_vec
            + &rot_keys
                .get(&(bfv_params.degree() * 2 - 1))
                .unwrap()
                .relinearize(&value_vec)
                .unwrap();

        pv.push(value_vec);
    }

    pv
}

pub fn pv_compress(
    bfv_params: &Arc<BfvParameters>,
    pv: &Vec<Ciphertext>,
    level: usize,
) -> Ciphertext {
    let mut compressed_pv = Ciphertext::zero(&bfv_params);
    let log_t = 64 - bfv_params.plaintext().leading_zeros() - 1;
    dbg!("sa", log_t);
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

/// Returns bucket assignments corresponding to each
/// pertinent payload scaled by corresponding weight
///
/// That is, for each payload, `PV[i] * a`, where `a` encodes
/// `payload * weight` at respective bucket slots.
pub fn pv_weights(
    assigned_buckets: Vec<Vec<usize>>,
    assigned_weights: Vec<Vec<u64>>,
    pv: &Vec<Ciphertext>,
    payloads: Vec<Vec<u64>>,
    payload_size: usize,
    bfv_params: &Arc<BfvParameters>,
    N: usize,
    gamma: usize,
) -> Vec<Ciphertext> {
    let q_mod = bfv_params.plaintext();
    let modulus = Modulus::new(q_mod).unwrap();

    let mut products = vec![Ciphertext::zero(&bfv_params); N];
    for row_index in 0..N {
        let mut pt = vec![0u64; bfv_params.degree()];
        for i in 0..gamma {
            // think of single bucket as spanning across `payload_size`
            // no. of rows of plaintext vector
            let bucket = assigned_buckets[row_index][i] * payload_size;

            for chunk_index in 0..payload_size {
                // payload chunk * weight
                pt[bucket + chunk_index] = modulus.add(
                    pt[bucket + chunk_index],
                    modulus.mul(
                        payloads[row_index][chunk_index],
                        assigned_weights[row_index][i],
                    ),
                )
            }
        }

        let pt = Plaintext::try_encode(&pt, Encoding::simd(), &bfv_params).unwrap();
        let product = &pv[row_index] * &pt;
        products[row_index] = product;
    }

    products
}

pub fn finalise_combinations(
    pv_weights: Vec<Ciphertext>,
    bfv_params: &Arc<BfvParameters>,
) -> Ciphertext {
    let mut cmb = Ciphertext::zero(bfv_params);
    for i in 0..pv_weights.len() {
        cmb = &cmb + &pv_weights[i];
    }

    cmb
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::{powers_of_x_poly, range_fn_poly, rot_to_exponent};
    use crate::{DEGREE, MODULI_OMR, MODULI_OMR_PT};
    use itertools::izip;

    #[test]
    fn test_range_fn_ct() {
        let poly_degree = DEGREE;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(poly_degree)
                .set_plaintext_modulus(t)
                // .set_moduli_sizes(&vec![
                //     28, 39, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60,
                // ])
                .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        // let mut now = std::time::SystemTime::now();
        let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
        for i in 0..bfv_params.max_level() {
            let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
            rlk_keys.insert(i, rlk);
        }
        // println!("RLK gen took {:?}", now.elapsed().unwrap());

        let X = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(poly_degree)
            .collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd(), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        // now = std::time::SystemTime::now();
        let res_ct = range_fn(&bfv_params, &ct, &rlk_keys);
        let res_pt = bfv_sk.try_decrypt(&res_ct).unwrap();
        // println!(" Range fn ct {:?}", now.elapsed().unwrap());

        // range operation on plaintext
        // let t_ctx = Arc::new(Context::new(&[65537], poly_degree).unwrap());
        // let pt_poly = Poly::try_convert_from(&X, &t_ctx, false, Representation::Ntt).unwrap();
        // let res_poly = range_fn_poly(&t_ctx, &pt_poly, poly_degree);

        // assert_eq!(
        //     Vec::<u64>::try_decode(&res_pt, Encoding::simd()).unwrap(),
        //     res_poly.coefficients().to_slice().unwrap()
        // );
    }

    #[test]
    fn test_range_fn_poly() {
        let degree = DEGREE;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let ctx = Arc::new(Context::new(&[t], degree).unwrap());
        let X = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(degree)
            .collect_vec();
        let pt_poly = Poly::try_convert_from(&X, &ctx, false, Representation::Ntt).unwrap();

        let now = std::time::SystemTime::now();
        range_fn_poly(&ctx, &pt_poly, degree);
        println!(" Range fn poly {:?}", now.elapsed().unwrap());
    }

    #[test]
    fn power_of_x() {
        let degree = DEGREE;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(t)
                .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
        for i in 0..bfv_params.max_level() {
            let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
            rlk_keys.insert(i, rlk);
        }

        let k_degree = 256;

        let X = Uniform::new(0u64, 65537)
            .sample_iter(rng.clone())
            .take(degree)
            .collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd(), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        // let mut now = std::time::SystemTime::now();
        let powers_ct = powers_of_x(&ct, k_degree, &bfv_params, &rlk_keys, 0);
        // println!(" Final power of X {:?}", now.elapsed().unwrap());

        // plaintext evaluation of X
        let t_ctx = Arc::new(Context::new(&[t], degree).unwrap());
        let pt_poly = Poly::try_convert_from(&X, &t_ctx, false, Representation::Ntt).unwrap();
        let powers = powers_of_x_poly(&t_ctx, &pt_poly, k_degree);

        izip!(powers.iter(), powers_ct.iter()).for_each(|(p, ct)| {
            let pt = bfv_sk.try_decrypt(ct).unwrap();
            let pt = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(pt, p.coefficients().to_slice().unwrap());
        })
    }

    #[test]
    fn test_pv_unpack() {
        let degree = 8;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(t)
                .set_moduli(&MODULI_OMR[MODULI_OMR.len() - 2..])
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

        let distr = Uniform::new(0u64, t);
        let values = distr.sample_iter(rng.clone()).take(degree).collect_vec();
        let pt = Plaintext::try_encode(&values, Encoding::simd(), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let mut now = std::time::SystemTime::now();
        let unpacked_cts = pv_unpack(&bfv_params, &rot_keys, &ct);
        println!("pv_unpack took {:?}", now.elapsed());

        unpacked_cts.iter().enumerate().for_each(|(index, u_ct)| {
            let pt = bfv_sk.try_decrypt(&u_ct).unwrap();
            let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(v, vec![values[index]; degree]);
        });
    }

    #[test]
    fn test_pv_compress() {
        let degree = 8;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(t)
                // .set_moduli(&MODULI_OMR[MODULI_OMR.len() - 2..])
                .set_moduli_sizes(&[30, 50, 60])
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
        let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1);
        let ct_capacity = degree as u32 * pt_bits;

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
        unsafe {
            let noise = bfv_sk.measure_noise(&pv_compressed);
            dbg!(noise);
        }
        let pv_compressed = bfv_sk.try_decrypt(&pv_compressed).unwrap();
        let mut pv_compressed = Vec::<u64>::try_decode(&pv_compressed, Encoding::simd()).unwrap();
        // dbg!(&pv_compressed);
        let final_vals = pv_compressed
            .iter_mut()
            .flat_map(|v| {
                let mut bits = vec![];
                for i in 0..16 {
                    bits.push(*v & 1);
                    *v >>= 1;
                }
                bits
            })
            .collect_vec();

        // println!("{:?}", final_vals);
        // println!("{:?}", pv);

        assert_eq!(final_vals[..pv.len()], pv);
    }
}
