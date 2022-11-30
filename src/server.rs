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
            // let mut now = std::time::SystemTime::now();
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
                        // now = std::time::SystemTime::now();

                        base.mod_switch_to_next_level();
                        num_mod[base_deg - 1] += 1;

                        // println!(
                        //     "Mod level {} {:?}",
                        //     num_mod[base_deg - 1],
                        //     now.elapsed().unwrap()
                        // );
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
    // let mut now = std::time::SystemTime::now();
    // all k_powers_of_x are at level 4
    let mut k_powers_of_x = powers_of_x(input, 256, bfv_params, rlk_keys, 0);
    // println!(" k_powers_of_x {:?}", now.elapsed().unwrap());

    // now = std::time::SystemTime::now();
    // m = x^256
    // all k_powers_of_m are at level 8
    let k_powers_of_m = powers_of_x(&k_powers_of_x[255], 256, bfv_params, rlk_keys, 4);
    // println!(" k_powers_of_m {:?}", now.elapsed().unwrap());

    for p in &mut k_powers_of_x {
        for _ in 0..4 {
            p.mod_switch_to_next_level();
        }
    }

    let coeffs = read_range_coeffs("params.bin");

    let mut total = Ciphertext::zero(bfv_params);
    for i in 0..256 {
        let mut sum: Ciphertext = Ciphertext::zero(bfv_params);
        let mut flag = false;

        // now = std::time::SystemTime::now();
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            let c_pt = Plaintext::try_encode(
                &vec![c; bfv_params.degree()],
                Encoding::simd_at_level(8),
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
        // println!(" sum for index {} {:?}", i, now.elapsed().unwrap());

        // now = std::time::SystemTime::now();
        // match modulus
        // for _ in 0..4 {
        //     sum.mod_switch_to_next_level();
        // }
        // println!(
        //     " switching down by 4 mods {} {:?}",
        //     i,
        //     now.elapsed().unwrap()
        // );

        // now = std::time::SystemTime::now();
        if i != 0 {
            // mul and add
            let mut p = &k_powers_of_m[i - 1] * &sum;
            let rlk = rlk_keys.get(&8).unwrap();
            rlk.relinearizes(&mut p).unwrap();

            total += &p
        } else {
            total = sum;
        }
        // println!(" total calc {} {:?}", i, now.elapsed().unwrap());
    }

    total = -total;
    // total.mod_switch_to_next_level();

    total
}

/// decrypt pvw cts
pub fn decrypt_pvw(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &Arc<PVWParameters>,
    mut ct_pvw_sk: Vec<Ciphertext>,
    rotation_key: GaloisKey,
    clues: Vec<PVWCiphertext>,
) -> Vec<Ciphertext> {
    debug_assert!(ct_pvw_sk.len() == pvw_params.ell);

    let sec_len = pvw_params.n.next_power_of_two();
    debug_assert!(((bfv_params.degree() / sec_len) * pvw_params.n) >= clues.len());

    // computes sk * a
    let mut sk_a = vec![Ciphertext::zero(bfv_params); pvw_params.ell];
    for i in 0..sec_len {
        let mut values = vec![0u64; clues.len()];
        for j in 0..clues.len() {
            let index = (i + j) % sec_len;

            if index >= pvw_params.n {
                values[j] = 0;
            } else {
                values[j] = clues[j].a[index];
            }
        }
        let values_pt = Plaintext::try_encode(&values, Encoding::simd(), bfv_params).unwrap();

        for ell_index in 0..pvw_params.ell {
            let product = &ct_pvw_sk[ell_index] * &values_pt;
            sk_a[ell_index] = &sk_a[ell_index] + &product;

            // rotate left by 1
            ct_pvw_sk[ell_index] = rotation_key.relinearize(&ct_pvw_sk[ell_index]).unwrap();
        }
    }

    // d = b - sk * a
    let mut d = vec![Ciphertext::zero(bfv_params); pvw_params.ell];
    for ell_index in 0..pvw_params.ell {
        let mut b_ell = vec![0u64; clues.len()];
        for i in 0..clues.len() {
            b_ell[i] = clues[i].b[ell_index];
        }
        let b_ell = Plaintext::try_encode(&b_ell, Encoding::simd(), bfv_params).unwrap();

        d[ell_index] = &(-&sk_a[ell_index]) + &b_ell;
    }

    d
}

/// Computes sum of all slot values
/// of `ct` such that each slot stores
/// the final sum.
/// That is translates from [0,1,2,3] -> [6, 6, 6, 6]
pub fn inner_sum(
    bfv_params: &Arc<BfvParameters>,
    ct: &Ciphertext,
    rot_keys: &HashMap<usize, GaloisKey>,
) -> Ciphertext {
    let mut inner_sum = ct.clone();
    let mut i = 1;
    while i < bfv_params.degree() / 2 {
        let temp = rot_keys.get(&i).unwrap().relinearize(&inner_sum).unwrap();
        inner_sum = &inner_sum + &temp;
        i *= 2;
    }
    inner_sum = &inner_sum
        + &rot_keys
            .get(&(bfv_params.degree() * 2 - 1))
            .unwrap()
            .relinearize(&inner_sum)
            .unwrap();

    inner_sum
}

/// unpacks pv_ct encrypting {0,1}
/// in `poly_degree` coefficients
/// into `poly_degree` ciphertexts
/// encrypting each coefficient value.
///
/// TODO: enable batch processing since
/// unpacking 2**15 ciphertexts in one
/// go is huge load on memory
pub fn pv_unpack(
    bfv_params: &Arc<BfvParameters>,
    rot_keys: &HashMap<usize, GaloisKey>,
    pv_ct: &mut Ciphertext,
    expansion_size: usize,
    offset: usize,
    sk: &SecretKey,
) -> Vec<Ciphertext> {
    // let mut now = std::time::SystemTime::now();

    let mut select = vec![0u64; bfv_params.degree()];
    select[0] = 1;
    let select_pt = Plaintext::try_encode(&select, Encoding::simd(), bfv_params).unwrap();

    let mut pv = vec![];
    for i in offset..(expansion_size + offset) {
        if i != 0 {
            if i == (bfv_params.degree() / 2) {
                // rotate column when offset is halfway
                *pv_ct = rot_keys
                    .get(&(bfv_params.degree() * 2 - 1))
                    .unwrap()
                    .relinearize(&pv_ct)
                    .unwrap();
                *pv_ct = rot_keys.get(&1).unwrap().relinearize(&pv_ct).unwrap();
            } else {
                *pv_ct = rot_keys.get(&1).unwrap().relinearize(&pv_ct).unwrap();
            }
        }

        let mut value_vec = &*pv_ct * &select_pt;
        dbg!(
            Vec::<u64>::try_decode(&sk.try_decrypt(&value_vec).unwrap(), Encoding::simd()).unwrap()
        );
        unsafe {
            dbg!(sk.measure_noise(&pv_ct));
        }
        value_vec = inner_sum(bfv_params, &value_vec, rot_keys);
        pv.push(value_vec);
    }

    pv
}

pub fn pv_compress(
    bfv_params: &Arc<BfvParameters>,
    pv: &Vec<Ciphertext>,
    level: usize,
    to_compress_len: usize,
    offset: usize,
    compressed_pv: &mut Ciphertext,
) {
    debug_assert!(pv.len() == to_compress_len);

    let log_t = 64 - bfv_params.plaintext().leading_zeros() - 1;

    for i in 0..to_compress_len {
        let index = ((i + offset) as f32 / log_t as f32).floor() as usize;
        let bit_index = ((i + offset) as u32) % log_t;

        let mut select = vec![0u64; bfv_params.degree()];
        select[index] = 1 << bit_index;
        let select_pt =
            Plaintext::try_encode(&select, Encoding::simd_at_level(level), &bfv_params).unwrap();

        // pv_i * select_i
        let product = &pv[i] * &select_pt;

        *compressed_pv += &product;
    }
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
    use crate::client::gen_pvw_sk_cts;
    use crate::utils::{powers_of_x_poly, range_fn_poly, rot_to_exponent};
    use crate::{DEGREE, MODULI_OMR, MODULI_OMR_PT};
    use itertools::izip;

    #[test]
    fn test_decrypt_pvw() {
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

        let pvw_params = Arc::new(PVWParameters {
            n: 450,
            m: 100,
            ell: 4,
            variance: 2,
            q: 65537,
        });
        let pvw_sk = PVWSecretKey::gen_sk(&pvw_params);
        let pvw_pk = pvw_sk.public_key();

        let pvw_sk_cts = gen_pvw_sk_cts(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk);

        // encrypt values
        let mut clues = vec![];
        let mut rng = thread_rng();
        for i in 0..DEGREE {
            let m = Uniform::new(0, 2)
                .sample_iter(rng.clone())
                .take(pvw_params.ell)
                .collect_vec();
            clues.push(m);
        }

        let clues_ct = clues
            .iter()
            .map(|c| pvw_pk.encrypt(c.to_vec()))
            .collect_vec();

        let mut rng = thread_rng();
        let rot_key =
            GaloisKey::new(&bfv_sk, rot_to_exponent(1, &bfv_params), 0, 0, &mut rng).unwrap();

        let now = std::time::SystemTime::now();
        let res = decrypt_pvw(&bfv_params, &pvw_params, pvw_sk_cts, rot_key, clues_ct);
        println!("decrypt_pvw took {:?}", now.elapsed());

        let res = res
            .iter()
            .map(|c| {
                let p = bfv_sk.try_decrypt(&c).unwrap();
                Vec::<u64>::try_decode(&p, Encoding::simd()).unwrap()[..clues.len()].to_vec()
            })
            .collect_vec();

        let mut count = 0;
        for i in 0..pvw_params.ell {
            for j in 0..clues.len() {
                let bit = (res[i][j] >= (pvw_params.q / 2)) as u64;
                if bit != clues[j][i] {
                    count += 1;
                }
            }
        }
        assert!(count == 0);
    }

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
                .set_moduli(&MODULI_OMR[..])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        let mut now = std::time::SystemTime::now();
        let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
        for i in 0..bfv_params.max_level() {
            let rlk = RelinearizationKey::new_leveled(&bfv_sk, i, i, &mut rng).unwrap();
            rlk_keys.insert(i, rlk);
        }
        println!("RLK gen took {:?}", now.elapsed().unwrap());

        let X = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(poly_degree)
            .collect_vec();
        let X_bin = X.iter().map(|v| (*v >= 32768u64) as u64).collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd(), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        now = std::time::SystemTime::now();
        let res_ct = range_fn(&bfv_params, &ct, &rlk_keys);
        let res_pt = bfv_sk.try_decrypt(&res_ct).unwrap();
        println!(" Range fn ct {:?}", now.elapsed().unwrap());

        assert_eq!(
            Vec::<u64>::try_decode(&res_pt, Encoding::simd()).unwrap(),
            X_bin
        );

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
                // .set_moduli(&MODULI_OMR[MODULI_OMR.len() - 3..])
                .set_moduli_sizes(&[60, 60, 60])
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

        let mut ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let mut now = std::time::SystemTime::now();
        let batch_size = 8;
        let mut offset = 0;
        let mut unpacked_cts: Vec<Ciphertext> = vec![];
        for i in 0..(degree / batch_size) {
            now = std::time::SystemTime::now();
            let res = pv_unpack(&bfv_params, &rot_keys, &mut ct, batch_size, offset, &bfv_sk);
            println!("pv_unpack took {:?}", now.elapsed());

            offset += batch_size;
            unpacked_cts.extend(res);
        }
        println!("{:?}", values);
        unpacked_cts.iter().enumerate().for_each(|(index, u_ct)| {
            let pt = bfv_sk.try_decrypt(&u_ct).unwrap();
            let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(v, vec![values[index]; degree]);
        });
    }

    #[test]
    fn test_inner_sum() {
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

        let values = rng
            .clone()
            .sample_iter(Uniform::new(0, t))
            .take(degree)
            .collect_vec();
        let values_pt = Plaintext::try_encode(&values, Encoding::simd(), &bfv_params).unwrap();

        let ct = bfv_sk.try_encrypt(&values_pt, &mut rng).unwrap();

        // construct rot keys
        let mut i = 1;
        let mut rot_keys = HashMap::<usize, GaloisKey>::new();
        while i < degree {
            rot_keys.insert(
                i,
                GaloisKey::new(
                    &bfv_sk,
                    rot_to_exponent(i as u64, &bfv_params),
                    0,
                    0,
                    &mut rng,
                )
                .unwrap(),
            );
            i *= 2;
        }
        rot_keys.insert(
            degree * 2 - 1,
            GaloisKey::new(&bfv_sk, degree * 2 - 1, 0, 0, &mut rng).unwrap(),
        );

        let ct2 = inner_sum(&bfv_params, &ct, &rot_keys);
        let sum_vec =
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&ct2).unwrap(), Encoding::simd()).unwrap();
        let sum: u64 = values.iter().sum();
        assert!(sum_vec == vec![sum % t; degree]);
    }

    #[test]
    fn test_pv_compress() {
        let degree = 512;
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

        // Packing capacity in bits: log_t * D
        let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1);
        let total_capacity = degree as u32 * pt_bits;

        let cts_count = pt_bits;
        let distr = Uniform::new(0u64, 2);
        let batch_size = 32;
        let mut offset = 0;
        let mut comressed_pv = Ciphertext::zero(&bfv_params);
        let mut pv_values = vec![];

        // let's compress to max capacity
        for i in 0..cts_count {
            // we are compressing in batches
            for j in 0..(degree / batch_size) {
                // gen random pv values for batch
                let batch_cts: (Vec<u64>, Vec<Ciphertext>) = (0..batch_size)
                    .into_iter()
                    .map(|_| {
                        let random = rng.sample(distr);
                        let pt = Plaintext::try_encode(
                            &vec![random; bfv_params.degree()],
                            Encoding::simd(),
                            &bfv_params,
                        )
                        .unwrap();
                        (random, bfv_sk.try_encrypt(&pt, &mut rng).unwrap())
                    })
                    .unzip();

                pv_values.extend(batch_cts.0);

                pv_compress(
                    &bfv_params,
                    &batch_cts.1,
                    0,
                    batch_size,
                    offset,
                    &mut comressed_pv,
                );

                offset += batch_size;
            }
        }

        let compressed_vals = bfv_sk.try_decrypt(&comressed_pv).unwrap();
        let compressed_vals = Vec::<u64>::try_decode(&compressed_vals, Encoding::simd()).unwrap();
        let uncompressed: Vec<_> = compressed_vals
            .into_iter()
            .flat_map(|mut v| {
                let mut vals = vec![];
                for _ in 0..pt_bits {
                    vals.push(v & 1);
                    v >>= 1;
                }
                vals
            })
            .collect();

        assert!(uncompressed == pv_values);
    }
}
