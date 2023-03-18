use crate::pvw::{PvwCiphertext, PvwParameters};
use crate::utils::{assign_buckets, read_range_coeffs};
use crate::{CT_SPAN_COUNT, DEGREE, GAMMA, M, MODULI_OMR, MODULI_OMR_PT, M_ROW_SPAN, SET_SIZE};
use byteorder::{ByteOrder, LittleEndian};
use fhe::bfv::{
    self, BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, EvaluationKey, Multiplicator,
    Plaintext, RelinearizationKey, SecretKey,
};
use fhe_math::zq::Modulus;
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder};
use itertools::{izip, Itertools};
use rand::{thread_rng, Rng, SeedableRng};
use rand_chacha::ChaChaRng;
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::vec;

#[derive(PartialEq, Debug)]
pub struct DetectionKey {
    pub ek1: EvaluationKey,
    pub ek2: EvaluationKey,
    pub ek3: EvaluationKey,
    pub rlk_keys: HashMap<usize, RelinearizationKey>,
    pub pvw_sk_cts: [Ciphertext; 4],
}

pub struct Digest1 {
    pub cts: Vec<Ciphertext>,
}

pub struct Digest2 {
    pub cts: Vec<Ciphertext>,
    pub seed: [u8; 32],
}

pub fn default_bfv() -> BfvParameters {
    BfvParametersBuilder::new()
        .set_degree(DEGREE)
        .set_plaintext_modulus(MODULI_OMR_PT[0])
        .set_moduli(MODULI_OMR)
        .build()
        .unwrap()
}

pub fn default_pvw() -> PvwParameters {
    PvwParameters::default()
}

pub fn mul_many(
    values: &mut Vec<Ciphertext>,
    multiplicators: &HashMap<usize, Multiplicator>,
    mut level_offset: usize,
) {
    let mut counter = 0usize;
    while values.len() != 1 {
        let mut mid = values.len() / 2;

        for i in 0..mid {
            values[i] = multiplicators
                .get(&level_offset)
                .unwrap()
                .multiply(&values[i], &values[mid + i])
                .unwrap();
        }

        if values.len() % 2 != 0 {
            values[mid] = values.last().unwrap().clone();
            mid += 1;
        }
        values.truncate(mid);

        counter += 1;
        if counter & 1 == 1 {
            level_offset += 1;
            for i in 0..values.len() {
                values[i].mod_switch_to_next_level();
            }
        }
    }
}

pub fn powers_of_x(
    input: &Ciphertext,
    degree: usize,
    params: &Arc<BfvParameters>,
    multiplicators: &HashMap<usize, Multiplicator>,
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
                        res = multiplicators
                            .get(&(num_mod[base_deg - 1] + mod_offset))
                            .unwrap()
                            .multiply(&res, &base)
                            .unwrap();

                        // now = std::time::SystemTime::now();
                        while num_mod[res_deg - 1]
                            < ((res_deg as f32).log2() / 2f32).ceil() as usize
                        {
                            res.mod_switch_to_next_level();
                            num_mod[res_deg - 1] += 1;
                        }
                        // println!(
                        //     "res.mod_switch_to_next_level(); {} {:?}",
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

                    base = multiplicators
                        .get(&(num_mod[base_deg - 1] + mod_offset))
                        .unwrap()
                        .multiply(&base, &base)
                        .unwrap();

                    // now = std::time::SystemTime::now();
                    while num_mod[base_deg - 1] < ((base_deg as f32).log2() / 2f32).ceil() as usize
                    {
                        base.mod_switch_to_next_level();
                        num_mod[base_deg - 1] += 1;
                    }
                    // println!(
                    //     "base.mod_switch_to_next_level(); {} {:?}",
                    //     num_mod[base_deg - 1],
                    //     now.elapsed()
                    // );

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
    multiplicators: &HashMap<usize, Multiplicator>,
    level_offset: usize,
    sk: &SecretKey,
) -> Ciphertext {
    let mut now = std::time::SystemTime::now();
    // all k_powers_of_x are at level `level_offset` + 4
    let mut k_powers_of_x = powers_of_x(input, 256, bfv_params, multiplicators, level_offset);
    println!(" k_powers_of_x {:?}", now.elapsed().unwrap());

    now = std::time::SystemTime::now();
    // m = x^256
    // all k_powers_of_m are at level `level_offset` + 8
    let k_powers_of_m = powers_of_x(
        &k_powers_of_x[255],
        256,
        bfv_params,
        multiplicators,
        level_offset + 4,
    );

    for p in &mut k_powers_of_x {
        for _ in 0..4 {
            p.mod_switch_to_next_level();
        }
    }

    let coeffs = read_range_coeffs();

    let mut total = Ciphertext::zero(bfv_params);
    for i in 0..256 {
        let mut sum: Ciphertext = Ciphertext::zero(bfv_params);
        let mut flag = false;

        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];

            let c_pt = Plaintext::try_encode(
                &vec![c; bfv_params.degree()],
                Encoding::simd_at_level(level_offset + 8),
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

        if i != 0 {
            // mul and add
            total += &multiplicators
                .get(&(level_offset + 8))
                .unwrap()
                .multiply(&k_powers_of_m[i - 1], &sum)
                .unwrap();
        } else {
            total = sum;
        }
    }

    let one = Plaintext::try_encode(
        &vec![1u64; bfv_params.degree()],
        Encoding::simd_at_level(level_offset + 8),
        bfv_params,
    )
    .unwrap();
    total = -total;
    total += &one;
    total.mod_switch_to_next_level();

    total
}

/// decrypt pvw cts
pub fn decrypt_pvw(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &PvwParameters,
    mut ct_pvw_sk: Vec<Ciphertext>,
    rotation_key: &EvaluationKey,
    clues: &[PvwCiphertext],
    sk: &SecretKey,
) -> Vec<Ciphertext> {
    debug_assert!(ct_pvw_sk.len() == pvw_params.ell);

    let sec_len = pvw_params.n.next_power_of_two();

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
            sk_a[ell_index] += &product;

            ct_pvw_sk[ell_index] = rotation_key
                .rotates_columns_by(&ct_pvw_sk[ell_index], 1)
                .unwrap();
        }
    }

    // let mut now = std::time::Instant::now();
    for p in &mut sk_a {
        *p = -&*p;
    }
    // println!("neg sk_a: {:?}", now.elapsed());

    // sk_a = b - sk * a
    let q = Modulus::new(pvw_params.q).unwrap();
    for ell_index in 0..pvw_params.ell {
        let mut b_ell = vec![0u64; clues.len()];
        for i in 0..clues.len() {
            // We shift decrypted value by q/4 so that if
            // it's encryption of `0`, then resulting value
            // is within [-r, r].
            // Note that in range function we output 1 (i.e
            // clue is pertinent) if decrypted value is within
            // [-r, r]
            b_ell[i] = q.sub(clues[i].b[ell_index], q.modulus() / 4);
        }
        let b_ell = Plaintext::try_encode(&b_ell, Encoding::simd(), bfv_params).unwrap();

        sk_a[ell_index] += &b_ell;

        sk_a[ell_index].mod_switch_to_next_level();
    }

    sk_a
}

/// unpacks pv_ct encrypting {0,1}
/// in `poly_degree` coefficients
/// into `poly_degree` ciphertexts
/// encrypting each coefficient value.
#[allow(clippy::too_many_arguments)]
pub fn pv_unpack(
    bfv_params: &Arc<BfvParameters>,
    rot_keys: &EvaluationKey,
    inner_sum_rot_keys: &EvaluationKey,
    pv_ct: &mut Ciphertext,
    expansion_size: usize,
    offset: usize,
    sk: &SecretKey,
    level: usize,
) -> Vec<Ciphertext> {
    // let mut now = std::time::SystemTime::now();

    let mut select = vec![0u64; bfv_params.degree()];
    select[0] = 1;
    let select_pt =
        Plaintext::try_encode(&select, Encoding::simd_at_level(level), bfv_params).unwrap();

    let mut pv = vec![];
    for i in offset..(expansion_size + offset) {
        if i != 0 {
            if i == (bfv_params.degree() / 2) {
                // rotate rows when offset is halfway
                *pv_ct = rot_keys.rotates_rows(pv_ct).unwrap();
            }
            *pv_ct = rot_keys.rotates_columns_by(pv_ct, 1).unwrap();
        }

        let mut value_vec = &*pv_ct * &select_pt;

        value_vec.mod_switch_to_next_level();
        value_vec.mod_switch_to_next_level();

        value_vec = inner_sum_rot_keys.computes_inner_sum(&value_vec).unwrap();

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
    sk: &SecretKey,
) {
    debug_assert!(pv.len() == to_compress_len);

    let log_t = 64 - bfv_params.plaintext().leading_zeros() - 1;
    let mut select = vec![0u64; bfv_params.degree()];

    for i in 0..to_compress_len {
        let index = ((i + offset) as f32 / log_t as f32).floor() as usize;
        let bit_index = ((i + offset) as u32) % log_t;

        select[index] = 1 << bit_index;
        // FIXME: performing forward NTT for same PT again and again isn't optimal
        let select_pt =
            Plaintext::try_encode(&select, Encoding::simd_at_level(level), &bfv_params).unwrap();

        // pv_i * select_i
        let product = &pv[i] * &select_pt;

        *compressed_pv += &product;

        select[index] = 0;
    }
}

/// Returns bucket assignments corresponding to each
/// pertinent payload scaled by corresponding weight
///
/// That is, for each payload, `PV[i] * a`, where `a` encodes
/// `payload * weight` at respective bucket slots.
#[allow(clippy::too_many_arguments)]
pub fn pv_weights(
    assigned_buckets: &Vec<Vec<usize>>,
    assigned_weights: &Vec<Vec<u64>>,
    pv: &Vec<Ciphertext>,
    payloads: &[Vec<u64>],
    m_row_span: usize,
    bfv_params: &Arc<BfvParameters>,
    batch_size: usize,
    ct_span_count: usize,
    gamma: usize,
    offset: usize,
    level: usize,
) -> Vec<Vec<Ciphertext>> {
    let degree = bfv_params.degree();
    let q_mod = bfv_params.plaintext();
    let modulus = Modulus::new(q_mod).unwrap();

    let mut products = vec![vec![Ciphertext::zero(bfv_params); ct_span_count]; batch_size];
    for batch_index in 0..batch_size {
        let mut pt = vec![vec![0u64; degree]; ct_span_count];
        for i in 0..gamma {
            // think of single bucket as spanning across `m_row_span`
            // no. of rows of plaintext vector
            let start_row = assigned_buckets[batch_index + offset][i] * m_row_span;
            let weight = assigned_weights[batch_index + offset][i];
            for payload_index in 0..m_row_span {
                let row = start_row + payload_index;
                let span_col = row / degree;
                let span_row = row % degree;

                // payload chunk * weight
                pt[span_col][span_row] = modulus.add(
                    pt[span_col][span_row],
                    modulus.mul(payloads[batch_index + offset][payload_index], weight),
                )
            }
        }

        let product = pt
            .iter()
            .map(|col| {
                let p = Plaintext::try_encode(col, Encoding::simd_at_level(level), &bfv_params)
                    .unwrap();
                &pv[batch_index] * &p
            })
            .collect_vec();

        products[batch_index] = product;
    }

    products
}

pub fn finalise_combinations(
    pv_weights: &[Vec<Ciphertext>],
    rhs: &mut [Ciphertext],
    m: usize,
    degree: usize,
    m_row_span: usize,
) {
    // m_row_span = row span of a single bucket
    // therefore, m * m_row_span = total rows required
    //
    debug_assert!(m * m_row_span <= rhs.len() * degree);

    pv_weights.iter().for_each(|pv_by_w| {
        debug_assert!(pv_by_w.len() == rhs.len());
        izip!(pv_by_w.iter(), rhs.iter_mut()).for_each(|(pv, rh)| {
            *rh += pv;
        });
    });
}

/// Does the following:
/// 1. Calls `decrypt_pvw` to decrypt clues values    
/// 2. Calls `range_fn` to reduce decrypted value to either 0 or 1.
#[allow(clippy::too_many_arguments)]
pub fn phase1(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &PvwParameters,
    ct_pvw_sk: &[Ciphertext],
    rotation_key: &EvaluationKey,
    multiplicators: &HashMap<usize, Multiplicator>,
    clues: &[PvwCiphertext],
    sk: &SecretKey,
) -> Vec<Ciphertext> {
    let set_size = clues.len();
    let degree = bfv_params.degree();

    println!("Phase 1 chunk count {}", set_size / degree);

    let res: Vec<Ciphertext> = clues
        .par_chunks(degree)
        .map(|c| {
            //

            // level 0
            let mut now = std::time::Instant::now();
            let decrypted_clues = decrypt_pvw(
                bfv_params,
                pvw_params,
                ct_pvw_sk.to_vec(),
                rotation_key,
                c,
                sk,
            );
            println!("Decrypt_pvw_time {:?}", now.elapsed());
            // assert!(decrypted_clues.len() == pvw_params.ell);

            // level 1; decryption consumes 1
            now = std::time::Instant::now();
            let mut ranged_decrypted_clues = decrypted_clues
                .iter()
                .map(|d| range_fn(bfv_params, d, multiplicators, 1, sk))
                .collect_vec();
            println!("range time {:?}", now.elapsed());

            // level 10; range fn consumes 9
            now = std::time::Instant::now();
            mul_many(&mut ranged_decrypted_clues, multiplicators, 10);
            println!("mul_many time {:?}", now.elapsed());
            // assert!(ranged_decrypted_clues.len() == 1);
            // level 11; mul_many consumes 1

            ranged_decrypted_clues[0].clone()
        })
        .collect();

    res
}

/// Does the following on all cts in batches:
/// 1. calls `pv_unpack`
/// 2. compresses unpacked ct into PV ct
/// 3. assigns weights to buckets
#[allow(clippy::too_many_arguments)]
pub fn phase2(
    assigned_buckets: &Vec<Vec<usize>>,
    assigned_weights: &Vec<Vec<u64>>,
    bfv_params: &Arc<BfvParameters>,
    rot_keys: &EvaluationKey,
    inner_sum_rot_keys: &EvaluationKey,
    pertinency_cts: &mut [Ciphertext],
    payloads: &[Vec<u64>],
    batch_size: usize,
    degree: usize,
    level: usize,
    set_size: usize,
    gamma: usize,
    ct_span_count: usize,
    m: usize,
    m_row_span: usize,
    sk: &SecretKey,
) -> (Ciphertext, Vec<Ciphertext>) {
    debug_assert!(set_size % batch_size == 0);
    // debug_assert!(set_size == degree * pertinency_cts.len()); // TODO: relax this from == to <=

    // unsafe {
    //     pertinency_cts.iter().for_each(|p| {
    //         println!("Phase2: pertinency_cts {}", sk.measure_noise(p).unwrap());
    //     })
    // }

    let (mut pertinency_vectors, mut rhs): (Vec<Ciphertext>, Vec<Vec<Ciphertext>>) = pertinency_cts
        .par_iter_mut()
        .enumerate()
        .map(|(core_index, p_ct)| {
            println!("Phase2...core:{core_index}");

            let mut pv = Ciphertext::zero(bfv_params);
            let compress_offset = core_index * degree;
            let mut offset = 0usize;

            let mut rhs = vec![Ciphertext::zero(bfv_params); ct_span_count];

            for i in 0..(1) {
                // level 11
                let unpacked_cts = pv_unpack(
                    bfv_params,
                    rot_keys,
                    inner_sum_rot_keys,
                    p_ct,
                    batch_size,
                    offset,
                    sk,
                    level,
                );

                unpacked_cts.iter().enumerate().for_each(|(index, ct)| {
                    let p = Vec::<u64>::try_decode(&sk.try_decrypt(ct).unwrap(), Encoding::simd())
                        .unwrap();
                    println!(
                        "unpacked {}: {}",
                        index + (i * batch_size),
                        p.iter().product::<u64>()
                    );
                });

                // level 13; unpacking consumes 2 levels
                pv_compress(
                    bfv_params,
                    &unpacked_cts,
                    level + 2,
                    batch_size,
                    offset + compress_offset,
                    &mut pv,
                    sk,
                );

                let pv_we = pv_weights(
                    assigned_buckets,
                    assigned_weights,
                    &unpacked_cts,
                    payloads,
                    m_row_span,
                    bfv_params,
                    batch_size,
                    ct_span_count,
                    gamma,
                    offset + compress_offset,
                    level + 2,
                );

                finalise_combinations(&pv_we, &mut rhs, m, degree, m_row_span);

                offset += batch_size;
            }

            (pv, rhs)
        })
        .collect();

    let mut pv = Ciphertext::zero(bfv_params);
    pertinency_vectors.iter().for_each(|p| {
        pv += p;
    });
    let mut rhs_total = vec![Ciphertext::zero(bfv_params); ct_span_count];
    rhs.iter().for_each(|r| {
        izip!(rhs_total.iter_mut(), r.iter()).for_each(|(rt, r)| {
            *rt += r;
        });
    });

    unsafe {
        println!("pv noise{}", sk.measure_noise(&pv).unwrap());
    }

    pv.mod_switch_to_last_level();
    for r in &mut rhs_total {
        r.mod_switch_to_last_level();
    }

    unsafe {
        println!(
            "pv after mod switch noise: {}",
            sk.measure_noise(&pv).unwrap()
        );
    }

    (pv, rhs_total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::{construct_lhs, construct_rhs, gen_pvw_sk_cts, pv_decompress};
    use crate::pvw::PvwSecretKey;
    use crate::utils::{
        assign_buckets, deserialize_detection_key, deserialize_digest2, gen_clues,
        gen_detection_key, gen_paylods, gen_pertinent_indices, gen_rlk_keys,
        gen_rot_keys_inner_product, gen_rot_keys_pv_selector, get_mapping,
        map_rlks_to_multiplicators, powers_of_x_poly, range_fn_poly, serialize_detection_key,
        solve_equations,
    };
    use crate::{DEGREE, MODULI_OMR, MODULI_OMR_PT, OMR_S_SIZES};
    use fhe::bfv::EvaluationKeyBuilder;
    use fhe_math::rq::traits::TryConvertFrom;
    use fhe_math::rq::{Context, Poly, Representation};
    use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, FheEncrypter, Serialize};
    use itertools::izip;
    use rand::distributions::Uniform;
    use rand::prelude::Distribution;
    use rand::{thread_rng, Rng};
    use std::io::Write;
    use std::path::PathBuf;
    use std::str::FromStr;

    #[test]
    fn test_phase1_and_phase2() {
        let mut rng = thread_rng();
        // let f = [28, 39, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60];
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_moduli(MODULI_OMR)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                // .set_variance(5)
                .build()
                .unwrap(),
        );
        let pvw_params = Arc::new(PvwParameters::default());

        println!("Bfv Params{:?}", bfv_params);
        println!("Bfv moduli sizes{:?}", bfv_params.moduli_sizes());

        let bfv_sk = {
            let bytes = std::fs::read("generated/keys/bfvPrivKeyRs").unwrap();
            let key: Vec<i64> = bincode::deserialize(&bytes).unwrap();
            SecretKey::new(key, &bfv_params)
        };
        let pvw_sk = {
            let bytes = std::fs::read("generated/keys/cluePrivKey").unwrap();
            PvwSecretKey::from_bytes(&bytes, &pvw_params)
        };
        let pvw_pk = Arc::new(pvw_sk.public_key(&mut rng));
        let detection_key = {
            let bytes = std::fs::read("generated/keys/detectionKey").unwrap();
            deserialize_detection_key(&bfv_params, &bytes)
        };

        // let bfv_sk = Arc::new(SecretKey::random(&bfv_params, &mut rng));
        // let dummy_sk = Arc::new(SecretKey::random(&bfv_params, &mut rng));
        // let pvw_sk = Arc::new(PvwSecretKey::random(&pvw_params, &mut rng));
        // let pvw_pk = Arc::new(pvw_sk.public_key(&mut rng));

        let set_size = SET_SIZE;
        let k = 50;
        let m = k * 2;
        let gamma = 5;
        let data_size_in_bytes = 256;
        let payload_size = data_size_in_bytes / 2; // t = 65537 ~ 2 ** 16 ~ 16 bits
        let ct_span_count = (((m * payload_size) as f64) / (DEGREE as f64)).ceil() as usize;
        dbg!(ct_span_count, payload_size);

        // gen clues
        // let mut pertinent_indices = gen_pertinent_indices(50, DEGREE);
        let mut pertinent_indices = vec![1, 2, 3];
        pertinent_indices.sort();
        println!("Pertinent indices: {:?}", pertinent_indices);

        let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, DEGREE);
        let payloads = gen_paylods(DEGREE);
        // assert!(clues.len() == set_size);
        assert!(payloads.len() == clues.len());
        println!("Clues generated");

        let mut rng = thread_rng();

        // let detection_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
        let multiplicators = map_rlks_to_multiplicators(&detection_key.rlk_keys);

        let (assigned_buckets, assigned_weights) =
            assign_buckets(m, gamma, MODULI_OMR_PT[0], set_size, &mut rng);

        println!("Phase 1 starting...");
        let now = std::time::Instant::now();
        let mut phase1_res = phase1(
            &bfv_params,
            &pvw_params,
            &detection_key.pvw_sk_cts,
            &detection_key.ek1,
            &multiplicators,
            &clues,
            &bfv_sk,
        );
        println!("phase1 time: {:?}", now.elapsed());
        let phase1_time = now.elapsed();

        {
            println!("phase1_res len:{}", phase1_res.len());
            let res = Vec::<u64>::try_decode(
                &bfv_sk.try_decrypt(&phase1_res[0]).unwrap(),
                Encoding::simd(),
            )
            .unwrap();
            let mut res_indices = vec![];
            res.iter().enumerate().for_each(|(i, bit)| {
                if *bit == 1 {
                    res_indices.push(i);
                }
            });
            println!("res_indices after phase 1: {:?}", res_indices);
        }

        println!("Phase 2 starting...");
        let (res_pv, res_rhs) = phase2(
            &assigned_buckets,
            &assigned_weights,
            &bfv_params,
            &detection_key.ek2,
            &detection_key.ek3,
            &mut phase1_res,
            &payloads,
            32,
            DEGREE,
            11,
            set_size,
            gamma,
            ct_span_count,
            m,
            payload_size,
            &bfv_sk,
        );
        let end_time = now.elapsed();
        println!(
            "Phase1 took: {:?}; Phase2 took: {:?}",
            phase1_time,
            end_time - phase1_time
        );

        /// CLIENT SIDE
        println!(
            "res_rhs.len(): {}, ct_span_count: {}",
            res_rhs.len(),
            ct_span_count
        );

        let pt = bfv_sk.try_decrypt(&res_pv).unwrap();
        let values = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
        let decompressed_pv = pv_decompress(
            &values,
            (64 - bfv_params.plaintext().leading_zeros() - 1) as usize,
        );

        {
            let mut res_indices = vec![];
            decompressed_pv.iter().enumerate().for_each(|(index, bit)| {
                if *bit == 1 {
                    res_indices.push(index);
                }
            });
            // println!("Expected indices {:?}", pertinent_indices);
            // println!("Res indices      {:?}", res_indices);
            assert_eq!(pertinent_indices, res_indices);
        }

        let lhs = construct_lhs(
            &decompressed_pv,
            assigned_buckets,
            assigned_weights,
            m,
            k,
            gamma,
            set_size,
        );

        // build m * payload_size rows
        let m_rows = res_rhs
            .iter()
            .flat_map(|rh| {
                let pt = bfv_sk.try_decrypt(rh).unwrap();
                Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap()
            })
            .collect_vec();

        let rhs = construct_rhs(&m_rows, m, payload_size, MODULI_OMR_PT[0]);

        let res = solve_equations(lhs, rhs, MODULI_OMR_PT[0]);

        let expected_pertinent_payloads = pertinent_indices
            .iter()
            .map(|index| payloads[*index].clone())
            .collect_vec();

        println!(
            "res[..expected_pertinent_payloads.len()]: {:?}",
            &res[..expected_pertinent_payloads.len()],
        );
        println!(
            "expected_pertinent_payloads: {:?}",
            &expected_pertinent_payloads
        );

        assert_eq!(
            &res[..expected_pertinent_payloads.len()],
            &expected_pertinent_payloads
        );
    }

    #[test]
    fn test_decrypt_pvw() {
        let poly_degree = 1024;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(poly_degree)
                .set_plaintext_modulus(t)
                // .set_moduli_sizes(&vec![
                //     28, 39, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60,
                // ])
                // .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        let pvw_params = Arc::new(PvwParameters {
            n: 450,
            m: 100,
            ell: 4,
            variance: 1.3,
            q: 65537,
        });
        let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
        let pvw_pk = pvw_sk.public_key(&mut rng);

        let pvw_sk_cts = gen_pvw_sk_cts(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);

        // encrypt values
        let mut clues = vec![];
        let mut rng = thread_rng();
        for i in 0..poly_degree {
            let m = Uniform::new(0, 2)
                .sample_iter(rng.clone())
                .take(pvw_params.ell)
                .collect_vec();
            clues.push(m);
        }

        let clues_ct = clues
            .iter()
            .map(|c| pvw_pk.encrypt(c, &mut rng))
            .collect_vec();

        let mut rng = thread_rng();
        // let rot_key =
        //     GaloisKey::new(&bfv_sk, rot_to_exponent(1, &bfv_params), 0, 0, &mut rng).unwrap();
        let rot_key = EvaluationKeyBuilder::new_leveled(&bfv_sk, 0, 0)
            .unwrap()
            .enable_column_rotation(1)
            .unwrap()
            .build(&mut rng)
            .unwrap();

        let now = std::time::SystemTime::now();
        let mut res = decrypt_pvw(
            &bfv_params,
            &pvw_params,
            pvw_sk_cts,
            &rot_key,
            &clues_ct,
            &bfv_sk,
        );
        println!("decrypt_pvw took {:?}", now.elapsed());

        // reduce noise of res cts
        for r in &mut res {
            r.mod_switch_to_next_level();
            unsafe {
                dbg!(bfv_sk.measure_noise(&r));
            }
        }

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
                .set_moduli(&MODULI_OMR[..13])
                .build()
                .unwrap(),
        );
        let pvw_params = Arc::new(PvwParameters::default());

        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
        let mut multiplicators = map_rlks_to_multiplicators(&gen_rlk_keys(&bfv_params, &bfv_sk));

        let X = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(poly_degree)
            .collect_vec();
        let q = Modulus::new(pvw_params.q).unwrap();
        let X_bin = X
            .iter()
            .map(|v| (*v <= 850 || *v >= (q.modulus() - 850)) as u64)
            .collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd_at_level(1), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        let mut now = std::time::SystemTime::now();
        let res_ct = range_fn(&bfv_params, &ct, &multiplicators, 1, &bfv_sk);
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
        let degree = 8;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let ctx = Arc::new(Context::new(&[t], degree, &mut HashMap::default(), true).unwrap());
        let mut X = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(degree)
            .collect_vec();
        let pt_poly = Poly::try_convert_from(&X, &ctx, false, Representation::Ntt).unwrap();

        let now = std::time::SystemTime::now();
        dbg!(range_fn_poly(&ctx, &pt_poly, degree, "params_850.bin"));
        println!(" Range fn poly {:?}", now.elapsed().unwrap());
    }

    #[test]
    fn test_power_of_x() {
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

        let mut multiplicators = map_rlks_to_multiplicators(&gen_rlk_keys(&bfv_params, &bfv_sk));

        let k_degree = 256;

        let X = Uniform::new(0u64, 65537)
            .sample_iter(rng.clone())
            .take(degree)
            .collect_vec();
        let pt = Plaintext::try_encode(&X, Encoding::simd_at_level(1), &bfv_params).unwrap();
        let ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        // let mut now = std::time::SystemTime::now();
        let powers_ct = powers_of_x(&ct, k_degree, &bfv_params, &multiplicators, 1);
        // println!(" Final power of X {:?}", now.elapsed().unwrap());

        // plaintext evaluation of X
        let t_ctx = Arc::new(Context::new(&[t], degree, &mut HashMap::default(), true).unwrap());
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
        let degree = 4096;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();
        dbg!(&MODULI_OMR[MODULI_OMR.len() - 4..]);
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(t)
                .set_moduli(&MODULI_OMR[MODULI_OMR.len() - 4..])
                // .set_moduli_sizes(&[60, 30, 60])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);

        let values = Uniform::new(0u64, t)
            .sample_iter(rng.clone())
            .take(degree)
            .collect_vec();
        let pt = Plaintext::try_encode(&values, Encoding::simd_at_level(1), &bfv_params).unwrap();
        let mut ct: Ciphertext = bfv_sk.try_encrypt(&pt, &mut rng).unwrap();

        // rotation keys
        let ct_level = 1;
        let mut rot_keys =
            gen_rot_keys_inner_product(&bfv_params, &bfv_sk, ct_level, ct_level - 1, &mut rng);
        let mut inner_sum_rot_keys =
            gen_rot_keys_inner_product(&bfv_params, &bfv_sk, ct_level + 2, ct_level + 1, &mut rng);
        let mut i = 1;

        let batch_size = 32;
        let mut offset = 0;
        let mut unpacked_cts: Vec<Ciphertext> = vec![];

        let mut now = std::time::SystemTime::now();
        let mut total_time = std::time::Duration::ZERO;
        for i in 0..(degree / batch_size) {
            now = std::time::SystemTime::now();
            let res = pv_unpack(
                &bfv_params,
                &rot_keys,
                &inner_sum_rot_keys,
                &mut ct,
                batch_size,
                offset,
                &bfv_sk,
                1,
            );
            println!("pv_unpack for batch {} took {:?}", i, now.elapsed());
            total_time += now.elapsed().unwrap();

            offset += batch_size;
            unpacked_cts.extend(res);

            unsafe {
                dbg!("ct noise after: ", bfv_sk.measure_noise(&ct).unwrap());
            }
        }
        println!("pv_unpack in total took {:?}", total_time);

        unpacked_cts.iter().enumerate().for_each(|(index, u_ct)| {
            // unsafe {
            //     println!(
            //         "noise of ct at index {}: {} ",
            //         index,
            //         bfv_sk.measure_noise(&u_ct).unwrap()
            //     );
            // }
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
        // let mut i = 1;
        // let mut rot_keys = HashMap::<usize, GaloisKey>::new();
        // while i < degree {
        //     rot_keys.insert(
        //         i,
        //         GaloisKey::new(
        //             &bfv_sk,
        //             rot_to_exponent(i as u64, &bfv_params),
        //             0,
        //             0,
        //             &mut rng,
        //         )
        //         .unwrap(),
        //     );
        //     i *= 2;
        // }
        // rot_keys.insert(
        //     degree * 2 - 1,
        //     GaloisKey::new(&bfv_sk, degree * 2 - 1, 0, 0, &mut rng).unwrap(),
        // );

        // let ct2 = inner_sum(&bfv_params, &ct, &rot_keys);

        let evk = EvaluationKeyBuilder::new_leveled(&bfv_sk, 0, 0)
            .unwrap()
            .enable_inner_sum()
            .unwrap()
            .build(&mut rng)
            .unwrap();
        let ct2 = evk.computes_inner_sum(&ct).unwrap();

        let sum_vec =
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&ct2).unwrap(), Encoding::simd()).unwrap();
        let sum: u64 = values.iter().sum();
        assert!(sum_vec == vec![sum % t; degree]);
    }

    #[test]
    fn test_pv_compress() {
        let degree = 1 << 15;
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

                let now = std::time::SystemTime::now();
                pv_compress(
                    &bfv_params,
                    &batch_cts.1,
                    0,
                    batch_size,
                    offset,
                    &mut comressed_pv,
                    &bfv_sk,
                );
                println!("pv pv_compress took: {:?}", now.elapsed());

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

    #[test]
    fn test_mul_many() {
        let mut rng = thread_rng();
        let degree = 512;
        let t = MODULI_OMR_PT[0];

        let mut rng = thread_rng();

        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(degree)
                .set_plaintext_modulus(t)
                // .set_moduli(&MODULI_OMR[MODULI_OMR.len() - 2..])
                .set_moduli_sizes(&[60, 60, 60, 60, 60])
                .build()
                .unwrap(),
        );
        let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
        let multiplicators = map_rlks_to_multiplicators(&gen_rlk_keys(&bfv_params, &bfv_sk));

        let mul_count = 5;
        let pt_modulus = Modulus::new(bfv_params.plaintext()).unwrap();
        let mut cts: Vec<Ciphertext> = vec![];
        for i in 0..mul_count {
            // let vals = pt_modulus.random_vec(bfv_params.degree(), &mut rng);
            let vals = vec![i + 1u64; bfv_params.degree()];
            let pt = Plaintext::try_encode(&vals, Encoding::simd_at_level(1), &bfv_params).unwrap();
            cts.push(bfv_sk.try_encrypt(&pt, &mut rng).unwrap());
        }

        mul_many(&mut cts, &multiplicators, 1);
        dbg!(
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&cts[0]).unwrap(), Encoding::simd())
                .unwrap()
        );
    }

    #[test]
    fn display_ct_size() {
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_moduli(MODULI_OMR)
                // .set_moduli_sizes(&[40, 50, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60])
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let mut ct: Ciphertext = sk
            .try_encrypt(
                &Plaintext::try_encode(&vec![1u64; params.degree()], Encoding::simd(), &params)
                    .unwrap(),
                &mut rng,
            )
            .unwrap();
        ct.mod_switch_to_last_level();
        dbg!(ct.to_bytes().len());
    }

    #[test]
    fn plaintext_noise() {
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(1 << 14)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                // .set_moduli(&MODULI_OMR[..2])
                .set_moduli_sizes(&[28, 39])
                .set_variance(10)
                .build()
                .unwrap(),
        );
        let pt = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd(),
            &params,
        )
        .unwrap();
        let pt2 = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd(),
            &params,
        )
        .unwrap();

        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let mut ct: Ciphertext = sk.try_encrypt(&pt, &mut rng).unwrap();
        unsafe { dbg!(sk.measure_noise(&ct)) };
        ct *= &pt2;
        unsafe { dbg!(sk.measure_noise(&ct)) };
    }

    #[test]
    fn inner_product_noise() {
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(1 << 15)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                // .set_moduli(&MODULI_OMR[..2])
                .set_moduli_sizes(&[28, 39, 60, 60])
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let pt = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd(),
            &params,
        )
        .unwrap();
        let mut ct: Ciphertext = sk.try_encrypt(&pt, &mut rng).unwrap();
        ct.mod_switch_to_next_level();

        let ek = gen_rot_keys_inner_product(&params, &sk, 1, 0, &mut rng);
        ct = ek.computes_inner_sum(&ct).unwrap();
        unsafe { dbg!(sk.measure_noise(&ct)) };
    }

    #[test]
    fn left_rotate_noise() {
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(1 << 15)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                // .set_moduli(&MODULI_OMR[..2])
                .set_moduli_sizes(&[28, 39, 60])
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let pt = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd(),
            &params,
        )
        .unwrap();
        let pt2 = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd_at_level(1),
            &params,
        )
        .unwrap();
        let mut ct: Ciphertext = sk.try_encrypt(&pt, &mut rng).unwrap();
        ct.mod_switch_to_next_level();

        // let ek = gen_rot_keys_inner_product(&params, &sk, 1, 0, &mut rng);
        let ek = gen_rot_keys_pv_selector(&params, &sk, 1, 0, &mut rng);
        ct = ek.rotates_rows(&ct).unwrap(); // 12 and 72
        unsafe { dbg!(sk.measure_noise(&ct)) };
        ct *= &pt2;
        unsafe { dbg!(sk.measure_noise(&ct)) };
    }

    #[test]
    fn mul_noise() {
        let params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(1 << 15)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                // .set_moduli(&MODULI_OMR[..2])
                .set_moduli_sizes(&[28, 39, 60, 60, 60, 60])
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&params, &mut rng);

        let rlk = RelinearizationKey::new_leveled(&sk, 1, 0, &mut rng).unwrap();
        let multiplicator = Multiplicator::default(&rlk).unwrap();

        let pt = Plaintext::try_encode(
            &vec![1u64, 34, 2, 4, 2, 2, 342, 2],
            Encoding::simd(),
            &params,
        )
        .unwrap();
        let mut ct: Ciphertext = sk.try_encrypt(&pt, &mut rng).unwrap();
        ct.mod_switch_to_next_level();

        // let ek = gen_rot_keys_inner_product(&params, &sk, 1, 0, &mut rng);
        let mut ct2 = multiplicator.multiply(&ct, &ct).unwrap();
        ct2.mod_switch_to_next_level();
        unsafe { dbg!(sk.measure_noise(&ct2)) };
    }

    // CLI related functions
    #[test]
    fn gen_and_save_clues() {
        let mut rng = thread_rng();
        let pvw_params = Arc::new(PvwParameters::default());
        let bytes = std::fs::read("generated/keys/cluePrivKey").unwrap();
        let pvw_sk = PvwSecretKey::from_bytes(&bytes, &pvw_params);
        let pvw_pk = pvw_sk.public_key(&mut rng);

        let fake_pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
        let fake_pvw_pk = fake_pvw_sk.public_key(&mut rng);
        let fake_clue = fake_pvw_pk.encrypt(&[0, 0, 0, 0], &mut rng);

        let pertinent_indices = gen_pertinent_indices(40, 1 << 15);
        // let pertinent_indices = vec![1, 2, 3];

        std::fs::create_dir_all("generated/clues").unwrap();

        (0..(1usize << 15))
            .map(|index| {
                if pertinent_indices.contains(&index) {
                    pvw_pk.encrypt(&[0, 0, 0, 0], &mut rng)
                } else {
                    fake_clue.clone()
                }
            })
            .enumerate()
            .for_each(|(index, ct)| {
                let mut file = std::fs::File::create(format!("./generated/clues/{index}")).unwrap();
                file.write_all(&ct.to_bytes()).unwrap();
            });
    }

    /// Reads clues from generated/clues/* and find the pertaining ones.
    #[test]
    fn find_pertaining_pvw_clues() {
        let pvw_params = Arc::new(PvwParameters::default());
        let pvw_sk = PvwSecretKey::from_bytes(
            &std::fs::read("generated/keys/cluePrivKey").unwrap(),
            &pvw_params,
        );
        let mut pertinent_indices = vec![];
        std::fs::read_dir("generated/clues")
            .unwrap()
            .collect_vec()
            .iter()
            .for_each(|path| {
                let path = path.as_ref().unwrap().path();
                let clue =
                    PvwCiphertext::from_bytes(&std::fs::read(&path).unwrap(), &pvw_params).unwrap();
                if pvw_sk.decrypt_shifted(clue) == vec![0, 0, 0, 0] {
                    pertinent_indices.push(path.file_name().unwrap().to_os_string());
                }
            });
        println!("Pertinent count: {:?}", pertinent_indices.len());
        println!("Pertinent file names: {:?}", pertinent_indices);
    }

    #[test]
    fn check_pertinency_cts() {
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk: Vec<i64> =
            bincode::deserialize(&std::fs::read("generated/keys/bfvPrivKey").unwrap()).unwrap();
        let bfv_sk = SecretKey::new(bfv_sk, &bfv_params);

        let mut pertinent_file_names = vec![];

        std::fs::read_dir("generated/o1")
            .unwrap()
            .collect_vec()
            .iter()
            .for_each(|path| {
                let path = path.as_ref().unwrap().path();
                let p_ct =
                    Ciphertext::from_bytes(std::fs::read(&path).unwrap().as_slice(), &bfv_params)
                        .unwrap();

                // unsafe {
                //     dbg!(bfv_sk.measure_noise(&p_ct).unwrap());
                // }

                if Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&p_ct).unwrap(), Encoding::simd())
                    .unwrap()
                    .iter()
                    .product::<u64>()
                    == 1
                {
                    println!(
                        "pertinent index: {:?}",
                        path.file_name().unwrap().to_os_string()
                    );
                    pertinent_file_names.push(path.file_name().unwrap().to_os_string());
                }
            });

        println!("Pertinent count: {:?}", pertinent_file_names.len());
        println!("Pertinent file names: {:?}", pertinent_file_names);
    }

    #[test]
    fn gen_and_save_random_data() {
        let mut rng = thread_rng();

        let output_dir = PathBuf::from_str("generated/messages").unwrap();
        std::fs::create_dir_all(&output_dir).unwrap();

        for index in 0..(1 << 15) {
            let values: Vec<u8> = rng
                .clone()
                .sample_iter(Uniform::new(0, 255))
                .take(400)
                .collect_vec();

            let mut path = output_dir.clone();
            path.push(format!("{index}"));
            std::fs::File::create(path)
                .unwrap()
                .write_all(&values)
                .unwrap();
        }
    }

    #[test]
    fn test_retrieval() {
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk: Vec<i64> =
            bincode::deserialize(&std::fs::read("generated/keys/bfvPrivKey").unwrap()).unwrap();
        let bfv_sk = SecretKey::new(bfv_sk, &bfv_params);

        let mapping = get_mapping("generated/test1/messages".into(), 21000, 80000);
        mapping
            .iter()
            .enumerate()
            .for_each(|(i, (tx_file_name, tx_hash))| {
                let ct = Ciphertext::from_bytes(
                    &std::fs::read(format!("generated/test1/output/{tx_hash}")).unwrap(),
                    &bfv_params,
                )
                .unwrap();
                if Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&ct).unwrap(), Encoding::simd())
                    .unwrap()
                    .iter()
                    .product::<u64>()
                    == 1
                {
                    let tx =
                        std::fs::read(format!("generated/test1/messages/{tx_file_name}")).unwrap();
                    println!("index: {i}; tx: {:?}", hex::encode(tx));
                }
            })
    }

    #[test]
    fn test_create_digest1() {
        let bfv_params = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_moduli(MODULI_OMR)
                .build()
                .unwrap(),
        );
        let bfv_sk: Vec<i64> =
            bincode::deserialize(&std::fs::read("generated/keys/bfvPrivKey").unwrap()).unwrap();
        let bfv_sk = SecretKey::new(bfv_sk, &bfv_params);

        // let ct = Ciphertext::from_bytes(
        //     &std::fs::read(format!("generated/digests/digest2")).unwrap(),
        //     &bfv_params,
        // )
        // .unwrap();

        let digest2 = deserialize_digest2(
            &std::fs::read(format!("generated/digests/digest2")).unwrap(),
            &bfv_params,
        );

        unsafe {
            digest2.cts.iter().for_each(|ct| {
                dbg!(bfv_sk.measure_noise(&ct).unwrap());
            });
        }

        // let mut pv =
        //     Vec::<u64>::try_decode(&bfv_sk.try_decrypt(&ct).unwrap(), Encoding::simd()).unwrap();

        // let mut count = 0;
        // pv.iter_mut().enumerate().for_each(|(index, v)| {
        //     for _ in 0..16 {
        //         let bit = *v & 1u64;
        //         if bit == 1 {
        //             // dbg!(index);
        //             count += 1;
        //         }
        //         *v >>= 1;
        //     }
        // });
        // dbg!(count);
    }
}
