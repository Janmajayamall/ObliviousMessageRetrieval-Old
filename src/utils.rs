use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use fhe::bfv::{BfvParameters, EvaluationKey, EvaluationKeyBuilder, RelinearizationKey, SecretKey};
use fhe_math::{
    rq::{traits::TryConvertFrom, Context, Poly, Representation},
    zq::Modulus,
};
use fhe_traits::{Deserialize, DeserializeParametrized, Serialize};
use itertools::Itertools;
use rand::{distributions::Uniform, prelude::Distribution, CryptoRng, RngCore};
use rand::{thread_rng, Rng};
use std::sync::Arc;
use std::vec;
use std::{collections::HashMap, fs::File};
use std::{io::Write, thread::current};

use crate::{
    pvw::{PVWCiphertext, PVWParameters, PVWSecretKey, PublicKey},
    server::DetectionKey,
};

pub fn read_range_coeffs(path: &str) -> Vec<u64> {
    let mut file = File::open(path).unwrap();
    let mut buf = vec![0u64; 65536];
    file.read_u64_into::<LittleEndian>(&mut buf).unwrap();
    buf
}

pub fn mul_many_poly(values: &mut Vec<Poly>) {
    while values.len() != 1 {
        let mut mid = values.len() / 2;
        for i in 0..mid {
            values[i] = &values[i] * &values[mid + i];
        }

        if values.len() % 2 != 0 {
            values[mid] = values.last().unwrap().clone();
            mid += 1;
        }

        values.truncate(mid);
    }
}

pub fn precompute_range_coeffs() {
    // precompute coefficients
    //
    // Range function returns 1 if input > 65536 / 2
    // otherwise returns 0.
    let q = Modulus::new(65537).unwrap();
    let r = 850;
    let mut coeffs = vec![];
    for i in 1..65537 {
        let mut sum = 0;
        for a in 0..65537 {
            // f(a) * a.pow(65536 - i)
            if a >= (q.modulus() - r) || a <= r {
                sum = q.add(sum, q.mul(1, q.pow(a, 65536 - i)));
            }
        }
        coeffs.push(sum);
    }
    let mut buf = [0u8; 65536 * 8];
    LittleEndian::write_u64_into(&coeffs, &mut buf);
    let mut f = File::create("params_850.bin").unwrap();
    f.write_all(&buf).unwrap();
}

pub fn rot_to_exponent(rot_by: u64, bfv_params: &Arc<BfvParameters>) -> usize {
    let q = Modulus::new(2 * bfv_params.degree() as u64).unwrap();
    q.pow(3, rot_by) as usize
}
pub fn assign_buckets<R: CryptoRng + RngCore>(
    no_of_buckets: usize,
    gamma: usize,
    q_mod: u64,
    set_size: usize,
    rng: &mut R,
) -> (Vec<Vec<usize>>, Vec<Vec<u64>>) {
    let mut buckets = vec![vec![]; set_size];
    let mut weights = vec![vec![]; set_size];

    for row_index in 0..set_size {
        while buckets[row_index].len() != gamma {
            // random bucket
            let bucket = rng.sample(Uniform::new(0, no_of_buckets));

            // avoid duplicate buckets
            if !buckets[row_index].contains(&bucket) {
                buckets[row_index].push(bucket);

                // Assign weight
                // Weight cannot be zero
                let weight = rng.sample(Uniform::new(1u64, q_mod));
                weights[row_index].push(weight);
            }
        }
    }

    (buckets, weights)
}

pub fn scale_factor(a: u64, b: u64, q_mod: u64) -> u64 {
    let modulus = Modulus::new(q_mod).unwrap();
    modulus.mul(a, modulus.inv(b).unwrap())
}

/// Scales b by `scale_factor`
/// and then perform a - b
pub fn sub_scaled_by_ratio(a: &[u64], b: &[u64], q_mod: u64, scale_factor: u64) -> Vec<u64> {
    let modulus = Modulus::new(q_mod).unwrap();

    let b = b
        .iter()
        .map(|v| modulus.mul(*v, scale_factor))
        .collect_vec();
    let mut a = a.to_vec();
    modulus.sub_vec(&mut a, &b);
    a
}

/// Note that RHS is of dim 2, since we attempt to solve all sets at once
pub fn solve_equations(
    mut lhs: Vec<Vec<u64>>,
    mut rhs: Vec<Vec<u64>>,
    q_mod: u64,
) -> Vec<Vec<u64>> {
    debug_assert!(lhs.len() == rhs.len());

    let cols = lhs[0].len();
    let rows = lhs.len();
    let mut pivot_rows = vec![-1; cols];

    for pi in 0..cols {
        for row_index in 0..rows {
            // A row can't be pivot more than once
            if pivot_rows.contains(&(row_index as i32)) {
                continue;
            } else if (pivot_rows[pi] != -1
                && lhs[pivot_rows[pi] as usize][pi] < lhs[row_index][pi])
                || (pivot_rows[pi] == -1 && lhs[row_index][pi] != 0)
            {
                pivot_rows[pi] = row_index as i32;
            }
        }

        // Not solvable
        if pivot_rows[pi] == -1 {
            println!("Unsolvable!");

            break;
        }

        for row_index in 0..rows {
            if lhs[row_index][pi] > 0 && row_index != pivot_rows[pi] as usize {
                let scale_factor =
                    scale_factor(lhs[pivot_rows[pi] as usize][pi], lhs[row_index][pi], q_mod);
                lhs[row_index] = sub_scaled_by_ratio(
                    &lhs[pivot_rows[pi] as usize],
                    &lhs[row_index],
                    q_mod,
                    scale_factor,
                );
                rhs[row_index] = sub_scaled_by_ratio(
                    &rhs[pivot_rows[pi] as usize],
                    &rhs[row_index],
                    q_mod,
                    scale_factor,
                )
            }
        }
    }

    let modulus = Modulus::new(q_mod).unwrap();
    let no_sols = rhs[0].len();
    let mut res = vec![vec![0u64; no_sols]; cols];
    for i in 0..cols {
        if pivot_rows[i] != -1 {
            let row = pivot_rows[i] as usize;
            for j in 0..no_sols {
                res[i][j] = modulus.mul(modulus.inv(lhs[row][i]).unwrap(), rhs[row][j]);
            }
        }
    }
    res
}

/// test fn that simulates powers_of_x on plaintext
/// for debugging
pub fn powers_of_x_poly(
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

pub fn range_fn_poly(
    ctx: &Arc<Context>,
    input: &Poly,
    poly_degree: usize,
    params_path: &str,
) -> Poly {
    // read coeffs
    let coeffs = read_range_coeffs(params_path);
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

    let one =
        Poly::try_convert_from(vec![1; poly_degree], &ctx, false, Representation::Ntt).unwrap();
    total_sum = -total_sum + one;

    total_sum
}

pub fn gen_rlk_keys(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
) -> HashMap<usize, RelinearizationKey> {
    let mut rng = thread_rng();
    let mut keys = HashMap::<usize, RelinearizationKey>::new();

    // let mut now = std::time::SystemTime::now();
    for i in 0..bfv_params.max_level() {
        let key_level = {
            if i == 0 {
                0
            } else {
                i - 1
            }
        };
        let rlk = RelinearizationKey::new_leveled(sk, i, key_level, &mut rng).unwrap();
        keys.insert(i, rlk);
    }
    // println!("RLK gen took {:?}", now.elapsed().unwrap());

    keys
}

pub fn gen_rlk_keys_levelled<R: CryptoRng + RngCore>(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
    rng: &mut R,
) -> HashMap<usize, RelinearizationKey> {
    let mut keys = HashMap::<usize, RelinearizationKey>::new();
    // for powers of x; range fn;
    for i in 1..11 {
        keys.insert(
            i,
            RelinearizationKey::new_leveled(sk, i, i - 1, rng).unwrap(),
        );
    }
    keys
}

pub fn gen_rot_keys_inner_product<R: CryptoRng + RngCore>(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
    ct_level: usize,
    ksk_level: usize,
    rng: &mut R,
) -> EvaluationKey {
    let mut evk = EvaluationKeyBuilder::new_leveled(sk, ct_level, ksk_level).unwrap();
    assert!(evk.enable_inner_sum().is_ok());
    evk.build(rng).unwrap()
}

pub fn gen_rot_keys_pv_selector<R: CryptoRng + RngCore>(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
    ct_level: usize,
    ksk_level: usize,
    rng: &mut R,
) -> EvaluationKey {
    let mut evk = EvaluationKeyBuilder::new_leveled(sk, ct_level, ksk_level).unwrap();
    // left rot by 1
    assert!(evk.enable_column_rotation(1).is_ok());
    // switch rows
    assert!(evk.enable_row_rotation().is_ok());
    evk.build(rng).unwrap()
}

pub fn gen_detection_key<R: CryptoRng + RngCore>(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
    rng: &mut R,
) -> DetectionKey {
    let ek1 = EvaluationKeyBuilder::new_leveled(sk, 0, 0)
        .unwrap()
        .enable_column_rotation(1)
        .unwrap()
        .build(rng)
        .unwrap();
    let rlk_keys = gen_rlk_keys_levelled(bfv_params, sk, rng);
    let ek2 = gen_rot_keys_pv_selector(bfv_params, sk, 10, 9, rng);
    let ek3 = gen_rot_keys_inner_product(bfv_params, sk, 12, 11, rng);

    DetectionKey {
        ek1,
        ek2,
        ek3,
        rlk_keys,
    }
}

pub fn serialize_detection_key(key: &DetectionKey) -> Vec<u8> {
    let mut s = vec![];

    s.extend_from_slice(key.ek1.to_bytes().as_slice());
    s.extend_from_slice(key.ek2.to_bytes().as_slice());
    s.extend_from_slice(key.ek3.to_bytes().as_slice());

    (1..11).into_iter().for_each(|i| {
        s.extend_from_slice(key.rlk_keys.get(&i).unwrap().to_bytes().as_slice());
    });

    s
}

pub fn deserialize_detection_key(bfv_params: &Arc<BfvParameters>, bytes: &[u8]) -> DetectionKey {
    // debug_assert!(bytes.len() == )
    let ek1 = EvaluationKey::from_bytes(&bytes[..3030031], bfv_params).unwrap();
    let ek2 = EvaluationKey::from_bytes(&bytes[3030031..3816202], bfv_params).unwrap();
    let ek3 = EvaluationKey::from_bytes(&bytes[3816202..5397013], bfv_params).unwrap();

    let mut rlk_keys = HashMap::<usize, RelinearizationKey>::new();
    macro_rules! rlk {
        ($i: literal, $r: expr) => {
            rlk_keys.insert(
                $i,
                RelinearizationKey::from_bytes(&bytes[$r], bfv_params).unwrap(),
            );
        };
    }
    rlk!(1, 5397013..8225040);
    rlk!(2, 8225040..10651390);
    rlk!(3, 10651390..12798941);
    rlk!(4, 12798941..14677420);
    rlk!(5, 14677420..16231532);
    rlk!(6, 16231532..17491997);
    rlk!(7, 17491997..18489535);
    rlk!(8, 18489535..19254866);
    rlk!(9, 19254866..19818710);
    rlk!(10, 19818710..);

    DetectionKey {
        ek1,
        ek2,
        ek3,
        rlk_keys,
    }
}

pub fn random_data(mut size_bits: usize) -> Vec<u64> {
    assert!(size_bits.is_power_of_two());
    let rng = thread_rng();

    let chunks = size_bits / 16;
    Uniform::new(0u64, 1 << 16)
        .sample_iter(rng)
        .take(chunks)
        .collect()
}

pub fn gen_pertinent_indices(size: usize, set_size: usize) -> Vec<usize> {
    let mut rng = thread_rng();
    let distr = Uniform::new(0, set_size);
    let mut indices = vec![];
    while indices.len() != size {
        let v = distr.sample(&mut rng);
        if !indices.contains(&v) {
            indices.push(v);
        }
    }
    indices
}

pub fn gen_clues(
    pvw_params: &PVWParameters,
    pvw_pk: &PublicKey,
    pertinent_indices: &[usize],
    set_size: usize,
) -> Vec<PVWCiphertext> {
    let mut rng = thread_rng();

    let tmp_sk = PVWSecretKey::random(pvw_params, &mut rng);
    let other = tmp_sk.public_key(&mut rng).encrypt(&[0, 0, 0, 0], &mut rng);

    (0..set_size)
        .map(|index| {
            if pertinent_indices.contains(&index) {
                pvw_pk.encrypt(&[0, 0, 0, 0], &mut rng)
            } else {
                other.clone()
            }
        })
        .collect()
}

pub fn gen_paylods(size: usize) -> Vec<Vec<u64>> {
    let rng = thread_rng();
    (0..size)
        .into_iter()
        .map(|_| {
            // 256 bytes of random data in size of 2 bytes
            rng.clone()
                .sample_iter(Uniform::new(0u64, 1 << 16))
                .take(128)
                .collect_vec()
        })
        .collect()
}

pub fn transcode_to_bytes(vals: &[u64], n_bits: usize) -> Vec<u8> {
    let mask = u128::MAX >> (64 - n_bits);
    let mut current_n_bits = 0;
    let mut buffer = 0;
    let mut current_index = 0;
    let mut bytes = vec![];
    while current_index < vals.len() {
        while current_n_bits < 8 {
            buffer |= ((vals[current_index] as u128) & mask) << current_n_bits;
            current_n_bits += n_bits;
            current_index += 1;
        }

        while current_n_bits >= 8 {
            bytes.push(buffer as u8);
            buffer >>= 8;
            current_n_bits -= 8;
        }
    }
    if current_n_bits != 0 {
        bytes.push(buffer as u8);
    }

    bytes
}

pub fn transcode_from_bytes(bytes: Vec<u8>, n_bits: usize) -> Vec<u64> {
    let mut buffer = 0;
    let mut current_index = 0;
    let mut current_n_bits = 0;
    let mut out = vec![];
    let mask = (u64::MAX >> (64 - n_bits)) as u128;
    while current_index < bytes.len() {
        while current_n_bits < n_bits {
            buffer |= ((bytes[current_index] as u128) << current_n_bits);
            current_n_bits += 8;
            current_index += 1;
        }

        while current_n_bits >= n_bits {
            out.push((buffer & mask) as u64);
            buffer >>= n_bits;
            current_n_bits -= n_bits;
        }
    }

    if current_n_bits != 0 {
        out.push(buffer as u64);
    }
    out
}

#[cfg(test)]
mod tests {
    use crate::{DEGREE, MODULI_OMR, MODULI_OMR_PT, VARIANCE};

    use super::*;
    use fhe::bfv::BfvParametersBuilder;
    use itertools::Itertools;
    use rand::{distributions::Uniform, thread_rng};

    #[test]
    fn trial() {
        precompute_range_coeffs();
    }

    #[test]
    fn test_assign_buckets() {
        let mut rng = thread_rng();
        let k = 50;
        let m = 100;
        let gamma = 5;
        let q_mod = 65537;

        let (buckets, weights) = assign_buckets(m, gamma, q_mod, k, &mut rng);

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

    #[test]
    fn detection_key_serialize_deserialize() {
        let par = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_moduli(MODULI_OMR)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_variance(VARIANCE)
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&par, &mut rng);

        let key = gen_detection_key(&par, &sk, &mut rng);
        let s = serialize_detection_key(&key);
        let key1 = deserialize_detection_key(&par, &s);

        assert_eq!(key, key1);
    }

    #[test]
    fn display_key_sizes() {
        pub fn serialize_detection_key(key: DetectionKey) {
            let mut s = vec![];
            let mut r = vec![];

            s.extend_from_slice(key.ek1.to_bytes().as_slice());
            r.push(s.len());
            s.extend_from_slice(key.ek2.to_bytes().as_slice());
            r.push(s.len());
            s.extend_from_slice(key.ek3.to_bytes().as_slice());
            r.push(s.len());

            (1..11).into_iter().for_each(|i| {
                s.extend_from_slice(key.rlk_keys.get(&i).unwrap().to_bytes().as_slice());
                r.push(s.len());
            });

            dbg!(r);
        }

        let par = Arc::new(
            BfvParametersBuilder::new()
                .set_degree(DEGREE)
                .set_moduli(MODULI_OMR)
                .set_plaintext_modulus(MODULI_OMR_PT[0])
                .set_variance(VARIANCE)
                .build()
                .unwrap(),
        );

        let mut rng = thread_rng();
        let sk = SecretKey::random(&par, &mut rng);

        let key = gen_detection_key(&par, &sk, &mut rng);
        serialize_detection_key(key);
    }

    #[test]
    fn print_rlk_macro() {
        let r = vec![
            3030031, 3816202, 5397013, 8225040, 10651390, 12798941, 14677420, 16231532, 17491997,
            18489535, 19254866, 19818710, 20211787,
        ];
        for i in (3..r.len()) {
            println!("rlk!({}, {}..{});", i - 2, r[i - 1], r[i]);
        }
    }

    #[test]
    fn transcode_bytes() {
        let rng = thread_rng();
        let p = 65537u64;
        let mut vals = rng.sample_iter(Uniform::new(0, p)).take(10).collect_vec();
        vals[0] = 65536;
        let n_bits = 64 - p.leading_zeros() - 1;
        let bytes = transcode_to_bytes(&vals, n_bits as usize);
        dbg!(bytes.len());
        let v = transcode_from_bytes(bytes, n_bits as usize);
        dbg!(vals, v, n_bits);
    }
}
