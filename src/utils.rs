use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use fhe::bfv::{BfvParameters, GaloisKey, RelinearizationKey, SecretKey};
use fhe_math::{
    rq::{traits::TryConvertFrom, Context, Poly, Representation},
    zq::Modulus,
};
use itertools::{Itertools, MultiProduct};
use rand::{distributions::Uniform, prelude::Distribution, seq::index};
use rand::{thread_rng, Rng};
use std::io::Write;
use std::sync::Arc;
use std::vec;
use std::{collections::HashMap, fs::File};

use crate::pvw::{PVWCiphertext, PVWParameters, PVWSecretKey, PublicKey};

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
    f.write_all(&buf);
}

pub fn rot_to_exponent(rot_by: u64, bfv_params: &Arc<BfvParameters>) -> usize {
    let q = Modulus::new(2 * bfv_params.degree() as u64).unwrap();
    q.pow(3, rot_by) as usize
}
pub fn assign_buckets(
    no_of_buckets: usize,
    gamma: usize,
    q_mod: u64,
    N: usize,
) -> (Vec<Vec<usize>>, Vec<Vec<u64>>) {
    let mut rng = thread_rng();

    let mut buckets = vec![vec![]; N];
    let mut weights = vec![vec![]; N];

    for row_index in 0..N {
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

pub fn sub_vec(a: &Vec<u64>, b: &Vec<u64>, q_mod: u64) -> Vec<u64> {
    let modulus = Modulus::new(q_mod).unwrap();
    let mut a = a.clone();
    modulus.sub_vec(&mut a, b);
    a
}

pub fn scalar_mul_vec() -> Vec<u64> {
    todo!()
}

pub fn scale_factor(a: u64, b: u64, q_mod: u64) -> u64 {
    let modulus = Modulus::new(q_mod).unwrap();
    modulus.mul(a, modulus.inv(b).unwrap())
}

/// Scales b by `scale_factor`
/// and then perform a - b
pub fn sub_scaled_by_ratio(a: &Vec<u64>, b: &Vec<u64>, q_mod: u64, scale_factor: u64) -> Vec<u64> {
    let modulus = Modulus::new(q_mod).unwrap();

    let b_scaled = b.iter().map(|v| modulus.mul(*v, scale_factor)).collect();
    sub_vec(a, &b_scaled, q_mod)
}

/// Note that RHS is of 2 dimensions, since we attempt to solve all sets at once
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
        let mut pivot_row = pi;
        if lhs[pivot_row][pi] > 0 {
            pivot_rows[pi] = pivot_row as i32;
        }
        for row_index in 0..rows {
            // Only check whether row can be used as pivot
            // if not already used
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
            dbg!("OOPS");
            // dbg!(&pivot_rows);
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

    let mut now = std::time::SystemTime::now();
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
    println!("RLK gen took {:?}", now.elapsed().unwrap());

    keys
}

pub fn gen_rot_keys(
    bfv_params: &Arc<BfvParameters>,
    sk: &SecretKey,
    ct_level: usize,
    ksk_level: usize,
) -> HashMap<usize, GaloisKey> {
    let mut rng = thread_rng();
    let mut keys = HashMap::<usize, GaloisKey>::new();
    let mut i = 1;
    while i < bfv_params.degree() / 2 {
        let key = GaloisKey::new(
            sk,
            rot_to_exponent(i as u64, bfv_params),
            ct_level,
            ksk_level,
            &mut rng,
        )
        .unwrap();
        keys.insert(i, key);
        i *= 2;
    }
    keys.insert(
        bfv_params.degree() * 2 - 1,
        GaloisKey::new(
            sk,
            bfv_params.degree() * 2 - 1,
            ct_level,
            ksk_level,
            &mut rng,
        )
        .unwrap(),
    );
    keys
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
    pvw_params: &Arc<PVWParameters>,
    pvw_pk: &Arc<PublicKey>,
    pertinent_indices: &Vec<usize>,
    set_size: usize,
) -> Vec<PVWCiphertext> {
    (0..set_size)
        .map(|index| {
            if pertinent_indices.contains(&index) {
                pvw_pk.encrypt(&[0, 0, 0, 0])
            } else {
                let tmp_sk = PVWSecretKey::gen_sk(pvw_params);
                tmp_sk.public_key().encrypt(&[0, 0, 0, 0])
            }
        })
        .collect()
}

pub fn gen_paylods(size: usize) -> Vec<Vec<u64>> {
    let rng = thread_rng();
    (0..size)
        .into_iter()
        .map(|_| {
            // 256 bytes in 2 bytes pieces
            rng.clone()
                .sample_iter(Uniform::new(0u64, 65536))
                .take(128)
                .collect_vec()
        })
        .collect()
}

// pub fn gen_data(size: ,gen: bool) -> {

// }

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use rand::{distributions::Uniform, thread_rng};

    #[test]
    fn trial() {
        precompute_range_coeffs();
    }

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
