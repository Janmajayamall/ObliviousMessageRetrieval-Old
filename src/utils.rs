use byteorder::{ByteOrder, LittleEndian, ReadBytesExt};
use fhe::bfv::BfvParameters;
use fhe_math::zq::Modulus;
use itertools::MultiProduct;
use std::fs::File;
use std::io::Write;
use std::sync::Arc;
use std::vec;
pub fn read_range_coeffs(path: &str) -> Vec<u64> {
    let mut file = File::open(path).unwrap();
    let mut buf = vec![0u64; 65536];
    file.read_u64_into::<LittleEndian>(&mut buf).unwrap();
    buf
}

pub fn precompute_range_coeffs() {
    // precompute coefficients
    //
    // Range function returns 1 if input > 65536 / 2
    // otherwise returns 0.
    let q = Modulus::new(65537).unwrap();
    let mut coeffs = vec![];
    for i in 1..65537 {
        let mut sum = 0;
        dbg!(i);
        for a in 0..65537 {
            // f(a) * a.pow(65536 - i)
            if a >= 32768 {
                sum = q.add(sum, q.pow(a, 65536 - i));
            }
        }
        coeffs.push(sum);
    }
    let mut bug = [0u8; 65536 * 8];
    LittleEndian::write_u64_into(&coeffs, &mut bug);
    let mut f = File::create("params.bin").unwrap();
    f.write_all(&bug);
}

pub fn rot_to_exponent(rot_by: u64, bfv_params: &Arc<BfvParameters>) -> usize {
    let q = Modulus::new(2 * bfv_params.degree() as u64).unwrap();
    q.pow(3, rot_by) as usize
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
            dbg!(&pivot_rows);
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
        let row = pivot_rows[i] as usize;
        for j in 0..no_sols {
            res[i][j] = modulus.mul(modulus.inv(lhs[row][i]).unwrap(), rhs[row][j]);
        }
    }
    res
}
