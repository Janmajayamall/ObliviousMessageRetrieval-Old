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

#[derive(Clone, Debug)]
pub struct PVWParameters {
    pub n: usize,
    pub m: usize,
    pub ell: usize,
    pub variance: usize,
    pub q: u64,
}

impl Default for PVWParameters {
    fn default() -> Self {
        Self {
            n: 450,
            m: 16000,
            ell: 4,
            variance: 2,
            q: 65537,
        }
    }
}

struct PVWCiphertext {
    a: Vec<u64>,
    b: Vec<u64>,
}

struct PublicKey {
    a: Vec<Vec<u64>>,
    b: Vec<Vec<u64>>,
    params: PVWParameters,
}

impl PublicKey {
    pub fn encrypt(&self, m: Vec<u64>) -> PVWCiphertext {
        let mut rng = thread_rng();
        let q = Modulus::new(self.params.q).unwrap();
        let t = m
            .iter()
            .map(|v| {
                if *v == 1 {
                    (3 * self.params.q / 4)
                } else {
                    (self.params.q / 4)
                }
            })
            .collect_vec();

        let distr = Uniform::new(0u64, 2);
        let e = distr
            .sample_iter(&mut rng)
            .take(self.params.m)
            .collect_vec();

        let mut a = vec![0u64; self.params.n];
        for n_i in 0..self.params.n {
            let mut sum = 0u64;
            for m_i in 0..self.params.m {
                sum = q.add(sum, q.mul(self.a[m_i][n_i], e[m_i]));
            }
            a[n_i] = q.add(a[n_i], sum);
        }
        let mut b = vec![0u64; self.params.ell];
        for ell_i in 0..self.params.ell {
            let mut sum = 0u64;
            for m_i in 0..self.params.m {
                sum = q.add(sum, q.mul(self.b[m_i][ell_i], e[m_i]));
            }
            sum = q.add(sum, t[ell_i]);
            b[ell_i] = q.add(b[ell_i], sum);
        }

        PVWCiphertext { a, b }
    }
}

struct PVWSecretKey {
    key: Vec<Vec<u64>>,
    params: PVWParameters,
}

impl PVWSecretKey {
    pub fn gen_sk(params: &PVWParameters) -> PVWSecretKey {
        let mut rng = rand::thread_rng();
        let q = Modulus::new(params.q).unwrap();

        let mut cols = vec![];
        for i in 0..params.ell {
            cols.push(q.random_vec(params.n, &mut rng));
        }

        PVWSecretKey {
            key: cols,
            params: params.clone(),
        }
    }

    pub fn public_key(&self) -> PublicKey {
        let q = Modulus::new(self.params.q).unwrap();
        let mut rng = thread_rng();

        let mut a = vec![];
        for i in 0..self.params.m {
            a.push(q.random_vec(self.params.n, &mut rng))
        }

        let mut b = vec![vec![0u64; self.params.ell]; self.params.m];
        for m_i in 0..self.params.m {
            let e = q.reduce_vec_i64(
                &sample_vec_cbd(self.params.ell, self.params.variance, &mut rng).unwrap(),
            );
            for l_i in 0..self.params.ell {
                let mut sum = 0u64;
                for n_i in 0..self.params.n {
                    sum = q.add(sum, q.mul(self.key[l_i][n_i], a[m_i][n_i]));
                }
                sum = q.add(sum, e[l_i]);
                b[m_i][l_i] = q.add(b[m_i][l_i], sum);
            }
        }

        PublicKey {
            a,
            b,
            params: self.params.clone(),
        }
    }

    fn decrypt(&self, ct: PVWCiphertext) -> Vec<u64> {
        let q = Modulus::new(self.params.q).unwrap();

        // b - sa
        let mut d = vec![0u64; self.params.ell];
        for ell_i in 0..self.params.ell {
            let mut sum = 0;
            for n_i in 0..self.params.n {
                sum = q.add(sum, q.mul(self.key[ell_i][n_i], ct.a[n_i]));
            }
            // b_elli - sa_elli
            d[ell_i] = q.sub(ct.b[ell_i], sum);
        }

        d.iter_mut()
            .for_each(|v| *v = (*v >= self.params.q / 2) as u64);
        d
    }
}

fn read_range_coeffs(path: &str) -> Vec<u64> {
    let mut file = File::open(path).unwrap();
    let mut buf = vec![0u64; 65536];
    file.read_u64_into::<LittleEndian>(&mut buf).unwrap();
    buf
}

fn precompute_range_coeffs() {
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

/// test fn that simulates powers_of_x on plaintext
/// for debugging
fn powers_of_x_poly(
    ctx: &Arc<Context>,
    input: &Poly,
    // k_degree
    degree: usize,
    poly_degree: usize,
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
    // dbg!(num_mod);
    outputs
}

fn powers_of_x(
    input: &Ciphertext,
    degree: usize,
    multiplicator: &Multiplicator,
    params: &Arc<BfvParameters>,
    rlk_keys: &HashMap<usize, RelinearizationKey>,
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
                        let rlk_level = rlk_keys.get(&num_mod[base_deg - 1]).unwrap();
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

                    let rlk_level = rlk_keys.get(&num_mod[base_deg - 1]).unwrap();
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

    outputs
}

fn range_fn_poly() {
    const poly_degree: usize = 8;
    let ctx = Arc::new(Context::new(&[65537], poly_degree).unwrap());

    // Since we used SIMD for operating on multiple values,
    // let's SIMD encode our input vector;
    let input_vec = [353u64, 32767, 142, 313, 2312, 1, 21, 38000]; // all must evaluate to 0
    let input = Poly::try_convert_from(&input_vec, &ctx, false, Representation::Ntt).unwrap();

    // read coeffs
    let coeffs = read_range_coeffs("params.bin");
    let k_degree = 256;
    let mut k_powers_of_x: Vec<Poly> = powers_of_x_poly(&ctx, &input, k_degree, poly_degree);
    // M = x^256
    let mut k_powers_of_m: Vec<Poly> =
        powers_of_x_poly(&ctx, &k_powers_of_x[255], k_degree, poly_degree);

    let mut total_sum = Poly::zero(&ctx, Representation::Ntt);
    for i in 0..256 {
        let mut sum = Poly::zero(&ctx, Representation::Ntt);
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            let c_poly =
                Poly::try_convert_from(&[c; poly_degree], &ctx, false, Representation::Ntt)
                    .unwrap();
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

    dbg!(total_sum);
}

fn range_fn(
    bfv_params: &Arc<BfvParameters>,
    input: &Ciphertext,
    rlk_keys: &HashMap<usize, RelinearizationKey>,
) -> Ciphertext {
    let multiplicator = Multiplicator::default(&rlk_keys.get(&0).unwrap()).unwrap();

    let k_powers_of_x = powers_of_x(input, 256, &multiplicator, bfv_params, rlk_keys);
    // m = x^256
    let k_powers_of_m = powers_of_x(
        &k_powers_of_x[255],
        255,
        &multiplicator,
        bfv_params,
        rlk_keys,
    );

    let coeffs = read_range_coeffs("params.bin");

    let mut total = Ciphertext::zero(bfv_params);
    for i in 0..256 {
        let mut sum = Ciphertext::zero(bfv_params);
        for j in 1..257 {
            let c = coeffs[(i * 256) + (j - 1)];
            let c_pt = Plaintext::try_encode(&[c], Encoding::simd(), bfv_params).unwrap();
            let scalar_product = &k_powers_of_x[j - 1] * &c_pt;
            sum += &scalar_product;
        }

        if i != 0 {
            // mul and add
            let p = multiplicator.multiply(&k_powers_of_m[i - 1], &sum).unwrap();
            total += &p
        } else {
            total = sum;
        }
    }

    total = -total;

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
        prep_sk();
        // range_fn()
        // trickle();
        // sq_mul();
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

        let rlk = RelinearizationKey::new(&bfv_sk, &mut rng).unwrap();
        let multiplicator = Multiplicator::default(&rlk).unwrap();

        let k_degree = 256;

        let powers = powers_of_x_poly(&t_ctx, &pt_poly, k_degree, 8);
        let powers_ct = powers_of_x(&ct, k_degree, &multiplicator, &bfv_params, &rlk_keys);

        izip!(powers.iter(), powers_ct.iter()).for_each(|(p, ct)| {
            let pt = bfv_sk.try_decrypt(ct).unwrap();
            let pt = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
            assert_eq!(pt, p.coefficients().to_slice().unwrap());
        })
    }

    #[test]
    fn encrypt() {
        let params = PVWParameters {
            n: 450,
            m: 100,
            ell: 4,
            variance: 2,
            q: 65537,
        };
        for _ in 0..10 {
            let mut rng = thread_rng();
            let sk = PVWSecretKey::gen_sk(&params);
            let pk = sk.public_key();

            let distr = Uniform::new(0u64, 2);
            let m = distr.sample_iter(rng).take(params.ell).collect_vec();
            let ct = pk.encrypt(m.clone());

            let d_m = sk.decrypt(ct);

            assert_eq!(m, d_m)
        }
    }
}

fn main() {
    println!("Hello, world!");
}
