use std::vec;

use fhe::bfv::{
    self, BfvParameters, BfvParametersBuilder, Ciphertext, Encoding, Multiplicator, Plaintext,
    RelinearizationKey, SecretKey,
};
use fhe_math::zq::Modulus;
use fhe_traits::{FheEncoder, FheEncrypter};
use fhe_util::sample_vec_cbd;
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
        let t = m.iter().map(|v| (self.params.q / 2) * v).collect_vec();

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
            .for_each(|v| *v = ((*v + (self.params.q / 4)) / (self.params.q / 2)) % 2);
        d
    }
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
    let p_c2 = pvw_pk.encrypt(vec![0, 0, 0, 1]);

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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trial() {
        prep_sk();
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

// 1. Generate sk cts:
//     Sk is of form ell * n and A is of form n * 1 and we need to perform
//     Sk * A. So we need to create ct encrypting every element in Sk,
//     so that Sk * A can be calculated for multiple encryptions
//     using SIMD.
