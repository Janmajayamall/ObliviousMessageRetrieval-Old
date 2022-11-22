use fhe_math::zq::Modulus;
use fhe_util::sample_vec_cbd;
use itertools::Itertools;
use rand::{
    distributions::{Distribution, Uniform},
    thread_rng,
};

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

#[derive(Clone)]
pub struct PVWCiphertext {
    pub a: Vec<u64>,
    pub b: Vec<u64>,
}

pub struct PublicKey {
    a: Vec<Vec<u64>>,
    b: Vec<Vec<u64>>,
    params: PVWParameters,
}

impl PublicKey {
    pub fn encrypt(&self, m: Vec<u64>) -> PVWCiphertext {
        debug_assert!(m.len() == self.params.ell);

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

pub struct PVWSecretKey {
    pub key: Vec<Vec<u64>>,
    pub params: PVWParameters,
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

    pub fn decrypt(&self, ct: PVWCiphertext) -> Vec<u64> {
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

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn encrypt_but() {
        let params = PVWParameters {
            n: 450,
            m: 100,
            ell: 4,
            variance: 2,
            q: 65537,
        };

        let mut rng = thread_rng();
        let sk = PVWSecretKey::gen_sk(&params);
        let pk = sk.public_key();

        let sk1 = PVWSecretKey::gen_sk(&params);
        let pk1 = sk1.public_key();

        let distr = Uniform::new(0u64, 2);
        let ct = pk1.encrypt(vec![1, 1, 1, 1]);

        let d_m = sk.decrypt(ct);

        dbg!(d_m);
    }
}
