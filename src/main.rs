use fhe::{
    bfv::{
        self, Ckg, Cks, EvaluationKey, GaloisKey, Pcks, Plaintext, PublicKey, RelinearizationKey,
        Rkg, Rtg,
    },
    ParametersError,
};
use fhe_math::{
    rq::{Context, Poly, SubstitutionExponent},
    zq::Modulus,
};
use itertools::{izip, Itertools};
use omr::{
    client::*,
    fhe::bfv::{BfvParameters, BfvParametersBuilder, Encoding, SecretKey},
    fhe_traits::*,
    pvw::{PvwParameters, PvwPublicKey, PvwSecretKey},
    server::*,
    utils::*,
    CT_SPAN_COUNT, DEGREE, GAMMA, K, M, MODULI_OMR, MODULI_OMR_PT, M_ROW_SPAN, SET_SIZE,
};
use rand::{thread_rng, CryptoRng, Rng, RngCore, SeedableRng};
use rand_chacha::ChaChaRng;
use std::vec;
use std::{collections::HashMap, sync::Arc};

struct Party {
    key: SecretKey,
    rlk_eph_key: SecretKey,
}

fn group_detection_key<R: CryptoRng + RngCore>(
    bfv_params: &Arc<BfvParameters>,
    pvw_params: &Arc<PvwParameters>,
    pvw_sk: &PvwSecretKey,
    parties: &[Party],
    rng: &mut R,
) -> DetectionKey {
    // ckg
    let crp = Ckg::sample_crp(&bfv_params);
    let ckg = Ckg::new(&bfv_params, &crp);
    let shares = parties.iter().map(|p| ckg.gen_share(&p.key)).collect_vec();
    let agg_shares = ckg.aggregate_shares(&shares);
    let pk = PublicKey::new_from_ckg(&ckg, &agg_shares);
    let pvw_sk_cts = gen_pvw_sk_cts(bfv_params, pvw_params, &pk, &pvw_sk, rng);

    // gen rln keys
    let mut rlk_keys = HashMap::new();
    for i in 1..11 {
        let crps = Rkg::sample_crps(&bfv_params, i, i);
        let rkg = Rkg::new(bfv_params, i, i, &crps);
        let shares1 = parties
            .iter()
            .map(|p| rkg.gen_share_round1(&bfv_params, &p.key, &p.rlk_eph_key))
            .collect_vec();
        let agg_shares1 = rkg.aggregate_shares(&shares1);
        let shares2 = parties
            .iter()
            .map(|p| rkg.gen_share_round2(&bfv_params, &agg_shares1, &p.key, &p.rlk_eph_key))
            .collect_vec();
        let agg_shares2 = rkg.aggregate_shares(&shares2);
        rlk_keys.insert(
            i,
            RelinearizationKey::new_from_rkg(&rkg, &agg_shares2, &agg_shares1),
        );
    }

    // top rot key
    let ek1 = {
        let ctx = Arc::new(Context::new(&bfv_params.moduli(), bfv_params.degree()).unwrap());
        let crps = Rtg::sample_crps(&bfv_params, 0, 0);
        let rtg = Rtg::new(
            &bfv_params,
            0,
            0,
            &crps,
            SubstitutionExponent::new(&ctx, 3).unwrap(),
        );
        let shares = parties.iter().map(|p| rtg.gen_share(&p.key)).collect_vec();
        let agg_shares = rtg.aggregate_shares(&shares);
        let mut gk = HashMap::new();
        gk.insert(3, GaloisKey::new_from_rtg(&rtg, &agg_shares));
        EvaluationKey::new_from_gks(&bfv_params, 0, 0, gk, false).unwrap()
    };

    // pv selector rotation keys
    let mut gk = HashMap::new();
    let ctx = Arc::new(Context::new(bfv_params.moduli(), bfv_params.degree()).unwrap());
    for i in [3, bfv_params.degree() * 2 - 1] {
        let crps = Rtg::sample_crps(&bfv_params, 10, 10);
        let rtg = Rtg::new(
            &bfv_params,
            10,
            10,
            &crps,
            SubstitutionExponent::new(&ctx, i).unwrap(),
        );
        let shares = parties.iter().map(|p| rtg.gen_share(&p.key)).collect_vec();
        let agg_shares = rtg.aggregate_shares(&shares);
        gk.insert(i, GaloisKey::new_from_rtg(&rtg, &agg_shares));
    }
    let ek2 = EvaluationKey::new_from_gks(&bfv_params, 10, 10, gk, false).unwrap();

    // inner sum rot keys
    let mut gal_ells = vec![2 * bfv_params.degree() as u64 - 1];
    let mut i = 1;
    let q = Modulus::new(2 * bfv_params.degree() as u64).unwrap();
    while i < bfv_params.degree() / 2 {
        gal_ells.push(q.pow(3, i as u64));
        i *= 2;
    }
    let mut gk = HashMap::new();
    gal_ells.iter().for_each(|i| {
        let crps = Rtg::sample_crps(&bfv_params, 12, 12);
        let rtg = Rtg::new(
            &bfv_params,
            12,
            12,
            &crps,
            SubstitutionExponent::new(&ctx, *i as usize).unwrap(),
        );
        let shares = parties.iter().map(|p| rtg.gen_share(&p.key)).collect_vec();
        let agg_shares = rtg.aggregate_shares(&shares);
        gk.insert(*i as usize, GaloisKey::new_from_rtg(&rtg, &agg_shares));
    });
    let ek3 = EvaluationKey::new_from_gks(&bfv_params, 12, 12, gk, true).unwrap();

    DetectionKey {
        ek1,
        ek2,
        ek3,
        rlk_keys,
        pvw_sk_cts: pvw_sk_cts.try_into().unwrap(),
    }
}

fn calculate_detection_key_size() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let pvw_params = Arc::new(PvwParameters::default());
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
    let s = serialize_detection_key(&key);
    println!("Detection key size: {}MB", s.len() as f64 / 1000000.0)
}

fn group_run() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            // .set_moduli_sizes(&[
            // 28, 39, 60, 60, 60, 60, 60, 60, 60, 60, 60, 60, 32, 30, 60, 60,
            // ])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1) as usize;
    let pvw_params = Arc::new(PvwParameters::default());

    let no_of_parties = 10;
    let parties = (0..no_of_parties)
        .map(|i| Party {
            key: SecretKey::random(&bfv_params, &mut rng),
            rlk_eph_key: SecretKey::random(&bfv_params, &mut rng),
        })
        .collect_vec();
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);
    let detection_key = group_detection_key(&bfv_params, &pvw_params, &pvw_sk, &parties, &mut rng);

    let mut pertinent_indices = gen_pertinent_indices(50, SET_SIZE);
    pertinent_indices.sort();
    println!("Pertinent indices: {:?}", pertinent_indices);
    let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, SET_SIZE);
    let payloads = gen_paylods(SET_SIZE);

    let mut pertinent_payloads = vec![];
    (0..SET_SIZE)
        .zip(payloads.iter())
        .for_each(|(index, load)| {
            if pertinent_indices.contains(&index) {
                pertinent_payloads.push(load.clone());
            }
        });

    let dummy_bfv_sk = SecretKey::random(&bfv_params, &mut rng);

    // SERVER SIDE //
    println!("Server: Starting OMR...");
    let now = std::time::Instant::now();
    let mut pertinency_cts = phase1(
        &bfv_params,
        &pvw_params,
        &detection_key.pvw_sk_cts,
        &detection_key.ek1,
        &detection_key.rlk_keys,
        &clues,
        &dummy_bfv_sk,
    );

    // seeded rng for buckets
    let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
    thread_rng().fill(&mut seed);
    let mut rng = ChaChaRng::from_seed(seed);
    let (assigned_buckets, assigned_weights) =
        assign_buckets(M, GAMMA, MODULI_OMR_PT[0], SET_SIZE, &mut rng);

    let (pv_ct, msg_cts) = phase2(
        &assigned_buckets,
        &assigned_weights,
        &bfv_params,
        &detection_key.ek2,
        &detection_key.ek3,
        &mut pertinency_cts,
        &payloads,
        32,
        DEGREE,
        10,
        SET_SIZE,
        GAMMA,
        CT_SPAN_COUNT,
        M,
        M_ROW_SPAN,
        &dummy_bfv_sk,
    );

    println!("Total server time: {:?}", now.elapsed());

    // collectively decrypt pv and msgs ct
    let recv_sk = SecretKey::random(&bfv_params, &mut rng);
    let recv_pk = PublicKey::new(&recv_sk, &mut rng);
    let pv = {
        let pcks = Pcks::new(&pv_ct, &recv_pk);
        let shares = parties.iter().map(|p| pcks.gen_share(&p.key)).collect_vec();
        let ks_ct = pcks.key_switch(&shares);
        let m = Vec::<u64>::try_decode(&recv_sk.try_decrypt(&ks_ct).unwrap(), Encoding::simd())
            .unwrap();
        pv_decompress(&m, pt_bits)
    };
    {
        let mut indices = vec![];
        pv.iter().enumerate().for_each(|(index, bit)| {
            if *bit == 1 {
                indices.push(index);
            }
        });
        assert_eq!(pertinent_indices, indices);
    }
}

fn run() {
    let mut rng = thread_rng();
    let bfv_params = Arc::new(
        BfvParametersBuilder::new()
            .set_degree(DEGREE)
            .set_plaintext_modulus(MODULI_OMR_PT[0])
            .set_moduli(MODULI_OMR)
            .build()
            .unwrap(),
    );
    let pt_bits = (64 - bfv_params.plaintext().leading_zeros() - 1) as usize;
    let pvw_params = Arc::new(PvwParameters::default());

    // CLIENT SETUP //
    let bfv_sk = SecretKey::random(&bfv_params, &mut rng);
    let pvw_sk = PvwSecretKey::random(&pvw_params, &mut rng);
    let pvw_pk = pvw_sk.public_key(&mut rng);

    // pvw secret key encrypted under bfv
    println!("Generating client keys");
    let d_key = gen_detection_key(&bfv_params, &pvw_params, &bfv_sk, &pvw_sk, &mut rng);
    let d_key_serialized = serialize_detection_key(&d_key);

    let mut pertinent_indices = gen_pertinent_indices(50, SET_SIZE);
    pertinent_indices.sort();
    println!("Pertinent indices: {:?}", pertinent_indices);
    let clues = gen_clues(&pvw_params, &pvw_pk, &pertinent_indices, SET_SIZE);
    let payloads = gen_paylods(SET_SIZE);

    let mut pertinent_payloads = vec![];
    (0..SET_SIZE)
        .zip(payloads.iter())
        .for_each(|(index, load)| {
            if pertinent_indices.contains(&index) {
                pertinent_payloads.push(load.clone());
            }
        });

    // SERVER SIDE //
    println!("Server: Starting OMR...");
    let now = std::time::Instant::now();
    let message_digest_bytes = server_process(&clues, &payloads, &d_key_serialized);
    println!("Total server time: {:?}", now.elapsed());

    // CLIENT SIDE //
    println!("Client: Processing digest");
    let now = std::time::Instant::now();

    let message_digest = deserialize_message_digest(&bfv_params, &message_digest_bytes);

    let pt = bfv_sk.try_decrypt(&message_digest.pv).unwrap();
    let pv_values = Vec::<u64>::try_decode(&pt, Encoding::simd()).unwrap();
    let pv = pv_decompress(&pv_values, pt_bits);
    // {
    //     let mut res_indices = vec![];
    //     pv.iter().enumerate().for_each(|(index, bit)| {
    //         if *bit == 1 {
    //             res_indices.push(index);
    //         }
    //     });
    //     pertinent_indices.sort();
    //     assert_eq!(pertinent_indices, res_indices);
    //     // println!("Expected indices {:?}", pertinent_indices);
    //     // println!("Res indices      {:?}", res_indices);
    //     // assert!(false);
    // }
    let mut rng = ChaChaRng::from_seed(message_digest.seed);
    let (assigned_buckets, assigned_weights) =
        assign_buckets(M, GAMMA, MODULI_OMR_PT[0], SET_SIZE, &mut rng);
    let lhs = construct_lhs(
        &pv,
        assigned_buckets,
        assigned_weights,
        M,
        K,
        GAMMA,
        SET_SIZE,
    );

    let m_rows = message_digest
        .msgs
        .iter()
        .flat_map(|m| {
            Vec::<u64>::try_decode(&bfv_sk.try_decrypt(m).unwrap(), Encoding::simd()).unwrap()
        })
        .collect_vec();
    let rhs = construct_rhs(&m_rows, M, M_ROW_SPAN, MODULI_OMR_PT[0]);
    let res_payloads = solve_equations(lhs, rhs, MODULI_OMR_PT[0]);
    println!("Total client time: {:?}", now.elapsed());

    assert_eq!(pertinent_payloads, res_payloads);
}

fn main() {
    let val = std::env::args().nth(1).map(|v| {
        v.as_str()
            .parse::<usize>()
            .expect("Choose 1 to run demo. Choose 2 to display detection key size")
    });

    match val {
        Some(1) => run(),
        Some(2) => calculate_detection_key_size(),
        Some(3) => group_run(),
        _ => {
            println!("Choose 1 to run demo. Choose 2 to display detection key size")
        }
    }
}
