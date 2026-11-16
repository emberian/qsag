//! Tests for the sharing engine and the threshold ML-DSA protocol. Every
//! party runs in its own thread against an in-memory synchronous network; a
//! corrupt party is modelled by rewriting its outgoing messages.

use super::*;
use crate::fips204_ntt::{ml_dsa_sign_deterministic, signing_key_from_secret_for_test};
use crate::rss_mpc::test_support::{arm_additive_fault, arm_binary_fault, deal};
use crate::rss_mpc::{MpcTransportError, RoundInbox, RoundInfo, RoundKind};
use std::boxed::Box;
use std::println;
use std::sync::{Arc, Condvar, Mutex};
use std::time::Instant;

type Tamper = Box<dyn FnMut(&RoundInfo, &mut Vec<Vec<u8>>, &mut Vec<u8>) + Send>;

struct Posted {
    kind: RoundKind,
    private: Vec<Vec<u8>>,
    broadcast: Vec<u8>,
}

struct NetState {
    round: u64,
    posted: Vec<Option<Posted>>,
    taken: Vec<bool>,
    stopped: bool,
    log: Vec<RoundInfo>,
}

struct LocalNet {
    state: Mutex<NetState>,
    changed: Condvar,
}

struct Endpoint {
    net: Arc<LocalNet>,
    me: usize,
    tamper: Option<Tamper>,
}

impl MpcTransport for Endpoint {
    fn exchange(
        &mut self,
        info: RoundInfo,
        mut private: Vec<Vec<u8>>,
        mut broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        if let Some(tamper) = &mut self.tamper {
            tamper(&info, &mut private, &mut broadcast);
        }
        let mut state = self.net.state.lock().unwrap();
        if state.stopped {
            return Err(MpcTransportError);
        }
        let my_round = state.round;
        if self.me == 0 {
            state.log.push(info);
        }
        state.posted[self.me] = Some(Posted {
            kind: info.kind,
            private,
            broadcast,
        });
        self.net.changed.notify_all();
        while !state.posted.iter().all(Option::is_some) && !state.stopped {
            state = self.net.changed.wait(state).unwrap();
        }
        if !state.posted.iter().all(Option::is_some) {
            return Err(MpcTransportError);
        }
        let parties = state.posted.len();
        let mut inbox = RoundInbox {
            private: vec![Vec::new(); parties],
            broadcast: vec![Vec::new(); parties],
        };
        for sender in 0..parties {
            let posted = state.posted[sender].as_ref().unwrap();
            if posted.kind != info.kind {
                return Err(MpcTransportError);
            }
            if sender != self.me {
                inbox.private[sender] = posted.private[self.me].clone();
                inbox.broadcast[sender] = posted.broadcast.clone();
            }
        }
        state.taken[self.me] = true;
        if state.taken.iter().all(|&t| t) {
            for slot in &mut state.posted {
                *slot = None;
            }
            state.taken.fill(false);
            state.round += 1;
            self.net.changed.notify_all();
        } else {
            while state.round == my_round && !state.stopped {
                state = self.net.changed.wait(state).unwrap();
            }
        }
        Ok(inbox)
    }
}

impl Drop for Endpoint {
    fn drop(&mut self) {
        let mut state = self.net.state.lock().unwrap();
        state.stopped = true;
        self.net.changed.notify_all();
    }
}

/// Runs `f(position, state, endpoint)` for every party and returns the
/// results and party 0's round log.
fn run<S: Send, R: Send>(
    states: Vec<S>,
    mut tampers: Vec<Option<Tamper>>,
    f: impl Fn(usize, S, &mut Endpoint) -> R + Sync,
) -> (Vec<R>, Vec<RoundInfo>) {
    let parties = states.len();
    tampers.resize_with(parties, || None);
    let net = Arc::new(LocalNet {
        state: Mutex::new(NetState {
            round: 0,
            posted: (0..parties).map(|_| None).collect(),
            taken: vec![false; parties],
            stopped: false,
            log: Vec::new(),
        }),
        changed: Condvar::new(),
    });
    let results = std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .zip(tampers)
            .enumerate()
            .map(|(me, (state, tamper))| {
                let mut endpoint = Endpoint {
                    net: net.clone(),
                    me,
                    tamper,
                };
                let f = &f;
                scope.spawn(move || f(me, state, &mut endpoint))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let log = net.state.lock().unwrap().log.clone();
    (results, log)
}

/// Flips the low bit of the first byte of the `nth` matching round's
/// private messages (to one recipient, or to all).
fn flip(kind: RoundKind, phase: u8, nth: usize, recipient: Option<usize>) -> Option<Tamper> {
    let mut seen = 0usize;
    Some(Box::new(move |info, private, _| {
        if info.kind == kind && info.phase == phase {
            if seen == nth {
                for (j, message) in private.iter_mut().enumerate() {
                    if recipient.is_none_or(|r| r == j) && !message.is_empty() {
                        message[0] ^= 1;
                    }
                }
            }
            seen += 1;
        }
    }))
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn field(&mut self) -> u32 {
        (self.next() % MLDSA_Q as u64) as u32
    }
}

struct AllowBurn;
impl NonceBurnPersistence for AllowBurn {
    fn reserve(&mut self, _: u16, _: u64, _: &[u8; 32], _: u32) -> bool {
        true
    }
}

fn engine_for<'a>(net: &'a mut Endpoint, st: &Structure, me: usize) -> Engine<'a, Endpoint> {
    Engine::setup(net, st.clone(), me, &[7; 32], &[me as u8 + 1; 32]).unwrap()
}

fn bit_planes(st: &Structure, me: usize, values: &[u32], seed: u8) -> Vec<Sh> {
    (0..MASK_BITS)
        .map(|i| {
            let plane: Vec<u32> = values.iter().map(|&v| (v >> i) & 1).collect();
            deal(st, me, &plane, seed.wrapping_add(8 * i as u8))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

#[test]
fn engine_products_open_to_plaintext_products() {
    for (parties, threshold) in [(3, 2), (5, 2), (5, 3), (6, 2), (7, 4)] {
        let st = Structure::new(parties, threshold).unwrap();
        let mut rng = Rng(parties as u64 * 10 + threshold as u64);
        let x: Vec<u32> = (0..97).map(|_| rng.field()).collect();
        let y: Vec<u32> = (0..97).map(|_| rng.field()).collect();
        let (results, _) = run(vec![(); parties], Vec::new(), |me, (), net| {
            let mut engine = engine_for(net, &st, me);
            let xs = deal(&st, me, &x, 1);
            let ys = deal(&st, me, &y, 50);
            let xy = engine.mul(&xs, &ys)?;
            let xyx = engine.mul(&xy, &xs)?;
            let random_bits = engine.rand_bits(64)?;
            let opened = engine.open(&[&xy, &xyx, &random_bits])?;
            Ok::<_, MpcError>((opened, engine.stats()))
        });
        let mut first: Option<Vec<Vec<u32>>> = None;
        for result in results {
            let (opened, stats) = result.unwrap();
            for k in 0..x.len() {
                assert_eq!(opened[0][k], fq_mul_ref(x[k], y[k]));
                assert_eq!(opened[1][k], fq_mul_ref(fq_mul_ref(x[k], y[k]), x[k]));
            }
            assert!(
                opened[2].iter().all(|&b| b <= 1),
                "random bits must be bits"
            );
            assert!(opened[2].contains(&0) && opened[2].contains(&1));
            assert_eq!(stats.verifications, 1);
            match &first {
                None => first = Some(opened),
                Some(reference) => assert_eq!(reference, &opened, "parties must agree"),
            }
        }
    }
}

fn fq_mul_ref(a: u32, b: u32) -> u32 {
    ((a as u64 * b as u64) % MLDSA_Q as u64) as u32
}

#[test]
fn engine_rejects_an_additive_fault_before_opening() {
    // In (2,3) each correction has one recipient: the fault is a pure
    // additive error and only the multiplication check can catch it.
    for nth in [0usize, 1] {
        let st = Structure::new(3, 2).unwrap();
        let x: Vec<u32> = (1..=40).collect();
        let (results, log) = run(vec![(); 3], Vec::new(), |me, (), net| {
            if me == 1 {
                arm_additive_fault(0, nth);
            }
            let mut engine = engine_for(net, &st, me);
            let xs = deal(&st, me, &x, 3);
            let sq = engine.mul(&xs, &xs)?;
            let cube = engine.mul(&sq, &xs)?;
            let result = engine.open(&[&cube]);
            if result.is_err() {
                assert_eq!(engine.verify(), Err(MpcError::Poisoned));
                assert_eq!(engine.open(&[&xs]).unwrap_err(), MpcError::Poisoned);
                assert_eq!(engine.mul(&xs, &xs).unwrap_err(), MpcError::Poisoned);
                assert_eq!(engine.rand(1).unwrap_err(), MpcError::Poisoned);
                assert_eq!(engine.rand_bits(1).unwrap_err(), MpcError::Poisoned);
                assert_eq!(engine.public(&[1]).unwrap_err(), MpcError::Poisoned);
                assert_eq!(engine.zeros(1).unwrap_err(), MpcError::Poisoned);
            }
            result
        });
        for (me, result) in results.into_iter().enumerate() {
            assert_eq!(
                result.unwrap_err(),
                MpcError::MultiplicationCheckFailed,
                "party {me}"
            );
        }
        // The last round is the verification opening; the value is never opened.
        let opens = log.iter().filter(|r| r.kind == RoundKind::Open).count();
        let coins_and_final = log
            .iter()
            .filter(|r| r.kind == RoundKind::VerifyReshare)
            .count()
            + 1;
        assert_eq!(
            opens, coins_and_final,
            "only verification coins and its final opening"
        );
    }
}

#[test]
fn engine_rejects_equivocated_shares_by_view_digest() {
    // In (2,5) a correction goes to three holders. Sending one of them a
    // different value splits the honest holders' views.
    let st = Structure::new(5, 2).unwrap();
    let x: Vec<u32> = (1..=40).collect();
    let mut tampers: Vec<Option<Tamper>> = (0..5).map(|_| None).collect();
    let mut hit = false;
    tampers[1] = Some(Box::new(move |info, private, _| {
        if info.kind == RoundKind::Multiply
            && !hit
            && let Some(message) = private.iter_mut().find(|m| !m.is_empty())
        {
            message[0] ^= 1;
            hit = true;
        }
    }));
    let (results, _) = run(vec![(); 5], tampers, |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        let xs = deal(&st, me, &x, 3);
        let sq = engine.mul(&xs, &xs)?;
        let result = engine.open(&[&sq]);
        if result.is_err() {
            assert_eq!(engine.verify(), Err(MpcError::Poisoned));
            assert_eq!(engine.open(&[&xs]).unwrap_err(), MpcError::Poisoned);
            assert_eq!(engine.mul(&xs, &xs).unwrap_err(), MpcError::Poisoned);
        }
        result
    });
    for (me, result) in results.into_iter().enumerate() {
        if me != 1 {
            assert!(matches!(
                result.unwrap_err(),
                MpcError::ViewDigestMismatch { .. }
            ));
        }
    }
}

#[test]
fn engine_rejects_a_substituted_opening() {
    let st = Structure::new(3, 2).unwrap();
    let x: Vec<u32> = (1..=40).collect();
    let tampers = vec![None, flip(RoundKind::Open, 0, 0, None), None];
    let (results, _) = run(vec![(); 3], tampers, |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        let xs = deal(&st, me, &x, 3);
        let result = engine.open(&[&xs]);
        if result.is_err() {
            assert_eq!(engine.verify(), Err(MpcError::Poisoned));
            assert_eq!(engine.open(&[&xs]).unwrap_err(), MpcError::Poisoned);
            assert_eq!(engine.mul(&xs, &xs).unwrap_err(), MpcError::Poisoned);
        }
        result
    });
    // Party 1 is the designated sender of subset {1,2} to party 0.
    assert!(matches!(
        results[0],
        Err(MpcError::OpeningInconsistent { .. })
    ));
    if let Ok(opened) = &results[2] {
        assert_eq!(opened[0], x);
    }
}

#[test]
fn comparison_and_range_tests_match_plaintext() {
    let st = Structure::new(3, 2).unwrap();
    let mut rng = Rng(99);
    // r < q flags, including values at and above q.
    let mut raw: Vec<u32> = vec![
        0,
        1,
        MLDSA_Q - 1,
        MLDSA_Q,
        MLDSA_Q + 1,
        (1 << 23) - 1,
        1 << 22,
    ];
    raw.extend((0..60).map(|_| (rng.next() & 0x7F_FFFF) as u32));
    // Range tests with several widths, masks and positions around the edges.
    let mut hidden = Vec::new();
    let mut widths = Vec::new();
    let mut masks = Vec::new();
    for width in [1u32, 2, 261_887, 190_307, MLDSA_Q - 1] {
        for e in [0, 1, width - 1, width, width + 1, MLDSA_Q - 1, MLDSA_Q / 2] {
            for mask in [0, 1, MLDSA_Q - 1, rng.field(), rng.field()] {
                hidden.push(e % MLDSA_Q);
                widths.push(width);
                masks.push(mask);
            }
        }
    }
    let opened: Vec<u32> = hidden
        .iter()
        .zip(&masks)
        .map(|(&e, &r)| fq_add(e, r))
        .collect();
    let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        let raw_planes = bit_planes(&st, me, &raw, 1);
        let in_field = less_than_public(&mut engine, &raw_planes, &vec![MLDSA_Q; raw.len()])?;
        let mask_planes = bit_planes(&st, me, &masks, 2);
        let inside = masked_range_test(&mut engine, &opened, &widths, &mask_planes)?;
        engine.open(&[&in_field, &inside])
    });
    for result in results {
        let out = result.unwrap();
        for (k, &v) in raw.iter().enumerate() {
            assert_eq!(out[0][k], (v < MLDSA_Q) as u32, "in-field flag for {v}");
        }
        for k in 0..hidden.len() {
            assert_eq!(
                out[1][k],
                (hidden[k] < widths[k]) as u32,
                "e={} width={}",
                hidden[k],
                widths[k]
            );
        }
    }
}

#[test]
fn high_bits_circuit_matches_fips_decompose() {
    let gamma2 = (MLDSA_Q - 1) / 88;
    let alpha = 2 * gamma2;
    let st = Structure::new(3, 2).unwrap();
    let mut rng = Rng(5);
    let mut w: Vec<u32> = vec![
        0,
        1,
        gamma2 - 1,
        gamma2,
        gamma2 + 1,
        MLDSA_Q - gamma2 - 1,
        MLDSA_Q - gamma2,
        MLDSA_Q - gamma2 + 1,
        MLDSA_Q - 2,
        MLDSA_Q - 1,
    ];
    for j in 1..44u32 {
        w.extend([
            j * alpha - gamma2,
            j * alpha - gamma2 + 1,
            j * alpha,
            j * alpha + gamma2,
            (j * alpha + gamma2 + 1) % MLDSA_Q,
        ]);
    }
    w.extend((0..200).map(|_| rng.field()));
    // Every value is tested under an adversarially chosen and a random mask.
    let mut values = Vec::new();
    let mut masks = Vec::new();
    for &value in &w {
        for mask in [
            0,
            MLDSA_Q - 1,
            fq_sub(0, fq_add(value, gamma2 - 1)),
            fq_add(1, fq_sub(0, fq_add(value, gamma2 - 1))),
            rng.field(),
        ] {
            values.push(value);
            masks.push(mask);
        }
    }
    let opened: Vec<u32> = values
        .iter()
        .zip(&masks)
        .map(|(&v, &r)| fq_add(fq_add(v, gamma2 - 1), r))
        .collect();
    let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        let planes = bit_planes(&st, me, &masks, 9);
        let w1 = high_bits_circuit(&mut engine, &opened, &planes)?;
        Ok::<_, MpcError>((engine.open(&[&w1])?, engine.stats()))
    });
    for result in results {
        let (out, stats) = result.unwrap();
        for (k, &value) in values.iter().enumerate() {
            assert_eq!(
                out[0][k],
                high_bits_ct(value, gamma2),
                "w={value} mask={}",
                masks[k]
            );
        }
        assert_eq!(stats.multiplications as usize, 131 * values.len());
    }
}

#[test]
fn rejection_verdict_is_the_exact_fips_predicate() {
    let params = MlDsaLevel::MlDsa44.params();
    let z_bound = params.gamma1 - params.beta;
    let low_bound = params.gamma2 - params.beta;
    let st = Structure::new(3, 2).unwrap();
    let centred = |v: i64| v.rem_euclid(MLDSA_Q as i64) as u32;
    let zb = z_bound as i64;
    let lb = low_bound as i64;
    // (z coefficients, low coefficients, expected acceptance)
    let cases: Vec<(Vec<i64>, Vec<i64>, bool)> = vec![
        (
            vec![0, 1, -1, zb - 1, -(zb - 1)],
            vec![0, lb - 1, -(lb - 1), 5],
            true,
        ),
        (vec![0, zb, 3], vec![0, 1], false),
        (vec![0, -zb, 3], vec![0, 1], false),
        (vec![0, zb + 77, 3], vec![0, 1], false),
        (vec![1, 2, 3], vec![lb, 0], false),
        (vec![1, 2, 3], vec![0, -lb], false),
        (vec![1, 2, 3], vec![(MLDSA_Q / 2) as i64, 0], false),
        (vec![zb, zb, zb], vec![lb, lb], false),
        (vec![zb - 1, 1 - zb, 0], vec![lb - 1, 1 - lb], true),
    ];
    for (index, (z, low, expected)) in cases.iter().enumerate() {
        let z: Vec<u32> = z.iter().map(|&v| centred(v)).collect();
        let low: Vec<u32> = low.iter().map(|&v| centred(v)).collect();
        let mut rng = Rng(1000 + index as u64);
        let masks: Vec<u32> = (0..z.len() + low.len()).map(|_| rng.field()).collect();
        let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
            let mut engine = engine_for(net, &st, me);
            let planes = bit_planes(&st, me, &masks, 4);
            let mask_values = compose(&planes);
            let z_sh = deal(&st, me, &z, 100);
            let z_masked = z_sh
                .add(&engine.public_const(z_bound - 1, z.len())?)
                .add(&mask_values.slice(0, z.len()));
            let low_masks = mask_values.slice(z.len(), low.len());
            rejection_verdict(
                &mut engine,
                (&z_masked, z_bound),
                (&deal(&st, me, &low, 200), low_bound, &low_masks),
                &planes,
                low_bound + 1,
            )
        });
        for result in results {
            let accepted = result
                .unwrap()
                .is_some_and(|(z, low, high)| z && low && high);
            assert_eq!(accepted, *expected, "case {index}");
        }
    }
}

// ---------------------------------------------------------------------------
// Protocol
// ---------------------------------------------------------------------------

fn dkg_level(
    level: MlDsaLevel,
    ids: &[u16],
    threshold: usize,
    session: u8,
) -> Vec<ThresholdMlDsaSignerShare> {
    let config = ThresholdMlDsaDkgConfig {
        level,
        threshold,
        party_ids: ids.to_vec(),
        session_id: [session; 32],
    };
    let mut sorted = ids.to_vec();
    sorted.sort_unstable();
    let (results, _) = run(sorted.clone(), Vec::new(), |me, id, net| {
        threshold_mldsa_dkg_party(&config, id, &[session ^ (me as u8 + 0x11); 32], net)
    });
    results
        .into_iter()
        .map(|r| r.expect("honest key generation succeeds"))
        .collect()
}

fn dkg(ids: &[u16], threshold: usize, session: u8) -> Vec<ThresholdMlDsaSignerShare> {
    dkg_level(MlDsaLevel::MlDsa44, ids, threshold, session)
}

type SignResults = Vec<Result<ThresholdSignOutput, ThresholdMlDsaError>>;

fn sign(
    shares: &mut [ThresholdMlDsaSignerShare],
    quorum: &[u16],
    session: u8,
    msg: &[u8],
    tampers: Vec<Option<Tamper>>,
    additive_fault: Option<(usize, u8, usize)>,
) -> (SignResults, Vec<RoundInfo>) {
    let request = ThresholdSignSession {
        session_id: [session; 32],
        quorum: quorum.to_vec(),
    };
    let states: Vec<&mut ThresholdMlDsaSignerShare> = shares
        .iter_mut()
        .filter(|s| quorum.contains(&s.party_id()))
        .collect();
    run(states, tampers, |me, share, net| {
        if let Some((party, phase, nth)) = additive_fault
            && party == me
        {
            arm_additive_fault(phase, nth);
        }
        threshold_sign_mldsa_party(
            share,
            &request,
            msg,
            b"ctx",
            &[session ^ (me as u8 + 0x61); 32],
            &mut AllowBurn,
            net,
        )
    })
}

/// Sums each distinct subset component once: the secret no party holds.
fn reconstruct(shares: &[ThresholdMlDsaSignerShare]) -> (Vec<Poly256>, Vec<Poly256>) {
    let params = shares[0].verification_pack().level.params();
    let mut seen: Vec<(Vec<usize>, Vec<Poly256>, Vec<Poly256>)> = Vec::new();
    for share in shares {
        for (holders, s1, s2) in share.components_for_test() {
            match seen.iter().find(|entry| entry.0 == holders) {
                Some(entry) => assert!(
                    entry.1 == s1 && entry.2 == s2,
                    "holders of a subset must agree"
                ),
                None => seen.push((holders, s1, s2)),
            }
        }
    }
    let mut s1 = vec![Poly256::zero(); params.ell];
    let mut s2 = vec![Poly256::zero(); params.k];
    for (_, a, b) in &seen {
        for (acc, poly) in s1.iter_mut().zip(a) {
            *acc = acc.add(poly);
        }
        for (acc, poly) in s2.iter_mut().zip(b) {
            *acc = acc.add(poly);
        }
    }
    (inv_ntt_all(s1), inv_ntt_all(s2))
}

fn assert_fips_key(shares: &[ThresholdMlDsaSignerShare]) {
    let pack = shares[0].verification_pack().clone();
    let params = pack.level.params();
    let eta = params.eta as i64;
    let bins = (2 * params.eta + 1) as usize;
    assert!(shares.iter().all(|s| s.verification_pack() == &pack));
    assert_eq!(pack.pk_bytes.len(), params.pk_bytes);
    let (s1, s2) = reconstruct(shares);
    let mut histogram = vec![0usize; bins];
    for poly in s1.iter().chain(&s2) {
        for &c in &poly.coeffs {
            let centred = if c > MLDSA_Q / 2 {
                c as i64 - MLDSA_Q as i64
            } else {
                c as i64
            };
            assert!(
                (-eta..=eta).contains(&centred),
                "coefficient {centred} outside [-eta, eta]"
            );
            histogram[(centred + eta) as usize] += 1;
        }
    }
    let total_draws = (params.ell + params.k) * MLDSA_N;
    let mean = total_draws / bins;
    assert!(
        histogram
            .iter()
            .all(|&count| count >= mean * 6 / 10 && count <= mean * 14 / 10),
        "{histogram:?}"
    );
    // The public key is the standard key of this secret, and the standard
    // signer with this secret verifies under it.
    let (standard_pk, standard_sk) = signing_key_from_secret_for_test(pack.level, pack.rho, s1, s2);
    assert_eq!(standard_pk, pack.pk_bytes);
    let signature = ml_dsa_sign_deterministic(&standard_sk, b"standard signer", b"").unwrap();
    assert!(ml_dsa_verify(
        pack.level,
        &pack.pk_bytes,
        b"standard signer",
        b"",
        &signature
    ));
}

#[test]
fn two_of_three_keygen_and_signing_are_standard_fips204() {
    let started = Instant::now();
    let mut shares = dkg(&[30, 10, 20], 2, 1);
    let keygen = started.elapsed();
    assert_fips_key(&shares);
    let pk = shares[0].verification_pack().pk_bytes.clone();

    for (session, msg) in [
        (2u8, &b"threshold message one"[..]),
        (3, &b"threshold message two"[..]),
    ] {
        let started = Instant::now();
        let (results, log) = sign(&mut shares, &[10, 20, 30], session, msg, Vec::new(), None);
        let elapsed = started.elapsed();
        let outputs: Vec<ThresholdSignOutput> = results.into_iter().map(|r| r.unwrap()).collect();
        assert!(outputs.iter().all(|o| o.signature == outputs[0].signature));
        assert_eq!(outputs[0].signature.len(), 2420);
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            msg,
            b"ctx",
            &outputs[0].signature
        ));
        assert!(!ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            b"another message",
            b"ctx",
            &outputs[0].signature
        ));
        assert!(!ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            msg,
            b"other",
            &outputs[0].signature
        ));
        // z is released at most once per attempt, and only straight after a
        // verdict opening of the rejection phase.
        let releases: Vec<usize> = (0..log.len())
            .filter(|&i| log[i].phase == PHASE_SIGN_RELEASE)
            .collect();
        assert!(!releases.is_empty() && releases.len() <= outputs[0].attempts as usize);
        for &i in &releases {
            assert_eq!(log[i].kind, RoundKind::Open);
            assert_eq!(
                (log[i - 1].phase, log[i - 1].kind),
                (PHASE_SIGN_REJECTION, RoundKind::Open)
            );
        }
        let bytes: u64 = outputs.iter().map(|o| o.stats.bytes_sent).sum();
        println!(
            "MEASURE (2,3) sign: attempts={} rounds={} bytes_all_parties={} multiplications={} elapsed_ms={:.1} per_attempt_ms={:.1}",
            outputs[0].attempts,
            outputs[0].stats.rounds,
            bytes,
            outputs[0].stats.multiplications,
            elapsed.as_secs_f64() * 1e3,
            elapsed.as_secs_f64() * 1e3 / outputs[0].attempts as f64,
        );
    }
    println!(
        "MEASURE (2,3) keygen: elapsed_ms={:.1}",
        keygen.as_secs_f64() * 1e3
    );
}

#[test]
fn two_of_five_signs_with_any_three_custodians() {
    let started = Instant::now();
    let mut shares = dkg(&[1, 2, 3, 4, 5], 2, 4);
    println!(
        "MEASURE (2,5) keygen: elapsed_ms={:.1}",
        started.elapsed().as_secs_f64() * 1e3
    );
    assert_fips_key(&shares);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    for (session, quorum) in [(5u8, [1u16, 3, 5]), (6, [2, 3, 4])] {
        let started = Instant::now();
        let (results, _) = sign(
            &mut shares,
            &quorum,
            session,
            b"any three of five",
            Vec::new(),
            None,
        );
        let elapsed = started.elapsed();
        let outputs: Vec<ThresholdSignOutput> = results.into_iter().map(|r| r.unwrap()).collect();
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            b"any three of five",
            b"ctx",
            &outputs[0].signature
        ));
        let bytes: u64 = outputs.iter().map(|o| o.stats.bytes_sent).sum();
        println!(
            "MEASURE (2,5) sign quorum {:?}: attempts={} rounds={} bytes_all_parties={} elapsed_ms={:.1}",
            quorum,
            outputs[0].attempts,
            outputs[0].stats.rounds,
            bytes,
            elapsed.as_secs_f64() * 1e3,
        );
    }
}

#[test]
fn three_of_five_keygen_is_standard_fips204() {
    let started = Instant::now();
    let shares = dkg(&[1, 2, 3, 4, 5], 3, 7);
    println!(
        "MEASURE (3,5) keygen: elapsed_ms={:.1}",
        started.elapsed().as_secs_f64() * 1e3
    );
    assert_fips_key(&shares);
    let other = dkg(&[1, 2, 3, 4], 2, 8);
    assert_fips_key(&other);
}

#[test]
fn unsupported_configurations_and_quorums_are_rejected() {
    let mut net = Endpoint {
        net: Arc::new(LocalNet {
            state: Mutex::new(NetState {
                round: 0,
                posted: Vec::new(),
                taken: Vec::new(),
                stopped: true,
                log: Vec::new(),
            }),
            changed: Condvar::new(),
        }),
        me: 0,
        tamper: None,
    };
    let config = |level, threshold, ids: &[u16]| ThresholdMlDsaDkgConfig {
        level,
        threshold,
        party_ids: ids.to_vec(),
        session_id: [0; 32],
    };
    let attempt = |c: ThresholdMlDsaDkgConfig, net: &mut Endpoint| {
        threshold_mldsa_dkg_party(&c, 1, &[0; 32], net).unwrap_err()
    };
    assert_eq!(
        attempt(config(MlDsaLevel::MlDsa44, 2, &[1, 2]), &mut net),
        ThresholdMlDsaError::InsufficientHonestHolderCoverage {
            threshold: 2,
            num_parties: 2
        }
    );
    assert_eq!(
        attempt(config(MlDsaLevel::MlDsa44, 3, &[1, 2, 3, 4]), &mut net),
        ThresholdMlDsaError::InsufficientHonestHolderCoverage {
            threshold: 3,
            num_parties: 4
        }
    );
    assert_eq!(
        attempt(config(MlDsaLevel::MlDsa44, 1, &[1, 2, 3]), &mut net),
        ThresholdMlDsaError::InvalidThresholdParameters {
            threshold: 1,
            num_parties: 3
        }
    );
    assert!(
        config(MlDsaLevel::MlDsa87, 2, &[1, 2, 3, 4, 5, 6])
            .validate()
            .is_ok()
    );
    assert!(
        config(MlDsaLevel::MlDsa44, 8, &(1..=16).collect::<Vec<_>>())
            .validate()
            .is_ok()
    );
    for parties in [17, 64] {
        assert_eq!(
            attempt(
                config(
                    MlDsaLevel::MlDsa44,
                    2,
                    &(1..=parties as u16).collect::<Vec<_>>()
                ),
                &mut net
            ),
            ThresholdMlDsaError::Mpc(MpcError::UnsupportedStructure {
                parties,
                threshold: 2
            })
        );
    }
    assert_eq!(
        attempt(config(MlDsaLevel::MlDsa44, 2, &[1, 2, 2]), &mut net),
        ThresholdMlDsaError::DuplicateOrUnknownParty { party_id: 2 }
    );

    // Two custodians of a (2,3) key are a dishonest-majority quorum: refused.
    let mut shares = dkg(&[1, 2, 3], 2, 9);
    let request = ThresholdSignSession {
        session_id: [1; 32],
        quorum: vec![1, 2],
    };
    let error = threshold_sign_mldsa_party(
        &mut shares[0],
        &request,
        b"m",
        b"",
        &[0; 32],
        &mut AllowBurn,
        &mut net,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ThresholdMlDsaError::QuorumTooSmall { have: 2, need: 3 }
    );
    let request = ThresholdSignSession {
        session_id: [1; 32],
        quorum: vec![1, 2, 9],
    };
    let error = threshold_sign_mldsa_party(
        &mut shares[0],
        &request,
        b"m",
        b"",
        &[0; 32],
        &mut AllowBurn,
        &mut net,
    )
    .unwrap_err();
    assert_eq!(
        error,
        ThresholdMlDsaError::DuplicateOrUnknownParty { party_id: 9 }
    );
}

#[test]
fn a_refused_attempt_reservation_stops_before_any_mask_exists() {
    struct DenyBurn;
    impl NonceBurnPersistence for DenyBurn {
        fn reserve(&mut self, _: u16, _: u64, _: &[u8; 32], _: u32) -> bool {
            false
        }
    }
    let mut shares = dkg(&[1, 2, 3], 2, 12);
    let request = ThresholdSignSession {
        session_id: [3; 32],
        quorum: vec![1, 2, 3],
    };
    let states: Vec<&mut ThresholdMlDsaSignerShare> = shares.iter_mut().collect();
    let (results, log) = run(states, Vec::new(), |me, share, net| {
        threshold_sign_mldsa_party(
            share,
            &request,
            b"m",
            b"",
            &[me as u8; 32],
            &mut DenyBurn,
            net,
        )
    });
    assert!(
        results
            .iter()
            .all(|r| r == &Err(ThresholdMlDsaError::NoncePersistenceFailed))
    );
    assert!(log.iter().all(|r| r.phase == PHASE_SETUP));
}

#[test]
fn custodians_given_different_messages_never_start() {
    let mut shares = dkg(&[1, 2, 3], 2, 13);
    let request = ThresholdSignSession {
        session_id: [4; 32],
        quorum: vec![1, 2, 3],
    };
    let states: Vec<&mut ThresholdMlDsaSignerShare> = shares.iter_mut().collect();
    let (results, log) = run(states, Vec::new(), |me, share, net| {
        let msg: &[u8] = if me == 2 {
            b"pay mallory"
        } else {
            b"pay alice"
        };
        threshold_sign_mldsa_party(
            share,
            &request,
            msg,
            b"",
            &[me as u8 + 9; 32],
            &mut AllowBurn,
            net,
        )
    });
    for result in &results {
        assert!(matches!(
            result,
            Err(ThresholdMlDsaError::Mpc(
                MpcError::KeyConfirmationMismatch { .. }
            ))
        ));
    }
    assert!(
        log.iter()
            .all(|r| matches!(r.kind, RoundKind::KeySetup | RoundKind::KeyConfirm))
    );
}

#[test]
fn malformed_mask_share_aborts_before_anything_about_y_is_opened() {
    // The corrupt custodian adds an error to a product inside the bit
    // generation of y and the conversion masks, making a "bit" a non-bit.
    for nth in [0usize, 1, 7] {
        let mut shares = dkg(&[1, 2, 3], 2, 14);
        let fault = Some((1, PHASE_SIGN_MASKS, nth));
        let (results, log) = sign(
            &mut shares,
            &[1, 2, 3],
            20 + nth as u8,
            b"m",
            Vec::new(),
            fault,
        );
        for result in &results {
            assert_eq!(
                result,
                &Err(ThresholdMlDsaError::Mpc(
                    MpcError::MultiplicationCheckFailed
                ))
            );
        }
        assert!(
            log.iter().all(|r| r.phase <= PHASE_SIGN_MASKS),
            "no w1, verdict or z round may exist"
        );
        // The only openings are verification coins and the masked final claim.
        let opens = log
            .iter()
            .filter(|r| r.phase == PHASE_SIGN_MASKS && r.kind == RoundKind::Open)
            .count();
        let reshares = log
            .iter()
            .filter(|r| r.kind == RoundKind::VerifyReshare)
            .count();
        assert_eq!(opens, reshares + 1);
    }
}

#[test]
fn a_share_rewritten_in_transit_aborts_before_any_opening() {
    // Rewriting a correction on the wire makes sender and receiver views of
    // the subset differ; either the digest comparison or the multiplication
    // check must stop the session before w1, the verdict or z exist.
    let mut shares = dkg(&[1, 2, 3], 2, 19);
    let tampers = vec![
        None,
        flip(RoundKind::Multiply, PHASE_SIGN_MASKS, 1, None),
        None,
    ];
    let (results, log) = sign(&mut shares, &[1, 2, 3], 60, b"m", tampers, None);
    for (me, result) in results.iter().enumerate() {
        if me != 1 {
            assert!(matches!(
                result,
                Err(ThresholdMlDsaError::Mpc(
                    MpcError::ViewDigestMismatch { .. } | MpcError::MultiplicationCheckFailed
                ))
            ));
        }
    }
    assert!(log.iter().all(|r| r.phase <= PHASE_SIGN_MASKS));
}

#[test]
fn a_fault_in_high_bits_or_in_the_rejection_circuit_never_releases_z() {
    for (phase, nth) in [
        (PHASE_SIGN_HIGH_BITS, 0usize),
        (PHASE_SIGN_HIGH_BITS, 60),
        (PHASE_SIGN_REJECTION, 0),
        (PHASE_SIGN_REJECTION, 21),
        (PHASE_SIGN_REJECTION, 22),
    ] {
        let mut shares = dkg(&[1, 2, 3], 2, 15);
        let (results, log) = sign(
            &mut shares,
            &[1, 2, 3],
            30 + nth as u8,
            b"m",
            Vec::new(),
            Some((2, phase, nth)),
        );
        for result in &results {
            assert_eq!(
                result,
                &Err(ThresholdMlDsaError::Mpc(
                    MpcError::MultiplicationCheckFailed
                ))
            );
        }
        assert!(
            log.iter().all(|r| r.phase != PHASE_SIGN_RELEASE),
            "z must not be released"
        );
        assert!(
            log.iter().all(|r| r.phase <= phase),
            "abort happens inside the faulted phase"
        );
    }
}

#[test]
fn a_substituted_response_share_is_refused() {
    // After acceptance the corrupt custodian reports a z component that is
    // not the committed y component plus c times its key component.
    let mut shares = dkg(&[1, 2, 3], 2, 16);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    let tampers = vec![
        None,
        flip(RoundKind::Open, PHASE_SIGN_RELEASE, 0, None),
        None,
    ];
    let (results, _) = sign(&mut shares, &[1, 2, 3], 40, b"m", tampers, None);
    assert!(matches!(
        results[0],
        Err(ThresholdMlDsaError::Mpc(
            MpcError::OpeningInconsistent { .. }
        ))
    ));
    for result in results.iter().flatten() {
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            b"m",
            b"ctx",
            &result.signature
        ));
    }

    // Lying in the broadcast digest instead is seen by everyone.
    let mut shares = dkg(&[1, 2, 3], 2, 17);
    let mut tampers: Vec<Option<Tamper>> = vec![None, None, None];
    tampers[1] = Some(Box::new(|info, _, broadcast| {
        if info.kind == RoundKind::Open && info.phase == PHASE_SIGN_RELEASE {
            broadcast[0] ^= 1;
        }
    }));
    let (results, _) = sign(&mut shares, &[1, 2, 3], 41, b"m", tampers, None);
    for (me, result) in results.iter().enumerate() {
        if me != 1 {
            assert!(matches!(
                result,
                Err(ThresholdMlDsaError::Mpc(
                    MpcError::OpeningInconsistent { .. }
                ))
            ));
        }
    }
}

#[test]
fn rejected_attempts_expose_only_masked_values() {
    // Run sessions until one needs several attempts, then check the public
    // round structure of every rejected attempt: no release round.
    let mut shares = dkg(&[1, 2, 3], 2, 18);
    let mut session = 50u8;
    loop {
        let (results, log) = sign(
            &mut shares,
            &[1, 2, 3],
            session,
            b"abort structure",
            Vec::new(),
            None,
        );
        let output = results[0].clone().unwrap();
        session += 1;
        if output.attempts < 2 {
            continue;
        }
        // Split party 0's log into attempts at each return to the mask phase.
        let mut attempts: Vec<Vec<RoundInfo>> = Vec::new();
        for (i, record) in log.iter().enumerate() {
            if record.phase == PHASE_SIGN_MASKS && (i == 0 || log[i - 1].phase != PHASE_SIGN_MASKS)
            {
                attempts.push(Vec::new());
            }
            if let Some(current) = attempts.last_mut() {
                current.push(*record);
            }
        }
        assert_eq!(attempts.len(), output.attempts as usize);
        for attempt in &attempts {
            // PHASE_SIGN_HIGH_BITS must verify its circuit in place without opening w1:
            // its only RoundKind::Open messages are verify() coins and the masked final check.
            let hb_opens = attempt
                .iter()
                .filter(|r| r.phase == PHASE_SIGN_HIGH_BITS && r.kind == RoundKind::Open)
                .count();
            let hb_reshares = attempt
                .iter()
                .filter(|r| r.phase == PHASE_SIGN_HIGH_BITS && r.kind == RoundKind::VerifyReshare)
                .count();
            assert_eq!(
                hb_opens,
                hb_reshares + 1,
                "w1 must remain sealed during PHASE_SIGN_HIGH_BITS"
            );
        }
        let (last, rejected) = attempts.split_last().unwrap();
        for attempt in rejected {
            assert!(attempt.iter().all(|r| r.phase != PHASE_SIGN_RELEASE));
        }
        assert_eq!(
            last.iter()
                .filter(|r| r.phase == PHASE_SIGN_RELEASE)
                .count(),
            1
        );
        break;
    }
}

#[test]
fn attempt_counts_follow_the_fips_rejection_rate() {
    // ML-DSA-44 accepts an attempt with probability about 0.235. Twelve
    // sessions on one key: every signature verifies and the mean number of
    // attempts is plausible for that rate (the exact rate is not asserted).
    let mut shares = dkg(&[1, 2, 3], 2, 70);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    let mut attempts = Vec::new();
    let mut bytes = 0u64;
    let mut rounds = 0u64;
    let started = Instant::now();
    for session in 0..12u8 {
        let msg = [session; 9];
        let (results, _) = sign(
            &mut shares,
            &[1, 2, 3],
            100 + session,
            &msg,
            Vec::new(),
            None,
        );
        let outputs: Vec<ThresholdSignOutput> = results.into_iter().map(|r| r.unwrap()).collect();
        assert!(ml_dsa_verify(
            MlDsaLevel::MlDsa44,
            &pk,
            &msg,
            b"ctx",
            &outputs[0].signature
        ));
        attempts.push(outputs[0].attempts);
        rounds += outputs[0].stats.rounds;
        bytes += outputs.iter().map(|o| o.stats.bytes_sent).sum::<u64>();
    }
    let total: u32 = attempts.iter().sum();
    println!(
        "MEASURE (2,3) 12 signatures: attempts={attempts:?} total_attempts={total} mean_ms_per_signature={:.1} mean_bytes_per_signature={} mean_rounds_per_signature={}",
        started.elapsed().as_secs_f64() * 1e3 / 12.0,
        bytes / 12,
        rounds / 12,
    );
    assert!(
        attempts.iter().any(|&a| a != attempts[0]),
        "attempt counts must vary across sessions"
    );
    assert!(
        (20..=110).contains(&total),
        "mean attempts {} is implausible",
        total as f64 / 12.0
    );
}

#[test]
fn three_of_five_signs_with_all_five_custodians() {
    // Privacy threshold two: the quorum is all five, ten subsets of three.
    let mut shares = dkg(&[1, 2, 3, 4, 5], 3, 80);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    let started = Instant::now();
    let (results, _) = sign(
        &mut shares,
        &[1, 2, 3, 4, 5],
        81,
        b"three of five",
        Vec::new(),
        None,
    );
    let elapsed = started.elapsed();
    let outputs: Vec<ThresholdSignOutput> = results.into_iter().map(|r| r.unwrap()).collect();
    assert!(ml_dsa_verify(
        MlDsaLevel::MlDsa44,
        &pk,
        b"three of five",
        b"ctx",
        &outputs[0].signature
    ));
    let bytes: u64 = outputs.iter().map(|o| o.stats.bytes_sent).sum();
    println!(
        "MEASURE (3,5) sign: attempts={} rounds={} bytes_all_parties={} multiplications={} elapsed_ms={:.1}",
        outputs[0].attempts,
        outputs[0].stats.rounds,
        bytes,
        outputs[0].stats.multiplications,
        elapsed.as_secs_f64() * 1e3,
    );
}

#[test]
fn zero_width_range_returns_error_without_underflow() {
    let st = Structure::new(3, 2).unwrap();
    let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        assert_eq!(
            masked_range_test(&mut engine, &[0], &[0], &[]).unwrap_err(),
            MpcError::InvalidRange
        );
        assert_eq!(
            masked_range_test(&mut engine, &[0], &[], &[]).unwrap_err(),
            MpcError::InvalidRange
        );
        engine.verify()
    });
    for result in results {
        result.unwrap();
    }
}

#[cfg(feature = "std")]
#[test]
fn durable_nonce_restart_recovers_epoch_and_rejects_both_replay_keys() {
    let dir = std::env::temp_dir().join(std::format!("qsag-cred-nonce-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("burns");
    let (pk_bytes, _) = crate::fips204_ntt::ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[91; 32]);
    let pack = ThresholdVerificationPack {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: vec![1, 2, 3],
        rho: [0; 32],
        pk_bytes,
        t: Vec::new(),
    };
    let key_id = pack.policy_signing_key_id();
    let mac_key = [0x5E; 32];
    {
        let mut store = FsNonceBurnStore::create(&path, key_id, mac_key).unwrap();
        assert!(store.reserve(1, 7, &[3; 32], 2));
        assert!(!store.reserve(1, 7, &[4; 32], 3));
        assert!(!store.reserve(1, 8, &[3; 32], 2));
    }
    assert!(FsNonceBurnStore::open(&path, [0; 32], mac_key).is_err());
    assert!(FsNonceBurnStore::open(&path, key_id, [0x99; 32]).is_err());
    let snap_gen1 = std::fs::read(&path).unwrap();
    {
        let mut store = FsNonceBurnStore::open(&path, key_id, mac_key).unwrap();
        let mut restarted = ThresholdMlDsaSignerShare {
            party_id: 1,
            pack,
            subsets: Vec::new(),
            shamir: None,
            next_epoch: 0,
        };
        restarted.recover_epoch_from_store(&store).unwrap();
        assert_eq!(restarted.next_epoch, 8);
        assert!(!store.reserve(1, 7, &[9; 32], 0));
        assert!(!store.reserve(1, 8, &[3; 32], 2));
        assert!(store.reserve(1, 8, &[3; 32], 3));
        assert!(store.reserve(2, 0, &[3; 32], 2));
        restarted.recover_epoch_from_store(&store).unwrap();
        assert_eq!(restarted.next_epoch, 9);
    }
    let store = FsNonceBurnStore::open_at_least(&path, key_id, mac_key, 3).unwrap();
    let latest_gen = store.generation();
    assert_eq!(latest_gen, 3);
    assert_eq!(store.next_epoch(&key_id, 1).unwrap(), 9);
    drop(store);

    // Offline attacker truncates rows and zeroes `count` without the MAC key -> rejected!
    let mut raw = std::fs::read(&path).unwrap();
    let mut tampered = raw[..96].to_vec();
    tampered[56..64].copy_from_slice(&0u64.to_le_bytes());
    std::fs::write(&path, &tampered).unwrap();
    assert!(FsNonceBurnStore::open(&path, key_id, mac_key).is_err());

    // Offline attacker replays valid authenticated historical snapshot -> rejected by floor!
    std::fs::write(&path, &snap_gen1).unwrap();
    assert!(FsNonceBurnStore::open_at_least(&path, key_id, mac_key, latest_gen).is_err());
    raw.clear();
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn verified_response_gate_enforces_every_barrier_and_context() {
    let context = [37; 32];
    let seal_entropy = [91; 32];
    let good = MlDsaBarrierChecks {
        req_session_id: context,
        req_attempt: 9,
        z_norm_ok: true,
        r0_norm_ok: true,
        w1_match: true,
        u_com_bound: true,
    };
    let response = || Sh {
        c: vec![vec![1, 2, 3]],
    };
    let pending = PendingResponse::new_sealed(response(), context, 9, &seal_entropy);
    // The pending response must be XOF-encrypted in RAM while waiting on the barrier.
    assert_ne!(pending.sealed_response.c, vec![vec![1, 2, 3]]);
    let released = pending.release(good).unwrap();
    assert_eq!(released.c, vec![vec![1, 2, 3]]);

    // Ciphertext tampering before release must fail closed even when all barriers hold.
    let mut tampered = PendingResponse::new_sealed(response(), context, 9, &seal_entropy);
    tampered.sealed_response.c[0][0] = fq_add(tampered.sealed_response.c[0][0], 1);
    assert!(tampered.release(good).is_err());

    for mutation in 0..6 {
        let mut checks = good;
        match mutation {
            0 => checks.z_norm_ok = false,
            1 => checks.r0_norm_ok = false,
            2 => checks.w1_match = false,
            3 => checks.u_com_bound = false,
            4 => checks.req_session_id[0] ^= 1,
            _ => checks.req_attempt += 1,
        }
        assert!(
            PendingResponse::new_sealed(response(), context, 9, &seal_entropy)
                .release(checks)
                .is_err()
        );
    }
}

#[test]
fn high_bits_circuit_gamma2_q_minus_1_over_32_matches_fips_across_all_boundaries() {
    let gamma2 = (MLDSA_Q - 1) / 32;
    let alpha = 2 * gamma2;
    let mut values: Vec<u32> = vec![
        0,
        1,
        gamma2 - 1,
        gamma2,
        gamma2 + 1,
        MLDSA_Q - gamma2 - 2,
        MLDSA_Q - gamma2 - 1,
        MLDSA_Q - gamma2,
        MLDSA_Q - gamma2 + 1,
        MLDSA_Q - 2,
        MLDSA_Q - 1,
    ];
    for bin in 0..16u32 {
        let edge = bin * alpha + gamma2;
        for delta in [-2i64, -1, 0, 1, 2] {
            let v = (edge as i64 + delta).rem_euclid(MLDSA_Q as i64) as u32;
            values.push(v);
        }
    }
    let mut rng = Rng(0x6587);
    for _ in 0..128 {
        values.push(rng.field());
    }
    let masks: Vec<u32> = (0..values.len()).map(|_| rng.field()).collect();
    let opened: Vec<u32> = values
        .iter()
        .zip(&masks)
        .map(|(&v, &r)| fq_add(fq_add(v, gamma2 - 1), r))
        .collect();
    let st = Structure::new(3, 2).unwrap();
    let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
        let mut engine = engine_for(net, &st, me);
        let r = bit_planes(&st, me, &masks, 29);
        let (hb, planes) = high_bits_circuit_with_bits(&mut engine, &opened, &r, gamma2)?;
        assert_eq!(planes.len(), 4);
        let mut refs: Vec<&Sh> = vec![&hb];
        for p in &planes {
            refs.push(p);
        }
        engine.open(&refs)
    });
    for result in results {
        let out = result.unwrap();
        for (idx, &v) in values.iter().enumerate() {
            let expected = high_bits_ct(v, gamma2);
            assert_eq!(out[0][idx], expected, "value {v}");
            let mut composed = 0u32;
            for b in 0..4 {
                let bit = out[1 + b][idx];
                assert!(bit <= 1);
                composed |= bit << b;
            }
            assert_eq!(composed, expected, "bit planes for {v}");
        }
    }
}

#[test]
fn sealed_mpc_challenge_derivation_matches_fips204_across_all_three_levels() {
    for (level_idx, level) in [
        MlDsaLevel::MlDsa44,
        MlDsaLevel::MlDsa65,
        MlDsaLevel::MlDsa87,
    ]
    .into_iter()
    .enumerate()
    {
        let params = level.params();
        let w_len = params.k * MLDSA_N;
        let b_width = if params.w1_poly_bytes == 192 { 6 } else { 4 };
        let w1_bins = (MLDSA_Q - 1) / (2 * params.gamma2);
        let mut rng = Rng(0xC0DE_0000 + level_idx as u64);
        let w1_plain: Vec<u32> = (0..w_len).map(|_| rng.field() % w1_bins).collect();
        let w1_polys = to_polys(&w1_plain);
        let mu = [0x3Au8.wrapping_add(level_idx as u8 * 17); 64];

        let mut c_tilde = vec![0u8; params.c_tilde_bytes];
        let mut xof = Shake256::new();
        xof.absorb(&mu);
        xof.absorb(&w1_encode(&params, &w1_polys));
        xof.finalize(0x1F);
        xof.squeeze(&mut c_tilde);
        let expected_c = sample_in_ball(&c_tilde, params.tau);

        let st = Structure::new(3, 2).unwrap();
        let (results, _) = run(vec![(); 3], Vec::new(), |me, (), net| {
            let mut engine = engine_for(net, &st, me);
            let planes: Vec<Sh> = (0..b_width)
                .map(|d| {
                    let bits: Vec<u32> = w1_plain.iter().map(|&v| (v >> d) & 1).collect();
                    deal(&st, me, &bits, 41 + (d * 7) as u8)
                })
                .collect();
            let (c_sh, sib_inc_sh) = mpc_derive_challenge(&mut engine, &params, &mu, &planes)?;
            Ok::<_, ThresholdMlDsaError>(engine.open(&[&c_sh, &sib_inc_sh])?)
        });
        for result in results {
            let opened = result.unwrap();
            assert_eq!(opened[1], vec![0u32]);
            assert_eq!(opened[0].as_slice(), expected_c.coeffs.as_slice());
        }
    }
}

#[test]
fn binary_fault_in_sealed_keccak_or_sample_in_ball_aborts_before_key_multiply() {
    for nth in [0usize, 10, 40] {
        let mut shares = dkg(&[1, 2, 3], 2, 91 + nth as u8);
        let request = ThresholdSignSession {
            session_id: [0xA0 + nth as u8; 32],
            quorum: vec![1, 2, 3],
        };
        let states: Vec<&mut ThresholdMlDsaSignerShare> = shares.iter_mut().collect();
        let (results, log) = run(states, Vec::new(), |me, share, net| {
            if me == 1 {
                arm_binary_fault(PHASE_SIGN_REJECTION, nth);
            }
            threshold_sign_mldsa_party(
                share,
                &request,
                b"binary fault check",
                b"ctx",
                &[(me as u8) ^ 0x55; 32],
                &mut AllowBurn,
                net,
            )
        });
        for result in &results {
            assert_eq!(
                result,
                &Err(ThresholdMlDsaError::Mpc(
                    MpcError::MultiplicationCheckFailed
                ))
            );
        }
        assert!(
            log.iter().all(|r| r.phase != PHASE_SIGN_RELEASE),
            "neither w1 nor z may be released after a binary circuit fault"
        );
    }
}

#[test]
fn mldsa65_and_mldsa87_pq128_threshold_keygen_signing_and_negative_forgery() {
    for (level, expected_pk_len, expected_sig_len, seed) in [
        (MlDsaLevel::MlDsa65, 1952usize, 3309usize, 0x65u8),
        (MlDsaLevel::MlDsa87, 2592usize, 4627usize, 0x87u8),
    ] {
        let started_kg = Instant::now();
        let mut shares = dkg_level(level, &[10, 20, 30], 2, seed);
        let kg_ms = started_kg.elapsed().as_secs_f64() * 1e3;
        assert_fips_key(&shares);
        let pk = shares[0].verification_pack().pk_bytes.clone();
        assert_eq!(pk.len(), expected_pk_len);

        let msg = b"PQ128 threshold FIPS 204 ML-DSA credential root";
        let started_sig = Instant::now();
        let (results, log) = sign(
            &mut shares,
            &[10, 20, 30],
            seed.wrapping_add(1),
            msg,
            Vec::new(),
            None,
        );
        let sig_ms = started_sig.elapsed().as_secs_f64() * 1e3;
        let outputs: Vec<ThresholdSignOutput> = results.into_iter().map(|r| r.unwrap()).collect();
        assert!(outputs.iter().all(|o| o.signature == outputs[0].signature));
        let sig = &outputs[0].signature;
        assert_eq!(sig.len(), expected_sig_len);
        assert!(ml_dsa_verify(level, &pk, msg, b"ctx", sig));

        // Negative forgery checks: wrong message, wrong context, corrupted c_tilde / z / h.
        assert!(!ml_dsa_verify(level, &pk, b"forged msg", b"ctx", sig));
        assert!(!ml_dsa_verify(level, &pk, msg, b"wrong ctx", sig));
        for flip_at in [0usize, expected_sig_len / 2, expected_sig_len - 1] {
            let mut forged = sig.clone();
            forged[flip_at] ^= 0x01;
            assert!(!ml_dsa_verify(level, &pk, msg, b"ctx", &forged));
        }

        // Verify sealed-w1 invariant across all attempts of ML-DSA-65 / ML-DSA-87 too.
        let releases: Vec<usize> = (0..log.len())
            .filter(|&i| log[i].phase == PHASE_SIGN_RELEASE)
            .collect();
        assert_eq!(releases.len(), 1);
        println!(
            "MEASURE {:?} (2,3): keygen_ms={kg_ms:.1} attempts={} sign_ms={sig_ms:.1}",
            level, outputs[0].attempts
        );
    }
}

#[test]
fn parametric_holder_sets_preserve_order_and_bound_rss_allocation() {
    for n in 3usize..=9 {
        for t in 2..=n.div_ceil(2) {
            let st = Structure::new(n, t).unwrap();
            let old: Vec<_> = (1u32..1u32 << n)
                .filter(|m| m.count_ones() as usize == n - t + 1)
                .map(|m| (0..n).filter(|p| (m >> p) & 1 == 1).collect::<Vec<_>>())
                .collect();
            assert_eq!(st.subsets, old);
        }
    }
    let st = Structure::new(16, 2).unwrap();
    assert_eq!(st.subsets.len(), 16);
    assert!(st.subsets.iter().all(|s| s.len() == 15));
    assert_eq!(st.subsets_of(15).len(), 15);
    assert!(Structure::new(17, 2).is_err());
    assert!(Structure::new(67, 2).is_err());
    assert!(Structure::new(3, usize::MAX).is_err());
    assert!(Structure::new(3, 3).is_err()); // dishonest-majority RSS remains unsound
}

#[test]
fn parametric_two_of_six_keygen_and_nonprefix_session_sign() {
    let mut shares = dkg(&[1, 2, 3, 4, 5, 6], 2, 0x91);
    assert_fips_key(&shares);
    let pk = shares[0].verification_pack().pk_bytes.clone();
    let (results, _) = sign(
        &mut shares,
        &[2, 4, 6],
        0x92,
        b"dynamic six-custodian holder sets",
        Vec::new(),
        None,
    );
    let outputs: Vec<_> = results.into_iter().map(Result::unwrap).collect();
    assert!(outputs.iter().all(|o| o.signature == outputs[0].signature));
    assert!(ml_dsa_verify(
        MlDsaLevel::MlDsa44,
        &pk,
        b"dynamic six-custodian holder sets",
        b"ctx",
        &outputs[0].signature
    ));
}

#[cfg(feature = "std")]
fn nonce_test_dir(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(std::format!(
        "qsag-cred-nonce-{name}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&dir).unwrap();
    dir
}

/// Writes `magic || header || payload` under a fresh tag for `store`'s lock.
#[cfg(feature = "std")]
fn write_nonce_record(
    store: &FsNonceBurnStore,
    magic: &[u8; 8],
    mac: &[u8; 32],
    generation: u64,
    count: u64,
    payload: &[u8],
) {
    let mut bytes = store.encode();
    bytes.truncate(BURN_HEADER_BYTES);
    bytes[..8].copy_from_slice(magic);
    bytes[48..56].copy_from_slice(&generation.to_le_bytes());
    bytes[56..64].copy_from_slice(&count.to_le_bytes());
    bytes.extend_from_slice(payload);
    let tag = cshake256_framed_32(b"QSAG.MLDSA.NONCE_BURN.V2", &[mac, &store.lock_id, &bytes]);
    bytes.extend_from_slice(&tag);
    store.record.replace(&bytes).unwrap();
}

#[cfg(feature = "std")]
#[test]
fn nonce_ledger_keeps_every_session_in_33_bytes() {
    let dir = nonce_test_dir("compact");
    let path = dir.join("burns");
    let key_id = [0x42; 32];
    let mac_key = [0x99; 32];
    let mut store = FsNonceBurnStore::create(&path, key_id, mac_key).unwrap();
    let empty_len = std::fs::metadata(&path).unwrap().len();

    // Consecutive attempts of one session never grow the record.
    let sess = [0xAA; 32];
    assert!(store.reserve(1, 0, &sess, 0));
    let len_after_first = std::fs::metadata(&path).unwrap().len();
    assert_eq!(
        len_after_first,
        empty_len + (BURN_PARTY_HEADER_BYTES + BURN_SESSION_MIN_BYTES) as u64
    );
    for att in 1..100u32 {
        assert!(store.reserve(1, u64::from(att), &sess, att));
        assert!(!store.reserve(1, u64::from(att) + 1, &sess, att));
    }
    assert_eq!(std::fs::metadata(&path).unwrap().len(), len_after_first);

    // Each further session costs exactly 33 bytes and none is ever dropped.
    let session = |idx: u32| {
        let mut s = [0u8; 32];
        // Descending IDs: every insertion lands at the front of the sorted index.
        s[..4].copy_from_slice(&(u32::MAX - idx).to_be_bytes());
        s
    };
    for idx in 0..200u32 {
        assert!(store.reserve(1, 100 + u64::from(idx), &session(idx), 0));
    }
    assert_eq!(
        std::fs::metadata(&path).unwrap().len(),
        len_after_first + 200 * BURN_SESSION_MIN_BYTES as u64
    );
    assert!(
        store.parties[0]
            .sessions
            .is_sorted_by(|a, b| a.session_id < b.session_id)
    );
    assert_eq!(store.next_epoch(&key_id, 1).unwrap(), 300);
    assert_eq!(store.generation(), 300);
    drop(store);

    let mut reopened = FsNonceBurnStore::open_at_least(&path, key_id, mac_key, 300).unwrap();
    assert_eq!(reopened.next_epoch(&key_id, 1).unwrap(), 300);
    // Every burn of every session is refused at the old epoch and at a fresh one.
    assert!(!reopened.reserve(1, 0, &sess, 0));
    for att in 0..100u32 {
        assert!(!reopened.reserve(1, 300, &sess, att));
    }
    for idx in 0..200u32 {
        assert!(!reopened.reserve(1, 300, &session(idx), 0));
    }
    assert_eq!(reopened.generation(), 300);
    // Unburned attempts of the oldest sessions stay usable.
    assert!(reopened.reserve(1, 300, &sess, 100));
    assert!(reopened.reserve(1, 301, &session(0), 1));
    assert!(!reopened.reserve(1, 302, &session(0), 1));
    // A second party has its own epochs and sessions.
    assert!(reopened.reserve(0, 0, &sess, 0));
    assert!(!reopened.reserve(0, 1, &sess, 0));
    assert_eq!(reopened.generation(), 303);
    drop(reopened);
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "std")]
#[test]
fn nonce_attempt_boundaries_and_sparse_attempts_survive_restart() {
    let dir = nonce_test_dir("bounds");
    let path = dir.join("burns");
    let key = [0x31; 32];
    let mac = [0x32; 32];
    let session = [0x33; 32];
    let mut store = FsNonceBurnStore::create(&path, key, mac).unwrap();
    let mut epoch = 0u64;
    let mut burn = |store: &mut FsNonceBurnStore, session: &[u8; 32], attempt: u32| {
        let reserved = store.reserve(1, epoch, session, attempt);
        epoch += u64::from(reserved);
        reserved
    };
    // The full default rejection budget of one session.
    for attempt in 0..DEFAULT_MAX_REJECTION_ATTEMPTS {
        assert!(burn(&mut store, &session, attempt));
        assert!(!burn(&mut store, &session, attempt));
        if attempt == 127 {
            assert_eq!(store.parties[0].sessions[0].prefix_len(), Some(128));
        }
    }
    assert_eq!(store.parties[0].sessions[0].prefix_len(), None);
    // Arbitrary attempt numbers, until the per-session list of attempts >= 128 is full.
    assert!(burn(&mut store, &session, u32::MAX));
    for attempt in 256..383 {
        assert!(burn(&mut store, &session, attempt));
    }
    assert_eq!(
        store.parties[0].sessions[0].high_attempts.len(),
        MAX_HIGH_ATTEMPTS_PER_SESSION
    );
    let full = store.generation();
    assert!(!burn(&mut store, &session, 383));
    assert_eq!(store.generation(), full);
    // Sparse sets: a lone high attempt, a lone low attempt, and a gap.
    let lone_high = [0x34; 32];
    let lone_low = [0x35; 32];
    let gap = [0x36; 32];
    assert!(burn(&mut store, &lone_high, u32::MAX));
    assert!(burn(&mut store, &lone_low, 127));
    assert!(burn(&mut store, &gap, 0));
    assert!(burn(&mut store, &gap, 2));
    let generation = store.generation();
    assert_eq!(generation, full + 4);
    drop(store);

    let mut store = FsNonceBurnStore::open_at_least(&path, key, mac, generation).unwrap();
    for attempt in [0, 127, 128, 255, 256, 382, u32::MAX] {
        assert!(!burn(&mut store, &session, attempt));
    }
    assert!(!burn(&mut store, &lone_high, u32::MAX));
    assert!(!burn(&mut store, &lone_low, 127));
    assert!(!burn(&mut store, &gap, 0));
    assert!(!burn(&mut store, &gap, 2));
    assert!(!store.reserve(1, u64::MAX, &[0xfe; 32], 0));
    assert_eq!(store.generation(), generation);
    // Filling the gap returns the entry to its 33-byte form.
    let before = std::fs::metadata(&path).unwrap().len();
    assert!(burn(&mut store, &gap, 1));
    assert_eq!(store.parties[0].sessions[3].prefix_len(), Some(3));
    assert_eq!(std::fs::metadata(&path).unwrap().len(), before - 18);
    assert!(burn(&mut store, &lone_low, 0));
    assert!(burn(&mut store, &lone_high, 128));
    drop(store);
    assert!(FsNonceBurnStore::open_at_least(&path, key, mac, generation + 3).is_ok());
    assert!(FsNonceBurnStore::open_at_least(&path, key, mac, generation + 4).is_err());
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "std")]
#[test]
fn nonce_session_capacity_refuses_new_sessions_only() {
    let dir = nonce_test_dir("capacity");
    let mut store = FsNonceBurnStore::create(dir.join("burns"), [1; 32], [2; 32]).unwrap();
    let session = |idx: u32| {
        let mut s = [0u8; 32];
        s[..4].copy_from_slice(&idx.to_be_bytes());
        s
    };
    store.parties.push(PartyBurnState {
        party_id: 3,
        max_epoch: 9,
        sessions: (0..MAX_TRACKED_SESSIONS_PER_PARTY as u32)
            .map(|idx| SessionBurnEntry {
                session_id: session(idx),
                low_mask: 1,
                high_attempts: Vec::new(),
            })
            .collect(),
    });
    assert!(!store.available(3, 10, &session(u32::MAX), 0));
    assert!(!store.available(3, 10, &session(7), 0));
    assert!(store.available(3, 10, &session(7), 1));
    assert!(store.available(4, 0, &session(u32::MAX), 0));
    drop(store);
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "std")]
#[test]
fn nonce_v2_ledger_migrates_every_burn_and_live_snapshot_substitution_fails() {
    let dir = nonce_test_dir("legacy");
    let path = dir.join("burns");
    let key = [0x41; 32];
    let mac = [0x42; 32];
    // (party, epoch, session, attempt) rows in reservation order, covering two
    // parties, interleaved sessions, a skipped attempt and attempts >= 128.
    let rows: [(u16, u64, [u8; 32], u32); 9] = [
        (7, 10, [5; 32], 0),
        (7, 11, [5; 32], 1),
        (2, 0, [5; 32], 0),
        (7, 12, [9; 32], 128),
        (7, 13, [5; 32], 2),
        (7, 20, [1; 32], 0),
        (2, 4, [8; 32], 3),
        (7, 21, [1; 32], 2),
        (7, 22, [9; 32], u32::MAX),
    ];
    let mut payload = Vec::new();
    for (party, epoch, session, attempt) in &rows {
        payload.extend_from_slice(&party.to_le_bytes());
        payload.extend_from_slice(&epoch.to_le_bytes());
        payload.extend_from_slice(session);
        payload.extend_from_slice(&attempt.to_le_bytes());
    }
    let store = FsNonceBurnStore::create(&path, key, mac).unwrap();
    write_nonce_record(&store, b"QSCBURN2", &mac, 9, 9, &payload);
    drop(store);
    let v2_disk = std::fs::read(&path).unwrap();
    assert!(FsNonceBurnStore::open_at_least(&path, key, mac, 10).is_err());
    assert_eq!(std::fs::read(&path).unwrap(), v2_disk);

    let mut store = FsNonceBurnStore::open_at_least(&path, key, mac, 9).unwrap();
    assert_eq!(&store.record.read().unwrap()[..8], b"QSCBURN3");
    assert_eq!(store.generation(), 9);
    assert_eq!(store.next_epoch(&key, 7).unwrap(), 23);
    assert_eq!(store.next_epoch(&key, 2).unwrap(), 5);
    assert_eq!(store.next_epoch(&key, 3).unwrap(), 0);
    for (party, _, session, attempt) in &rows {
        assert!(!store.reserve(*party, 100, session, *attempt));
    }
    assert_eq!(store.generation(), 9);
    assert!(store.reserve(7, 23, &[1; 32], 1));
    assert!(store.reserve(2, 5, &[9; 32], 128));
    drop(store);
    let mut store = FsNonceBurnStore::open_at_least(&path, key, mac, 11).unwrap();
    for (party, _, session, attempt) in &rows {
        assert!(!store.reserve(*party, 100, session, *attempt));
    }
    // An authentic historical snapshot must not pass for the live record.
    std::fs::write(&path, &v2_disk).unwrap();
    assert_eq!(
        store.next_epoch(&key, 7),
        Err(ThresholdMlDsaError::NoncePersistenceFailed)
    );
    drop(store);

    // A row ledger that repeats an epoch or an attempt is refused, unmodified.
    for (epoch, attempt) in [(13, 3), (14, 2)] {
        let path = dir.join(std::format!("bad-{epoch}"));
        let store = FsNonceBurnStore::create(&path, key, mac).unwrap();
        let mut bad = payload[..5 * BURN_V2_ROW_BYTES].to_vec();
        bad.extend_from_slice(&7u16.to_le_bytes());
        bad.extend_from_slice(&u64::to_le_bytes(epoch));
        bad.extend_from_slice(&[5; 32]);
        bad.extend_from_slice(&u32::to_le_bytes(attempt));
        write_nonce_record(&store, b"QSCBURN2", &mac, 6, 6, &bad);
        drop(store);
        let disk = std::fs::read(&path).unwrap();
        assert!(FsNonceBurnStore::open(&path, key, mac).is_err());
        assert_eq!(std::fs::read(&path).unwrap(), disk);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "std")]
#[test]
fn nonce_malformed_or_noncanonical_records_fail_closed() {
    let dir = nonce_test_dir("malformed");
    let path = dir.join("burns");
    let key = [0x51; 32];
    let mac = [0x52; 32];
    let party = |sessions: u32, entries: &[&[u8]]| {
        let mut payload = Vec::new();
        payload.extend_from_slice(&1u16.to_le_bytes());
        payload.extend_from_slice(&2u64.to_le_bytes());
        payload.extend_from_slice(&sessions.to_le_bytes());
        for entry in entries {
            payload.extend_from_slice(entry);
        }
        payload
    };
    let prefix = |id: u8, tag: u8| {
        let mut entry = [id; 33];
        entry[32] = tag;
        entry
    };
    let explicit = |id: u8, low_mask: u128, high: &[u32]| {
        let mut entry = prefix(id, BURN_EXPLICIT_TAG).to_vec();
        entry.extend_from_slice(&low_mask.to_le_bytes());
        entry.extend_from_slice(&(high.len() as u16).to_le_bytes());
        for attempt in high {
            entry.extend_from_slice(&attempt.to_le_bytes());
        }
        entry
    };
    let store = FsNonceBurnStore::create(&path, key, mac).unwrap();
    let opens = |magic: &[u8; 8], generation: u64, count: u64, payload: &[u8]| {
        let copy = dir.join("copy");
        let fresh = FsNonceBurnStore::create(&copy, key, mac).unwrap();
        write_nonce_record(&fresh, magic, &mac, generation, count, payload);
        drop(fresh);
        let result = FsNonceBurnStore::open(&copy, key, mac).map(|s| s.generation());
        std::fs::remove_file(&copy).unwrap();
        std::fs::remove_file(dir.join("copy.lock")).unwrap();
        result.ok()
    };
    // Well-formed controls.
    assert_eq!(opens(b"QSCBURN3", 0, 0, &[]), Some(0));
    assert_eq!(
        opens(b"QSCBURN3", 2, 1, &party(1, &[&prefix(4, 2)])),
        Some(2)
    );
    assert_eq!(
        opens(
            b"QSCBURN3",
            131,
            1,
            &party(2, &[&prefix(4, 128), &explicit(5, 0b101, &[200])])
        ),
        Some(131)
    );
    // The generation must equal the number of burns recorded.
    assert_eq!(opens(b"QSCBURN3", 3, 1, &party(1, &[&prefix(4, 2)])), None);
    assert_eq!(opens(b"QSCBURN3", 1, 1, &party(1, &[&prefix(4, 2)])), None);
    assert_eq!(opens(b"QSCBURN3", 1, 0, &[]), None);
    // Unknown magic and unknown or empty entry tags.
    assert_eq!(opens(b"QSCBURN1", 2, 1, &party(1, &[&prefix(4, 2)])), None);
    assert_eq!(opens(b"QSCBURN3", 0, 1, &party(1, &[&prefix(4, 0)])), None);
    assert_eq!(
        opens(b"QSCBURN3", 129, 1, &party(1, &[&prefix(4, 129)])),
        None
    );
    // Explicit entries: empty, expressible as a prefix, unsorted, below 128, over-long.
    assert_eq!(
        opens(b"QSCBURN3", 0, 1, &party(1, &[&explicit(4, 0, &[])])),
        None
    );
    assert_eq!(
        opens(b"QSCBURN3", 2, 1, &party(1, &[&explicit(4, 0b11, &[])])),
        None
    );
    assert_eq!(
        opens(
            b"QSCBURN3",
            2,
            1,
            &party(1, &[&explicit(4, 0, &[300, 200])])
        ),
        None
    );
    assert_eq!(
        opens(b"QSCBURN3", 1, 1, &party(1, &[&explicit(4, 0, &[127])])),
        None
    );
    let too_many: Vec<u32> = (128..128 + MAX_HIGH_ATTEMPTS_PER_SESSION as u32 + 1).collect();
    assert_eq!(
        opens(
            b"QSCBURN3",
            too_many.len() as u64,
            1,
            &party(1, &[&explicit(4, 0, &too_many)])
        ),
        None
    );
    // Sessions out of order or repeated; trailing bytes; a party without sessions.
    assert_eq!(
        opens(
            b"QSCBURN3",
            2,
            1,
            &party(2, &[&prefix(5, 1), &prefix(4, 1)])
        ),
        None
    );
    assert_eq!(
        opens(
            b"QSCBURN3",
            2,
            1,
            &party(2, &[&prefix(4, 1), &prefix(4, 1)])
        ),
        None
    );
    assert_eq!(
        opens(b"QSCBURN3", 1, 1, &party(1, &[&prefix(4, 1), &[0]])),
        None
    );
    assert_eq!(opens(b"QSCBURN3", 0, 1, &party(0, &[])), None);
    // Parties out of order or repeated.
    let twice = [party(1, &[&prefix(4, 1)]), party(1, &[&prefix(4, 1)])].concat();
    assert_eq!(opens(b"QSCBURN3", 2, 2, &twice), None);
    // Counts far beyond the bytes present are refused before any allocation.
    assert_eq!(
        opens(
            b"QSCBURN3",
            1,
            1,
            &party(MAX_TRACKED_SESSIONS_PER_PARTY as u32, &[&prefix(4, 1)])
        ),
        None
    );
    assert_eq!(
        opens(b"QSCBURN3", 1, 1, &party(u32::MAX, &[&prefix(4, 1)])),
        None
    );
    assert_eq!(
        opens(b"QSCBURN3", 1, u64::MAX, &party(1, &[&prefix(4, 1)])),
        None
    );
    // A tag made for one format does not carry over to the other.
    let v3 = party(1, &[&prefix(4, 2)]);
    write_nonce_record(&store, b"QSCBURN3", &mac, 2, 1, &v3);
    let mut relabelled = store.record.read().unwrap();
    relabelled[..8].copy_from_slice(b"QSCBURN2");
    store.record.replace(&relabelled).unwrap();
    drop(store);
    assert!(FsNonceBurnStore::open(&path, key, mac).is_err());
    std::fs::remove_dir_all(dir).unwrap();
}

#[cfg(all(feature = "std", unix))]
#[test]
fn nonce_ledger_and_lock_must_remain_private() {
    use std::os::unix::fs::PermissionsExt;
    let dir =
        std::env::temp_dir().join(std::format!("qsag-cred-nonce-perms-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("burns");
    let key = [0x61; 32];
    let mac = [0x62; 32];
    let store = FsNonceBurnStore::create(&path, key, mac).unwrap();
    drop(store);
    for file in [&path, &dir.join("burns.lock")] {
        assert_eq!(
            std::fs::metadata(file).unwrap().permissions().mode() & 0o777,
            0o600
        );
        std::fs::set_permissions(file, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(FsNonceBurnStore::open(&path, key, mac).is_err());
        std::fs::set_permissions(file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let mut store = FsNonceBurnStore::open(&path, key, mac).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
    assert!(!store.reserve(1, 0, &[1; 32], 0));
    assert!(store.next_epoch(&key, 1).is_err());
    drop(store);
    std::fs::remove_dir_all(dir).unwrap();
}
