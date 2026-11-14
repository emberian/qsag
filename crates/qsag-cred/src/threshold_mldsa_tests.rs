//! Tests for the sharing engine and the threshold ML-DSA protocol. Every
//! party runs in its own thread against an in-memory synchronous network; a
//! corrupt party is modelled by rewriting its outgoing messages.

use super::*;
use crate::fips204_ntt::{ml_dsa_sign_deterministic, signing_key_from_secret_for_test};
use crate::rss_mpc::test_support::{arm_additive_fault, deal};
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
    for (parties, threshold) in [(3, 2), (5, 2), (5, 3)] {
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
            rejection_verdict(
                &mut engine,
                (&deal(&st, me, &z, 100), z_bound),
                (&deal(&st, me, &low, 200), low_bound),
                &mask_values,
                &planes,
            )
        });
        for result in results {
            assert_eq!(result.unwrap(), *expected, "case {index}");
        }
    }
}

// ---------------------------------------------------------------------------
// Protocol
// ---------------------------------------------------------------------------

fn dkg(ids: &[u16], threshold: usize, session: u8) -> Vec<ThresholdMlDsaSignerShare> {
    let config = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
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
    let params = MlDsaLevel::MlDsa44.params();
    let mut seen: Vec<(u32, Vec<Poly256>, Vec<Poly256>)> = Vec::new();
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
    assert!(shares.iter().all(|s| s.verification_pack() == &pack));
    assert_eq!(pack.pk_bytes.len(), 1312);
    let (s1, s2) = reconstruct(shares);
    let mut histogram = [0usize; 5];
    for poly in s1.iter().chain(&s2) {
        for &c in &poly.coeffs {
            let centred = if c > MLDSA_Q / 2 {
                c as i64 - MLDSA_Q as i64
            } else {
                c as i64
            };
            assert!(
                (-2..=2).contains(&centred),
                "coefficient {centred} outside [-eta, eta]"
            );
            histogram[(centred + 2) as usize] += 1;
        }
    }
    // 2048 uniform draws over five values: each count is 409.6 +- 18.1.
    assert!(
        histogram.iter().all(|&count| (300..=520).contains(&count)),
        "{histogram:?}"
    );
    // The public key is the standard key of this secret, and the standard
    // signer with this secret verifies under it.
