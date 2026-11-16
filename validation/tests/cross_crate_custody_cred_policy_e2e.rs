// SPDX-License-Identifier: Apache-2.0 OR MIT
//! End-to-End Cross-Crate Custody, BlindVC -> `zk-Hem`, Policy/Capability -> Threshold `ML-DSA`,
//! and Paged Crash-Journal (`QSBURN05` & `QSHDQB04`) Validation Suite.
//!
//! Proves zero architectural seams across crates (`Subcarbon C4` & `Subcarbon C5` remediation):
//! 1. **Journey A (`qsag-cred` -> `qsag-agg` `239 KiB` `zk-Hem` BlindVC Selective Disclosure):**
//!    - 3-of-5 dishonest-majority SPDZ TOPRF DKG & online blinded evaluation (`voprf_spdz`)
//!    - 438-repetition Quantum-128 ZKBoo blind issuance (`holder_prepare_blind_issuance`,
//!      `threshold_issue_blind_vc`) into `IssuerCredentialAccumulator` + ML-DSA-44 root attestation
//!    - Zero-copy witness extraction via `HolderCredentialSecret::{arity, attrs, holder_blind}`
//!      into `qsag_agg::zk_hem::blind_vc::{BlindVcWitness, BlindVcStatement::derive, prove_presentation}`
//!    - Exact cross-crate Poseidon2 rate-6 accumulator root equality, `~239 KiB` succinct proof wire
//!      roundtrip, verification, and adversarial tamper rejection.
//! 2. **Journey B (`qsag-addr` + `qsag-policy` + `SpongeMacaroon` + `Compact1122` `PqBiscuit` ->
//!    `qsag-cred::threshold_sign_mldsa_party_policy_gated` + upstream `fips204`):**
//!    - Canonical `policy_signing_key_id` handshake parity (`C4-F3`, `C4-F6`) across `qsag-addr`,
//!      `qsag-policy`, and `qsag-cred::ThresholdVerificationPack`
//!    - Dealerless `PolicyGuardDkgRound1..2` + `finalize_distributed_policy_guard` provisioning
//!    - Flow B1: `SpongeMacaroon` + bound 3rd-party `Discharge` -> `PolicyEngine::authorize_committed_barrier`
//!      -> `AuthorizedSignReleaseToken::into_quorum_party_tokens` -> `threshold_sign_mldsa_party_policy_gated`
//!      (with durable `FsNonceBurnStore` `QSCBURN3`) verified under `fips204::ml_dsa_44`
//!    - Flow B2: Multi-hop offline `Compact1122` `PqBiscuit` (`PQ_BISCUIT_HOP_CRYPTO_BYTES = 1,154 B`)
//!      with move-only `PqBiscuitStepKey::attenuate` + PoP request-bound `seal` -> `PolicyEngine` ->
//!      `threshold_sign_mldsa_party_policy_gated`, plus pre-slot capability refusal and digest mismatch checks.
//! 3. **Journey C (`TwoSlotHwmCrashModel` Paged Crash Journals: `QSBURN05` in `qsag-fts::wal` &
//!    `QSHDQB04` in `qsag-hd::budget`):**
//!    - Verifies 3-page `12,288 B` physical layout (`4096` Slot A, `8192` Slot B, `12288` records)
//!      and NIST SP 800-185 `cshake256_framed_32_nist_ref` HWM/record MAC parity
//!    - Simulates sector tears on Slot A (`4096`), sector tears on Slot B (`8192`), simultaneous
//!      dual-slot tears, uncommitted tail bytes (`<= RECORD_LEN`) under steady (`(c, c)`), lagging
//!      Slot B (`(c, c - 1)`), and unacknowledged synced record (`committed = c + 1` while HWM holds `c`),
//!      oversized tails (`RECORD_LEN + 1`), committed-record bit-flips, overclaimed HWM / silent
//!      record truncation, and inode-copy attacks!

use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::{Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Condvar, Mutex, mpsc};

use fips204::ml_dsa_44;
use fips204::traits::{SerDes as Fips204SerDes, Verifier as Fips204Verifier};
use qsag_accel::CpuReferenceBackend;
use qsag_addr::{KeyIdentityKind, QsagAddress, WitnessSuiteTag, policy_signing_key_id};
use qsag_agg::field::Goldilocks as AggGoldilocks;
use qsag_agg::pcs::WhirSecurityRegime;
use qsag_agg::zk_hem::blind_vc::{
    BlindVcStatement, BlindVcWitness, prove_presentation, verify_presentation,
};
use qsag_agg::zk_hem::protocol::{ZkHemError, ZkHemProof};
use qsag_asm::durable::{
    CounterOrder, HWM_PAGE_BYTES, HWM_SLOT_BYTES, RECORD_HEADER_BYTES, TwoSlotHwm, file_dev_ino,
    file_identity as asm_file_identity,
};
use qsag_cred::blind_vc::{
    IssuerCredentialAccumulator, holder_prepare_blind_issuance, issuance_input,
    threshold_issue_blind_vc,
};
use qsag_cred::voprf::{CounterStore, Error as ToprfError, IssuanceReceiptKey};
use qsag_cred::voprf_spdz::{SpdzConfig, SpdzServer, SpdzSession, spdz_blind, spdz_dkg};
use qsag_cred::{
    FsNonceBurnStore, MlDsaLevel, MpcTransport, MpcTransportError, NonceBurnPersistence,
    RoundInbox, RoundInfo, RoundKind, ThresholdMlDsaDkgConfig, ThresholdMlDsaError,
    ThresholdPolicyGate, ml_dsa_keygen_from_seed, ml_dsa_verify, threshold_mldsa_dkg_party,
    threshold_sign_mldsa_party_policy_gated,
};
use qsag_external_validation::spec_ref::cshake256_framed_32_nist_ref;
use qsag_fts::wal::DurableBurnJournal;
use qsag_fts::{FrontierDpTable, FrontierFtsProfile};
use qsag_hd::HdError;
use qsag_hd::budget::DurableQueryBudget;
use qsag_policy::{
    AuthorizedSignReleaseToken, CapabilityError, CapabilityGate, CapabilityRequest, Caveat,
    Discharge, MacaroonVerifier, PQ_BISCUIT_HOP_CRYPTO_BYTES, PolicyAuthenticatedOt, PolicyEngine,
    PolicyGuardDkgRound1, PolicySignerGuardShare, PolicyViolation, PqBiscuit,
    PqBiscuitAuthorityKey, QuorumTierRule, SigningPayloadBinding, SpongeMacaroon,
    TransactionIntent, TransactionPolicy, finalize_distributed_policy_guard,
};

// ============================================================================
// Shared TempDir Guard & In-Memory Synchronous Transports
// ============================================================================

struct TempDirGuard(PathBuf);

impl TempDirGuard {
    fn new(prefix: &str) -> Self {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        // `create_dir` claims the path atomically; a leftover from a reused PID is skipped.
        let dir = loop {
            let seq = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let candidate =
                std::env::temp_dir().join(format!("qsag-e7-{prefix}-{}-{seq}", std::process::id()));
            match fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create temp dir: {e}"),
            }
        };
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).expect("chmod 0700 dir");
        }
        Self(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct InMemToprfCounter(Option<u64>);

impl CounterStore for InMemToprfCounter {
    fn high_water(&self) -> Result<Option<u64>, ToprfError> {
        Ok(self.0)
    }
    fn reserve(
        &mut self,
        _key: &[u8; 32],
        _party: usize,
        counter: u64,
        items: usize,
    ) -> Result<(), ToprfError> {
        if items == 0 || self.0.is_some_and(|prev| counter <= prev) {
            return Err(ToprfError::Counter);
        }
        self.0 = Some(counter.saturating_add((items - 1) as u64));
        Ok(())
    }
}

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
}

struct LocalMpcNet {
    state: Mutex<NetState>,
    changed: Condvar,
}

struct MpcEndpoint {
    net: Arc<LocalMpcNet>,
    me: usize,
}

impl MpcTransport for MpcEndpoint {
    fn exchange(
        &mut self,
        info: RoundInfo,
        private: Vec<Vec<u8>>,
        broadcast: Vec<u8>,
    ) -> Result<RoundInbox, MpcTransportError> {
        let mut state = self.net.state.lock().unwrap();
        if state.stopped {
            return Err(MpcTransportError);
        }
        let my_round = state.round;
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
            inbox.private[sender] = posted.private[self.me].clone();
            inbox.broadcast[sender] = posted.broadcast.clone();
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

impl Drop for MpcEndpoint {
    fn drop(&mut self) {
        let mut state = self.net.state.lock().unwrap();
        state.stopped = true;
        self.net.changed.notify_all();
    }
}

fn run_mpc_parties<S: Send, R: Send>(
    states: Vec<S>,
    f: impl Fn(usize, S, &mut MpcEndpoint) -> R + Sync,
) -> Vec<R> {
    let parties = states.len();
    let net = Arc::new(LocalMpcNet {
        state: Mutex::new(NetState {
            round: 0,
            posted: (0..parties).map(|_| None).collect(),
            taken: vec![false; parties],
            stopped: false,
        }),
        changed: Condvar::new(),
    });
    std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .enumerate()
            .map(|(me, s)| {
                let net = Arc::clone(&net);
                let f_ref = &f;
                scope.spawn(move || {
                    let mut ep = MpcEndpoint { net, me };
                    f_ref(me, s, &mut ep)
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

/// Ideal authenticated 1-of-2 OT channel over private point-to-point `mpsc` pipes for
/// dealerless `PolicyGuardDkg` (`finalize_distributed_policy_guard`).
type PolicyOtFrame = ([u8; 32], Vec<[u128; 2]>);

struct IdealPolicyOtChannel {
    party: u16,
    tx: BTreeMap<u16, mpsc::Sender<PolicyOtFrame>>,
    rx: BTreeMap<u16, mpsc::Receiver<PolicyOtFrame>>,
}

impl PolicyAuthenticatedOt for IdealPolicyOtChannel {
    fn exchange(
        &mut self,
        local_party: u16,
        peer: u16,
        domain: [u8; 32],
        alternatives: &[[u128; 2]],
        choices: &[bool],
    ) -> Result<Vec<u128>, PolicyViolation> {
        if local_party != self.party || alternatives.len() != choices.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        self.tx
            .get(&peer)
            .ok_or(PolicyViolation::IntentBindingMismatch)?
            .send((domain, alternatives.to_vec()))
            .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
        let (peer_dom, peer_alts) = self
            .rx
            .get(&peer)
            .ok_or(PolicyViolation::IntentBindingMismatch)?
            .recv()
            .map_err(|_| PolicyViolation::BarrierBdozMacFailed)?;
        if peer_dom != domain || peer_alts.len() != choices.len() {
            return Err(PolicyViolation::IntentBindingMismatch);
        }
        Ok(peer_alts
            .iter()
            .zip(choices)
            .map(|(pair, &bit)| pair[usize::from(bit)])
            .collect())
    }
}

fn provision_dealerless_policy_guards(
    party_ids: &[u16],
    setup_id: [u8; 32],
    slots: usize,
) -> Vec<PolicySignerGuardShare> {
    let mut r1_states = Vec::new();
    let mut inboxes_commits: BTreeMap<u16, Vec<_>> =
        party_ids.iter().map(|&id| (id, Vec::new())).collect();
    for (idx, &pid) in party_ids.iter().enumerate() {
        let (st, commits) = PolicyGuardDkgRound1::new_with_capacity(
            pid,
            party_ids,
            setup_id,
            [0x21 + idx as u8; 32],
            slots,
        )
        .expect("PolicyGuardDkgRound1");
        for c in commits {
            inboxes_commits.get_mut(&c.recipient).unwrap().push(c);
        }
        r1_states.push((pid, st));
    }

    let mut r2_states = Vec::new();
    let mut inboxes_opens: BTreeMap<u16, Vec<_>> =
        party_ids.iter().map(|&id| (id, Vec::new())).collect();
    for (pid, st) in r1_states {
        let (r2, opens) = st
            .round2_open_seeds(&inboxes_commits[&pid])
            .expect("round2_open_seeds");
        for o in opens {
            inboxes_opens.get_mut(&o.recipient).unwrap().push(o);
        }
        r2_states.push((pid, r2));
    }

    let mut tx_map: BTreeMap<u16, BTreeMap<u16, _>> =
        party_ids.iter().map(|&id| (id, BTreeMap::new())).collect();
    let mut rx_map: BTreeMap<u16, BTreeMap<u16, _>> =
        party_ids.iter().map(|&id| (id, BTreeMap::new())).collect();
    for &a in party_ids {
        for &b in party_ids {
            if a != b {
                let (tx, rx) = mpsc::channel();
                tx_map.get_mut(&a).unwrap().insert(b, tx);
                rx_map.get_mut(&b).unwrap().insert(a, rx);
            }
        }
    }

    std::thread::scope(|scope| {
        let handles: Vec<_> = r2_states
            .into_iter()
            .map(|(pid, r2)| {
                let opens = inboxes_opens.remove(&pid).unwrap();
                let mut ot = IdealPolicyOtChannel {
                    party: pid,
                    tx: tx_map.remove(&pid).unwrap(),
                    rx: rx_map.remove(&pid).unwrap(),
                };
                scope.spawn(move || {
                    finalize_distributed_policy_guard(r2, &opens, &mut ot)
                        .expect("finalize_distributed_policy_guard")
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

/// Splits a quorum release into per-party tokens (quorum order) and checks the policy
/// API's party binding: each token authorizes its owner and no other presenter.
fn split_and_check_party_bindings(
    release: AuthorizedSignReleaseToken,
    key_id: &[u8; 32],
    msg: &[u8],
    ctx: &[u8],
    quorum: &[u16],
) -> Vec<AuthorizedSignReleaseToken> {
    assert_eq!(release.party_id(), None);
    assert_eq!(release.quorum_ids(), quorum);
    for &party in quorum {
        assert!(
            !release.matches_signing_party(party, key_id, msg, ctx, quorum),
            "unsplit release must not authorize a single party"
        );
    }
    let tokens = release.into_quorum_party_tokens();
    assert_eq!(tokens.len(), quorum.len());
    tokens
        .into_iter()
        .zip(quorum)
        .map(|(token, &owner)| {
            assert_eq!(token.party_id(), Some(owner));
            for &presenting_party in quorum {
                assert_eq!(
                    token.matches_signing_party(presenting_party, key_id, msg, ctx, quorum),
                    presenting_party == owner,
                    "party {presenting_party} must not spend party {owner}'s token"
                );
            }
            assert!(!quorum.contains(&0));
            assert!(!token.matches_signing_party(0, key_id, msg, ctx, quorum));
            // A child token cannot be expanded back into the entire quorum's authority.
            let mut again = token.into_quorum_party_tokens();
            assert_eq!(again.len(), 1);
            let child = again.remove(0);
            assert_eq!(child.party_id(), Some(owner));
            assert!(child.matches_signing_party(owner, key_id, msg, ctx, quorum));
            child
        })
        .collect()
}

// ============================================================================
// Journey A: BlindVC Issuance (`qsag-cred`) -> `239 KiB` `zk-Hem` Presentation (`qsag-agg`)
// ============================================================================

#[test]
fn e2e_blind_vc_spdz_toprf_issuance_to_239kib_zk_hem_selective_disclosure() {
    // 1. 3-of-5 Dishonest-Majority SPDZ TOPRF DKG (`qsag_cred::voprf_spdz`).
    let spdz_cfg = SpdzConfig::new(3, 5).expect("SpdzConfig(3, 5)");
    let dkg_entropy: Vec<[u8; 32]> = (0..5u8).map(|i| [0x11 + i; 32]).collect();
    let mut servers: Vec<SpdzServer> =
        spdz_dkg(spdz_cfg, [0xA0; 32], &dkg_entropy).expect("spdz_dkg");
    let toprf_pub = servers[0].public().clone();
    let oprf_pk = toprf_pub.public_key();
    let issuer_pk_digest = oprf_pk.commitment();
    let issuer_epoch = 19u64;
    let schema_id = 0x5153_4147_0001_0042u64;

    // 2. Holder prepares a 438-repetition Quantum-128 ZKBoo BlindIssuanceRequest (`qsag_cred::blind_vc`).
    let attested_attrs: [u64; 8] = [1994, 840, 3, 2030, 77_777, 1, 999_001, 42];
    let issuance_sid = [0xB2; 32];
    let (req, holder_secret) = holder_prepare_blind_issuance(
        schema_id,
        &attested_attrs,
        issuer_pk_digest,
        issuer_epoch,
        [0xC3; 32],
        issuance_sid,
    )
    .expect("holder_prepare_blind_issuance");
    assert_eq!(req.opened_reps.len(), 438);
    assert_eq!(holder_secret.arity(), attested_attrs.len());
    assert_eq!(holder_secret.attrs(), &attested_attrs);

    // 3. Quorum `{0, 2, 4}` evaluates the blinded issuance token via SPDZ TOPRF, and the issuer
    //    enrolls a second dummy credential first so our holder sits at non-zero leaf index `1`!
    let mut accumulator = IssuerCredentialAccumulator::new(oprf_pk.clone(), issuer_epoch);
    let receipt_key = IssuanceReceiptKey::new([0xD4; 32]);
    let mut stores = [
        InMemToprfCounter(None),
        InMemToprfCounter(None),
        InMemToprfCounter(None),
    ];

    // Enroll a sibling credential at leaf 0 first so the Merkle path has non-trivial sibling leaves.
    {
        let other_attrs = [2001u64, 826, 2, 2031, 12_345, 0, 500, 9];
        let (other_req, _) = holder_prepare_blind_issuance(
            schema_id,
            &other_attrs,
            issuer_pk_digest,
            issuer_epoch,
            [0xC0; 32],
            [0xB0; 32],
        )
        .unwrap();
        let input0 = issuance_input(&other_req);
        let inputs_slice: [&[u8]; 1] = [&input0];
        let (s0, rest) = servers.split_at_mut(1);
        let (_, rest) = rest.split_at_mut(1);
        let (s2, rest) = rest.split_at_mut(1);
        let (_, s4) = rest.split_at_mut(1);
        let mut quorum = [&mut s0[0], &mut s2[0], &mut s4[0]];
        let mut store_refs: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|s| s as &mut dyn CounterStore)
            .collect();
        let sess_ent = [[0x31; 32], [0x32; 32], [0x33; 32]];
        let (spdz_sess, grants) =
            SpdzSession::begin(&mut quorum, &mut store_refs, [0xE0; 32], 0, 1, &sess_ent)
                .expect("SpdzSession::begin 0");
        let (client, spdz_req) =
            spdz_blind(&toprf_pub, &inputs_slice, [0xE0; 32], 0, &grants).unwrap();
        let outs = spdz_sess.evaluate(&spdz_req).unwrap();
        let eval0 = client.finalize_for_issuance(&outs, &receipt_key).unwrap();
        let cred0 = threshold_issue_blind_vc(
            &mut accumulator,
            &other_req,
            &other_attrs,
            &eval0,
            &receipt_key,
            schema_id,
        )
        .unwrap();
        assert_eq!(cred0.accumulator_leaf_index, 0);
    }

    // Issue our target credential at leaf index `1`.
    let cred = {
        let input1 = issuance_input(&req);
        let inputs_slice: [&[u8]; 1] = [&input1];
        let (s0, rest) = servers.split_at_mut(1);
        let (_, rest) = rest.split_at_mut(1);
        let (s2, rest) = rest.split_at_mut(1);
        let (_, s4) = rest.split_at_mut(1);
        let mut quorum = [&mut s0[0], &mut s2[0], &mut s4[0]];
        let mut store_refs: Vec<&mut dyn CounterStore> = stores
            .iter_mut()
            .map(|s| s as &mut dyn CounterStore)
            .collect();
        let sess_ent = [[0x41; 32], [0x42; 32], [0x43; 32]];
        let (spdz_sess, grants) =
            SpdzSession::begin(&mut quorum, &mut store_refs, [0xE1; 32], 1, 1, &sess_ent)
                .expect("SpdzSession::begin 1");
        let (client, spdz_req) =
            spdz_blind(&toprf_pub, &inputs_slice, [0xE1; 32], 1, &grants).unwrap();
        let outs = spdz_sess.evaluate(&spdz_req).unwrap();
        let eval1 = client.finalize_for_issuance(&outs, &receipt_key).unwrap();
        threshold_issue_blind_vc(
            &mut accumulator,
            &req,
            &attested_attrs,
            &eval1,
            &receipt_key,
            schema_id,
        )
        .expect("threshold_issue_blind_vc")
    };
    assert_eq!(cred.accumulator_leaf_index, 1);

    // Issuer signs an FIPS 204 ML-DSA-44 root attestation over `(issuer_pk_digest, epoch, root)`.
    let (issuer_mldsa_pk, issuer_mldsa_sk) =
        ml_dsa_keygen_from_seed(MlDsaLevel::MlDsa44, &[0x55; 32]);
    let root_attestation = accumulator
        .attest_root_deterministic(
            MlDsaLevel::MlDsa44,
            &issuer_mldsa_sk,
            issuer_mldsa_pk.clone(),
        )
        .expect("attest_root_deterministic");
    assert!(root_attestation.verify(&issuer_mldsa_pk, &oprf_pk));

    // 4. Bridge `HolderCredentialSecret` + `CredentialMembershipWitness` directly into
    //    `qsag_agg::zk_hem::blind_vc::{BlindVcWitness, BlindVcStatement::derive}` (`C4-F7` fix)!
    let membership = accumulator
        .membership_witness(cred.accumulator_leaf_index)
        .expect("membership_witness");
    assert_eq!(membership.accumulator_root, accumulator.root());

    let zk_witness = BlindVcWitness {
        attrs: holder_secret
            .attrs()
            .iter()
            .copied()
            .map(AggGoldilocks::from_u64_reduced)
            .collect(),
        holder_blind: holder_secret
            .holder_blind()
            .map(AggGoldilocks::from_u64_reduced),
        presentation_blind: [0x9001u64, 0x9002, 0x9003, 0x9004]
            .map(AggGoldilocks::from_u64_reduced),
        path_bits: core::array::from_fn(|lvl| ((membership.leaf_index >> lvl) & 1) == 1),
        siblings: core::array::from_fn(|lvl| {
            membership.siblings[lvl].map(AggGoldilocks::from_u64_reduced)
        }),
    };

    let scope_limbs = [101u64, 202, 303, 404].map(AggGoldilocks::from_u64_reduced);
    let disclosed_indices = [1usize, 3, 7]; // selectively disclose country=840, exp=2030, tier=42; hide 5 attrs!
    let zk_statement = BlindVcStatement::derive(
        &zk_witness,
        cred.issuer_epoch,
        cred.schema_id,
        scope_limbs,
        &disclosed_indices,
    );

    // Cross-crate Poseidon2 rate-6 parity check: `qsag-agg` derived root MUST equal `qsag-cred`
    // accumulator root limb-for-limb!
    let agg_root_u64: [u64; 6] = zk_statement.accumulator_root.map(|x| x.to_canonical_u64());
    assert_eq!(
        agg_root_u64,
        *root_attestation.accumulator_root(),
        "qsag-agg BlindVcStatement::derive root != qsag-cred IssuerCredentialAccumulator root"
    );
    assert_eq!(
        zk_statement.disclosed,
        vec![
            (1, AggGoldilocks::from_u64_reduced(840)),
            (3, AggGoldilocks::from_u64_reduced(2030)),
            (7, AggGoldilocks::from_u64_reduced(42)),
        ]
    );

    // 5. Prove & verify succinct `~239 KiB` `zk-Hem` presentation!
    let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
    let verifier_ctx = b"qsag-e2e-verifier-challenge-nonce-v1";
    let zk_proof = prove_presentation(
        &zk_statement,
        &zk_witness,
        verifier_ctx,
        regime,
        &[0x7A; 32],
    )
    .expect("prove_presentation");

    let proof_bytes = zk_proof.to_bytes();
    assert!(
        (200_000..=265_000).contains(&proof_bytes.len()),
        "expected ~239 KiB succinct BlindVC zk-Hem proof, got {} B",
        proof_bytes.len()
    );
    let shape = zk_statement
        .shape()
        .expect("well-formed BlindVcStatement shape");
    let decoded =
        ZkHemProof::from_bytes(&proof_bytes, &shape, regime).expect("ZkHemProof::from_bytes");
    assert_eq!(decoded, zk_proof);
    assert!(verify_presentation(
        &zk_statement,
        verifier_ctx,
        regime,
        &decoded
    ));

    // Adversarial rejection checks: wrong verifier context, altered disclosed attribute,
    // altered accumulator root, altered scope tag, and un-enrolled holder blind.
    assert!(!verify_presentation(
        &zk_statement,
        b"replayed-context",
        regime,
        &decoded
    ));
    let mut forged_attr = zk_statement.clone();
    forged_attr.disclosed[0].1 += AggGoldilocks::ONE;
    assert!(!verify_presentation(
        &forged_attr,
        verifier_ctx,
        regime,
        &decoded
    ));
    let mut forged_root = zk_statement.clone();
    forged_root.accumulator_root[0] += AggGoldilocks::ONE;
    assert!(!verify_presentation(
        &forged_root,
        verifier_ctx,
        regime,
        &decoded
    ));
    let mut forged_scope = zk_statement.clone();
    forged_scope.scope[0] += AggGoldilocks::ONE;
    assert!(!verify_presentation(
        &forged_scope,
        verifier_ctx,
        regime,
        &decoded
    ));
    let mut forged_witness = zk_witness;
    forged_witness.holder_blind[0] += AggGoldilocks::ONE;
    assert_eq!(
        prove_presentation(
            &zk_statement,
            &forged_witness,
            verifier_ctx,
            regime,
            &[0x7B; 32]
        ),
        Err(ZkHemError::Unsatisfied)
    );
}

// ============================================================================
// Journey B: `qsag-policy` + `SpongeMacaroon` / `PqBiscuit` -> `threshold_sign_mldsa_party_policy_gated`
// ============================================================================

#[test]
fn e2e_policy_macaroon_and_compact1122_biscuit_to_threshold_mldsa_signing() {
    let accel = CpuReferenceBackend::new();
    let tmp = TempDirGuard::new("policy-mldsa");

    // 1. Verify newly unified `WitnessSuiteTag` discriminants (`C4-F6`) and run 2-of-3 dealerless
    //    Threshold ML-DSA-44 DKG (`qsag-cred`).
    assert_eq!(WitnessSuiteTag::Baggy as u16, 0x0211);
    assert_eq!(WitnessSuiteTag::Jorts as u16, 0x0212);
    assert_eq!(WitnessSuiteTag::QuorumJorts as u16, 0x0213);
    assert_eq!(WitnessSuiteTag::JortsPoseidon2 as u16, 0x0214);
    assert_eq!(WitnessSuiteTag::CorduroyPoseidon2 as u16, 0x0215);

    // RSS Threshold ML-DSA (`threshold = 2`) requires `2t - 1 = 3` signing custodians; combined
    // with `forbid_initiator_self_approval = true`, a 4-custodian desk `[10, 20, 30, 40]` allows
    // custodian `10` to initiate while `[20, 30, 40]` form the 3-of-4 BDOZ & RSS signing quorum!
    let party_ids = [10u16, 20, 30, 40];
    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: party_ids.to_vec(),
        session_id: [0x31; 32],
    };
    let mut mldsa_shares = run_mpc_parties(vec![0u8, 1, 2, 3], |_, idx, net| {
        threshold_mldsa_dkg_party(&dkg_cfg, party_ids[idx as usize], &[0x40 + idx; 32], net)
            .expect("threshold_mldsa_dkg_party")
    });

    let pack = mldsa_shares[0].verification_pack().clone();
    let canonical_key_id = policy_signing_key_id(WitnessSuiteTag::MlDsa44, &pack.pk_bytes);
    assert_eq!(
        pack.policy_signing_key_id(),
        canonical_key_id,
        "C4-F3 regression: ThresholdVerificationPack::policy_signing_key_id != qsag_addr::policy_signing_key_id"
    );
    assert_eq!(
        qsag_policy::policy_signing_key_id(WitnessSuiteTag::MlDsa44, &pack.pk_bytes),
        canonical_key_id
    );
    let upstream_pk =
        ml_dsa_44::PublicKey::try_from_bytes(pack.pk_bytes.as_slice().try_into().unwrap())
            .expect("upstream fips204::ml_dsa_44::PublicKey");

    // 2. Build allowlisted `QsagAddress`, `TransactionPolicy`, and dealerless `PolicySignerGuardShare`s.
    let recipient = QsagAddress::from_pubkey_poseidon2(
        "qsag",
        WitnessSuiteTag::MlDsa44,
        KeyIdentityKind::SingleOrThreshold,
        b"recipient-vault-ml-dsa-44-pubkey",
    )
    .expect("recipient QsagAddress");
    let bech = recipient.encode().expect("Bech32m encode");
    assert_eq!(
        QsagAddress::decode_for_hrp(&bech, "qsag").expect("Bech32m decode"),
        recipient
    );

    let policy = TransactionPolicy {
        chain_id: 2026,
        pinned_suite: WitnessSuiteTag::MlDsa44,
        recipient_allowlist: vec![recipient.commitment_256],
        max_single_tx_amount: 10_000,
        velocity_window_cap: 15_000,
        valid_not_before_secs: 1_000,
        valid_not_after_secs: 9_000,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(30),
        quorum_tiers: vec![
            QuorumTierRule {
                max_amount_units: 1_000,
                min_approvers: 1,
                require_hardware_guardian: false,
            },
            QuorumTierRule {
                max_amount_units: 10_000,
                min_approvers: 2,
                require_hardware_guardian: true,
            },
        ],
    };
    let required_actions = 0b0011u64;
    let engine = PolicyEngine::new(&policy, required_actions);
    let authority_pk = [0xAA; 32];
    let signing_ctx = b"qsag-policy-gated-mldsa-v1";
    // Custodian `10` initiates (`forbid_initiator_self_approval = true`), so custodians `[20, 30, 40]`
    // (including hardware guardian `30`) form the `2t - 1 = 3` BDOZ approval & RSS signing quorum!
    let quorum = [20u16, 30, 40];

    let mut guards = provision_dealerless_policy_guards(&party_ids, [0x51; 32], 6);

    // Durable `FsNonceBurnStore` (`QSCBURN3`) per custodian.
    let mut burn_stores: Vec<FsNonceBurnStore> = party_ids
        .iter()
        .map(|&pid| {
            FsNonceBurnStore::create(
                tmp.path().join(format!("mldsa-burn-{pid}")),
                canonical_key_id,
                [0x60 + (pid as u8); 32],
            )
            .expect("FsNonceBurnStore::create")
        })
        .collect();

    // ------------------------------------------------------------------------
    // Flow B1: `SpongeMacaroon` + 3rd-party `Discharge` -> `PolicyEngine` -> `ThresholdMlDsa`
    // ------------------------------------------------------------------------
    let session_b1 = [0x71; 32];
    let (mut intent_b1, _) =
        TransactionIntent::builder(2026, WitnessSuiteTag::MlDsa44, recipient.clone(), 4_500)
            .window_id(0)
            .timestamp_secs(2_500)
            .initiator_and_approvers(10, &[20, 30, 40])
            .bind_signing_payload(
                &SigningPayloadBinding {
                    key_id: canonical_key_id,
                    payload: b"wire-transfer-001: 4500 units",
                    ctx: signing_ctx,
                    session_id: session_b1,
                    policy_revision: 1,
                    quorum: &quorum,
                    authority_pk,
                },
                &policy,
            )
            .expect("bind_signing_payload B1");
    let signing_bytes_b1 = guards[0]
        .authenticate_initiated_intent(&policy, &mut intent_b1)
        .expect("authenticate_initiated_intent B1");
    let intent_digest_b1 = intent_b1.canonical_digest();

    let mac_root_key = [0x81; 32];
    let mac_id = [0x82; 32];
    let third_party_key = [0x83; 32];
    let third_party_caveat_id = [0x84; 32];
    let audience = policy.canonical_digest();
    let mac_verifier = MacaroonVerifier::new(&mac_root_key, mac_id, audience);

    let mut macaroon = SpongeMacaroon::issue(&mac_root_key, mac_id, audience);
    macaroon.attenuate(Caveat::NotBefore(2_000)).unwrap();
    macaroon.attenuate(Caveat::ExpiresAt(5_000)).unwrap();
    macaroon
        .attenuate(Caveat::Resource(recipient.commitment_256))
        .unwrap();
    macaroon.attenuate(Caveat::Actions(0b0111)).unwrap();
    macaroon.attenuate(Caveat::MaxAmount(5_000)).unwrap();
    macaroon
        .attenuate(Caveat::ThirdParty(third_party_caveat_id))
        .unwrap();

    // Missing or unbound 3rd-party discharge MUST be rejected by `PolicyEngine` BEFORE BDOZ slot burn!
    let unbound_discharge =
        SpongeMacaroon::issue_discharge(&third_party_key, third_party_caveat_id, audience);
    let bad_gate = CapabilityGate::Macaroon {
        verifier: &mac_verifier,
        token: &macaroon,
        discharges: &[Discharge {
            token: &unbound_discharge,
            root_key: &third_party_key,
        }],
    };
    assert_eq!(
        engine
            .authorize_committed_barrier(
                &intent_b1,
                session_b1,
                2_500,
                Some(&bad_gate),
                &mut guards[1..4],
                &accel,
            )
            .err(),
        Some(PolicyViolation::CapabilityDenied(
            CapabilityError::UnboundDischarge
        ))
    );
    assert!(
        guards
            .iter()
            .all(|g| !g.is_poisoned() && g.accumulated_window_spend() == 0)
    );

    // Bind discharge to parent macaroon and authorize through the 4-round BDOZ barrier!
    let mut bound_discharge = unbound_discharge;
    macaroon
        .bind_discharge(&mut bound_discharge)
        .expect("bind_discharge");
    let mac_gate = CapabilityGate::Macaroon {
        verifier: &mac_verifier,
        token: &macaroon,
        discharges: &[Discharge {
            token: &bound_discharge,
            root_key: &third_party_key,
        }],
    };
    let release_b1 = engine
        .authorize_committed_barrier(
            &intent_b1,
            session_b1,
            2_500,
            Some(&mac_gate),
            &mut guards[1..4],
            &accel,
        )
        .expect("PolicyEngine authorize B1");
    assert_eq!(guards[0].accumulated_window_spend(), 0);
    assert!(
        guards[1..4]
            .iter()
            .all(|g| g.accumulated_window_spend() == 4_500)
    );

    let party_tokens_b1 = split_and_check_party_bindings(
        release_b1,
        &canonical_key_id,
        &signing_bytes_b1,
        signing_ctx,
        &quorum,
    );

    // Execute real policy-gated 3-of-4 (`2t - 1 = 3`) threshold ML-DSA signing across `[20, 30, 40]`!
    let party_inputs_b1: Vec<_> = mldsa_shares[1..4]
        .iter_mut()
        .zip(burn_stores[1..4].iter_mut())
        .zip(party_tokens_b1)
        .enumerate()
        .map(|(idx, ((sh, burn), tok))| (idx, sh, burn, tok))
        .collect();
    let sig_outputs_b1 = run_mpc_parties(party_inputs_b1, |_, (idx, sh, burn, tok), net| {
        threshold_sign_mldsa_party_policy_gated(
            sh,
            ThresholdPolicyGate {
                token: tok,
                expected_intent_digest: &intent_digest_b1,
                quorum: &quorum,
            },
            &signing_bytes_b1,
            signing_ctx,
            &[0xA0 + idx as u8; 32],
            burn as &mut dyn NonceBurnPersistence,
            net,
        )
        .expect("threshold_sign_mldsa_party_policy_gated B1")
    });
    let sig_b1 = &sig_outputs_b1[0].signature;
    assert!(sig_outputs_b1.iter().all(|o| &o.signature == sig_b1));
    assert!(ml_dsa_verify(
        MlDsaLevel::MlDsa44,
        &pack.pk_bytes,
        &signing_bytes_b1,
        signing_ctx,
        sig_b1
    ));
    let sig_b1_arr: [u8; ml_dsa_44::SIG_LEN] = sig_b1.as_slice().try_into().unwrap();
    assert!(upstream_pk.verify(&signing_bytes_b1, &sig_b1_arr, signing_ctx));

    // ------------------------------------------------------------------------
    // Flow B2: Multi-hop `Compact1122` `PqBiscuit` (PoP request-bound) -> `PolicyEngine` -> `ThresholdMlDsa`
    // ------------------------------------------------------------------------
    assert_eq!(PQ_BISCUIT_HOP_CRYPTO_BYTES, 1154);
    let dp_1122 = FrontierDpTable::build(FrontierFtsProfile::Compact1122);
    let mut biscuit_auth =
        PqBiscuitAuthorityKey::keygen([0xB1; 32], [0xB2; 32], 2, &accel).expect("PqBiscuit keygen");
    let biscuit_auth_pk = *biscuit_auth.public_key();
    assert_eq!(biscuit_auth.remaining_mints(), 4);

    let session_b2 = [0x72; 32];
    let (mut intent_b2, _) = TransactionIntent::builder(
        2026,
        WitnessSuiteTag::MlDsa44,
        recipient.clone(),
        800, // Tier 0 (`<= 1000`, 1 non-initiator approver suffices, rolling spend `4500 + 800 = 5300`)
    )
    .rolling_window(4_500, [0; 32])
    .window_id(0)
    .timestamp_secs(3_000)
    .initiator_and_approvers(10, &[20, 30, 40])
    .bind_signing_payload(
        &SigningPayloadBinding {
            key_id: canonical_key_id,
            payload: b"wire-transfer-002: 800 units via Compact1122 PQ Biscuit",
            ctx: signing_ctx,
            session_id: session_b2,
            policy_revision: 1,
            quorum: &quorum,
            authority_pk,
        },
        &policy,
    )
    .expect("bind_signing_payload B2");
    let signing_bytes_b2 = guards[0]
        .authenticate_initiated_intent(&policy, &mut intent_b2)
        .expect("authenticate_initiated_intent B2");
    let intent_digest_b2 = intent_b2.canonical_digest();

    // Root mint (hop 0) -> offline public-key attenuation (hop 1) -> PoP request-bound seal!
    let (biscuit_hop0, step1) = biscuit_auth
        .mint(
            &dp_1122,
            [0xC1; 32],
            audience,
            &[
                Caveat::NotBefore(2_000),
                Caveat::ExpiresAt(6_000),
                Caveat::MaxAmount(5_000),
            ],
            [0xC2; 32],
            &[0xC3; 32],
            &accel,
        )
        .expect("PqBiscuit mint");
    assert_eq!(biscuit_auth.remaining_mints(), 3);

    // Unsealed `PqBiscuit` MUST be rejected before latching any BDOZ slot!
    let unsealed_gate = CapabilityGate::Biscuit {
        authority_pk: &biscuit_auth_pk,
        dp: &dp_1122,
        token: &biscuit_hop0,
    };
    assert!(
        engine
            .authorize_committed_barrier(
                &intent_b2,
                session_b2,
                3_000,
                Some(&unsealed_gate),
                &mut guards[1..4],
                &accel,
            )
            .is_err()
    );

    // Offline attenuation narrowing `MaxAmount` to `1_000` and pinning `Resource` + `Actions`.
    let (biscuit_hop1, step2) = step1
        .attenuate(
            &biscuit_hop0,
            &dp_1122,
            &[
                Caveat::MaxAmount(1_000),
                Caveat::Resource(recipient.commitment_256),
                Caveat::Actions(required_actions),
            ],
            [0xC4; 32],
            &[0xC5; 32],
            &accel,
        )
        .expect("PqBiscuit attenuate");
    let bound_req =
        CapabilityRequest::from_policy_intent(&policy, &intent_b2, required_actions, 3_000);
    let sealed_biscuit = step2
        .seal(
            &biscuit_hop1,
            &dp_1122,
            Some(&bound_req),
            &[0xC6; 32],
            &accel,
        )
        .expect("PqBiscuit seal");

    let biscuit_wire = sealed_biscuit.to_bytes().expect("PqBiscuit::to_bytes");
    let decoded_biscuit = PqBiscuit::from_bytes(&biscuit_wire).expect("PqBiscuit::from_bytes");
    assert_eq!(decoded_biscuit, sealed_biscuit);

    let biscuit_gate = CapabilityGate::Biscuit {
        authority_pk: &biscuit_auth_pk,
        dp: &dp_1122,
        token: &decoded_biscuit,
    };
    // Replay at a different timestamp (`3_001 != 3_000`) fails PoP request-bound seal verification!
    assert_eq!(
        engine.verify_capability(&intent_b2, 3_001, &biscuit_gate),
        Err(PolicyViolation::CapabilityDenied(
            CapabilityError::InvalidTag
        ))
    );

    let release_b2 = engine
        .authorize_committed_barrier(
            &intent_b2,
            session_b2,
            3_000,
            Some(&biscuit_gate),
            &mut guards[1..4],
            &accel,
        )
        .expect("PolicyEngine authorize B2 via Compact1122 PqBiscuit");
    assert!(
        guards[1..4]
            .iter()
            .all(|g| g.accumulated_window_spend() == 5_300)
    );

    let party_tokens_b2 = split_and_check_party_bindings(
        release_b2,
        &canonical_key_id,
        &signing_bytes_b2,
        signing_ctx,
        &quorum,
    );
    let party_inputs_b2: Vec<_> = mldsa_shares[1..4]
        .iter_mut()
        .zip(burn_stores[1..4].iter_mut())
        .zip(party_tokens_b2)
        .enumerate()
        .map(|(idx, ((sh, burn), tok))| (idx, sh, burn, tok))
        .collect();
    let sig_outputs_b2 = run_mpc_parties(party_inputs_b2, |_, (idx, sh, burn, tok), net| {
        threshold_sign_mldsa_party_policy_gated(
            sh,
            ThresholdPolicyGate {
                token: tok,
                expected_intent_digest: &intent_digest_b2,
                quorum: &quorum,
            },
            &signing_bytes_b2,
            signing_ctx,
            &[0xD0 + idx as u8; 32],
            burn as &mut dyn NonceBurnPersistence,
            net,
        )
        .expect("threshold_sign_mldsa_party_policy_gated B2")
    });
    let sig_b2_arr: [u8; ml_dsa_44::SIG_LEN] =
        sig_outputs_b2[0].signature.as_slice().try_into().unwrap();
    assert!(upstream_pk.verify(&signing_bytes_b2, &sig_b2_arr, signing_ctx));

    // Negative check (Flow B3): a fresh move-only `AuthorizedSignReleaseToken` presented with a
    // hijacked signing payload MUST be rejected by `threshold_sign_mldsa_party_policy_gated` with
    // `PolicyTokenDigestMismatch` before running any MPC round!
    let session_b3 = [0x73; 32];
    let (mut intent_b3, _) =
        TransactionIntent::builder(2026, WitnessSuiteTag::MlDsa44, recipient, 100)
            .rolling_window(5_300, [0; 32])
            .window_id(0)
            .timestamp_secs(3_100)
            .initiator_and_approvers(10, &[20, 30, 40])
            .bind_signing_payload(
                &SigningPayloadBinding {
                    key_id: canonical_key_id,
                    payload: b"wire-transfer-003: 100 units",
                    ctx: signing_ctx,
                    session_id: session_b3,
                    policy_revision: 1,
                    quorum: &quorum,
                    authority_pk,
                },
                &policy,
            )
            .expect("bind_signing_payload B3");
    let signing_bytes_b3 = guards[0]
        .authenticate_initiated_intent(&policy, &mut intent_b3)
        .expect("authenticate_initiated_intent B3");
    let intent_digest_b3 = intent_b3.canonical_digest();
    let release_b3 = engine
        .authorize_committed_barrier(
            &intent_b3,
            session_b3,
            3_100,
            None,
            &mut guards[1..4],
            &accel,
        )
        .expect("PolicyEngine authorize B3");
    let mut party_tokens_b3 = release_b3.into_quorum_party_tokens();
    let tok0_b3 = party_tokens_b3.remove(0);
    let tok1_b3 = party_tokens_b3.remove(0);
    assert_eq!(
        (tok0_b3.party_id(), tok1_b3.party_id()),
        (Some(20), Some(30))
    );

    let mut dummy_ep = MpcEndpoint {
        net: Arc::new(LocalMpcNet {
            state: Mutex::new(NetState {
                round: 0,
                posted: vec![None],
                taken: vec![false],
                stopped: false,
            }),
            changed: Condvar::new(),
        }),
        me: 0,
    };
    let epoch_before_refusals = burn_stores[1].next_epoch(&canonical_key_id, 20);
    assert!(epoch_before_refusals.is_ok());
    let bad_res = threshold_sign_mldsa_party_policy_gated(
        &mut mldsa_shares[1],
        ThresholdPolicyGate {
            token: tok0_b3,
            expected_intent_digest: &intent_digest_b3,
            quorum: &quorum,
        },
        b"unauthorized-hijacked-payload",
        signing_ctx,
        &[0x99; 32],
        &mut burn_stores[1],
        &mut dummy_ep,
    );
    assert_eq!(
        bad_res.err(),
        Some(ThresholdMlDsaError::PolicyTokenDigestMismatch)
    );

    // Custodian `20` presenting custodian `30`'s token for the authorized payload is refused
    // the same way, and neither refusal burns a nonce epoch.
    let swapped_res = threshold_sign_mldsa_party_policy_gated(
        &mut mldsa_shares[1],
        ThresholdPolicyGate {
            token: tok1_b3,
            expected_intent_digest: &intent_digest_b3,
            quorum: &quorum,
        },
        &signing_bytes_b3,
        signing_ctx,
        &[0x9A; 32],
        &mut burn_stores[1],
        &mut dummy_ep,
    );
    assert_eq!(
        swapped_res.err(),
        Some(ThresholdMlDsaError::PolicyTokenDigestMismatch)
    );
    assert_eq!(
        burn_stores[1].next_epoch(&canonical_key_id, 20),
        epoch_before_refusals
    );
}

#[test]
fn e2e_nonce_burn_reopen_preserves_public_replay_contract() {
    let tmp = TempDirGuard::new("nonce-reopen");
    let path = tmp.path().join("nonce-burn");
    let key = [0x31; 32];
    let mac_key = [0x42; 32];
    let session = [0x53; 32];
    let mut store = FsNonceBurnStore::create(&path, key, mac_key).unwrap();
    assert_eq!(store.next_epoch(&key, 20), Ok(0));
    assert!(store.reserve(20, 0, &session, 0));
    assert_eq!(store.next_epoch(&key, 20), Ok(1));
    drop(store);

    let mut store = FsNonceBurnStore::open(&path, key, mac_key).unwrap();
    assert_eq!(store.next_epoch(&key, 20), Ok(1));
    assert!(!store.reserve(20, 0, &session, 0));
    // A fresh epoch cannot replay an already burned (party, session, attempt).
    assert!(!store.reserve(20, 1, &session, 0));
    assert_eq!(store.next_epoch(&key, 20), Ok(1));
    assert!(store.reserve(20, 1, &session, 1));
    // Reservations are scoped to the party, so another custodian may reserve its own tuple.
    assert_eq!(store.next_epoch(&key, 30), Ok(0));
    assert!(store.reserve(30, 0, &session, 0));
    assert_eq!(
        store.next_epoch(&[0xff; 32], 20),
        Err(ThresholdMlDsaError::NoncePersistenceFailed)
    );
    drop(store);

    let mut reopened = FsNonceBurnStore::open(&path, key, mac_key).unwrap();
    assert_eq!(reopened.next_epoch(&key, 20), Ok(2));
    assert_eq!(reopened.next_epoch(&key, 30), Ok(1));
    assert!(!reopened.reserve(20, 2, &session, 1));
    assert!(!reopened.reserve(30, 1, &session, 0));
}

// ============================================================================
// Journey C: Paged Crash Journals (`QSBURN05` in `qsag-fts` & `QSHDQB04` in `qsag-hd`)
// ============================================================================

const PAGE_BYTES: usize = HWM_PAGE_BYTES as usize; // 4096
const HEADER_BYTES: usize = 3 * PAGE_BYTES; // 12,288
const SLOT_A_OFF: usize = PAGE_BYTES; // 4096
const SLOT_B_OFF: usize = 2 * PAGE_BYTES; // 8192
const QSBURN05_REC_BYTES: usize = 42;
const QSHDQB04_REC_BYTES: usize = 40;

fn write_in_place(path: &Path, offset: u64, data: &[u8]) {
    let mut f = OpenOptions::new().write(true).open(path).unwrap();
    f.seek(SeekFrom::Start(offset)).unwrap();
    f.write_all(data).unwrap();
    f.sync_all().unwrap();
}

fn burn_file_identity_be(path: &Path) -> [u8; 16] {
    let meta = fs::metadata(path).unwrap();
    let (dev, ino) = file_dev_ino(&meta).unwrap();
    let mut id = [0u8; 16];
    id[..8].copy_from_slice(&dev.to_be_bytes());
    id[8..].copy_from_slice(&ino.to_be_bytes());
    id
}

#[test]
fn e2e_qsburn05_paged_crash_journal_tears_tail_truncation_and_tamper_matrix() {
    let tmp = TempDirGuard::new("qsburn05");
    let key = [0x17; 32];
    let mac_key = [0x29; 32];

    // Provision a clean journal with 2 committed burns: `(0, 10)` and `(1, 11)`.
    let mk_two_burns = |name: &str| -> (PathBuf, [u8; 32], [u8; 32], [u8; 32]) {
        let p = tmp.path().join(name);
        let mut j = DurableBurnJournal::create(&p, key, mac_key).unwrap();
        j.reserve(&key, 0, 10).unwrap();
        let ck1 = j.checkpoint();
        j.reserve(&key, 1, 11).unwrap();
        let ck2 = j.checkpoint();
        drop(j);

        let raw = fs::read(&p).unwrap();
        assert_eq!(raw.len(), HEADER_BYTES + 2 * QSBURN05_REC_BYTES);
        assert_eq!(&raw[..8], b"QSBURN05");
        let genesis: [u8; 32] = raw[40..72].try_into().unwrap();
        (p, genesis, ck1.tag, ck2.tag)
    };

    // 1. Verify exact 3-page layout (`4096`, `8192`, `12288`) & NIST SP 800-185 cSHAKE256 MAC parity!
    {
        let (p, genesis, tag1, tag2) = mk_two_burns("layout.burn");
        let raw = fs::read(&p).unwrap();
        let id = burn_file_identity_be(&p);

        let expected_gen_mac =
            cshake256_framed_32_nist_ref(b"QSAG.BURN.GENESIS.V4", &[&mac_key, &id, &raw[..72]]);
        assert_eq!(&raw[72..104], &expected_gen_mac);

        let expected_rec1_mac = cshake256_framed_32_nist_ref(
            b"QSAG.BURN.RECORD.V2",
            &[
                &mac_key,
                &key,
                &genesis,
                &expected_gen_mac,
                &raw[HEADER_BYTES..HEADER_BYTES + 10],
            ],
        );
        assert_eq!(tag1, expected_rec1_mac);

        for (slot, off) in [(0u8, SLOT_A_OFF), (1u8, SLOT_B_OFF)] {
            let slot_bytes = &raw[off..off + HWM_SLOT_BYTES];
            assert_eq!(&slot_bytes[..8], &2u64.to_be_bytes());
            assert_eq!(&slot_bytes[8..40], &tag2);
            let expected_hwm_mac = cshake256_framed_32_nist_ref(
                b"QSAG.BURN.HWM.V4",
                &[
                    &mac_key,
                    &id,
                    &key,
                    &genesis,
                    &[slot],
                    &2u64.to_be_bytes(),
                    &tag2,
                    &[0u8; 8],
                ],
            );
            assert_eq!(&slot_bytes[40..72], &expected_hwm_mac);
            assert_eq!(&slot_bytes[72..80], &[0u8; 8]);
        }
    }

    // 2. Sector tear on Slot A (`4096`) AND sector tear on Slot B (`8192`) -> heals cleanly;
    //    simultaneous tear on BOTH Slot A and Slot B -> fails closed!
    for (name, tear_off) in [("tear_a.burn", SLOT_A_OFF), ("tear_b.burn", SLOT_B_OFF)] {
        let (p, _, _, tag2) = mk_two_burns(name);
        write_in_place(&p, tear_off as u64, &[0xFFu8; HWM_SLOT_BYTES]);
        let mut recovered = DurableBurnJournal::open_existing(&p, key, mac_key).unwrap();
        assert_eq!(recovered.checkpoint().generation, 2);
        assert_eq!(recovered.checkpoint().tag, tag2);
        // Burned epochs remain enforced and new burns succeed!
        assert!(recovered.reserve(&key, 0, 10).is_err());
        assert!(recovered.reserve(&key, 1, 11).is_err());
        recovered.reserve(&key, 2, 12).unwrap();
        assert_eq!(recovered.checkpoint().generation, 3);
    }
    {
        let (p, _, _, _) = mk_two_burns("tear_both.burn");
        write_in_place(&p, SLOT_A_OFF as u64, &[0xAAu8; HWM_SLOT_BYTES]);
        write_in_place(&p, SLOT_B_OFF as u64, &[0x55u8; HWM_SLOT_BYTES]);
        assert!(DurableBurnJournal::open_existing(&p, key, mac_key).is_err());
    }

    // 3. Uncommitted tail bytes (`<= 42 B`) across ALL 3 `TwoSlotHwmCrashModel` crash states:
    //    (3a) Steady `(Slot A = 2, Slot B = 2)` + 17-byte partial append AND 42-byte torn record
    for tail_len in [1usize, 17, QSBURN05_REC_BYTES] {
        let (p, _, _, tag2) = mk_two_burns(&format!("tail_steady_{tail_len}.burn"));
        write_in_place(
            &p,
            (HEADER_BYTES + 2 * QSBURN05_REC_BYTES) as u64,
            &vec![0xEEu8; tail_len],
        );
        let recovered = DurableBurnJournal::open_existing(&p, key, mac_key).unwrap();
        assert_eq!(recovered.checkpoint().generation, 2);
        assert_eq!(recovered.checkpoint().tag, tag2);
        drop(recovered);
        assert_eq!(
            fs::metadata(&p).unwrap().len(),
            (HEADER_BYTES + 2 * QSBURN05_REC_BYTES) as u64
        );
    }

    //    (3b) Lagging Slot B (`Slot A = 2, Slot B = 1`) + 42-byte uncommitted tail:
    //         Recovery truncates tail AND heals Slot B up to `2`!
    {
        let (p, genesis, tag1, tag2) = mk_two_burns("tail_lagging_b.burn");
        let id = burn_file_identity_be(&p);
        let hwm_mac = |slot: u8, ctr: &[u8; 8], tip: &[u8; 32], res: &[u8; 8]| {
            cshake256_framed_32_nist_ref(
                b"QSAG.BURN.HWM.V4",
                &[&mac_key, &id, &key, &genesis, &[slot], ctr, tip, res],
            )
        };
        let hwm = TwoSlotHwm::paged(1, CounterOrder::Big, &hwm_mac);
        let slot_b_gen1 = hwm.encode(1, 1, &tag1);
        write_in_place(&p, SLOT_B_OFF as u64, &slot_b_gen1);
        write_in_place(
            &p,
            (HEADER_BYTES + 2 * QSBURN05_REC_BYTES) as u64,
            &[0xDEu8; QSBURN05_REC_BYTES],
        );

        let recovered = DurableBurnJournal::open_existing(&p, key, mac_key).unwrap();
        assert_eq!(recovered.checkpoint().generation, 2);
        assert_eq!(recovered.checkpoint().tag, tag2);
        drop(recovered);
        let healed = fs::read(&p).unwrap();
        assert_eq!(healed.len(), HEADER_BYTES + 2 * QSBURN05_REC_BYTES);
        assert_eq!(&healed[SLOT_B_OFF..SLOT_B_OFF + 8], &2u64.to_be_bytes());
    }

    //    (3c) Unacknowledged synced record (`committed = 3` reached disk while `Slot A = Slot B = 2`),
    //         followed by a 19-byte uncommitted tail -> advances HWM to `3` AND truncates the 19-byte tail!
    {
        let (p, genesis, _, tag2) = mk_two_burns("tail_committed_plus_1.burn");
        let mut rec3 = [0u8; QSBURN05_REC_BYTES];
        rec3[..2].copy_from_slice(&2u16.to_be_bytes());
        rec3[2..10].copy_from_slice(&12u64.to_be_bytes());
        let tag3 = cshake256_framed_32_nist_ref(
            b"QSAG.BURN.RECORD.V2",
            &[&mac_key, &key, &genesis, &tag2, &rec3[..10]],
        );
        rec3[10..].copy_from_slice(&tag3);
        write_in_place(&p, (HEADER_BYTES + 2 * QSBURN05_REC_BYTES) as u64, &rec3);
        write_in_place(
            &p,
            (HEADER_BYTES + 3 * QSBURN05_REC_BYTES) as u64,
            &[0xABu8; 19],
        );

        let mut recovered = DurableBurnJournal::open_existing(&p, key, mac_key).unwrap();
        assert_eq!(recovered.checkpoint().generation, 3);
        assert_eq!(recovered.checkpoint().tag, tag3);
        assert!(
            recovered.reserve(&key, 2, 12).is_err(),
            "record 3 must stay burned"
        );
        drop(recovered);
        let healed = fs::read(&p).unwrap();
        assert_eq!(healed.len(), HEADER_BYTES + 3 * QSBURN05_REC_BYTES);
        assert_eq!(&healed[SLOT_A_OFF..SLOT_A_OFF + 8], &3u64.to_be_bytes());
        assert_eq!(&healed[SLOT_B_OFF..SLOT_B_OFF + 8], &3u64.to_be_bytes());
    }

    //    (3d) Oversized uncommitted tail (`43 B = RECORD_LEN + 1`) -> MUST fail closed!
    {
        let (p, _, _, _) = mk_two_burns("tail_oversized.burn");
        write_in_place(
            &p,
            (HEADER_BYTES + 2 * QSBURN05_REC_BYTES) as u64,
            &[0xEEu8; QSBURN05_REC_BYTES + 1],
        );
        assert!(DurableBurnJournal::open_existing(&p, key, mac_key).is_err());
    }

    // 4. Committed-record corruption, silent last-record truncation, overclaimed HWM, and inode copy:
    //    ALL must fail closed without truncating committed history!
    {
        // Flipping 1 bit in committed record #2 (`index = 1`): `verified = 1 < HWM = 2` -> refused!
        let (p, _, _, _) = mk_two_burns("corrupt_committed.burn");
        let last_rec_off = HEADER_BYTES + QSBURN05_REC_BYTES + 5;
        let mut raw = fs::read(&p).unwrap();
        raw[last_rec_off] ^= 0x01;
        write_in_place(&p, last_rec_off as u64, &[raw[last_rec_off]]);
        assert!(DurableBurnJournal::open_existing(&p, key, mac_key).is_err());
    }
    {
        // Truncating record #2 off disk while HWM slots hold `2` -> refused!
        let (p, _, _, _) = mk_two_burns("truncated_chain.burn");
        let f = OpenOptions::new().write(true).open(&p).unwrap();
        f.set_len((HEADER_BYTES + QSBURN05_REC_BYTES) as u64)
            .unwrap();
        f.sync_all().unwrap();
        assert!(DurableBurnJournal::open_existing(&p, key, mac_key).is_err());
    }
    {
        // Forging authenticated HWM slots claiming `counter = 3` when only `2` records exist -> refused!
        let (p, genesis, _, tag2) = mk_two_burns("overclaimed_hwm.burn");
        let id = burn_file_identity_be(&p);
        let hwm_mac = |slot: u8, ctr: &[u8; 8], tip: &[u8; 32], res: &[u8; 8]| {
            cshake256_framed_32_nist_ref(
                b"QSAG.BURN.HWM.V4",
                &[&mac_key, &id, &key, &genesis, &[slot], ctr, tip, res],
            )
        };
        let hwm = TwoSlotHwm::paged(1, CounterOrder::Big, &hwm_mac);
        write_in_place(&p, SLOT_A_OFF as u64, &hwm.encode(0, 3, &tag2));
        write_in_place(&p, SLOT_B_OFF as u64, &hwm.encode(1, 3, &tag2));
        assert!(DurableBurnJournal::open_existing(&p, key, mac_key).is_err());
    }
    {
        // Copying valid journal bytes onto a fresh file (different inode) -> refused!
        let (p, _, _, _) = mk_two_burns("orig_inode.burn");
        let copy_path = tmp.path().join("copied_inode.burn");
        fs::copy(&p, &copy_path).unwrap();
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(&copy_path, fs::Permissions::from_mode(0o600)).unwrap();
        }
        assert!(DurableBurnJournal::open_existing(&copy_path, key, mac_key).is_err());
    }
}

#[test]
fn e2e_qshdqb04_paged_crash_journal_tears_tail_truncation_and_tamper_matrix() {
    let tmp = TempDirGuard::new("qshdqb04");
    let family = [0x3B; 32];
    let key = [0x4D; 32];

    // Provision a clean `QSHDQB04` HD query-budget journal with `used = 2` (`3` records including genesis `0`).
    let mk_two_uses = |name: &str| -> (PathBuf, [u8; 8], [u8; 16], [u8; 32], [u8; 32]) {
        let p = tmp.path().join(name);
        let mut b = DurableQueryBudget::create(&p, family, key).unwrap();
        b.reserve().unwrap();
        let mac1 = b.checkpoint().tag;
        b.reserve().unwrap();
        let mac2 = b.checkpoint().tag;
        assert_eq!(b.used(), 2);
        drop(b);

        let raw = fs::read(&p).unwrap();
        assert_eq!(raw.len(), HEADER_BYTES + 3 * QSHDQB04_REC_BYTES);
        assert_eq!(
            &raw[RECORD_HEADER_BYTES + 16..RECORD_HEADER_BYTES + 24],
            b"QSHDQB04"
        );
        // `LockedRecord` 16-byte header stores `QSAGREC1` (`[0..8]`) + `lock_seal` (`[8..16]`).
        assert_eq!(&raw[0..8], b"QSAGREC1");
        let lock_seal: [u8; 8] = raw[8..16].try_into().unwrap();
        let data_seal = asm_file_identity(&fs::metadata(&p).unwrap());
        assert_eq!(
            &raw[RECORD_HEADER_BYTES..RECORD_HEADER_BYTES + 16],
            &data_seal
        );
        (p, lock_seal, data_seal, mac1, mac2)
    };

    // 1. Verify physical page alignment (`4096` Slot A, `8192` Slot B, `12288` genesis record)
    //    and NIST SP 800-185 `cshake256_framed_32_nist_ref` MAC parity!
    {
        let (p, lock_seal, data_seal, mac1, mac2) = mk_two_uses("layout.hdqb");
        let raw = fs::read(&p).unwrap();
        let limit_le = 128u64.to_le_bytes();

        let mac0 = cshake256_framed_32_nist_ref(
            b"QSAG.HD.QUERY_BUDGET.V3",
            &[
                &key,
                &family,
                &lock_seal,
                &data_seal,
                &limit_le,
                &0u64.to_le_bytes(),
                &[0u8; 32],
            ],
        );
        assert_eq!(&raw[HEADER_BYTES + 8..HEADER_BYTES + 40], &mac0);
        let expected_mac1 = cshake256_framed_32_nist_ref(
            b"QSAG.HD.QUERY_BUDGET.V3",
            &[
                &key,
                &family,
                &lock_seal,
                &data_seal,
                &limit_le,
                &1u64.to_le_bytes(),
                &mac0,
            ],
        );
        assert_eq!(mac1, expected_mac1);

        for (slot, off) in [(0u8, SLOT_A_OFF), (1u8, SLOT_B_OFF)] {
            let slot_bytes = &raw[off..off + HWM_SLOT_BYTES];
            assert_eq!(&slot_bytes[..8], &2u64.to_le_bytes());
            assert_eq!(&slot_bytes[8..40], &mac2);
            let expected_hwm_mac = cshake256_framed_32_nist_ref(
                b"QSAG.HD.QUERY_BUDGET.HWM.V4",
                &[
                    &key,
                    &family,
                    &lock_seal,
                    &data_seal,
                    &[slot],
                    &limit_le,
                    &2u64.to_le_bytes(),
                    &mac2,
                    &[0u8; 8],
                ],
            );
            assert_eq!(&slot_bytes[40..72], &expected_hwm_mac);
        }
    }

    // 2. Sector tear on Slot A (`4096`) AND Slot B (`8192`) -> recovers; dual tear -> fails closed!
    for (name, tear_off) in [("tear_a.hdqb", SLOT_A_OFF), ("tear_b.hdqb", SLOT_B_OFF)] {
        let (p, _, _, _, mac2) = mk_two_uses(name);
        write_in_place(&p, tear_off as u64, &[0xCCu8; HWM_SLOT_BYTES]);
        let mut b = DurableQueryBudget::open(&p, family, key).unwrap();
        assert_eq!(b.used(), 2);
        assert_eq!(b.checkpoint().tag, mac2);
        b.reserve().unwrap();
        assert_eq!(b.used(), 3);
    }
    {
        let (p, _, _, _, _) = mk_two_uses("tear_both.hdqb");
        write_in_place(&p, SLOT_A_OFF as u64, &[0xCCu8; HWM_SLOT_BYTES]);
        write_in_place(&p, SLOT_B_OFF as u64, &[0x33u8; HWM_SLOT_BYTES]);
        assert_eq!(
            DurableQueryBudget::open(&p, family, key).err(),
            Some(HdError::BudgetStorageFailed)
        );
    }

    // 3. Uncommitted tail bytes (`<= 40 B`) across steady `(2, 2)`, lagging Slot B `(2, 1)`,
    //    and synced unacknowledged record `used = 3` while HWM holds `(2, 2)`, plus `41 B` rejection!
    for tail_len in [1usize, 23, QSHDQB04_REC_BYTES] {
        let (p, _, _, _, mac2) = mk_two_uses(&format!("tail_steady_{tail_len}.hdqb"));
        write_in_place(
            &p,
            (HEADER_BYTES + 3 * QSHDQB04_REC_BYTES) as u64,
            &vec![0x77u8; tail_len],
        );
        let b = DurableQueryBudget::open(&p, family, key).unwrap();
        assert_eq!(b.used(), 2);
        assert_eq!(b.checkpoint().tag, mac2);
        drop(b);
        assert_eq!(
            fs::metadata(&p).unwrap().len(),
            (HEADER_BYTES + 3 * QSHDQB04_REC_BYTES) as u64
        );
    }

    {
        // Lagging Slot B (`Slot A = 2, Slot B = 1`) + 40-byte uncommitted tail -> truncates & heals!
        let (p, lock_seal, data_seal, mac1, mac2) = mk_two_uses("tail_lagging_b.hdqb");
        let limit_le = 128u64.to_le_bytes();
        let hwm_mac = |slot: u8, used: &[u8; 8], tip: &[u8; 32], res: &[u8; 8]| {
            cshake256_framed_32_nist_ref(
                b"QSAG.HD.QUERY_BUDGET.HWM.V4",
                &[
                    &key,
                    &family,
                    &lock_seal,
                    &data_seal,
                    &[slot],
                    &limit_le,
                    used,
                    tip,
                    res,
                ],
            )
        };
        let hwm = TwoSlotHwm::paged(1, CounterOrder::Little, &hwm_mac);
        write_in_place(&p, SLOT_B_OFF as u64, &hwm.encode(1, 1, &mac1));
        write_in_place(
            &p,
            (HEADER_BYTES + 3 * QSHDQB04_REC_BYTES) as u64,
            &[0x99u8; QSHDQB04_REC_BYTES],
        );

        let b = DurableQueryBudget::open(&p, family, key).unwrap();
        assert_eq!(b.used(), 2);
        assert_eq!(b.checkpoint().tag, mac2);
        drop(b);
        let healed = fs::read(&p).unwrap();
        assert_eq!(healed.len(), HEADER_BYTES + 3 * QSHDQB04_REC_BYTES);
        assert_eq!(&healed[SLOT_B_OFF..SLOT_B_OFF + 8], &2u64.to_le_bytes());
    }

    {
        // Unacknowledged synced record `count = 3` (`used = 3`) while HWM slots hold `2`, plus 15B tail!
        let (p, lock_seal, data_seal, _, mac2) = mk_two_uses("tail_committed_plus_1.hdqb");
        let mut rec3 = [0u8; QSHDQB04_REC_BYTES];
        rec3[..8].copy_from_slice(&3u64.to_le_bytes());
        let mac3 = cshake256_framed_32_nist_ref(
            b"QSAG.HD.QUERY_BUDGET.V3",
            &[
                &key,
                &family,
                &lock_seal,
                &data_seal,
                &128u64.to_le_bytes(),
                &rec3[..8],
                &mac2,
            ],
        );
        rec3[8..].copy_from_slice(&mac3);
        write_in_place(&p, (HEADER_BYTES + 3 * QSHDQB04_REC_BYTES) as u64, &rec3);
        write_in_place(
            &p,
            (HEADER_BYTES + 4 * QSHDQB04_REC_BYTES) as u64,
            &[0xFEu8; 15],
        );

        let b = DurableQueryBudget::open(&p, family, key).unwrap();
        assert_eq!(b.used(), 3);
        assert_eq!(b.checkpoint().tag, mac3);
        drop(b);
        let healed = fs::read(&p).unwrap();
        assert_eq!(healed.len(), HEADER_BYTES + 4 * QSHDQB04_REC_BYTES);
        assert_eq!(&healed[SLOT_A_OFF..SLOT_A_OFF + 8], &3u64.to_le_bytes());
        assert_eq!(&healed[SLOT_B_OFF..SLOT_B_OFF + 8], &3u64.to_le_bytes());
    }

    {
        // Oversized tail (`41 B = RECORD_LEN + 1`) -> fails closed!
        let (p, _, _, _, _) = mk_two_uses("tail_oversized.hdqb");
        write_in_place(
            &p,
            (HEADER_BYTES + 3 * QSHDQB04_REC_BYTES) as u64,
            &[0x77u8; QSHDQB04_REC_BYTES + 1],
        );
        assert_eq!(
            DurableQueryBudget::open(&p, family, key).err(),
            Some(HdError::BudgetStorageFailed)
        );
    }

    // 4. Committed-record corruption & overclaimed HWM must fail closed!
    {
        let (p, _, _, _, _) = mk_two_uses("corrupt_committed.hdqb");
        let rec2_off = HEADER_BYTES + 2 * QSHDQB04_REC_BYTES + 12;
        let mut raw = fs::read(&p).unwrap();
        raw[rec2_off] ^= 0x01;
        write_in_place(&p, rec2_off as u64, &[raw[rec2_off]]);
        assert_eq!(
            DurableQueryBudget::open(&p, family, key).err(),
            Some(HdError::BudgetStorageFailed)
        );
    }
    {
        let (p, lock_seal, data_seal, _, mac2) = mk_two_uses("overclaimed_hwm.hdqb");
        let limit_le = 128u64.to_le_bytes();
        let hwm_mac = |slot: u8, used: &[u8; 8], tip: &[u8; 32], res: &[u8; 8]| {
            cshake256_framed_32_nist_ref(
                b"QSAG.HD.QUERY_BUDGET.HWM.V4",
                &[
                    &key,
                    &family,
                    &lock_seal,
                    &data_seal,
                    &[slot],
                    &limit_le,
                    used,
                    tip,
                    res,
                ],
            )
        };
        let hwm = TwoSlotHwm::paged(1, CounterOrder::Little, &hwm_mac);
        write_in_place(&p, SLOT_A_OFF as u64, &hwm.encode(0, 3, &mac2));
        write_in_place(&p, SLOT_B_OFF as u64, &hwm.encode(1, 3, &mac2));
        assert_eq!(
            DurableQueryBudget::open(&p, family, key).err(),
            Some(HdError::BudgetStorageFailed)
        );
    }
}

#[test]
fn e2e_shamir_17_custodian_committee_policy_gated_mldsa_signing() {
    // C5 §6(e): Committees above 16 custodians (`17 <= n <= 64`) switch from direct RSS subsets
    // to Shamir secret sharing (`is_shamir() == true`) with on-the-fly Shamir -> RSS projection
    // onto the active `2t - 1` signing quorum.
    let accel = CpuReferenceBackend::new();
    let tmp = TempDirGuard::new("shamir-17-mldsa");
    let party_ids: Vec<u16> = (1..=17).map(|i| i * 10).collect();
    let dkg_cfg = ThresholdMlDsaDkgConfig {
        level: MlDsaLevel::MlDsa44,
        threshold: 2,
        party_ids: party_ids.clone(),
        session_id: [0x9A; 32],
    };
    let committee_cfg = dkg_cfg.shamir_committee().expect("shamir_committee");
    let mut committee_shares = run_mpc_parties(vec![0u8, 1, 2], |_, idx, net| {
        threshold_mldsa_dkg_party(
            &committee_cfg,
            committee_cfg.party_ids[idx as usize],
            &[0x05 + idx; 32],
            net,
        )
        .expect("3-party sampling committee DKG")
    });
    let expand_inputs: Vec<(u8, Option<_>)> = (0..17u8)
        .map(|idx| {
            let cs = if idx < 3 {
                Some(committee_shares.remove(0))
            } else {
                None
            };
            (idx, cs)
        })
        .collect();
    let mut shares = run_mpc_parties(expand_inputs, |_, (idx, cs), net| {
        qsag_cred::threshold_mldsa_shamir_expand_party(
            &dkg_cfg,
            party_ids[idx as usize],
            cs,
            &[0x10 + idx; 32],
            net,
        )
        .expect("17-party threshold_mldsa_shamir_expand_party")
    });
    assert!(shares.iter().all(|s| s.is_shamir()));

    let pack = shares[0].verification_pack().clone();
    let canonical_key_id = policy_signing_key_id(WitnessSuiteTag::MlDsa44, &pack.pk_bytes);
    assert_eq!(pack.policy_signing_key_id(), canonical_key_id);
    let upstream_pk =
        ml_dsa_44::PublicKey::try_from_bytes(pack.pk_bytes.as_slice().try_into().unwrap())
            .expect("upstream fips204::ml_dsa_44::PublicKey");

    let recipient = QsagAddress::from_pubkey_poseidon2(
        "qsag",
        WitnessSuiteTag::MlDsa44,
        KeyIdentityKind::SingleOrThreshold,
        b"shamir-17-recipient-vault",
    )
    .unwrap();
    let policy = TransactionPolicy {
        chain_id: 2026,
        pinned_suite: WitnessSuiteTag::MlDsa44,
        recipient_allowlist: vec![recipient.commitment_256],
        max_single_tx_amount: 10_000,
        velocity_window_cap: 10_000,
        valid_not_before_secs: 100,
        valid_not_after_secs: 900,
        forbid_initiator_self_approval: true,
        hardware_guardian_party: Some(170),
        quorum_tiers: vec![QuorumTierRule {
            max_amount_units: 10_000,
            min_approvers: 3,
            require_hardware_guardian: true,
        }],
    };
    // Provision dealerless BDOZ policy guards for initiator `10` + far-apart quorum `[50, 110, 170]`.
    let active_guard_committee = [10u16, 50, 110, 170];
    let mut guards = provision_dealerless_policy_guards(&active_guard_committee, [0x9B; 32], 2);
    let quorum = [50u16, 110, 170];
    let session_id = [0x9C; 32];
    let signing_ctx = b"qsag-shamir-17-policy-mldsa";

    let (mut intent, _) =
        TransactionIntent::builder(2026, WitnessSuiteTag::MlDsa44, recipient, 2_500)
            .window_id(0)
            .timestamp_secs(500)
            .initiator_and_approvers(10, &quorum)
            .bind_signing_payload(
                &SigningPayloadBinding {
                    key_id: canonical_key_id,
                    payload: b"shamir-17-transfer: 2500 units",
                    ctx: signing_ctx,
                    session_id,
                    policy_revision: 1,
                    quorum: &quorum,
                    authority_pk: [0xAB; 32],
                },
                &policy,
            )
            .unwrap();
    let signing_bytes = guards[0]
        .authenticate_initiated_intent(&policy, &mut intent)
        .unwrap();
    let intent_digest = intent.canonical_digest();

    let engine = PolicyEngine::new(&policy, 0);
    let release = engine
        .authorize_committed_barrier(&intent, session_id, 500, None, &mut guards[1..4], &accel)
        .expect("PolicyEngine authorize Shamir-17");
    let party_tokens = split_and_check_party_bindings(
        release,
        &canonical_key_id,
        &signing_bytes,
        signing_ctx,
        &quorum,
    );

    // Extract shares for `[50, 110, 170]` (indices `4, 10, 16`) in ascending order!
    let selected_indices = [4usize, 10, 16];
    let mut selected_shares: Vec<_> = shares
        .drain(..)
        .enumerate()
        .filter_map(|(i, s)| selected_indices.contains(&i).then_some(s))
        .collect();
    let mut burn_stores: Vec<_> = quorum
        .iter()
        .map(|&pid| {
            FsNonceBurnStore::create(
                tmp.path().join(format!("shamir-burn-{pid}")),
                canonical_key_id,
                [0x70 + (pid / 10) as u8; 32],
            )
            .unwrap()
        })
        .collect();

    let inputs: Vec<_> = selected_shares
        .iter_mut()
        .zip(burn_stores.iter_mut())
        .zip(party_tokens)
        .enumerate()
        .map(|(idx, ((sh, burn), tok))| (idx, sh, burn, tok))
        .collect();
    let outputs = run_mpc_parties(inputs, |_, (idx, sh, burn, tok), net| {
        threshold_sign_mldsa_party_policy_gated(
            sh,
            ThresholdPolicyGate {
                token: tok,
                expected_intent_digest: &intent_digest,
                quorum: &quorum,
            },
            &signing_bytes,
            signing_ctx,
            &[0xE0 + idx as u8; 32],
            burn as &mut dyn NonceBurnPersistence,
            net,
        )
        .expect("Shamir-17 threshold_sign_mldsa_party_policy_gated")
    });
    let sig_arr: [u8; ml_dsa_44::SIG_LEN] = outputs[0].signature.as_slice().try_into().unwrap();
    assert!(upstream_pk.verify(&signing_bytes, &sig_arr, signing_ctx));
}
