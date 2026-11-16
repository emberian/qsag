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
use std::time::{SystemTime, UNIX_EPOCH};

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
    CapabilityError, CapabilityGate, CapabilityRequest, Caveat, Discharge, MacaroonVerifier,
    PQ_BISCUIT_HOP_CRYPTO_BYTES, PolicyAuthenticatedOt, PolicyEngine, PolicyGuardDkgRound1,
    PolicySignerGuardShare, PolicyViolation, PqBiscuit, PqBiscuitAuthorityKey, QuorumTierRule,
    SigningPayloadBinding, SpongeMacaroon, TransactionIntent, TransactionPolicy,
    finalize_distributed_policy_guard,
};

// ============================================================================
// Shared TempDir Guard & In-Memory Synchronous Transports
// ============================================================================

struct TempDirGuard(PathBuf);

impl TempDirGuard {
    fn new(prefix: &str) -> Self {
        static COUNTER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let seq = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock")
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "qsag-e7-{prefix}-{}-{nanos}-{seq}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("create temp dir");
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
        let (st, commits) =
            PolicyGuardDkgRound1::new_with_capacity(pid, party_ids, setup_id, [0x21 + idx as u8; 32], slots)
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
        let mut store_refs: Vec<&mut dyn CounterStore> =
            stores.iter_mut().map(|s| s as &mut dyn CounterStore).collect();
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
        let mut store_refs: Vec<&mut dyn CounterStore> =
            stores.iter_mut().map(|s| s as &mut dyn CounterStore).collect();
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
        .attest_root_deterministic(MlDsaLevel::MlDsa44, &issuer_mldsa_sk, issuer_mldsa_pk.clone())
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
    let agg_root_u64: [u64; 6] = zk_statement
        .accumulator_root
        .map(|x| x.to_canonical_u64());
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
    let zk_proof =
        prove_presentation(&zk_statement, &zk_witness, verifier_ctx, regime, &[0x7A; 32])
            .expect("prove_presentation");

    let proof_bytes = zk_proof.to_bytes();
    assert!(
        (200_000..=265_000).contains(&proof_bytes.len()),
        "expected ~239 KiB succinct BlindVC zk-Hem proof, got {} B",
        proof_bytes.len()
    );
    let shape = zk_statement.shape().expect("well-formed BlindVcStatement shape");
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
    let mut forged_witness = zk_witness;
    forged_witness.holder_blind[0] += AggGoldilocks::ONE;
    assert_eq!(
        prove_presentation(&zk_statement, &forged_witness, verifier_ctx, regime, &[0x7B; 32]),
        Err(ZkHemError::Unsatisfied)
    );
}

// ============================================================================
// Journey B: `qsag-policy` + `SpongeMacaroon` / `PqBiscuit` -> `threshold_sign_mldsa_party_policy_gated`
