//! Distributed custodian prover over an actively secure outer MPC.
//!
//! Two backends implement the same prover:
//!
//! * `CoZkCustodianShare::new`: three custodians, replicated 2-of-3 sharing,
//!   at most one corrupted custodian, no preprocessing (`outer_mpc`).
//! * `CoZkCustodianShare::new_shamir` / `new_additive`: any `(t, n)` quorum,
//!   MAC-authenticated additive sharing that tolerates corruption of all but
//!   one quorum member, with witness-independent preprocessing
//!   (`threshold_mpc`, `threshold_prep`).
//!
//! Both assume confidential authenticated pairwise channels and independently
//! sampled private custodian entropy, and both verify every Boolean `AND`,
//! prime-field multiplication and conversion before any wire opening, view
//! commitment, public output, or challenged ZKBoo party view is reconstructed
//! (replicated: per flush `< 2^-244` Boolean, `< 2^-249` over the curve
//! fields and `< 2^-186` over Goldilocks `GF(p^3)`; authenticated: per check
//! `< 2^-126`). Abort is non-identifiable and unfair in both: one corrupt
//! custodian can force it. See `SECURITY.md` for exact scope.
#[cfg(test)]
use crate::batch_hash::{
    COZK_TREE_LEAVES, COZK_VIEW_MAGIC_V4, TURBOSHAKE_LEAF_SUFFIX, TURBOSHAKE_ROOT_SUFFIX,
    TURBOSHAKE_VIEW_MIDSTATE, cozk_product_leaf_range,
};
pub use crate::outer_mpc::{Envelope, Error, Transport};
use crate::secret::{Secret, SecretVec, Wipe};
#[cfg(any(feature = "std", test))]
use crate::threshold_mpc::QuorumKeyEscrow;
use crate::{
    batch_hash::COZK_VIEW_MAGIC_V5,
    bls12_381::{
        self, BlsG1Point, BlsMigrationRequest, BlsMigrationStatement, BlsValidatorCommitment,
    },
    circuit::{Circuit, Domain, Op, Value, ZERO},
    outer_mpc::{self, Core, Engine, FieldWord, Gadgets, ShareBit, Sponge, Word},
    pallas::{self, PallasMigrationRequest, PallasMigrationStatement, PallasPoint},
    threshold_mpc::{MacKeyShare, SpdzEngine, ThresholdConfig},
    zk_engine::{
        self, MIT_REPETITIONS, MigrationStatement, MigrationZkProof, OpenedRepetitionView,
        PartyView,
    },
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    keccak::{InterleavedTranscript, commit_mpc_broadcast, cshake256_framed_32},
};

/// General-quorum custody: the active quorum, one channel key per other
/// quorum member (in quorum order) and this custodian's MAC key shares.
struct QuorumCustody {
    config: ThresholdConfig,
    is_shamir: bool,
    peer_keys: Vec<[u8; 32]>,
    mac_keys: MacKeyShare,
}
impl Drop for QuorumCustody {
    fn drop(&mut self) {
        for k in &mut self.peer_keys {
            ct_zeroize_bytes(k);
        }
    }
}

enum CeremonyEngine<T> {
    Replicated(alloc::boxed::Box<Engine<T>>),
    Quorum(alloc::boxed::Box<SpdzEngine<T>>),
}

/// One-shot local custody material. Supply the XOR share of the *normalized
/// spending scalar*, encoded little endian, not a derivation seed. Session
/// identifiers must be unique; entropy must be fresh and independent at every
/// custodian. No combined witness or other custodian's entropy enters the
/// online prover, and no constructor takes a dealer: the general-quorum
/// constructors take this custodian's MAC key shares, which come out of the
/// same preprocessing ceremony as the material its transport serves.
pub struct CoZkCustodianShare {
    party: usize,
    session: [u8; 32],
    witness: [u8; 32],
    rerandomizer: Option<[u8; 32]>,
    entropy: [u8; 32],
    /// Replicated custody: keys shared with `[previous, next]`.
    channel_keys: [[u8; 32]; 2],
    quorum: Option<QuorumCustody>,
}
impl Drop for CoZkCustodianShare {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.witness);
        if let Some(alpha) = &mut self.rerandomizer {
            ct_zeroize_bytes(alpha);
        }
        ct_zeroize_bytes(&mut self.entropy);
        for k in &mut self.channel_keys {
            ct_zeroize_bytes(k);
        }
    }
}
impl CoZkCustodianShare {
    /// Replicated 2-of-3 custody for parties `0..3`.
    pub fn new(
        party: usize,
        session: [u8; 32],
        witness: [u8; 32],
        entropy: [u8; 32],
        channel_keys: [[u8; 32]; 2],
    ) -> Result<Self, Error> {
        let share = Self {
            party,
            session,
            witness,
            rerandomizer: None,
            entropy,
            channel_keys,
            quorum: None,
        };
        if party >= 3 {
            return Err(Error::InvalidConfiguration);
        }
        Ok(share)
    }

    /// General `(t,n)` bytewise Shamir custody over the Wiedemann tower `GF(256)`.
    /// The selected, sorted quorum must contain at least `t` members. `peer_keys`
    /// follow quorum order, omitting self. All members use the same session and
    /// configuration, independent entropy, and MAC key shares and preprocessing
    /// from one ceremony (`threshold_prep`). The transport must implement
    /// `exchange_many` and the `take_*` preprocessing methods.
    pub fn new_shamir(
        party: usize,
        config: ThresholdConfig,
        session: [u8; 32],
        witness: [u8; 32],
        entropy: [u8; 32],
        peer_keys: Vec<[u8; 32]>,
        mac_keys: MacKeyShare,
    ) -> Result<Self, Error> {
        let mut share = Self::quorum_contribution(
            party, config, true, session, witness, entropy, peer_keys, mac_keys,
        )?;
        let contribution = share
            .quorum
            .as_ref()
            .unwrap()
            .config
            .shamir_contribution(party, &share.witness)?;
        ct_zeroize_bytes(&mut share.witness);
        share.witness = contribution;
        Ok(share)
    }

    /// General n-of-n XOR custody. Every roster member participates. The input
    /// is a share of normalized scalar bytes, not a scalar-field additive share.
    /// Requirements are those of `new_shamir`.
    pub fn new_additive(
        party: usize,
        parties: usize,
        session: [u8; 32],
        witness: [u8; 32],
        entropy: [u8; 32],
        peer_keys: Vec<[u8; 32]>,
        mac_keys: MacKeyShare,
    ) -> Result<Self, Error> {
        let config = if (2..=64).contains(&parties) {
            ThresholdConfig::new(parties, parties, (0..parties).collect())
        } else {
            Err(Error::InvalidConfiguration)
        };
        match config {
            Ok(config) => Self::quorum_contribution(
                party, config, false, session, witness, entropy, peer_keys, mac_keys,
            ),
            Err(error) => {
                let mut secrets = (witness, entropy, peer_keys);
                secrets.secret_wipe();
                Err(error)
            }
        }
    }

    /// Attach this custodian's share of the 32-byte little-endian RedPallas action
    /// rerandomizer `alpha` (`0 <= alpha < q_pallas`) for proving Zcash Orchard
    /// [`pallas::PallasCommitmentKind::OrchardRedPallasRk`] ownership without
    /// reconstructing `ask` or `alpha`.
    ///
    /// For [`Self::new_shamir`] shares, `alpha_share` is scaled by this party's
    /// `TowerGf256` Lagrange weight at zero; for [`Self::new`] and
    /// [`Self::new_additive`], `alpha_share` is this party's XOR share directly.
    pub fn with_rerandomizer(mut self, mut alpha_share: [u8; 32]) -> Result<Self, Error> {
        if let Some(custody) = &self.quorum
            && custody.is_shamir
        {
            let contribution = match custody.config.shamir_contribution(self.party, &alpha_share) {
                Ok(c) => c,
                Err(err) => {
                    ct_zeroize_bytes(&mut alpha_share);
                    return Err(err);
                }
            };
            ct_zeroize_bytes(&mut alpha_share);
            alpha_share = contribution;
        }
        if let Some(prev) = &mut self.rerandomizer {
            ct_zeroize_bytes(prev);
        }
        self.rerandomizer = Some(alpha_share);
        Ok(self)
    }

    #[allow(clippy::too_many_arguments)]
    fn quorum_contribution(
        party: usize,
        config: ThresholdConfig,
        is_shamir: bool,
        session: [u8; 32],
        witness: [u8; 32],
        entropy: [u8; 32],
        peer_keys: Vec<[u8; 32]>,
        mac_keys: MacKeyShare,
    ) -> Result<Self, Error> {
        let share = Self {
            party,
            session,
            witness,
            rerandomizer: None,
            entropy,
            channel_keys: [[0; 32]; 2],
            quorum: Some(QuorumCustody {
                config,
                is_shamir,
                peer_keys,
                mac_keys,
            }),
        };
        let custody = share.quorum.as_ref().unwrap();
        if !custody.config.quorum().contains(&party)
            || custody.peer_keys.len() != custody.config.quorum().len() - 1
        {
            return Err(Error::InvalidConfiguration);
        }
        Ok(share)
    }

    fn start_ceremony<T: Transport>(
        &mut self,
        #[allow(unused_mut)] mut transport: T,
        #[cfg_attr(not(test), allow(unused_variables))] statement_bytes: &[u8],
    ) -> Result<(CeremonyEngine<T>, Vec<T>), Error> {
        #[cfg(test)]
        if self.quorum.is_none() {
            transport.audit_private_transcript_bytes(
                self.party,
                &self.session,
                &self.witness,
                &self.entropy,
                &self.channel_keys,
                statement_bytes,
            );
        }
        #[allow(unused_mut)]
        let mut children = Vec::new();
        #[cfg(any(feature = "std", test))]
        {
            for batch in 0..MIT_REPETITIONS.div_ceil(64) {
                if let Some(child) = transport.fork(batch) {
                    children.push(child);
                }
            }
            if !children.is_empty() && children.len() != MIT_REPETITIONS.div_ceil(64) {
                return Err(Error::InvalidConfiguration);
            }
        }
        match &mut self.quorum {
            Some(custody) => {
                // Move `mac_keys` out of `CoZkCustodianShare` so `SpdzEngine` /
                // `QuorumKeyEscrow` owns the sole live copy and wipes all copies on abort.
                let mac_keys = core::mem::replace(&mut custody.mac_keys, MacKeyShare::wiped());
                let mut e = SpdzEngine::new(
                    self.party,
                    self.session,
                    custody.config.clone(),
                    custody.peer_keys.clone(),
                    mac_keys,
                    transport,
                )?;
                e.mix_entropy(&self.entropy);
                Ok((CeremonyEngine::Quorum(alloc::boxed::Box::new(e)), children))
            }
            None => {
                let mut e = Engine::new(self.party, self.session, self.channel_keys, transport)?;
                e.mix_entropy(&self.entropy);
                Ok((
                    CeremonyEngine::Replicated(alloc::boxed::Box::new(e)),
                    children,
                ))
            }
        }
    }

    fn expand_witness_lanes(&self, expect_rerandomizer: bool) -> Result<SecretVec<u64>, Error> {
        if self.rerandomizer.is_some() != expect_rerandomizer {
            return Err(Error::InvalidConfiguration);
        }
        let mut own = SecretVec::with_capacity(if expect_rerandomizer { 512 } else { 256 });
        for &b in &self.witness {
            for i in 0..8 {
                own.push(if (b >> i) & 1 != 0 { u64::MAX } else { 0 });
            }
        }
        if let Some(alpha) = &self.rerandomizer {
            for &b in alpha {
                for i in 0..8 {
                    own.push(if (b >> i) & 1 != 0 { u64::MAX } else { 0 });
                }
            }
        }
        Ok(own)
    }

    /// Consumes the ceremony. A transport or verification error consumes all state as well.
    /// The returned proof has passed the unchanged single-prover verifier.
    ///
    /// Ceremony state cannot be reused, including after a failed call:
    /// ```compile_fail
    /// use qsag_migrate::{CoZkCustodianShare, MigrationStatement};
    /// use qsag_migrate::co_zk_mpc::Transport;
    /// fn reuse<T: Transport>(state: CoZkCustodianShare, statement: &MigrationStatement, a: T, b: T) {
    ///     let _ = state.prove(statement, a);
    ///     let _ = state.prove(statement, b);
    /// }
    /// ```
    pub fn prove<T: Transport>(
        self,
        statement: &MigrationStatement,
        transport: T,
    ) -> Result<MigrationZkProof, Error> {
        self.prove_with_backend(statement, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Use the selected backend for legacy commitment verification. V4/V5
    /// commitments use the versioned TurboSHAKE tree implementation. V5 opens
    /// only seed-masked views for hashing, never an unchallenged plaintext view.
    pub fn prove_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        mut self,
        statement: &MigrationStatement,
        transport: T,
        accel: &B,
    ) -> Result<MigrationZkProof, Error> {
        let own = self.expand_witness_lanes(false)?;
        let statement_bytes = statement.to_transcript_bytes();
        let circuit = crate::ownership::build(statement, &[0; 32]);
        let (engine, children) = self.start_ceremony(transport, &statement_bytes)?;
        match engine {
            CeremonyEngine::Replicated(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| zk_engine::transcript(statement, root),
                |proof| {
                    zk_engine::verify_migration_proof_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
            CeremonyEngine::Quorum(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| zk_engine::transcript(statement, root),
                |proof| {
                    zk_engine::verify_migration_proof_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
        }
    }

    /// Prove Zcash Orchard `Pallas` / `RedPallas` (`OrchardSpendAuthKey` `ak` or
    /// `OrchardRedPallasRk` `rk`) ownership across the custodian quorum without
    /// reconstructing `ask` or `alpha`.
    pub fn prove_pallas<T: Transport>(
        self,
        statement: &PallasMigrationStatement,
        transport: T,
    ) -> Result<MigrationZkProof, Error> {
        self.prove_pallas_with_backend(statement, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Backend-accelerated [`Self::prove_pallas`].
    pub fn prove_pallas_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        mut self,
        statement: &PallasMigrationStatement,
        transport: T,
        accel: &B,
    ) -> Result<MigrationZkProof, Error> {
        let is_rk = statement.commitment.is_rerandomized();
        let own = self.expand_witness_lanes(is_rk)?;
        let pub_pt = PallasPoint::from_nonidentity_bytes(statement.commitment.compressed_bytes())
            .ok_or(Error::InvalidConfiguration)?;
        let expected_affine = pub_pt.to_affine().ok_or(Error::InvalidConfiguration)?;
        let statement_bytes = statement.to_transcript_bytes();
        let circuit =
            pallas::build_pallas_ownership_circuit(statement, expected_affine, &[0; 32], &[0; 32])
                .0;
        let (engine, children) = self.start_ceremony(transport, &statement_bytes)?;
        match engine {
            CeremonyEngine::Replicated(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| pallas::pallas_transcript(statement, root),
                |proof| {
                    pallas::verify_pallas_migration_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
            CeremonyEngine::Quorum(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| pallas::pallas_transcript(statement, root),
                |proof| {
                    pallas::verify_pallas_migration_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
        }
    }

    /// Jointly derive the public Poseidon2 `migration_nullifier` inside active MPC
    /// (after verifying in-MPC that the shared `(ask, alpha)` matches `request.commitment`
    /// so zero bits open on a mismatched witness!) and prove the full 438-repetition
    /// Zcash Orchard `Pallas` / `RedPallas` ZKBoo proof without ever reconstructing
    /// `ask` or `alpha`.
    pub fn prove_pallas_request<T: Transport>(
        self,
        request: PallasMigrationRequest,
        transport: T,
    ) -> Result<(PallasMigrationStatement, MigrationZkProof), Error> {
        self.prove_pallas_request_with_backend(request, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Backend-accelerated [`Self::prove_pallas_request`].
    pub fn prove_pallas_request_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        mut self,
        request: PallasMigrationRequest,
        transport: T,
        accel: &B,
    ) -> Result<(PallasMigrationStatement, MigrationZkProof), Error> {
        let is_rk = request.commitment.is_rerandomized();
        let own = self.expand_witness_lanes(is_rk)?;
        let pub_pt = PallasPoint::from_nonidentity_bytes(request.commitment.compressed_bytes())
            .ok_or(Error::InvalidConfiguration)?;
        let expected_affine = pub_pt.to_affine().ok_or(Error::InvalidConfiguration)?;
        let mut statement = PallasMigrationStatement {
            commitment: request.commitment,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: [0; 4],
        };
        let req_bytes = statement.to_transcript_bytes();
        let pre_circuit =
            pallas::build_pallas_ownership_circuit(&statement, expected_affine, &[0; 32], &[0; 32])
                .0;
        let (engine, children) = self.start_ceremony(transport, &req_bytes)?;
        match engine {
            CeremonyEngine::Replicated(mut e) => {
                statement.migration_nullifier =
                    derive_nullifier_in_mpc(&mut *e, &pre_circuit, &own, &req_bytes)?;
                let stmt_bytes = statement.to_transcript_bytes();
                let circuit = pallas::build_pallas_ownership_circuit(
                    &statement,
                    expected_affine,
                    &[0; 32],
                    &[0; 32],
                )
                .0;
                let proof = self.run_circuit(
                    &mut *e,
                    children,
                    &stmt_bytes,
                    &circuit,
                    &own,
                    |root| pallas::pallas_transcript(&statement, root),
                    |proof| {
                        pallas::verify_pallas_migration_with_backend(
                            &statement,
                            proof,
                            &statement.migration_domain,
                            statement.epoch_anchor,
                            accel,
                        )
                        .map_err(|_| Error::InvalidProof)
                    },
                )?;
                Ok((statement, proof))
            }
            CeremonyEngine::Quorum(mut e) => {
                statement.migration_nullifier =
                    derive_nullifier_in_mpc(&mut *e, &pre_circuit, &own, &req_bytes)?;
                let stmt_bytes = statement.to_transcript_bytes();
                let circuit = pallas::build_pallas_ownership_circuit(
                    &statement,
                    expected_affine,
                    &[0; 32],
                    &[0; 32],
                )
                .0;
                let proof = self.run_circuit(
                    &mut *e,
                    children,
                    &stmt_bytes,
                    &circuit,
                    &own,
                    |root| pallas::pallas_transcript(&statement, root),
                    |proof| {
                        pallas::verify_pallas_migration_with_backend(
                            &statement,
                            proof,
                            &statement.migration_domain,
                            statement.epoch_anchor,
                            accel,
                        )
                        .map_err(|_| Error::InvalidProof)
                    },
                )?;
                Ok((statement, proof))
            }
        }
    }

    /// Prove Ethereum Beacon validator `BLS12-381` (`BeaconValidatorPubkey` or
    /// `UnrevealedBls0x00Credential`) ownership across the custodian quorum without
    /// reconstructing `sk` (or `pk_48` in `UnrevealedBls0x00Credential` mode).
    pub fn prove_bls<T: Transport>(
        self,
        statement: &BlsMigrationStatement,
        transport: T,
    ) -> Result<MigrationZkProof, Error> {
        self.prove_bls_with_backend(statement, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Backend-accelerated [`Self::prove_bls`].
    pub fn prove_bls_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        mut self,
        statement: &BlsMigrationStatement,
        transport: T,
        accel: &B,
    ) -> Result<MigrationZkProof, Error> {
        let own = self.expand_witness_lanes(false)?;
        if !statement.credentials_consistent() {
            return Err(Error::InvalidConfiguration);
        }
        let public_affine = match &statement.commitment {
            BlsValidatorCommitment::BeaconValidatorPubkey(pk_48) => {
                let pt = BlsG1Point::from_validator_pubkey_48(pk_48)
                    .ok_or(Error::InvalidConfiguration)?;
                Some(pt.to_affine().ok_or(Error::InvalidConfiguration)?)
            }
            BlsValidatorCommitment::UnrevealedBls0x00Credential(_) => None,
        };
        let statement_bytes = statement.to_transcript_bytes();
        let circuit = bls12_381::build_bls_ownership_circuit(statement, public_affine, &[0; 32]).0;
        let (engine, children) = self.start_ceremony(transport, &statement_bytes)?;
        match engine {
            CeremonyEngine::Replicated(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| bls12_381::bls_transcript(statement, root),
                |proof| {
                    bls12_381::verify_bls_migration_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
            CeremonyEngine::Quorum(mut e) => self.run_circuit(
                &mut *e,
                children,
                &statement_bytes,
                &circuit,
                &own,
                |root| bls12_381::bls_transcript(statement, root),
                |proof| {
                    bls12_381::verify_bls_migration_with_backend(
                        statement,
                        proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                        accel,
                    )
                    .map_err(|_| Error::InvalidProof)
                },
            ),
        }
    }

    /// Jointly derive the public Poseidon2 `migration_nullifier` inside active MPC
    /// (after verifying in-MPC that the shared `sk` matches `request.commitment`,
    /// including SHA-256 of the unrevealed compressed `G_1` key in `0x00` mode!) and
    /// prove the full 438-repetition Ethereum Beacon `BLS12-381` ZKBoo proof without
    /// ever reconstructing `sk` or `pk_48`.
    pub fn prove_bls_request<T: Transport>(
        self,
        request: BlsMigrationRequest,
        transport: T,
    ) -> Result<(BlsMigrationStatement, MigrationZkProof), Error> {
        self.prove_bls_request_with_backend(request, transport, &qsag_accel::CpuReferenceBackend)
    }

    /// Backend-accelerated [`Self::prove_bls_request`].
    pub fn prove_bls_request_with_backend<T: Transport, B: qsag_accel::AcceleratorBackend>(
        mut self,
        request: BlsMigrationRequest,
        transport: T,
        accel: &B,
    ) -> Result<(BlsMigrationStatement, MigrationZkProof), Error> {
        let own = self.expand_witness_lanes(false)?;
        let public_affine = match &request.commitment {
            BlsValidatorCommitment::BeaconValidatorPubkey(pk_48) => {
                let pt = BlsG1Point::from_validator_pubkey_48(pk_48)
                    .ok_or(Error::InvalidConfiguration)?;
                Some(pt.to_affine().ok_or(Error::InvalidConfiguration)?)
            }
            BlsValidatorCommitment::UnrevealedBls0x00Credential(_) => None,
        };
        let mut statement = BlsMigrationStatement {
            commitment: request.commitment,
            validator_index: request.validator_index,
            withdrawal_credentials: request.withdrawal_credentials,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: [0; 4],
        };
        if !statement.credentials_consistent() {
            return Err(Error::InvalidConfiguration);
        }
        let req_bytes = statement.to_transcript_bytes();
        let pre_circuit =
            bls12_381::build_bls_ownership_circuit(&statement, public_affine, &[0; 32]).0;
        let (engine, children) = self.start_ceremony(transport, &req_bytes)?;
        match engine {
            CeremonyEngine::Replicated(mut e) => {
                statement.migration_nullifier =
                    derive_nullifier_in_mpc(&mut *e, &pre_circuit, &own, &req_bytes)?;
                let stmt_bytes = statement.to_transcript_bytes();
                let circuit =
                    bls12_381::build_bls_ownership_circuit(&statement, public_affine, &[0; 32]).0;
                let proof = self.run_circuit(
                    &mut *e,
                    children,
                    &stmt_bytes,
                    &circuit,
                    &own,
                    |root| bls12_381::bls_transcript(&statement, root),
                    |proof| {
                        bls12_381::verify_bls_migration_with_backend(
                            &statement,
                            proof,
                            &statement.migration_domain,
                            statement.epoch_anchor,
                            accel,
                        )
                        .map_err(|_| Error::InvalidProof)
                    },
                )?;
                Ok((statement, proof))
            }
            CeremonyEngine::Quorum(mut e) => {
                statement.migration_nullifier =
                    derive_nullifier_in_mpc(&mut *e, &pre_circuit, &own, &req_bytes)?;
                let stmt_bytes = statement.to_transcript_bytes();
                let circuit =
                    bls12_381::build_bls_ownership_circuit(&statement, public_affine, &[0; 32]).0;
                let proof = self.run_circuit(
                    &mut *e,
                    children,
                    &stmt_bytes,
                    &circuit,
                    &own,
                    |root| bls12_381::bls_transcript(&statement, root),
                    |proof| {
                        bls12_381::verify_bls_migration_with_backend(
                            &statement,
                            proof,
                            &statement.migration_domain,
                            statement.epoch_anchor,
                            accel,
                        )
                        .map_err(|_| Error::InvalidProof)
                    },
                )?;
                Ok((statement, proof))
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run_circuit<E: ProverEngine>(
        &self,
        e: &mut E,
        children: Vec<E::Transport>,
        statement_bytes: &[u8],
        circuit: &Circuit,
        own_witness: &[u64],
        transcript_fn: impl FnOnce(&[u8; 32]) -> InterleavedTranscript,
        verify_fn: impl FnOnce(&MigrationZkProof) -> Result<(), Error>,
    ) -> Result<MigrationZkProof, Error> {
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.STATEMENT.V1",
            &[
                &COZK_VIEW_MAGIC_V5,
                statement_bytes,
                &(children.len() as u64).to_le_bytes(),
            ],
        ))?;

        // Both replicated witness components this custodian holds are wiped on
        // every exit path, as are its local sub-seeds and commitment salts.
        let witness = e.share_uniform_lanes(own_witness)?;
        let witness: &[E::Bit] = &witness;

        let (quorum_pos, quorum_m) = e.quorum_position();
        let num_batches = MIT_REPETITIONS.div_ceil(64);
        let mut local_batches = Vec::with_capacity(num_batches);
        let mut own_commits_flat = Vec::with_capacity(MIT_REPETITIONS * 3 * 64);
        for batch in 0..num_batches {
            let mut subseeds = Secret([[[0u8; 32]; 64]; 3]);
            let mut salts = Secret([[[0u8; 32]; 64]; 3]);
            for (head, (head_seeds, head_salts)) in
                subseeds.iter_mut().zip(salts.iter_mut()).enumerate()
            {
                for lane in 0..64 {
                    let rep = batch * 64 + lane;
                    head_seeds[lane] = cshake256_framed_32(
                        b"QSAG.OUTER.SEED.V1",
                        &[
                            &self.entropy,
                            &self.session,
                            statement_bytes,
                            &(rep as u64).to_le_bytes(),
                            &[head as u8, quorum_pos as u8, 0],
                        ],
                    );
                    head_salts[lane] = cshake256_framed_32(
                        b"QSAG.OUTER.SEED.V1",
                        &[
                            &self.entropy,
                            &self.session,
                            statement_bytes,
                            &(rep as u64).to_le_bytes(),
                            &[head as u8, quorum_pos as u8, 1],
                        ],
                    );
                }
            }
            let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
            for lane in 0..count {
                let rep = batch * 64 + lane;
                for head in 0..3 {
                    let com = commit_mpc_broadcast(
                        &self.session,
                        rep as u32,
                        (quorum_pos * 3 + head) as u16,
                        &subseeds[head][lane],
                        &salts[head][lane],
                    );
                    own_commits_flat.extend_from_slice(&com);
                    own_commits_flat.extend_from_slice(&crate::batch_hash::cozk_seed_commit(
                        rep,
                        head,
                        quorum_pos,
                        &subseeds[head][lane],
                    ));
                }
            }
            local_batches.push(LocalBatchSeeds { subseeds, salts });
        }

        // Phase 0: Commit-before-execute binding of every custodian's per-(rep, head)
        // sub-seeds before any tape share, witness conversion, or circuit gate executes.
        let peer_commits = e.broadcast_bytes(&own_commits_flat)?;
        if peer_commits.len() != quorum_m
            || peer_commits
                .iter()
                .any(|c| c.len() != MIT_REPETITIONS * 3 * 64)
        {
            e.poison();
            return Err(Error::InvalidConfiguration);
        }
        {
            let mut commit_frames: Vec<&[u8]> = Vec::with_capacity(1 + quorum_m);
            commit_frames.push(statement_bytes);
            for c in &peer_commits {
                commit_frames.push(c.as_slice());
            }
            e.agree(cshake256_framed_32(
                b"QSAG.OUTER.STATEMENT.V1",
                &commit_frames,
            ))?;
        }

        // Phase 1: Evaluate all batches using locally expanded sub-seed tapes (0 in-MPC
        // SHAKE permutations!), mask the views under independent custodian streams,
        // and run mandatory active multiplication checks on EVERY batch BEFORE opening.
        let mut computed_batches =
            compute_batches(e, circuit, witness, &local_batches, children, &self.entropy)?;

        // Cross-batch barrier: all custodians confirm every batch passed active
        // multiplication verification before ANY view commitment or output opens.
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.PRECOMMIT.V1",
            &[statement_bytes],
        ))?;

        // Phase 2: Open view commitments and public outputs for each batch.
        let mut public = Vec::with_capacity(MIT_REPETITIONS);
        for (batch, item) in computed_batches.iter_mut().enumerate() {
            let opening_engine = item.engine.as_mut().unwrap_or(&mut *e);
            let rounds = open_batch_public_rounds(
                opening_engine,
                batch,
                &item.masked_views,
                &item.views,
                &peer_commits,
            )?;
            public.extend(rounds);
        }

        let roots: Vec<_> = public
            .iter()
            .enumerate()
            .flat_map(|(rep, r)| {
                zk_engine::rep_root_cozk_v5(
                    rep,
                    &r.commits,
                    r.outputs.each_ref().map(Vec::as_slice),
                )
            })
            .collect();
        let root = cshake256_framed_32(b"QSAG.MIGRATE.ROOT.V3", &[&roots]);

        // Ceremony-wide Fiat-Shamir freeze precedes every challenged ZKBoo view opening.
        e.agree(cshake256_framed_32(
            b"QSAG.OUTER.FREEZE.V1",
            &[statement_bytes, &root],
        ))?;

        let mut t = transcript_fn(&root);
        let challenges = zk_engine::challenges(&mut t);

        // Phase 3a: Reveal salted sub-seeds ONLY for the two challenged heads of each
        // repetition (`(e_r, (e_r + 1) % 3)`); the hidden third head's sub-seeds and salts
        // are NEVER transmitted. Verify every peer's Phase-0 commitment in constant time.
        let mut own_decommits = Secret(Vec::with_capacity(MIT_REPETITIONS * 2 * 64));
        for (rep, &ch_byte) in challenges.iter().enumerate() {
            let batch = rep / 64;
            let lane = rep % 64;
            let ch = ch_byte as usize;
            for head in [ch, (ch + 1) % 3] {
                own_decommits.extend_from_slice(&local_batches[batch].subseeds[head][lane]);
                own_decommits.extend_from_slice(&local_batches[batch].salts[head][lane]);
            }
        }
        drop(local_batches);

        #[cfg(test)]
        e.on_public_or_view_open();
        let mut peer_decommits = Secret(e.broadcast_bytes(&own_decommits)?);
        ct_zeroize_bytes(&mut own_decommits);
        if peer_decommits.len() != quorum_m
            || peer_decommits
                .iter()
                .any(|d| d.len() != MIT_REPETITIONS * 2 * 64)
        {
            for d in peer_decommits.iter_mut() {
                ct_zeroize_bytes(d);
            }
            e.poison();
            return Err(Error::InvalidConfiguration);
        }
        for (pos, decommit_buf) in peer_decommits.iter().enumerate() {
            let commit_buf = &peer_commits[pos];
            let mut all_ok = u64::MAX;
            for (rep, &ch_byte) in challenges.iter().enumerate() {
                let ch = ch_byte as usize;
                for (pair_idx, head) in [ch, (ch + 1) % 3].into_iter().enumerate() {
                    let dec_off = (rep * 2 + pair_idx) * 64;
                    let subseed: &[u8; 32] =
                        decommit_buf[dec_off..dec_off + 32].try_into().unwrap();
                    let salt: &[u8; 32] =
                        decommit_buf[dec_off + 32..dec_off + 64].try_into().unwrap();
                    let actual = commit_mpc_broadcast(
                        &self.session,
                        rep as u32,
                        (pos * 3 + head) as u16,
                        subseed,
                        salt,
                    );
                    let com_off = (rep * 3 + head) * 64;
                    let expected: &[u8; 32] = commit_buf[com_off..com_off + 32].try_into().unwrap();
                    all_ok &= ct_eq_bytes_mask(&actual, expected);
                    let expected_seed: &[u8; 32] =
                        commit_buf[com_off + 32..com_off + 64].try_into().unwrap();
                    all_ok &= ct_eq_bytes_mask(
                        &crate::batch_hash::cozk_seed_commit(rep, head, pos, subseed),
                        expected_seed,
                    );
                }
            }
            if all_ok != u64::MAX {
                for d in peer_decommits.iter_mut() {
                    ct_zeroize_bytes(d);
                }
                e.poison();
                return Err(Error::Disagreement(pos));
            }
        }

        // Phase 3b: Open challenged ZKBoo view wires (`pair[0]` omits `products` via KKW
        // deterministic replay reconstruction; `head_inputs` exists only on head 2) and
        // verify consistency between MPC-committed sub-seed bits and Phase-0 decommitments.
        let mut repetitions = Vec::with_capacity(MIT_REPETITIONS);

        #[cfg(test)]
        let audit_inputs: Vec<[Word<E::Bit>; 3]> = computed_batches
            .iter()
            .map(|batch| batch.audit_witness_inputs.clone())
            .collect();

        for (batch, mut result) in computed_batches.into_iter().enumerate() {
            let opening_engine = result.engine.as_mut().unwrap_or(&mut *e);
            let views = &result.views;
            let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
            let mut opened: Vec<Vec<PartyView>> = Vec::with_capacity(3);
            for (head, view) in views.iter().enumerate() {
                let mut mask_both = 0u64;
                let mut mask_second = 0u64;
                for lane in 0..count {
                    let ch = challenges[batch * 64 + lane] as usize;
                    if (ch + 2) % 3 != head {
                        mask_both |= 1u64 << lane;
                    }
                    if (ch + 1) % 3 == head {
                        mask_second |= 1u64 << lane;
                    }
                }
                #[cfg(test)]
                opening_engine.on_public_or_view_open();
                let clear_meta = opening_engine.open_lanes(&view.subseeds, mask_both)?;
                let clear_inputs = open_typed_values(opening_engine, &view.inputs, mask_both)?;
                let clear_prods = open_typed_values(opening_engine, &view.products, mask_second)?;

                let mut subseed_match_mask = u64::MAX;
                let mut head_views = Vec::with_capacity(count);
                for lane in 0..count {
                    let rep = batch * 64 + lane;
                    let ch = challenges[rep] as usize;
                    if (ch + 2) % 3 == head {
                        head_views.push(PartyView {
                            seed: [0u8; 32],
                            inputs: Vec::new(),
                            products: Vec::new(),
                            outputs: Vec::new(),
                        });
                        continue;
                    }
                    let pair_idx = usize::from(head != ch);
                    let mut meta_bytes = outer_mpc::lane_bytes(&clear_meta, lane);
                    let mut decommitted_subseeds = Vec::with_capacity(quorum_m);
                    for (pos, decommit_buf) in peer_decommits.iter().enumerate() {
                        let dec_off = (rep * 2 + pair_idx) * 64;
                        let mut s = [0u8; 32];
                        s.copy_from_slice(&decommit_buf[dec_off..dec_off + 32]);
                        let mpc_slice: &[u8; 32] =
                            meta_bytes[pos * 32..(pos + 1) * 32].try_into().unwrap();
                        subseed_match_mask &= ct_eq_bytes_mask(mpc_slice, &s);
                        decommitted_subseeds.push(s);
                    }
                    let head_in_slice = &clear_inputs[lane];
                    let (seed, inputs) =
                        zk_engine::encode_cozk_v5_inputs(&decommitted_subseeds, head_in_slice);
                    ct_zeroize_bytes(&mut meta_bytes);
                    for s in &mut decommitted_subseeds {
                        ct_zeroize_bytes(s);
                    }
                    let products = if pair_idx == 1 {
                        clear_prods[lane].clone()
                    } else {
                        Vec::new()
                    };
                    head_views.push(PartyView {
                        seed,
                        inputs,
                        products,
                        outputs: public[rep].outputs[head].clone(),
                    });
                }
                if subseed_match_mask != u64::MAX {
                    for d in peer_decommits.iter_mut() {
                        ct_zeroize_bytes(d);
                    }
                    opening_engine.poison();
                    e.poison();
                    return Err(Error::InvalidProof);
                }
                opened.push(head_views);
            }
            for (lane, &ch_byte) in challenges[batch * 64..batch * 64 + count]
                .iter()
                .enumerate()
            {
                let rep = batch * 64 + lane;
                let challenge = ch_byte as usize;
                let hidden = (challenge + 2) % 3;
                repetitions.push(OpenedRepetitionView {
                    opened_e: ch_byte,
                    pair: [
                        opened[challenge][lane].clone(),
                        opened[(challenge + 1) % 3][lane].clone(),
                    ],
                    hidden_party_commit: public[rep].commits[hidden],
                    hidden_outputs: public[rep].outputs[hidden].clone(),
                });
            }
        }
        for d in peer_decommits.iter_mut() {
            ct_zeroize_bytes(d);
        }

        let proof = MigrationZkProof {
            views_merkle_root: root,
            repetitions,
        };
        verify_fn(&proof)?;
        #[cfg(test)]
        std::eprintln!(
            "BENCH cozk repetitions={} proof_bytes={}",
            proof.repetitions.len(),
            crate::benchmarks::proof_bytes(&proof)
        );
        e.agree(cshake256_framed_32(b"QSAG.OUTER.COMPLETE.V1", &[&root]))?;
        #[cfg(test)]
        e.audit(self, witness, &audit_inputs, &proof);
        Ok(proof)
    }
}

/// What the distributed prover needs from a backend besides [`Core`]: how to
/// start the engine of one repetition batch on its own transport stream.
pub(crate) trait ProverEngine: Core + Sized + Send {
    type Transport: Transport;
    /// Custody secrets a batch engine starts from; erased on drop.
    #[cfg(any(feature = "std", test))]
    type BatchSeed: Send + Sync;
    #[cfg(any(feature = "std", test))]
    fn batch_seed(
        &mut self,
        entropy: &[u8; 32],
        cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> Self::BatchSeed;
    #[cfg(any(feature = "std", test))]
    fn poison_batch_seed(_seed: &Self::BatchSeed) {}
    /// Engine for `batch`, bound to a batch-specific session and entropy.
    /// It aborts at its next exchange once `cancelled` is set.
    #[cfg(any(feature = "std", test))]
    fn for_batch(
        seed: &Self::BatchSeed,
        batch: usize,
        transport: Self::Transport,
        cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> Result<Self, Error>;
    /// Called once a batch has passed all checks; the engine stays live for
    /// the opening rounds.
    #[cfg(any(feature = "std", test))]
    fn finish_batch(&mut self);
    #[cfg(any(feature = "std", test))]
    fn max_parallel_batches(&self) -> usize;
    #[cfg(test)]
    fn audit(
        &self,
        _share: &CoZkCustodianShare,
        _witness: &[Self::Bit],
        _inputs: &[[Word<Self::Bit>; 3]],
        _proof: &MigrationZkProof,
    ) {
    }
}

#[cfg(any(feature = "std", test))]
fn batch_session(session: &[u8; 32], batch: usize) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.OUTER.BATCH.V1",
        &[session, &(batch as u64).to_le_bytes()],
    )
}
#[cfg(any(feature = "std", test))]
fn batch_entropy(entropy: &[u8; 32], session: &[u8; 32], batch: usize) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.OUTER.BATCH.ENTROPY.V1",
        &[entropy, session, &(batch as u64).to_le_bytes()],
    )
}

#[cfg(any(feature = "std", test))]
pub(crate) struct ReplicatedSeed {
    party: usize,
    session: [u8; 32],
    entropy: [u8; 32],
    keys: [[u8; 32]; 2],
}
#[cfg(any(feature = "std", test))]
impl Drop for ReplicatedSeed {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.entropy);
        for k in &mut self.keys {
            ct_zeroize_bytes(k);
        }
    }
}
impl<T: Transport> ProverEngine for Engine<T> {
    type Transport = T;
    #[cfg(any(feature = "std", test))]
    type BatchSeed = ReplicatedSeed;
    #[cfg(any(feature = "std", test))]
    fn batch_seed(
        &mut self,
        entropy: &[u8; 32],
        _cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> ReplicatedSeed {
        let (session, keys) = self.custody();
        ReplicatedSeed {
            party: self.party,
            session,
            entropy: *entropy,
            keys,
        }
    }
    #[cfg(any(feature = "std", test))]
    fn for_batch(
        seed: &ReplicatedSeed,
        batch: usize,
        transport: T,
        cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> Result<Self, Error> {
        let mut entropy = batch_entropy(&seed.entropy, &seed.session, batch);
        let engine = Engine::new(
            seed.party,
            batch_session(&seed.session, batch),
            seed.keys,
            transport,
        );
        let mut engine = match engine {
            Ok(engine) => engine,
            Err(error) => {
                ct_zeroize_bytes(&mut entropy);
                return Err(error);
            }
        };
        engine.batch_cancelled = Some(cancelled);
        engine.mix_entropy(&entropy);
        ct_zeroize_bytes(&mut entropy);
        Ok(engine)
    }
    #[cfg(any(feature = "std", test))]
    fn finish_batch(&mut self) {
        self.release_verified_scratch();
        self.batch_cancelled = None;
    }
    #[cfg(any(feature = "std", test))]
    fn max_parallel_batches(&self) -> usize {
        self.transport.max_parallel_batches()
    }
    #[cfg(test)]
    fn audit(
        &self,
        share: &CoZkCustodianShare,
        witness: &[outer_mpc::Bit],
        inputs: &[[Word; 3]],
        proof: &MigrationZkProof,
    ) {
        tests::audit_old_attack(share, self, witness, inputs, proof);
    }
}

#[cfg(any(feature = "std", test))]
pub(crate) struct QuorumSeed {
    party: usize,
    session: [u8; 32],
    entropy: [u8; 32],
    config: ThresholdConfig,
    peer_keys: Vec<[u8; 32]>,
    seed_slot: std::sync::Arc<std::sync::Mutex<MacKeyShare>>,
    pub(crate) escrow: QuorumKeyEscrow,
}
#[cfg(any(feature = "std", test))]
impl Drop for QuorumSeed {
    fn drop(&mut self) {
        ct_zeroize_bytes(&mut self.entropy);
        for k in &mut self.peer_keys {
            ct_zeroize_bytes(k);
        }
        self.seed_slot
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .wipe();
    }
}
impl<T: Transport> ProverEngine for SpdzEngine<T> {
    type Transport = T;
    #[cfg(any(feature = "std", test))]
    type BatchSeed = QuorumSeed;
    #[cfg(any(feature = "std", test))]
    fn batch_seed(
        &mut self,
        entropy: &[u8; 32],
        cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> QuorumSeed {
        let escrow = QuorumKeyEscrow::new(cancelled);
        self.attach_escrow(&escrow);
        let (session, config, peer_keys, mac_keys) = self.custody();
        let seed_slot = escrow.register(mac_keys);
        QuorumSeed {
            party: self.party,
            session,
            entropy: *entropy,
            config,
            peer_keys,
            seed_slot,
            escrow,
        }
    }
    #[cfg(any(feature = "std", test))]
    fn poison_batch_seed(seed: &QuorumSeed) {
        seed.escrow.poison_all();
    }
    #[cfg(any(feature = "std", test))]
    fn for_batch(
        seed: &QuorumSeed,
        batch: usize,
        transport: T,
        cancelled: alloc::sync::Arc<core::sync::atomic::AtomicBool>,
    ) -> Result<Self, Error> {
        if seed.escrow.is_poisoned() {
            return Err(Error::MultiplicationCheck);
        }
        let batch_keys = {
            let guard = seed.seed_slot.lock().unwrap_or_else(|e| e.into_inner());
            if seed.escrow.is_poisoned() {
                return Err(Error::MultiplicationCheck);
            }
            guard.fork_stream(b"BATCH", batch as u64)
        };
        let mut entropy = batch_entropy(&seed.entropy, &seed.session, batch);
        let engine = SpdzEngine::new(
            seed.party,
            batch_session(&seed.session, batch),
            seed.config.clone(),
            seed.peer_keys.clone(),
            batch_keys,
            transport,
        );
        let mut engine = match engine {
            Ok(engine) => engine,
            Err(error) => {
                ct_zeroize_bytes(&mut entropy);
                seed.escrow.poison_all();
                return Err(error);
            }
        };
        engine.attach_escrow(&seed.escrow);
        engine.batch_cancelled = Some(cancelled);
        engine.mix_entropy(&entropy);
        ct_zeroize_bytes(&mut entropy);
        Ok(engine)
    }
    #[cfg(any(feature = "std", test))]
    fn finish_batch(&mut self) {
        self.batch_cancelled = None;
    }
    #[cfg(any(feature = "std", test))]
    fn max_parallel_batches(&self) -> usize {
        self.transport.max_parallel_batches()
    }
}

struct LocalBatchSeeds {
    subseeds: Secret<[[[u8; 32]; 64]; 3]>,
    salts: Secret<[[[u8; 32]; 64]; 3]>,
}

struct BatchComputed<E: Core> {
    views: Vec<TypedView<E::Bit>>,
    masked_views: Vec<TypedView<E::Bit>>,
    engine: Option<E>,
    #[cfg(test)]
    audit_witness_inputs: [Word<E::Bit>; 3],
}

fn compute_batch<E: Core>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: &LocalBatchSeeds,
    batch: usize,
) -> Result<BatchComputed<E>, Error> {
    let (pos, m) = e.quorum_position();
    let mut own = SecretVec::from(vec![0u64; 3 * m * 256]);
    for h in 0..3 {
        for bit in 0..256 {
            own[(h * m + pos) * 256 + bit] = (0..64).fold(0, |v, lane| {
                v | (u64::from((seeds.subseeds[h][lane][bit / 8] >> (bit % 8)) & 1) << lane)
            });
        }
    }
    let shared = e.share_masked(&own)?;
    let mut views = evaluate_typed_views(e, c, witness, seeds, true)?;
    for (h, view) in views.iter_mut().enumerate() {
        view.subseeds = shared[h * m * 256..(h + 1) * m * 256]
            .iter()
            .copied()
            .collect();
    }
    let masked_views = mask_shared_views(e, batch, seeds, &views)?;
    e.verify_all_pending()?;
    #[cfg(test)]
    let audit_witness_inputs = core::array::from_fn(|h| views[h].audit_inputs.clone());
    Ok(BatchComputed {
        views,
        masked_views,
        engine: None,
        #[cfg(test)]
        audit_witness_inputs,
    })
}

#[derive(Clone)]
struct TypedValue<B: ShareBit> {
    domain: Domain,
    share: SharedValue<B>,
}
struct TypedView<B: ShareBit> {
    subseeds: Word<B>,
    inputs: Vec<TypedValue<B>>,
    products: Vec<TypedValue<B>>,
    outputs: Vec<TypedValue<B>>,
    #[cfg(test)]
    audit_inputs: Word<B>,
}
impl<B: ShareBit> TypedView<B> {
    fn new() -> Self {
        Self { subseeds: SecretVec::new(), inputs: Vec::new(), products: Vec::new(), outputs: Vec::new(), #[cfg(test)] audit_inputs: SecretVec::new() }
    }
}

/// Retain field-valued view entries in their original domain. All circuit
/// conversions still execute in evaluate_wires; only serialization conversions
/// are deferred until the masked values or challenged lanes are public.
fn evaluate_typed_views<E: Core>(e: &mut E, c: &Circuit, witness: &[E::Bit], seeds: &LocalBatchSeeds, require_zero: bool) -> Result<Vec<TypedView<E::Bit>>, Error> {
    let empty: [Word<E::Bit>; 3] = core::array::from_fn(|_| SecretVec::new());
    let EvaluatedWires { mut wires, .. } = evaluate_wires(e, c, witness, Some(&empty), Some(seeds))?;
    if require_zero { check_outputs_zero(e, c, &wires, &c.outputs)?; }
    let mut views: Vec<TypedView<E::Bit>> = (0..3).map(|_| TypedView::new()).collect();
    for &idx in &c.outputs {
        for (h, view) in views.iter_mut().enumerate() {
            view.outputs.push(TypedValue { domain: c.nodes[idx].domain, share: wires[idx].as_ref().unwrap()[h].clone() });
        }
    }
    for (idx, node) in c.nodes.iter().enumerate() {
        match node.op {
            Op::Input | Op::Mul(_, _) => {
                for (h, value) in wires[idx].take().unwrap().into_iter().enumerate() {
                    if matches!(node.op, Op::Input) {
                        // The existing concrete key-recovery audit uses the
                        // initial byte-padded witness-bit inputs, unchanged.
                        #[cfg(test)]
                        if node.domain == Domain::Bit { outer_mpc::encode(&mut views[h].audit_inputs, &[value.bit()]); }
                        if h == 2 { views[h].inputs.push(TypedValue { domain: node.domain, share: value }); }
                    } else { views[h].products.push(TypedValue { domain: node.domain, share: value }); }
                }
            }
            _ => {}
        }
    }
    Ok(views)
}

/// One independent mask contribution per custodian, sampled in each entry's
/// additive group (XOR for bits). No private field entry is serialized/opened
/// merely to hash it. Fixed seeds and the public circuit fix every mask.
fn mask_shared_views<E: Core>(e: &mut E, batch: usize, seeds: &LocalBatchSeeds, views: &[TypedView<E::Bit>]) -> Result<Vec<TypedView<E::Bit>>, Error> {
    let mut result = Vec::with_capacity(3);
    for (h, view) in views.iter().enumerate() {
        let values: Vec<_> = view.inputs.iter().chain(&view.products).chain(&view.outputs).collect();
        let bit_indices: Vec<_> = values.iter().enumerate().filter_map(|(i, v)| (v.domain == Domain::Bit).then_some(i)).collect();
        let field_indices: Vec<_> = values.iter().enumerate().filter_map(|(i, v)| (v.domain != Domain::Bit).then_some(i)).collect();
        let mut own_bits: SecretVec<u64> = vec![0; bit_indices.len()].into();
        let mut own_fields: SecretVec<Value> = vec![ZERO; field_indices.len() * 64].into();
        for (lane, seed) in seeds.subseeds[h].iter().enumerate() {
            let mask_seed = Secret(crate::batch_hash::view_mask_seed(seed, batch * 64 + lane, h));
            let mut tape = zk_engine::Tape::new(&mask_seed);
            let (mut bit_idx, mut field_idx) = (0, 0);
            for v in &values {
                let value = Secret(tape.sample(v.domain));
                if v.domain == Domain::Bit { own_bits[bit_idx] |= value[0] << lane; bit_idx += 1; }
                else { own_fields[field_idx * 64 + lane] = *value; field_idx += 1; }
            }
        }
        let mut masked: Vec<Option<TypedValue<E::Bit>>> = (0..values.len()).map(|_| None).collect();
        let bits = e.share_masked(&own_bits)?;
        for (&idx, &bit) in bit_indices.iter().zip(bits.iter()) {
            masked[idx] = Some(TypedValue { domain: Domain::Bit, share: SharedValue::Bit(values[idx].share.bit() ^ bit) });
        }
        for d in Domain::ALL_FIELDS {
            let indices: Vec<_> = field_indices.iter().enumerate().filter_map(|(f, &idx)| (values[idx].domain == d).then_some((f, idx))).collect();
            let mut own = SecretVec::with_capacity(indices.len() * 64);
            for &(f, _) in &indices { own.extend_from_slice(&own_fields[f * 64..(f + 1) * 64]); }
            let shares = e.fshare_many(&own, d)?;
            for ((_, idx), mask) in indices.into_iter().zip(shares) {
                masked[idx] = Some(TypedValue { domain: d, share: SharedValue::Field(e.fadd(values[idx].share.field(), &mask, d)) });
            }
        }
        let mut entries = masked.into_iter().map(Option::unwrap);
        let mut out = TypedView::new();
        out.inputs = entries.by_ref().take(view.inputs.len()).collect();
        out.products = entries.by_ref().take(view.products.len()).collect();
        out.outputs = entries.collect();
        result.push(out);
    }
    Ok(result)
}

/// Open only selected lanes, scaling unselected field lanes to zero before
/// the backend's mandatory authenticated opening. Encoding then operates on
/// public values, with the same canonical packed format used by the verifier.
fn open_typed_values<E: Core>(e: &mut E, values: &[TypedValue<E::Bit>], mask: u64) -> Result<Vec<Vec<u8>>, Error> {
    if values.is_empty() { return Ok(vec![Vec::new(); 64]); }
    let mut clear: SecretVec<Value> = vec![ZERO; values.len() * 64].into();
    let bit_indices: Vec<_> = values.iter().enumerate().filter_map(|(i, v)| (v.domain == Domain::Bit).then_some(i)).collect();
    let bits: Word<E::Bit> = bit_indices.iter().map(|&i| values[i].share.bit()).collect();
    let opened = e.open_lanes(&bits, mask)?;
    for (&idx, &word) in bit_indices.iter().zip(&opened) {
        for lane in 0..64 { clear[idx * 64 + lane][0] = (word >> lane) & 1; }
    }
    let selectors: [Value; 64] = core::array::from_fn(|lane| [(mask >> lane) & 1, 0, 0, 0, 0, 0]);
    for d in Domain::ALL_FIELDS {
        let indices: Vec<_> = values.iter().enumerate().filter_map(|(i, v)| (v.domain == d).then_some(i)).collect();
        if indices.is_empty() { continue; }
        let words: Vec<_> = indices.iter().map(|&i| e.fscale_lanes(values[i].share.field(), &selectors, d)).collect();
        let opened = e.fopen_many(&words, d)?;
        for (idx, word) in indices.into_iter().zip(opened) { clear[idx * 64..(idx + 1) * 64].copy_from_slice(&word); }
    }
    let bytes = values.iter().map(|v| v.domain.width()).sum::<usize>().div_ceil(8);
    Ok((0..64).map(|lane| {
        let mut packer = zk_engine::BitPacker::with_capacity(bytes);
        for (idx, v) in values.iter().enumerate() { packer.push_value(v.domain, clear[idx * 64 + lane]); }
        packer.into_bytes()
    }).collect())
}

fn open_batch_public_rounds<E: Core>(e: &mut E, batch: usize, masked_views: &[TypedView<E::Bit>], views: &[TypedView<E::Bit>], seed_commitments: &[Vec<u8>]) -> Result<Vec<PublicRound>, Error> {
    #[cfg(test)]
    e.on_public_or_view_open();
    let mut masked = Vec::with_capacity(3);
    let mut outputs = Vec::with_capacity(3);
    for (masked_view, view) in masked_views.iter().zip(views) {
        masked.push((open_typed_values(e, &masked_view.inputs, u64::MAX)?, open_typed_values(e, &masked_view.products, u64::MAX)?, open_typed_values(e, &masked_view.outputs, u64::MAX)?));
        outputs.push(open_typed_values(e, &view.outputs, u64::MAX)?);
    }
    let count = core::cmp::min(64, MIT_REPETITIONS - batch * 64);
    Ok(crate::parallel::map(count, |lane| {
        let rep = batch * 64 + lane;
        let commits = core::array::from_fn(|h| {
            let offset = (rep * 3 + h) * 64 + 32;
            let seeds: Vec<[u8; 32]> = seed_commitments.iter().map(|v| v[offset..offset + 32].try_into().unwrap()).collect();
            crate::batch_hash::commit_cozk_tree_one(&COZK_VIEW_MAGIC_V5, rep, h, &seeds, &masked[h].0[lane], &masked[h].1[lane], &masked[h].2[lane])
        });
        PublicRound { commits, outputs: core::array::from_fn(|h| outputs[h][lane].clone()) }
    }))
}

fn compute_batches<E: ProverEngine>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: &[LocalBatchSeeds],
    children: Vec<E::Transport>,
    entropy: &[u8; 32],
) -> Result<Vec<BatchComputed<E>>, Error> {
    #[cfg(any(feature = "std", test))]
    if !children.is_empty() {
        let cancelled = alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false));
        let seed = e.batch_seed(entropy, cancelled.clone());
        let seed = &seed;
        let width = e
            .max_parallel_batches()
            .max(1)
            .min(children.len())
            .min(crate::parallel::workers(children.len()));
        let mut jobs = children.into_iter().enumerate();
        let mut completed = Vec::with_capacity(seeds.len());
        while jobs.len() != 0 {
            let wave: Result<Vec<_>, Error> = std::thread::scope(|scope| {
                let handles: Vec<_> = jobs
                    .by_ref()
                    .take(width)
                    .map(|(batch, transport)| {
                        let cancelled = cancelled.clone();
                        scope.spawn(move || {
                            let result = (|| {
                                let mut engine =
                                    E::for_batch(seed, batch, transport, cancelled.clone())?;
                                let mut result =
                                    compute_batch(&mut engine, c, witness, &seeds[batch], batch)?;
                                engine.finish_batch();
                                result.engine = Some(engine);
                                Ok(result)
                            })();
                            if result.is_err() {
                                // Cancellation can only abort, and synchronously poisons + wipes
                                // all concurrent worker `MacKeyShare`s in `QuorumKeyEscrow`.
                                cancelled.store(true, core::sync::atomic::Ordering::SeqCst);
                                E::poison_batch_seed(seed);
                            }
                            result
                        })
                    })
                    .collect();
                let results: Vec<Result<_, Error>> = handles
                    .into_iter()
                    .map(|h| {
                        h.join().unwrap_or_else(|_| {
                            cancelled.store(true, core::sync::atomic::Ordering::SeqCst);
                            E::poison_batch_seed(seed);
                            Err(Error::Transport)
                        })
                    })
                    .collect();
                // A sibling cancelled at an exchange reports Transport or MultiplicationCheck.
                // Preserve the primary non-Transport rejection.
                if let Some(error) = results
                    .iter()
                    .filter_map(|r| r.as_ref().err())
                    .find(|&&error| error != Error::Transport)
                {
                    return Err(*error);
                }
                results.into_iter().collect()
            });
            completed.extend(wave?);
        }
        return Ok(completed);
    }
    #[cfg(not(any(feature = "std", test)))]
    let _ = (children, entropy);
    seeds
        .iter()
        .enumerate()
        .map(|(batch, seed)| compute_batch(e, c, witness, seed, batch))
        .collect()
}

#[derive(Clone)]
struct PublicRound {
    commits: [[u8; 32]; 3],
    outputs: [Vec<u8>; 3],
}

#[cfg(test)]
struct SharedView<B: ShareBit> {
    subseeds: Word<B>,
    #[cfg(test)]
    audit_inputs: Word<B>,
    #[cfg(test)]
    seed: Word<B>,
    inputs: Word<B>,
    products: Word<B>,
    outputs: Word<B>,
}
#[cfg(test)]
impl<B: ShareBit> SharedView<B> {
    #[cfg(test)]
    fn bytes(&self) -> Word<B> {
        let mut out = SecretVec::with_capacity(
            self.seed.len() + self.inputs.len() + self.products.len() + self.outputs.len(),
        );
        out.extend_from_slice(&self.seed);
        out.extend_from_slice(&self.inputs);
        out.extend_from_slice(&self.products);
        out.extend_from_slice(&self.outputs);
        out
    }
}

#[derive(Clone)]
enum SharedValue<B: ShareBit> {
    Bit(B),
    Field(FieldWord),
}
impl<B: ShareBit> SharedValue<B> {
    fn zero(d: Domain) -> Self {
        if d == Domain::Bit {
            Self::Bit(B::default())
        } else {
            Self::Field(vec![[ZERO; 2]; 64].into())
        }
    }
    fn bit(&self) -> B {
        match self {
            Self::Bit(b) => *b,
            _ => unreachable!("public circuit domain"),
        }
    }
    fn field(&self) -> &FieldWord {
        match self {
            Self::Field(f) => f,
            _ => unreachable!("public circuit domain"),
        }
    }
}
impl<B: ShareBit> Drop for SharedValue<B> {
    fn drop(&mut self) {
        match self {
            Self::Bit(b) => b.secret_wipe(),
            Self::Field(_) => {} // FieldWord owns its wipe-on-drop storage.
        }
    }
}

#[derive(Default)]
struct TapeCursor {
    sponge_bits: usize,
    bit_chunk_start: usize,
    bit_rem: usize,
}
impl TapeCursor {
    fn next_bit(&mut self) -> usize {
        if self.bit_rem == 0 {
            self.bit_chunk_start = self.sponge_bits;
            self.sponge_bits += 64;
            self.bit_rem = 64;
        }
        let pos = self.bit_chunk_start + (64 - self.bit_rem);
        self.bit_rem -= 1;
        pos
    }
    fn next_field(&mut self, d: Domain) -> usize {
        let start = self.sponge_bits;
        self.sponge_bits += d.tape_draw_bits();
        start
    }
}

#[derive(Clone, Copy)]
enum NodeTape {
    None,
    InputBit { witness_idx: usize, pos: [usize; 2] },
    InputField { target: usize, draws: [usize; 2] },
    MulBit { pos: [usize; 3] },
    MulField { draws: [usize; 3] },
}

struct FieldTapeDraw {
    head: usize,
    start: usize,
    domain: Domain,
}

/// Most candidates one field draw may consume. A Goldilocks word is rejected
/// with probability `2^-32` (the 256-bit domains: below `2^-127`), so a draw
/// that still has no canonical candidate after this many has probability at
/// most `2^-256` and is reported as [`Error::InvalidTape`].
const MAX_TAPE_ATTEMPTS: usize = 8;

// Replay a finite tape with a public per-draw attempt budget. Rejection masks
// remain shared: each lane conditionally removes a rejected word from the entire
// unread suffix, including future Boolean refill words. Previously cached bits
// precede `start` and are never moved. A failed budget is retried from the original
// stream, so an unresolved draw cannot discard a later draw's valid candidate.
//
// The result is the stream `zk_engine::Tape` reads from the same seed: a
// non-canonical word is skipped and the draw takes the next word of the same
// width, Boolean refills take whole 64-bit words in stream order. Wide
// zero-rejection domains (`PallasFp` and `BlsFp`) never reject, while still
// shifting in lockstep whenever an earlier `Gold`/`Secp`/`Ed` draw skips a word.
fn canonical_tape_attempt<E: Core>(
    e: &mut E,
    streams: &[Word<E::Bit>],
    draws: &[FieldTapeDraw],
    counts: [usize; 3],
    attempts: usize,
) -> Result<Option<Vec<Word<E::Bit>>>, Error> {
    let required = tape_counts(draws, counts, attempts)?;
    if streams.len() != 3 || streams.iter().zip(required).any(|(s, n)| s.len() < n) {
        return Err(Error::InvalidTape);
    }
    let mut out: Vec<Word<E::Bit>> = streams
        .iter()
        .zip(required)
        .map(|(s, n)| s[..n].iter().copied().collect())
        .collect();
    let mut valid: [Word<E::Bit>; 3] = core::array::from_fn(|_| SecretVec::new());
    for draw in draws {
        if matches!(draw.domain, Domain::PallasFp | Domain::BlsFp) {
            continue;
        }
        let stream = &mut out[draw.head];
        let width = draw.domain.width();
        let consumed = draw.domain.tape_draw_bits();
        for attempt in 0..attempts {
            let word = stream[draw.start..draw.start + width]
                .iter()
                .copied()
                .collect();
            let accepted = e.less_than_modulus_many(&[word], draw.domain)?[0];
            if attempt + 1 == attempts {
                valid[draw.head].push(accepted);
            } else {
                let end = stream.len() - consumed;
                let reject = accepted ^ e.constant(u64::MAX);
                let pairs: SecretVec<_> = (draw.start..end)
                    .map(|i| (reject, stream[i] ^ stream[i + consumed]))
                    .collect();
                let changes = e.and(&pairs)?;
                for (slot, change) in stream[draw.start..end].iter_mut().zip(changes.iter()) {
                    *slot = *slot ^ *change;
                }
                stream.truncate(end);
            }
        }
    }
    let valid = fold_valid_bits(e, valid)?;
    Ok(if e.open(&valid)?.iter().all(|&v| v == u64::MAX) {
        Some(out)
    } else {
        None
    })
}

fn tape_counts(
    draws: &[FieldTapeDraw],
    counts: [usize; 3],
    attempts: usize,
) -> Result<[usize; 3], Error> {
    let extra = attempts.checked_sub(1).ok_or(Error::InvalidTape)?;
    let mut required = counts;
    let mut ends = [0; 3];
    for draw in draws {
        if draw.head >= 3 || draw.domain == Domain::Bit {
            return Err(Error::InvalidTape);
        }
        let width = draw.domain.tape_draw_bits();
        let end = draw.start.checked_add(width).ok_or(Error::InvalidTape)?;
        if draw.start < ends[draw.head] || end > counts[draw.head] {
            return Err(Error::InvalidTape);
        }
        ends[draw.head] = end;
        if !matches!(draw.domain, Domain::PallasFp | Domain::BlsFp) {
            required[draw.head] = required[draw.head]
                .checked_add(width.checked_mul(extra).ok_or(Error::InvalidTape)?)
                .ok_or(Error::InvalidTape)?;
        }
    }
    Ok(required)
}

fn fold_valid_bits<E: Core>(
    e: &mut E,
    mut groups: [Word<E::Bit>; 3],
) -> Result<[E::Bit; 3], Error> {
    for g in &mut groups {
        if g.is_empty() {
            g.push(e.constant(u64::MAX));
        }
    }
    while groups.iter().any(|g| g.len() > 1) {
        let mut pairs = SecretVec::new();
        for g in &groups {
            for pair in g.chunks_exact(2) {
                pairs.push((pair[0], pair[1]));
            }
        }
        let prods = e.and(&pairs)?;
        let mut cur = 0usize;
        for g in &mut groups {
            let num_pairs = g.len() / 2;
            let mut next = SecretVec::with_capacity(num_pairs + (g.len() % 2));
            next.extend_from_slice(&prods[cur..cur + num_pairs]);
            cur += num_pairs;
            if g.len() % 2 == 1 {
                next.push(*g.last().unwrap());
            }
            *g = next;
        }
    }
    Ok([groups[0][0], groups[1][0], groups[2][0]])
}

fn fold_all_true_bits<E: Core>(e: &mut E, mut bits: Word<E::Bit>) -> Result<E::Bit, Error> {
    if bits.is_empty() {
        return Ok(e.constant(u64::MAX));
    }
    while bits.len() > 1 {
        let mut pairs = SecretVec::with_capacity(bits.len() / 2);
        for pair in bits.chunks_exact(2) {
            pairs.push((pair[0], pair[1]));
        }
        let mut next = e.and(&pairs)?;
        if bits.len() % 2 == 1 {
            next.push(*bits.last().unwrap());
        }
        bits = next;
    }
    Ok(bits[0])
}

struct EvaluatedWires<B: ShareBit> {
    wires: Vec<Option<[SharedValue<B>; 3]>>,
    #[cfg(test)]
    raw_draw_words: Vec<Word<B>>,
    #[cfg(test)]
    encodings: Vec<[Option<Word<B>>; 3]>,
    #[cfg(test)]
    node_tapes: Vec<NodeTape>,
}

fn check_outputs_zero<E: Core>(
    e: &mut E,
    c: &Circuit,
    wires: &[Option<[SharedValue<E::Bit>; 3]>],
    outputs: &[usize],
) -> Result<(), Error> {
    let mut residual_bits: Word<E::Bit> = SecretVec::new();
    for &out in outputs {
        if c.nodes[out].domain == Domain::Bit {
            let w = wires[out].as_ref().unwrap();
            residual_bits.push(w[0].bit() ^ w[1].bit() ^ w[2].bit());
        }
    }
    for dom in Domain::ALL_FIELDS {
        let mut sums: Vec<FieldWord> = Vec::new();
        for &out in outputs {
            if c.nodes[out].domain == dom {
                let w = wires[out].as_ref().unwrap();
                let s01 = e.fadd(w[0].field(), w[1].field(), dom);
                sums.push(e.fadd(&s01, w[2].field(), dom));
            }
        }
        if !sums.is_empty() {
            let refs: Vec<&FieldWord> = sums.iter().collect();
            let converted = e.field_to_bits_many(&refs, dom)?;
            for fw in &mut sums {
                for pair in fw {
                    ct_zeroize_u64s(&mut pair[0]);
                    ct_zeroize_u64s(&mut pair[1]);
                }
            }
            for word in converted {
                residual_bits.extend(word);
            }
        }
    }
    let ones = e.constant(u64::MAX);
    let zero_flags: Word<E::Bit> = residual_bits.into_iter().map(|b| b ^ ones).collect();
    let all_outputs_zero = fold_all_true_bits(e, zero_flags)?;
    // Explicitly verify all circuit, conversion, and tree-AND multiplications
    // BEFORE opening the single 1-bit `all_outputs_zero` predicate.
    e.verify_all_pending()?;
    let opened_ok = e.open(&[all_outputs_zero])?;
    if opened_ok[0] != u64::MAX {
        return Err(Error::InvalidProof);
    }
    Ok(())
}

fn derive_nullifier_in_mpc<E: Core>(
    e: &mut E,
    pre_circuit: &Circuit,
    own_witness: &[u64],
    req_bytes: &[u8],
) -> Result<[u64; 4], Error> {
    if pre_circuit.outputs.len() < 4 {
        return Err(Error::InvalidConfiguration);
    }
    e.agree(cshake256_framed_32(b"QSAG.OUTER.REQUEST.V1", &[req_bytes]))?;
    let witness = e.share_uniform_lanes(own_witness)?;
    // No virtual head of this evaluation is ever opened, so its tapes are
    // public zeros: the outer sharing alone hides every wire.
    let eval = evaluate_wires(e, pre_circuit, &witness, None, None)?;
    let split = pre_circuit.outputs.len() - 4;
    // Verify scalar canonicality + public commitment match BEFORE opening the nullifier!
    check_outputs_zero(e, pre_circuit, &eval.wires, &pre_circuit.outputs[..split])?;

    let mut nul_words = Vec::with_capacity(4);
    for &out_idx in &pre_circuit.outputs[split..] {
        if pre_circuit.nodes[out_idx].domain != Domain::Gold {
            return Err(Error::InvalidConfiguration);
        }
        let w = eval.wires[out_idx].as_ref().unwrap();
        let s01 = e.fadd(w[0].field(), w[1].field(), Domain::Gold);
        nul_words.push(e.fadd(&s01, w[2].field(), Domain::Gold));
    }
    let opened = e.fopen_many(&nul_words, Domain::Gold)?;
    let mut nullifier = [0u64; 4];
    for (slot, lanes) in nullifier.iter_mut().zip(&opened) {
        let first = lanes[0][0];
        if lanes.iter().any(|v| v[0] != first) {
            e.poison();
            return Err(Error::InvalidProof);
        }
        *slot = first;
    }
    Ok(nullifier)
}

#[cfg(test)]
fn evaluate<E: Core>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: &[Word<E::Bit>],
) -> Result<Vec<SharedView<E::Bit>>, Error> {
    evaluate_inner(e, c, witness, seeds, false)
}

/// Evaluate `c` over the three virtual heads. `seeds` are the heads' shared
/// tape seeds; `None` gives every head an all-zero public tape, which is only
/// sound when no head view or commitment of this evaluation is opened.
fn evaluate_wires<E: Core>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: Option<&[Word<E::Bit>]>,
    local: Option<&LocalBatchSeeds>,
) -> Result<EvaluatedWires<E::Bit>, Error> {
    // Keep field-fault regressions aimed at circuit evaluation, even when tape
    // conversion itself uses arithmetic multiplications for carry correction.
    #[cfg(test)]
    let circuit_field_fault = e.take_field_fault();

    // 1. Pre-schedule exact `Tape` bit/field draws and topological DAG waves.
    let mut cursors: [TapeCursor; 3] = core::array::from_fn(|_| TapeCursor::default());
    let mut field_draws: Vec<FieldTapeDraw> = Vec::new();
    let mut node_tapes = Vec::with_capacity(c.nodes.len());
    let mut waves = vec![0usize; c.nodes.len()];
    let mut max_wave = 0usize;
    let mut witness_cursor = 0usize;

    for (index, node) in c.nodes.iter().enumerate() {
        let d = node.domain;
        let (nt, w) = match node.op {
            Op::Constant(_) => (NodeTape::None, 0),
            Op::Input => {
                if d == Domain::Bit {
                    if witness_cursor >= witness.len() {
                        return Err(Error::InvalidConfiguration);
                    }
                    let witness_idx = witness_cursor;
                    witness_cursor += 1;
                    let pos = [cursors[0].next_bit(), cursors[1].next_bit()];
                    (NodeTape::InputBit { witness_idx, pos }, 0)
                } else {
                    let target = match c.nodes.get(index + 1).map(|n| n.op) {
                        Some(Op::Mul(a, b)) if a == index => b,
                        Some(Op::Mul(a, b)) if b == index => a,
                        _ => return Err(Error::InvalidConfiguration),
                    };
                    if target >= index {
                        return Err(Error::InvalidConfiguration);
                    }
                    let d0 = field_draws.len();
                    field_draws.push(FieldTapeDraw {
                        head: 0,
                        start: if local.is_some() {
                            0
                        } else {
                            cursors[0].next_field(d)
                        },
                        domain: d,
                    });
                    let d1 = field_draws.len();
                    field_draws.push(FieldTapeDraw {
                        head: 1,
                        start: if local.is_some() {
                            0
                        } else {
                            cursors[1].next_field(d)
                        },
                        domain: d,
                    });
                    (
                        NodeTape::InputField {
                            target,
                            draws: [d0, d1],
                        },
                        waves[target] + 1,
                    )
                }
            }
            Op::Lift(a, _) | Op::Digit(a, _, _) => (NodeTape::None, waves[a] + 1),
            Op::Add(a, b) | Op::Sub(a, b) => (NodeTape::None, waves[a].max(waves[b])),
            Op::Scale(a, _) => (NodeTape::None, waves[a]),
            Op::Mul(a, b) => {
                let w = waves[a].max(waves[b]) + 1;
                if d == Domain::Bit {
                    let pos = [
                        cursors[0].next_bit(),
                        cursors[1].next_bit(),
                        cursors[2].next_bit(),
                    ];
                    (NodeTape::MulBit { pos }, w)
                } else {
                    let mut draws = [0usize; 3];
                    for h in 0..3 {
                        draws[h] = field_draws.len();
                        field_draws.push(FieldTapeDraw {
                            head: h,
                            start: if local.is_some() {
                                0
                            } else {
                                cursors[h].next_field(d)
                            },
                            domain: d,
                        });
                    }
                    (NodeTape::MulField { draws }, w)
                }
            }
        };
        waves[index] = w;
        if w > max_wave {
            max_wave = w;
        }
        node_tapes.push(nt);
    }

    // 2. Initialize all 3 `Tape` sponges and squeeze their exact streams in lockstep.
    let zero_bit = e.constant(0);
    let mut local_fields: Vec<Option<FieldWord>> = (0..field_draws.len()).map(|_| None).collect();
    let (squeezed, raw_draw_words) = if let Some(local) = local {
        let mut own_bits: [SecretVec<u64>; 3] =
            core::array::from_fn(|h| vec![0; cursors[h].sponge_bits].into());
        let mut own_fields: SecretVec<Value> = vec![ZERO; field_draws.len() * 64].into();
        for h in 0..3 {
            for (lane, seed) in local.subseeds[h].iter().enumerate() {
                let mut tape = zk_engine::Tape::new(seed);
                for (node, nt) in c.nodes.iter().zip(&node_tapes) {
                    match *nt {
                        NodeTape::InputBit { pos, .. } if h < 2 => {
                            let v = Secret(tape.sample(Domain::Bit));
                            own_bits[h][pos[h]] |= v[0] << lane;
                        }
                        NodeTape::MulBit { pos } => {
                            let v = Secret(tape.sample(Domain::Bit));
                            own_bits[h][pos[h]] |= v[0] << lane;
                        }
                        NodeTape::InputField { draws, .. } if h < 2 => {
                            own_fields[draws[h] * 64 + lane] = tape.sample(node.domain);
                        }
                        NodeTape::MulField { draws } => {
                            own_fields[draws[h] * 64 + lane] = tape.sample(node.domain);
                        }
                        _ => {}
                    }
                }
            }
        }
        // Pack only actual Boolean draws, skipping public field/cached-bit gaps.
        let mut positions = Vec::new();
        for nt in &node_tapes {
            match *nt {
                NodeTape::InputBit { pos, .. } => positions.extend((0..2).map(|h| (h, pos[h]))),
                NodeTape::MulBit { pos } => positions.extend((0..3).map(|h| (h, pos[h]))),
                _ => {}
            }
        }
        let flat: SecretVec<u64> = positions.iter().map(|&(h, p)| own_bits[h][p]).collect();
        let shares = e.share_masked(&flat)?;
        let mut streams: Vec<Word<E::Bit>> = cursors
            .iter()
            .map(|c| vec![zero_bit; c.sponge_bits].into())
            .collect();
        for ((h, p), share) in positions.into_iter().zip(shares.iter()) {
            streams[h][p] = *share;
        }
        for d in Domain::ALL_FIELDS {
            let indices: Vec<_> = field_draws
                .iter()
                .enumerate()
                .filter_map(|(i, f)| (f.domain == d).then_some(i))
                .collect();
            let mut words = SecretVec::with_capacity(indices.len() * 64);
            for &i in &indices {
                words.extend_from_slice(&own_fields[i * 64..(i + 1) * 64]);
            }
            let shared = e.fshare_many(&words, d)?;
            for (i, word) in indices.into_iter().zip(shared) {
                local_fields[i] = Some(word);
            }
        }
        (
            streams,
            field_draws.iter().map(|_| SecretVec::new()).collect(),
        )
    } else if let Some(seeds) = seeds {
        let mut tape_sponges = Vec::with_capacity(3);
        for seed in seeds {
            let mut sp = Sponge::new(e);
            sp.public(e, b"QSAG.MIGRATE.TAPE.V3")?;
            sp.absorb(e, seed)?;
            sp.pad_only(e, 0x1f);
            tape_sponges.push(sp);
        }
        {
            let (s0, rest) = tape_sponges.split_first_mut().unwrap();
            let (s1, rest2) = rest.split_first_mut().unwrap();
            let s2 = &mut rest2[0];
            e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
        }
        let mut squeezed = outer_mpc::squeeze_sponges_lockstep(
            e,
            &mut tape_sponges,
            &[
                cursors[0].sponge_bits,
                cursors[1].sponge_bits,
                cursors[2].sponge_bits,
            ],
        )?;

        // 3. Batch-check `< modulus` across rejection-sampled domains (`Gold`, `Secp`, `Ed`)
        // and open `valid` upfront; `PallasFp` and `BlsFp` use wide zero-rejection draws.
        let mut valid_groups: [Word<E::Bit>; 3] = core::array::from_fn(|_| SecretVec::new());
        let mut raw_draw_words: Vec<Word<E::Bit>> = field_draws
            .iter()
            .map(|fd| {
                if matches!(fd.domain, Domain::PallasFp | Domain::BlsFp) {
                    SecretVec::new()
                } else {
                    squeezed[fd.head][fd.start..fd.start + fd.domain.width()]
                        .iter()
                        .copied()
                        .collect()
                }
            })
            .collect();

        for dom in [Domain::Gold, Domain::Secp, Domain::Ed] {
            let mut dom_words = Vec::new();
            let mut dom_heads = Vec::new();
            for (idx, fd) in field_draws.iter().enumerate() {
                if fd.domain == dom {
                    dom_words.push(raw_draw_words[idx].clone());
                    dom_heads.push(fd.head);
                }
            }
            if !dom_words.is_empty() {
                let lt_bits = e.less_than_modulus_many(&dom_words, dom)?;
                for (h, lt) in dom_heads.into_iter().zip(lt_bits) {
                    valid_groups[h].push(lt);
                }
            }
        }
        let valid = fold_valid_bits(e, valid_groups)?;
        if e.open(&valid)?.iter().any(|&v| v != u64::MAX) {
            let counts = core::array::from_fn(|h| cursors[h].sponge_bits);
            let mut attempts = 2usize;
            loop {
                let required = tape_counts(&field_draws, counts, attempts)?;
                let additional: Vec<_> = required
                    .iter()
                    .zip(&squeezed)
                    .map(|(&n, s)| n - s.len())
                    .collect();
                let more = outer_mpc::squeeze_sponges_lockstep(e, &mut tape_sponges, &additional)?;
                for (stream, tail) in squeezed.iter_mut().zip(&more) {
                    stream.extend_from_slice(tail);
                }
                if let Some(repaired) =
                    canonical_tape_attempt(e, &squeezed, &field_draws, counts, attempts)?
                {
                    squeezed = repaired;
                    break;
                }
                if attempts >= MAX_TAPE_ATTEMPTS {
                    return Err(Error::InvalidTape);
                }
                attempts *= 2;
            }
            for (word, draw) in raw_draw_words.iter_mut().zip(&field_draws) {
                if !matches!(draw.domain, Domain::PallasFp | Domain::BlsFp) {
                    word.copy_from_slice(
                        &squeezed[draw.head][draw.start..draw.start + draw.domain.width()],
                    );
                }
            }
        }
        (squeezed, raw_draw_words)
    } else {
        let squeezed: Vec<Word<E::Bit>> = cursors
            .iter()
            .map(|cursor| (0..cursor.sponge_bits).map(|_| zero_bit).collect())
            .collect();
        let raw_draw_words = field_draws.iter().map(|_| SecretVec::new()).collect();
        (squeezed, raw_draw_words)
    };
    let mut raw_draw_words: Vec<Word<E::Bit>> = raw_draw_words;

    // Only single-word `NodeTape::InputField` draws (`Gold`/`Secp`/`Ed`) are read again in Step 7.
    let mut keep_raw_draw = vec![false; field_draws.len()];
    for nt in &node_tapes {
        if let NodeTape::InputField { draws, .. } = *nt {
            keep_raw_draw[draws[0]] = true;
            keep_raw_draw[draws[1]] = true;
        }
    }

    // 4. Batch-convert all validated field tape draws (`bits_to_field_many` per domain).
    let mut draw_fields: Vec<Option<FieldWord>> = field_draws
        .iter()
        .map(|fd| seeds.is_none().then(|| e.fconstant(ZERO, fd.domain)))
        .collect();
    if local.is_some() {
        draw_fields = local_fields;
    }
    let converted_domains: &[Domain] = if seeds.is_some() && local.is_none() {
        &[Domain::Gold, Domain::Secp, Domain::Ed]
    } else {
        &[]
    };
    for &dom in converted_domains {
        let mut idxs = Vec::new();
        let mut dom_words = Vec::new();
        for (idx, fd) in field_draws.iter().enumerate() {
            if fd.domain == dom {
                idxs.push(idx);
                if keep_raw_draw[idx] {
                    dom_words.push(raw_draw_words[idx].clone());
                } else {
                    dom_words.push(core::mem::take(&mut raw_draw_words[idx]));
                }
            }
        }
        if !dom_words.is_empty() {
            let converted = e.bits_to_field_many(&dom_words, dom)?;
            for (idx, fw) in idxs.into_iter().zip(converted) {
                draw_fields[idx] = Some(fw);
            }
        }
    }
    for (dom, limb_bits, hi_offset, two_pow) in [
        (
            Domain::PallasFp,
            254usize,
            256usize,
            [0, 0, 0, 1u64 << 62, 0, 0],
        ),
        (
            Domain::BlsFp,
            380usize,
            384usize,
            [0, 0, 0, 0, 0, 1u64 << 60],
        ),
    ] {
        let mut idxs = Vec::new();
        let mut wide_words: Vec<Word<E::Bit>> = Vec::new();
        for (idx, fd) in field_draws.iter().enumerate() {
            if fd.domain == dom && seeds.is_some() && local.is_none() {
                idxs.push(idx);
                let mut lo: Word<E::Bit> = squeezed[fd.head][fd.start..fd.start + limb_bits]
                    .iter()
                    .copied()
                    .collect();
                lo.push(zero_bit);
                let mut hi: Word<E::Bit> = squeezed[fd.head]
                    [fd.start + hi_offset..fd.start + hi_offset + limb_bits]
                    .iter()
                    .copied()
                    .collect();
                hi.push(zero_bit);
                wide_words.push(lo);
                wide_words.push(hi);
            }
        }
        if !wide_words.is_empty() {
            let converted = e.bits_to_field_many(&wide_words, dom)?;
            for (idx, pair) in idxs.into_iter().zip(converted.chunks_exact(2)) {
                let hi_scaled = e.fscale(&pair[1], two_pow, dom);
                draw_fields[idx] = Some(e.fadd(&pair[0], &hi_scaled, dom));
            }
        }
    }

    #[cfg(test)]
    if let Some(fault) = circuit_field_fault {
        e.restore_fault(fault);
    }

    // 5. Execute the circuit wave by wave, batching all parallel communication gates.
    let mut wave_comm: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    let mut wave_local: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    let mut keep_wire = vec![false; c.nodes.len()];
    let mut last_use_wave = waves.clone();
    for &out in &c.outputs {
        keep_wire[out] = true;
    }
    for (index, node) in c.nodes.iter().enumerate() {
        let w = waves[index];
        match node.op {
            Op::Input => {
                keep_wire[index] = true;
                if let NodeTape::InputField { target, .. } = node_tapes[index] {
                    last_use_wave[target] = last_use_wave[target].max(w);
                }
            }
            Op::Mul(a, b) => {
                keep_wire[index] = true;
                last_use_wave[a] = last_use_wave[a].max(w);
                last_use_wave[b] = last_use_wave[b].max(w);
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                last_use_wave[a] = last_use_wave[a].max(w);
                last_use_wave[b] = last_use_wave[b].max(w);
            }
            Op::Scale(a, _) | Op::Lift(a, _) | Op::Digit(a, _, _) => {
                last_use_wave[a] = last_use_wave[a].max(w);
            }
            Op::Constant(_) => {}
        }
        let is_comm = match node.op {
            Op::Input => node.domain != Domain::Bit,
            Op::Lift(_, _) | Op::Digit(_, _, _) | Op::Mul(_, _) => true,
            Op::Constant(_) | Op::Add(_, _) | Op::Sub(_, _) | Op::Scale(_, _) => false,
        };
        if is_comm {
            wave_comm[w].push(index);
        } else {
            wave_local[w].push(index);
        }
    }
    let mut retire_at_wave: Vec<Vec<usize>> = (0..=max_wave).map(|_| Vec::new()).collect();
    for (index, &keep) in keep_wire.iter().enumerate() {
        if !keep {
            retire_at_wave[last_use_wave[index]].push(index);
        }
    }

    let mut wires: Vec<Option<[SharedValue<E::Bit>; 3]>> =
        (0..c.nodes.len()).map(|_| None).collect();
    let mut encodings: Vec<[Option<Word<E::Bit>>; 3]> =
        (0..c.nodes.len()).map(|_| [None, None, None]).collect();

    for w in 0..=max_wave {
        let comm_nodes = &wave_comm[w];
        if !comm_nodes.is_empty() {
            // 5a. Prime-field `Op::Input` (`finverse`).
            for &idx in comm_nodes {
                if let NodeTape::InputField { target, draws } = node_tapes[idx] {
                    let d = c.nodes[idx].domain;
                    let tw = wires[target].as_ref().unwrap();
                    let sum01 = e.fadd(tw[0].field(), tw[1].field(), d);
                    let sum = e.fadd(&sum01, tw[2].field(), d);
                    let inv = e.finverse(&sum, d)?;
                    let aa = draw_fields[draws[0]].take().unwrap();
                    let bb = draw_fields[draws[1]].take().unwrap();
                    let ab = e.fadd(&aa, &bb, d);
                    let cc = e.fsub(&inv, &ab, d);
                    wires[idx] = Some([
                        SharedValue::Field(aa),
                        SharedValue::Field(bb),
                        SharedValue::Field(cc),
                    ]);
                }
            }

            // 5b. `Op::Lift` batched per domain (`lift_bits_many`).
            for dom in Domain::ALL_FIELDS {
                let mut lift_idxs = Vec::new();
                let mut lift_owners = Vec::new();
                let mut lift_bits = SecretVec::new();
                for &idx in comm_nodes {
                    if c.nodes[idx].domain == dom
                        && let Op::Lift(a, owner) = c.nodes[idx].op
                    {
                        lift_idxs.push(idx);
                        lift_owners.push(owner);
                        lift_bits.push(wires[a].as_ref().unwrap()[owner].bit());
                    }
                }
                if !lift_bits.is_empty() {
                    let lifted = e.lift_bits_many(&lift_bits, dom)?;
                    for ((idx, owner), fw) in lift_idxs.into_iter().zip(lift_owners).zip(lifted) {
                        let mut parts = core::array::from_fn(|_| SharedValue::zero(dom));
                        parts[owner] = SharedValue::Field(fw);
                        wires[idx] = Some(parts);
                    }
                }
            }

            // 5c. `Op::Digit` batched per source domain (`field_to_bits_many`).
            let mut digit_nodes = Vec::new();
            let mut unique_sources: Vec<(usize, usize)> = Vec::new();
            for &idx in comm_nodes {
                if let Op::Digit(a, owner, bit) = c.nodes[idx].op {
                    digit_nodes.push((idx, a, owner, bit));
                    if encodings[a][owner].is_none() && !unique_sources.contains(&(a, owner)) {
                        unique_sources.push((a, owner));
                    }
                }
            }
            for &(a, owner) in &unique_sources {
                if c.nodes[a].domain == Domain::Bit {
                    encodings[a][owner] =
                        Some(vec![wires[a].as_ref().unwrap()[owner].bit()].into());
                }
            }
            for dom in Domain::ALL_FIELDS {
                let mut src_pairs = Vec::new();
                let mut src_refs = Vec::new();
                for &(a, owner) in &unique_sources {
                    if c.nodes[a].domain == dom && encodings[a][owner].is_none() {
                        src_pairs.push((a, owner));
                        src_refs.push(wires[a].as_ref().unwrap()[owner].field());
                    }
                }
                if !src_refs.is_empty() {
                    let converted = e.field_to_bits_many(&src_refs, dom)?;
                    for ((a, owner), bits_w) in src_pairs.into_iter().zip(converted) {
                        encodings[a][owner] = Some(bits_w);
                    }
                }
            }
            for (idx, a, owner, bit) in digit_nodes {
                let mut parts = core::array::from_fn(|_| SharedValue::zero(Domain::Bit));
                parts[owner] = SharedValue::Bit(encodings[a][owner].as_ref().unwrap()[bit]);
                wires[idx] = Some(parts);
            }

            // 5d. Boolean `Op::Mul` batched into a single `e.and`.
            let mut bit_mul_idxs = Vec::new();
            let mut bit_mul_pairs = SecretVec::new();
            for &idx in comm_nodes {
                if c.nodes[idx].domain == Domain::Bit
                    && let Op::Mul(a, b) = c.nodes[idx].op
                {
                    let wa = wires[a].as_ref().unwrap();
                    let wb = wires[b].as_ref().unwrap();
                    bit_mul_idxs.push(idx);
                    for head in 0..3 {
                        let next = (head + 1) % 3;
                        bit_mul_pairs.push((wa[head].bit(), wb[head].bit() ^ wb[next].bit()));
                        bit_mul_pairs.push((wa[next].bit(), wb[head].bit()));
                    }
                }
            }
            if !bit_mul_pairs.is_empty() {
                let prods = e.and(&bit_mul_pairs)?;
                for (idx, chunk) in bit_mul_idxs.into_iter().zip(prods.chunks_exact(6)) {
                    let NodeTape::MulBit { pos } = node_tapes[idx] else {
                        unreachable!()
                    };
                    let m = [
                        squeezed[0][pos[0]],
                        squeezed[1][pos[1]],
                        squeezed[2][pos[2]],
                    ];
                    let parts = core::array::from_fn(|head| {
                        SharedValue::Bit(
                            chunk[2 * head] ^ chunk[2 * head + 1] ^ m[head] ^ m[(head + 1) % 3],
                        )
                    });
                    wires[idx] = Some(parts);
                }
            }

            // 5e. Prime-field `Op::Mul` batched per domain into a single `e.fmul_many`.
            for dom in Domain::ALL_FIELDS {
                let mut fmul_idxs = Vec::new();
                let mut bb_sums: Vec<[FieldWord; 3]> = Vec::new();
                for &idx in comm_nodes {
                    if c.nodes[idx].domain == dom
                        && let Op::Mul(_, b) = c.nodes[idx].op
                    {
                        let wb = wires[b].as_ref().unwrap();
                        fmul_idxs.push(idx);
                        bb_sums.push(core::array::from_fn(|head| {
                            e.fadd(wb[head].field(), wb[(head + 1) % 3].field(), dom)
                        }));
                    }
                }
                if !fmul_idxs.is_empty() {
                    let mut pairs = Vec::with_capacity(fmul_idxs.len() * 6);
                    for (k, &idx) in fmul_idxs.iter().enumerate() {
                        let Op::Mul(a, b) = c.nodes[idx].op else {
                            unreachable!()
                        };
                        let wa = wires[a].as_ref().unwrap();
                        let wb = wires[b].as_ref().unwrap();
                        for head in 0..3 {
                            let next = (head + 1) % 3;
                            pairs.push((wa[head].field(), &bb_sums[k][head]));
                            pairs.push((wa[next].field(), wb[head].field()));
                        }
                    }
                    let prods = e.fmul_many(&pairs, dom)?;
                    for (idx, chunk) in fmul_idxs.into_iter().zip(prods.chunks_exact(6)) {
                        let NodeTape::MulField { draws } = node_tapes[idx] else {
                            unreachable!()
                        };
                        let masks: [FieldWord; 3] = [
                            draw_fields[draws[0]].take().unwrap(),
                            draw_fields[draws[1]].take().unwrap(),
                            draw_fields[draws[2]].take().unwrap(),
                        ];
                        let parts = core::array::from_fn(|head| {
                            let next = (head + 1) % 3;
                            let sum = e.fadd(&chunk[2 * head], &chunk[2 * head + 1], dom);
                            let r = e.fsub(&masks[head], &masks[next], dom);
                            SharedValue::Field(e.fadd(&sum, &r, dom))
                        });
                        wires[idx] = Some(parts);
                    }
                }
            }
        }

        // 5f. Local gates in increasing `index` order.
        for &idx in &wave_local[w] {
            let node = &c.nodes[idx];
            let d = node.domain;
            let val = match node.op {
                Op::Constant(value) => [
                    if d == Domain::Bit {
                        SharedValue::Bit(e.constant(if value[0] == 0 { 0 } else { u64::MAX }))
                    } else {
                        SharedValue::Field(e.fconstant(value, d))
                    },
                    SharedValue::zero(d),
                    SharedValue::zero(d),
                ],
                Op::Input => {
                    let NodeTape::InputBit { witness_idx, pos } = node_tapes[idx] else {
                        unreachable!()
                    };
                    let a = squeezed[0][pos[0]];
                    let b = squeezed[1][pos[1]];
                    let secret = witness[witness_idx];
                    [
                        SharedValue::Bit(a),
                        SharedValue::Bit(b),
                        SharedValue::Bit(secret ^ a ^ b),
                    ]
                }
                Op::Add(a, b) | Op::Sub(a, b) => {
                    let wa = wires[a].as_ref().unwrap();
                    let wb = wires[b].as_ref().unwrap();
                    core::array::from_fn(|head| {
                        if d == Domain::Bit {
                            SharedValue::Bit(wa[head].bit() ^ wb[head].bit())
                        } else if matches!(node.op, Op::Add(..)) {
                            SharedValue::Field(e.fadd(wa[head].field(), wb[head].field(), d))
                        } else {
                            SharedValue::Field(e.fsub(wa[head].field(), wb[head].field(), d))
                        }
                    })
                }
                Op::Scale(a, value) => {
                    let wa = wires[a].as_ref().unwrap();
                    core::array::from_fn(|head| {
                        if d == Domain::Bit {
                            SharedValue::Bit(if value[0] == 0 {
                                E::Bit::default()
                            } else {
                                wa[head].bit()
                            })
                        } else {
                            SharedValue::Field(e.fscale(wa[head].field(), value, d))
                        }
                    })
                }
                Op::Lift(_, _) | Op::Digit(_, _, _) | Op::Mul(_, _) => unreachable!(),
            };
            wires[idx] = Some(val);
        }
        for &dead in &retire_at_wave[w] {
            wires[dead] = None;
        }
    }
    drop(squeezed);
    drop(draw_fields);

    Ok(EvaluatedWires {
        wires,
        #[cfg(test)]
        raw_draw_words,
        #[cfg(test)]
        encodings,
        #[cfg(test)]
        node_tapes,
    })
}

#[cfg(test)]
fn evaluate_inner<E: Core>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: &[Word<E::Bit>],
    verify_zero_outputs: bool,
) -> Result<Vec<SharedView<E::Bit>>, Error> {
    evaluate_inner_with_local(e, c, witness, seeds, verify_zero_outputs, None)
}

#[cfg(test)]
fn evaluate_inner_with_local<E: Core>(
    e: &mut E,
    c: &Circuit,
    witness: &[E::Bit],
    seeds: &[Word<E::Bit>],
    verify_zero_outputs: bool,
    local: Option<&LocalBatchSeeds>,
) -> Result<Vec<SharedView<E::Bit>>, Error> {
    let EvaluatedWires {
        mut wires,
        raw_draw_words,
        mut encodings,
        node_tapes,
    } = evaluate_wires(e, c, witness, Some(seeds), local)?;

    // 5g. Mandatory in-MPC output-residual zero check (`P0-1`): verify that every
    // Boolean and prime-field output residual reconstructs to `0` across all 3 ZKBoo
    // heads BEFORE converting views or opening any output shares / view commitments.
    if verify_zero_outputs {
        check_outputs_zero(e, c, &wires, &c.outputs)?;
    }

    // 6. Batch-convert all remaining `FieldWord`s needed for `views[0..3]` per domain.
    for dom in Domain::ALL_FIELDS {
        let mut to_convert_pairs: Vec<(usize, usize)> = Vec::new();
        for (idx, node) in c.nodes.iter().enumerate() {
            if node.domain != dom {
                continue;
            }
            match node.op {
                Op::Input => {
                    let heads =
                        if local.is_some() || matches!(dom, Domain::PallasFp | Domain::BlsFp) {
                            0..3
                        } else {
                            2..3
                        };
                    for head in heads {
                        if encodings[idx][head].is_none() {
                            to_convert_pairs.push((idx, head));
                        }
                    }
                }
                Op::Mul(_, _) => {
                    for (head, slot) in encodings[idx].iter().enumerate() {
                        if slot.is_none() {
                            to_convert_pairs.push((idx, head));
                        }
                    }
                }
                _ => {}
            }
        }
        for &out in &c.outputs {
            if c.nodes[out].domain == dom {
                for (head, slot) in encodings[out].iter().enumerate() {
                    if slot.is_none() && !to_convert_pairs.contains(&(out, head)) {
                        to_convert_pairs.push((out, head));
                    }
                }
            }
        }
        if !to_convert_pairs.is_empty() {
            let refs: Vec<&FieldWord> = to_convert_pairs
                .iter()
                .map(|&(idx, head)| wires[idx].as_ref().unwrap()[head].field())
                .collect();
            let converted = e.field_to_bits_many(&refs, dom)?;
            for ((idx, head), bits_w) in to_convert_pairs.into_iter().zip(converted) {
                encodings[idx][head] = Some(bits_w);
            }
        }
    }
    for (idx, node) in c.nodes.iter().enumerate() {
        if node.domain != Domain::Bit {
            wires[idx] = None;
        }
    }

    // 7. Assemble `SharedView<E::Bit>`s in exact `c.nodes` / `c.outputs` topological order.
    let input_bits: usize = c
        .nodes
        .iter()
        .filter(|n| matches!(n.op, Op::Input))
        .map(|n| n.domain.width())
        .sum();
    let product_bits: usize = c
        .nodes
        .iter()
        .filter(|n| matches!(n.op, Op::Mul(_, _)))
        .map(|n| n.domain.width())
        .sum();
    let output_bits: usize = c.outputs.iter().map(|&i| c.nodes[i].domain.width()).sum();
    let mut views: Vec<SharedView<E::Bit>> = seeds
        .iter()
        .map(|_seed| SharedView {
            subseeds: SecretVec::new(),
            #[cfg(test)]
            audit_inputs: SecretVec::new(),
            #[cfg(test)]
            seed: _seed.clone(),
            inputs: SecretVec::with_capacity(input_bits.div_ceil(8) * 8),
            products: SecretVec::with_capacity(product_bits.div_ceil(8) * 8),
            outputs: SecretVec::with_capacity(output_bits.div_ceil(8) * 8),
        })
        .collect();

    if local.is_some() {
        for (idx, node) in c.nodes.iter().enumerate() {
            if matches!(node.op, Op::Input | Op::Mul(_, _)) {
                for h in 0..3 {
                    let bit;
                    let bits: &[E::Bit] = if node.domain == Domain::Bit {
                        bit = [wires[idx].as_ref().unwrap()[h].bit()];
                        &bit
                    } else {
                        &encodings[idx][h].as_ref().unwrap()[..node.domain.width()]
                    };
                    if matches!(node.op, Op::Input) {
                        #[cfg(test)]
                        outer_mpc::encode(&mut views[h].audit_inputs, bits);
                        if h == 2 {
                            views[h].inputs.extend_from_slice(bits);
                        }
                    } else {
                        views[h].products.extend_from_slice(bits);
                    }
                }
            }
        }
        for &idx in &c.outputs {
            for h in 0..3 {
                if c.nodes[idx].domain == Domain::Bit {
                    views[h].outputs.push(wires[idx].as_ref().unwrap()[h].bit());
                } else {
                    views[h].outputs.extend_from_slice(
                        &encodings[idx][h].as_ref().unwrap()[..c.nodes[idx].domain.width()],
                    );
                }
            }
        }
        for view in &mut views {
            pad_byte(&mut view.inputs);
            pad_byte(&mut view.products);
            pad_byte(&mut view.outputs);
        }
        return Ok(views);
    }

    for (idx, node) in c.nodes.iter().enumerate() {
        let d = node.domain;
        match node.op {
            Op::Input => {
                if d == Domain::Bit {
                    let w = wires[idx].as_ref().unwrap();
                    for head in 0..3 {
                        outer_mpc::encode(&mut views[head].inputs, &[w[head].bit()]);
                    }
                } else if matches!(d, Domain::PallasFp | Domain::BlsFp) {
                    for head in 0..3 {
                        outer_mpc::encode(
                            &mut views[head].inputs,
                            encodings[idx][head].as_ref().unwrap(),
                        );
                    }
                } else {
                    let NodeTape::InputField { draws, .. } = node_tapes[idx] else {
                        unreachable!()
                    };
                    outer_mpc::encode(&mut views[0].inputs, &raw_draw_words[draws[0]]);
                    outer_mpc::encode(&mut views[1].inputs, &raw_draw_words[draws[1]]);
                    outer_mpc::encode(&mut views[2].inputs, encodings[idx][2].as_ref().unwrap());
                }
            }
            Op::Mul(_, _) => {
                if d == Domain::Bit {
                    let w = wires[idx].as_ref().unwrap();
                    for head in 0..3 {
                        views[head].products.push(w[head].bit());
                    }
                } else {
                    for head in 0..3 {
                        pad_byte(&mut views[head].products);
                        outer_mpc::encode(
                            &mut views[head].products,
                            encodings[idx][head].as_ref().unwrap(),
                        );
                    }
                }
            }
            _ => {}
        }
    }

    for &out in &c.outputs {
        let d = c.nodes[out].domain;
        if d == Domain::Bit {
            let w = wires[out].as_ref().unwrap();
            for head in 0..3 {
                views[head].outputs.push(w[head].bit());
            }
        } else {
            for head in 0..3 {
                pad_byte(&mut views[head].outputs);
                outer_mpc::encode(
                    &mut views[head].outputs,
                    encodings[out][head].as_ref().unwrap(),
                );
            }
        }
    }
    for view in &mut views {
        pad_byte(&mut view.products);
        pad_byte(&mut view.outputs);
    }

    Ok(views)
}

#[cfg(test)]
fn pad_byte<B: ShareBit>(bits: &mut Word<B>) {
    bits.resize(bits.len().div_ceil(8) * 8, B::default());
}

/// Hash borrowed streams in lockstep. All scheduling depends on public lengths;
/// every permutation goes through the actively checked outer MPC.
#[cfg(test)]
fn turbo_shared<E: Core>(
    e: &mut E,
    streams: &[Vec<&[E::Bit]>],
    suffix: u8,
) -> Result<Vec<Word<E::Bit>>, Error> {
    let mut sponges: Vec<_> = streams
        .iter()
        .map(|_| Sponge::from_public_midstate(e, &TURBOSHAKE_VIEW_MIDSTATE))
        .collect();
    let mut cursor = vec![(0usize, 0usize); streams.len()];
    let mut done = vec![false; streams.len()];
    let mut result: Vec<Word<E::Bit>> = streams
        .iter()
        .map(|_| SecretVec::with_capacity(256))
        .collect();
    while done.iter().any(|&d| !d) {
        let mut finishing = vec![false; streams.len()];
        for i in 0..streams.len() {
            if done[i] {
                continue;
            }
            let sp = &mut sponges[i];
            sp.pos = 0;
            let (seg, offset) = &mut cursor[i];
            while sp.pos < 1088 && *seg < streams[i].len() {
                let source = &streams[i][*seg][*offset..];
                let take = (1088 - sp.pos).min(source.len());
                for (dst, &src) in sp.state[sp.pos..sp.pos + take]
                    .iter_mut()
                    .zip(&source[..take])
                {
                    *dst = *dst ^ src;
                }
                sp.pos += take;
                *offset += take;
                if *offset == streams[i][*seg].len() {
                    *seg += 1;
                    *offset = 0;
                }
            }
            if sp.pos < 1088 {
                sp.pad_only(e, suffix);
                finishing[i] = true;
            }
        }
        let mut refs: Vec<_> = sponges
            .iter_mut()
            .enumerate()
            .filter_map(|(i, s)| (!done[i]).then_some(s.state.as_mut_slice()))
            .collect();
        e.permutations_12(&mut refs)?;
        for i in 0..streams.len() {
            if finishing[i] {
                result[i].extend_from_slice(&sponges[i].state[..256]);
                done[i] = true;
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
fn compute_cozk_view_commit_bits<E: Core>(
    e: &mut E,
    batch: usize,
    views: &[SharedView<E::Bit>],
) -> Result<[Word<E::Bit>; 3], Error> {
    let headers: Vec<[Word<E::Bit>; 2]> = views
        .iter()
        .flat_map(|v| {
            (0..COZK_TREE_LEAVES).map(move |leaf| {
                let (start, end) = cozk_product_leaf_range(v.products.len() / 8, leaf);
                (leaf, start, end)
            })
        })
        .map(|(leaf, start, end)| {
            [
                outer_mpc::public_bytes(e, &(leaf as u64).to_le_bytes()),
                outer_mpc::public_bytes(e, &((end - start) as u64).to_le_bytes()),
            ]
        })
        .collect();
    let streams: Vec<Vec<&[E::Bit]>> = headers
        .iter()
        .enumerate()
        .map(|(i, h)| {
            let v = &views[i / COZK_TREE_LEAVES];
            let (start, end) = cozk_product_leaf_range(v.products.len() / 8, i % COZK_TREE_LEAVES);
            vec![&h[0], &h[1], &v.products[start * 8..end * 8]]
        })
        .collect();
    let leaves = turbo_shared(e, &streams, TURBOSHAKE_LEAF_SUFFIX)?;
    let magic = outer_mpc::public_bytes(e, &COZK_VIEW_MAGIC_V4);
    let rep: Word<E::Bit> = (0..64)
        .map(|bit| {
            e.constant((0..64).fold(0, |v, lane| {
                v | ((((batch * 64 + lane) as u64 >> bit) & 1) << lane)
            }))
        })
        .collect();
    let headers: Vec<[Word<E::Bit>; 5]> = views
        .iter()
        .enumerate()
        .map(|(h, v)| {
            [
                outer_mpc::public_bytes(e, &[h as u8]),
                outer_mpc::public_bytes(e, &((v.subseeds.len() / 256) as u64).to_le_bytes()),
                outer_mpc::public_bytes(e, &((v.inputs.len() / 8) as u64).to_le_bytes()),
                outer_mpc::public_bytes(e, &((v.products.len() / 8) as u64).to_le_bytes()),
                outer_mpc::public_bytes(e, &((v.outputs.len() / 8) as u64).to_le_bytes()),
            ]
        })
        .collect();
    let streams: Vec<Vec<&[E::Bit]>> = views
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let h = &headers[i];
            let mut pieces: Vec<&[E::Bit]> = vec![
                &magic,
                &rep,
                &h[0],
                &h[1],
                &v.subseeds,
                &h[2],
                &v.inputs,
                &h[3],
            ];
            pieces.extend(
                leaves[i * COZK_TREE_LEAVES..(i + 1) * COZK_TREE_LEAVES]
                    .iter()
                    .map(|w| w.as_slice()),
            );
            pieces.extend([h[4].as_slice(), v.outputs.as_slice()]);
            pieces
        })
        .collect();
    let mut hashes = turbo_shared(e, &streams, TURBOSHAKE_ROOT_SUFFIX)?.into_iter();
    Ok(core::array::from_fn(|_| hashes.next().unwrap()))
}

#[cfg(test)]
/// Compute the 256-bit `cSHAKE256("QSAG.MIGRATE.VIEW.V3")` view commitment shares
/// for all 3 virtual heads in lockstep (`3x` fewer network rounds than sequential
/// sponges, `0` rounds for the public customization block, `0` intermediate stream
/// allocations, and `0` wire openings).
fn compute_view_commit_bits<E: Core>(
    e: &mut E,
    batch: usize,
    views: &[SharedView<E::Bit>],
) -> Result<[Word<E::Bit>; 3], Error> {
    let rep: Word<E::Bit> = (0..64)
        .map(|bit| {
            e.constant((0..64).fold(0, |v, lane| {
                v | ((((batch * 64 + lane) as u64 >> bit) & 1) << lane)
            }))
        })
        .collect();
    let count6 = outer_mpc::public_bytes(e, &6u64.to_le_bytes());
    let head_bits: [Word<E::Bit>; 3] =
        core::array::from_fn(|head| outer_mpc::public_bytes(e, &[head as u8]));
    let len_words =
        |bit_len: usize| outer_mpc::public_bytes(e, &((bit_len / 8) as u64).to_le_bytes());
    let len_rep = len_words(rep.len());
    let len_head = len_words(head_bits[0].len());
    let len_seed = len_words(views[0].seed.len());
    let len_in = len_words(views[0].inputs.len());
    let len_prod = len_words(views[0].products.len());
    let len_out = len_words(views[0].outputs.len());

    let mut sponges: [Sponge<E::Bit>; 3] =
        core::array::from_fn(|_| Sponge::cshake_public(e, b"QSAG.MIGRATE.VIEW.V3"));

    let segments: [[&[E::Bit]; 3]; 13] = [
        [&count6, &count6, &count6],
        [&len_rep, &len_rep, &len_rep],
        [&rep, &rep, &rep],
        [&len_head, &len_head, &len_head],
        [&head_bits[0], &head_bits[1], &head_bits[2]],
        [&len_seed, &len_seed, &len_seed],
        [&views[0].seed, &views[1].seed, &views[2].seed],
        [&len_in, &len_in, &len_in],
        [&views[0].inputs, &views[1].inputs, &views[2].inputs],
        [&len_prod, &len_prod, &len_prod],
        [&views[0].products, &views[1].products, &views[2].products],
        [&len_out, &len_out, &len_out],
        [&views[0].outputs, &views[1].outputs, &views[2].outputs],
    ];

    for segs in segments {
        debug_assert_eq!(segs[0].len(), segs[1].len());
        debug_assert_eq!(segs[0].len(), segs[2].len());
        let seg_len = segs[0].len();
        let mut offset = 0usize;
        while offset < seg_len {
            let pos = sponges[0].pos;
            let take = (1088 - pos).min(seg_len - offset);
            for h in 0..3 {
                let dst = &mut sponges[h].state[pos..pos + take];
                let src = &segs[h][offset..offset + take];
                for (d, &s) in dst.iter_mut().zip(src) {
                    *d = *d ^ s;
                }
                sponges[h].pos = pos + take;
            }
            offset += take;
            if sponges[0].pos == 1088 {
                for sp in &mut sponges {
                    sp.pos = 0;
                }
                let (s0, rest) = sponges.split_first_mut().unwrap();
                let (s1, rest2) = rest.split_first_mut().unwrap();
                let s2 = &mut rest2[0];
                e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
            }
        }
    }

    for sp in &mut sponges {
        sp.pad_only(e, 0x04);
    }
    {
        let (s0, rest) = sponges.split_first_mut().unwrap();
        let (s1, rest2) = rest.split_first_mut().unwrap();
        let s2 = &mut rest2[0];
        e.permutations(&mut [&mut s0.state, &mut s1.state, &mut s2.state])?;
    }

    Ok(core::array::from_fn(|h| {
        sponges[h].state[..256].iter().copied().collect()
    }))
}

#[cfg(test)]
fn commit_views<E: Core>(
    e: &mut E,
    batch: usize,
    views: &[SharedView<E::Bit>],
) -> Result<Vec<Vec<u64>>, Error> {
    let bits = compute_view_commit_bits(e, batch, views)?;
    bits.iter().map(|b| e.open(b)).collect()
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use crate::{
        circuit::Builder,
        legacy::LegacyOwnershipWitness,
        outer_mpc::{
            Bit, FaultInjection,
            tests::{Network, audited_networks, keys, run},
        },
    };
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };

    // Run the concrete former XOR attack with the live custody state, outer
    // input replicas and actual verified published proof available. This is a
    // regression for that attack, not an exhaustive adversarial computation.
    pub(super) fn audit_old_attack<T: Transport>(
        state: &CoZkCustodianShare,
        engine: &Engine<T>,
        physical_input: &[Bit],
        inputs: &[[Word; 3]],
        proof: &MigrationZkProof,
    ) {
        let Some((messages, words)) = engine.transport.audit_transcript() else {
            return;
        };
        let mut candidates = Vec::with_capacity(MIT_REPETITIONS * 3);
        assert_eq!(state.party, engine.party);
        assert!(physical_input.len() == 256 || physical_input.len() == 512);
        assert!(messages > 0 && words > 0);
        for (rep, opening) in proof.repetitions.iter().enumerate() {
            let e = opening.opened_e as usize;
            let hidden = (e + 2) % 3;
            let published_inputs: [Vec<u8>; 2] = core::array::from_fn(|j| {
                let head = (e + j) % 3;
                let (seeds, input) = zk_engine::parse_cozk_v4_inputs(&opening.pair[j]).unwrap();
                if head == 2 {
                    (0..256).map(|i| (input[i / 8] >> (i % 8)) & 1).collect()
                } else {
                    let mut tape = zk_engine::MultiTape::new(&seeds);
                    (0..256)
                        .map(|_| tape.sample(Domain::Bit)[0] as u8)
                        .collect()
                }
            });
            let lane = rep % 64;
            for components in [1, 2, 3] {
                let partial: Vec<_> = inputs[rep / 64][hidden]
                    .iter()
                    .map(|b| match components {
                        1 => b.0[0],
                        2 => b.0[1],
                        _ => b.0[0] ^ b.0[1],
                    })
                    .collect();
                let local = outer_mpc::lane_bytes(&partial, lane);
                let mut recovered = [0u8; 32];
                for bit in 0..256 {
                    recovered[bit / 8] |=
                        (local[bit] ^ published_inputs[0][bit] ^ published_inputs[1][bit])
                            << (bit % 8);
                }
                candidates.push(recovered);
            }
            if e != state.party {
                let locals: [[Vec<u8>; 3]; 2] = core::array::from_fn(|j| {
                    core::array::from_fn(|mask| {
                        let partial: Vec<_> = inputs[rep / 64][(state.party + j) % 3]
                            .iter()
                            .map(|b| match mask {
                                0 => b.0[0],
                                1 => b.0[1],
                                _ => b.0[0] ^ b.0[1],
                            })
                            .collect();
                        outer_mpc::lane_bytes(&partial, lane)
                    })
                });
                let missing = (state.party + 2) % 3;
                let published = &published_inputs[usize::from(e != missing)];
                for a in &locals[0] {
                    for b in &locals[1] {
                        let mut recovered = [0u8; 32];
                        for bit in 0..256 {
                            recovered[bit / 8] |= (a[bit] ^ b[bit] ^ published[bit]) << (bit % 8);
                        }
                        candidates.push(recovered);
                    }
                }
            }
            for view in &published_inputs {
                let mut recovered = [0u8; 32];
                for bit in 0..256 {
                    let local = ((physical_input[bit].0[0] ^ physical_input[bit].0[1]) >> lane) & 1;
                    recovered[bit / 8] |= ((local as u8) ^ view[bit]) << (bit % 8);
                }
                candidates.push(recovered);
            }
        }
        engine.transport.audit_candidates(candidates);
    }

    #[test]
    fn canonical_tapes_reject_boundary_words_without_aborting_or_losing_cached_bits() {
        use qsag_accel::goldilocks::GOLDILOCKS_PRIME;
        run(|p, n| {
            let mut e = Engine::new(p, [0x61; 32], keys(p), n).unwrap();
            let draws: Vec<_> = [64, 128, 256]
                .into_iter()
                .flat_map(|start| {
                    (0..3).map(move |head| FieldTapeDraw {
                        head,
                        start,
                        domain: Domain::Gold,
                    })
                })
                .collect();
            let counts = [320; 3];
            let required = tape_counts(&draws, counts, 4).unwrap();
            let value = |head: usize, lane: usize, word: usize| {
                let rejects = (head + lane) % 4;
                if word > 0 && word <= rejects {
                    [GOLDILOCKS_PRIME, GOLDILOCKS_PRIME + 1, u64::MAX][word - 1]
                } else if word == rejects + 1 {
                    GOLDILOCKS_PRIME - 1
                } else {
                    (word + 100 * head + 1000 * lane) as u64
                }
            };
            let streams: Vec<_> = (0..3)
                .map(|head| {
                    let words: Vec<_> = (0..required[head])
                        .map(|bit| {
                            if p != 0 {
                                return 0;
                            }
                            (0..64).fold(0, |acc, lane| {
                                acc | (((value(head, lane, bit / 64) >> (bit % 64)) & 1) << lane)
                            })
                        })
                        .collect();
                    e.share(&words).unwrap()
                })
                .collect();
            // Two consecutive boundary words exceed this attempt budget, but are
            // not an invalid tape: the caller extends the PRG and replays it.
            assert!(
                canonical_tape_attempt(&mut e, &streams, &draws, counts, 2)
                    .unwrap()
                    .is_none()
            );
            let repaired = canonical_tape_attempt(&mut e, &streams, &draws, counts, 4)
                .unwrap()
                .unwrap();
            for (head, stream) in repaired.iter().enumerate() {
                assert_eq!(stream.len(), counts[head]);
                let opened = e.open(stream).unwrap();
                for lane in 0..64 {
                    let mut cursor = 1;
                    let mut expected = vec![value(head, lane, 0)];
                    for slot in 1..5 {
                        loop {
                            let v = value(head, lane, cursor);
                            cursor += 1;
                            if slot == 3 || v < GOLDILOCKS_PRIME {
                                expected.push(v);
                                break;
                            }
                        }
                    }
                    let bytes = outer_mpc::lane_bytes(&opened, lane);
                    let actual: Vec<_> = bytes
                        .chunks_exact(8)
                        .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
                        .collect();
                    assert_eq!(actual, expected, "head {head}, lane {lane}");
                }
            }
            let short: Vec<Word> = streams
                .iter()
                .map(|s| s[..320].iter().copied().collect())
                .collect();
            assert!(matches!(
                canonical_tape_attempt(&mut e, &short, &draws, counts, 4),
                Err(Error::InvalidTape)
            ));
            assert!(matches!(
                canonical_tape_attempt(&mut e, &streams[..2], &draws, counts, 4),
                Err(Error::InvalidTape)
            ));
            assert_eq!(tape_counts(&draws, counts, 0), Err(Error::InvalidTape));
            assert_eq!(
                tape_counts(&draws, counts, usize::MAX),
                Err(Error::InvalidTape)
            );
            let malformed = [FieldTapeDraw {
                head: 3,
                start: 0,
                domain: Domain::Gold,
            }];
            assert_eq!(tape_counts(&malformed, counts, 2), Err(Error::InvalidTape));
        });
    }

    /// Head 2 reads one 64-bit Boolean word, then 66 Goldilocks masks (two for
    /// the lift, 64 for the products), then a second Boolean word. For this seed
    /// exactly one raw word in that range is not canonical, so the shared tape
    /// has to skip it and move every later draw and the Boolean refill up by one
    /// word, as `zk_engine::Tape` does.
    #[test]
    fn a_real_seed_with_a_rejected_goldilocks_word_gives_the_native_views() {
        use qsag_accel::goldilocks::GOLDILOCKS_PRIME;
        const PRODUCTS: u64 = 64;
        const GOLD_DRAWS: usize = PRODUCTS as usize + 2;
        const SEED: [u8; 32] = *b"QSAG.TAPE.REJECT\x02\x35\x26\0\0\0\0\0\0\0\0\0\0\0\0\x04";
        const REJECTED_WORD: usize = 27;

        let mut raw = [0u8; 8 * (GOLD_DRAWS + 3)];
        crate::tape_sponge::TapeSponge::new(&SEED).squeeze(&mut raw);
        let rejected: Vec<usize> = raw
            .chunks_exact(8)
            .enumerate()
            .skip(1)
            .filter(|(_, w)| u64::from_le_bytes((*w).try_into().unwrap()) >= GOLDILOCKS_PRIME)
            .map(|(i, _)| i)
            .collect();
        assert_eq!(rejected, [REJECTED_WORD]);
        assert!((1..=GOLD_DRAWS).contains(&REJECTED_WORD));

        let clear_seeds = [[1; 32], [2; 32], SEED];
        run(|p, n| {
            let mut e = Engine::new(p, [52; 32], keys(p), n).unwrap();
            let c = Builder::default();
            let bit = c.input(1);
            c.output(c.mul(bit, bit));
            let a = c.lift(bit, Domain::Gold);
            let b = c.add(a, c.small(Domain::Gold, 27));
            for i in 0..PRODUCTS {
                c.output(c.mul(c.add(a, c.small(Domain::Gold, 3 + i)), b));
            }
            for _ in 0..70 {
                c.output(c.mul(bit, bit));
            }
            let c = c.finish();
            let muls = |d| {
                c.nodes
                    .iter()
                    .filter(|n| n.domain == d && matches!(n.op, Op::Mul(_, _)))
                    .count()
            };
            assert_eq!((muls(Domain::Bit), muls(Domain::Gold)), (71, GOLD_DRAWS));
            let witness = e.share(&[if p == 0 { u64::MAX } else { 0 }]).unwrap();
            let seeds: Vec<_> = clear_seeds
                .iter()
                .map(|seed| {
                    let own: Vec<u64> = (0..256)
                        .map(|i| {
                            if p == 0 && (seed[i / 8] >> (i % 8)) & 1 != 0 {
                                u64::MAX
                            } else {
                                0
                            }
                        })
                        .collect();
                    e.share(&own).unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let native = zk_engine::simulate(&c, clear_seeds);
            for (head, view) in views.iter().enumerate() {
                let opened = e.open(&view.bytes()).unwrap();
                let expected: Vec<_> = [
                    native[head].seed.as_slice(),
                    &native[head].inputs,
                    &native[head].products,
                    &native[head].outputs,
                ]
                .concat();
                for lane in [0, 37, 63] {
                    assert_eq!(outer_mpc::lane_bytes(&opened, lane), expected);
                }
            }
        });
    }

    fn check_v4_batch<E: Core>(e: &mut E) {
        let (p, m) = e.quorum_position();
        let c = Builder::default();
        let bit = c.input(1);
        for d in Domain::ALL_FIELDS {
            c.output(c.mul(bit, bit));
            let a = c.lift(bit, d);
            let z = c.mul(a, c.small(d, 27));
            c.output(z);
            c.output(c.inverse(z));
        }
        let c = c.finish();
        let witness = e.share(&[if p == 0 { u64::MAX } else { 0 }]).unwrap();
        let seeds = LocalBatchSeeds {
            subseeds: Secret(core::array::from_fn(|h| {
                core::array::from_fn(|lane| [((p * 11 + h * 3 + lane) % 256) as u8; 32])
            })),
            salts: Secret([[[0; 32]; 64]; 3]),
        };
        let empty = core::array::from_fn::<_, 3, _>(|_| SecretVec::new());
        let mut views =
            evaluate_inner_with_local(e, &c, &witness, &empty, false, Some(&seeds)).unwrap();
        for (h, view) in views.iter_mut().enumerate() {
            let own: Vec<u64> = (0..m * 256)
                .map(|i| {
                    if i / 256 != p {
                        return 0;
                    }
                    (0..64).fold(0, |v, lane| {
                        v | (u64::from((seeds.subseeds[h][lane][(i % 256) / 8] >> (i % 8)) & 1)
                            << lane)
                    })
                })
                .collect();
            view.subseeds = e.share_masked(&own).unwrap();
        }
        let commitments = compute_cozk_view_commit_bits(e, 0, &views).unwrap();
        let typed = evaluate_typed_views(e, &c, &witness, &seeds, false).unwrap();
        let masked = mask_shared_views(e, 0, &seeds, &typed).unwrap();
        let peer_commits: Vec<Vec<u8>> = (0..m)
            .map(|p| {
                let mut row = vec![0u8; MIT_REPETITIONS * 3 * 64];
                for rep in 0..64 {
                    for h in 0..3 {
                        let seed = [((p * 11 + h * 3 + rep) % 256) as u8; 32];
                        let offset = (rep * 3 + h) * 64 + 32;
                        row[offset..offset + 32].copy_from_slice(
                            &crate::batch_hash::cozk_seed_commit(rep, h, p, &seed),
                        );
                    }
                }
                row
            })
            .collect();
        let v5_rounds = open_batch_public_rounds(e, 0, &masked, &typed, &peer_commits).unwrap();
        // Field openings must erase every unchallenged lane before the
        // authenticated open, on both replicated and Shamir backends.
        let selected = (1u64 << 17) | (1u64 << 63);
        let selected_products: Vec<_> = typed.iter().map(|v| open_typed_values(e, &v.products, selected).unwrap()).collect();
        for products in &selected_products {
            for (lane, bytes) in products.iter().enumerate() {
                if (selected >> lane) & 1 == 0 { assert!(bytes.iter().all(|&b| b == 0)); }
            }
        }
        let opened_commits: Vec<_> = commitments.iter().map(|w| e.open(w).unwrap()).collect();
        let opened_views: Vec<_> = views
            .iter()
            .map(|v| {
                (
                    e.open(&v.inputs).unwrap(),
                    e.open(&v.products).unwrap(),
                    e.open(&v.outputs).unwrap(),
                )
            })
            .collect();
        for lane in [0, 17, 63] {
            let all_seeds = core::array::from_fn(|h| {
                (0..m)
                    .map(|p| [((p * 11 + h * 3 + lane) % 256) as u8; 32])
                    .collect()
            });
            let native = zk_engine::simulate_cozk_v4(&c, &all_seeds);
            for h in 0..3 {
                let (subseeds, input) = zk_engine::parse_cozk_v4_inputs(&native[h]).unwrap();
                let indexed = crate::batch_hash::CozkIndexedView {
                    rep: lane,
                    head: h,
                    subseeds,
                    head_inputs: input,
                    products: &native[h].products,
                    outputs: &native[h].outputs,
                };
                assert_eq!(
                    v5_rounds[lane].commits[h],
                    crate::batch_hash::commit_cozk_v5_indexed(&[indexed], &crate::batch_hash::CozkViewLayout::new(&c)).unwrap()[0]
                );
                assert_eq!(v5_rounds[lane].outputs[h], native[h].outputs);
                if (selected >> lane) & 1 != 0 { assert_eq!(selected_products[h][lane], native[h].products); }
                assert_eq!(outer_mpc::lane_bytes(&opened_views[h].0, lane), input);
                assert_eq!(
                    outer_mpc::lane_bytes(&opened_views[h].1, lane),
                    native[h].products
                );
                assert_eq!(
                    outer_mpc::lane_bytes(&opened_views[h].2, lane),
                    native[h].outputs
                );
                assert_eq!(
                    outer_mpc::lane_bytes(&opened_commits[h], lane),
                    zk_engine::commit_cozk_v4(lane, h, &native[h])
                );
            }
        }
    }

    #[test]
    fn cozk_v4_replicated_tapes_and_tree_match_native_all_domains() {
        run(|p, t| check_v4_batch(&mut Engine::new(p, [0x62; 32], keys(p), t).unwrap()));
    }

    #[test]
    fn cozk_v4_quorum_tapes_and_tree_match_native_all_domains() {
        use crate::threshold_mpc::tests as quorum;
        let config = ThresholdConfig::new(2, 3, vec![0, 2]).unwrap();
        quorum::run(config.clone(), |p, mac, t| {
            check_v4_batch(&mut quorum::engine(&config, p, mac, t))
        });
    }

    #[test]
    fn shared_views_and_commitments_are_byte_identical_to_native() {
        run(|p, n| {
            let mut e = Engine::new(p, [51; 32], keys(p), n).unwrap();
            let c = Builder::default();
            let bit = c.input(1);
            for (d, count) in [
                (Domain::Gold, 1),
                (Domain::Secp, 8),
                (Domain::Ed, 9),
                (Domain::PallasFp, 3),
                (Domain::BlsFp, 5),
            ] {
                for _ in 0..count {
                    c.output(c.mul(bit, bit));
                }
                let a = c.lift(bit, d);
                let b = c.add(a, c.small(d, 27));
                let z = c.mul(a, b);
                c.output(z);
                if matches!(d, Domain::Gold | Domain::PallasFp | Domain::BlsFp) {
                    let inverse = c.inverse(z);
                    c.output(inverse);
                }
                for b in c.bits(z) {
                    c.output(b);
                }
            }
            for _ in 0..9 {
                c.output(c.mul(bit, bit));
            }
            let c = c.finish();
            let witness = e.share(&[if p == 0 { u64::MAX } else { 0 }]).unwrap();
            let seeds: Vec<_> = (0..3)
                .map(|head| {
                    e.share(
                        &(0..256)
                            .map(|i| {
                                if ((p + head + 1) >> (i % 8)) & 1 != 0 {
                                    u64::MAX
                                } else {
                                    0
                                }
                            })
                            .collect::<Vec<_>>(),
                    )
                    .unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let commitments = commit_views(&mut e, 0, &views).unwrap();
            let clear_seeds: Vec<[u8; 32]> = seeds
                .iter()
                .map(|s| {
                    outer_mpc::lane_bytes(&e.open(s).unwrap(), 0)
                        .try_into()
                        .unwrap()
                })
                .collect();
            let native = zk_engine::simulate(&c, clear_seeds.try_into().unwrap());
            for (head, view) in views.iter().enumerate() {
                let bytes = outer_mpc::lane_bytes(&e.open(&view.bytes()).unwrap(), 0);
                let expected: Vec<_> = [
                    native[head].seed.as_slice(),
                    &native[head].inputs,
                    &native[head].products,
                    &native[head].outputs,
                ]
                .concat();
                assert_eq!(bytes, expected);
                for lane in 0..64 {
                    assert_eq!(
                        outer_mpc::lane_bytes(&commitments[head], lane),
                        zk_engine::commit(lane, head, &native[head])
                    );
                }
            }
        });
    }

    #[test]
    fn quorum_shamir_views_and_commitments_match_native() {
        use crate::threshold_mpc::tests as quorum;
        let config = ThresholdConfig::new(3, 8, vec![1, 4, 7]).unwrap();
        quorum::run(config.clone(), |party, mac_keys, transport| {
            let witness_bytes = [1; 32];
            let contribution = config
                .shamir_contribution(party, &quorum::shamir_share(party, 3, &witness_bytes))
                .unwrap();
            let mut e = quorum::engine(&config, party, mac_keys, transport);
            let c = Builder::default();
            let bit = c.input(1);
            c.output(c.mul(bit, bit));
            for dom in [Domain::Gold, Domain::PallasFp, Domain::BlsFp] {
                let lifted = c.lift(bit, dom);
                let value = c.mul(lifted, c.small(dom, 7));
                let inv = c.inverse(value);
                c.output(value);
                c.output(inv);
                for b in c.bits(value) {
                    c.output(b);
                }
            }
            let c = c.finish();
            let witness = e
                .share_uniform_lanes(&[if contribution[0] & 1 != 0 {
                    u64::MAX
                } else {
                    0
                }])
                .unwrap();
            let seeds: Vec<_> = (0..3)
                .map(|head| {
                    let bytes = cshake256_framed_32(b"QUORUM.VIEW.TEST", &[&[party as u8, head]]);
                    let bits: Vec<_> = bytes
                        .iter()
                        .flat_map(|b| {
                            (0..8).map(move |i| if (b >> i) & 1 != 0 { u64::MAX } else { 0 })
                        })
                        .collect();
                    e.share(&bits).unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let commitments = commit_views(&mut e, 0, &views).unwrap();
            let clear_seeds: Vec<[u8; 32]> = seeds
                .iter()
                .map(|s| {
                    outer_mpc::lane_bytes(&e.open(s).unwrap(), 0)
                        .try_into()
                        .unwrap()
                })
                .collect();
            let native = zk_engine::simulate(&c, clear_seeds.try_into().unwrap());
            for (head, view) in views.iter().enumerate() {
                let bytes = outer_mpc::lane_bytes(&e.open(&view.bytes()).unwrap(), 0);
                let expected: Vec<_> = [
                    native[head].seed.as_slice(),
                    &native[head].inputs,
                    &native[head].products,
                    &native[head].outputs,
                ]
                .concat();
                assert_eq!(bytes, expected);
                for lane in 0..64 {
                    assert_eq!(
                        outer_mpc::lane_bytes(&commitments[head], lane),
                        zk_engine::commit(lane, head, &native[head])
                    );
                }
            }
        });
    }

    #[test]
    fn published_pairs_do_not_complete_local_outer_shares_over_64_witnesses() {
        let witnesses: Vec<_> = (0..64u64)
            .map(|i| cshake256_framed_32(b"OUTER.PRIVACY.WITNESS", &[&i.to_le_bytes()]))
            .collect();
        run(|p, n| {
            let mut e = Engine::new(p, [53; 32], keys(p), n).unwrap();
            let c = Builder::default();
            for _ in 0..256 {
                c.input(0);
            }
            let c = c.finish();
            let own: Vec<_> = (0..256)
                .map(|i| {
                    (0..64).fold(0, |v, lane| {
                        let a = cshake256_framed_32(b"OUTER.PRIVACY.SHARE", &[&[0, lane as u8]]);
                        let b = cshake256_framed_32(b"OUTER.PRIVACY.SHARE", &[&[1, lane as u8]]);
                        let x = match p {
                            0 => a[i / 8],
                            1 => b[i / 8],
                            _ => witnesses[lane][i / 8] ^ a[i / 8] ^ b[i / 8],
                        };
                        v | ((((x >> (i % 8)) & 1) as u64) << lane)
                    })
                })
                .collect();
            let witness = e.share(&own).unwrap();
            let seeds: Vec<_> = (0..3u8)
                .map(|head| {
                    let own: Vec<_> = (0..256)
                        .map(|i| {
                            (0..64).fold(0, |v, lane| {
                                let seed = cshake256_framed_32(
                                    b"OUTER.PRIVACY.SEED",
                                    &[&[p as u8, head, lane as u8]],
                                );
                                v | ((((seed[i / 8] >> (i % 8)) & 1) as u64) << lane)
                            })
                        })
                        .collect();
                    e.share(&own).unwrap()
                })
                .collect();
            let views = evaluate(&mut e, &c, &witness, &seeds).unwrap();
            let published: Vec<_> = views
                .iter()
                .enumerate()
                .map(|(head, v)| {
                    let mask = (0..64).fold(0, |m, lane| {
                        if (lane % 3 + 2) % 3 != head {
                            m | (1u64 << lane)
                        } else {
                            m
                        }
                    });
                    let bits: Word = v
                        .inputs
                        .iter()
                        .map(|b| Bit([b.0[0] & mask, b.0[1] & mask]))
                        .collect();
                    e.open(&bits).unwrap()
                })
                .collect();
            for (lane, expected) in witnesses.iter().enumerate() {
                let hidden = (lane % 3 + 2) % 3;
                for components in [1u8, 2, 3] {
                    let partial: Vec<_> = views[hidden]
                        .inputs
                        .iter()
                        .map(|b| {
                            if components == 1 {
                                b.0[0]
                            } else if components == 2 {
                                b.0[1]
                            } else {
                                b.0[0] ^ b.0[1]
                            }
                        })
                        .collect();
                    let local = outer_mpc::lane_bytes(&partial, lane);
                    let a = outer_mpc::lane_bytes(&published[lane % 3], lane);
                    let b = outer_mpc::lane_bytes(&published[(lane % 3 + 1) % 3], lane);
                    let mut recovered = [0u8; 32];
                    for i in 0..256 {
                        recovered[i / 8] |= (local[i] ^ a[i] ^ b[i]) << (i % 8);
                    }
                    assert_ne!(
                        &recovered, expected,
                        "custodian {p}, lane {lane}, components {components}"
                    );
                }
            }
        });
    }

    // The six `complete_distributed_*` tests each run one full 438-repetition
    // ceremony: 2,000 to 4,500 CPU-seconds and up to 10 GB. They are ignored by
    // default and run one at a time by name with `--ignored`.
    //
    // Bound concurrent ceremonies by the batch engines they run at once, so
    // the suite stays within the host's cores and the builder memory budget.
    // A full ceremony takes `parallel_batches()` units per custodian; a
    // single-stream one takes one and may overlap a full ceremony.
    static HEAVY_CEREMONIES: (std::sync::Mutex<usize>, std::sync::Condvar) =
        (std::sync::Mutex::new(0), std::sync::Condvar::new());
    struct CeremonySlot(usize);
    impl CeremonySlot {
        fn acquire(batches: usize) -> Self {
            let (active, ready) = &HEAVY_CEREMONIES;
            let mut count = active.lock().unwrap_or_else(|e| e.into_inner());
            let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
            let limit = (cores / 3).max(outer_mpc::tests::parallel_batches()) + 2;
            while *count + batches > limit {
                count = ready.wait(count).unwrap_or_else(|e| e.into_inner());
            }
            *count += batches;
            Self(batches)
        }
    }
    impl Drop for CeremonySlot {
        fn drop(&mut self) {
            let (active, ready) = &HEAVY_CEREMONIES;
            *active.lock().unwrap_or_else(|e| e.into_inner()) -= self.0;
            ready.notify_all();
        }
    }

    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_bitcoin_proof_verifies() {
        complete_proof(false);
    }

    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_ed25519_proof_verifies() {
        complete_proof(true);
    }

    fn complete_proof(ed: bool) {
        use std::io::Read;
        let _ceremony_guard = CeremonySlot::acquire(outer_mpc::tests::parallel_batches());
        let mut master = [0u8; 32];
        std::fs::File::open("/dev/urandom")
            .unwrap()
            .read_exact(&mut master)
            .unwrap();
        let derive = |label: &[u8], id: u8| cshake256_framed_32(label, &[&master, &[id]]);
        let witness =
            LegacyOwnershipWitness::from_raw_secret(derive(b"OUTER.FULL.WITNESS", u8::from(ed)));
        let kind = if ed {
            witness.compute_slip0010_commitment()
        } else {
            witness.compute_bitcoin_hash160().unwrap()
        };
        let request = zk_engine::tests::request(kind);
        let scalar = witness.normalize_spending_scalar(&kind).unwrap();
        let statement = MigrationStatement {
            legacy_commitment: kind,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        let mut parts = [
            derive(b"OUTER.FULL.INPUT", 0),
            derive(b"OUTER.FULL.INPUT", 1),
            *scalar.as_le_bytes(),
        ];
        let masks = [parts[0], parts[1]];
        for (i, byte) in parts[2].iter_mut().enumerate() {
            *byte ^= masks[0][i] ^ masks[1][i];
        }
        let session = derive(b"OUTER.FULL.SESSION", 0);
        let pair_keys: [_; 3] = core::array::from_fn(|p| derive(b"OUTER.FULL.PAIR.KEY", p as u8));
        let entropy: [_; 3] = core::array::from_fn(|p| derive(b"OUTER.FULL.ENTROPY", p as u8));
        ct_zeroize_bytes(&mut master);
        let states: [_; 3] = core::array::from_fn(|p| {
            CoZkCustodianShare::new(
                p,
                session,
                parts[p],
                entropy[p],
                [pair_keys[(p + 2) % 3], pair_keys[p]],
            )
            .unwrap()
        });
        let start = std::time::Instant::now();
        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = states
                .into_iter()
                .zip(audited_networks())
                .map(|(state, (network, audit))| {
                    let public = statement.clone();
                    scope.spawn(move || (state.prove(&public, network), audit))
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });
        let mut errors = Vec::new();
        for (party, (result, audit)) in outcomes.into_iter().enumerate() {
            match result {
                Ok(proof) => {
                    zk_engine::verify_migration_proof(
                        &statement,
                        &proof,
                        &statement.migration_domain,
                        statement.epoch_anchor,
                    )
                    .unwrap();
                    let candidates = audit.candidates();
                    let former_attack_rounds = proof
                        .repetitions
                        .iter()
                        .filter(|r| r.opened_e as usize != party)
                        .count();
                    assert_eq!(
                        candidates.len(),
                        MIT_REPETITIONS * 5 + former_attack_rounds * 9
                    );
                    for recovered in candidates {
                        assert_ne!(&recovered, scalar.as_le_bytes());
                    }
                }
                Err(error) => errors.push(error),
            }
        }
        assert!(errors.is_empty(), "unexpected errors: {errors:?}");
        std::eprintln!(
            "distributed 438-rep {}: {:?}",
            if ed { "Ed25519" } else { "Bitcoin HASH160" },
            start.elapsed()
        );
    }

    #[test]
    fn one_custodian_valid_mac_equivocation_aborts_every_output() {
        struct Equivocate(Network);
        impl Transport for Equivocate {
            fn exchange(&mut self, mut outgoing: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
                if outgoing[0].sender == 0 && outgoing[0].sequence == 0 {
                    let m = &mut outgoing[0];
                    m.payload[0] ^= 1;
                    let bytes: Vec<_> = m.payload.iter().flat_map(|w| w.to_le_bytes()).collect();
                    m.tag = cshake256_framed_32(
                        b"QSAG.OUTER.MESSAGE.V1",
                        &[
                            &keys(0)[0],
                            &[62; 32],
                            &[m.sender as u8, m.recipient as u8],
                            &m.sequence.to_le_bytes(),
                            &bytes,
                        ],
                    );
                }
                self.0.exchange(outgoing)
            }
        }
        let witness = LegacyOwnershipWitness::from_raw_secret([7; 32]);
        let kind = witness.compute_bitcoin_hash160().unwrap();
        let request = zk_engine::tests::request(kind);
        let scalar = witness.normalize_spending_scalar(&kind).unwrap();
        let statement = MigrationStatement {
            legacy_commitment: kind,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        run(|p, n| {
            let result =
                CoZkCustodianShare::new(p, [62; 32], [0; 32], [(p + 1) as u8; 32], keys(p))
                    .unwrap()
                    .prove(&statement, Equivocate(n));
            if p == 2 {
                assert!(matches!(result, Err(Error::Disagreement(0))));
            } else {
                assert!(matches!(result, Err(Error::Transport)));
            }
        });
    }

    const PRECOMMIT_SEQ: u64 = 4;

    struct ZkbooFaultSpy {
        inner: Network,
        is_root: bool,
        /// Offer no batch streams: the root engine evaluates the batches one
        /// after another on the root stream.
        single_stream: bool,
        fault: Option<FaultInjection>,
        precommit_or_view_opened: Arc<AtomicBool>,
    }
    impl Transport for ZkbooFaultSpy {
        fn max_parallel_batches(&self) -> usize {
            outer_mpc::tests::parallel_batches()
        }

        fn test_fault_raw(&self) -> Option<[usize; 4]> {
            self.fault.map(FaultInjection::to_raw)
        }
        fn on_public_or_view_open(&self) {
            self.precommit_or_view_opened.store(true, Ordering::SeqCst);
        }
        fn fork(&mut self, batch: usize) -> Option<Self> {
            if self.single_stream {
                return None;
            }
            self.inner.fork(batch).map(|child| Self {
                inner: child,
                is_root: false,
                single_stream: false,
                // Inject the fault ONLY in batch 2 so all other batches are clean,
                // proving the cross-batch barrier also blocks clean batches from opening!
                fault: if batch == 2 { self.fault } else { None },
                precommit_or_view_opened: self.precommit_or_view_opened.clone(),
            })
        }
        fn exchange(&mut self, out: [Envelope; 2]) -> Result<[Envelope; 2], Error> {
            // V4 root: 0 = statement, 1 = witness, 2 = seed commitments,
            // 3 = agreement on those commitments, 4 = PRECOMMIT.
            // A single-stream root also carries the batch evaluation itself, so
            // there only the explicit opening hook marks a release.
            if self.is_root && !self.single_stream && out[0].sequence >= PRECOMMIT_SEQ {
                self.precommit_or_view_opened.store(true, Ordering::SeqCst);
            }
            self.inner.exchange(out)
        }
    }

    /// With `single_stream` the faulty custodian's root engine evaluates the
    /// first batch itself and the fault fires there; otherwise the fault is
    /// confined to batch 2 of seven concurrent batches, which also shows that
    /// the clean batches are held back by the cross-batch barrier.
    fn assert_zkboo_fault_aborts_cleanly(
        ed: bool,
        fault: FaultInjection,
        session_tag: u8,
        single_stream: bool,
    ) {
        let _ceremony_guard = CeremonySlot::acquire(if single_stream {
            1
        } else {
            outer_mpc::tests::parallel_batches()
        });
        let witness = LegacyOwnershipWitness::from_raw_secret([0x31; 32]);
        let kind = if ed {
            witness.compute_slip0010_commitment()
        } else {
            witness.compute_bitcoin_hash160().unwrap()
        };
        let request = zk_engine::tests::request(kind);
        let scalar = witness.normalize_spending_scalar(&kind).unwrap();
        let statement = MigrationStatement {
            legacy_commitment: kind,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        let p0 = [0x11; 32];
        let p1 = [0x22; 32];
        let mut p2 = *scalar.as_le_bytes();
        for i in 0..32 {
            p2[i] ^= p0[i] ^ p1[i];
        }
        let parts = [p0, p1, p2];
        let session = [session_tag; 32];
        let leaked: [Arc<AtomicBool>; 3] =
            core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = outer_mpc::tests::networks()
                .into_iter()
                .enumerate()
                .map(|(p, net)| {
                    let st = statement.clone();
                    let flag = leaked[p].clone();
                    scope.spawn(move || {
                        let spy = ZkbooFaultSpy {
                            inner: net,
                            is_root: true,
                            single_stream,
                            fault: (p == 1).then_some(fault),
                            precommit_or_view_opened: flag,
                        };
                        CoZkCustodianShare::new(p, session, parts[p], [0x50 + p as u8; 32], keys(p))
                            .unwrap()
                            .prove(&st, spy)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });

        for (p, res) in outcomes.into_iter().enumerate() {
            assert_eq!(
                res,
                Err(Error::MultiplicationCheck),
                "custodian {p} must abort with MultiplicationCheck on ZKBoo fault"
            );
            assert!(
                !leaked[p].load(Ordering::SeqCst),
                "custodian {p} must NEVER reach PRECOMMIT or open commitments/views on ZKBoo fault!"
            );
        }
    }

    #[test]
    fn active_boolean_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        // `call_countdown: 600` injects a 1-bit consistent-share fault inside ZKBoo circuit /
        // view-commitment evaluation on batch 2, after upfront `Tape` validation has passed.
        assert_zkboo_fault_aborts_cleanly(
            false,
            FaultInjection::BitAnd {
                call_countdown: 600,
                gate: 7,
                lane: 41,
            },
            0xd0,
            false,
        );
    }

    #[test]
    fn active_field_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        assert_zkboo_fault_aborts_cleanly(
            false,
            FaultInjection::FieldMul {
                domain: Domain::Secp,
                call_countdown: 5,
                lane: 19,
            },
            0xe0,
            true,
        );
    }

    #[test]
    fn active_goldilocks_field_fault_in_zkboo_circuit_aborts_before_commitments_or_views_open() {
        assert_zkboo_fault_aborts_cleanly(
            true,
            FaultInjection::FieldMul {
                domain: Domain::Gold,
                call_countdown: 5,
                lane: 23,
            },
            0xf0,
            true,
        );
    }

    /// A substituted key share makes every repetition batch fail its own
    /// output-zero check, so one batch reaches the abort. The custodians run
    /// single-stream: the first batch is evaluated in full and the ceremony
    /// must stop there, before anything is opened.
    fn assert_input_substitution_aborts(ed: bool, delta_64bit: bool, session_tag: u8) {
        let _ceremony_guard = CeremonySlot::acquire(1);
        let witness = LegacyOwnershipWitness::from_raw_secret([0x41; 32]);
        let kind = if ed {
            witness.compute_slip0010_commitment()
        } else {
            witness.compute_bitcoin_hash160().unwrap()
        };
        let request = zk_engine::tests::request(kind);
        let scalar = witness.normalize_spending_scalar(&kind).unwrap();
        let statement = MigrationStatement {
            legacy_commitment: kind,
            target_pq_address: request.target,
            epoch_anchor: request.epoch,
            migration_domain: request.domain,
            migration_nullifier: scalar.compute_nullifier(&request.domain),
            witness_anchor: [0; 4],
        };
        let p0 = [0x15; 32];
        let p1 = [0x2a; 32];
        let mut p2 = *scalar.as_le_bytes();
        for i in 0..32 {
            p2[i] ^= p0[i] ^ p1[i];
        }
        // Malicious custodian 2 substitutes `share ^ Delta` (`64`-bit MITM delta or `1`-bit flip).
        if delta_64bit {
            for b in &mut p2[..8] {
                *b ^= 0xa5;
            }
        } else {
            p2[0] ^= 0x08;
        }
        let parts = [p0, p1, p2];
        let session = [session_tag; 32];
        let leaked: [Arc<AtomicBool>; 3] =
            core::array::from_fn(|_| Arc::new(AtomicBool::new(false)));

        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = outer_mpc::tests::networks()
                .into_iter()
                .enumerate()
                .map(|(p, net)| {
                    let st = statement.clone();
                    let flag = leaked[p].clone();
                    scope.spawn(move || {
                        let spy = ZkbooFaultSpy {
                            inner: net,
                            is_root: true,
                            single_stream: true,
                            fault: None,
                            precommit_or_view_opened: flag,
                        };
                        CoZkCustodianShare::new(p, session, parts[p], [0x60 + p as u8; 32], keys(p))
                            .unwrap()
                            .prove(&st, spy)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });

        for (p, res) in outcomes.into_iter().enumerate() {
            assert_eq!(
                res,
                Err(Error::InvalidProof),
                "custodian {p} must abort with InvalidProof on input key-share substitution"
            );
            assert!(
                !leaked[p].load(Ordering::SeqCst),
                "custodian {p} must NEVER open output residuals, commitments, or views on input substitution!"
            );
        }
    }

    #[test]
    fn custodian_input_key_share_substitution_aborts_before_any_output_or_commitment_opens() {
        assert_input_substitution_aborts(false, true, 0xa0);
    }

    #[test]
    fn custodian_ed25519_input_key_share_substitution_aborts_before_any_output_or_commitment_opens()
    {
        assert_input_substitution_aborts(true, false, 0xb0);
    }

    #[test]
    fn concurrent_quorum_batch_worker_abort_poisons_escrow_and_wipes_all_mac_keys() {
        let config = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let dealer = crate::threshold_prep::FixtureDealer::new(&config, [0x7c; 32]);
        let mut mac_shares = dealer.mac_key_shares();
        let party0_keys = mac_shares.remove(0);

        struct DummyTransport;
        impl Transport for DummyTransport {}

        let mut root = SpdzEngine::new(
            0,
            [0x7d; 32],
            config.clone(),
            vec![[0x11; 32], [0x22; 32]],
            party0_keys,
            DummyTransport,
        )
        .unwrap();
        let cancelled = Arc::new(AtomicBool::new(false));
        let seed = root.batch_seed(&[0x33; 32], cancelled.clone());

        let mut workers: Vec<_> = (0..4)
            .map(|batch| {
                SpdzEngine::for_batch(&seed, batch, DummyTransport, cancelled.clone()).unwrap()
            })
            .collect();
        // Root + QuorumSeed + 4 concurrent workers = 6 registered slots, all non-zero before abort.
        assert_eq!(seed.escrow.registered_count_and_all_wiped(), (6, false));

        // Induce an abort on worker 2 (`Core::poison`): must synchronously poison the escrow,
        // set `cancelled = true`, and volatile-wipe ALL 6 `MacKeyShare` slots across workers!
        Core::poison(&mut workers[2]);
        assert!(cancelled.load(Ordering::SeqCst));
        assert!(seed.escrow.is_poisoned());
        assert_eq!(seed.escrow.registered_count_and_all_wiped(), (6, true));

        // Subsequent `for_batch` spawns fail closed immediately.
        assert!(matches!(
            SpdzEngine::for_batch(&seed, 4, DummyTransport, cancelled),
            Err(Error::MultiplicationCheck)
        ));
    }

    /// Run one three-custodian ceremony over audited networks and report its wall time.
    fn run_full_ceremony<R: Send>(
        label: &str,
        prove: impl Fn(usize, outer_mpc::tests::Network) -> R + Sync,
    ) -> Vec<(R, outer_mpc::tests::AuditHandle)> {
        let _ceremony_guard = CeremonySlot::acquire(outer_mpc::tests::parallel_batches());
        let start = std::time::Instant::now();
        let prove = &prove;
        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = audited_networks()
                .into_iter()
                .enumerate()
                .map(|(p, (net, audit))| scope.spawn(move || (prove(p, net), audit)))
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });
        std::eprintln!("distributed 438-rep {label}: {:?}", start.elapsed());
        outcomes
    }

    fn xor_shares(secret: [u8; 32], s0: [u8; 32], s1: [u8; 32]) -> [[u8; 32]; 3] {
        let mut s2 = secret;
        for i in 0..32 {
            s2[i] ^= s0[i] ^ s1[i];
        }
        [s0, s1, s2]
    }

    struct PallasFixture {
        target: qsag_addr::QsagAddress,
        domain: [u8; 32],
        ask_le: [u8; 32],
        ask_shares: [[u8; 32]; 3],
    }
    fn pallas_fixture() -> PallasFixture {
        let mut ask_le = [0u8; 32];
        ask_le[0] = 0x5d;
        ask_le[7] = 0xa3;
        ask_le[19] = 0x11;
        PallasFixture {
            target: zk_engine::tests::request(crate::legacy::LegacyCommitmentKind::BitcoinHash160(
                [0x42; 20],
            ))
            .target,
            domain: cshake256_framed_32(b"QSAG.PALLAS.CAMPAIGN.V1", &[&77u64.to_le_bytes()]),
            ask_le,
            ask_shares: xor_shares(ask_le, [0x91; 32], [0x64; 32]),
        }
    }

    // Orchard `ak = [ask] SpendAuthG` through `prove_pallas`.
    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_pallas_ak_proof_verifies() {
        use crate::pallas::PallasOwnershipWitness;
        let PallasFixture {
            target,
            domain,
            ask_le,
            ask_shares,
        } = pallas_fixture();
        let witness = PallasOwnershipWitness::from_spend_auth_scalar_le(ask_le).unwrap();
        let commitment = witness.compute_spend_auth_key().unwrap();
        let (_, _, rsk) = witness.effective_scalar(&commitment).unwrap();
        let statement = PallasMigrationStatement {
            commitment,
            target_pq_address: target,
            epoch_anchor: 77,
            migration_domain: domain,
            migration_nullifier: rsk.compute_nullifier(pallas::NULLIFIER_TAG_PALLAS_AK, &domain),
        };
        let outcomes = run_full_ceremony("Pallas ak", |p, net| {
            CoZkCustodianShare::new(p, [0x81; 32], ask_shares[p], [0x30 + p as u8; 32], keys(p))
                .unwrap()
                .prove_pallas(&statement, net)
        });
        for (party, (res, audit)) in outcomes.into_iter().enumerate() {
            let proof = res.expect("distributed Pallas ak proof must succeed");
            pallas::verify_pallas_migration(&statement, &proof, &domain, 77).unwrap();
            let candidates = audit.candidates();
            assert!(!candidates.is_empty());
            for recovered in candidates {
                assert_ne!(recovered, ask_le, "custodian {party} leaked Pallas ask");
            }
        }
    }

    // RedPallas `rk = [ask + alpha] SpendAuthG` through `prove_pallas_request`,
    // which derives the nullifier inside the MPC.
    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_pallas_rk_request_proof_verifies() {
        use crate::pallas::PallasOwnershipWitness;
        let PallasFixture {
            target,
            domain,
            ask_le,
            ask_shares,
        } = pallas_fixture();
        let mut alpha_le = [0u8; 32];
        alpha_le[0] = 0x77;
        alpha_le[13] = 0x29;
        let witness = PallasOwnershipWitness::from_rerandomized_le(ask_le, alpha_le).unwrap();
        let commitment = witness.compute_rerandomized_rk().unwrap();
        let (_, _, rsk) = witness.effective_scalar(&commitment).unwrap();
        let expected_nullifier = rsk.compute_nullifier(pallas::NULLIFIER_TAG_PALLAS_RK, &domain);
        let alpha_shares = xor_shares(alpha_le, [0x17; 32], [0xc2; 32]);
        let request = PallasMigrationRequest {
            commitment,
            target,
            epoch: 77,
            domain,
        };
        let outcomes = run_full_ceremony("Pallas rk request", |p, net| {
            CoZkCustodianShare::new(p, [0x82; 32], ask_shares[p], [0x40 + p as u8; 32], keys(p))
                .unwrap()
                .with_rerandomizer(alpha_shares[p])
                .unwrap()
                .prove_pallas_request(request.clone(), net)
        });
        for (party, (res, audit)) in outcomes.into_iter().enumerate() {
            let (statement, proof) = res.expect("distributed Pallas rk request proof must succeed");
            assert_eq!(statement.migration_nullifier, expected_nullifier);
            pallas::verify_pallas_migration(&statement, &proof, &domain, 77).unwrap();
            for recovered in audit.candidates() {
                assert_ne!(recovered, ask_le, "custodian {party} leaked Pallas ask");
                assert_ne!(recovered, alpha_le, "custodian {party} leaked Pallas alpha");
            }
        }
    }

    struct BlsFixture {
        target: qsag_addr::QsagAddress,
        domain: [u8; 32],
        witness: crate::bls12_381::BlsOwnershipWitness,
        sk_le: [u8; 32],
        sk_shares: [[u8; 32]; 3],
        nullifier: [u64; 4],
    }
    fn bls_fixture() -> BlsFixture {
        let mut sk_be = [0u8; 32];
        sk_be[31] = 0x4b;
        sk_be[24] = 0x9e;
        sk_be[12] = 0x17;
        let witness = crate::bls12_381::BlsOwnershipWitness::from_secret_scalar_be(sk_be).unwrap();
        let domain = cshake256_framed_32(b"QSAG.BLS12_381.CAMPAIGN.V1", &[&99u64.to_le_bytes()]);
        let scalar = witness.scalar().unwrap();
        let sk_le = scalar.to_le_bytes();
        BlsFixture {
            target: zk_engine::tests::request(crate::legacy::LegacyCommitmentKind::BitcoinHash160(
                [0x55; 20],
            ))
            .target,
            domain,
            nullifier: scalar.compute_nullifier(&domain),
            witness,
            sk_le,
            sk_shares: xor_shares(sk_le, [0x3a; 32], [0x8f; 32]),
        }
    }

    // Revealed `BeaconValidatorPubkey` (`0x01` credentials) through `prove_bls`.
    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_bls12_381_pubkey_proof_verifies() {
        let fixture = bls_fixture();
        let mut withdrawal_credentials = [0x11u8; 32];
        withdrawal_credentials[0] = 0x01;
        let statement = BlsMigrationStatement {
            commitment: fixture.witness.compute_beacon_commitment().unwrap(),
            validator_index: 123_456,
            withdrawal_credentials,
            target_pq_address: fixture.target.clone(),
            epoch_anchor: 99,
            migration_domain: fixture.domain,
            migration_nullifier: fixture.nullifier,
        };
        let outcomes = run_full_ceremony("BLS12-381 revealed pubkey", |p, net| {
            CoZkCustodianShare::new(
                p,
                [0x83; 32],
                fixture.sk_shares[p],
                [0x70 + p as u8; 32],
                keys(p),
            )
            .unwrap()
            .prove_bls(&statement, net)
        });
        for (party, (res, audit)) in outcomes.into_iter().enumerate() {
            let proof = res.expect("distributed BLS BeaconValidatorPubkey proof must succeed");
            bls12_381::verify_bls_migration(&statement, &proof, &fixture.domain, 99).unwrap();
            for recovered in audit.candidates() {
                assert_ne!(recovered, fixture.sk_le, "custodian {party} leaked BLS sk");
            }
        }
    }

    // Unrevealed `0x00` withdrawal credential through `prove_bls_request`: the
    // compressed public key is hashed inside the circuit and never opened.
    #[test]
    #[ignore = "full 438-repetition ceremony; run by name"]
    fn complete_distributed_bls12_381_unrevealed_0x00_request_proof_verifies() {
        let fixture = bls_fixture();
        let commitment = fixture
            .witness
            .compute_unrevealed_0x00_commitment()
            .unwrap();
        let BlsValidatorCommitment::UnrevealedBls0x00Credential(withdrawal_credentials) =
            commitment
        else {
            unreachable!()
        };
        let request = BlsMigrationRequest {
            commitment,
            validator_index: 654_321,
            withdrawal_credentials,
            target: fixture.target.clone(),
            epoch: 99,
            domain: fixture.domain,
        };
        let outcomes = run_full_ceremony("BLS12-381 unrevealed 0x00 request", |p, net| {
            CoZkCustodianShare::new(
                p,
                [0x84; 32],
                fixture.sk_shares[p],
                [0x80 + p as u8; 32],
                keys(p),
            )
            .unwrap()
            .prove_bls_request(request.clone(), net)
        });
        for (party, (res, audit)) in outcomes.into_iter().enumerate() {
            let (statement, proof) =
                res.expect("distributed BLS UnrevealedBls0x00Credential proof must succeed");
            assert_eq!(statement.migration_nullifier, fixture.nullifier);
            bls12_381::verify_bls_migration(&statement, &proof, &fixture.domain, 99).unwrap();
            for recovered in audit.candidates() {
                assert_ne!(recovered, fixture.sk_le, "custodian {party} leaked BLS sk");
            }
        }
    }

    /// Single-stream ceremony in which custodian `faulty` injects `fault`.
    /// Returns every custodian's outcome and whether it saw any opening.
    fn run_single_stream_with_fault<R: Send>(
        fault: Option<(usize, FaultInjection)>,
        prove: impl Fn(usize, ZkbooFaultSpy) -> R + Sync,
    ) -> Vec<(R, bool)> {
        let _ceremony_guard = CeremonySlot::acquire(1);
        let prove = &prove;
        std::thread::scope(|scope| {
            let handles: Vec<_> = outer_mpc::tests::networks()
                .into_iter()
                .enumerate()
                .map(|(p, net)| {
                    scope.spawn(move || {
                        let opened = Arc::new(AtomicBool::new(false));
                        let spy = ZkbooFaultSpy {
                            inner: net,
                            is_root: true,
                            single_stream: true,
                            fault: fault.and_then(|(faulty, fault)| (p == faulty).then_some(fault)),
                            precommit_or_view_opened: opened.clone(),
                        };
                        (prove(p, spy), opened.load(Ordering::SeqCst))
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        })
    }

    #[test]
    fn active_pallas_field_fault_aborts_before_commitments_or_views_open() {
        use crate::pallas::PallasOwnershipWitness;
        let mut ask_le = [0u8; 32];
        ask_le[0] = 0x19;
        let witness = PallasOwnershipWitness::from_spend_auth_scalar_le(ask_le).unwrap();
        let commitment = witness.compute_spend_auth_key().unwrap();
        let (_, _, rsk) = witness.effective_scalar(&commitment).unwrap();
        let domain = [0x21u8; 32];
        let statement = PallasMigrationStatement {
            commitment,
            target_pq_address: zk_engine::tests::request(
                crate::legacy::LegacyCommitmentKind::BitcoinHash160([0x66; 20]),
            )
            .target,
            epoch_anchor: 5,
            migration_domain: domain,
            migration_nullifier: rsk.compute_nullifier(pallas::NULLIFIER_TAG_PALLAS_AK, &domain),
        };
        let shares = xor_shares(ask_le, [0x11; 32], [0x22; 32]);
        let fault = FaultInjection::FieldMul {
            domain: Domain::PallasFp,
            call_countdown: 3,
            lane: 17,
        };
        let outcomes = run_single_stream_with_fault(Some((1, fault)), |p, spy| {
            CoZkCustodianShare::new(p, [0x95; 32], shares[p], [p as u8; 32], keys(p))
                .unwrap()
                .prove_pallas(&statement, spy)
        });
        for (result, opened) in outcomes {
            assert_eq!(result, Err(Error::MultiplicationCheck));
            assert!(!opened);
        }
    }

    struct BlsFaultFixture {
        witness: crate::bls12_381::BlsOwnershipWitness,
        target: qsag_addr::QsagAddress,
        domain: [u8; 32],
        shares: [[u8; 32]; 3],
    }
    fn bls_fault_fixture() -> BlsFaultFixture {
        let mut sk_be = [0u8; 32];
        sk_be[31] = 0x2f;
        let witness = crate::bls12_381::BlsOwnershipWitness::from_secret_scalar_be(sk_be).unwrap();
        let sk_le = witness.scalar().unwrap().to_le_bytes();
        BlsFaultFixture {
            witness,
            target: zk_engine::tests::request(crate::legacy::LegacyCommitmentKind::BitcoinHash160(
                [0x66; 20],
            ))
            .target,
            domain: [0x31; 32],
            shares: xor_shares(sk_le, [0x44; 32], [0x88; 32]),
        }
    }

    #[test]
    fn active_bls12_381_field_fault_aborts_before_commitments_or_views_open() {
        let BlsFaultFixture {
            witness,
            target,
            domain,
            shares,
        } = bls_fault_fixture();
        let mut withdrawal_credentials = [0u8; 32];
        withdrawal_credentials[0] = 0x02;
        let statement = BlsMigrationStatement {
            commitment: witness.compute_beacon_commitment().unwrap(),
            validator_index: 9,
            withdrawal_credentials,
            target_pq_address: target,
            epoch_anchor: 6,
            migration_domain: domain,
            migration_nullifier: witness.scalar().unwrap().compute_nullifier(&domain),
        };
        let fault = FaultInjection::FieldMul {
            domain: Domain::BlsFp,
            call_countdown: 3,
            lane: 9,
        };
        let outcomes = run_single_stream_with_fault(Some((2, fault)), |p, spy| {
            CoZkCustodianShare::new(p, [0x96; 32], shares[p], [p as u8; 32], keys(p))
                .unwrap()
                .prove_bls(&statement, spy)
        });
        for (result, opened) in outcomes {
            assert_eq!(result, Err(Error::MultiplicationCheck));
            assert!(!opened);
        }
    }

    // A substituted witness share fails the in-MPC commitment check, so the
    // nullifier never opens.
    #[test]
    fn bls12_381_request_with_a_substituted_share_aborts_before_the_nullifier_opens() {
        let BlsFaultFixture {
            witness,
            target,
            domain,
            mut shares,
        } = bls_fault_fixture();
        shares[0][0] ^= 0x01;
        let commitment = witness.compute_unrevealed_0x00_commitment().unwrap();
        let BlsValidatorCommitment::UnrevealedBls0x00Credential(withdrawal_credentials) =
            commitment
        else {
            unreachable!()
        };
        let request = BlsMigrationRequest {
            commitment,
            validator_index: 9,
            withdrawal_credentials,
            target,
            epoch: 6,
            domain,
        };
        let outcomes = run_single_stream_with_fault(None, |p, spy| {
            CoZkCustodianShare::new(p, [0x97; 32], shares[p], [p as u8; 32], keys(p))
                .unwrap()
                .prove_bls_request(request.clone(), spy)
        });
        for (result, opened) in outcomes {
            assert!(matches!(result, Err(Error::InvalidProof)));
            assert!(!opened);
        }
    }
}
