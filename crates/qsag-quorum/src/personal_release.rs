//! End-to-end personal release: an [`AsymmetricQuorumSystem`] certificate from the
//! [`PersonalBeltLatch`] unlocks each certified party's [`PersonalMspInput`] lanes, and
//! the lanes enter an SPDZ-authenticated `Poseidon2` evaluation whose only opened value
//! is the `Hem` PRF-check digest of the shared secret.
//!
//! ### Roles & Wire Isolation
//! * [`PersonalReleaseContext`] is public. It fixes the policy, the enrolled span
//!   program, the key/epoch context, the ceremony, the latch epoch, the exact signer
//!   set, and the enrolled commitment. Its digest is the message the latch binds, so an
//!   acknowledgement for one context authorizes nothing in any other.
//! * [`PersonalReleaseParty`] is one custodian: its own latch and WAL and its own span
//!   program rows. Over [`WireTransport`], [`PersonalReleaseParty::ceremony_over_wire`]
//!   derives pairwise Encrypt-then-MAC [`MacSealedWireChannel`] keys from its enrolled
//!   [`PersonalBeltLatch`], exchanges latch acknowledgements, collapses its own MSP rows
//!   locally, reshares its 4 `Goldilocks` lanes over encrypted point-to-point links,
//!   establishes pairwise PQ Ring-LWE + interactive `SoftSpokenOT (n_C = 256, k = 2)` channels
//!   ([`PartyOtEndpoint`]),
//!   authenticates inputs and 118 `Π_pow7` S-box tuples under a dealerless `GoldilocksExt2`
//!   SPDZ MAC key, evaluates `poseidon2_compress12_ff`, and verifies a two-stage
//!   multiplicatively blinded `MacCheck` strictly before opening the PRF-check digest.
//!   **No driver, coordinator, or peer ever sees another custodian's released lanes.**

use alloc::{vec, vec::Vec};
use core::hint::black_box;

use qsag_core::{
    belt_latch::{BeltLatchRecord, DurableWal},
    field::goldilocks::{Goldilocks, GoldilocksExt2, wipe_ext2},
    poseidon2_mpc::{
        HEM_DOMAIN_PRF_CHECK, HemDigest4, POSEIDON2_SBOXES_PER_PERM, Poseidon2MpcError,
        release_additive_hem_prf_check_mpc,
    },
    preprocessing::{
        BaseOtCrsCommitMsg, BaseOtCrsOpenMsg, BaseOtCrsReceiverRound0, BaseOtCrsSenderRound0,
        BaseOtCrsShareMsg, BaseOtExtReceiverRound2, BaseOtExtSenderRound1, BaseOtRound1Msg,
        BaseOtRound2Msg, BaseOtRound3Msg, BaseOtRound4Msg, KosOtChallengeMsg, KosOtProofMsg,
        KosOtUColsMsg, OtExtReceiverChannel, OtExtSenderChannel, OtMesh, OtPadPair,
        PartyPrivateRng, PreprocessError,
    },
    sponge::{
        keccak::{Cshake256Xof, shake256_32},
        poseidon2::{
            POSEIDON2_CONST_IV, POSEIDON2_HALF_EXTERNAL_ROUNDS, POSEIDON2_INTERNAL_ROUNDS,
            poseidon2_const_at,
        },
    },
    wipe::{SecretBuffer, SecretWipe, ct_eq_bytes32, wipe_bytes, wipe_bytes32},
};

use crate::access::{
    AccessError, AsymmetricQuorumSystem, MonotoneSpanProgram, PartySet, PersonalBeltLatch,
    PersonalLatchAck, PersonalLatchCertificate, QuorumPolicyError,
};
use crate::hash::h32;
use crate::party_node::{PersonalMspInput, PersonalMspInputError, PoisonJournal, ROUND_ABORT};
use crate::wire_channel::{MacSealedWireChannel, TransportError, WireTransport};

mod dkg;
pub use dkg::{DealerlessPersonalReleaseDkg, run_dealerless_personal_release_dkg_over_wire};

/// Wire round tags for isolated [`PersonalReleaseParty::ceremony_over_wire`].
pub const ROUND_PREL_ACK: u32 = 0x0500_0001;
pub const ROUND_PREL_RESHARE: u32 = 0x0500_0002;
pub const ROUND_PREL_OT_CRS_COM: u32 = 0x0501_0001;
pub const ROUND_PREL_OT_CRS_SH: u32 = 0x0501_0002;
pub const ROUND_PREL_OT_CRS_OPEN: u32 = 0x0501_0003;
pub const ROUND_PREL_OT_R1: u32 = 0x0501_0004;
pub const ROUND_PREL_OT_R2: u32 = 0x0501_0005;
pub const ROUND_PREL_OT_R3: u32 = 0x0501_0006;
pub const ROUND_PREL_OT_R4: u32 = 0x0501_0007;
pub const ROUND_PREL_KOS_U: u32 = 0x0502_0001;
pub const ROUND_PREL_KOS_CHAL: u32 = 0x0502_0002;
pub const ROUND_PREL_KOS_PROOF: u32 = 0x0502_0003;
pub const ROUND_PREL_OLE_CT: u32 = 0x0503_0001;
pub const ROUND_PREL_OLE_DIFF: u32 = 0x0503_0002;
pub const ROUND_PREL_COIN_COM: u32 = 0x0504_0001;
pub const ROUND_PREL_COIN_OPEN: u32 = 0x0504_0002;
pub const ROUND_PREL_COMMIT: u32 = 0x0505_0001;
pub const ROUND_PREL_OPEN: u32 = 0x0505_0002;
pub const ROUND_PREL_SBOX_Y: u32 = 0x0506_0001;
pub const ROUND_PREL_CUT_COM: u32 = 0x0507_0001;
pub const ROUND_PREL_CUT_OPEN: u32 = 0x0507_0002;

/// One party's released additive lanes. Wiped on drop.
pub type ReleasedLanes = SecretBuffer<[Goldilocks; 4]>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PersonalReleaseError {
    /// The context names another policy, key/epoch context or span program than this
    /// party enrolled, or a signer set the program does not authorize.
    ContextMismatch,
    /// This party, or the addressed receiver, is not in the context's signer set.
    NotASigner,
    /// The certificate is valid for the policy but not signed by exactly the signer set.
    SignerSetMismatch,
    /// This party's input was already released.
    AlreadyReleased,
    /// The lanes or transport handed to the evaluation do not match the certified signer roster.
    LaneRosterMismatch,
    /// The opened digest differs from the enrolled commitment.
    CommitmentMismatch,
    /// The ceremony session was already reserved or poisoned in the party's [`PoisonJournal`].
    SessionPoisoned,
    /// Peer `party` aborted the wire ceremony.
    PeerAborted {
        party: u16,
    },
    /// Peer `from` sent an unparseable payload in `round`.
    MalformedWireMessage {
        from: u16,
        round: u32,
    },
    Transport(TransportError),
    Policy(QuorumPolicyError),
    Access(AccessError),
    Mpc(Poseidon2MpcError),
}

impl From<TransportError> for PersonalReleaseError {
    fn from(e: TransportError) -> Self {
        Self::Transport(e)
    }
}

/// Public description of one release ceremony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersonalReleaseContext {
    deployment_id: [u8; 32],
    key_epoch_context: [u8; 32],
    policy_digest: [u8; 32],
    program_digest: [u8; 32],
    ceremony_id: [u8; 32],
    latch_epoch: u64,
    signers: PartySet,
    pk_seed: HemDigest4,
    commitment: HemDigest4,
}

/// Digest of a span program's canonical encoding (already framed with `QMSP0001`).
pub fn span_program_digest(program: &MonotoneSpanProgram) -> [u8; 32] {
    shake256_32(&program.canonical_bytes())
}

impl PersonalReleaseContext {
    #[expect(
        clippy::too_many_arguments,
        reason = "Every argument is a separately bound public ceremony field"
    )]
    pub fn new(
        deployment_id: [u8; 32],
        system: &AsymmetricQuorumSystem,
        program: &MonotoneSpanProgram,
        key_epoch_context: [u8; 32],
        ceremony_id: [u8; 32],
        latch_epoch: u64,
        signers: PartySet,
        pk_seed: HemDigest4,
        commitment: HemDigest4,
    ) -> Result<Self, PersonalReleaseError> {
        if signers.len() < 2
            || !signers.is_subset(system.participants())
            || program.solve_reconstruction_weights(&signers).is_none()
        {
            return Err(PersonalReleaseError::ContextMismatch);
        }
        Ok(Self {
            deployment_id,
            key_epoch_context,
            policy_digest: system.policy_digest(&key_epoch_context),
            program_digest: span_program_digest(program),
            ceremony_id,
            latch_epoch,
            signers,
            pk_seed,
            commitment,
        })
    }

    pub fn signers(&self) -> &PartySet {
        &self.signers
    }

    pub fn commitment(&self) -> &HemDigest4 {
        &self.commitment
    }

    pub fn pk_seed(&self) -> &HemDigest4 {
        &self.pk_seed
    }

    /// Fixed-order `QPRC0002` frame of every field. All fields but the signer list have
    /// fixed width and the list carries its length, so the encoding is injective.
    fn frame(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + 5 * 32 + 8 + 8 + 2 * self.signers.len() + 64);
        out.extend_from_slice(b"QPRC0002");
        out.extend_from_slice(&self.deployment_id);
        out.extend_from_slice(&self.key_epoch_context);
        out.extend_from_slice(&self.policy_digest);
        out.extend_from_slice(&self.program_digest);
        out.extend_from_slice(&self.ceremony_id);
        out.extend_from_slice(&self.latch_epoch.to_be_bytes());
        out.extend_from_slice(&(self.signers.len() as u64).to_be_bytes());
        for p in &self.signers {
            out.extend_from_slice(&p.to_be_bytes());
        }
        for limb in self.pk_seed.iter().chain(&self.commitment) {
            out.extend_from_slice(&limb.to_be_bytes());
        }
        out
    }

    /// The latch record of this ceremony. Its message digest is plain `SHAKE256` of the
    /// frame; the ceremony identifier doubles as the latched salt, so one latch epoch
    /// admits exactly one ceremony.
    pub fn record(&self) -> BeltLatchRecord {
        BeltLatchRecord {
            epoch: self.latch_epoch,
            msg_digest: shake256_32(&self.frame()),
            retry_salt: self.ceremony_id,
            target_sum_digits: Vec::new(),
        }
    }

    /// Session identifier of the authenticated evaluation, bound to the latch binding.
    pub fn mpc_session_id(&self) -> [u8; 32] {
        let mut framed = [0u8; 40];
        framed[..8].copy_from_slice(b"QPRS0002");
        framed[8..].copy_from_slice(&self.record().binding());
        shake256_32(&framed)
    }
}

struct LocalSendPads(Vec<OtPadPair>);

impl Drop for LocalSendPads {
    fn drop(&mut self) {
        for (p0, p1) in &mut self.0 {
            wipe_bytes(p0);
            wipe_bytes(p1);
        }
    }
}

impl core::ops::Deref for LocalSendPads {
    type Target = [OtPadPair];
    fn deref(&self) -> &[OtPadPair] {
        &self.0
    }
}

struct LocalRecvPads(Vec<[u8; 48]>);

impl Drop for LocalRecvPads {
    fn drop(&mut self) {
        for pad in &mut self.0 {
            wipe_bytes(pad);
        }
    }
}

impl core::ops::Deref for LocalRecvPads {
    type Target = [[u8; 48]];
    fn deref(&self) -> &[[u8; 48]] {
        &self.0
    }
}

type LocalOtBatchPads = (LocalSendPads, LocalRecvPads);

struct WireExt2BlindTriple {
    r: GoldilocksExt2,
    a: GoldilocksExt2,
    c: GoldilocksExt2,
}

impl Drop for WireExt2BlindTriple {
    fn drop(&mut self) {
        wipe_ext2(core::slice::from_mut(&mut self.r));
        wipe_ext2(core::slice::from_mut(&mut self.a));
        wipe_ext2(core::slice::from_mut(&mut self.c));
    }
}

/// One custodian's end of a pairwise PQ Ring-LWE + interactive `SoftSpokenOT (n_C = 256, k = 2)`
/// mesh over
/// [`WireTransport`], with pooled single-use `GoldilocksExt2` multiplicative blinding triples.
///
/// Holds **only** local `me -> peer` [`OtExtSenderChannel`]s and `peer -> me`
/// [`OtExtReceiverChannel`]s (`!Clone`, wiped on `Drop`).
pub struct PartyOtEndpoint {
    me: usize,
    parties: usize,
    roster: Vec<u16>,
    session_id: [u8; 32],
    senders: Vec<Option<OtExtSenderChannel>>,
    receivers: Vec<Option<OtExtReceiverChannel>>,
    transcript: [u8; 32],
    ext2_blind_pool: Vec<WireExt2BlindTriple>,
    ext2_blind_cursor: usize,
    ext2_blind_serial: u64,
    poisoned: bool,
    #[cfg(test)]
    tamper_next_ext2_c: Option<(usize, GoldilocksExt2)>,
}

impl Drop for PartyOtEndpoint {
    fn drop(&mut self) {
        self.poison_and_wipe();
    }
}

impl PartyOtEndpoint {
    /// Establish active-secure PQ Ring-LWE + 4-ciphertext parity-combined
    /// `SoftSpokenOT (n_C = 256, k = 2)` channels
    /// with every peer in `roster` over `wire` using deadlock-free lexicographic pair scheduling.
    pub fn establish_over_wire<T: WireTransport>(
        session_id: [u8; 32],
        roster: &[u16],
        wire: &mut T,
        rng: &mut PartyPrivateRng,
    ) -> Result<Self, PersonalReleaseError> {
        let m = roster.len();
        let me = wire.party();
        if m < 2 || wire.parties() != m || me >= m {
            return Err(PersonalReleaseError::LaneRosterMismatch);
        }
        let ot_sid = h32(b"personal-release/ot-setup", &[&session_id]);
        let mut senders: Vec<Option<OtExtSenderChannel>> = (0..m).map(|_| None).collect();
        let mut receivers: Vec<Option<OtExtReceiverChannel>> = (0..m).map(|_| None).collect();

        for a in 0..m {
            for b in (a + 1)..m {
                for (sender, receiver) in [(a, b), (b, a)] {
                    if me == receiver {
                        let (crs_r0, crs_com) =
                            BaseOtCrsReceiverRound0::commit(ot_sid, sender, receiver, rng);
                        wire.send_frame(sender, ROUND_PREL_OT_CRS_COM, &crs_com.to_bytes())?;
                        let sh_raw = recv_wire(wire, roster, sender, ROUND_PREL_OT_CRS_SH)?;
                        let crs_sh = BaseOtCrsShareMsg::from_bytes(&sh_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[sender],
                                round: ROUND_PREL_OT_CRS_SH,
                            },
                        )?;
                        let (r_crs_coin, crs_open) = crs_r0.open_and_derive_crs_coin(&crs_sh);
                        wire.send_frame(sender, ROUND_PREL_OT_CRS_OPEN, &crs_open.to_bytes())?;

                        let r1_raw = recv_wire(wire, roster, sender, ROUND_PREL_OT_R1)?;
                        let msg1 = BaseOtRound1Msg::from_bytes(&r1_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[sender],
                                round: ROUND_PREL_OT_R1,
                            },
                        )?;
                        let (r_r2, msg2) = BaseOtExtReceiverRound2::respond_with_crs(
                            r_crs_coin, ot_sid, sender, receiver, &msg1, rng,
                        )
                        .map_err(|e| PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e)))?;
                        wire.send_frame(sender, ROUND_PREL_OT_R2, &msg2.to_bytes())?;

                        let r3_raw = recv_wire(wire, roster, sender, ROUND_PREL_OT_R3)?;
                        let msg3 = BaseOtRound3Msg::from_bytes(&r3_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[sender],
                                round: ROUND_PREL_OT_R3,
                            },
                        )?;
                        let (r_chan, msg4) = r_r2.finalize(&msg3);
                        wire.send_frame(sender, ROUND_PREL_OT_R4, &msg4.to_bytes())?;
                        receivers[sender] = Some(r_chan);
                    } else if me == sender {
                        let com_raw = recv_wire(wire, roster, receiver, ROUND_PREL_OT_CRS_COM)?;
                        let crs_com = BaseOtCrsCommitMsg::from_bytes(&com_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[receiver],
                                round: ROUND_PREL_OT_CRS_COM,
                            },
                        )?;
                        let (crs_s0, crs_sh) =
                            BaseOtCrsSenderRound0::respond(ot_sid, sender, receiver, &crs_com, rng);
                        wire.send_frame(receiver, ROUND_PREL_OT_CRS_SH, &crs_sh.to_bytes())?;
                        let open_raw = recv_wire(wire, roster, receiver, ROUND_PREL_OT_CRS_OPEN)?;
                        let crs_open = BaseOtCrsOpenMsg::from_bytes(&open_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[receiver],
                                round: ROUND_PREL_OT_CRS_OPEN,
                            },
                        )?;
                        let s_crs_coin =
                            crs_s0.verify_and_derive_crs_coin(&crs_open).map_err(|e| {
                                PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e))
                            })?;

                        let (s_r1, msg1) = BaseOtExtSenderRound1::start_with_crs(
                            s_crs_coin, ot_sid, sender, receiver, rng,
                        );
                        wire.send_frame(receiver, ROUND_PREL_OT_R1, &msg1.to_bytes())?;

                        let r2_raw = recv_wire(wire, roster, receiver, ROUND_PREL_OT_R2)?;
                        let msg2 = BaseOtRound2Msg::from_bytes(&r2_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[receiver],
                                round: ROUND_PREL_OT_R2,
                            },
                        )?;
                        let (s_r3, msg3) =
                            s_r1.verify_fo_and_respond_coin(&msg2, rng).map_err(|e| {
                                PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e))
                            })?;
                        wire.send_frame(receiver, ROUND_PREL_OT_R3, &msg3.to_bytes())?;

                        let r4_raw = recv_wire(wire, roster, receiver, ROUND_PREL_OT_R4)?;
                        let msg4 = BaseOtRound4Msg::from_bytes(&r4_raw).ok_or(
                            PersonalReleaseError::MalformedWireMessage {
                                from: roster[receiver],
                                round: ROUND_PREL_OT_R4,
                            },
                        )?;
                        let s_chan = s_r3.finalize(&msg4).map_err(|e| {
                            PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e))
                        })?;
                        senders[receiver] = Some(s_chan);
                    }
                }
            }
        }

        let transcript = h32(b"personal-release/ot-init", &[&ot_sid]);
        Ok(Self {
            me,
            parties: m,
            roster: roster.to_vec(),
            session_id: ot_sid,
            senders,
            receivers,
            transcript,
            ext2_blind_pool: Vec::new(),
            ext2_blind_cursor: 0,
            ext2_blind_serial: 0,
            poisoned: false,
            #[cfg(test)]
            tamper_next_ext2_c: None,
        })
    }

    /// Remaining pre-staged `GoldilocksExt2` multiplicative blinding triples.
    pub fn staged_ext2_blinding(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.ext2_blind_pool
                .len()
                .saturating_sub(self.ext2_blind_cursor)
        }
    }

    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        self.ext2_blind_pool.clear();
        self.ext2_blind_cursor = 0;
        for ch in &mut self.senders {
            let _ = ch.take();
        }
        for ch in &mut self.receivers {
            let _ = ch.take();
        }
        wipe_bytes32(&mut self.transcript);
    }

    fn run_directed_kos<T: WireTransport>(
        &mut self,
        wire: &mut T,
        sender: usize,
        receiver: usize,
        my_choices: &[u64],
        rng: &mut PartyPrivateRng,
    ) -> Result<Option<LocalOtBatchPads>, PersonalReleaseError> {
        if self.poisoned {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::VaultPoisoned {
                    kind: "personal_release_ot",
                },
            )));
        }
        if self.me == receiver {
            let recv_ch = self.receivers[sender]
                .as_mut()
                .ok_or(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                    PreprocessError::ChannelPoisoned {
                        sender_id: sender,
                        receiver_id: receiver,
                    },
                )))?;
            let (pending, u_msg) = recv_ch.round1_send_u_cols(my_choices, rng);
            let u_bytes = u_msg.to_bytes();
            wire.send_frame(sender, ROUND_PREL_KOS_U, &u_bytes)?;
            let chal_raw = recv_wire(wire, &self.roster, sender, ROUND_PREL_KOS_CHAL)?;
            let chal = KosOtChallengeMsg::from_bytes(&chal_raw).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: self.roster[sender],
                    round: ROUND_PREL_KOS_CHAL,
                },
            )?;
            let (proof, pads) = recv_ch.round3_prove_and_finish(pending, &chal);
            let proof_bytes = proof.to_bytes();
            wire.send_frame(sender, ROUND_PREL_KOS_PROOF, &proof_bytes)?;
            self.transcript = h32(
                b"personal-release/kos-step",
                &[
                    &self.transcript,
                    &(sender as u64).to_be_bytes(),
                    &(receiver as u64).to_be_bytes(),
                    &chal.chi_seed,
                    &proof_bytes,
                ],
            );
            Ok(Some((LocalSendPads(Vec::new()), LocalRecvPads(pads))))
        } else if self.me == sender {
            let send_ch = self.senders[receiver]
                .as_mut()
                .ok_or(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                    PreprocessError::ChannelPoisoned {
                        sender_id: sender,
                        receiver_id: receiver,
                    },
                )))?;
            let u_raw = recv_wire(wire, &self.roster, receiver, ROUND_PREL_KOS_U)?;
            let u_msg = KosOtUColsMsg::from_bytes(&u_raw).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: self.roster[receiver],
                    round: ROUND_PREL_KOS_U,
                },
            )?;
            let (pending, chal) = send_ch.round2_sample_challenge(&u_msg, rng).map_err(|e| {
                self.poisoned = true;
                PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e))
            })?;
            wire.send_frame(receiver, ROUND_PREL_KOS_CHAL, &chal.to_bytes())?;
            let proof_raw = recv_wire(wire, &self.roster, receiver, ROUND_PREL_KOS_PROOF)?;
            let proof = KosOtProofMsg::from_bytes(&proof_raw).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: self.roster[receiver],
                    round: ROUND_PREL_KOS_PROOF,
                },
            )?;
            let pad_pairs = send_ch
                .round4_verify_and_finish(pending, &proof)
                .map_err(|e| {
                    self.poisoned = true;
                    PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(e))
                })?;
            if my_choices.len().checked_mul(64) != Some(pad_pairs.len()) {
                self.poisoned = true;
                return Err(PersonalReleaseError::MalformedWireMessage {
                    from: self.roster[receiver],
                    round: ROUND_PREL_KOS_PROOF,
                });
            }
            let proof_bytes = proof.to_bytes();
            self.transcript = h32(
                b"personal-release/kos-step",
                &[
                    &self.transcript,
                    &(sender as u64).to_be_bytes(),
                    &(receiver as u64).to_be_bytes(),
                    &chal.chi_seed,
                    &proof_bytes,
                ],
            );
            Ok(Some((LocalSendPads(pad_pairs), LocalRecvPads(Vec::new()))))
        } else {
            Ok(None)
        }
    }

    /// Pre-stage `additional` single-use multiplicative `GoldilocksExt2` blinding triples
    /// `(r_me, a_me, c_me)` (`\sum c == (\sum r) * (\sum a)`) over `wire` in one batched OT pass.
    pub fn prestage_ext2_blinding<T: WireTransport>(
        &mut self,
        wire: &mut T,
        additional: usize,
        rng: &mut PartyPrivateRng,
    ) -> Result<(), PersonalReleaseError> {
        let result = self.prestage_ext2_blinding_inner(wire, additional, rng);
        if result.is_err() {
            self.poison_and_wipe();
        }
        result
    }

    fn prestage_ext2_blinding_inner<T: WireTransport>(
        &mut self,
        wire: &mut T,
        additional: usize,
        rng: &mut PartyPrivateRng,
    ) -> Result<(), PersonalReleaseError> {
        if self.poisoned {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::VaultPoisoned {
                    kind: "personal_release_ext2_blind",
                },
            )));
        }
        if wire.party() != self.me || wire.parties() != self.parties {
            return Err(PersonalReleaseError::LaneRosterMismatch);
        }
        // Bound the largest ciphertext frame, including two sacrifice companions per staged
        // triple (`3 * additional` OLE items) and the sealed-channel overhead, before any
        // multiplication or allocation derived from this public count.
        const SAC_COMPANIONS: usize = 2;
        let ole_items = additional
            .checked_mul(1 + SAC_COMPANIONS)
            .ok_or(TransportError::PayloadTooLarge)?;
        let frame_bytes = ole_items
            .checked_mul(640 * 32)
            .ok_or(TransportError::PayloadTooLarge)?;
        if frame_bytes
            > crate::wire_channel::MAX_FRAME_PAYLOAD - crate::wire_channel::FRAME_HEADER_BYTES - 33
        {
            return Err(TransportError::PayloadTooLarge.into());
        }
        if additional == 0 {
            return Ok(());
        }
        if self.ext2_blind_cursor > 0 {
            self.ext2_blind_pool.drain(..self.ext2_blind_cursor);
            self.ext2_blind_cursor = 0;
        }
        let refill_sid = h32(
            b"personal-release/ext2-blind-refill",
            &[
                &self.session_id,
                &self.ext2_blind_serial.to_be_bytes(),
                &(additional as u64).to_be_bytes(),
            ],
        );
        self.ext2_blind_serial =
            self.ext2_blind_serial
                .checked_add(1)
                .ok_or(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                    PreprocessError::VaultExhausted {
                        kind: "personal_release_ext2_blind",
                    },
                )))?;

        const WORDS_PER_ITEM: usize = 10;
        const BITS_PER_ITEM: usize = 64 * WORDS_PER_ITEM;
        let r_shares = SecretBuffer(
            (0..ole_items)
                .map(|_| rng.next_ext2())
                .collect::<Vec<GoldilocksExt2>>(),
        );
        let total_words = ole_items * WORDS_PER_ITEM;
        let total_bits = ole_items * BITS_PER_ITEM;
        let choices = SecretBuffer(
            (0..total_words)
                .map(|_| rng.next_u64())
                .collect::<Vec<u64>>(),
        );
        let mut raw_acc = SecretBuffer(vec![GoldilocksExt2::ZERO; total_bits]);
        let mut ct_bind = h32(b"personal-release/ext2-blind-ct0", &[&refill_sid]);
        let m = self.parties;

        for a in 0..m {
            for b in (a + 1)..m {
                for (sender, receiver) in [(a, b), (b, a)] {
                    let pads = self.run_directed_kos(wire, sender, receiver, &choices, rng)?;
                    if self.me == sender {
                        let (send_pads, _) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let mut frame = SecretBuffer(Vec::with_capacity(total_bits * 32));
                        for (k, &s_val) in r_shares.iter().enumerate() {
                            let base_bit = k * BITS_PER_ITEM;
                            for bit_off in 0..BITS_PER_ITEM {
                                let bit = base_bit + bit_off;
                                let pad0 = decode_pad48_ext2(&send_pads[bit].0);
                                let pad1 = decode_pad48_ext2(&send_pads[bit].1);
                                let mask = rng.next_ext2();
                                let ct0 = pad0 - mask;
                                let ct1 = pad1 + s_val - mask;
                                frame.extend_from_slice(&ct0.to_be_bytes());
                                frame.extend_from_slice(&ct1.to_be_bytes());
                                raw_acc[bit] += mask;
                            }
                        }
                        ct_bind = h32(
                            b"personal-release/ext2-blind-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &frame,
                            ],
                        );
                        wire.send_frame(receiver, ROUND_PREL_OLE_CT, &frame)?;
                    } else if self.me == receiver {
                        let (_, recv_pads) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let raw = recv_wire(wire, &self.roster, sender, ROUND_PREL_OLE_CT)?;
                        if raw.len() != total_bits * 32 {
                            self.poison_and_wipe();
                            return Err(PersonalReleaseError::MalformedWireMessage {
                                from: self.roster[sender],
                                round: ROUND_PREL_OLE_CT,
                            });
                        }
                        ct_bind = h32(
                            b"personal-release/ext2-blind-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &raw,
                            ],
                        );
                        for bit in 0..total_bits {
                            let off = bit * 32;
                            let ct0 = decode_ext2_be(&raw[off..off + 16]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: self.roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let ct1 = decode_ext2_be(&raw[off + 16..off + 32]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: self.roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let choice = (choices[bit / 64] >> (bit % 64)) & 1;
                            let selected = ct_select_ext2(choice, ct0, ct1);
                            raw_acc[bit] += selected - decode_pad48_ext2(&recv_pads[bit]);
                        }
                    }
                }
            }
        }

        // Synchronize a joint coin across all `m` signers bound to each party's view of `ct_bind`.
        let local_view = h32(
            b"personal-release/ext2-blind-view",
            &[&ct_bind, &self.transcript],
        );
        let coin = joint_coin_over_wire(
            wire,
            &self.roster,
            &refill_sid,
            b"ext2-blind-lhl",
            &local_view,
            false,
            rng,
        )?;
        let mut xof = Cshake256Xof::new_shake256();
        xof.absorb(b"personal-release/ext2-blind-h");
        xof.absorb(&coin);

        let mut a_shares = SecretBuffer(Vec::with_capacity(ole_items));
        let mut c_shares = SecretBuffer(Vec::with_capacity(ole_items));
        for k in 0..ole_items {
            let base_bit = k * BITS_PER_ITEM;
            let mut a_me = GoldilocksExt2::ZERO;
            let mut w_me = GoldilocksExt2::ZERO;
            for bit_off in 0..BITS_PER_ITEM {
                let bit = base_bit + bit_off;
                let mut bytes = [0u8; 48];
                xof.squeeze(&mut bytes);
                let g = decode_pad48_ext2(&bytes);
                wipe_bytes(&mut bytes);
                let select = 0u64.wrapping_sub(black_box((choices[bit / 64] >> (bit % 64)) & 1));
                a_me += GoldilocksExt2::new(
                    Goldilocks::from_u64_reduced(select & g.c0.to_canonical_u64()),
                    Goldilocks::from_u64_reduced(select & g.c1.to_canonical_u64()),
                );
                w_me += g * raw_acc[bit];
            }
            a_shares.push(a_me);
            c_shares.push(r_shares[k] * a_me + w_me);
        }
        #[cfg(test)]
        if let Some((item, delta)) = self.tamper_next_ext2_c.take() {
            c_shares[item] += delta;
        }

        // Active Beaver triple sacrifice over `wire`: check each live triple `0..additional`
        // against `SAC_COMPANIONS = 2` companion triples (`(p^2 - 1)^-2 < 2^-255` soundness)
        // before sealing any triple into `ext2_blind_pool`.
        let sac_view = h32(
            b"personal-release/ext2-blind-sac-view",
            &[&refill_sid, &coin, &self.transcript],
        );
        let sac_coin = joint_coin_over_wire(
            wire,
            &self.roster,
            &refill_sid,
            b"ext2-blind-sac",
            &sac_view,
            false,
            rng,
        )?;
        let mut sac_xof = Cshake256Xof::new_shake256();
        sac_xof.absorb(b"personal-release/ext2-blind-sac-theta");
        sac_xof.absorb(&refill_sid);
        sac_xof.absorb(&sac_coin);
        let sac_pairs = additional * SAC_COMPANIONS;
        let mut thetas = Vec::with_capacity(sac_pairs);
        for _ in 0..sac_pairs {
            let t = loop {
                let mut bytes = [0u8; 48];
                sac_xof.squeeze(&mut bytes);
                let cand = decode_pad48_ext2(&bytes);
                wipe_bytes(&mut bytes);
                if !cand.ct_eq(GoldilocksExt2::ZERO) {
                    break cand;
                }
            };
            thetas.push(t);
        }

        let mut uv_me = SecretBuffer(Vec::with_capacity(2 * sac_pairs));
        for k in 0..additional {
            for j in 0..SAC_COMPANIONS {
                let comp = (1 + j) * additional + k;
                let theta = thetas[k * SAC_COMPANIONS + j];
                uv_me.push(theta * r_shares[k] - r_shares[comp]);
                uv_me.push(a_shares[k] - a_shares[comp]);
            }
        }
        let uv_open = commit_and_open_ext2_vec_over_wire(
            wire,
            &self.roster,
            &refill_sid,
            b"ext2-blind-sac-uv",
            0,
            &uv_me,
            rng,
        )?;

        let mut s_me = SecretBuffer(Vec::with_capacity(sac_pairs));
        for k in 0..additional {
            for j in 0..SAC_COMPANIONS {
                let comp = (1 + j) * additional + k;
                let pair_idx = k * SAC_COMPANIONS + j;
                let theta = thetas[pair_idx];
                let u = uv_open[2 * pair_idx];
                let v = uv_open[2 * pair_idx + 1];
                let mut s =
                    theta * c_shares[k] - c_shares[comp] - v * r_shares[comp] - u * a_shares[comp];
                if self.me == 0 {
                    s -= u * v;
                }
                s_me.push(s);
            }
        }
        let s_open = commit_and_open_ext2_vec_over_wire(
            wire,
            &self.roster,
            &refill_sid,
            b"ext2-blind-sac-s",
            1,
            &s_me,
            rng,
        )?;
        let mut all_zero = true;
        for &s in &s_open {
            all_zero &= s.ct_eq(GoldilocksExt2::ZERO);
        }
        if !all_zero {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::SacrificeResidualNonZero {
                    phase: "personal_release_ext2_blind",
                },
            )));
        }

        self.ext2_blind_pool.reserve(additional);
        for k in 0..additional {
            self.ext2_blind_pool.push(WireExt2BlindTriple {
                r: r_shares[k],
                a: a_shares[k],
                c: c_shares[k],
            });
        }
        Ok(())
    }

    /// Multiplicatively blind and open additive `GoldilocksExt2` residual share `d_me`:
    /// opens `e = d + A` then `w = R * d`, checking `w == 0` in constant time and poisoning
    /// on any non-zero residual (`0` leakage of the global SPDZ MAC key `\alpha`).
    fn blind_check_zero_ext2<T: WireTransport>(
        &mut self,
        wire: &mut T,
        session_id: &[u8; 32],
        phase: &'static str,
        d_me: GoldilocksExt2,
        rng: &mut PartyPrivateRng,
    ) -> Result<(), PersonalReleaseError> {
        if self.staged_ext2_blinding() == 0 {
            self.prestage_ext2_blinding(wire, 4, rng)?;
        }
        let idx = self.ext2_blind_cursor;
        self.ext2_blind_cursor += 1;
        let triple = core::mem::replace(
            &mut self.ext2_blind_pool[idx],
            WireExt2BlindTriple {
                r: GoldilocksExt2::ZERO,
                a: GoldilocksExt2::ZERO,
                c: GoldilocksExt2::ZERO,
            },
        );
        let mut e_me = SecretBuffer(d_me + triple.a);
        let e_open = match commit_and_open_ext2_over_wire(
            wire,
            &self.roster,
            session_id,
            phase.as_bytes(),
            0,
            *e_me,
            rng,
        ) {
            Ok(v) => v,
            Err(err) => {
                self.poison_and_wipe();
                return Err(err);
            }
        };
        wipe_ext2(core::slice::from_mut(&mut *e_me));
        let mut w_me = SecretBuffer(triple.r * e_open - triple.c);
        drop(triple);
        let w_open = match commit_and_open_ext2_over_wire(
            wire,
            &self.roster,
            session_id,
            phase.as_bytes(),
            1,
            *w_me,
            rng,
        ) {
            Ok(v) => v,
            Err(err) => {
                self.poison_and_wipe();
                return Err(err);
            }
        };
        wipe_ext2(core::slice::from_mut(&mut *w_me));
        if !w_open.ct_eq(GoldilocksExt2::ZERO) {
            self.poison_and_wipe();
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::MacCheckFailed {
                    phase,
                    accused_party: None,
                },
            )));
        }
        Ok(())
    }
}

#[inline]
fn decode_pad48_ext2(pad: &[u8; 48]) -> GoldilocksExt2 {
    GoldilocksExt2::new(
        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| pad[i])),
        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| pad[24 + i])),
    )
}

#[inline]
fn decode_gl_be(raw: &[u8]) -> Option<Goldilocks> {
    let b8: [u8; 8] = raw.try_into().ok()?;
    Goldilocks::from_be_bytes_canonical(b8).ok()
}

#[inline]
fn decode_ext2_be(raw: &[u8]) -> Option<GoldilocksExt2> {
    if raw.len() != 16 {
        return None;
    }
    let c0 = decode_gl_be(&raw[0..8])?;
    let c1 = decode_gl_be(&raw[8..16])?;
    Some(GoldilocksExt2::new(c0, c1))
}

#[inline]
fn ct_select_ext2(choice_bit: u64, ct0: GoldilocksExt2, ct1: GoldilocksExt2) -> GoldilocksExt2 {
    let select = 0u64.wrapping_sub(black_box(choice_bit & 1));
    GoldilocksExt2::new(
        Goldilocks::from_u64_reduced(
            ct0.c0.to_canonical_u64()
                ^ (select & (ct0.c0.to_canonical_u64() ^ ct1.c0.to_canonical_u64())),
        ),
        Goldilocks::from_u64_reduced(
            ct0.c1.to_canonical_u64()
                ^ (select & (ct0.c1.to_canonical_u64() ^ ct1.c1.to_canonical_u64())),
        ),
    )
}

fn recv_wire<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    peer: usize,
    round: u32,
) -> Result<SecretBuffer<Vec<u8>>, PersonalReleaseError> {
    match wire.recv_frame(peer, round) {
        Ok(payload) => Ok(SecretBuffer(payload)),
        Err(TransportError::RoundTagMismatch {
            got: ROUND_ABORT, ..
        }) => Err(PersonalReleaseError::PeerAborted {
            party: roster[peer],
        }),
        Err(e) => Err(PersonalReleaseError::Transport(e)),
    }
}

fn send_abort_all<T: WireTransport>(wire: &mut T) {
    let me = wire.party();
    let m = wire.parties();
    for peer in 0..m {
        if peer != me {
            let _ = wire.send_frame(peer, ROUND_ABORT, &[]);
        }
    }
}

/// Broadcast `payload` to all `peer != me` and collect `m` payloads in canonical `0..m` order.
fn broadcast_collect<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    round: u32,
    my_payload: &[u8],
) -> Result<SecretBuffer<Vec<Vec<u8>>>, PersonalReleaseError> {
    let me = wire.party();
    let m = wire.parties();
    for peer in 0..m {
        if peer != me {
            wire.send_frame(peer, round, my_payload)?;
        }
    }
    let mut out = SecretBuffer(vec![Vec::new(); m]);
    out[me] = my_payload.to_vec();
    for peer in 0..m {
        if peer != me {
            let mut raw = recv_wire(wire, roster, peer, round)?;
            out[peer] = core::mem::take(&mut raw.0);
        }
    }
    Ok(out)
}

/// Commit-then-open joint 256-bit coin with echo-commitment consistency check across all `m` signers.
fn joint_coin_over_wire<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    session_id: &[u8; 32],
    label: &[u8],
    bind: &[u8; 32],
    require_identical_bind: bool,
    rng: &mut PartyPrivateRng,
) -> Result<[u8; 32], PersonalReleaseError> {
    let me = wire.party();
    let m = wire.parties();
    let my_share = SecretBuffer(rng.next_bytes32());
    let my_com = h32(
        b"personal-release/coin-com",
        &[
            session_id,
            label,
            bind,
            &(me as u64).to_be_bytes(),
            &*my_share,
        ],
    );
    let mut com_frame = [0u8; 64];
    com_frame[0..32].copy_from_slice(&my_com);
    com_frame[32..64].copy_from_slice(bind);
    let com_frames = broadcast_collect(wire, roster, ROUND_PREL_COIN_COM, &com_frame)?;

    let mut coms = vec![[0u8; 32]; m];
    let mut binds = vec![[0u8; 32]; m];
    let mut all_coms_flat = Vec::with_capacity(m * 64);
    for p in 0..m {
        if com_frames[p].len() != 64 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_COIN_COM,
            });
        }
        coms[p].copy_from_slice(&com_frames[p][0..32]);
        binds[p].copy_from_slice(&com_frames[p][32..64]);
        if require_identical_bind && !ct_eq_bytes32(&binds[p], bind) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::CoinCommitMismatch { party_id: p },
            )));
        }
        all_coms_flat.extend_from_slice(&com_frames[p]);
    }
    let echo_digest = h32(
        b"personal-release/coin-echo",
        &[session_id, label, &all_coms_flat],
    );
    let mut open_payload = SecretBuffer([0u8; 64]);
    open_payload[0..32].copy_from_slice(&*my_share);
    open_payload[32..64].copy_from_slice(&echo_digest);
    let opens = broadcast_collect(wire, roster, ROUND_PREL_COIN_OPEN, &*open_payload)?;

    let mut coin = [0u8; 32];
    for p in 0..m {
        if opens[p].len() != 64 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_COIN_OPEN,
            });
        }
        let mut peer_share = [0u8; 32];
        let mut peer_echo = [0u8; 32];
        peer_share.copy_from_slice(&opens[p][0..32]);
        peer_echo.copy_from_slice(&opens[p][32..64]);
        if !ct_eq_bytes32(&peer_echo, &echo_digest) {
            wipe_bytes32(&mut peer_share);
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::CoinCommitMismatch { party_id: p },
            )));
        }
        let exp = h32(
            b"personal-release/coin-com",
            &[
                session_id,
                label,
                &binds[p],
                &(p as u64).to_be_bytes(),
                &peer_share,
            ],
        );
        if !ct_eq_bytes32(&exp, &coms[p]) {
            wipe_bytes32(&mut peer_share);
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::CoinCommitMismatch { party_id: p },
            )));
        }
        for (dst, &src) in coin.iter_mut().zip(&peer_share) {
            *dst ^= src;
        }
        wipe_bytes32(&mut peer_share);
    }
    Ok(coin)
}

/// Commit-before-open sum of additive `GoldilocksExt2` shares across all `m` signers.
fn commit_and_open_ext2_over_wire<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    session_id: &[u8; 32],
    phase: &[u8],
    sub_step: u64,
    my_share: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Result<GoldilocksExt2, PersonalReleaseError> {
    let me = wire.party();
    let m = wire.parties();
    let salt = SecretBuffer(rng.next_bytes32());
    let share_be = SecretBuffer(my_share.to_be_bytes());
    let step_be = sub_step.to_be_bytes();
    let my_com = h32(
        b"personal-release/ext2-open-com",
        &[
            session_id,
            phase,
            &step_be,
            &(me as u64).to_be_bytes(),
            &*share_be,
            &*salt,
        ],
    );
    let coms = broadcast_collect(wire, roster, ROUND_PREL_COMMIT, &my_com)?;

    let mut all_coms_flat = Vec::with_capacity(m * 32);
    for p in 0..m {
        if coms[p].len() != 32 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_COMMIT,
            });
        }
        all_coms_flat.extend_from_slice(&coms[p]);
    }
    let echo = h32(
        b"personal-release/ext2-open-echo",
        &[session_id, &all_coms_flat],
    );
    let mut open_frame = SecretBuffer([0u8; 80]);
    open_frame[0..16].copy_from_slice(&*share_be);
    open_frame[16..48].copy_from_slice(&*salt);
    open_frame[48..80].copy_from_slice(&echo);
    let opens = broadcast_collect(wire, roster, ROUND_PREL_OPEN, &*open_frame)?;

    let mut total = GoldilocksExt2::ZERO;
    for p in 0..m {
        if opens[p].len() != 80 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_OPEN,
            });
        }
        let sh =
            decode_ext2_be(&opens[p][0..16]).ok_or(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_OPEN,
            })?;
        let mut peer_echo = [0u8; 32];
        peer_echo.copy_from_slice(&opens[p][48..80]);
        if !ct_eq_bytes32(&peer_echo, &echo) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch {
                    phase: "personal_release_ext2_open",
                    party_id: p,
                },
            )));
        }
        let exp = h32(
            b"personal-release/ext2-open-com",
            &[
                session_id,
                phase,
                &step_be,
                &(p as u64).to_be_bytes(),
                &opens[p][0..16],
                &opens[p][16..48],
            ],
        );
        let mut peer_com = [0u8; 32];
        peer_com.copy_from_slice(&coms[p]);
        if !ct_eq_bytes32(&exp, &peer_com) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch {
                    phase: "personal_release_ext2_open",
                    party_id: p,
                },
            )));
        }
        total += sh;
    }
    Ok(total)
}

/// Commit-before-open elementwise sum of additive `GoldilocksExt2` vectors across all `m` signers.
fn commit_and_open_ext2_vec_over_wire<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    session_id: &[u8; 32],
    phase: &[u8],
    sub_step: u64,
    my_shares: &[GoldilocksExt2],
    rng: &mut PartyPrivateRng,
) -> Result<Vec<GoldilocksExt2>, PersonalReleaseError> {
    let me = wire.party();
    let m = wire.parties();
    let count = my_shares.len();
    let salt = SecretBuffer(rng.next_bytes32());
    let mut shares_be = SecretBuffer(Vec::with_capacity(16 * count));
    for &sh in my_shares {
        shares_be.extend_from_slice(&sh.to_be_bytes());
    }
    let step_be = sub_step.to_be_bytes();
    let len_be = (count as u64).to_be_bytes();
    let my_com = h32(
        b"personal-release/ext2-vec-open-com",
        &[
            session_id,
            phase,
            &step_be,
            &len_be,
            &(me as u64).to_be_bytes(),
            &shares_be,
            &*salt,
        ],
    );
    let coms = broadcast_collect(wire, roster, ROUND_PREL_COMMIT, &my_com)?;

    let mut all_coms_flat = Vec::with_capacity(m * 32);
    for p in 0..m {
        if coms[p].len() != 32 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_COMMIT,
            });
        }
        all_coms_flat.extend_from_slice(&coms[p]);
    }
    let echo = h32(
        b"personal-release/ext2-vec-open-echo",
        &[session_id, phase, &step_be, &len_be, &all_coms_flat],
    );
    let expected_open_len = 16 * count + 64;
    let mut open_frame = SecretBuffer(Vec::with_capacity(expected_open_len));
    open_frame.extend_from_slice(&shares_be);
    open_frame.extend_from_slice(&*salt);
    open_frame.extend_from_slice(&echo);
    let opens = broadcast_collect(wire, roster, ROUND_PREL_OPEN, &open_frame)?;

    let mut totals = vec![GoldilocksExt2::ZERO; count];
    for p in 0..m {
        if opens[p].len() != expected_open_len {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_OPEN,
            });
        }
        let share_bytes = &opens[p][0..16 * count];
        let salt_bytes = &opens[p][16 * count..16 * count + 32];
        let mut peer_echo = [0u8; 32];
        peer_echo.copy_from_slice(&opens[p][16 * count + 32..expected_open_len]);
        if !ct_eq_bytes32(&peer_echo, &echo) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch {
                    phase: "personal_release_ext2_vec_open",
                    party_id: p,
                },
            )));
        }
        let exp = h32(
            b"personal-release/ext2-vec-open-com",
            &[
                session_id,
                phase,
                &step_be,
                &len_be,
                &(p as u64).to_be_bytes(),
                share_bytes,
                salt_bytes,
            ],
        );
        let mut peer_com = [0u8; 32];
        peer_com.copy_from_slice(&coms[p]);
        if !ct_eq_bytes32(&exp, &peer_com) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch {
                    phase: "personal_release_ext2_vec_open",
                    party_id: p,
                },
            )));
        }
        for k in 0..count {
            let sh = decode_ext2_be(&share_bytes[16 * k..16 * k + 16]).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: roster[p],
                    round: ROUND_PREL_OPEN,
                },
            )?;
            totals[k] += sh;
        }
    }
    Ok(totals)
}

#[derive(Clone, Copy)]
struct LocalAuthWire {
    val: Goldilocks,
    mac: GoldilocksExt2,
}

impl LocalAuthWire {
    const ZERO: Self = Self {
        val: Goldilocks::ZERO,
        mac: GoldilocksExt2::ZERO,
    };

    #[inline]
    fn public_const(c: Goldilocks, me: usize, alpha_me: GoldilocksExt2) -> Self {
        Self {
            val: if me == 0 { c } else { Goldilocks::ZERO },
            mac: alpha_me.mul_base(c),
        }
    }

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self {
            val: self.val + rhs.val,
            mac: self.mac + rhs.mac,
        }
    }

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            val: self.val - rhs.val,
            mac: self.mac - rhs.mac,
        }
    }

    #[inline]
    fn scale(self, c: Goldilocks) -> Self {
        Self {
            val: self.val * c,
            mac: self.mac.mul_base(c),
        }
    }

    #[inline]
    fn neg(self) -> Self {
        Self {
            val: self.val.const_neg(),
            mac: GoldilocksExt2::ZERO - self.mac,
        }
    }
}

impl SecretWipe for LocalAuthWire {
    #[inline]
    fn secret_wipe(&mut self) {
        self.val.secret_wipe();
        self.mac.secret_wipe();
    }
}

#[inline]
fn apply_m4_local(b: [LocalAuthWire; 4]) -> [LocalAuthWire; 4] {
    let s = b[0].add(b[1]).add(b[2].add(b[3]));
    [
        s.add(b[0].add(b[1].scale(Goldilocks::TWO))),
        s.add(b[1].add(b[2].scale(Goldilocks::TWO))),
        s.add(b[2].add(b[3].scale(Goldilocks::TWO))),
        s.add(b[3].add(b[0].scale(Goldilocks::TWO))),
    ]
}

fn apply_me_local(st: &mut [LocalAuthWire; 12]) {
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
    let y0 = apply_m4_local([st[0], st[1], st[2], st[3]]);
    let y1 = apply_m4_local([st[4], st[5], st[6], st[7]]);
    let y2 = apply_m4_local([st[8], st[9], st[10], st[11]]);
    for i in 0..4 {
        let s = y0[i].add(y1[i]).add(y2[i]);
        st[i] = y0[i].add(s);
        st[4 + i] = y1[i].add(s);
        st[8 + i] = y2[i].add(s);
    }
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}

fn apply_mi_local(st: &mut [LocalAuthWire; 12]) {
    let mut s = LocalAuthWire::ZERO;
    for lane in st.iter() {
        s = s.add(*lane);
    }
    st[0] = st[0].scale(Goldilocks::from_u64_reduced(64)).neg().add(s);
    st[1] = st[1].add(s);
    let mut d = Goldilocks::TWO;
    for lane in st.iter_mut().skip(2) {
        *lane = lane.scale(d).add(s);
        d = d + d;
    }
}

/// Commit-before-open batch of authenticated `Goldilocks` wires followed by a pooled
/// multiplicatively blinded `GoldilocksExt2` `MacCheck` before returning the opened values.
#[expect(
    clippy::too_many_arguments,
    reason = "Wire transport, roster, session/phase labels, round tags, wires, MAC key and RNG are distinct protocol inputs"
)]
fn commit_open_and_check_goldilocks_over_wire<T: WireTransport>(
    wire: &mut T,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    session_id: &[u8; 32],
    phase: &'static str,
    com_round: u32,
    open_round: u32,
    wires: &[LocalAuthWire],
    alpha_me: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Result<Vec<Goldilocks>, PersonalReleaseError> {
    let count = wires.len();
    if count == 0 {
        return Ok(Vec::new());
    }
    let me = wire.party();
    let m = wire.parties();
    let salt = SecretBuffer(rng.next_bytes32());
    let mut share_bytes = SecretBuffer(Vec::with_capacity(count * 8));
    for w in wires {
        share_bytes.extend_from_slice(&w.val.to_be_bytes());
    }
    let my_com = h32(
        b"personal-release/gl-batch-com",
        &[
            session_id,
            phase.as_bytes(),
            &(me as u64).to_be_bytes(),
            &share_bytes,
            &*salt,
        ],
    );
    let coms = broadcast_collect(wire, roster, com_round, &my_com)?;
    let mut all_coms_flat = Vec::with_capacity(m * 32);
    for p in 0..m {
        if coms[p].len() != 32 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: com_round,
            });
        }
        all_coms_flat.extend_from_slice(&coms[p]);
    }
    let echo = h32(
        b"personal-release/gl-batch-echo",
        &[session_id, &all_coms_flat],
    );

    let mut open_payload = SecretBuffer(Vec::with_capacity(count * 8 + 64));
    open_payload.extend_from_slice(&share_bytes);
    open_payload.extend_from_slice(&*salt);
    open_payload.extend_from_slice(&echo);
    let opens = broadcast_collect(wire, roster, open_round, &open_payload)?;

    let mut opened = vec![Goldilocks::ZERO; count];
    for p in 0..m {
        if opens[p].len() != count * 8 + 64 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: open_round,
            });
        }
        let mut peer_echo = [0u8; 32];
        peer_echo.copy_from_slice(&opens[p][count * 8 + 32..count * 8 + 64]);
        if !ct_eq_bytes32(&peer_echo, &echo) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch { phase, party_id: p },
            )));
        }
        let exp = h32(
            b"personal-release/gl-batch-com",
            &[
                session_id,
                phase.as_bytes(),
                &(p as u64).to_be_bytes(),
                &opens[p][..count * 8],
                &opens[p][count * 8..count * 8 + 32],
            ],
        );
        let mut peer_com = [0u8; 32];
        peer_com.copy_from_slice(&coms[p]);
        if !ct_eq_bytes32(&exp, &peer_com) {
            return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                PreprocessError::ShareCommitMismatch { phase, party_id: p },
            )));
        }
        for (k, acc) in opened.iter_mut().enumerate() {
            let limb = decode_gl_be(&opens[p][8 * k..8 * k + 8]).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: roster[p],
                    round: open_round,
                },
            )?;
            *acc += limb;
        }
    }

    let mut open_bytes = Vec::with_capacity(count * 8);
    for &v in &opened {
        open_bytes.extend_from_slice(&v.to_be_bytes());
    }
    let open_digest = h32(
        b"personal-release/gl-batch-dig",
        &[session_id, phase.as_bytes(), &open_bytes],
    );
    let fold_coin = joint_coin_over_wire(
        wire,
        roster,
        session_id,
        phase.as_bytes(),
        &open_digest,
        true,
        rng,
    )?;
    let mut xof = Cshake256Xof::new_shake256();
    xof.absorb(b"personal-release/gl-batch-chis");
    xof.absorb(&fold_coin);

    let mut x_folded = GoldilocksExt2::ZERO;
    let mut m_folded = SecretBuffer(GoldilocksExt2::ZERO);
    for (w, &pub_val) in wires.iter().zip(&opened) {
        let mut b48 = [0u8; 48];
        xof.squeeze(&mut b48);
        let chi = decode_pad48_ext2(&b48);
        x_folded += chi.mul_base(pub_val);
        *m_folded += chi * w.mac;
    }
    let residual = SecretBuffer(*m_folded - alpha_me * x_folded);
    ot.blind_check_zero_ext2(wire, session_id, phase, *residual, rng)?;
    Ok(opened)
}

/// Pairwise LHL Gilboa OLE over `Goldilocks` in `512`-element frames (`< 2.7 MiB` per wire frame).
fn pairwise_gilboa_ole_over_wire<T: WireTransport>(
    wire: &mut T,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    session_id: &[u8; 32],
    u_me: &[Goldilocks],
    v_me: &[Goldilocks],
    rng: &mut PartyPrivateRng,
) -> Result<SecretBuffer<Vec<Goldilocks>>, PersonalReleaseError> {
    const CHUNK: usize = 384;
    const WORDS_PER_ITEM: usize = 5;
    const BITS_PER_ITEM: usize = 64 * WORDS_PER_ITEM;
    let total = u_me.len();
    let m = wire.parties();
    let mut w_me = SecretBuffer(
        u_me.iter()
            .zip(v_me)
            .map(|(&u, &v)| u * v)
            .collect::<Vec<Goldilocks>>(),
    );

    for (chunk_idx, start) in (0..total).step_by(CHUNK).enumerate() {
        let end = (start + CHUNK).min(total);
        let count = end - start;
        let total_words = count * WORDS_PER_ITEM;
        let total_bits = count * BITS_PER_ITEM;
        let chunk_sid = h32(
            b"personal-release/ole-gl-chunk",
            &[session_id, &(chunk_idx as u64).to_be_bytes()],
        );
        let r_words = SecretBuffer(
            (0..total_words)
                .map(|_| rng.next_u64())
                .collect::<Vec<u64>>(),
        );
        // `sender_masks[receiver][bit]` for when `me == sender`, and `recv_terms[sender][bit]` for `me == receiver`.
        let mut sender_masks = SecretBuffer(vec![vec![Goldilocks::ZERO; total_bits]; m]);
        let mut recv_terms = SecretBuffer(vec![vec![Goldilocks::ZERO; total_bits]; m]);
        let mut ct_bind = h32(b"personal-release/ole-gl-ct0", &[&chunk_sid]);

        for a in 0..m {
            for b in (a + 1)..m {
                for (sender, receiver) in [(a, b), (b, a)] {
                    let pads = ot.run_directed_kos(wire, sender, receiver, &r_words, rng)?;
                    if wire.party() == sender {
                        let (send_pads, _) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let mut frame = SecretBuffer(Vec::with_capacity(total_bits * 16));
                        for k in 0..count {
                            let vj = v_me[start + k];
                            let base_bit = k * BITS_PER_ITEM;
                            for bit_off in 0..BITS_PER_ITEM {
                                let bit = base_bit + bit_off;
                                let pad0 =
                                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| {
                                        send_pads[bit].0[i]
                                    }));
                                let pad1 =
                                    Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| {
                                        send_pads[bit].1[i]
                                    }));
                                let mask = rng.next_goldilocks();
                                sender_masks[receiver][bit] = mask;
                                let ct0 = pad0 - mask;
                                let ct1 = vj - mask + pad1;
                                frame.extend_from_slice(&ct0.to_be_bytes());
                                frame.extend_from_slice(&ct1.to_be_bytes());
                            }
                        }
                        ct_bind = h32(
                            b"personal-release/ole-gl-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &frame,
                            ],
                        );
                        wire.send_frame(receiver, ROUND_PREL_OLE_CT, &frame)?;
                    } else if wire.party() == receiver {
                        let (_, recv_pads) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let raw = recv_wire(wire, roster, sender, ROUND_PREL_OLE_CT)?;
                        if raw.len() != total_bits * 16 {
                            ot.poison_and_wipe();
                            return Err(PersonalReleaseError::MalformedWireMessage {
                                from: roster[sender],
                                round: ROUND_PREL_OLE_CT,
                            });
                        }
                        ct_bind = h32(
                            b"personal-release/ole-gl-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &raw,
                            ],
                        );
                        for bit in 0..total_bits {
                            let off = bit * 16;
                            let ct0 = decode_gl_be(&raw[off..off + 8]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let ct1 = decode_gl_be(&raw[off + 8..off + 16]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let choice = (r_words[bit / 64] >> (bit % 64)) & 1;
                            let mask64 = 0u64.wrapping_sub(black_box(choice));
                            let sel = Goldilocks::from_u64_reduced(
                                ct0.to_canonical_u64()
                                    ^ (mask64 & (ct0.to_canonical_u64() ^ ct1.to_canonical_u64())),
                            );
                            let pad_c =
                                Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| {
                                    recv_pads[bit][i]
                                }));
                            recv_terms[sender][bit] = sel - pad_c;
                        }
                    }
                }
            }
        }

        let local_view = h32(b"personal-release/ole-gl-view", &[&ct_bind, &ot.transcript]);
        let lhl_coin = joint_coin_over_wire(
            wire,
            roster,
            &chunk_sid,
            b"ole-gl-lhl",
            &local_view,
            false,
            rng,
        )?;
        let mut g_xof = Cshake256Xof::new_shake256();
        g_xof.absorb(b"personal-release/ole-gl-g");
        g_xof.absorb(&lhl_coin);
        let mut g_weights = [Goldilocks::ZERO; BITS_PER_ITEM];
        for gw in &mut g_weights {
            let mut b24 = [0u8; 24];
            g_xof.squeeze(&mut b24);
            *gw = Goldilocks::from_bytes24_unbiased(&b24);
        }

        let mut my_diff_bytes = SecretBuffer(Vec::with_capacity(count * 8));
        for k in 0..count {
            let mut u_comb = Goldilocks::ZERO;
            let base_bit = k * BITS_PER_ITEM;
            for (s, &gw) in g_weights.iter().enumerate() {
                let bit = base_bit + s;
                let b_mask = 0u64.wrapping_sub(black_box((r_words[bit / 64] >> (bit % 64)) & 1));
                u_comb += Goldilocks::from_u64_reduced(b_mask & gw.to_canonical_u64());
            }
            let diff = u_me[start + k] - u_comb;
            my_diff_bytes.extend_from_slice(&diff.to_be_bytes());
        }
        let all_diffs = broadcast_collect(wire, roster, ROUND_PREL_OLE_DIFF, &my_diff_bytes)?;
        for peer in 0..m {
            if peer == wire.party() {
                continue;
            }
            if all_diffs[peer].len() != count * 8 {
                return Err(PersonalReleaseError::MalformedWireMessage {
                    from: roster[peer],
                    round: ROUND_PREL_OLE_DIFF,
                });
            }
            for k in 0..count {
                let diff_peer = decode_gl_be(&all_diffs[peer][8 * k..8 * k + 8]).ok_or(
                    PersonalReleaseError::MalformedWireMessage {
                        from: roster[peer],
                        round: ROUND_PREL_OLE_DIFF,
                    },
                )?;
                let base_bit = k * BITS_PER_ITEM;
                let mut s_acc = diff_peer * v_me[start + k];
                let mut r_acc = Goldilocks::ZERO;
                for (s, &gw) in g_weights.iter().enumerate() {
                    let bit = base_bit + s;
                    s_acc += gw * sender_masks[peer][bit];
                    r_acc += gw * recv_terms[peer][bit];
                }
                w_me[start + k] += s_acc + r_acc;
            }
        }
    }
    Ok(w_me)
}

/// Dealerless `Π_MAC` authenticating additive `Goldilocks` shares under `\alpha = \sum \alpha_u \in F_{p^2}`
/// in 32-element Toeplitz blocks with batch `F_{p^2}` linear check + blinded zero check.
fn authenticate_goldilocks_batch_over_wire<T: WireTransport>(
    wire: &mut T,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    session_id: &[u8; 32],
    alpha_me: GoldilocksExt2,
    x_me: &[Goldilocks],
    rng: &mut PartyPrivateRng,
) -> Result<SecretBuffer<Vec<GoldilocksExt2>>, PersonalReleaseError> {
    const BLOCK: usize = 32;
    let total = x_me.len();
    let m = wire.parties();
    let mut out = SecretBuffer(Vec::with_capacity(total));
    let two_pow_64_mod_p = Goldilocks::from_u64_reduced((1u64 << 32) - 1);
    let two_pow_128_mod_p = two_pow_64_mod_p * two_pow_64_mod_p;

    for (blk_idx, start) in (0..total).step_by(BLOCK).enumerate() {
        let end = (start + BLOCK).min(total);
        let count = end - start;
        let blk_sid = h32(
            b"personal-release/pimac-block",
            &[session_id, &(blk_idx as u64).to_be_bytes()],
        );
        let r_pad_me = SecretBuffer([rng.next_goldilocks(), rng.next_goldilocks()]);
        let total_items = count + 2;
        let m_words = total_items + 4;
        let m_bits = 64 * m_words;

        let mut u_target = SecretBuffer(Vec::with_capacity(total_items));
        u_target.extend_from_slice(&x_me[start..end]);
        u_target.push(r_pad_me[0]);
        u_target.push(r_pad_me[1]);

        let r_words = SecretBuffer((0..m_words).map(|_| rng.next_u64()).collect::<Vec<u64>>());
        let mut raw_sum = SecretBuffer(vec![GoldilocksExt2::ZERO; m_bits]);
        for (s, slot) in raw_sum.iter_mut().enumerate() {
            let bit_val = (r_words[s / 64] >> (s % 64)) & 1;
            *slot = alpha_me.mul_base(Goldilocks::from_u64_reduced(bit_val));
        }

        let mut ct_bind = h32(b"personal-release/pimac-ct0", &[&blk_sid]);
        for a in 0..m {
            for b in (a + 1)..m {
                for (sender, receiver) in [(a, b), (b, a)] {
                    let pads = ot.run_directed_kos(wire, sender, receiver, &r_words, rng)?;
                    if wire.party() == sender {
                        let (send_pads, _) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let mut frame = SecretBuffer(Vec::with_capacity(m_bits * 32));
                        for (s, acc) in raw_sum.iter_mut().enumerate() {
                            let pad0 = decode_pad48_ext2(&send_pads[s].0);
                            let pad1 = decode_pad48_ext2(&send_pads[s].1);
                            let mask = rng.next_ext2();
                            *acc += mask;
                            let ct0 = pad0 - mask;
                            let ct1 = alpha_me - mask + pad1;
                            frame.extend_from_slice(&ct0.to_be_bytes());
                            frame.extend_from_slice(&ct1.to_be_bytes());
                        }
                        ct_bind = h32(
                            b"personal-release/pimac-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &frame,
                            ],
                        );
                        wire.send_frame(receiver, ROUND_PREL_OLE_CT, &frame)?;
                    } else if wire.party() == receiver {
                        let (_, recv_pads) =
                            pads.ok_or(PersonalReleaseError::LaneRosterMismatch)?;
                        let raw = recv_wire(wire, roster, sender, ROUND_PREL_OLE_CT)?;
                        if raw.len() != m_bits * 32 {
                            ot.poison_and_wipe();
                            return Err(PersonalReleaseError::MalformedWireMessage {
                                from: roster[sender],
                                round: ROUND_PREL_OLE_CT,
                            });
                        }
                        ct_bind = h32(
                            b"personal-release/pimac-ct-pair",
                            &[
                                &ct_bind,
                                &(sender as u64).to_be_bytes(),
                                &(receiver as u64).to_be_bytes(),
                                &raw,
                            ],
                        );
                        for (s, acc) in raw_sum.iter_mut().enumerate() {
                            let off = s * 32;
                            let ct0 = decode_ext2_be(&raw[off..off + 16]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let ct1 = decode_ext2_be(&raw[off + 16..off + 32]).ok_or(
                                PersonalReleaseError::MalformedWireMessage {
                                    from: roster[sender],
                                    round: ROUND_PREL_OLE_CT,
                                },
                            )?;
                            let choice = (r_words[s / 64] >> (s % 64)) & 1;
                            *acc +=
                                ct_select_ext2(choice, ct0, ct1) - decode_pad48_ext2(&recv_pads[s]);
                        }
                    }
                }
            }
        }

        let local_view = h32(b"personal-release/pimac-view", &[&ct_bind, &ot.transcript]);
        let lhl_coin = joint_coin_over_wire(
            wire,
            roster,
            &blk_sid,
            b"pimac-lhl",
            &local_view,
            false,
            rng,
        )?;
        let mut h_xof = Cshake256Xof::new_shake256();
        h_xof.absorb(b"personal-release/pimac-toeplitz");
        h_xof.absorb(&lhl_coin);
        let mut toeplitz_u64 = vec![0u64; total_items + m_bits];
        for slot in &mut toeplitz_u64 {
            let mut b24 = [0u8; 24];
            h_xof.squeeze(&mut b24);
            *slot = Goldilocks::from_bytes24_unbiased(&b24).to_canonical_u64();
        }

        let mut my_diff_bytes = SecretBuffer(Vec::with_capacity(total_items * 8));
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc_u128 = 0u128;
            for w in 0..m_words {
                let rw = black_box(r_words[w]);
                let h_word = &h_row[64 * w..64 * (w + 1)];
                for (b, &h) in h_word.iter().enumerate() {
                    let mask = 0u64.wrapping_sub((rw >> b) & 1);
                    acc_u128 += (mask & h) as u128;
                }
            }
            let diff = u_target[idx] - Goldilocks::reduce128(acc_u128);
            my_diff_bytes.extend_from_slice(&diff.to_be_bytes());
        }
        let all_diffs = broadcast_collect(wire, roster, ROUND_PREL_OLE_DIFF, &my_diff_bytes)?;
        let mut diff_sum = SecretBuffer(vec![Goldilocks::ZERO; total_items]);
        for p in 0..m {
            if all_diffs[p].len() != total_items * 8 {
                return Err(PersonalReleaseError::MalformedWireMessage {
                    from: roster[p],
                    round: ROUND_PREL_OLE_DIFF,
                });
            }
            for (idx, dst) in diff_sum.iter_mut().enumerate() {
                let d = decode_gl_be(&all_diffs[p][8 * idx..8 * idx + 8]).ok_or(
                    PersonalReleaseError::MalformedWireMessage {
                        from: roster[p],
                        round: ROUND_PREL_OLE_DIFF,
                    },
                )?;
                *dst += d;
            }
        }

        let mut blk_macs = SecretBuffer(vec![GoldilocksExt2::ZERO; total_items]);
        for idx in 0..total_items {
            let h_row = &toeplitz_u64[idx..idx + m_bits];
            let mut acc0_lo = 0u128;
            let mut acc0_hi = 0u64;
            let mut acc1_lo = 0u128;
            let mut acc1_hi = 0u64;
            for (s, &h_val) in h_row.iter().enumerate() {
                let h = h_val as u128;
                let (n0, ov0) =
                    acc0_lo.overflowing_add((raw_sum[s].c0.to_canonical_u64() as u128) * h);
                acc0_lo = n0;
                acc0_hi += ov0 as u64;
                let (n1, ov1) =
                    acc1_lo.overflowing_add((raw_sum[s].c1.to_canonical_u64() as u128) * h);
                acc1_lo = n1;
                acc1_hi += ov1 as u64;
            }
            let comb_c0 = Goldilocks::reduce128(acc0_lo)
                + Goldilocks::from_u64_reduced(acc0_hi) * two_pow_128_mod_p;
            let comb_c1 = Goldilocks::reduce128(acc1_lo)
                + Goldilocks::from_u64_reduced(acc1_hi) * two_pow_128_mod_p;
            blk_macs[idx] =
                alpha_me.mul_base(diff_sum[idx]) + GoldilocksExt2::new(comb_c0, comb_c1);
        }

        let chk_coin =
            joint_coin_over_wire(wire, roster, &blk_sid, b"pimac-chk", &lhl_coin, true, rng)?;
        let mut chk_xof = Cshake256Xof::new_shake256();
        chk_xof.absorb(b"personal-release/pimac-chis");
        chk_xof.absorb(&chk_coin);
        let ext_u = GoldilocksExt2::new(Goldilocks::ZERO, Goldilocks::ONE);
        let mut z_me = SecretBuffer(GoldilocksExt2::new(r_pad_me[0], r_pad_me[1]));
        let mut z_mac_me = SecretBuffer(blk_macs[count] + ext_u * blk_macs[count + 1]);
        for k in 0..count {
            let mut b48 = [0u8; 48];
            chk_xof.squeeze(&mut b48);
            let chi = decode_pad48_ext2(&b48);
            *z_me += chi.mul_base(x_me[start + k]);
            *z_mac_me += chi * blk_macs[k];
        }
        let z_open =
            commit_and_open_ext2_over_wire(wire, roster, &blk_sid, b"pimac-z", 0, *z_me, rng)?;
        let d_me = SecretBuffer(*z_mac_me - alpha_me * z_open);
        ot.blind_check_zero_ext2(wire, &blk_sid, "personal_release_pimac", *d_me, rng)?;
        out.extend_from_slice(&blk_macs[..count]);
    }
    Ok(out)
}

#[expect(
    clippy::too_many_arguments,
    reason = "Beaver multiplication batch takes transport, OT endpoint, roster, session/phase labels, operands, triples, MAC key and RNG"
)]
fn eval_beaver_batch_over_wire<T: WireTransport>(
    wire: &mut T,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    session_id: &[u8; 32],
    phase: &'static str,
    xs: &[LocalAuthWire],
    ys: &[LocalAuthWire],
    ta: &[LocalAuthWire],
    tb: &[LocalAuthWire],
    tc: &[LocalAuthWire],
    alpha_me: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Result<SecretBuffer<Vec<LocalAuthWire>>, PersonalReleaseError> {
    let count = xs.len();
    let me = wire.party();
    let mut de = SecretBuffer(Vec::with_capacity(2 * count));
    for k in 0..count {
        de.push(xs[k].sub(ta[k]));
        de.push(ys[k].sub(tb[k]));
    }
    let opened = commit_open_and_check_goldilocks_over_wire(
        wire,
        ot,
        roster,
        session_id,
        phase,
        ROUND_PREL_COMMIT,
        ROUND_PREL_OPEN,
        &de,
        alpha_me,
        rng,
    )?;
    let mut out = SecretBuffer(Vec::with_capacity(count));
    for k in 0..count {
        let delta = opened[2 * k];
        let eps = opened[2 * k + 1];
        let de_pub = LocalAuthWire::public_const(delta * eps, me, alpha_me);
        out.push(
            tc[k]
                .add(tb[k].scale(delta))
                .add(ta[k].scale(eps))
                .add(de_pub),
        );
    }
    Ok(out)
}

struct LocalPow7Tuple {
    pows: [LocalAuthWire; 7],
}

impl SecretWipe for LocalPow7Tuple {
    fn secret_wipe(&mut self) {
        for w in &mut self.pows {
            w.secret_wipe();
        }
    }
}

/// Generate `count` SPDZ-authenticated `Π_pow7` tuples (`[r, r^2, ..., r^7]`) over `wire`
/// using LHL Gilboa OLE + `GoldilocksExt2` companion sacrifice (`< 2^{-127}`) + 3-round Beaver tree.
fn generate_pow7_tuples_over_wire<T: WireTransport>(
    wire: &mut T,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    session_id: &[u8; 32],
    count: usize,
    alpha_me: GoldilocksExt2,
    rng: &mut PartyPrivateRng,
) -> Result<SecretBuffer<Vec<LocalPow7Tuple>>, PersonalReleaseError> {
    let base_triples = 6 * count;
    let ole_len = 3 * base_triples;
    let mut u_in = SecretBuffer(vec![Goldilocks::ZERO; ole_len]);
    let mut v_in = SecretBuffer(vec![Goldilocks::ZERO; ole_len]);
    for k in 0..base_triples {
        let a = rng.next_goldilocks();
        let b = rng.next_goldilocks();
        let at0 = rng.next_goldilocks();
        let at1 = rng.next_goldilocks();
        u_in[3 * k] = a;
        v_in[3 * k] = b;
        u_in[3 * k + 1] = at0;
        v_in[3 * k + 1] = b;
        u_in[3 * k + 2] = at1;
        v_in[3 * k + 2] = b;
    }
    let w_out = pairwise_gilboa_ole_over_wire(wire, ot, roster, session_id, &u_in, &v_in, rng)?;

    let r1_vals = SecretBuffer(
        (0..count)
            .map(|_| rng.next_goldilocks())
            .collect::<Vec<Goldilocks>>(),
    );
    let mut auth_pack = SecretBuffer(Vec::with_capacity(7 * base_triples + count));
    for k in 0..base_triples {
        auth_pack.push(u_in[3 * k]); // a
    }
    for k in 0..base_triples {
        auth_pack.push(v_in[3 * k]); // b
    }
    for k in 0..base_triples {
        auth_pack.push(w_out[3 * k]); // c
    }
    for k in 0..base_triples {
        auth_pack.push(u_in[3 * k + 1]); // at0
    }
    for k in 0..base_triples {
        auth_pack.push(u_in[3 * k + 2]); // at1
    }
    for k in 0..base_triples {
        auth_pack.push(w_out[3 * k + 1]); // ct0
    }
    for k in 0..base_triples {
        auth_pack.push(w_out[3 * k + 2]); // ct1
    }
    auth_pack.extend_from_slice(&r1_vals);

    let all_macs = authenticate_goldilocks_batch_over_wire(
        wire, ot, roster, session_id, alpha_me, &auth_pack, rng,
    )?;

    let wire_at = |slot: usize, k: usize| LocalAuthWire {
        val: auth_pack[slot * base_triples + k],
        mac: all_macs[slot * base_triples + k],
    };
    let ta: SecretBuffer<Vec<LocalAuthWire>> =
        SecretBuffer((0..base_triples).map(|k| wire_at(0, k)).collect());
    let tb: SecretBuffer<Vec<LocalAuthWire>> =
        SecretBuffer((0..base_triples).map(|k| wire_at(1, k)).collect());
    let tc: SecretBuffer<Vec<LocalAuthWire>> =
        SecretBuffer((0..base_triples).map(|k| wire_at(2, k)).collect());

    // `GoldilocksExt2` companion sacrifice (`< 2^{-127}` soundness).
    let sac_coin = joint_coin_over_wire(
        wire,
        roster,
        session_id,
        b"pow7-sacrifice",
        session_id,
        true,
        rng,
    )?;
    let rho = GoldilocksExt2::new(
        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|i| sac_coin[i])),
        Goldilocks::from_u128_reduced(
            u128::from_le_bytes(core::array::from_fn(|i| sac_coin[16 + i])) | 1,
        ),
    );
    let mut u_sac = SecretBuffer(Vec::with_capacity(2 * base_triples));
    for k in 0..base_triples {
        let at0 = wire_at(3, k);
        let at1 = wire_at(4, k);
        u_sac.push(ta[k].scale(rho.c0).sub(at0));
        u_sac.push(ta[k].scale(rho.c1).sub(at1));
    }
    let u_opened = commit_open_and_check_goldilocks_over_wire(
        wire,
        ot,
        roster,
        session_id,
        "personal_release_sac_u",
        ROUND_PREL_COMMIT,
        ROUND_PREL_OPEN,
        &u_sac,
        alpha_me,
        rng,
    )?;
    let mut res_sac = SecretBuffer(Vec::with_capacity(2 * base_triples));
    for k in 0..base_triples {
        let ct0 = wire_at(5, k);
        let ct1 = wire_at(6, k);
        res_sac.push(
            tc[k]
                .scale(rho.c0)
                .sub(ct0)
                .sub(tb[k].scale(u_opened[2 * k])),
        );
        res_sac.push(
            tc[k]
                .scale(rho.c1)
                .sub(ct1)
                .sub(tb[k].scale(u_opened[2 * k + 1])),
        );
    }
    let res_opened = commit_open_and_check_goldilocks_over_wire(
        wire,
        ot,
        roster,
        session_id,
        "personal_release_sac_res",
        ROUND_PREL_COMMIT,
        ROUND_PREL_OPEN,
        &res_sac,
        alpha_me,
        rng,
    )?;
    if res_opened.iter().any(|&v| v != Goldilocks::ZERO) {
        ot.poison_and_wipe();
        return Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
            PreprocessError::SacrificeResidualNonZero {
                phase: "personal_release_pow7",
            },
        )));
    }

    let r1_base = 7 * base_triples;
    let r1: SecretBuffer<Vec<LocalAuthWire>> = SecretBuffer(
        (0..count)
            .map(|k| LocalAuthWire {
                val: auth_pack[r1_base + k],
                mac: all_macs[r1_base + k],
            })
            .collect(),
    );
    drop((auth_pack, all_macs, u_in, v_in, w_out));

    // Round 1: `r^2 = r * r` (`0..count`)
    let r2 = eval_beaver_batch_over_wire(
        wire,
        ot,
        roster,
        session_id,
        "personal_release_pow7_r2",
        &r1,
        &r1,
        &ta[0..count],
        &tb[0..count],
        &tc[0..count],
        alpha_me,
        rng,
    )?;
    // Round 2: `(r^3, r^4) = (r^2 * r, r^2 * r^2)` in 1 parallel batch (`count..3*count`)
    let mut lhs2 = SecretBuffer(Vec::with_capacity(2 * count));
    let mut rhs2 = SecretBuffer(Vec::with_capacity(2 * count));
    lhs2.extend_from_slice(&r2);
    lhs2.extend_from_slice(&r2);
    rhs2.extend_from_slice(&r1);
    rhs2.extend_from_slice(&r2);
    let r34 = eval_beaver_batch_over_wire(
        wire,
        ot,
        roster,
        session_id,
        "personal_release_pow7_r34",
        &lhs2,
        &rhs2,
        &ta[count..3 * count],
        &tb[count..3 * count],
        &tc[count..3 * count],
        alpha_me,
        rng,
    )?;
    let r3 = &r34[0..count];
    let r4 = &r34[count..2 * count];

    // Round 3: `(r^5, r^6, r^7) = (r^4 * r, r^4 * r^2, r^4 * r^3)` in 1 parallel batch (`3*count..6*count`)
    let mut lhs3 = SecretBuffer(Vec::with_capacity(3 * count));
    let mut rhs3 = SecretBuffer(Vec::with_capacity(3 * count));
    lhs3.extend_from_slice(r4);
    lhs3.extend_from_slice(r4);
    lhs3.extend_from_slice(r4);
    rhs3.extend_from_slice(&r1);
    rhs3.extend_from_slice(&r2);
    rhs3.extend_from_slice(r3);
    let r567 = eval_beaver_batch_over_wire(
        wire,
        ot,
        roster,
        session_id,
        "personal_release_pow7_r567",
        &lhs3,
        &rhs3,
        &ta[3 * count..6 * count],
        &tb[3 * count..6 * count],
        &tc[3 * count..6 * count],
        alpha_me,
        rng,
    )?;

    let mut tuples = SecretBuffer(Vec::with_capacity(count));
    for k in 0..count {
        tuples.push(LocalPow7Tuple {
            pows: [
                r1[k],
                r2[k],
                r3[k],
                r4[k],
                r567[k],
                r567[count + k],
                r567[2 * count + k],
            ],
        });
    }
    Ok(tuples)
}

#[expect(
    clippy::too_many_arguments,
    reason = "S-box round evaluation takes transport, roster, wires, pow7 tuples, MAC key and pending buffers"
)]
fn eval_sbox7_round_over_wire<T: WireTransport>(
    wire: &mut T,
    roster: &[u16],
    inputs: &[LocalAuthWire],
    tuples: &[LocalPow7Tuple],
    me: usize,
    alpha_me: GoldilocksExt2,
    pending_wires: &mut Vec<LocalAuthWire>,
    pending_opened: &mut Vec<Goldilocks>,
) -> Result<Vec<LocalAuthWire>, PersonalReleaseError> {
    let count = inputs.len();
    let m = wire.parties();
    let mut masked = SecretBuffer(Vec::with_capacity(count));
    let mut payload = SecretBuffer(Vec::with_capacity(count * 8));
    for (inp, tup) in inputs.iter().zip(tuples) {
        let w = inp.add(tup.pows[0]);
        payload.extend_from_slice(&w.val.to_be_bytes());
        masked.push(w);
    }
    let all_frames = broadcast_collect(wire, roster, ROUND_PREL_SBOX_Y, &payload)?;
    let mut y_opened = vec![Goldilocks::ZERO; count];
    for p in 0..m {
        if all_frames[p].len() != count * 8 {
            return Err(PersonalReleaseError::MalformedWireMessage {
                from: roster[p],
                round: ROUND_PREL_SBOX_Y,
            });
        }
        for (k, dst) in y_opened.iter_mut().enumerate() {
            let v = decode_gl_be(&all_frames[p][8 * k..8 * k + 8]).ok_or(
                PersonalReleaseError::MalformedWireMessage {
                    from: roster[p],
                    round: ROUND_PREL_SBOX_Y,
                },
            )?;
            *dst += v;
        }
    }

    pending_wires.extend_from_slice(&masked);
    pending_opened.extend_from_slice(&y_opened);

    let c7 = Goldilocks::from_u64_reduced(7);
    let c21 = Goldilocks::from_u64_reduced(21);
    let c35 = Goldilocks::from_u64_reduced(35);
    let mut out = Vec::with_capacity(count);
    for (k, &y) in y_opened.iter().enumerate() {
        let y2 = y * y;
        let y3 = y2 * y;
        let y4 = y2 * y2;
        let y5 = y4 * y;
        let y6 = y3 * y3;
        let y7 = y6 * y;
        let p = &tuples[k].pows;
        let mut acc = LocalAuthWire::public_const(y7, me, alpha_me);
        acc = acc.sub(p[0].scale(c7 * y6));
        acc = acc.add(p[1].scale(c21 * y5));
        acc = acc.sub(p[2].scale(c35 * y4));
        acc = acc.add(p[3].scale(c35 * y3));
        acc = acc.sub(p[4].scale(c21 * y2));
        acc = acc.add(p[5].scale(c7 * y));
        acc = acc.sub(p[6]);
        out.push(acc);
    }
    Ok(out)
}

// ============================================================================
// `PersonalReleaseParty`: Local Custody + Isolated Wire-Transport Ceremony
// ============================================================================

/// One custodian: its own latch and its own span-program rows, nothing of any peer.
pub struct PersonalReleaseParty<W: DurableWal> {
    deployment_id: [u8; 32],
    enrolled_key: Option<(HemDigest4, HemDigest4)>,
    latch: PersonalBeltLatch<W>,
    program_digest: [u8; 32],
    program: MonotoneSpanProgram,
    input: Option<PersonalMspInput>,
}

impl<W: DurableWal> PersonalReleaseParty<W> {
    pub fn new(
        deployment_id: [u8; 32],
        latch: PersonalBeltLatch<W>,
        input: PersonalMspInput,
    ) -> Result<Self, PersonalReleaseError> {
        if latch.party() != input.party() {
            return Err(PersonalReleaseError::ContextMismatch);
        }
        Ok(Self {
            deployment_id,
            enrolled_key: None,
            latch,
            program_digest: span_program_digest(input.program()),
            program: input.program().clone(),
            input: Some(input),
        })
    }

    pub fn party(&self) -> u16 {
        self.latch.party()
    }

    pub fn has_input(&self) -> bool {
        self.input.is_some()
    }

    /// Derive this custodian's Encrypt-then-MAC [`MacSealedWireChannel::new_encrypted`] link keys
    /// for `ctx` from its enrolled pairwise latch secrets.
    pub fn derive_wire_keys(
        &self,
        ctx: &PersonalReleaseContext,
    ) -> Result<SecretBuffer<Vec<[u8; 32]>>, PersonalReleaseError> {
        let _ = self.checked_record(ctx)?;
        let sid = ctx.mpc_session_id();
        let me_id = self.party();
        let mut keys = SecretBuffer(Vec::with_capacity(ctx.signers.len()));
        for &peer in &ctx.signers {
            if peer == me_id {
                keys.push([0u8; 32]);
            } else {
                let k = self
                    .latch
                    .derive_wire_link_key(&sid, peer)
                    .ok_or(PersonalReleaseError::ContextMismatch)?;
                keys.push(k);
            }
        }
        Ok(keys)
    }

    /// Check the public context against this party's own enrolled state and return the
    /// record it would bind. Nothing is persisted here.
    fn checked_record(
        &self,
        ctx: &PersonalReleaseContext,
    ) -> Result<BeltLatchRecord, PersonalReleaseError> {
        let own_context = self.latch.key_epoch_context();
        if ctx.deployment_id != self.deployment_id
            || self
                .enrolled_key
                .is_some_and(|key| key != (ctx.pk_seed, ctx.commitment))
            || ctx.key_epoch_context != *own_context
            || ctx.policy_digest != self.latch.system().policy_digest(own_context)
            || ctx.program_digest != self.program_digest
            || !ctx.signers.is_subset(self.latch.system().participants())
            || self
                .program
                .solve_reconstruction_weights(&ctx.signers)
                .is_none()
        {
            return Err(PersonalReleaseError::ContextMismatch);
        }
        if !ctx.signers.contains(&self.party()) {
            return Err(PersonalReleaseError::NotASigner);
        }
        Ok(ctx.record())
    }

    /// Durably bind the ceremony, then acknowledge it to `receiver`.
    pub fn acknowledge(
        &mut self,
        ctx: &PersonalReleaseContext,
        receiver: u16,
    ) -> Result<PersonalLatchAck, PersonalReleaseError> {
        let record = self.checked_record(ctx)?;
        if !ctx.signers.contains(&receiver) {
            return Err(PersonalReleaseError::NotASigner);
        }
        self.latch
            .acknowledge(&record, receiver)
            .map_err(PersonalReleaseError::Policy)
    }

    /// Release this party's lanes for `ctx`. A rejected certificate leaves the input in
    /// place; a successful release consumes it.
    pub fn release(
        &mut self,
        ctx: &PersonalReleaseContext,
        certificate: &PersonalLatchCertificate,
    ) -> Result<ReleasedLanes, PersonalReleaseError> {
        let record = self.checked_record(ctx)?;
        if self.input.is_none() {
            return Err(PersonalReleaseError::AlreadyReleased);
        }
        let permit = self
            .latch
            .authorize(&record, certificate)
            .map_err(PersonalReleaseError::Policy)?;
        if permit.signers() != &ctx.signers {
            return Err(PersonalReleaseError::SignerSetMismatch);
        }
        let input = self
            .input
            .take()
            .ok_or(PersonalReleaseError::AlreadyReleased)?;
        input.release_with_permit(&permit).map_err(|e| match e {
            PersonalMspInputError::Policy(p) => PersonalReleaseError::Policy(p),
            PersonalMspInputError::Access(a) => PersonalReleaseError::Access(a),
        })
    }

    /// Execute the complete end-to-end personal release ceremony over `transport` with **zero
    /// coordinator access to any custodian's lanes**:
    /// 1. Atomically reserves `ctx.mpc_session_id()` in `journal` and wraps `transport` in an
    ///    encrypted, direction-bound [`MacSealedWireChannel`] keyed from [`PersonalBeltLatch`];
    /// 2. Exchanges receiver-bound [`PersonalLatchAck`]s, verifies the B³ quorum certificate, and
    ///    collapses only this custodian's MSP rows locally;
    /// 3. Reshares the 4 `Goldilocks` lanes into uniform additive shares over the encrypted links,
    ///    establishes pairwise PQ Ring-LWE + `SoftSpokenOT (n_C = 256, k = 2)` channels, runs
    ///    dealerless `Π_MAC` + `Π_pow7`,
    ///    evaluates `poseidon2_compress12_ff`, and verifies a two-stage multiplicatively blinded
    ///    `GoldilocksExt2` `MacCheck` **strictly before** opening the PRF-check digest.
    pub fn ceremony_over_wire<T: WireTransport, J: PoisonJournal>(
        &mut self,
        ctx: &PersonalReleaseContext,
        transport: T,
        rng: &mut PartyPrivateRng,
        journal: &mut J,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        self.ceremony_over_wire_inner(ctx, transport, None, rng, journal, false)
    }

    /// Execute [`Self::ceremony_over_wire`] reusing an already-established [`PartyOtEndpoint`]
    /// (including its pooled single-use `GoldilocksExt2` blinding triples) over `wire`.
    pub fn ceremony_over_wire_with_ot<T: WireTransport, J: PoisonJournal>(
        &mut self,
        ctx: &PersonalReleaseContext,
        wire: &mut MacSealedWireChannel<T>,
        ot: &mut PartyOtEndpoint,
        rng: &mut PartyPrivateRng,
        journal: &mut J,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        self.ceremony_with_established_ot(ctx, wire, ot, rng, journal, false)
    }

    fn ceremony_over_wire_inner<T: WireTransport, J: PoisonJournal>(
        &mut self,
        ctx: &PersonalReleaseContext,
        transport: T,
        ot_override: Option<&mut PartyOtEndpoint>,
        rng: &mut PartyPrivateRng,
        journal: &mut J,
        corrupt_after_auth: bool,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        let _ = self.checked_record(ctx)?;
        if !self.has_input() {
            return Err(PersonalReleaseError::AlreadyReleased);
        }
        let roster: Vec<u16> = ctx.signers.iter().copied().collect();
        let m = roster.len();
        let Some(me) = roster.iter().position(|&p| p == self.party()) else {
            return Err(PersonalReleaseError::NotASigner);
        };
        if transport.parties() != m || transport.party() != me {
            return Err(PersonalReleaseError::LaneRosterMismatch);
        }
        if ot_override.as_ref().is_some_and(|ot| ot.poisoned) {
            return Err(PersonalReleaseError::SessionPoisoned);
        }
        let mpc_sid = ctx.mpc_session_id();
        if journal.is_poisoned(&mpc_sid) || journal.reserve_session(&mpc_sid).is_err() {
            return Err(PersonalReleaseError::SessionPoisoned);
        }
        let mut wire_keys = self.derive_wire_keys(ctx)?;
        let raw_keys = core::mem::take(&mut wire_keys.0);
        let mut wire =
            MacSealedWireChannel::new_encrypted(transport, self.deployment_id, mpc_sid, raw_keys)?;

        match ot_override {
            Some(ot) => self.ceremony_with_established_ot_reserved(
                ctx,
                &roster,
                &mpc_sid,
                &mut wire,
                ot,
                rng,
                journal,
                corrupt_after_auth,
            ),
            None => {
                let mut ot =
                    match PartyOtEndpoint::establish_over_wire(mpc_sid, &roster, &mut wire, rng) {
                        Ok(ep) => ep,
                        Err(err) => {
                            let _ = journal.mark_poisoned(&mpc_sid);
                            send_abort_all(&mut wire);
                            return Err(err);
                        }
                    };
                // Pre-stage all 16 `GoldilocksExt2` blinding triples in 1 batched OT pass!
                if let Err(err) = ot.prestage_ext2_blinding(&mut wire, 16, rng) {
                    ot.poison_and_wipe();
                    let _ = journal.mark_poisoned(&mpc_sid);
                    send_abort_all(&mut wire);
                    return Err(err);
                }
                self.ceremony_with_established_ot_reserved(
                    ctx,
                    &roster,
                    &mpc_sid,
                    &mut wire,
                    &mut ot,
                    rng,
                    journal,
                    corrupt_after_auth,
                )
            }
        }
    }

    fn ceremony_with_established_ot<T: WireTransport, J: PoisonJournal>(
        &mut self,
        ctx: &PersonalReleaseContext,
        wire: &mut MacSealedWireChannel<T>,
        ot: &mut PartyOtEndpoint,
        rng: &mut PartyPrivateRng,
        journal: &mut J,
        corrupt_after_auth: bool,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        let _ = self.checked_record(ctx)?;
        if !self.has_input() {
            return Err(PersonalReleaseError::AlreadyReleased);
        }
        let roster: Vec<u16> = ctx.signers.iter().copied().collect();
        let m = roster.len();
        let Some(me) = roster.iter().position(|&p| p == self.party()) else {
            return Err(PersonalReleaseError::NotASigner);
        };
        if !wire.matches_encrypted(&self.deployment_id, &ctx.mpc_session_id())
            || wire.parties() != m
            || wire.party() != me
            || ot.roster != roster
            || ot.parties != m
            || ot.me != me
        {
            return Err(PersonalReleaseError::LaneRosterMismatch);
        }
        if ot.poisoned {
            return Err(PersonalReleaseError::SessionPoisoned);
        }
        let mpc_sid = ctx.mpc_session_id();
        if journal.is_poisoned(&mpc_sid) || journal.reserve_session(&mpc_sid).is_err() {
            return Err(PersonalReleaseError::SessionPoisoned);
        }
        self.ceremony_with_established_ot_reserved(
            ctx,
            &roster,
            &mpc_sid,
            wire,
            ot,
            rng,
            journal,
            corrupt_after_auth,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Internal ceremony execution binds context, roster, session id, wire channel, OT endpoint, RNG, journal and fault flag"
    )]
    fn ceremony_with_established_ot_reserved<T: WireTransport, J: PoisonJournal>(
        &mut self,
        ctx: &PersonalReleaseContext,
        roster: &[u16],
        mpc_sid: &[u8; 32],
        wire: &mut MacSealedWireChannel<T>,
        ot: &mut PartyOtEndpoint,
        rng: &mut PartyPrivateRng,
        journal: &mut J,
        corrupt_after_auth: bool,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        let res = self.run_wire_mpc_core(ctx, roster, mpc_sid, wire, ot, rng, corrupt_after_auth);
        if let Err(ref err) = res {
            ot.poison_and_wipe();
            if !matches!(err, PersonalReleaseError::CommitmentMismatch) {
                let _ = journal.mark_poisoned(mpc_sid);
            }
            send_abort_all(wire);
        }
        res
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Core wire ceremony binds context, roster, session id, wire channel, OT endpoint, RNG and fault flag"
    )]
    fn run_wire_mpc_core<T: WireTransport>(
        &mut self,
        ctx: &PersonalReleaseContext,
        roster: &[u16],
        mpc_sid: &[u8; 32],
        wire: &mut MacSealedWireChannel<T>,
        ot: &mut PartyOtEndpoint,
        rng: &mut PartyPrivateRng,
        corrupt_after_auth: bool,
    ) -> Result<HemDigest4, PersonalReleaseError> {
        let me = wire.party();
        let m = roster.len();

        // 1. Exchange receiver-specific PersonalLatchAcks over the encrypted wire links and
        //    release ONLY this custodian's collapsed MSP lanes locally.
        let mut acks = vec![None; m];
        acks[me] = Some(self.acknowledge(ctx, roster[me])?);
        for (peer, &peer_id) in roster.iter().enumerate() {
            if peer != me {
                let ack = self.acknowledge(ctx, peer_id)?;
                wire.send_frame(peer, ROUND_PREL_ACK, &ack.to_bytes())?;
            }
        }
        for (peer, &peer_id) in roster.iter().enumerate() {
            if peer != me {
                let raw = recv_wire(wire, roster, peer, ROUND_PREL_ACK)?;
                let ack = PersonalLatchAck::from_bytes(&raw).ok_or(
                    PersonalReleaseError::MalformedWireMessage {
                        from: peer_id,
                        round: ROUND_PREL_ACK,
                    },
                )?;
                acks[peer] = Some(ack);
            }
        }
        let cert = PersonalLatchCertificate {
            acks: acks
                .into_iter()
                .collect::<Option<Vec<_>>>()
                .ok_or(PersonalReleaseError::LaneRosterMismatch)?,
        };
        let my_lanes = self.release(ctx, &cert)?;

        // 2. Re-randomize `my_lanes[0..4]` across the encrypted links so `my_lanes` is wiped
        //    immediately and each party holds a fresh uniform additive share `x_me[0..4]`.
        let mut x_me = SecretBuffer([Goldilocks::ZERO; 4]);
        for lane in 0..4 {
            x_me[lane] = my_lanes[lane];
        }
        drop(my_lanes);
        for peer in 0..m {
            if peer != me {
                let mut outbound = SecretBuffer([0u8; 32]);
                for lane in 0..4 {
                    let mask = rng.next_goldilocks();
                    x_me[lane] -= mask;
                    outbound[8 * lane..8 * lane + 8].copy_from_slice(&mask.to_be_bytes());
                }
                wire.send_frame(peer, ROUND_PREL_RESHARE, &*outbound)?;
            }
        }
        for (peer, &peer_id) in roster.iter().enumerate() {
            if peer != me {
                let inbound = recv_wire(wire, roster, peer, ROUND_PREL_RESHARE)?;
                if inbound.len() != 32 {
                    return Err(PersonalReleaseError::MalformedWireMessage {
                        from: peer_id,
                        round: ROUND_PREL_RESHARE,
                    });
                }
                for lane in 0..4 {
                    let share = decode_gl_be(&inbound[8 * lane..8 * lane + 8]).ok_or(
                        PersonalReleaseError::MalformedWireMessage {
                            from: peer_id,
                            round: ROUND_PREL_RESHARE,
                        },
                    )?;
                    x_me[lane] += share;
                }
            }
        }

        // 3. Authenticate the 4 reshared input lanes and generate 118 `Π_pow7` tuples under a
        //    single dealerless `GoldilocksExt2` SPDZ MAC key `\alpha = \sum \alpha_u`.
        let mut framed = [0u8; 40];
        framed[..8].copy_from_slice(b"QPRELWIR");
        framed[8..].copy_from_slice(mpc_sid);
        let spdz_sid = shake256_32(&framed);
        let alpha_me = SecretBuffer(rng.next_ext2());

        let auth_sid = h32(b"personal-release/input-auth", &[&spdz_sid]);
        let x_macs = authenticate_goldilocks_batch_over_wire(
            wire, ot, roster, &auth_sid, *alpha_me, &*x_me, rng,
        )?;
        let mut in0: SecretBuffer<[LocalAuthWire; 4]> =
            SecretBuffer(core::array::from_fn(|i| LocalAuthWire {
                val: x_me[i],
                mac: x_macs[i],
            }));
        drop((x_me, x_macs));
        if corrupt_after_auth {
            in0[0].val += Goldilocks::ONE;
        }

        let opened =
            authenticated_prf_check(wire, ot, roster, spdz_sid, &ctx.pk_seed, alpha_me, in0, rng)?;
        if opened != ctx.commitment {
            return Err(PersonalReleaseError::CommitmentMismatch);
        }
        Ok(opened)
    }
}

#[allow(clippy::too_many_arguments)]
fn authenticated_prf_check<T: WireTransport>(
    wire: &mut MacSealedWireChannel<T>,
    ot: &mut PartyOtEndpoint,
    roster: &[u16],
    spdz_sid: [u8; 32],
    pk_seed: &HemDigest4,
    alpha_me: SecretBuffer<GoldilocksExt2>,
    in0: SecretBuffer<[LocalAuthWire; 4]>,
    rng: &mut PartyPrivateRng,
) -> Result<HemDigest4, PersonalReleaseError> {
    let me = wire.party();
    let pow7_sid = h32(b"personal-release/pow7-vault", &[&spdz_sid]);
    let pow7_tuples = generate_pow7_tuples_over_wire(
        wire,
        ot,
        roster,
        &pow7_sid,
        POSEIDON2_SBOXES_PER_PERM,
        *alpha_me,
        rng,
    )?;

    // 4. Evaluate `poseidon2_compress12_ff(secret, pk_seed, [HEM_DOMAIN_PRF_CHECK, 0, 0, IV])`
    //    on authenticated shares (`30` S-box rounds, `118` S-boxes).
    let tweak = [
        Goldilocks::from_u64_reduced(HEM_DOMAIN_PRF_CHECK),
        Goldilocks::ZERO,
        Goldilocks::ZERO,
        Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
    ];
    let mut st = SecretBuffer([
        in0[0],
        in0[1],
        in0[2],
        in0[3],
        LocalAuthWire::public_const(pk_seed[0], me, *alpha_me),
        LocalAuthWire::public_const(pk_seed[1], me, *alpha_me),
        LocalAuthWire::public_const(pk_seed[2], me, *alpha_me),
        LocalAuthWire::public_const(pk_seed[3], me, *alpha_me),
        LocalAuthWire::public_const(tweak[0], me, *alpha_me),
        LocalAuthWire::public_const(tweak[1], me, *alpha_me),
        LocalAuthWire::public_const(tweak[2], me, *alpha_me),
        LocalAuthWire::public_const(tweak[3], me, *alpha_me),
    ]);
    apply_me_local(&mut st);

    let mut tup_cursor = 0usize;
    let mut pending_wires = SecretBuffer(Vec::with_capacity(POSEIDON2_SBOXES_PER_PERM));
    let mut pending_opened = Vec::with_capacity(POSEIDON2_SBOXES_PER_PERM);

    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = SecretBuffer(Vec::with_capacity(12));
        for (lane, w) in st.iter().enumerate() {
            let rc =
                LocalAuthWire::public_const(poseidon2_const_at(0, r, lane as u64), me, *alpha_me);
            sbox_in.push(w.add(rc));
        }
        let sbox_out = eval_sbox7_round_over_wire(
            wire,
            roster,
            &sbox_in,
            &pow7_tuples[tup_cursor..tup_cursor + 12],
            me,
            *alpha_me,
            &mut pending_wires,
            &mut pending_opened,
        )?;
        tup_cursor += 12;
        st.copy_from_slice(&sbox_out);
        apply_me_local(&mut st);
    }

    for r in 0..POSEIDON2_INTERNAL_ROUNDS {
        let rc0 = LocalAuthWire::public_const(poseidon2_const_at(1, r, 0), me, *alpha_me);
        let sbox_in = SecretBuffer([st[0].add(rc0)]);
        let sbox_out = eval_sbox7_round_over_wire(
            wire,
            roster,
            &*sbox_in,
            &pow7_tuples[tup_cursor..tup_cursor + 1],
            me,
            *alpha_me,
            &mut pending_wires,
            &mut pending_opened,
        )?;
        tup_cursor += 1;
        st[0] = sbox_out[0];
        apply_mi_local(&mut st);
    }

    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = SecretBuffer(Vec::with_capacity(12));
        for (lane, w) in st.iter().enumerate() {
            let rc =
                LocalAuthWire::public_const(poseidon2_const_at(2, r, lane as u64), me, *alpha_me);
            sbox_in.push(w.add(rc));
        }
        let sbox_out = eval_sbox7_round_over_wire(
            wire,
            roster,
            &sbox_in,
            &pow7_tuples[tup_cursor..tup_cursor + 12],
            me,
            *alpha_me,
            &mut pending_wires,
            &mut pending_opened,
        )?;
        tup_cursor += 12;
        st.copy_from_slice(&sbox_out);
        apply_me_local(&mut st);
    }
    debug_assert_eq!(tup_cursor, POSEIDON2_SBOXES_PER_PERM);

    let c4 = Goldilocks::from_u64_reduced(4);
    let cut_wires = SecretBuffer([
        st[0].add(in0[0]).add(LocalAuthWire::public_const(
            pk_seed[0] * Goldilocks::TWO + tweak[0] * c4,
            me,
            *alpha_me,
        )),
        st[1].add(in0[1]).add(LocalAuthWire::public_const(
            pk_seed[1] * Goldilocks::TWO + tweak[1] * c4,
            me,
            *alpha_me,
        )),
        st[2].add(in0[2]).add(LocalAuthWire::public_const(
            pk_seed[2] * Goldilocks::TWO + tweak[2] * c4,
            me,
            *alpha_me,
        )),
        st[3].add(in0[3]).add(LocalAuthWire::public_const(
            pk_seed[3] * Goldilocks::TWO + tweak[3] * c4,
            me,
            *alpha_me,
        )),
    ]);
    drop((st, in0, pow7_tuples));

    // 5. Stage A Pre-Cut Blinded `MacCheck`: verify ALL 118 intermediate S-box openings
    //    STRICTLY BEFORE any cut-boundary commitment or share leaves this custodian!
    let mut pend_bytes = Vec::with_capacity(pending_opened.len() * 8);
    for &y in &pending_opened {
        pend_bytes.extend_from_slice(&y.to_be_bytes());
    }
    let stage_a_dig = h32(b"personal-release/stage-a-dig", &[&spdz_sid, &pend_bytes]);
    let stage_a_coin = joint_coin_over_wire(
        wire,
        roster,
        &spdz_sid,
        b"stage-a-mac",
        &stage_a_dig,
        true,
        rng,
    )?;
    let mut a_xof = Cshake256Xof::new_shake256();
    a_xof.absorb(b"personal-release/stage-a-chis");
    a_xof.absorb(&stage_a_coin);
    let mut x_fold = GoldilocksExt2::ZERO;
    let mut m_fold = SecretBuffer(GoldilocksExt2::ZERO);
    for (w, &y) in pending_wires.iter().zip(&pending_opened) {
        let mut b48 = [0u8; 48];
        a_xof.squeeze(&mut b48);
        let chi = decode_pad48_ext2(&b48);
        x_fold += chi.mul_base(y);
        *m_fold += chi * w.mac;
    }
    let stage_a_res = SecretBuffer(*m_fold - *alpha_me * x_fold);
    ot.blind_check_zero_ext2(
        wire,
        &spdz_sid,
        "personal_release_stage_a_mac",
        *stage_a_res,
        rng,
    )?;

    // 6. Stage B Cut-Boundary Commit-Open + Blinded `MacCheck`: open ONLY the 4-limb digest!
    let opened_vec = commit_open_and_check_goldilocks_over_wire(
        wire,
        ot,
        roster,
        &spdz_sid,
        "personal_release_cut_digest",
        ROUND_PREL_CUT_COM,
        ROUND_PREL_CUT_OPEN,
        &*cut_wires,
        *alpha_me,
        rng,
    )?;
    let opened: HemDigest4 = [opened_vec[0], opened_vec[1], opened_vec[2], opened_vec[3]];
    Ok(opened)
}

/// Returned `(digest, Vec<(party, journal)>)` from [`run_isolated_personal_release_ceremony`].
pub type IsolatedReleaseOutcome<W, J> = (HemDigest4, Vec<(PersonalReleaseParty<W>, J)>);

/// Spawn one OS thread per certified custodian over [`crate::wire_channel::InMemoryWireMesh`] and
/// run [`PersonalReleaseParty::ceremony_over_wire`]: the caller supplies each custodian's isolated
/// `(party, rng, journal)` bundle and receives back only the public [`HemDigest4`] and the
/// post-ceremony `(party, journal)` handles (`0` coordinator access to any released lane).
#[cfg(any(test, feature = "std"))]
pub fn run_isolated_personal_release_ceremony<W, J>(
    ctx: &PersonalReleaseContext,
    parties: Vec<(PersonalReleaseParty<W>, PartyPrivateRng, J)>,
) -> Result<IsolatedReleaseOutcome<W, J>, PersonalReleaseError>
where
    W: DurableWal + Send,
    J: PoisonJournal + Send,
{
    let m = ctx.signers.len();
    if parties.len() != m
        || !parties
            .iter()
            .map(|(p, _, _)| p.party())
            .eq(ctx.signers.iter().copied())
    {
        return Err(PersonalReleaseError::LaneRosterMismatch);
    }
    let (endpoints, _) = crate::wire_channel::InMemoryWireMesh::connect(m, ctx.mpc_session_id());
    let outcomes = std::thread::scope(|scope| {
        let handles: Vec<_> = parties
            .into_iter()
            .zip(endpoints)
            .map(|((mut party, mut rng, mut journal), endpoint)| {
                scope.spawn(move || {
                    let res = party.ceremony_over_wire(ctx, endpoint, &mut rng, &mut journal);
                    (res, party, journal)
                })
            })
            .collect();
        let joined = handles.into_iter().map(|h| h.join()).collect::<Vec<_>>();
        joined
            .into_iter()
            .map(|r| r.map_err(|_| PersonalReleaseError::SessionPoisoned))
            .collect::<Result<Vec<_>, _>>()
    })?;
    let mut returned = Vec::with_capacity(m);
    let mut first_digest = None;
    for (res, party, journal) in outcomes {
        let d = res?;
        if let Some(prev) = first_digest
            && prev != d
        {
            return Err(PersonalReleaseError::CommitmentMismatch);
        }
        first_digest = Some(d);
        returned.push((party, journal));
    }
    Ok((
        first_digest.ok_or(PersonalReleaseError::LaneRosterMismatch)?,
        returned,
    ))
}

/// Legacy in-process test driver for `PersonalRelease` (prefer
/// [`PersonalReleaseParty::ceremony_over_wire`] or [`run_isolated_personal_release_ceremony`] so
/// no caller ever holds all signers' released lanes in one process).
#[doc(hidden)]
pub fn run_personal_release_mpc(
    ctx: &PersonalReleaseContext,
    lanes: &[(u16, ReleasedLanes)],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<HemDigest4, PersonalReleaseError> {
    if lanes.len() != ctx.signers.len()
        || lanes.len() < 2
        || !lanes.iter().map(|(p, _)| p).eq(ctx.signers.iter())
    {
        return Err(PersonalReleaseError::LaneRosterMismatch);
    }
    let points: Vec<Goldilocks> = lanes
        .iter()
        .map(|(p, _)| Goldilocks::from_u64_reduced(u64::from(*p) + 1))
        .collect();
    let shares: Vec<ReleasedLanes> = lanes.iter().map(|(_, l)| SecretBuffer(**l)).collect();
    let opened = release_additive_hem_prf_check_mpc(
        ctx.mpc_session_id(),
        lanes.len(),
        &points,
        ctx.pk_seed,
        &shares,
        ot_mesh,
        party_rngs,
    )
    .map_err(PersonalReleaseError::Mpc)?;
    if opened != ctx.commitment {
        return Err(PersonalReleaseError::CommitmentMismatch);
    }
    Ok(opened)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::access::{QuorumTopology, reshare_rank_guard};
    use crate::party_node::MemoryPoisonJournal;
    use crate::wire_channel::InMemoryWireMesh;
    use alloc::{collections::BTreeMap, sync::Arc, vec, vec::Vec};
    use qsag_core::{
        belt_latch::{BeltLatch, MemoryWal},
        poseidon2_mpc::hem_prf_check_digest_clear,
    };
    use std::sync::Mutex;

    type F = Goldilocks;
    const KEY_EPOCH: [u8; 32] = [9; 32];

    fn f4(base: u64) -> [F; 4] {
        core::array::from_fn(|i| F::from_u64_reduced(base + 17 * i as u64))
    }

    /// Four parties; every observer tolerates any single fault, so quorums are the
    /// three-party sets.
    fn system() -> AsymmetricQuorumSystem {
        let roster = PartySet::from([0, 1, 2, 3]);
        let faults: Vec<_> = roster.iter().map(|&p| PartySet::from([p])).collect();
        AsymmetricQuorumSystem::from_fail_prone(
            roster.clone(),
            roster.iter().map(|&p| (p, faults.clone())).collect(),
        )
        .unwrap()
    }

    struct Fixture {
        system: AsymmetricQuorumSystem,
        program: MonotoneSpanProgram,
        parties: Vec<PersonalReleaseParty<MemoryWal>>,
        pk_seed: HemDigest4,
        /// Reference digest of the dealt secret; the secret itself is dropped by the dealer.
        commitment: HemDigest4,
    }

    fn latch(
        system: &AsymmetricQuorumSystem,
        p: u8,
        context: [u8; 32],
    ) -> PersonalBeltLatch<MemoryWal> {
        let keys: BTreeMap<u16, SecretBuffer<[u8; 32]>> = (0u8..4)
            .map(|q| {
                (
                    u16::from(q),
                    SecretBuffer([10 + p.min(q) * 4 + p.max(q); 32]),
                )
            })
            .collect();
        PersonalBeltLatch::new(
            u16::from(p),
            system.clone(),
            BeltLatch::recover(MemoryWal::new(), 4).unwrap(),
            context,
            keys,
        )
        .unwrap()
    }

    /// The share-generation step: a dealer that knows the secret. It hands each party
    /// only its own rows and publishes the PRF-check commitment.
    fn deal(secret_base: u64) -> Fixture {
        let system = system();
        let program = QuorumTopology::PersonalSlices(system.clone())
            .to_span_program(0)
            .unwrap();
        let secret = f4(secret_base);
        let masks: Vec<[F; 4]> = (0..program.num_cols() - 1)
            .map(|i| f4(1000 + 31 * i as u64))
            .collect();
        // Distinct unit mask directions: the public rank guard accepts the schedule.
        let basis: Vec<Vec<F>> = (0..masks.len())
            .map(|i| {
                (0..masks.len())
                    .map(|j| if i == j { F::ONE } else { F::ZERO })
                    .collect()
            })
            .collect();
        assert!(reshare_rank_guard(masks.len(), &basis));
        let rows = program.share(&secret, &masks).unwrap();
        let pk_seed = f4(555);
        let parties = (0u8..4)
            .map(|p| {
                let local: Vec<[F; 4]> = program
                    .row_owners()
                    .iter()
                    .zip(rows.iter())
                    .filter_map(|(&owner, &row)| (owner == u16::from(p)).then_some(row))
                    .collect();
                let input =
                    PersonalMspInput::new(u16::from(p), program.clone(), SecretBuffer(local))
                        .unwrap();
                PersonalReleaseParty::new([0xDA; 32], latch(&system, p, KEY_EPOCH), input).unwrap()
            })
            .collect();
        Fixture {
            commitment: hem_prf_check_digest_clear(secret, pk_seed),
            system,
            program,
            parties,
            pk_seed,
        }
    }

    #[test]
    fn dealerless_msp_rows_release_the_enrolled_key_and_refuse_tampering() {
        let system = system();
        let program = QuorumTopology::PersonalSlices(system.clone())
            .to_span_program(0)
            .unwrap();
        for corrupt in [true, false] {
            let (endpoints, _) = InMemoryWireMesh::connect(4, [3; 32]);
            let results = std::thread::scope(|scope| {
                let handles: Vec<_> = endpoints
                    .into_iter()
                    .enumerate()
                    .map(|(i, mut ep)| {
                        let latch = latch(&system, i as u8, KEY_EPOCH);
                        let program = program.clone();
                        ep.set_timeout(std::time::Duration::from_secs(120));
                        scope.spawn(move || {
                            dkg::CORRUPT_ROW.with(|flag| flag.set(corrupt && i == 0));
                            let mut rng =
                                PartyPrivateRng::from_seed([23 + i as u8; 32], b"dkg-test");
                            run_dealerless_personal_release_dkg_over_wire(
                                [0xDA; 32],
                                [5; 32],
                                latch,
                                program,
                                f4(555),
                                ep,
                                &mut rng,
                                &mut MemoryPoisonJournal::new(),
                            )
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });
            if corrupt {
                assert!(results.iter().all(Result::is_err));
                assert!(
                    results
                        .iter()
                        .any(|r| matches!(r, Err(PersonalReleaseError::CommitmentMismatch)))
                );
                continue;
            }
            let outputs = results.into_iter().collect::<Result<Vec<_>, _>>().unwrap();
            let commitment = outputs[0].commitment;
            assert!(outputs.iter().all(|o| o.commitment == commitment));
            let mut fx = Fixture {
                system: system.clone(),
                program: program.clone(),
                pk_seed: f4(555),
                commitment,
                parties: outputs.into_iter().map(|o| o.party).collect(),
            };
            let ctx = context(&fx, 0x45, 0, &[0, 2, 3]);
            let mut foreign = ctx.clone();
            foreign.deployment_id[0] ^= 1;
            assert_eq!(
                fx.parties[0].acknowledge(&foreign, 2),
                Err(PersonalReleaseError::ContextMismatch)
            );
            // Only this test oracle sums a certified authorized subset for comparison.
            let shares = release_all(&mut fx, &ctx);
            let root = SecretBuffer(core::array::from_fn(|k| {
                shares.iter().fold(F::ZERO, |v, (_, s)| v + s[k])
            }));
            assert_eq!(hem_prf_check_digest_clear(*root, fx.pk_seed), commitment);
        }
    }

    fn context(fx: &Fixture, ceremony: u8, epoch: u64, signers: &[u16]) -> PersonalReleaseContext {
        PersonalReleaseContext::new(
            [0xDA; 32],
            &fx.system,
            &fx.program,
            KEY_EPOCH,
            [ceremony; 32],
            epoch,
            signers.iter().copied().collect(),
            fx.pk_seed,
            fx.commitment,
        )
        .unwrap()
    }

    /// Every signer acknowledges to `receiver`; the result is `receiver`'s certificate.
    fn certificate(
        fx: &mut Fixture,
        ctx: &PersonalReleaseContext,
        receiver: u16,
    ) -> PersonalLatchCertificate {
        let acks = ctx
            .signers()
            .clone()
            .iter()
            .map(|&s| {
                fx.parties[usize::from(s)]
                    .acknowledge(ctx, receiver)
                    .unwrap()
            })
            .collect();
        PersonalLatchCertificate { acks }
    }

    fn release_all(fx: &mut Fixture, ctx: &PersonalReleaseContext) -> Vec<(u16, ReleasedLanes)> {
        ctx.signers()
            .clone()
            .iter()
            .map(|&p| {
                let cert = certificate(fx, ctx, p);
                (p, fx.parties[usize::from(p)].release(ctx, &cert).unwrap())
            })
            .collect()
    }

    fn mesh(parties: usize, tag: u8) -> (OtMesh, Vec<PartyPrivateRng>) {
        let mut rngs: Vec<PartyPrivateRng> = (0..parties)
            .map(|i| PartyPrivateRng::from_seed([tag + i as u8; 32], b"personal release test"))
            .collect();
        (OtMesh::establish([tag; 32], &mut rngs).unwrap(), rngs)
    }

    type WireTapEntry = (usize, usize, u32, Vec<u8>);

    /// Passive wire-tap wrapper recording every raw outer payload sent across the transport.
    struct WireTapTransport<T: WireTransport> {
        inner: T,
        log: Arc<Mutex<Vec<WireTapEntry>>>,
    }

    impl<T: WireTransport> WireTransport for WireTapTransport<T> {
        fn party(&self) -> usize {
            self.inner.party()
        }
        fn parties(&self) -> usize {
            self.inner.parties()
        }
        fn send_frame(
            &mut self,
            to_party: usize,
            round_tag: u32,
            payload: &[u8],
        ) -> Result<(), TransportError> {
            self.log
                .lock()
                .unwrap()
                .push((self.party(), to_party, round_tag, payload.to_vec()));
            self.inner.send_frame(to_party, round_tag, payload)
        }
        fn recv_frame(
            &mut self,
            from_party: usize,
            expected_round_tag: u32,
        ) -> Result<Vec<u8>, TransportError> {
            self.inner.recv_frame(from_party, expected_round_tag)
        }
        fn recv_authenticated_envelope(
            &mut self,
            from_party: usize,
            expected_round_tag: u32,
        ) -> Result<Vec<u8>, TransportError> {
            self.inner
                .recv_authenticated_envelope(from_party, expected_round_tag)
        }
    }

    #[test]
    fn wire_ceremony_releases_authenticated_digest_with_zero_coordinator_lane_access() {
        let mut fx_ref = deal(73);
        let ctx = context(&fx_ref, 0x11, 0, &[0, 1, 3]);
        let expected_lanes: Vec<[F; 4]> = release_all(&mut fx_ref, &ctx)
            .into_iter()
            .map(|(_, l)| *l)
            .collect();
        let secret = f4(73);

        let fx = deal(73);
        let mut all_parties: Vec<Option<PersonalReleaseParty<MemoryWal>>> =
            fx.parties.into_iter().map(Some).collect();
        let signers = [0usize, 1, 3];
        let (endpoints, stats) = InMemoryWireMesh::connect(3, ctx.mpc_session_id());
        let tap_log = Arc::new(Mutex::new(Vec::new()));

        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = signers
                .iter()
                .enumerate()
                .zip(endpoints)
                .map(|((idx, &pid), endpoint)| {
                    let mut party = all_parties[pid].take().unwrap();
                    let tap = WireTapTransport {
                        inner: endpoint,
                        log: Arc::clone(&tap_log),
                    };
                    let ctx_ref = &ctx;
                    scope.spawn(move || {
                        let mut rng = PartyPrivateRng::from_seed(
                            [0x50 + idx as u8; 32],
                            b"personal-release-wire-honest",
                        );
                        let mut journal = MemoryPoisonJournal::new();
                        let res = party.ceremony_over_wire(ctx_ref, tap, &mut rng, &mut journal);
                        (res, party, journal)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });

        // Unselected party 2 never participated and keeps its input intact.
        assert!(all_parties[2].as_ref().unwrap().has_input());
        assert!(stats.total_frames() > 0);

        for (res, party, journal) in &outcomes {
            assert_eq!(res.as_ref(), Ok(&fx.commitment));
            assert!(!party.has_input());
            assert!(!journal.is_poisoned(&ctx.mpc_session_id()));
        }

        // Verify wire confidentiality & view isolation: every outer payload on the mesh is a
        // `MacSealedWireChannel::new_encrypted` envelope (`mode == 1`) and never contains any
        // custodian's collapsed lane bytes or the reconstructed secret bytes!
        let mut forbidden_slices: Vec<[u8; 32]> = Vec::new();
        for lane4 in expected_lanes.iter().chain(core::iter::once(&secret)) {
            let mut be = [0u8; 32];
            let mut le = [0u8; 32];
            for i in 0..4 {
                be[8 * i..8 * i + 8].copy_from_slice(&lane4[i].to_be_bytes());
                le[8 * i..8 * i + 8].copy_from_slice(&lane4[i].to_le_bytes());
            }
            forbidden_slices.push(be);
            forbidden_slices.push(le);
        }
        let logged = tap_log.lock().unwrap();
        assert!(!logged.is_empty());
        for (_, _, _, raw_outer) in logged.iter() {
            // Inner `FrameHeader` (56 bytes) + `encrypted` mode byte == `1` + ciphertext + 32B MAC
            assert!(raw_outer.len() >= crate::wire_channel::FRAME_HEADER_BYTES + 33);
            assert_eq!(raw_outer[crate::wire_channel::FRAME_HEADER_BYTES], 1u8);
            for needle in &forbidden_slices {
                assert!(
                    !raw_outer.windows(32).any(|w| w == needle),
                    "raw wire payload leaked secret or collapsed lane bytes"
                );
            }
        }
    }

    #[test]
    fn wire_ceremony_aborts_before_cut_opening_and_poisons_journal_on_post_auth_tamper() {
        let fx = deal(91);
        let ctx = context(&fx, 0x22, 0, &[0, 1, 2]);
        let mut all_parties: Vec<Option<PersonalReleaseParty<MemoryWal>>> =
            fx.parties.into_iter().map(Some).collect();
        let (endpoints, stats) = InMemoryWireMesh::connect(3, ctx.mpc_session_id());

        let outcomes = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..3usize)
                .zip(endpoints)
                .map(|(idx, endpoint)| {
                    let mut party = all_parties[idx].take().unwrap();
                    let ctx_ref = &ctx;
                    scope.spawn(move || {
                        let mut rng = PartyPrivateRng::from_seed(
                            [0x70 + idx as u8; 32],
                            b"personal-release-wire-tamper",
                        );
                        let mut journal = MemoryPoisonJournal::new();
                        // Party 2 mutates its authenticated wire share after `Π_MAC`!
                        let res = party.ceremony_over_wire_inner(
                            ctx_ref,
                            endpoint,
                            None,
                            &mut rng,
                            &mut journal,
                            idx == 2,
                        );
                        (res, journal)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });

        for (idx, (res, journal)) in outcomes.iter().enumerate() {
            assert!(
                matches!(
                    res,
                    Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                        PreprocessError::MacCheckFailed { .. }
                    ))) | Err(PersonalReleaseError::PeerAborted { .. })
                ),
                "party {idx} unexpected result: {res:?}"
            );
            assert!(
                journal.is_poisoned(&ctx.mpc_session_id()),
                "party {idx} journal must be poisoned after active tamper"
            );
        }
        // Stage A `MacCheck` aborted BEFORE any cut-boundary digest commitment or opening frame!
        for p in 0..3 {
            assert_eq!(
                stats.frames_sent_by(p, |tag| {
                    tag == ROUND_PREL_CUT_COM || tag == ROUND_PREL_CUT_OPEN
                }),
                0,
                "party {p} must never send a cut-boundary digest share after Stage A MAC failure"
            );
        }
    }

    #[test]
    fn failed_wire_blinding_refill_wipes_retained_triples_and_refuses_retry() {
        for additional in [1, usize::MAX] {
            let (mut endpoints, _) = InMemoryWireMesh::connect(2, [47; 32]);
            let mut wire = endpoints.pop().unwrap(); // Party 1, receiver on the first OT.
            let mut ot = PartyOtEndpoint {
                me: 1,
                parties: 2,
                roster: vec![0, 1],
                session_id: [47; 32],
                senders: vec![None, None],
                receivers: vec![None, None],
                transcript: [9; 32],
                ext2_blind_pool: vec![WireExt2BlindTriple {
                    r: GoldilocksExt2::ONE,
                    a: GoldilocksExt2::ONE,
                    c: GoldilocksExt2::ONE,
                }],
                ext2_blind_cursor: 0,
                ext2_blind_serial: 0,
                poisoned: false,
                tamper_next_ext2_c: None,
            };
            let mut rng = PartyPrivateRng::from_seed([48; 32], b"failed-refill");
            let error = ot
                .prestage_ext2_blinding(&mut wire, additional, &mut rng)
                .unwrap_err();
            if additional == usize::MAX {
                assert!(matches!(
                    error,
                    PersonalReleaseError::Transport(TransportError::PayloadTooLarge)
                ));
            } else {
                assert!(matches!(
                    error,
                    PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                        PreprocessError::ChannelPoisoned { .. }
                    ))
                ));
            }
            assert!(ot.poisoned);
            assert!(ot.ext2_blind_pool.is_empty());
            assert_eq!(ot.transcript, [0; 32]);
            assert!(ot.prestage_ext2_blinding(&mut wire, 0, &mut rng).is_err());
        }
    }

    #[test]
    fn tooth_wire_blinding_sacrifice_rejects_corrupted_triple_and_poisons_endpoint() {
        let roster = [0u16, 1, 2];
        let sid = [0x61; 32];
        for bad_item in [0usize, 3usize] {
            let (endpoints, _) = InMemoryWireMesh::connect(3, sid);
            let outcomes = std::thread::scope(|scope| {
                let handles: Vec<_> = endpoints
                    .into_iter()
                    .enumerate()
                    .map(|(idx, mut wire)| {
                        wire.set_timeout(std::time::Duration::from_secs(60));
                        scope.spawn(move || {
                            let mut rng = PartyPrivateRng::from_seed(
                                [0xa0 + idx as u8; 32],
                                b"wire-blind-sac-tamper",
                            );
                            let mut ot = PartyOtEndpoint::establish_over_wire(
                                sid, &roster, &mut wire, &mut rng,
                            )
                            .unwrap();
                            if idx == 1 {
                                ot.tamper_next_ext2_c = Some((bad_item, GoldilocksExt2::ONE));
                            }
                            let res = ot.prestage_ext2_blinding(&mut wire, 2, &mut rng);
                            (res, ot.poisoned, ot.staged_ext2_blinding())
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .map(|h| h.join().unwrap())
                    .collect::<Vec<_>>()
            });
            for (res, poisoned, staged) in outcomes {
                assert_eq!(
                    res,
                    Err(PersonalReleaseError::Mpc(Poseidon2MpcError::Preprocess(
                        PreprocessError::SacrificeResidualNonZero {
                            phase: "personal_release_ext2_blind",
                        }
                    )))
                );
                assert!(poisoned);
                assert_eq!(staged, 0);
            }
        }
    }

    #[test]
    fn wire_ceremony_reuses_retained_ot_blinding_pool_and_detects_substituted_input() {
        // 1. Retained `PartyOtEndpoint` consumes pre-staged `GoldilocksExt2` blinding triples!
        let fx = deal(105);
        let ctx = context(&fx, 0x33, 0, &[0, 2, 3]);
        let roster = [0u16, 2, 3];
        let mut all_parties: Vec<Option<PersonalReleaseParty<MemoryWal>>> =
            fx.parties.into_iter().map(Some).collect();
        let (endpoints, _) = InMemoryWireMesh::connect(3, ctx.mpc_session_id());

        std::thread::scope(|scope| {
            let handles: Vec<_> = roster
                .iter()
                .enumerate()
                .zip(endpoints)
                .map(|((idx, &pid), endpoint)| {
                    let mut party = all_parties[usize::from(pid)].take().unwrap();
                    let ctx_ref = &ctx;
                    scope.spawn(move || {
                        let mut rng = PartyPrivateRng::from_seed(
                            [0x90 + idx as u8; 32],
                            b"personal-release-retained-ot",
                        );
                        let mut journal = MemoryPoisonJournal::new();
                        let mut wire_keys = party.derive_wire_keys(ctx_ref).unwrap();
                        let raw_keys = core::mem::take(&mut wire_keys.0);
                        let mut wire = MacSealedWireChannel::new_encrypted(
                            endpoint,
                            ctx_ref.deployment_id,
                            ctx_ref.mpc_session_id(),
                            raw_keys,
                        )
                        .unwrap();
                        let mut ot = PartyOtEndpoint::establish_over_wire(
                            ctx_ref.mpc_session_id(),
                            &roster,
                            &mut wire,
                            &mut rng,
                        )
                        .unwrap();
                        ot.prestage_ext2_blinding(&mut wire, 20, &mut rng).unwrap();
                        let before = ot.staged_ext2_blinding();
                        assert_eq!(before, 20);
                        let d = party
                            .ceremony_over_wire_with_ot(
                                ctx_ref,
                                &mut wire,
                                &mut ot,
                                &mut rng,
                                &mut journal,
                            )
                            .unwrap();
                        assert_eq!(d, fx.commitment);
                        let after = ot.staged_ext2_blinding();
                        assert!(after < before && after > 0);
                        // Replaying the same session on the same journal fails closed!
                        assert_eq!(
                            party.ceremony_over_wire_with_ot(
                                ctx_ref,
                                &mut wire,
                                &mut ot,
                                &mut rng,
                                &mut journal,
                            ),
                            Err(PersonalReleaseError::AlreadyReleased)
                        );
                    })
                })
                .collect();
            for h in handles {
                h.join().unwrap();
            }
        });

        // 2. Substituted MSP row before authentication is caught by `ctx.commitment` over the wire!
        let mut fx_bad = deal(105);
        let ctx_bad = context(&fx_bad, 0x34, 0, &[0, 1, 2]);
        let bad_rows_len = fx_bad
            .program
            .row_owners()
            .iter()
            .filter(|&&p| p == 2)
            .count();
        let bad_input = PersonalMspInput::new(
            2,
            fx_bad.program.clone(),
            SecretBuffer(vec![[F::from_u64_reduced(999); 4]; bad_rows_len]),
        )
        .unwrap();
        fx_bad.parties[2] =
            PersonalReleaseParty::new([0xDA; 32], latch(&fx_bad.system, 2, KEY_EPOCH), bad_input)
                .unwrap();
        let bundle: Vec<_> = fx_bad
            .parties
            .into_iter()
            .take(3)
            .enumerate()
            .map(|(i, p)| {
                (
                    p,
                    PartyPrivateRng::from_seed([0xB0 + i as u8; 32], b"sub-test"),
                    MemoryPoisonJournal::new(),
                )
            })
            .collect();
        let err = match run_isolated_personal_release_ceremony(&ctx_bad, bundle) {
            Ok(_) => panic!("substituted input must fail commitment check"),
            Err(e) => e,
        };
        assert_eq!(err, PersonalReleaseError::CommitmentMismatch);
    }

    #[test]
    fn certified_quorum_releases_lanes_into_authenticated_digest_and_tamper_aborts() {
        let mut fx = deal(73);
        let ctx = context(&fx, 1, 0, &[0, 1, 3]);
        let lanes = release_all(&mut fx, &ctx);
        assert!(!fx.parties[0].has_input() && fx.parties[2].has_input());
        let (mut ot, mut rngs) = mesh(3, 0x20);

        // The roster handed to the evaluation must be the certified one, in order.
        assert_eq!(
            run_personal_release_mpc(&ctx, &lanes[..2], &mut ot, &mut rngs[..2]),
            Err(PersonalReleaseError::LaneRosterMismatch)
        );
        let mut swapped: Vec<(u16, ReleasedLanes)> =
            lanes.iter().map(|(p, l)| (*p, SecretBuffer(**l))).collect();
        swapped.swap(0, 1);
        assert_eq!(
            run_personal_release_mpc(&ctx, &swapped, &mut ot, &mut rngs),
            Err(PersonalReleaseError::LaneRosterMismatch)
        );

        // Authorized: the opened digest equals the dealer's clear-text reference.
        assert_eq!(
            run_personal_release_mpc(&ctx, &lanes, &mut ot, &mut rngs),
            Ok(fx.commitment)
        );

        // A party that feeds a different lane is caught by the enrolled commitment.
        let mut fx = deal(73);
        let ctx = context(&fx, 2, 0, &[0, 1, 2]);
        let mut lanes = release_all(&mut fx, &ctx);
        lanes[2].1[3] += F::ONE;
        let (mut ot, mut rngs) = mesh(3, 0x40);
        assert_eq!(
            run_personal_release_mpc(&ctx, &lanes, &mut ot, &mut rngs),
            Err(PersonalReleaseError::CommitmentMismatch)
        );
    }

    #[test]
    fn unauthorized_sets_and_foreign_contexts_release_nothing() {
        let mut fx = deal(73);
        // No context exists for a set the program does not authorize.
        for bad in [vec![0u16, 1], vec![2], vec![], vec![0, 1, 9]] {
            assert_eq!(
                PersonalReleaseContext::new(
                    [0xDA; 32],
                    &fx.system,
                    &fx.program,
                    KEY_EPOCH,
                    [1; 32],
                    0,
                    bad.into_iter().collect(),
                    fx.pk_seed,
                    fx.commitment,
                ),
                Err(PersonalReleaseError::ContextMismatch)
            );
        }
        let ctx = context(&fx, 1, 0, &[0, 1, 2]);
        // A non-signer neither acknowledges nor is acknowledged to.
        assert_eq!(
            fx.parties[3].acknowledge(&ctx, 0),
            Err(PersonalReleaseError::NotASigner)
        );
        assert_eq!(
            fx.parties[0].acknowledge(&ctx, 3),
            Err(PersonalReleaseError::NotASigner)
        );
        // Two acknowledgements are not a quorum; the input stays in place.
        let mut cert = certificate(&mut fx, &ctx, 0);
        let full = cert.clone();
        cert.acks.pop();
        assert_eq!(
            fx.parties[0].release(&ctx, &cert).err(),
            Some(PersonalReleaseError::Policy(
                QuorumPolicyError::InvalidCertificate
            ))
        );
        assert!(fx.parties[0].has_input());

        // The same honest acknowledgements under any other context are rejected:
        // ceremony, signer set, commitment, public seed and program each change the binding.
        let other_program = MonotoneSpanProgram::from_authorized_sets(&[
            PartySet::from([0, 1, 2]),
            PartySet::from([0, 1, 3]),
        ])
        .unwrap();
        let mut foreign = vec![
            context(&fx, 2, 0, &[0, 1, 2]),
            context(&fx, 1, 0, &[0, 1, 2, 3]),
        ];
        let mut c = ctx.clone();
        c.commitment[0] += F::ONE;
        foreign.push(c);
        let mut c = ctx.clone();
        c.pk_seed[1] += F::ONE;
        foreign.push(c);
        for other in &foreign {
            assert_eq!(
                fx.parties[0].release(other, &full).err(),
                Some(PersonalReleaseError::Policy(
                    QuorumPolicyError::InvalidCertificate
                )),
            );
        }
        // A context for another program, policy or key/epoch never reaches the latch.
        let mut c = ctx.clone();
        c.program_digest = span_program_digest(&other_program);
        assert_eq!(
            fx.parties[0].release(&c, &full).err(),
            Some(PersonalReleaseError::ContextMismatch)
        );
        let mut c = ctx.clone();
        c.policy_digest[0] ^= 1;
        assert_eq!(
            fx.parties[0].release(&c, &full).err(),
            Some(PersonalReleaseError::ContextMismatch)
        );
        let mut c = ctx.clone();
        c.key_epoch_context[0] ^= 1;
        assert_eq!(
            fx.parties[0].acknowledge(&c, 1),
            Err(PersonalReleaseError::ContextMismatch)
        );
        assert!(fx.parties[0].has_input());

        // Another latch epoch for the same ceremony is a different record: the old
        // certificate does not open it.
        let later = context(&fx, 1, 1, &[0, 1, 2]);
        assert_eq!(
            fx.parties[0].release(&later, &full).err(),
            Some(PersonalReleaseError::Policy(
                QuorumPolicyError::InvalidCertificate
            ))
        );
        // A second ceremony at the already bound epoch is refused by every latch.
        let rival = context(&fx, 7, 0, &[0, 1, 2]);
        assert!(matches!(
            fx.parties[1].acknowledge(&rival, 0),
            Err(PersonalReleaseError::Policy(QuorumPolicyError::Latch(_)))
        ));

        // A party enrolled under another key/epoch context derives other pair keys:
        // its acknowledgements do not verify here.
        let outsider_input = PersonalMspInput::new(1, fx.program.clone(), {
            let count = fx.program.row_owners().iter().filter(|&&p| p == 1).count();
            SecretBuffer(vec![[F::ZERO; 4]; count])
        })
        .unwrap();
        let mut outsider =
            PersonalReleaseParty::new([0xDA; 32], latch(&fx.system, 1, [8; 32]), outsider_input)
                .unwrap();
        let mut outsider_ctx = ctx.clone();
        outsider_ctx.key_epoch_context = [8; 32];
        outsider_ctx.policy_digest = fx.system.policy_digest(&[8; 32]);
        let mut forged = full.clone();
        forged.acks[1] = outsider.acknowledge(&outsider_ctx, 0).unwrap();
        assert_eq!(
            fx.parties[0].release(&ctx, &forged).err(),
            Some(PersonalReleaseError::Policy(
                QuorumPolicyError::InvalidCertificate
            ))
        );

        // Finally the honest certificate still works, exactly once.
        assert!(fx.parties[0].release(&ctx, &full).is_ok());
        assert_eq!(
            fx.parties[0].release(&ctx, &full).err(),
            Some(PersonalReleaseError::AlreadyReleased)
        );
    }

    #[test]
    fn swapped_and_mixed_set_certificates_are_refused() {
        let mut fx = deal(73);
        let ctx = context(&fx, 1, 0, &[0, 1, 2]);
        // A certificate addressed to party 1 does not release party 0.
        let for_one = certificate(&mut fx, &ctx, 1);
        assert_eq!(
            fx.parties[0].release(&ctx, &for_one).err(),
            Some(PersonalReleaseError::Policy(
                QuorumPolicyError::InvalidCertificate
            ))
        );
        // Duplicated acknowledgements do not make a quorum.
        let mut duplicated = certificate(&mut fx, &ctx, 0);
        duplicated.acks[2] = duplicated.acks[1].clone();
        assert!(fx.parties[0].release(&ctx, &duplicated).is_err());

        // The latch alone accepts any quorum of its policy. A certificate for the same
        // record signed by a different set would select other reconstruction weights,
        // so the party refuses it. Party 3 acknowledges the raw record directly, as a
        // peer that ignores the context checks could.
        let record = ctx.record();
        let mut wider = certificate(&mut fx, &ctx, 0);
        let mut rogue = latch(&fx.system, 3, KEY_EPOCH);
        wider.acks.push(rogue.acknowledge(&record, 0).unwrap());
        assert_eq!(
            fx.parties[0].release(&ctx, &wider).err(),
            Some(PersonalReleaseError::SignerSetMismatch)
        );
        let mut other_three = wider.clone();
        other_three.acks.remove(2);
        assert_eq!(
            fx.parties[0].release(&ctx, &other_three).err(),
            Some(PersonalReleaseError::SignerSetMismatch)
        );
        assert!(fx.parties[0].has_input());
    }

    /// The defect the signer-set check closes: the plain adapter collapses for whatever
    /// set each receiver's certificate happens to carry, and lanes for different sets
    /// silently reconstruct a value that is not the secret.
    #[test]
    fn lanes_collapsed_for_different_signer_sets_do_not_reconstruct() {
        let system = system();
        let program = QuorumTopology::PersonalSlices(system.clone())
            .to_span_program(0)
            .unwrap();
        let secret = f4(73);
        let masks: Vec<[F; 4]> = (0..program.num_cols() - 1)
            .map(|i| f4(1000 + 31 * i as u64))
            .collect();
        let rows = program.share(&secret, &masks).unwrap();
        let mut latches: Vec<_> = (0u8..4).map(|p| latch(&system, p, KEY_EPOCH)).collect();
        let record = BeltLatchRecord {
            epoch: 0,
            msg_digest: [1; 32],
            retry_salt: [2; 32],
            target_sum_digits: Vec::new(),
        };
        let input = |p: u16| {
            let local: Vec<[F; 4]> = program
                .row_owners()
                .iter()
                .zip(rows.iter())
                .filter_map(|(&owner, &row)| (owner == p).then_some(row))
                .collect();
            PersonalMspInput::new(p, program.clone(), SecretBuffer(local)).unwrap()
        };
        let cert = |latches: &mut Vec<PersonalBeltLatch<MemoryWal>>, set: &[usize], to: u16| {
            PersonalLatchCertificate {
                acks: set
                    .iter()
                    .map(|&s| latches[s].acknowledge(&record, to).unwrap())
                    .collect(),
            }
        };
        // Parties 0 and 1 are in both quorums; each is shown a different one.
        let views: [(u16, [usize; 3]); 3] = [(0, [0, 1, 2]), (1, [0, 1, 3]), (2, [0, 1, 2])];
        let mut sum = [F::ZERO; 4];
        for (p, set) in views {
            let c = cert(&mut latches, &set, p);
            let lanes = input(p)
                .release(&mut latches[usize::from(p)], &record, &c)
                .unwrap();
            for k in 0..4 {
                sum[k] += lanes[k];
            }
        }
        assert_ne!(
            sum, secret,
            "mixed-set lanes must not be mistaken for the secret"
        );
        // The set-bound release refuses the odd certificate instead.
        let expected = PartySet::from([0, 1, 2]);
        let c = cert(&mut latches, &[0, 1, 3], 1);
        assert_eq!(
            input(1)
                .release_for_signers(&mut latches[1], &record, &c, &expected)
                .err(),
            Some(PersonalMspInputError::Access(AccessError::Unauthorized))
        );
        let mut sum = [F::ZERO; 4];
        for p in [0u16, 1, 2] {
            let c = cert(&mut latches, &[0, 1, 2], p);
            let lanes = input(p)
                .release_for_signers(&mut latches[usize::from(p)], &record, &c, &expected)
                .unwrap();
            for k in 0..4 {
                sum[k] += lanes[k];
            }
        }
        assert_eq!(sum, secret);
    }

    #[test]
    fn tooth_poisoned_ot_endpoint_preserves_unreleased_msp_input_and_journal() {
        // `#tooth`: Passing an already-poisoned `PartyOtEndpoint` to
        // `ceremony_with_established_ot` previously reserved the `mpc_sid` in the journal,
        // broadcast `ROUND_PREL_ACK` frames, and permanently burned `self.has_input()` before
        // discovering `ot.poisoned` inside the first OT step.
        let mut fx = deal(92);
        let ctx = context(&fx, 0x33, 0, &[0, 1, 2]);
        let mpc_sid = ctx.mpc_session_id();
        let mut party0 = fx.parties.remove(0);
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, mpc_sid);
        let endpoint0 = endpoints.remove(0);
        let mut wire_keys = party0.derive_wire_keys(&ctx).unwrap();
        let raw_keys = core::mem::take(&mut wire_keys.0);
        let mut wire0 =
            MacSealedWireChannel::new_encrypted(endpoint0, party0.deployment_id, mpc_sid, raw_keys)
                .unwrap();
        let mut poisoned_ot = PartyOtEndpoint {
            me: 0,
            parties: 3,
            roster: alloc::vec![0, 1, 2],
            session_id: mpc_sid,
            senders: alloc::vec![None, None, None],
            receivers: alloc::vec![None, None, None],
            transcript: [0; 32],
            ext2_blind_pool: Vec::new(),
            ext2_blind_cursor: 0,
            ext2_blind_serial: 0,
            poisoned: true,
            tamper_next_ext2_c: None,
        };
        let mut rng0 = PartyPrivateRng::from_seed([0x55; 32], b"poisoned-ot-preflight");
        let mut journal = MemoryPoisonJournal::new();

        assert_eq!(
            party0.ceremony_over_wire_with_ot(
                &ctx,
                &mut wire0,
                &mut poisoned_ot,
                &mut rng0,
                &mut journal,
            ),
            Err(PersonalReleaseError::SessionPoisoned)
        );
        assert!(
            party0.has_input(),
            "poisoned OT preflight must not burn the custodian's one-time MSP input"
        );
        assert!(
            !journal.is_poisoned(&mpc_sid),
            "poisoned OT preflight must fail before mutating the session journal"
        );
    }
}
