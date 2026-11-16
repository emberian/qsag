//! End-to-end personal release: an [`AsymmetricQuorumSystem`] certificate from the
//! [`PersonalBeltLatch`] unlocks each certified party's [`PersonalMspInput`] lanes, and
//! the lanes enter an SPDZ-authenticated `Poseidon2` evaluation whose only opened value
//! is the `Hem` PRF-check digest of the shared secret.
//!
//! ### Roles
//! * [`PersonalReleaseContext`] is public. It fixes the policy, the enrolled span
//!   program, the key/epoch context, the ceremony, the latch epoch, the exact signer
//!   set, and the enrolled commitment. Its digest is the message the latch binds, so an
//!   acknowledgement for one context authorizes nothing in any other.
//! * [`PersonalReleaseParty`] is one custodian: its own latch and WAL and its own span
//!   program rows. It acknowledges a context only after checking it against its own
//!   enrolled policy and program, and it releases only for a certificate signed by
//!   exactly the context's signer set.
//! * [`run_personal_release_mpc`] drives the authenticated evaluation. It never adds
//!   lanes together; it opens one digest and compares it with the enrolled commitment.
//!
//! ### What is assumed
//! * The span-program rows and the commitment come from a share-generation step outside
//!   this module ([`MonotoneSpanProgram::share`] by a dealer in the tests). Whoever runs
//!   that step knows the secret. Nothing here is a distributed key generation.
//! * Latch pair keys are authenticated pairwise secrets established beforehand.
//! * `qsag-core`'s SPDZ entry points take every party's private state as slices of one
//!   call. [`run_personal_release_mpc`] is therefore an in-process driver of the party
//!   computations, not a wire transport: the process that calls it sees the released
//!   lanes of all signers. Run it where that is acceptable, or port the party steps to
//!   [`crate::wire_channel`].
//! * A party that substitutes its own lane changes the input, which no MAC can detect;
//!   the comparison with the enrolled commitment does. A share changed after
//!   authentication fails `MacCheck` inside the evaluation.

use alloc::vec::Vec;

use qsag_core::{
    belt_latch::{BeltLatchRecord, DurableWal},
    field::goldilocks::Goldilocks,
    poseidon2_mpc::{HemDigest4, Poseidon2MpcError, release_additive_hem_prf_check_mpc},
    preprocessing::{OtMesh, PartyPrivateRng},
    sponge::keccak::shake256_32,
    wipe::SecretBuffer,
};

use crate::access::{
    AccessError, AsymmetricQuorumSystem, MonotoneSpanProgram, PartySet, PersonalBeltLatch,
    PersonalLatchAck, PersonalLatchCertificate, QuorumPolicyError,
};
use crate::party_node::{PersonalMspInput, PersonalMspInputError};

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
    /// The lanes handed to the evaluation are not exactly one per signer, in order.
    LaneRosterMismatch,
    /// The opened digest differs from the enrolled commitment.
    CommitmentMismatch,
    Policy(QuorumPolicyError),
    Access(AccessError),
    Mpc(Poseidon2MpcError),
}

/// Public description of one release ceremony.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PersonalReleaseContext {
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
        system: &AsymmetricQuorumSystem,
        program: &MonotoneSpanProgram,
        key_epoch_context: [u8; 32],
        ceremony_id: [u8; 32],
        latch_epoch: u64,
        signers: PartySet,
        pk_seed: HemDigest4,
        commitment: HemDigest4,
    ) -> Result<Self, PersonalReleaseError> {
        if signers.is_empty()
            || !signers.is_subset(system.participants())
            || program.solve_reconstruction_weights(&signers).is_none()
        {
            return Err(PersonalReleaseError::ContextMismatch);
        }
        Ok(Self {
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

    /// Fixed-order `QPRC0001` frame of every field. All fields but the signer list have
    /// fixed width and the list carries its length, so the encoding is injective.
    fn frame(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + 4 * 32 + 8 + 8 + 2 * self.signers.len() + 64);
        out.extend_from_slice(b"QPRC0001");
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
    fn mpc_session_id(&self) -> [u8; 32] {
        let mut framed = [0u8; 40];
        framed[..8].copy_from_slice(b"QPRS0001");
        framed[8..].copy_from_slice(&self.record().binding());
        shake256_32(&framed)
    }
}

/// One custodian: its own latch and its own span-program rows, nothing of any peer.
pub struct PersonalReleaseParty<W: DurableWal> {
    latch: PersonalBeltLatch<W>,
    program_digest: [u8; 32],
    program: MonotoneSpanProgram,
    input: Option<PersonalMspInput>,
}

impl<W: DurableWal> PersonalReleaseParty<W> {
    pub fn new(
        latch: PersonalBeltLatch<W>,
        input: PersonalMspInput,
    ) -> Result<Self, PersonalReleaseError> {
        if latch.party() != input.party() {
            return Err(PersonalReleaseError::ContextMismatch);
        }
        Ok(Self {
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

    /// Check the public context against this party's own enrolled state and return the
    /// record it would bind. Nothing is persisted here.
    fn checked_record(
        &self,
        ctx: &PersonalReleaseContext,
    ) -> Result<BeltLatchRecord, PersonalReleaseError> {
        let own_context = self.latch.key_epoch_context();
        if ctx.key_epoch_context != *own_context
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
}

/// Evaluate the PRF-check digest on the released lanes under SPDZ authentication and
/// return it only if it equals the enrolled commitment.
///
/// `lanes` holds exactly one entry per context signer, in ascending party order, and
/// `party_rngs` the matching private randomness. The evaluation is full-threshold among
/// the signers. `ot_mesh` must be an authenticated mesh among those same parties.
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
    use alloc::{collections::BTreeMap, vec, vec::Vec};
    use qsag_core::{
        belt_latch::{BeltLatch, MemoryWal},
        poseidon2_mpc::hem_prf_check_digest_clear,
    };

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
                PersonalReleaseParty::new(latch(&system, p, KEY_EPOCH), input).unwrap()
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

    fn context(fx: &Fixture, ceremony: u8, epoch: u64, signers: &[u16]) -> PersonalReleaseContext {
        PersonalReleaseContext::new(
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
            PersonalReleaseParty::new(latch(&fx.system, 1, [8; 32]), outsider_input).unwrap();
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
}
