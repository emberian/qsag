//! Deterministic public Hem over the quintic Goldilocks extension. The verifier reconstructs
//! all public columns from the ordered committee, signer bitmap and messages. One commitment
//! covers all active signature traces. The schedule is derived from their dimensions.
use crate::arithmetize::{ShardCircuit, ShardSigner};
use crate::field::Goldilocks as F;
use crate::sig::{
    compute_message_mu, validate_unique_active_committee, verify_individual_signature_with_mu,
};
use crate::trace::{
    NUM_TRACE_COLS, populate_active_signer_rows, populate_inactive_signer_rows, rows_per_signer,
};
pub use crate::zk_hem::v2::field5::Fp5 as QuinticFp5;
use crate::zk_hem::v2::{hash::Transcript, params, pcs};
use crate::{SignerBitmap, SigningMode, ValidatorPublicKey, ValidatorSignature};
use QuinticFp5 as E;
use alloc::{vec, vec::Vec};

mod rows;
#[cfg(test)]
mod tests;
mod tree;
mod whir;

const FS_DOMAIN: [u64; 25] =
    crate::sponge::turboshake256_static_midstate(b"QSAG.HEM.QUINTIC.FS/v2");
// Paired with the verifier-call budget in PublicHemQuintic128.lean.
const FS_CALL_LIMIT: u16 = 4096;
pub const MAGIC: &[u8; 8] = b"QSAGHQM2";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum HemQuinticProfile {
    TurboShake400 = 1,
    Poseidon2Gl24 = 2,
}

impl HemQuinticProfile {
    /// Initialize the bounded `QSAG.HEM.QUINTIC.FS/v2` Fiat-Shamir [`Transcript`] bound to
    /// `(MAGIC, bitmap, committee)` and `mode`, identical to [`prove_hem_quintic_128`] and
    /// [`verify_hem_quintic_128`].
    pub fn open_transcript(
        self,
        pks: &[ValidatorPublicKey],
        bitmap: &SignerBitmap,
        mode: &SigningMode<'_>,
    ) -> Option<Transcript> {
        let committee: Vec<u8> = pks.iter().flat_map(ValidatorPublicKey::to_bytes).collect();
        let mut tr = Transcript::turbo_domain(
            &FS_DOMAIN,
            self as u8,
            &[MAGIC, &bitmap.to_bytes(), &committee],
            FS_CALL_LIMIT,
        );
        match mode {
            SigningMode::SharedMessage(m) => tr.absorb(b"SHARED", m),
            SigningMode::PerSignerMessages(ms) => {
                if ms.len() != bitmap.count_ones() {
                    return None;
                }
                tr.absorb(b"PER_SIGNER", &crate::sponge::encode_multi_frame(ms));
            }
        }
        Some(tr)
    }

    /// Canonical 50-byte (`TurboShake400`) Canopy leaf digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn turbo_canopy_leaf(stage: u8, index: u32, symbols: &[u8]) -> [u8; 50] {
        <tree::Turbo as tree::Hash<50>>::leaf(tree::Turbo, stage as usize, index as usize, symbols)
    }

    /// Canonical 50-byte (`TurboShake400`) Canopy internal node digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn turbo_canopy_node(index: u32, left: &[u8; 50], right: &[u8; 50]) -> [u8; 50] {
        <tree::Turbo as crate::zk_hem::v2::hash::CanopyHash<50>>::node(
            tree::Turbo,
            index,
            left,
            right,
        )
    }

    /// Canonical 50-byte (`TurboShake400`) Canopy root digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn turbo_canopy_root(stage: u8, depth: u8, top: &[u8; 50]) -> [u8; 50] {
        <tree::Turbo as crate::zk_hem::v2::hash::CanopyHash<50>>::root(
            tree::Turbo,
            stage,
            depth,
            top,
        )
    }

    /// Canonical 56-byte (`Poseidon2Gl24`) Canopy leaf digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn gl24_canopy_leaf(stage: u8, index: u32, symbols: &[u8]) -> [u8; 56] {
        <tree::Gl24 as tree::Hash<56>>::leaf(tree::Gl24, stage as usize, index as usize, symbols)
    }

    /// Canonical 56-byte (`Poseidon2Gl24`) Canopy Jive internal node digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn gl24_canopy_node(index: u32, left: &[u8; 56], right: &[u8; 56]) -> [u8; 56] {
        <tree::Gl24 as crate::zk_hem::v2::hash::CanopyHash<56>>::node(
            tree::Gl24,
            index,
            left,
            right,
        )
    }

    /// Canonical 56-byte (`Poseidon2Gl24`) Canopy root digest on `QSAG.HEM.QUINTIC.TREE/v2`.
    pub fn gl24_canopy_root(stage: u8, depth: u8, top: &[u8; 56]) -> [u8; 56] {
        <tree::Gl24 as crate::zk_hem::v2::hash::CanopyHash<56>>::root(
            tree::Gl24,
            stage,
            depth,
            top,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    Statement,
    Geometry,
    Signature,
    InconsistentTrace,
    TranscriptLimit,
}

/// A framed proof. Decoding the envelope is structural. Verification consumes the complete
/// payload using the dimensions and challenge indices derived from the caller's statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HemQuinticProof {
    pub profile: HemQuinticProfile,
    pub bitmap: SignerBitmap,
    payload: Vec<u8>,
}

impl HemQuinticProof {
    #[inline]
    pub fn num_signers(&self) -> usize {
        self.bitmap.count_ones()
    }

    pub(crate) fn push_wire_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(MAGIC);
        out.push(self.profile as u8);
        out.extend_from_slice(&self.bitmap.to_bytes());
        out.extend_from_slice(&(self.payload.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.payload);
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(24 + self.payload.len());
        self.push_wire_bytes(&mut out);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut input = bytes;
        let magic = take::<8>(&mut input)?;
        let profile_tag = *input.split_off_first()?;
        let (bitmap, used) = SignerBitmap::from_bytes_canonical(input)?;
        input = &input[used..];
        let declared_len = u64::from_le_bytes(take(&mut input)?);
        let header = qsag_whir_verified::verify_qsaghqm2_header(
            magic,
            profile_tag,
            bitmap.count_ones() as u64,
            bitmap.num_validators() as u64,
            declared_len,
            input.len() as u64,
        )?;
        let profile = match header.profile_tag {
            qsag_whir_verified::QSAGHQM2_PROFILE_TURBO400 => HemQuinticProfile::TurboShake400,
            qsag_whir_verified::QSAGHQM2_PROFILE_GL24 => HemQuinticProfile::Poseidon2Gl24,
            _ => return None,
        };
        Some(Self {
            profile,
            bitmap,
            payload: input.to_vec(),
        })
    }
}

fn take<const N: usize>(input: &mut &[u8]) -> Option<[u8; N]> {
    Some(*input.split_off(..N)?.first_chunk()?)
}

fn read_e(input: &mut &[u8]) -> Option<E> {
    E::from_le_bytes_canonical(take(input)?)
}
fn read_es<const K: usize>(input: &mut &[u8]) -> Option<[E; K]> {
    let mut out = [E::ZERO; K];
    for x in &mut out {
        *x = read_e(input)?;
    }
    Some(out)
}
fn write_es(out: &mut Vec<u8>, xs: &[E]) {
    for x in xs {
        out.extend_from_slice(&x.to_le_bytes());
    }
}

struct Statement {
    circuit: ShardCircuit,
    signers: Vec<ShardSigner>,
    dims: Vec<pcs::StageDims>,
    transcript: Transcript,
}

fn statement(
    profile: HemQuinticProfile,
    pks: &[ValidatorPublicKey],
    bitmap: &SignerBitmap,
    mode: &SigningMode<'_>,
) -> Result<Statement, Error> {
    let scheme = pks
        .get(bitmap.first_active().ok_or(Error::Statement)?)
        .ok_or(Error::Statement)?
        .profile;
    if !validate_unique_active_committee(pks, bitmap, scheme) {
        return Err(Error::Statement);
    }
    let active = bitmap.active_indices();
    let slots = active
        .len()
        .checked_next_power_of_two()
        .ok_or(Error::Geometry)?;
    let cells = slots
        .checked_mul(rows_per_signer(scheme) * NUM_TRACE_COLS)
        .ok_or(Error::Geometry)?;
    let log = cells.ilog2() as usize;
    let schedule = params::schedule(log).ok_or(Error::Geometry)?;
    let folded_sum: u32 = schedule.stages.iter().map(|s| s.step_vars as u32).sum();
    if !qsag_whir_verified::verify_quintic_schedule_envelope(
        log as u32,
        schedule.early_stop_vars as u32,
        folded_sum,
        schedule.stages.len() as u32,
    ) {
        return Err(Error::Geometry);
    }
    let dims = pcs::stage_dims(log, &schedule).ok_or(Error::Geometry)?;
    let circuit = ShardCircuit::new(scheme, slots);
    let committee: Vec<u8> = pks.iter().flat_map(ValidatorPublicKey::to_bytes).collect();
    let mut transcript = Transcript::turbo_domain(
        &FS_DOMAIN,
        profile as u8,
        &[MAGIC, &bitmap.to_bytes(), &committee],
        FS_CALL_LIMIT,
    );
    match mode {
        SigningMode::SharedMessage(m) => transcript.absorb(b"SHARED", m),
        SigningMode::PerSignerMessages(ms) => {
            if ms.len() != active.len() {
                return Err(Error::Statement);
            }
            transcript.absorb(b"PER_SIGNER", &crate::sponge::encode_multi_frame(ms));
        }
    }
    let signers = active
        .into_iter()
        .enumerate()
        .map(|(pos, i)| {
            let pk = pks[i];
            let msg = match mode {
                SigningMode::SharedMessage(m) => *m,
                SigningMode::PerSignerMessages(ms) => ms[pos],
            };
            ShardSigner {
                pk,
                mu: compute_message_mu(&pk, msg).1,
            }
        })
        .collect();
    Ok(Statement {
        circuit,
        signers,
        dims,
        transcript,
    })
}

/// Prove one signature for each set bit, in ascending committee index order.
pub fn prove_hem_quintic_128(
    profile: HemQuinticProfile,
    pks: &[ValidatorPublicKey],
    bitmap: &SignerBitmap,
    mode: &SigningMode<'_>,
    sigs: &[ValidatorSignature],
) -> Result<HemQuinticProof, Error> {
    let st = statement(profile, pks, bitmap, mode)?;
    if sigs.len() != st.signers.len()
        || !st
            .signers
            .iter()
            .zip(sigs)
            .all(|(s, sig)| verify_individual_signature_with_mu(&s.pk, s.mu, sig))
    {
        return Err(Error::Signature);
    }
    #[cfg(feature = "std")]
    let _permit = crate::prover_admission::acquire();
    let mut rows = vec![[F::ZERO; NUM_TRACE_COLS]; 1 << st.circuit.log_rows()];
    for (i, slot) in rows.chunks_mut(st.circuit.rows_per_signer()).enumerate() {
        if let Some(s) = st.signers.get(i) {
            populate_active_signer_rows(&st.circuit.program, &s.pk, s.mu, &sigs[i], slot);
        } else {
            populate_inactive_signer_rows(slot, &[]);
        }
    }
    let payload = match profile {
        HemQuinticProfile::TurboShake400 => whir::prove(tree::Turbo, st, rows),
        HemQuinticProfile::Poseidon2Gl24 => whir::prove(tree::Gl24, st, rows),
    }?;
    Ok(HemQuinticProof {
        profile,
        bitmap: bitmap.clone(),
        payload,
    })
}

/// Verify a decoded public proof against the ordered committee and signing mode.
/// On success, the set bits of `proof.bitmap` identify the signing validators.
pub fn verify_hem_quintic_128(
    pks: &[ValidatorPublicKey],
    mode: &SigningMode<'_>,
    proof: &HemQuinticProof,
) -> bool {
    let Ok(st) = statement(proof.profile, pks, &proof.bitmap, mode) else {
        return false;
    };
    match proof.profile {
        HemQuinticProfile::TurboShake400 => whir::verify(tree::Turbo, st, &proof.payload),
        HemQuinticProfile::Poseidon2Gl24 => whir::verify(tree::Gl24, st, &proof.payload),
    }
    .is_some()
}
