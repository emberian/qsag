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
    pub fn to_bytes(&self) -> Vec<u8> {
        [
            MAGIC.as_slice(),
            &[self.profile as u8],
            &self.bitmap.to_bytes(),
            &(self.payload.len() as u64).to_le_bytes(),
            &self.payload,
        ]
        .concat()
    }

    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut input = bytes.strip_prefix(MAGIC)?;
        let profile = match *input.split_off_first()? {
            1 => HemQuinticProfile::TurboShake400,
            2 => HemQuinticProfile::Poseidon2Gl24,
            _ => return None,
        };
        let (bitmap, used) = SignerBitmap::from_bytes_canonical(input)?;
        input = &input[used..];
        let len = u64::from_le_bytes(take(&mut input)?);
        (len == input.len() as u64 && len > 0 && bitmap.count_ones() != 0).then(|| Self {
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
