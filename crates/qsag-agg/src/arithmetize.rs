//! Multilinear Sumcheck + `Hem` `GoldilocksExt4` WHIR Arithmetization for Batches of Signature Shards.
//!
//! Proves simultaneous algebraic satisfaction of parallel post-quantum hash-based signature
//! verifications (`JortsPoseidon2` or `CorduroyPoseidon2`) without shipping the underlying
//! raw WOTS+C chains or FORS/XMSS Merkle paths. The signers of a batch are split into shards of
//! at most [`max_shard_signers`] signers; for each shard the prover
//! 1. flattens the $M \times 256$ execution trace (`M = num_signer_slots * rows_per_signer`) into a
//!    multilinear witness polynomial $W(z_0..z_7, x_0..x_{\ell_x - 1})$ over `Goldilocks`
//!    (with `Idle` rows blinded by fresh cryptographic randomness).
//!
//! All shard witnesses of the batch are committed under ONE Merkle-Canopy tree
//! (`pcs::whir_commit_batch_owned`), and a single `FiatShamirTranscript<InstanceBound>` binds the
//! batch statement (profile, committee root, signer bitmap, shard signer counts, signing-mode
//! digest) and then that commitment. Shard by shard, on that same transcript, the prover then
//! 2. absorbs the shard index and squeezes the row-zerocheck challenge
//!    $\tau \in \mathbb{F}_{p^4}^{\ell_x}$ and constraint-batching challenge $\gamma \in \mathbb{F}_{p^4}$,
//! 3. runs a degree-8 Multilinear Sumcheck over $x \in \{0, 1\}^{\ell_x}$ (`~249` bits unconditional
//!    sumcheck soundness over `GoldilocksExt4`; Round 0 evaluated via the 8-byte base-field turbo path),
//!    proving all 118 `Poseidon2` $x^7$ S-box equations, boundary resets, opcode-gated WOTS+C/FORS/XMSS
//!    transitions, AND the 44 multilinear inter-row shift-bus identities,
//! 4. emits the 256 column evaluations `col_evals[0..256]` at $r_x$ and absorbs them; the verifier
//!    **enforces the mandatory terminal Sumcheck evaluation check**
//!    `cur_sum_claim == eval_batched_row_constraints_ext4(..., &col_evals, &pub_eval_at_rx, gamma)`,
//! 5. squeezes the column-folding challenge $r_z \in \mathbb{F}_{p^4}^8$, which fixes the shard's
//!    evaluation claim $W(r_z, r_x) = \widetilde{\text{col\_evals}}(r_z)$.
//!
//! Finally one `pcs::whir_open_batch` proof opens every shard's claim at once with WHIR rate
//! escalation, OOD list-pinning, per-stage Proof-of-Work, and Steiner deduplicated multiproofs.

use alloc::vec;
use alloc::vec::Vec;

use crate::field::{
    Goldilocks, GoldilocksExt4, build_eq_table_ext4, eq_poly_ext4, eval_univariate_ext4,
    mle_eval_ext4,
};
use crate::pcs::{
    CanopyCommitment, HemWhirBatchOpeningProof, MAX_BATCH_POLYS, MAX_PCS_NUM_VARS, WhirSchedule,
    whir_commit_batch_owned_with_schedule, whir_open_batch, whir_verify_batch_with_schedule,
};
use crate::sig::{
    AggSigProfile, Digest5, SignerBitmap, SigningMode, ValidatorPublicKey, ValidatorSignature,
    compute_message_mu, validate_unique_active_committee, verify_individual_signature,
};
use crate::sponge::{
    FiatShamirTranscript, InstanceBound, cshake256_32, encode_multi_frame, shake256_into,
};
use crate::trace::{
    COL_AUX, COL_SBOX_OUT, COL_ST_IN, ConstraintKind, LOG_TRACE_COLS, NUM_TRACE_COLS,
    RowPublicEvalExt4, SparseBaseRowPublicEvalExt4, SparseRowPublicEvalExt4, StepOp,
    build_gamma_schedule_ext4, build_signer_program, dot_shift_state_base_ext4,
    dot_shift_state_ext4, eval_batched_row_constraints_ext4, eval_eq_part_base_row_ext4,
    eval_eq_part_sparse_ext4, index_unique_program_ops, populate_active_signer_rows,
    populate_inactive_signer_rows, record_poseidon2_perm12, rows_per_signer,
};

/// Degree bound of the row-sumcheck univariate polynomial in each round (`1` from `eq_tau` + `7` from $x^7$).
pub const ROW_SUMCHECK_DEGREE: usize = 8;
/// Number of evaluation points / full coefficients per degree-8 sumcheck round polynomial (`9`).
pub const ROW_SUMCHECK_COEFFS: usize = ROW_SUMCHECK_DEGREE + 1;
/// Number of wire-transmitted `GoldilocksExt4` coefficients per degree-8 round (`c_1` omitted via $P(0)+P(1)=\text{claim}$).
pub const ROW_SUMCHECK_WIRE_COEFFS: usize = ROW_SUMCHECK_DEGREE;

// ============================================================================
// 1. Exact Multilinear Inter-Row Shift Kernel Identities
// ============================================================================

/// Evaluate $E_{\text{not\_last}}(\tau, X) = \text{eq}(\tau, X) - \prod_{i=0}^{\ell-1} (\tau_i X_i)$ in $O(\ell)$ over `GoldilocksExt4`.
///
/// On $\{0, 1\}^\ell$, equals $\text{eq}(\tau, u)$ for $0 \le u < 2^\ell - 1$ and $0$ at $u = 2^\ell - 1$.
pub fn eval_eq_not_last_ext4(tau: &[GoldilocksExt4], rx: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(tau.len(), rx.len());
    let eq_val = eq_poly_ext4(tau, rx);
    let mut all_ones_term = GoldilocksExt4::ONE;
    for (&t, &x) in tau.iter().zip(rx.iter()) {
        all_ones_term *= t * x;
    }
    eq_val - all_ones_term
}

/// Evaluate the exact multilinear shift kernel $S_\tau(X)$ in $O(\ell)$ over `GoldilocksExt4`.
pub fn eval_shift_kernel_ext4(tau: &[GoldilocksExt4], rx: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(tau.len(), rx.len());
    let ell = tau.len();
    if ell == 0 {
        return GoldilocksExt4::ZERO;
    }
    let mut suf = vec![GoldilocksExt4::ONE; ell];
    let mut acc = GoldilocksExt4::ONE;
    for j in (0..ell).rev() {
        suf[j] = acc;
        let t = tau[j];
        let x = rx[j];
        let eq_j = t * x + (GoldilocksExt4::ONE - t) * (GoldilocksExt4::ONE - x);
        acc *= eq_j;
    }

    let mut total = GoldilocksExt4::ZERO;
    let mut pref_carry = GoldilocksExt4::ONE;
    for j in 0..ell {
        let one_minus_tau = GoldilocksExt4::ONE - tau[j];
        let term = pref_carry * one_minus_tau * rx[j] * suf[j];
        total += term;
        pref_carry *= tau[j] * (GoldilocksExt4::ONE - rx[j]);
    }
    total
}

/// Build boolean-hypercube tables `(eq_table, eq_not_last_table, shift_table)` of length $2^\ell$ over `GoldilocksExt4`.
pub fn build_shift_tables_ext4(
    tau: &[GoldilocksExt4],
) -> (
    Vec<GoldilocksExt4>,
    Vec<GoldilocksExt4>,
    Vec<GoldilocksExt4>,
) {
    let eq_table = build_eq_table_ext4(tau);
    let m = eq_table.len();
    let mut not_last = eq_table.clone();
    if m > 0 {
        not_last[m - 1] = GoldilocksExt4::ZERO;
    }
    let mut shift = vec![GoldilocksExt4::ZERO; m];
    if m > 0 {
        shift[1..].copy_from_slice(&eq_table[..m - 1]);
    }
    (eq_table, not_last, shift)
}

// ============================================================================
// 2. Degree-8 Newton Forward-Difference Interpolation
// ============================================================================

/// Interpolate a degree-$\le 8$ univariate polynomial $P(T) = \sum_{k=0}^8 c_k T^k$ from its
/// 9 evaluations `evals = [P(0), P(1), ..., P(8)]` over `GoldilocksExt4`.
pub fn interpolate_deg8_from_evals_ext4(
    evals: &[GoldilocksExt4; ROW_SUMCHECK_COEFFS],
) -> [GoldilocksExt4; ROW_SUMCHECK_COEFFS] {
    let mut diff = *evals;
    let mut newton = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
    newton[0] = diff[0];
    for (k, newton_k) in newton.iter_mut().enumerate().skip(1) {
        for i in 0..(ROW_SUMCHECK_COEFFS - k) {
            diff[i] = diff[i + 1] - diff[i];
        }
        *newton_k = diff[0];
    }

    let mut coeffs = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
    let mut fall = [Goldilocks::ZERO; ROW_SUMCHECK_COEFFS];
    fall[0] = Goldilocks::ONE;
    let mut fact = Goldilocks::ONE;

    for (k, &newton_item) in newton.iter().enumerate().take(ROW_SUMCHECK_COEFFS) {
        if k > 0 {
            fact *= Goldilocks::from_u64_reduced(k as u64);
        }
        let scaled_nk = newton_item.mul_base(fact.inv());
        for j in 0..=k {
            coeffs[j] += scaled_nk.mul_base(fall[j]);
        }
        if k + 1 < ROW_SUMCHECK_COEFFS {
            let k_elem = Goldilocks::from_u64_reduced(k as u64);
            let mut next_fall = [Goldilocks::ZERO; ROW_SUMCHECK_COEFFS];
            for j in 0..=k {
                next_fall[j + 1] += fall[j];
                next_fall[j] -= fall[j] * k_elem;
            }
            fall = next_fall;
        }
    }
    coeffs
}

#[inline]
fn pack_deg8_wire(
    full: &[GoldilocksExt4; ROW_SUMCHECK_COEFFS],
) -> [GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS] {
    [
        full[0], full[2], full[3], full[4], full[5], full[6], full[7], full[8],
    ]
}

#[inline]
fn unpack_deg8_wire(
    wire: &[GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS],
    sum_claim: GoldilocksExt4,
) -> [GoldilocksExt4; ROW_SUMCHECK_COEFFS] {
    let mut hi_sum = GoldilocksExt4::ZERO;
    for &c in &wire[1..] {
        hi_sum += c;
    }
    let c0 = wire[0];
    let c1 = sum_claim - c0 - c0 - hi_sum;
    [
        c0, c1, wire[1], wire[2], wire[3], wire[4], wire[5], wire[6], wire[7],
    ]
}

// ============================================================================
// 3. Shard Batch Proof & Canonical Wire Encoding
// ============================================================================

/// Largest number of signers one shard can hold under `profile`: the shard's witness polynomial
/// has `LOG_TRACE_COLS + log2(num_signer_slots * rows_per_signer)` variables, which must not
/// exceed [`MAX_PCS_NUM_VARS`].
pub const fn max_shard_signers(profile: AggSigProfile) -> usize {
    1usize
        << (MAX_PCS_NUM_VARS - LOG_TRACE_COLS - rows_per_signer(profile).trailing_zeros() as usize)
}

/// Per-shard part of a [`ShardBatchProof`]: the degree-8 `GoldilocksExt4` row sumcheck
/// (`c_1` reconstructed via $P(0) + P(1) = \text{claim}$) and the 256 trace column evaluations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardRowProof {
    pub row_sumcheck_polys: Vec<[GoldilocksExt4; ROW_SUMCHECK_WIRE_COEFFS]>,
    pub col_evals: Vec<GoldilocksExt4>,
}

/// Proof that every signer marked in `bitmap` produced a valid signature, for
/// `shard_signer_counts.len()` shards whose witness polynomials share one commitment and one
/// batched WHIR PCS opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardBatchProof {
    pub schedule: WhirSchedule,
    pub bitmap: SignerBitmap,
    pub shard_signer_counts: Vec<u32>,
    pub witness_comm: CanopyCommitment,
    pub shards: Vec<ShardRowProof>,
    pub pcs_opening: HemWhirBatchOpeningProof,
}

/// Validated dimensions of a shard batch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BatchShape {
    num_signer_slots: usize,
    log_rows: usize,
}

/// Check `shard_signer_counts` against the batch's signer total and the profile's shard capacity.
fn batch_shape(
    profile: AggSigProfile,
    shard_signer_counts: &[u32],
    total_signers: usize,
) -> Option<BatchShape> {
    if shard_signer_counts.is_empty() || shard_signer_counts.len() > MAX_BATCH_POLYS {
        return None;
    }
    let mut sum = 0usize;
    let mut largest = 0usize;
    for &count in shard_signer_counts {
        let count = count as usize;
        if count == 0 || count > max_shard_signers(profile) {
            return None;
        }
        sum += count;
        largest = largest.max(count);
    }
    if sum != total_signers {
        return None;
    }
    let num_signer_slots = largest.next_power_of_two().max(2);
    let total_rows = num_signer_slots * rows_per_signer(profile);
    Some(BatchShape {
        num_signer_slots,
        log_rows: total_rows.trailing_zeros() as usize,
    })
}

impl ShardBatchProof {
    #[inline]
    pub fn num_shards(&self) -> usize {
        self.shard_signer_counts.len()
    }

    pub fn push_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.bitmap.to_bytes());
        out.push(self.shard_signer_counts.len() as u8);
        for count in &self.shard_signer_counts {
            out.extend_from_slice(&count.to_le_bytes());
        }
        out.extend_from_slice(&self.schedule.to_bytes());
        out.extend_from_slice(&self.witness_comm.to_bytes());
        for shard in &self.shards {
            for poly in &shard.row_sumcheck_polys {
                for c in poly {
                    out.extend_from_slice(&c.to_le_bytes());
                }
            }
            for v in &shard.col_evals {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        self.pcs_opening.push_bytes(out);
    }

    /// Parse the canonical encoding of a shard batch under `profile`. The number of row-sumcheck
    /// rounds is not on the wire: it follows from the signer counts and the profile.
    pub fn from_bytes_canonical(profile: AggSigProfile, bytes: &[u8]) -> Option<(Self, usize)> {
        let (bitmap, mut pos) = SignerBitmap::from_bytes_canonical(bytes)?;
        let num_shards = *bytes.get(pos)? as usize;
        pos += 1;
        let count_bytes = bytes.get(pos..pos.checked_add(4 * num_shards)?)?;
        let shard_signer_counts: Vec<u32> = count_bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
            .collect();
        pos += 4 * num_shards;
        let shape = batch_shape(profile, &shard_signer_counts, bitmap.count_ones())?;

        let (schedule, used_schedule) =
            WhirSchedule::from_bytes_canonical(bytes.get(pos..)?, LOG_TRACE_COLS + shape.log_rows)?;
        pos += used_schedule;

        let (witness_comm, used_wc) = CanopyCommitment::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_wc;

        let read_ext4 = |pos: &mut usize| -> Option<GoldilocksExt4> {
            let chunk = bytes.get(*pos..pos.checked_add(32)?)?;
            let mut cb = [0u8; 32];
            cb.copy_from_slice(chunk);
            *pos += 32;
            GoldilocksExt4::from_le_bytes_canonical(cb)
        };
        let mut shards = Vec::with_capacity(num_shards);
        for _ in 0..num_shards {
            let mut row_sumcheck_polys = Vec::with_capacity(shape.log_rows);
            for _ in 0..shape.log_rows {
                let mut poly = [GoldilocksExt4::ZERO; ROW_SUMCHECK_WIRE_COEFFS];
                for coeff in &mut poly {
                    *coeff = read_ext4(&mut pos)?;
                }
                row_sumcheck_polys.push(poly);
            }
            let mut col_evals = Vec::with_capacity(NUM_TRACE_COLS);
            for _ in 0..NUM_TRACE_COLS {
                col_evals.push(read_ext4(&mut pos)?);
            }
            shards.push(ShardRowProof {
                row_sumcheck_polys,
                col_evals,
            });
        }

        let (pcs_opening, used_pcs) =
            HemWhirBatchOpeningProof::from_bytes_canonical(bytes.get(pos..)?)?;
        pos += used_pcs;

        Some((
            Self {
                schedule,
                bitmap,
                shard_signer_counts,
                witness_comm,
                shards,
                pcs_opening,
            },
            pos,
        ))
    }
}

// ============================================================================
// 4. Transcript Statement Binding & Blinding Helpers
// ============================================================================

/// Domain-separated 32-byte digest binding the exact `SigningMode` statement for `active_indices`.
pub fn compute_signing_mode_digest(
    pks: &[ValidatorPublicKey],
    active_indices: &[usize],
    mode: &SigningMode<'_>,
) -> Option<[u8; 32]> {
    match mode {
        SigningMode::SharedMessage(msg) => {
            let framed = encode_multi_frame(&[b"SHARED_MSG_V2", msg]);
            Some(cshake256_32(b"QSAG.SIGNING.MODE/v2", &framed))
        }
        SigningMode::PerSignerMessages(msgs) => {
            if msgs.len() != active_indices.len() {
                return None;
            }
            let mut slices: Vec<&[u8]> = Vec::with_capacity(1 + 2 * msgs.len());
            slices.push(b"PER_SIGNER_MSGS_V2");
            let pk_bytes_vec: Vec<[u8; 65]> = active_indices
                .iter()
                .map(|&idx| pks[idx].to_bytes())
                .collect();
            for (pk_b, m) in pk_bytes_vec.iter().zip(msgs.iter()) {
                slices.push(pk_b);
                slices.push(m);
            }
            let framed = encode_multi_frame(&slices);
            Some(cshake256_32(b"QSAG.SIGNING.MODE/v2", &framed))
        }
    }
}

fn init_shard_batch_transcript(
    profile: AggSigProfile,
    committee_root: &[u8; 32],
    bitmap: &SignerBitmap,
    shard_signer_counts: &[u32],
    signing_mode_digest: &[u8; 32],
    schedule: &WhirSchedule,
) -> FiatShamirTranscript<InstanceBound> {
    let bm_bytes = bitmap.to_bytes();
    let mut count_bytes = Vec::with_capacity(4 * shard_signer_counts.len());
    for count in shard_signer_counts {
        count_bytes.extend_from_slice(&count.to_le_bytes());
    }
    let prof_byte = [profile as u8];
    FiatShamirTranscript::new()
        .bind_relation(b"QSAG.SHARD.BATCH/v5", &prof_byte, schedule)
        .bind_instance(&[committee_root, &bm_bytes, &count_bytes, signing_mode_digest])
}

fn blind_idle_rows_in_slot(
    program: &[StepOp],
    slot_rows: &mut [[Goldilocks; NUM_TRACE_COLS]],
    blinding_seed: &[u8; 32],
    slot_idx: usize,
) {
    let mut prg_in = [0u8; 40];
    prg_in[0..32].copy_from_slice(blinding_seed);
    prg_in[32..40].copy_from_slice(&(slot_idx as u64).to_le_bytes());

    let mut stream = [0u8; 400];
    for (t, &op) in program.iter().enumerate() {
        if op != StepOp::Idle {
            continue;
        }
        let mut row_seed = [0u8; 48];
        row_seed[0..40].copy_from_slice(&prg_in);
        row_seed[40..48].copy_from_slice(&(t as u64).to_le_bytes());
        shake256_into(&row_seed, &mut stream);

        let row = &mut slot_rows[t];
        let mut st_in = [Goldilocks::ZERO; 12];
        for i in 0..12 {
            let mut b = [0u8; 8];
            b.copy_from_slice(&stream[8 * i..8 * (i + 1)]);
            st_in[i] = Goldilocks::from_u64_reduced(u64::from_le_bytes(b));
        }
        let mut sbox = [Goldilocks::ZERO; 118];
        let _ = record_poseidon2_perm12(st_in, &mut sbox);
        row[COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
        row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&sbox);

        for i in 0..38 {
            let base = 96 + 8 * i;
            let mut b = [0u8; 8];
            b.copy_from_slice(&stream[base..base + 8]);
            row[COL_AUX + i] = Goldilocks::from_u64_reduced(u64::from_le_bytes(b));
        }
    }
}

fn merge_sparse_op_lists(
    l0: &[(usize, GoldilocksExt4)],
    l1: &[(usize, GoldilocksExt4)],
    r: GoldilocksExt4,
) -> Vec<(usize, GoldilocksExt4)> {
    let one_minus_r = GoldilocksExt4::ONE - r;
    let mut out = Vec::with_capacity(l0.len() + l1.len());
    let (mut i, mut j) = (0usize, 0usize);
    while i < l0.len() && j < l1.len() {
        let (u0, v0) = l0[i];
        let (u1, v1) = l1[j];
        if u0 == u1 {
            let v = one_minus_r * v0 + r * v1;
            if !v.is_zero() {
                out.push((u0, v));
            }
            i += 1;
            j += 1;
        } else if u0 < u1 {
            let v = one_minus_r * v0;
            if !v.is_zero() {
                out.push((u0, v));
            }
            i += 1;
        } else {
            let v = r * v1;
            if !v.is_zero() {
                out.push((u1, v));
            }
            j += 1;
        }
    }
    while i < l0.len() {
        let (u0, v0) = l0[i];
        let v = one_minus_r * v0;
        if !v.is_zero() {
            out.push((u0, v));
        }
        i += 1;
    }
    while j < l1.len() {
        let (u1, v1) = l1[j];
        let v = r * v1;
        if !v.is_zero() {
            out.push((u1, v));
        }
        j += 1;
    }
    out
}

/// Interpolate union of `(op_uid, v0, v1 - v0)` pairs for evaluating `0..=8` along `(l0, l1)`.
fn union_sparse_op_pairs(
    l0: &[(usize, GoldilocksExt4)],
    l1: &[(usize, GoldilocksExt4)],
    out: &mut Vec<(usize, GoldilocksExt4, GoldilocksExt4)>,
) {
    out.clear();
    let (mut i, mut j) = (0usize, 0usize);
    while i < l0.len() && j < l1.len() {
        let (u0, v0) = l0[i];
        let (u1, v1) = l1[j];
        if u0 == u1 {
            out.push((u0, v0, v1 - v0));
            i += 1;
            j += 1;
        } else if u0 < u1 {
            out.push((u0, v0, -v0));
            i += 1;
        } else {
            out.push((u1, GoldilocksExt4::ZERO, v1));
            j += 1;
        }
    }
    while i < l0.len() {
        let (u0, v0) = l0[i];
        out.push((u0, v0, -v0));
        i += 1;
    }
    while j < l1.len() {
        let (u1, v1) = l1[j];
        out.push((u1, GoldilocksExt4::ZERO, v1));
        j += 1;
    }
}

// ============================================================================
// 5. Shard Batch Prover & Verifier
