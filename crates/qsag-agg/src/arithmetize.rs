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
    WhirSecurityRegime, whir_commit_batch_owned_with_schedule_and_extra_vram, whir_open_batch,
    whir_verify_batch_with_schedule,
};
use crate::sig::{
    AggSigProfile, Digest5, SignerBitmap, SigningMode, ValidatorPublicKey, ValidatorSignature,
    compute_message_mu, validate_unique_active_committee, verify_individual_signature_with_mu,
};
use crate::sponge::{
    FiatShamirTranscript, InstanceBound, cshake256_32, encode_multi_frame, shake256_into,
};
use crate::trace::{
    COL_AUX, COL_SBOX_OUT, COL_ST_IN, ConstraintKind, GroupALineExt4, LOG_TRACE_COLS,
    NUM_TRACE_COLS, RowPublicEvalExt4, SparseBaseRowPublicEvalExt4, SparseRowPublicEvalExt4,
    StepOp, build_gamma_schedule_ext4, build_signer_program, dot_shift_state_base_ext4,
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

/// Witness size (in variables) of a full shard under the default aggregation configuration.
/// A `2^24`-entry witness commits in about 1 GiB; every extra variable doubles prover memory.
pub const DEFAULT_SHARD_PCS_NUM_VARS: usize = 24;

/// Signers per shard under the default configuration: the largest count whose witness has
/// [`DEFAULT_SHARD_PCS_NUM_VARS`] variables. Configurations may raise it to
/// [`max_shard_signers`].
pub const fn default_shard_signers(profile: AggSigProfile) -> usize {
    1usize
        << (DEFAULT_SHARD_PCS_NUM_VARS
            - LOG_TRACE_COLS
            - rows_per_signer(profile).trailing_zeros() as usize)
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
            .as_chunks::<4>()
            .0
            .iter()
            .copied()
            .map(u32::from_le_bytes)
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
// ============================================================================

/// One shard signer's public inputs to the row constraints.
#[derive(Clone, Copy)]
struct ShardSigner {
    pk: ValidatorPublicKey,
    mu: Digest5,
}

/// The per-signer step program and its constraint index, shared by every shard of a batch.
struct ShardCircuit {
    program: Vec<StepOp>,
    unique_ops: Vec<ConstraintKind>,
    step_to_uid: Vec<usize>,
    step_c0_base: Vec<Goldilocks>,
    num_signer_slots: usize,
}

impl ShardCircuit {
    fn new(profile: AggSigProfile, num_signer_slots: usize) -> Self {
        let _phase = crate::profile::span("shard_circuit_new");
        let program = build_signer_program(profile);
        let (unique_ops, step_to_uid, step_c0_base) = index_unique_program_ops(&program);
        Self {
            program,
            unique_ops,
            step_to_uid,
            step_c0_base,
            num_signer_slots,
        }
    }

    #[inline]
    fn rows_per_signer(&self) -> usize {
        self.program.len()
    }

    #[inline]
    fn log_local(&self) -> usize {
        self.rows_per_signer().trailing_zeros() as usize
    }

    #[inline]
    fn log_rows(&self) -> usize {
        self.log_local() + self.num_signer_slots.trailing_zeros() as usize
    }
}

/// The public statement of a shard batch, resolved against the committee and signing mode.
struct BatchStatement {
    shape: BatchShape,
    signers: Vec<ShardSigner>,
    signing_mode_digest: [u8; 32],
}

/// Resolve and validate the statement `(pks, profile, bitmap, shard_signer_counts, mode)`.
/// `mode` covers exactly the signers of `bitmap`, in ascending index order.
fn resolve_batch_statement(
    pks: &[ValidatorPublicKey],
    profile: AggSigProfile,
    bitmap: &SignerBitmap,
    shard_signer_counts: &[u32],
    mode: &SigningMode<'_>,
) -> Option<BatchStatement> {
    let _phase = crate::profile::span("resolve_batch_statement");
    if !validate_unique_active_committee(pks, bitmap, profile) {
        return None;
    }
    let active_indices = bitmap.active_indices();
    let shape = batch_shape(profile, shard_signer_counts, active_indices.len())?;
    let signing_mode_digest = compute_signing_mode_digest(pks, &active_indices, mode)?;
    let resolve_one = |pos: usize, val_idx: usize| -> ShardSigner {
        let pk = pks[val_idx];
        let msg: &[u8] = match mode {
            SigningMode::SharedMessage(m) => m,
            SigningMode::PerSignerMessages(ms) => ms[pos],
        };
        let (_, mu) = compute_message_mu(&pk, msg);
        ShardSigner { pk, mu }
    };

    #[cfg(feature = "std")]
    if let SigningMode::SharedMessage(shared) = mode
        && active_indices.len() >= 16
        && crate::parallel_workers() > 1
    {
        let active_pks: alloc::sync::Arc<[ValidatorPublicKey]> = active_indices
            .iter()
            .map(|&idx| pks[idx])
            .collect::<Vec<_>>()
            .into();
        let msg_arc: alloc::sync::Arc<[u8]> = (*shared).into();
        let signers = crate::pool::map_indices(active_pks.len(), 8, move |pos| {
            let pk = active_pks[pos];
            let (_, mu) = compute_message_mu(&pk, &msg_arc);
            ShardSigner { pk, mu }
        });
        return Some(BatchStatement {
            shape,
            signers,
            signing_mode_digest,
        });
    }

    let signers = active_indices
        .iter()
        .enumerate()
        .map(|(pos, &val_idx)| resolve_one(pos, val_idx))
        .collect();

    Some(BatchStatement {
        shape,
        signers,
        signing_mode_digest,
    })
}

/// Populate one shard's `num_signer_slots * rows_per_signer` trace rows (active signers first,
/// then inactive slots; every `Idle` row blinded) and flatten them into the witness table
/// `flat[u * 256 + c]`.
fn build_shard_witness(
    circuit: &ShardCircuit,
    signers: &[ShardSigner],
    sigs: &[ValidatorSignature],
    blinding_seed: &[u8; 32],
) -> Vec<Goldilocks> {
    let _phase = crate::profile::span("build_shard_witness");
    let r_rows = circuit.rows_per_signer();
    let num_signer_slots = circuit.num_signer_slots;
    let mut rows = vec![[Goldilocks::ZERO; NUM_TRACE_COLS]; num_signer_slots * r_rows];
    let fill_slot = |s: usize, slot_rows: &mut [[Goldilocks; NUM_TRACE_COLS]]| {
        match signers.get(s) {
            Some(signer) => populate_active_signer_rows(
                &circuit.program,
                &signer.pk,
                signer.mu,
                &sigs[s],
                slot_rows,
            ),
            None => populate_inactive_signer_rows(slot_rows, &[]),
        }
        blind_idle_rows_in_slot(&circuit.program, slot_rows, blinding_seed, s);
    };

    #[cfg(feature = "std")]
    if num_signer_slots >= 4 && crate::parallel_workers() > 1 {
        let workers = crate::available_worker_budget().min(num_signer_slots);
        if workers > 1 {
            let chunk_slots = num_signer_slots.div_ceil(workers);
            let fill_ref = &fill_slot;
            std::thread::scope(|scope| {
                let first_slots = chunk_slots.min(num_signer_slots);
                let (head_rows, mut rest_rows) = rows.split_at_mut(first_slots * r_rows);
                let mut base_slot = first_slots;
                let mut handles = Vec::with_capacity(workers.saturating_sub(1));
                while !rest_rows.is_empty() {
                    let rem_slots = rest_rows.len() / r_rows;
                    let take_slots = chunk_slots.min(rem_slots);
                    let (sub_rows, next_rows) = rest_rows.split_at_mut(take_slots * r_rows);
                    let start_slot = base_slot;
                    base_slot += take_slots;
                    rest_rows = next_rows;
                    handles.push(crate::spawn_bounded(scope, move || {
                        for (off, slot_rows) in sub_rows.chunks_mut(r_rows).enumerate() {
                            fill_ref(start_slot + off, slot_rows);
                        }
                    }));
                }
                for (off, slot_rows) in head_rows.chunks_mut(r_rows).enumerate() {
                    fill_ref(off, slot_rows);
                }
                for h in handles {
                    crate::join_worker(h);
                }
            });
            return rows.into_flattened();
        }
    }
    for (s, slot_rows) in rows.chunks_mut(r_rows).enumerate() {
        fill_slot(s, slot_rows);
    }
    rows.into_flattened()
}

/// Run one shard's degree-8 `GoldilocksExt4` row sumcheck over its committed witness table `flat`,
/// continuing the batch transcript. Returns the shard's proof part and its PCS claim `W(point) = v_star`.
fn prove_shard_rows(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    circuit: &ShardCircuit,
    signers: &[ShardSigner],
    flat: &[Goldilocks],
) -> (ShardRowProof, Vec<GoldilocksExt4>, GoldilocksExt4) {
    let _phase = crate::profile::span("prove_shard_rows");
    let unique_ops = &circuit.unique_ops;
    let step_to_uid = &circuit.step_to_uid;
    let r_rows = circuit.rows_per_signer();
    let num_signer_slots = circuit.num_signer_slots;
    let total_rows = num_signer_slots * r_rows;
    let log_rows = circuit.log_rows();
    let log_s = num_signer_slots.trailing_zeros() as usize;

    let tau = transcript.squeeze_ext4_vec(b"LEAF_TAU", log_rows);
    let gamma = transcript.squeeze_ext4(b"LEAF_GAMMA");
    let sched = build_gamma_schedule_ext4(unique_ops, gamma);

    // Build row-level multilinear tables for MSB-to-LSB degree-8 Sumcheck over `GoldilocksExt4`.
    let (mut eq_tau_tbl, mut eq_not_last_tbl, mut shift_tau_tbl) = build_shift_tables_ext4(&tau);

    // Base-field signer-slot public tables (`len = num_signer_slots`) for Round-0 turbo evaluation:
    let mut active_base_tbl = vec![Goldilocks::ZERO; num_signer_slots];
    let mut pk_seed_base_tbl = vec![[Goldilocks::ZERO; 4]; num_signer_slots];
    let mut pk_root_base_tbl = vec![[Goldilocks::ZERO; 4]; num_signer_slots];
    let mut mu_base_tbl = vec![[Goldilocks::ZERO; 5]; num_signer_slots];

    // `GoldilocksExt4` signer-slot public tables (`len = num_signer_slots`):
    let mut active_tbl = vec![GoldilocksExt4::ZERO; num_signer_slots];
    let mut pk_seed_tbl = vec![[GoldilocksExt4::ZERO; 4]; num_signer_slots];
    let mut pk_root_tbl = vec![[GoldilocksExt4::ZERO; 4]; num_signer_slots];
    let mut mu_tbl = vec![[GoldilocksExt4::ZERO; 5]; num_signer_slots];
    for (s, signer) in signers.iter().enumerate() {
        active_base_tbl[s] = Goldilocks::ONE;
        pk_seed_base_tbl[s] = signer.pk.pk_seed;
        pk_root_base_tbl[s] = signer.pk.pk_root;
        mu_base_tbl[s] = signer.mu;

        active_tbl[s] = GoldilocksExt4::ONE;
        pk_seed_tbl[s] = signer.pk.pk_seed.map(GoldilocksExt4::from_base);
        pk_root_tbl[s] = signer.pk.pk_root.map(GoldilocksExt4::from_base);
        mu_tbl[s] = signer.mu.map(GoldilocksExt4::from_base);
    }

    // Local-step public tables (`len = r_rows`):
    let mut is_first_tbl = vec![GoldilocksExt4::ZERO; r_rows];
    let mut is_last_tbl = vec![GoldilocksExt4::ZERO; r_rows];
    is_first_tbl[0] = GoldilocksExt4::ONE;
    is_last_tbl[r_rows - 1] = GoldilocksExt4::ONE;
    let mut step_c0_tbl: Vec<GoldilocksExt4> = circuit
        .step_c0_base
        .iter()
        .map(|&c| GoldilocksExt4::from_base(c))
        .collect();
    let mut op_sparse_tbl: Vec<Vec<(usize, GoldilocksExt4)>> = (0..r_rows)
        .map(|t| vec![(step_to_uid[t], GoldilocksExt4::ONE)])
        .collect();

    // `cols_ext4` starts empty in Round 0 (streaming directly from 8-byte base-field `flat`!)
    // and is populated at size `total_rows / 2` right after Round 0.
    let mut cols_ext4: Vec<[GoldilocksExt4; NUM_TRACE_COLS]> = Vec::new();

    let mut row_sumcheck_polys = Vec::with_capacity(log_rows);
    let mut challenges_msb_to_lsb = Vec::with_capacity(log_rows);
    let mut cur_sum_claim = GoldilocksExt4::ZERO;
    let mut cur_m = total_rows;
    let mut cur_s = num_signer_slots;
    let mut cur_r = r_rows;

    for round in 0..log_rows {
        let half = cur_m / 2;
        let folding_signer = round < log_s;
        let half_s = if folding_signer { cur_s / 2 } else { 1 };
        let half_r = if folding_signer { cur_r } else { cur_r / 2 };

        let eval_range = |start_idx: usize,
                          end_idx: usize|
         -> [GoldilocksExt4; ROW_SUMCHECK_COEFFS] {
            let mut local_sums = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
            let mut eval_cols = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
            let mut eval_cols_base = [Goldilocks::ZERO; NUM_TRACE_COLS];
            let mut op_eval_buf: Vec<(usize, GoldilocksExt4)> = Vec::new();
            let mut op_pairs: Vec<(usize, GoldilocksExt4, GoldilocksExt4)> = Vec::new();

            for idx in start_idx..end_idx {
                let idx_hi = idx + half;
                let eq0 = eq_tau_tbl[idx];
                let eq1 = eq_tau_tbl[idx_hi];
                let d_eq = eq1 - eq0;
                let nl0 = eq_not_last_tbl[idx];
                let nl1 = eq_not_last_tbl[idx_hi];
                let d_nl = nl1 - nl0;
                let sh0 = shift_tau_tbl[idx];
                let sh1 = shift_tau_tbl[idx_hi];
                let d_sh = sh1 - sh0;

                if round == 0 && folding_signer {
                    let s0 = idx / cur_r;
                    let s1 = s0 + half_s;
                    let loc = idx & (cur_r - 1);

                    let r0 = &flat[idx * NUM_TRACE_COLS..(idx + 1) * NUM_TRACE_COLS];
                    let r1 = &flat[idx_hi * NUM_TRACE_COLS..(idx_hi + 1) * NUM_TRACE_COLS];
                    let (a0, b0) = dot_shift_state_base_ext4(&sched, r0);
                    let (a1, b1) = dot_shift_state_base_ext4(&sched, r1);
                    let da = a1 - a0;
                    let db = b1 - b0;

                    let single_op_b = [(step_to_uid[loc], Goldilocks::ONE)];
                    let sc0_b = circuit.step_c0_base[loc];
                    let rf0_b = if loc == 0 {
                        Goldilocks::ONE
                    } else {
                        Goldilocks::ZERO
                    };
                    let rl0_b = if loc + 1 == cur_r {
                        Goldilocks::ONE
                    } else {
                        Goldilocks::ZERO
                    };

                    // At `round == 0, k == 0`, `r0` is a satisfied trace row (`eq_acc == 0`), so
                    // only the degree-2 inter-row shift bus contributes to `local_sums[0]`;
                    // `k == 1` is reconstructed algebraically via `sum_evals[1] = claim - sum_evals[0]`.
                    #[cfg(debug_assertions)]
                    if idx == start_idx {
                        eval_cols_base.copy_from_slice(r0);
                        debug_assert_eq!(
                            eval_eq_part_base_row_ext4(
                                unique_ops,
                                &sched,
                                &eval_cols_base,
                                &SparseBaseRowPublicEvalExt4 {
                                    active_signer: active_base_tbl[s0],
                                    pk_seed: &pk_seed_base_tbl[s0],
                                    pk_root: &pk_root_base_tbl[s0],
                                    mu: &mu_base_tbl[s0],
                                    raw_active_ops: &single_op_b,
                                    step_c0: sc0_b,
                                    is_row_first: rf0_b,
                                    is_row_last: rl0_b,
                                    eq_tau: eq0,
                                    eq_not_last: nl0,
                                    shift_tau: sh0,
                                },
                            ),
                            GoldilocksExt4::ZERO
                        );
                    }
                    local_sums[0] += nl0 * a0 - sh0 * b0;

                    let d_act_b = active_base_tbl[s1] - active_base_tbl[s0];
                    let mut cur_act_b = active_base_tbl[s1] + d_act_b;
                    let mut cur_pks_b = [Goldilocks::ZERO; 4];
                    let mut d_pks_b = [Goldilocks::ZERO; 4];
                    let mut cur_pkr_b = [Goldilocks::ZERO; 4];
                    let mut d_pkr_b = [Goldilocks::ZERO; 4];
                    for i in 0..4 {
                        let dp = pk_seed_base_tbl[s1][i] - pk_seed_base_tbl[s0][i];
                        d_pks_b[i] = dp;
                        cur_pks_b[i] = pk_seed_base_tbl[s1][i] + dp;
                        let drp = pk_root_base_tbl[s1][i] - pk_root_base_tbl[s0][i];
                        d_pkr_b[i] = drp;
                        cur_pkr_b[i] = pk_root_base_tbl[s1][i] + drp;
                    }
                    let mut cur_mu_b = [Goldilocks::ZERO; 5];
                    let mut d_mu_b = [Goldilocks::ZERO; 5];
                    for i in 0..5 {
                        let dm = mu_base_tbl[s1][i] - mu_base_tbl[s0][i];
                        d_mu_b[i] = dm;
                        cur_mu_b[i] = mu_base_tbl[s1][i] + dm;
                    }

                    let mut dr = [Goldilocks::ZERO; NUM_TRACE_COLS];
                    for c in 0..NUM_TRACE_COLS {
                        let d = r1[c] - r0[c];
                        dr[c] = d;
                        eval_cols_base[c] = r1[c] + d;
                    }

                    let mut cur_eq = eq1 + d_eq;
                    let mut cur_nl = nl1 + d_nl;
                    let mut cur_sh = sh1 + d_sh;
                    let mut cur_a = a1 + da;
                    let mut cur_b = b1 + db;

                    for (k, sum) in local_sums
                        .iter_mut()
                        .enumerate()
                        .take(ROW_SUMCHECK_COEFFS)
                        .skip(2)
                    {
                        *sum += eval_eq_part_base_row_ext4(
                            unique_ops,
                            &sched,
                            &eval_cols_base,
                            &SparseBaseRowPublicEvalExt4 {
                                active_signer: cur_act_b,
                                pk_seed: &cur_pks_b,
                                pk_root: &cur_pkr_b,
                                mu: &cur_mu_b,
                                raw_active_ops: &single_op_b,
                                step_c0: sc0_b,
                                is_row_first: rf0_b,
                                is_row_last: rl0_b,
                                eq_tau: cur_eq,
                                eq_not_last: cur_nl,
                                shift_tau: cur_sh,
                            },
                        ) + (cur_nl * cur_a - cur_sh * cur_b);
                        if k + 1 < ROW_SUMCHECK_COEFFS {
                            for c in 0..NUM_TRACE_COLS {
                                eval_cols_base[c] += dr[c];
                            }
                            cur_act_b += d_act_b;
                            for i in 0..4 {
                                cur_pks_b[i] += d_pks_b[i];
                                cur_pkr_b[i] += d_pkr_b[i];
                            }
                            for i in 0..5 {
                                cur_mu_b[i] += d_mu_b[i];
                            }
                            cur_eq += d_eq;
                            cur_nl += d_nl;
                            cur_sh += d_sh;
                            cur_a += da;
                            cur_b += db;
                        }
                    }
                    continue;
                }

                let (act0, d_act, pks0, d_pks, pkr0, d_pkr, mu0, d_mu) = if folding_signer {
                    let s0 = idx / cur_r;
                    let s1 = s0 + half_s;
                    let mut dpks = [GoldilocksExt4::ZERO; 4];
                    let mut dpkr = [GoldilocksExt4::ZERO; 4];
                    for i in 0..4 {
                        dpks[i] = pk_seed_tbl[s1][i] - pk_seed_tbl[s0][i];
                        dpkr[i] = pk_root_tbl[s1][i] - pk_root_tbl[s0][i];
                    }
                    let mut dmu = [GoldilocksExt4::ZERO; 5];
                    for i in 0..5 {
                        dmu[i] = mu_tbl[s1][i] - mu_tbl[s0][i];
                    }
                    (
                        active_tbl[s0],
                        active_tbl[s1] - active_tbl[s0],
                        pk_seed_tbl[s0],
                        dpks,
                        pk_root_tbl[s0],
                        dpkr,
                        mu_tbl[s0],
                        dmu,
                    )
                } else {
                    (
                        active_tbl[0],
                        GoldilocksExt4::ZERO,
                        pk_seed_tbl[0],
                        [GoldilocksExt4::ZERO; 4],
                        pk_root_tbl[0],
                        [GoldilocksExt4::ZERO; 4],
                        mu_tbl[0],
                        [GoldilocksExt4::ZERO; 5],
                    )
                };

                let (rf0, d_rf, rl0, d_rl, sc0, d_sc0) = if folding_signer {
                    let loc = idx & (cur_r - 1);
                    (
                        is_first_tbl[loc],
                        GoldilocksExt4::ZERO,
                        is_last_tbl[loc],
                        GoldilocksExt4::ZERO,
                        step_c0_tbl[loc],
                        GoldilocksExt4::ZERO,
                    )
                } else {
                    (
                        is_first_tbl[idx],
                        is_first_tbl[idx + half_r] - is_first_tbl[idx],
                        is_last_tbl[idx],
                        is_last_tbl[idx + half_r] - is_last_tbl[idx],
                        step_c0_tbl[idx],
                        step_c0_tbl[idx + half_r] - step_c0_tbl[idx],
                    )
                };

                let mut dc = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
                let ((a0, b0), (a1, b1)) = if round == 0 {
                    let r0 = &flat[idx * NUM_TRACE_COLS..(idx + 1) * NUM_TRACE_COLS];
                    let r1 = &flat[idx_hi * NUM_TRACE_COLS..(idx_hi + 1) * NUM_TRACE_COLS];
                    for c in 0..NUM_TRACE_COLS {
                        eval_cols[c] = GoldilocksExt4::from_base(r0[c]);
                        dc[c] = GoldilocksExt4::from_base(r1[c] - r0[c]);
                    }
                    (
                        dot_shift_state_base_ext4(&sched, r0),
                        dot_shift_state_base_ext4(&sched, r1),
                    )
                } else {
                    let c0 = &cols_ext4[idx];
                    let c1 = &cols_ext4[idx_hi];
                    eval_cols.copy_from_slice(c0);
                    for c in 0..NUM_TRACE_COLS {
                        dc[c] = c1[c] - c0[c];
                    }
                    (
                        dot_shift_state_ext4(&sched, c0),
                        dot_shift_state_ext4(&sched, c1),
                    )
                };
                let da = a1 - a0;
                let db = b1 - b0;
                let line = GroupALineExt4::new(&sched, &eval_cols, &dc);

                if folding_signer {
                    let loc = idx & (cur_r - 1);
                    let single_op = &op_sparse_tbl[loc];
                    local_sums[0] += eval_eq_part_sparse_ext4(
                        unique_ops,
                        &sched,
                        &eval_cols,
                        &SparseRowPublicEvalExt4 {
                            active_signer: act0,
                            pk_seed: &pks0,
                            pk_root: &pkr0,
                            mu: &mu0,
                            raw_active_ops: single_op,
                            step_c0: sc0,
                            is_row_first: rf0,
                            is_row_last: rl0,
                            eq_tau: eq0,
                            eq_not_last: nl0,
                            shift_tau: sh0,
                        },
                        &line.at(0),
                    ) + (nl0 * a0 - sh0 * b0);

                    for c in 0..NUM_TRACE_COLS {
                        eval_cols[c] += dc[c] + dc[c];
                    }
                    let mut cur_act = act0 + d_act + d_act;
                    let mut cur_pks = pks0;
                    let mut cur_pkr = pkr0;
                    for i in 0..4 {
                        cur_pks[i] += d_pks[i] + d_pks[i];
                        cur_pkr[i] += d_pkr[i] + d_pkr[i];
                    }
                    let mut cur_mu = mu0;
                    for i in 0..5 {
                        cur_mu[i] += d_mu[i] + d_mu[i];
                    }
                    let mut cur_eq = eq1 + d_eq;
                    let mut cur_nl = nl1 + d_nl;
                    let mut cur_sh = sh1 + d_sh;
                    let mut cur_a = a1 + da;
                    let mut cur_b = b1 + db;

                    for (k, sum) in local_sums
                        .iter_mut()
                        .enumerate()
                        .take(ROW_SUMCHECK_COEFFS)
                        .skip(2)
                    {
                        *sum += eval_eq_part_sparse_ext4(
                            unique_ops,
                            &sched,
                            &eval_cols,
                            &SparseRowPublicEvalExt4 {
                                active_signer: cur_act,
                                pk_seed: &cur_pks,
                                pk_root: &cur_pkr,
                                mu: &cur_mu,
                                raw_active_ops: single_op,
                                step_c0: sc0,
                                is_row_first: rf0,
                                is_row_last: rl0,
                                eq_tau: cur_eq,
                                eq_not_last: cur_nl,
                                shift_tau: cur_sh,
                            },
                            &line.at(k as u64),
                        ) + (cur_nl * cur_a - cur_sh * cur_b);
                        if k + 1 < ROW_SUMCHECK_COEFFS {
                            for c in 0..NUM_TRACE_COLS {
                                eval_cols[c] += dc[c];
                            }
                            cur_act += d_act;
                            for i in 0..4 {
                                cur_pks[i] += d_pks[i];
                                cur_pkr[i] += d_pkr[i];
                            }
                            for i in 0..5 {
                                cur_mu[i] += d_mu[i];
                            }
                            cur_eq += d_eq;
                            cur_nl += d_nl;
                            cur_sh += d_sh;
                            cur_a += da;
                            cur_b += db;
                        }
                    }
                } else {
                    union_sparse_op_pairs(
                        &op_sparse_tbl[idx],
                        &op_sparse_tbl[idx + half_r],
                        &mut op_pairs,
                    );
                    op_eval_buf.clear();
                    for &(uid, v0, _) in &op_pairs {
                        op_eval_buf.push((uid, v0));
                    }
                    local_sums[0] += eval_eq_part_sparse_ext4(
                        unique_ops,
                        &sched,
                        &eval_cols,
                        &SparseRowPublicEvalExt4 {
                            active_signer: act0,
                            pk_seed: &pks0,
                            pk_root: &pkr0,
                            mu: &mu0,
                            raw_active_ops: &op_eval_buf,
                            step_c0: sc0,
                            is_row_first: rf0,
                            is_row_last: rl0,
                            eq_tau: eq0,
                            eq_not_last: nl0,
                            shift_tau: sh0,
                        },
                        &line.at(0),
                    ) + (nl0 * a0 - sh0 * b0);

                    for c in 0..NUM_TRACE_COLS {
                        eval_cols[c] += dc[c] + dc[c];
                    }
                    for (slot, &(_, v0, dv)) in op_eval_buf.iter_mut().zip(op_pairs.iter()) {
                        slot.1 = v0 + dv + dv;
                    }
                    let mut cur_sc0 = sc0 + d_sc0 + d_sc0;
                    let mut cur_rf = rf0 + d_rf + d_rf;
                    let mut cur_rl = rl0 + d_rl + d_rl;
                    let mut cur_eq = eq1 + d_eq;
                    let mut cur_nl = nl1 + d_nl;
                    let mut cur_sh = sh1 + d_sh;
                    let mut cur_a = a1 + da;
                    let mut cur_b = b1 + db;

                    for (k, sum) in local_sums
                        .iter_mut()
                        .enumerate()
                        .take(ROW_SUMCHECK_COEFFS)
                        .skip(2)
                    {
                        *sum += eval_eq_part_sparse_ext4(
                            unique_ops,
                            &sched,
                            &eval_cols,
                            &SparseRowPublicEvalExt4 {
                                active_signer: act0,
                                pk_seed: &pks0,
                                pk_root: &pkr0,
                                mu: &mu0,
                                raw_active_ops: &op_eval_buf,
                                step_c0: cur_sc0,
                                is_row_first: cur_rf,
                                is_row_last: cur_rl,
                                eq_tau: cur_eq,
                                eq_not_last: cur_nl,
                                shift_tau: cur_sh,
                            },
                            &line.at(k as u64),
                        ) + (cur_nl * cur_a - cur_sh * cur_b);
                        if k + 1 < ROW_SUMCHECK_COEFFS {
                            for c in 0..NUM_TRACE_COLS {
                                eval_cols[c] += dc[c];
                            }
                            for (slot, &(_, _, dv)) in op_eval_buf.iter_mut().zip(op_pairs.iter()) {
                                slot.1 += dv;
                            }
                            cur_sc0 += d_sc0;
                            cur_rf += d_rf;
                            cur_rl += d_rl;
                            cur_eq += d_eq;
                            cur_nl += d_nl;
                            cur_sh += d_sh;
                            cur_a += da;
                            cur_b += db;
                        }
                    }
                }
            }
            local_sums
        };

        #[cfg(feature = "std")]
        let mut sum_evals = if half >= 16 {
            let sc_threads = crate::parallel_workers().min(half);
            let chunk = half / sc_threads;
            let eval_ref = &eval_range;
            let partials: Vec<[GoldilocksExt4; ROW_SUMCHECK_COEFFS]> =
                std::thread::scope(|scope| {
                    let mut handles = Vec::with_capacity(sc_threads);
                    for t_idx in 0..sc_threads {
                        let s_idx = t_idx * chunk;
                        let e_idx = if t_idx + 1 == sc_threads {
                            half
                        } else {
                            (t_idx + 1) * chunk
                        };
                        handles.push(crate::spawn_bounded(scope, move || eval_ref(s_idx, e_idx)));
                    }
                    handles.into_iter().map(crate::join_worker).collect()
                });
            let mut tot = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
            for part in partials {
                for (dst, &val) in tot.iter_mut().zip(part.iter()) {
                    *dst += val;
                }
            }
            tot
        } else {
            eval_range(0, half)
        };
        #[cfg(not(feature = "std"))]
        let mut sum_evals = eval_range(0, half);

        sum_evals[1] = cur_sum_claim - sum_evals[0];

        let poly_coeffs = interpolate_deg8_from_evals_ext4(&sum_evals);
        let wire_poly = pack_deg8_wire(&poly_coeffs);
        let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
        for (i, c) in wire_poly.iter().enumerate() {
            sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
        }
        transcript.absorb(b"LEAF_SC_POLY", &sc_bytes);
        let chal = transcript.squeeze_ext4(b"LEAF_SC_CHAL");
        cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
        row_sumcheck_polys.push(wire_poly);
        challenges_msb_to_lsb.push(chal);

        // Fold all tables at `X_{rem - 1} = chal`:
        if round == 0 {
            cols_ext4 = vec![[GoldilocksExt4::ZERO; NUM_TRACE_COLS]; half];
            #[cfg(feature = "std")]
            if half >= 64 {
                let fold_threads = crate::parallel_pow2_workers(half);
                let chunk = half / fold_threads;
                std::thread::scope(|scope| {
                    for (t_idx, sub_dst) in cols_ext4.chunks_mut(chunk).enumerate() {
                        let base_idx = t_idx * chunk;
                        crate::spawn_bounded(scope, move || {
                            for (off, dst_row) in sub_dst.iter_mut().enumerate() {
                                let idx = base_idx + off;
                                let r0 = &flat[idx * NUM_TRACE_COLS..(idx + 1) * NUM_TRACE_COLS];
                                let r1 = &flat[(idx + half) * NUM_TRACE_COLS
                                    ..(idx + half + 1) * NUM_TRACE_COLS];
                                for c in 0..NUM_TRACE_COLS {
                                    let a = r0[c];
                                    dst_row[c] =
                                        GoldilocksExt4::from_base(a) + chal.mul_base(r1[c] - a);
                                }
                            }
                        });
                    }
                });
            } else {
                for (idx, dst_row) in cols_ext4.iter_mut().enumerate() {
                    let r0 = &flat[idx * NUM_TRACE_COLS..(idx + 1) * NUM_TRACE_COLS];
                    let r1 =
                        &flat[(idx + half) * NUM_TRACE_COLS..(idx + half + 1) * NUM_TRACE_COLS];
                    for c in 0..NUM_TRACE_COLS {
                        let a = r0[c];
                        dst_row[c] = GoldilocksExt4::from_base(a) + chal.mul_base(r1[c] - a);
                    }
                }
            }
            #[cfg(not(feature = "std"))]
            for (idx, dst_row) in cols_ext4.iter_mut().enumerate() {
                let r0 = &flat[idx * NUM_TRACE_COLS..(idx + 1) * NUM_TRACE_COLS];
                let r1 = &flat[(idx + half) * NUM_TRACE_COLS..(idx + half + 1) * NUM_TRACE_COLS];
                for c in 0..NUM_TRACE_COLS {
                    let a = r0[c];
                    dst_row[c] = GoldilocksExt4::from_base(a) + chal.mul_base(r1[c] - a);
                }
            }
        } else {
            let (lo_half, hi_half) = cols_ext4.split_at_mut(half);
            #[cfg(feature = "std")]
            if half >= 64 {
                let fold_threads = crate::parallel_pow2_workers(half);
                let chunk = half / fold_threads;
                std::thread::scope(|scope| {
                    for (lo_sub, hi_sub) in
                        lo_half.chunks_mut(chunk).zip(hi_half[..half].chunks(chunk))
                    {
                        crate::spawn_bounded(scope, move || {
                            for (lo, hi) in lo_sub.iter_mut().zip(hi_sub.iter()) {
                                for c in 0..NUM_TRACE_COLS {
                                    lo[c] += chal * (hi[c] - lo[c]);
                                }
                            }
                        });
                    }
                });
            } else {
                for (lo, hi) in lo_half.iter_mut().zip(hi_half[..half].iter()) {
                    for c in 0..NUM_TRACE_COLS {
                        lo[c] += chal * (hi[c] - lo[c]);
                    }
                }
            }
            #[cfg(not(feature = "std"))]
            for (lo, hi) in lo_half.iter_mut().zip(hi_half[..half].iter()) {
                for c in 0..NUM_TRACE_COLS {
                    lo[c] += chal * (hi[c] - lo[c]);
                }
            }
            cols_ext4.truncate(half);
        }

        for idx in 0..half {
            let e0 = eq_tau_tbl[idx];
            let e1 = eq_tau_tbl[idx + half];
            eq_tau_tbl[idx] = e0 + chal * (e1 - e0);
            let n0 = eq_not_last_tbl[idx];
            let n1 = eq_not_last_tbl[idx + half];
            eq_not_last_tbl[idx] = n0 + chal * (n1 - n0);
            let s0 = shift_tau_tbl[idx];
            let s1 = shift_tau_tbl[idx + half];
            shift_tau_tbl[idx] = s0 + chal * (s1 - s0);
        }
        eq_tau_tbl.truncate(half);
        eq_not_last_tbl.truncate(half);
        shift_tau_tbl.truncate(half);

        if folding_signer {
            for s in 0..half_s {
                let a0 = active_tbl[s];
                let a1 = active_tbl[s + half_s];
                active_tbl[s] = a0 + chal * (a1 - a0);
                let p_hi = pk_seed_tbl[s + half_s];
                for (dst, &p1) in pk_seed_tbl[s].iter_mut().zip(p_hi.iter()) {
                    let p0 = *dst;
                    *dst = p0 + chal * (p1 - p0);
                }
                let r_hi = pk_root_tbl[s + half_s];
                for (dst, &r1) in pk_root_tbl[s].iter_mut().zip(r_hi.iter()) {
                    let r0 = *dst;
                    *dst = r0 + chal * (r1 - r0);
                }
                let m_hi = mu_tbl[s + half_s];
                for (dst, &m1) in mu_tbl[s].iter_mut().zip(m_hi.iter()) {
                    let m0 = *dst;
                    *dst = m0 + chal * (m1 - m0);
                }
            }
            active_tbl.truncate(half_s);
            pk_seed_tbl.truncate(half_s);
            pk_root_tbl.truncate(half_s);
            mu_tbl.truncate(half_s);
            cur_s = half_s;
        } else {
            let mut next_ops = Vec::with_capacity(half_r);
            for idx in 0..half_r {
                let f0 = is_first_tbl[idx];
                let f1 = is_first_tbl[idx + half_r];
                is_first_tbl[idx] = f0 + chal * (f1 - f0);
                let l0 = is_last_tbl[idx];
                let l1 = is_last_tbl[idx + half_r];
                is_last_tbl[idx] = l0 + chal * (l1 - l0);
                let sc0 = step_c0_tbl[idx];
                let sc1 = step_c0_tbl[idx + half_r];
                step_c0_tbl[idx] = sc0 + chal * (sc1 - sc0);
                next_ops.push(merge_sparse_op_lists(
                    &op_sparse_tbl[idx],
                    &op_sparse_tbl[idx + half_r],
                    chal,
                ));
            }
            is_first_tbl.truncate(half_r);
            is_last_tbl.truncate(half_r);
            step_c0_tbl.truncate(half_r);
            op_sparse_tbl = next_ops;
            cur_r = half_r;
        }
        cur_m = half;
    }

    debug_assert_eq!(cols_ext4.len(), 1);
    let col_evals = cols_ext4[0].to_vec();
    absorb_col_evals(transcript, &col_evals);

    // Reverse `challenges_msb_to_lsb` to standard `(X_0 .. X_{log_rows - 1})` coordinate order:
    let mut rx = challenges_msb_to_lsb;
    rx.reverse();

    // Squeeze the column challenge `r_z` (`8` `GoldilocksExt4` coords): claim is `W(r_z, r_x) = v_star`.
    let mut point = Vec::with_capacity(LOG_TRACE_COLS + log_rows);
    for _ in 0..LOG_TRACE_COLS {
        point.push(transcript.squeeze_ext4(b"LEAF_RZ"));
    }
    let v_star = mle_eval_ext4(&col_evals, &point);
    point.extend_from_slice(&rx);

    (
        ShardRowProof {
            row_sumcheck_polys,
            col_evals,
        },
        point,
        v_star,
    )
}

fn absorb_col_evals(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    col_evals: &[GoldilocksExt4],
) {
    let mut col_eval_bytes = Vec::with_capacity(col_evals.len() * 32);
    for v in col_evals {
        col_eval_bytes.extend_from_slice(&v.to_le_bytes());
    }
    transcript.absorb(b"LEAF_COL_EVALS", &col_eval_bytes);
}

/// Derive shard `shard_idx`'s `Idle`-row blinding seed from the batch seed.
fn shard_blinding_seed(batch_seed: &[u8; 32], shard_idx: usize) -> [u8; 32] {
    let mut seed_in = [0u8; 40];
    seed_in[0..32].copy_from_slice(batch_seed);
    seed_in[32..40].copy_from_slice(&(shard_idx as u64).to_le_bytes());
    cshake256_32(b"QSAG.SHARD.BLIND/v4", &seed_in)
}

/// Prove a batch of shards: the signers of `bitmap`, split in ascending order into consecutive
/// shards of `shard_signer_counts[i]` signers, each signed its message under `mode`.
///
/// `mode` and `sigs` cover exactly the signers of `bitmap`, in ascending index order. Returns
/// `None` if any individual signature fails standalone verification, if `bitmap` or `pks`
/// violate `validate_unique_active_committee`, or if the counts or `mode` lengths mismatch.
pub fn prove_shard_batch(
    pks: &[ValidatorPublicKey],
    committee_root: &[u8; 32],
    bitmap: &SignerBitmap,
    shard_signer_counts: &[u32],
    mode: &SigningMode<'_>,
    sigs: &[ValidatorSignature],
    blinding_seed: &[u8; 32],
) -> Option<ShardBatchProof> {
    let cfg =
        crate::HemAggConfig::default_for(pks.get(bitmap.first_active()?)?.profile, *blinding_seed);
    prove_shard_batch_with_config(
        pks,
        committee_root,
        bitmap,
        shard_signer_counts,
        mode,
        sigs,
        &cfg,
    )
}

pub fn prove_shard_batch_with_config(
    pks: &[ValidatorPublicKey],
    committee_root: &[u8; 32],
    bitmap: &SignerBitmap,
    shard_signer_counts: &[u32],
    mode: &SigningMode<'_>,
    sigs: &[ValidatorSignature],
    cfg: &crate::HemAggConfig,
) -> Option<ShardBatchProof> {
    // Admission precedes statement/trace allocation, including direct public API callers.
    #[cfg(feature = "std")]
    let _admission = crate::prover_admission::acquire();
    let blinding_seed = &cfg.blinding_seed;
    let first_active = bitmap.first_active()?;
    let profile = pks.get(first_active)?.profile;
    let statement = resolve_batch_statement(pks, profile, bitmap, shard_signer_counts, mode)?;
    let signers = &statement.signers;
    if sigs.len() != signers.len() {
        return None;
    }
    #[cfg(feature = "std")]
    let all_sigs_valid = if signers.len() >= 4 && crate::parallel_workers() > 1 {
        let workers = crate::available_worker_budget().min(signers.len());
        if workers > 1 {
            let chunk = signers.len().div_ceil(workers);
            let ok = core::sync::atomic::AtomicBool::new(true);
            let ok_ref = &ok;
            std::thread::scope(|scope| {
                let slices: Vec<_> = signers.chunks(chunk).zip(sigs.chunks(chunk)).collect();
                let tails: Vec<_> = slices[1..]
                    .iter()
                    .map(|&(sub_signers, sub_sigs)| {
                        crate::spawn_bounded(scope, move || {
                            for (signer, sig) in sub_signers.iter().zip(sub_sigs.iter()) {
                                if !ok_ref.load(core::sync::atomic::Ordering::Relaxed) {
                                    return;
                                }
                                if !verify_individual_signature_with_mu(&signer.pk, signer.mu, sig)
                                {
                                    ok_ref.store(false, core::sync::atomic::Ordering::Relaxed);
                                    return;
                                }
                            }
                        })
                    })
                    .collect();
                for (signer, sig) in slices[0].0.iter().zip(slices[0].1.iter()) {
                    if !ok_ref.load(core::sync::atomic::Ordering::Relaxed) {
                        break;
                    }
                    if !verify_individual_signature_with_mu(&signer.pk, signer.mu, sig) {
                        ok_ref.store(false, core::sync::atomic::Ordering::Relaxed);
                        break;
                    }
                }
                for h in tails {
                    crate::join_worker(h);
                }
            });
            ok.load(core::sync::atomic::Ordering::Relaxed)
        } else {
            signers.iter().zip(sigs.iter()).all(|(signer, sig)| {
                verify_individual_signature_with_mu(&signer.pk, signer.mu, sig)
            })
        }
    } else {
        signers
            .iter()
            .zip(sigs.iter())
            .all(|(signer, sig)| verify_individual_signature_with_mu(&signer.pk, signer.mu, sig))
    };
    #[cfg(not(feature = "std"))]
    let all_sigs_valid = signers
        .iter()
        .zip(sigs.iter())
        .all(|(signer, sig)| verify_individual_signature_with_mu(&signer.pk, signer.mu, sig));
    if !all_sigs_valid {
        return None;
    }

    // 1. Build every shard's witness table and commit them under ONE Merkle-Canopy tree.
    let circuit = ShardCircuit::new(profile, statement.shape.num_signer_slots);
    let num_vars = LOG_TRACE_COLS + circuit.log_rows();
    // Only the canonical schedule of the configured regime is ever proven or accepted.
    let schedule = cfg.regime.schedule(num_vars);
    if !schedule.validate(num_vars) {
        return None;
    }
    let mut shard_ranges = Vec::with_capacity(shard_signer_counts.len());
    let mut start = 0usize;
    for &count in shard_signer_counts {
        shard_ranges.push(start..start + count as usize);
        start += count as usize;
    }
    let build_witness = |shard_idx: usize| {
        let range = shard_ranges[shard_idx].clone();
        build_shard_witness(
            &circuit,
            &signers[range.clone()],
            &sigs[range],
            &shard_blinding_seed(blinding_seed, shard_idx),
        )
    };
    #[cfg(feature = "std")]
    let witnesses: Vec<Vec<Goldilocks>> = if shard_ranges.len() > 1 && crate::parallel_workers() > 1
    {
        std::thread::scope(|scope| {
            let build_ref = &build_witness;
            let tails: Vec<_> = (1..shard_ranges.len())
                .map(|shard_idx| crate::spawn_bounded(scope, move || build_ref(shard_idx)))
                .collect();
            let mut out = Vec::with_capacity(shard_ranges.len());
            out.push(build_ref(0));
            out.extend(tails.into_iter().map(crate::join_worker));
            out
        })
    } else {
        (0..shard_ranges.len()).map(build_witness).collect()
    };
    #[cfg(not(feature = "std"))]
    let witnesses: Vec<Vec<Goldilocks>> = (0..shard_ranges.len()).map(build_witness).collect();
    let pcs_salt_seed = cshake256_32(b"QSAG.LEAF.PCS_SALT/v4", blinding_seed);
    let shard_total_rows = circuit.num_signer_slots * circuit.rows_per_signer();
    let (witness_comm, pcs_state) = whir_commit_batch_owned_with_schedule_and_extra_vram(
        witnesses,
        &pcs_salt_seed,
        &schedule,
        shard_total_rows * NUM_TRACE_COLS,
    );

    // 2. One transcript for the whole batch: the statement and the joint commitment are bound
    //    before any shard's challenges, and every shard's messages before the batched opening.
    let mut transcript = init_shard_batch_transcript(
        profile,
        committee_root,
        bitmap,
        shard_signer_counts,
        &statement.signing_mode_digest,
        &schedule,
    );
    transcript.absorb(b"BATCH_WITNESS_COMM", &witness_comm.to_bytes());

    let mut shards = Vec::with_capacity(shard_ranges.len());
    let mut points = Vec::with_capacity(shard_ranges.len());
    let mut claims = Vec::with_capacity(shard_ranges.len());
    for (shard_idx, range) in shard_ranges.iter().enumerate() {
        transcript.absorb(b"BATCH_SHARD_INDEX", &(shard_idx as u32).to_le_bytes());
        #[cfg(feature = "vulkan")]
        let (shard, point, v_star) = prove_shard_rows_with_gpu(
            &mut transcript,
            &circuit,
            &signers[range.clone()],
            &pcs_state.hypercube_evals[shard_idx],
            pcs_state.gpu_session.as_ref(),
            shard_idx,
            shard_ranges.len(),
        );
        #[cfg(not(feature = "vulkan"))]
        let (shard, point, v_star) = prove_shard_rows(
            &mut transcript,
            &circuit,
            &signers[range.clone()],
            &pcs_state.hypercube_evals[shard_idx],
        );
        shards.push(shard);
        points.push(point);
        claims.push(v_star);
    }

    // 3. Open all shard claims with one batched `Hem` WHIR PCS proof.
    let point_refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();
    let pcs_opening = whir_open_batch(&pcs_state, &point_refs, &claims, &mut transcript);

    Some(ShardBatchProof {
        schedule,
        bitmap: bitmap.clone(),
        shard_signer_counts: shard_signer_counts.to_vec(),
        witness_comm,
        shards,
        pcs_opening,
    })
}

#[cfg(feature = "vulkan")]
fn prove_shard_rows_with_gpu(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    circuit: &ShardCircuit,
    signers: &[ShardSigner],
    flat: &[Goldilocks],
    gpu_session: Option<&crate::acceleration::GpuWhirSession>,
    shard_idx: usize,
    num_shards: usize,
) -> (ShardRowProof, Vec<GoldilocksExt4>, GoldilocksExt4) {
    if let Some(session) = gpu_session {
        let mut gpu_tr = transcript.clone();
        match prove_shard_rows_gpu(
            &mut gpu_tr,
            circuit,
            signers,
            session,
            shard_idx,
            num_shards,
        ) {
            Ok(out) => {
                *transcript = gpu_tr;
                return out;
            }
            Err(err) => session.record_fallback("prove_shard_rows", err),
        }
    }
    prove_shard_rows(transcript, circuit, signers, flat)
}

#[cfg(feature = "vulkan")]
fn push_ext4_words(dst: &mut Vec<u64>, e: GoldilocksExt4) {
    dst.extend_from_slice(&crate::pcs::ext4_to_arr(e));
}

#[cfg(feature = "vulkan")]
fn prove_shard_rows_gpu(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    circuit: &ShardCircuit,
    signers: &[ShardSigner],
    session: &crate::acceleration::GpuWhirSession,
    shard_idx: usize,
    num_shards: usize,
) -> Result<(ShardRowProof, Vec<GoldilocksExt4>, GoldilocksExt4), qsag_accel::VulkanError> {
    let _phase = crate::profile::span("prove_shard_rows_gpu");
    let unique_ops = &circuit.unique_ops;
    let step_to_uid = &circuit.step_to_uid;
    let r_rows = circuit.rows_per_signer();
    let num_signer_slots = circuit.num_signer_slots;
    let total_rows = num_signer_slots * r_rows;
    let log_rows = circuit.log_rows();
    let log_s = num_signer_slots.trailing_zeros() as usize;
    let raw = session.raw();

    let tau = transcript.squeeze_ext4_vec(b"LEAF_TAU", log_rows);
    let gamma = transcript.squeeze_ext4(b"LEAF_GAMMA");
    let sched = build_gamma_schedule_ext4(unique_ops, gamma);

    let eq_tau_tbl = build_eq_table_ext4(&tau);
    let mut shift_tables_3m = Vec::with_capacity(3 * total_rows);
    shift_tables_3m.extend(eq_tau_tbl.iter().copied().map(crate::pcs::ext4_to_arr));
    if total_rows > 0 {
        shift_tables_3m.extend(
            eq_tau_tbl[..total_rows - 1]
                .iter()
                .copied()
                .map(crate::pcs::ext4_to_arr),
        );
        shift_tables_3m.push([0u64; 4]);
        shift_tables_3m.push([0u64; 4]);
        shift_tables_3m.extend(
            eq_tau_tbl[..total_rows - 1]
                .iter()
                .copied()
                .map(crate::pcs::ext4_to_arr),
        );
    }
    drop(eq_tau_tbl);

    let op_gamma_total: usize = sched.op_gammas.iter().map(Vec::len).sum();
    let mut static_gammas_ext4 = Vec::with_capacity(250 + op_gamma_total);
    static_gammas_ext4.extend(
        sched
            .group_a_gammas
            .iter()
            .copied()
            .map(crate::pcs::ext4_to_arr),
    );
    static_gammas_ext4.extend(
        sched
            .shift_gammas
            .iter()
            .copied()
            .map(crate::pcs::ext4_to_arr),
    );
    let mut op_meta = Vec::with_capacity(unique_ops.len());
    for (uid, &kind) in unique_ops.iter().enumerate() {
        let (kind_id, kind_arg) = crate::trace::encode_constraint_kind(kind);
        let g_base = static_gammas_ext4.len() as u64;
        static_gammas_ext4.extend(
            sched.op_gammas[uid]
                .iter()
                .copied()
                .map(crate::pcs::ext4_to_arr),
        );
        op_meta.push((kind_id, kind_arg, g_base));
    }
    let id_sorted_u64_off = (static_gammas_ext4.len() * 4) as u32;
    let id_half_r = r_rows / 2;
    for base_idx in (0..id_half_r).step_by(4) {
        static_gammas_ext4.push([
            base_idx as u64,
            (base_idx + 1).min(id_half_r.saturating_sub(1)) as u64,
            (base_idx + 2).min(id_half_r.saturating_sub(1)) as u64,
            (base_idx + 3).min(id_half_r.saturating_sub(1)) as u64,
        ]);
    }
    let dyn_ext4_off = static_gammas_ext4.len() as u32;

    let witness_word_offset = (shard_idx * total_rows * NUM_TRACE_COLS) as u32;
    let cols_base_word_offset = (num_shards * total_rows * NUM_TRACE_COLS) as u32;
    raw.prover_air_init_shard(
        witness_word_offset,
        cols_base_word_offset,
        total_rows,
        &shift_tables_3m,
        &static_gammas_ext4,
    )?;

    let mut active_tbl = vec![GoldilocksExt4::ZERO; num_signer_slots];
    let mut pk_seed_tbl = vec![[GoldilocksExt4::ZERO; 4]; num_signer_slots];
    let mut pk_root_tbl = vec![[GoldilocksExt4::ZERO; 4]; num_signer_slots];
    let mut mu_tbl = vec![[GoldilocksExt4::ZERO; 5]; num_signer_slots];
    for (s, signer) in signers.iter().enumerate() {
        active_tbl[s] = GoldilocksExt4::ONE;
        pk_seed_tbl[s] = signer.pk.pk_seed.map(GoldilocksExt4::from_base);
        pk_root_tbl[s] = signer.pk.pk_root.map(GoldilocksExt4::from_base);
        mu_tbl[s] = signer.mu.map(GoldilocksExt4::from_base);
    }

    let mut is_first_tbl = vec![GoldilocksExt4::ZERO; r_rows];
    let mut is_last_tbl = vec![GoldilocksExt4::ZERO; r_rows];
    is_first_tbl[0] = GoldilocksExt4::ONE;
    is_last_tbl[r_rows - 1] = GoldilocksExt4::ONE;
    let mut step_c0_tbl: Vec<GoldilocksExt4> = circuit
        .step_c0_base
        .iter()
        .map(|&c| GoldilocksExt4::from_base(c))
        .collect();
    let mut op_sparse_tbl: Vec<Vec<(usize, GoldilocksExt4)>> = (0..r_rows)
        .map(|t| vec![(step_to_uid[t], GoldilocksExt4::ONE)])
        .collect();

    // Group local steps by `uid` once so Wave32 workgroups execute identical opcodes with 0 branch divergence.
    let mut uid_buckets: Vec<Vec<usize>> = vec![Vec::new(); unique_ops.len()];
    for (loc, &uid) in step_to_uid.iter().enumerate() {
        uid_buckets[uid].push(loc);
    }
    let steps_by_uid: Vec<usize> = uid_buckets.into_iter().flatten().collect();

    let col_pp_hi = (NUM_TRACE_COLS * (total_rows / 2)) as u32;
    let sh_pp_hi = (3 * total_rows) as u32;
    let mut col_ext4_cur = 0u32;
    let mut sh_cur = 0u32;

    let mut row_sumcheck_polys = Vec::with_capacity(log_rows);
    let mut challenges_msb_to_lsb = Vec::with_capacity(log_rows);
    let mut cur_sum_claim = GoldilocksExt4::ZERO;
    let mut cur_m = total_rows;
    let mut cur_s = num_signer_slots;
    let mut cur_r = r_rows;

    let mut dyn_words: Vec<u64> = Vec::with_capacity(total_rows / 2 + r_rows * 24);
    let mut op_hdr: Vec<[u64; 4]> = Vec::with_capacity(r_rows);
    let mut op_ent: Vec<[u64; 4]> = Vec::with_capacity(r_rows * 6);
    let mut op_pairs: Vec<(usize, GoldilocksExt4, GoldilocksExt4)> = Vec::new();

    let mut gpu_rounds_done = 0usize;
    for round in 0..log_rows {
        let half = cur_m / 2;
        let folding_signer = round < log_s;
        if round >= 1 && !folding_signer && cur_m <= 1_024 {
            break;
        }
        let half_s = if folding_signer { cur_s / 2 } else { 1 };
        let half_r = if folding_signer { cur_r } else { cur_r / 2 };
        let is_round0 = round == 0;

        dyn_words.clear();
        op_hdr.clear();
        op_ent.clear();
        let mut cur_off = dyn_ext4_off;

        let signers_off = cur_off;
        for s in 0..cur_s {
            push_ext4_words(&mut dyn_words, active_tbl[s]);
            for &v in &pk_seed_tbl[s] {
                push_ext4_words(&mut dyn_words, v);
            }
            for &v in &pk_root_tbl[s] {
                push_ext4_words(&mut dyn_words, v);
            }
            for &v in &mu_tbl[s] {
                push_ext4_words(&mut dyn_words, v);
            }
        }
        cur_off += (cur_s * 14) as u32;

        let steps_off = cur_off;
        for loc in 0..cur_r {
            push_ext4_words(&mut dyn_words, is_first_tbl[loc]);
            push_ext4_words(&mut dyn_words, is_last_tbl[loc]);
            push_ext4_words(&mut dyn_words, step_c0_tbl[loc]);
        }
        cur_off += (cur_r * 3) as u32;

        if folding_signer {
            for list in op_sparse_tbl.iter().take(cur_r) {
                let e_start = (op_ent.len() / 3) as u64;
                op_hdr.push([e_start, list.len() as u64, 0, 0]);
                for &(uid, v0) in list {
                    let (kind_id, kind_arg, g_base) = op_meta[uid];
                    op_ent.push([kind_id as u64, kind_arg as u64, g_base, 0]);
                    op_ent.push(crate::pcs::ext4_to_arr(v0));
                    op_ent.push([0u64; 4]);
                }
            }
        } else {
            for idx in 0..half_r {
                union_sparse_op_pairs(
                    &op_sparse_tbl[idx],
                    &op_sparse_tbl[idx + half_r],
                    &mut op_pairs,
                );
                let e_start = (op_ent.len() / 3) as u64;
                op_hdr.push([e_start, op_pairs.len() as u64, 0, 0]);
                for &(uid, v0, dv) in &op_pairs {
                    let (kind_id, kind_arg, g_base) = op_meta[uid];
                    op_ent.push([kind_id as u64, kind_arg as u64, g_base, 0]);
                    op_ent.push(crate::pcs::ext4_to_arr(v0));
                    op_ent.push(crate::pcs::ext4_to_arr(dv));
                }
            }
        }

        let op_hdr_off = cur_off;
        for h in &op_hdr {
            dyn_words.extend_from_slice(h);
        }
        cur_off += op_hdr.len() as u32;

        let op_ent_off = cur_off;
        for e in &op_ent {
            dyn_words.extend_from_slice(e);
        }
        cur_off += op_ent.len() as u32;

        let sorted_u64_off = if folding_signer {
            let off = cur_off * 4;
            let stride = cur_r as u64;
            for &loc in &steps_by_uid {
                let mut idx = loc as u64;
                for _ in 0..half_s {
                    dyn_words.push(idx);
                    idx += stride;
                }
            }
            off
        } else {
            id_sorted_u64_off
        };

        let col_src = if is_round0 {
            cols_base_word_offset
        } else {
            col_ext4_cur
        };
        let col_dst = if is_round0 {
            0
        } else if col_ext4_cur == 0 {
            col_pp_hi
        } else {
            0
        };
        let sh_dst = if sh_cur == 0 { sh_pp_hi } else { 0 };

        let raw8 = raw.prover_air_eval_round(
            is_round0,
            cur_m,
            cur_r,
            cur_s,
            folding_signer,
            col_src,
            sh_cur,
            dyn_ext4_off,
            &dyn_words,
            signers_off,
            steps_off,
            op_hdr_off,
            op_ent_off,
            sorted_u64_off,
        )?;

        let mut sum_evals = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
        sum_evals[0] = crate::pcs::arr_to_ext4_checked(raw8[0])?;
        for k_slot in 1..8 {
            sum_evals[k_slot + 1] = crate::pcs::arr_to_ext4_checked(raw8[k_slot])?;
        }
        sum_evals[1] = cur_sum_claim - sum_evals[0];

        let poly_coeffs = interpolate_deg8_from_evals_ext4(&sum_evals);
        let wire_poly = pack_deg8_wire(&poly_coeffs);
        let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
        for (i, c) in wire_poly.iter().enumerate() {
            sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
        }
        transcript.absorb(b"LEAF_SC_POLY", &sc_bytes);
        let chal = transcript.squeeze_ext4(b"LEAF_SC_CHAL");
        cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
        row_sumcheck_polys.push(wire_poly);
        challenges_msb_to_lsb.push(chal);

        raw.prover_air_fold_round(
            is_round0,
            cur_m,
            col_src,
            col_dst,
            sh_cur,
            sh_dst,
            crate::pcs::ext4_to_arr(chal),
        )?;
        col_ext4_cur = col_dst;
        sh_cur = sh_dst;

        if folding_signer {
            for s in 0..half_s {
                let a0 = active_tbl[s];
                let a1 = active_tbl[s + half_s];
                active_tbl[s] = a0 + chal * (a1 - a0);
                let p_hi = pk_seed_tbl[s + half_s];
                for (dst, &p1) in pk_seed_tbl[s].iter_mut().zip(p_hi.iter()) {
                    let p0 = *dst;
                    *dst = p0 + chal * (p1 - p0);
                }
                let r_hi = pk_root_tbl[s + half_s];
                for (dst, &r1) in pk_root_tbl[s].iter_mut().zip(r_hi.iter()) {
                    let r0 = *dst;
                    *dst = r0 + chal * (r1 - r0);
                }
                let m_hi = mu_tbl[s + half_s];
                for (dst, &m1) in mu_tbl[s].iter_mut().zip(m_hi.iter()) {
                    let m0 = *dst;
                    *dst = m0 + chal * (m1 - m0);
                }
            }
            active_tbl.truncate(half_s);
            pk_seed_tbl.truncate(half_s);
            pk_root_tbl.truncate(half_s);
            mu_tbl.truncate(half_s);
            cur_s = half_s;
        } else {
            let mut next_ops = Vec::with_capacity(half_r);
            for idx in 0..half_r {
                let f0 = is_first_tbl[idx];
                let f1 = is_first_tbl[idx + half_r];
                is_first_tbl[idx] = f0 + chal * (f1 - f0);
                let l0 = is_last_tbl[idx];
                let l1 = is_last_tbl[idx + half_r];
                is_last_tbl[idx] = l0 + chal * (l1 - l0);
                let sc0 = step_c0_tbl[idx];
                let sc1 = step_c0_tbl[idx + half_r];
                step_c0_tbl[idx] = sc0 + chal * (sc1 - sc0);
                next_ops.push(merge_sparse_op_lists(
                    &op_sparse_tbl[idx],
                    &op_sparse_tbl[idx + half_r],
                    chal,
                ));
            }
            is_first_tbl.truncate(half_r);
            is_last_tbl.truncate(half_r);
            step_c0_tbl.truncate(half_r);
            op_sparse_tbl = next_ops;
            cur_r = half_r;
        }
        cur_m = half;
        gpu_rounds_done = round + 1;
    }

    let mut col_evals_arr = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
    if gpu_rounds_done == log_rows {
        let mut raw_cols = [[0u64; 4]; NUM_TRACE_COLS];
        raw.prover_air_read_folded_cols(col_ext4_cur, &mut raw_cols)?;
        for (dst, raw_c) in col_evals_arr.iter_mut().zip(raw_cols) {
            *dst = crate::pcs::arr_to_ext4_checked(raw_c)?;
        }
    } else {
        debug_assert_eq!(cur_s, 1);
        debug_assert_eq!(cur_m, cur_r);
        let mut raw_cols = vec![[0u64; 4]; NUM_TRACE_COLS * cur_m];
        let mut raw_shifts = vec![[0u64; 4]; 3 * cur_m];
        raw.prover_air_read_tail(col_ext4_cur, sh_cur, &mut raw_cols, &mut raw_shifts)?;

        let mut cols_ext4 = vec![[GoldilocksExt4::ZERO; NUM_TRACE_COLS]; cur_m];
        for c in 0..NUM_TRACE_COLS {
            let c_base = c * cur_m;
            for (row_idx, row_dst) in cols_ext4.iter_mut().enumerate() {
                row_dst[c] = crate::pcs::arr_to_ext4_checked(raw_cols[c_base + row_idx])?;
            }
        }
        let mut eq_tau_tbl = Vec::with_capacity(cur_m);
        let mut eq_not_last_tbl = Vec::with_capacity(cur_m);
        let mut shift_tau_tbl = Vec::with_capacity(cur_m);
        for &w in &raw_shifts[0..cur_m] {
            eq_tau_tbl.push(crate::pcs::arr_to_ext4_checked(w)?);
        }
        for &w in &raw_shifts[cur_m..2 * cur_m] {
            eq_not_last_tbl.push(crate::pcs::arr_to_ext4_checked(w)?);
        }
        for &w in &raw_shifts[2 * cur_m..3 * cur_m] {
            shift_tau_tbl.push(crate::pcs::arr_to_ext4_checked(w)?);
        }

        let act0 = active_tbl[0];
        let pks0 = pk_seed_tbl[0];
        let pkr0 = pk_root_tbl[0];
        let mu0 = mu_tbl[0];

        for _ in gpu_rounds_done..log_rows {
            let half = cur_m / 2;
            let half_r = cur_r / 2;
            let eval_range = |start_idx: usize,
                              end_idx: usize|
             -> [GoldilocksExt4; ROW_SUMCHECK_COEFFS] {
                let mut local_sums = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
                let mut eval_cols = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
                let mut dc = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
                let mut op_pairs_loc = Vec::new();
                let mut op_eval_buf = Vec::new();

                for idx in start_idx..end_idx {
                    let idx_hi = idx + half;
                    let eq0 = eq_tau_tbl[idx];
                    let eq1 = eq_tau_tbl[idx_hi];
                    let d_eq = eq1 - eq0;
                    let nl0 = eq_not_last_tbl[idx];
                    let nl1 = eq_not_last_tbl[idx_hi];
                    let d_nl = nl1 - nl0;
                    let sh0 = shift_tau_tbl[idx];
                    let sh1 = shift_tau_tbl[idx_hi];
                    let d_sh = sh1 - sh0;

                    let rf0 = is_first_tbl[idx];
                    let d_rf = is_first_tbl[idx + half_r] - rf0;
                    let rl0 = is_last_tbl[idx];
                    let d_rl = is_last_tbl[idx + half_r] - rl0;
                    let sc0 = step_c0_tbl[idx];
                    let d_sc0 = step_c0_tbl[idx + half_r] - sc0;

                    let c0 = &cols_ext4[idx];
                    let c1 = &cols_ext4[idx_hi];
                    eval_cols.copy_from_slice(c0);
                    for c in 0..NUM_TRACE_COLS {
                        dc[c] = c1[c] - c0[c];
                    }
                    let (a0, b0) = dot_shift_state_ext4(&sched, c0);
                    let (a1, b1) = dot_shift_state_ext4(&sched, c1);
                    let da = a1 - a0;
                    let db = b1 - b0;
                    let line = GroupALineExt4::new(&sched, &eval_cols, &dc);

                    union_sparse_op_pairs(
                        &op_sparse_tbl[idx],
                        &op_sparse_tbl[idx + half_r],
                        &mut op_pairs_loc,
                    );
                    op_eval_buf.clear();
                    for &(uid, v0, _) in &op_pairs_loc {
                        op_eval_buf.push((uid, v0));
                    }
                    local_sums[0] += eval_eq_part_sparse_ext4(
                        unique_ops,
                        &sched,
                        &eval_cols,
                        &SparseRowPublicEvalExt4 {
                            active_signer: act0,
                            pk_seed: &pks0,
                            pk_root: &pkr0,
                            mu: &mu0,
                            raw_active_ops: &op_eval_buf,
                            step_c0: sc0,
                            is_row_first: rf0,
                            is_row_last: rl0,
                            eq_tau: eq0,
                            eq_not_last: nl0,
                            shift_tau: sh0,
                        },
                        &line.at(0),
                    ) + (nl0 * a0 - sh0 * b0);

                    for c in 0..NUM_TRACE_COLS {
                        eval_cols[c] += dc[c] + dc[c];
                    }
                    for (slot, &(_, v0, dv)) in op_eval_buf.iter_mut().zip(op_pairs_loc.iter()) {
                        slot.1 = v0 + dv + dv;
                    }
                    let mut cur_sc0 = sc0 + d_sc0 + d_sc0;
                    let mut cur_rf = rf0 + d_rf + d_rf;
                    let mut cur_rl = rl0 + d_rl + d_rl;
                    let mut cur_eq = eq1 + d_eq;
                    let mut cur_nl = nl1 + d_nl;
                    let mut cur_sh = sh1 + d_sh;
                    let mut cur_a = a1 + da;
                    let mut cur_b = b1 + db;

                    for (k, sum) in local_sums
                        .iter_mut()
                        .enumerate()
                        .take(ROW_SUMCHECK_COEFFS)
                        .skip(2)
                    {
                        *sum += eval_eq_part_sparse_ext4(
                            unique_ops,
                            &sched,
                            &eval_cols,
                            &SparseRowPublicEvalExt4 {
                                active_signer: act0,
                                pk_seed: &pks0,
                                pk_root: &pkr0,
                                mu: &mu0,
                                raw_active_ops: &op_eval_buf,
                                step_c0: cur_sc0,
                                is_row_first: cur_rf,
                                is_row_last: cur_rl,
                                eq_tau: cur_eq,
                                eq_not_last: cur_nl,
                                shift_tau: cur_sh,
                            },
                            &line.at(k as u64),
                        ) + (cur_nl * cur_a - cur_sh * cur_b);
                        if k + 1 < ROW_SUMCHECK_COEFFS {
                            for c in 0..NUM_TRACE_COLS {
                                eval_cols[c] += dc[c];
                            }
                            for (slot, &(_, _, dv)) in
                                op_eval_buf.iter_mut().zip(op_pairs_loc.iter())
                            {
                                slot.1 += dv;
                            }
                            cur_sc0 += d_sc0;
                            cur_rf += d_rf;
                            cur_rl += d_rl;
                            cur_eq += d_eq;
                            cur_nl += d_nl;
                            cur_sh += d_sh;
                            cur_a += da;
                            cur_b += db;
                        }
                    }
                }
                local_sums
            };

            let mut sum_evals = if half >= 16 && crate::parallel_workers() > 1 {
                let sc_threads = crate::parallel_workers().min(half);
                let chunk = half / sc_threads;
                let eval_ref = &eval_range;
                let partials: Vec<[GoldilocksExt4; ROW_SUMCHECK_COEFFS]> =
                    std::thread::scope(|scope| {
                        let mut handles = Vec::with_capacity(sc_threads);
                        for t_idx in 0..sc_threads {
                            let s_idx = t_idx * chunk;
                            let e_idx = if t_idx + 1 == sc_threads {
                                half
                            } else {
                                (t_idx + 1) * chunk
                            };
                            handles
                                .push(crate::spawn_bounded(scope, move || eval_ref(s_idx, e_idx)));
                        }
                        handles.into_iter().map(crate::join_worker).collect()
                    });
                let mut tot = [GoldilocksExt4::ZERO; ROW_SUMCHECK_COEFFS];
                for part in partials {
                    for (dst, &val) in tot.iter_mut().zip(part.iter()) {
                        *dst += val;
                    }
                }
                tot
            } else {
                eval_range(0, half)
            };
            sum_evals[1] = cur_sum_claim - sum_evals[0];

            let poly_coeffs = interpolate_deg8_from_evals_ext4(&sum_evals);
            let wire_poly = pack_deg8_wire(&poly_coeffs);
            let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
            for (i, c) in wire_poly.iter().enumerate() {
                sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
            }
            transcript.absorb(b"LEAF_SC_POLY", &sc_bytes);
            let chal = transcript.squeeze_ext4(b"LEAF_SC_CHAL");
            cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
            row_sumcheck_polys.push(wire_poly);
            challenges_msb_to_lsb.push(chal);

            let (lo_half, hi_half) = cols_ext4.split_at_mut(half);
            if half >= 64 && crate::parallel_workers() > 1 {
                let fold_threads = crate::parallel_pow2_workers(half);
                let chunk = half / fold_threads;
                std::thread::scope(|scope| {
                    for (lo_sub, hi_sub) in
                        lo_half.chunks_mut(chunk).zip(hi_half[..half].chunks(chunk))
                    {
                        crate::spawn_bounded(scope, move || {
                            for (lo, hi) in lo_sub.iter_mut().zip(hi_sub.iter()) {
                                for c in 0..NUM_TRACE_COLS {
                                    lo[c] += chal * (hi[c] - lo[c]);
                                }
                            }
                        });
                    }
                });
            } else {
                for (lo, hi) in lo_half.iter_mut().zip(hi_half[..half].iter()) {
                    for c in 0..NUM_TRACE_COLS {
                        lo[c] += chal * (hi[c] - lo[c]);
                    }
                }
            }
            cols_ext4.truncate(half);

            for idx in 0..half {
                let e0 = eq_tau_tbl[idx];
                let e1 = eq_tau_tbl[idx + half];
                eq_tau_tbl[idx] = e0 + chal * (e1 - e0);
                let n0 = eq_not_last_tbl[idx];
                let n1 = eq_not_last_tbl[idx + half];
                eq_not_last_tbl[idx] = n0 + chal * (n1 - n0);
                let s0 = shift_tau_tbl[idx];
                let s1 = shift_tau_tbl[idx + half];
                shift_tau_tbl[idx] = s0 + chal * (s1 - s0);
            }
            eq_tau_tbl.truncate(half);
            eq_not_last_tbl.truncate(half);
            shift_tau_tbl.truncate(half);

            let mut next_ops = Vec::with_capacity(half_r);
            for idx in 0..half_r {
                let f0 = is_first_tbl[idx];
                let f1 = is_first_tbl[idx + half_r];
                is_first_tbl[idx] = f0 + chal * (f1 - f0);
                let l0 = is_last_tbl[idx];
                let l1 = is_last_tbl[idx + half_r];
                is_last_tbl[idx] = l0 + chal * (l1 - l0);
                let sc0 = step_c0_tbl[idx];
                let sc1 = step_c0_tbl[idx + half_r];
                step_c0_tbl[idx] = sc0 + chal * (sc1 - sc0);
                next_ops.push(merge_sparse_op_lists(
                    &op_sparse_tbl[idx],
                    &op_sparse_tbl[idx + half_r],
                    chal,
                ));
            }
            is_first_tbl.truncate(half_r);
            is_last_tbl.truncate(half_r);
            step_c0_tbl.truncate(half_r);
            op_sparse_tbl = next_ops;
            cur_r = half_r;
            cur_m = half;
        }
        col_evals_arr = cols_ext4[0];
    }

    // Prover-side algebraic self-check before committing transcript or V5 receipt:
    let mut rx = challenges_msb_to_lsb;
    rx.reverse();
    let eq_tau_rx = eq_poly_ext4(&tau, &rx);
    let eq_nl_rx = eval_eq_not_last_ext4(&tau, &rx);
    let shift_rx = eval_shift_kernel_ext4(&tau, &rx);
    let mut gated_op_sels = vec![GoldilocksExt4::ZERO; unique_ops.len()];
    for &(uid, v) in &op_sparse_tbl[0] {
        gated_op_sels[uid] = active_tbl[0] * v;
    }
    let expected_terminal = eval_batched_row_constraints_ext4(
        unique_ops,
        &col_evals_arr,
        &RowPublicEvalExt4 {
            active_signer: active_tbl[0],
            pk_seed: pk_seed_tbl[0],
            pk_root: pk_root_tbl[0],
            mu: mu_tbl[0],
            gated_op_sels: &gated_op_sels,
            step_c0: step_c0_tbl[0],
            is_row_first: is_first_tbl[0],
            is_row_last: is_last_tbl[0],
            eq_tau: eq_tau_rx,
            eq_not_last: eq_nl_rx,
            shift_tau: shift_rx,
        },
        gamma,
    );
    if cur_sum_claim != expected_terminal {
        return Err(qsag_accel::VulkanError::WorkspacePoisoned);
    }

    let col_evals = col_evals_arr.to_vec();
    let mut col_eval_bytes = Vec::with_capacity(col_evals.len() * 32);
    for v in &col_evals {
        col_eval_bytes.extend_from_slice(&v.to_le_bytes());
    }
    if !session.record_stage(qsag_accel::ProverKernelSlot::AirRowGroupB) {
        return Err(qsag_accel::VulkanError::WorkspacePoisoned);
    }
    transcript.absorb(b"LEAF_COL_EVALS", &col_eval_bytes);

    let mut point = Vec::with_capacity(LOG_TRACE_COLS + log_rows);
    for _ in 0..LOG_TRACE_COLS {
        point.push(transcript.squeeze_ext4(b"LEAF_RZ"));
    }
    let v_star = mle_eval_ext4(&col_evals, &point);
    point.extend_from_slice(&rx);

    Ok((
        ShardRowProof {
            row_sumcheck_polys,
            col_evals,
        },
        point,
        v_star,
    ))
}

/// Replay one shard's `GoldilocksExt4` row sumcheck and enforce its terminal evaluation check
/// against the shard's public inputs. Returns the shard's PCS claim `(point, v_star)`.
fn verify_shard_rows(
    transcript: &mut FiatShamirTranscript<InstanceBound>,
    circuit: &ShardCircuit,
    signers: &[ShardSigner],
    proof: &ShardRowProof,
) -> Option<(Vec<GoldilocksExt4>, GoldilocksExt4)> {
    let _phase = crate::profile::span("verify_shard_rows");
    let r_rows = circuit.rows_per_signer();
    let log_rows = circuit.log_rows();
    let log_r = circuit.log_local();
    if proof.row_sumcheck_polys.len() != log_rows || proof.col_evals.len() != NUM_TRACE_COLS {
        return None;
    }

    let tau = transcript.squeeze_ext4_vec(b"LEAF_TAU", log_rows);
    let gamma = transcript.squeeze_ext4(b"LEAF_GAMMA");

    // 1. Verify all `log_rows` rounds of degree-8 Row Sumcheck starting from `cur_sum_claim = 0`!
    //    `unpack_deg8_wire` reconstructs `c_1 = cur_sum_claim - 2*c_0 - sum_{k=2}^8 c_k`,
    //    algebraically enforcing `P(0) + P(1) == cur_sum_claim` at every round.
    let mut cur_sum_claim = GoldilocksExt4::ZERO;
    let mut challenges_msb_to_lsb = Vec::with_capacity(log_rows);

    for wire_poly in &proof.row_sumcheck_polys {
        let mut sc_bytes = [0u8; ROW_SUMCHECK_WIRE_COEFFS * 32];
        for (i, c) in wire_poly.iter().enumerate() {
            sc_bytes[32 * i..32 * (i + 1)].copy_from_slice(&c.to_le_bytes());
        }
        transcript.absorb(b"LEAF_SC_POLY", &sc_bytes);
        let poly_coeffs = unpack_deg8_wire(wire_poly, cur_sum_claim);
        let chal = transcript.squeeze_ext4(b"LEAF_SC_CHAL");
        cur_sum_claim = eval_univariate_ext4(&poly_coeffs, chal);
        challenges_msb_to_lsb.push(chal);
    }

    absorb_col_evals(transcript, &proof.col_evals);

    let mut rx = challenges_msb_to_lsb;
    rx.reverse();
    let r_local = &rx[0..log_r];
    let r_signer = &rx[log_r..log_rows];

    // 2. Evaluate all public multilinear inputs at `r_x = (r_local, r_signer)` and ENFORCE
    //    THE MANDATORY TERMINAL SUMCHECK EVALUATION CHECK!
    let eq_local = build_eq_table_ext4(r_local);
    let is_row_first = eq_local[0];
    let is_row_last = eq_local[r_rows - 1];
    let mut step_c0 = GoldilocksExt4::ZERO;
    let mut raw_op_sels = vec![GoldilocksExt4::ZERO; circuit.unique_ops.len()];
    for (t, &w) in eq_local.iter().enumerate() {
        raw_op_sels[circuit.step_to_uid[t]] += w;
        step_c0 += w.mul_base(circuit.step_c0_base[t]);
    }

    let eq_signer = build_eq_table_ext4(r_signer);
    let mut active_signer = GoldilocksExt4::ZERO;
    let mut pk_seed = [GoldilocksExt4::ZERO; 4];
    let mut pk_root = [GoldilocksExt4::ZERO; 4];
    let mut mu = [GoldilocksExt4::ZERO; 5];

    for (signer, &w) in signers.iter().zip(&eq_signer) {
        active_signer += w;
        for i in 0..4 {
            pk_seed[i] += w.mul_base(signer.pk.pk_seed[i]);
            pk_root[i] += w.mul_base(signer.pk.pk_root[i]);
        }
        for (acc, &limb) in mu.iter_mut().zip(&signer.mu) {
            *acc += w.mul_base(limb);
        }
    }

    let gated_op_sels: Vec<GoldilocksExt4> =
        raw_op_sels.into_iter().map(|s| active_signer * s).collect();
    let pub_eval = RowPublicEvalExt4 {
        active_signer,
        pk_seed,
        pk_root,
        mu,
        step_c0,
        gated_op_sels: &gated_op_sels,
        is_row_first,
        is_row_last,
        eq_tau: eq_poly_ext4(&tau, &rx),
        eq_not_last: eval_eq_not_last_ext4(&tau, &rx),
        shift_tau: eval_shift_kernel_ext4(&tau, &rx),
    };

    let mut cols_arr = [GoldilocksExt4::ZERO; NUM_TRACE_COLS];
    cols_arr.copy_from_slice(&proof.col_evals);

    // CRITICAL TERMINAL SUMCHECK CHECK (`cur_sum_claim == committed_mle_eval` constraint polynomial):
    let expected_terminal_val =
        eval_batched_row_constraints_ext4(&circuit.unique_ops, &cols_arr, &pub_eval, gamma);
    if !qsag_whir_verified::verify_ood_pin_eq(
        &expected_terminal_val
            .to_limbs()
            .map(Goldilocks::to_canonical_u64),
        &cur_sum_claim.to_limbs().map(Goldilocks::to_canonical_u64),
    ) {
        return None;
    }

    // 3. Squeeze `r_z`: the shard's PCS claim is `W(r_z, r_x) = v_star`.
    let mut point = Vec::with_capacity(LOG_TRACE_COLS + log_rows);
    for _ in 0..LOG_TRACE_COLS {
        point.push(transcript.squeeze_ext4(b"LEAF_RZ"));
    }
    let v_star = mle_eval_ext4(&proof.col_evals, &point);
    point.extend_from_slice(&rx);
    Some((point, v_star))
}

/// Verify a `ShardBatchProof` without ever seeing any raw signature: statement binding, every
/// shard's degree-8 `GoldilocksExt4` row sumcheck and **terminal sumcheck evaluation check**, and
/// the single batched `Hem` WHIR opening of all shard claims against the joint commitment.
///
/// `mode` covers exactly the signers of `proof.bitmap`, in ascending index order.
///
/// The proof must use the default Johnson QROM schedule. Use
/// [`verify_shard_batch_with_regime`] to select another QROM-128 regime explicitly.
pub fn verify_shard_batch(
    pks: &[ValidatorPublicKey],
    committee_root: &[u8; 32],
    profile: AggSigProfile,
    mode: &SigningMode<'_>,
    proof: &ShardBatchProof,
) -> bool {
    verify_shard_batch_with_regime(
        pks,
        committee_root,
        profile,
        mode,
        proof,
        WhirSecurityRegime::default(),
    )
}

/// [`verify_shard_batch`] under exactly `expected_regime`: the proof's schedule must equal
/// `expected_regime.schedule(num_vars)`, the canonical stage geometry and query budget that
/// the finite Theorem 4.8 witnesses cover. No other validated schedule is accepted, so a
/// weaker regime or a hand-tuned blowup/fold ladder cannot be substituted.
pub fn verify_shard_batch_with_regime(
    pks: &[ValidatorPublicKey],
    committee_root: &[u8; 32],
    profile: AggSigProfile,
    mode: &SigningMode<'_>,
    proof: &ShardBatchProof,
    expected_regime: WhirSecurityRegime,
) -> bool {
    let _phase = crate::profile::span("verify_shard_batch");
    let Some(statement) = resolve_batch_statement(
        pks,
        profile,
        &proof.bitmap,
        &proof.shard_signer_counts,
        mode,
    ) else {
        return false;
    };
    if proof.shards.len() != proof.shard_signer_counts.len() {
        return false;
    }
    let circuit = ShardCircuit::new(profile, statement.shape.num_signer_slots);

    let schedule = &proof.schedule;
    let num_vars = LOG_TRACE_COLS + circuit.log_rows();
    let expected_schedule = expected_regime.schedule(num_vars);
    if !expected_regime.meets_qrom_128_floor()
        || *schedule != expected_schedule
        || !schedule.validate(num_vars)
        || !schedule.is_canonical(num_vars)
    {
        return false;
    }
    let mut transcript = init_shard_batch_transcript(
        profile,
        committee_root,
        &proof.bitmap,
        &proof.shard_signer_counts,
        &statement.signing_mode_digest,
        schedule,
    );
    transcript.absorb(b"BATCH_WITNESS_COMM", &proof.witness_comm.to_bytes());

    let mut points = Vec::with_capacity(proof.shards.len());
    let mut claims = Vec::with_capacity(proof.shards.len());
    let mut start = 0usize;
    for (shard_idx, (shard, &count)) in proof
        .shards
        .iter()
        .zip(&proof.shard_signer_counts)
        .enumerate()
    {
        let end = start + count as usize;
        transcript.absorb(b"BATCH_SHARD_INDEX", &(shard_idx as u32).to_le_bytes());
        let Some((point, v_star)) = verify_shard_rows(
            &mut transcript,
            &circuit,
            &statement.signers[start..end],
            shard,
        ) else {
            return false;
        };
        points.push(point);
        claims.push(v_star);
        start = end;
    }

    let point_refs: Vec<&[GoldilocksExt4]> = points.iter().map(Vec::as_slice).collect();
    whir_verify_batch_with_schedule(
        &proof.witness_comm,
        num_vars,
        &point_refs,
        &claims,
        &proof.pcs_opening,
        &mut transcript,
        schedule,
    )
}
