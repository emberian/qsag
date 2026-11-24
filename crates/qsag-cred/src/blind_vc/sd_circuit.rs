use super::*;

// ============================================================================
// Plaintext & Single-Party Additive-Share Selective-Disclosure Circuit Engines
// ============================================================================

pub(super) struct SdPlaintextCircuitTrace {
    pub(super) x: SecretBuffer<Vec<u64>>,
    pub(super) y: SecretBuffer<Vec<u64>>,
    pub(super) z: SecretBuffer<Vec<u64>>,
    pub(super) final_outs: [u64; VC_FINAL_OUTPUTS],
}

pub(super) struct PlaintextGateRecorder {
    pub(super) x: Vec<u64>,
    pub(super) y: Vec<u64>,
    pub(super) z: Vec<u64>,
}

impl PlaintextGateRecorder {
    pub(super) fn new() -> Self {
        Self {
            x: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
            y: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
            z: Vec::with_capacity(SD_GRID_B * SD_GRID_L),
        }
    }

    #[inline]
    fn mul_gate(&mut self, xv: u64, yv: u64) -> u64 {
        let zv = gl_mul(xv, yv);
        self.x.push(xv);
        self.y.push(yv);
        self.z.push(zv);
        zv
    }

    #[inline]
    fn sbox7(&mut self, xv: u64) -> u64 {
        let x2 = self.mul_gate(xv, xv);
        let x3 = self.mul_gate(x2, xv);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    pub(super) fn perm12(&mut self, message: &mut [u64]) {
        let mut state = [0u64; 12];
        for chunk in message.chunks(6) {
            for (wire, &value) in state.iter_mut().zip(chunk) {
                *wire = gl_add(*wire, value);
            }
            if chunk.len() < 6 {
                state[chunk.len()] = gl_add(state[chunk.len()], 1);
            }
            self.raw_perm12(&mut state);
        }
        if message.len().is_multiple_of(6) {
            state[0] = gl_add(state[0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state);
        ct_zeroize_u64s(&mut state);
    }

    pub(super) fn raw_perm12(&mut self, st: &mut [u64; 12]) {
        poseidon2_apply_me(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = gl_add(*wire, poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            poseidon2_apply_me(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0] = gl_add(st[0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            poseidon2_apply_mi(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = gl_add(*wire, poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            poseidon2_apply_me(st);
        }
    }
}

pub(super) fn eval_sd_plaintext_circuit(
    arity: usize,
    issuer_epoch: u64,
    schema_id: u64,
    verifier_scope_limbs: &[u64; 4],
    disclosed_attrs: &[(usize, u64)],
    expected_final_outs: &[u64; VC_FINAL_OUTPUTS],
    secret_vals: &[u64],
) -> SdPlaintextCircuitTrace {
    let mut rec = PlaintextGateRecorder::new();
    let mut cursor = 0usize;

    let mut attr_wires = SecretBuffer([0u64; MAX_VC_ATTRS]);
    for (i, slot_w) in attr_wires.iter_mut().enumerate() {
        if i >= arity {
            *slot_w = 0;
        } else if let Some(&(_, pub_val)) = disclosed_attrs.iter().find(|&&(idx, _)| idx == i) {
            *slot_w = pub_val;
        } else {
            *slot_w = secret_vals[cursor];
            cursor += 1;
        }
    }
    let hb_wires: SecretBuffer<[u64; 4]> = SecretBuffer(core::array::from_fn(|_| {
        let v = secret_vals[cursor];
        cursor += 1;
        v
    }));
    let pb_wires: SecretBuffer<[u64; 4]> = SecretBuffer(core::array::from_fn(|_| {
        let v = secret_vals[cursor];
        cursor += 1;
        v
    }));
    let bit_wires: SecretBuffer<[u64; VC_ACCUMULATOR_DEPTH]> =
        SecretBuffer(core::array::from_fn(|_| {
            let v = secret_vals[cursor];
            cursor += 1;
            v
        }));
    let sib_wires: SecretBuffer<[[u64; 6]; VC_ACCUMULATOR_DEPTH]> =
        SecretBuffer(core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                let v = secret_vals[cursor];
                cursor += 1;
                v
            })
        }));
    debug_assert_eq!(cursor, secret_vals.len());

    // Sized once: growing a `to_vec` copy would leave the wires in freed heap blocks.
    let mut st_attr = SecretBuffer(Vec::with_capacity(arity.max(6) + 7));
    st_attr.extend_from_slice(&attr_wires[..arity.max(6)]);
    st_attr.extend_from_slice(&hb_wires[..]);
    st_attr.extend_from_slice(&[
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
        arity as u64,
    ]);
    rec.perm12(&mut st_attr);
    let mut cur_node = SecretBuffer(core::array::from_fn::<u64, 6, _>(|j| st_attr[j]));
    ct_zeroize_u64s(&mut st_attr);

    let mut bool_zeros = SecretBuffer([0u64; VC_ACCUMULATOR_DEPTH]);
    for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(bit_wires.iter()).enumerate() {
        let one_minus_b = gl_sub(1, b);
        *zero = rec.mul_gate(b, one_minus_b);

        let mut left = SecretBuffer([0u64; 6]);
        let mut right = SecretBuffer([0u64; 6]);
        for (j, (left_slot, right_slot)) in left.iter_mut().zip(right.iter_mut()).enumerate() {
            let sib_j = sib_wires[lvl][j];
            let diff = gl_sub(sib_j, cur_node[j]);
            let delta = rec.mul_gate(b, diff);
            *left_slot = gl_add(cur_node[j], delta);
            *right_slot = gl_sub(sib_j, delta);
        }

        let mut st_mk = SecretBuffer([
            left[0],
            left[1],
            left[2],
            left[3],
            left[4],
            left[5],
            right[0],
            right[1],
            right[2],
            right[3],
            right[4],
            right[5],
            issuer_epoch & 0xffff_ffff,
            lvl as u64,
            gl_reduce_u64(VC_MERKLE_NODE_TAG),
            gl_add(issuer_epoch >> 32, gl_reduce_u64(POSEIDON2_CONST_IV)),
        ]);
        rec.perm12(&mut st_mk[..]);
        *cur_node = core::array::from_fn(|j| st_mk[j]);
    }

    // Sized once: growing a `to_vec` copy would leave the wires in freed heap blocks.
    let mut st_pres = SecretBuffer(Vec::with_capacity(arity.max(6) + 7));
    st_pres.extend_from_slice(&attr_wires[..arity.max(6)]);
    st_pres.extend_from_slice(&pb_wires[..]);
    st_pres.extend_from_slice(&[
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG)),
        arity as u64,
    ]);
    rec.perm12(&mut st_pres);

    let mut st_sc = SecretBuffer([
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        verifier_scope_limbs[0],
        verifier_scope_limbs[1],
        verifier_scope_limbs[2],
        verifier_scope_limbs[3],
        0,
        0,
        schema_id & 0xffff_ffff,
        gl_add(schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM)),
    ]);
    rec.perm12(&mut st_sc[..]);
    debug_assert_eq!(
        rec.x.len(),
        SD_TOTAL_GATES
            - 2 * (attribute_commitment_gates(MAX_VC_ATTRS)
                - attribute_commitment_gates(arity.max(6)))
    );
    rec.x.resize(SD_TOTAL_GATES, 0);
    rec.y.resize(SD_TOTAL_GATES, 0);
    rec.z.resize(SD_TOTAL_GATES, 0);

    let mut final_outs = [0u64; VC_FINAL_OUTPUTS];
    final_outs[0..6].copy_from_slice(&cur_node[..]);
    final_outs[6..12].copy_from_slice(&st_pres[0..6]);
    final_outs[12..18].copy_from_slice(&st_sc[0..6]);
    final_outs[18..VC_FINAL_OUTPUTS].copy_from_slice(&bool_zeros[..]);
    ct_zeroize_u64s(&mut st_pres);

    debug_assert_eq!(&final_outs, expected_final_outs);

    // Append 38 public output-wire consistency gates `1 * final_outs[j] = expected_final_outs[j]`,
    // then pad to `SD_GRID_B * SD_GRID_L = 36,864` with `0 * 0 = 0`.
    for j in 0..VC_FINAL_OUTPUTS {
        rec.x.push(1);
        rec.y.push(final_outs[j]);
        rec.z.push(expected_final_outs[j]);
    }
    rec.x.resize(SD_GRID_B * SD_GRID_L, 0);
    rec.y.resize(SD_GRID_B * SD_GRID_L, 0);
    rec.z.resize(SD_GRID_B * SD_GRID_L, 0);

    SdPlaintextCircuitTrace {
        x: SecretBuffer(rec.x),
        y: SecretBuffer(rec.y),
        z: SecretBuffer(rec.z),
        final_outs,
    }
}

pub(super) struct LinearShareEvaluator<'a> {
    pub(super) is_party_zero: bool,
    pub(super) z_shares: &'a [u64],
    pub(super) gate_cursor: usize,
    pub(super) x_out: &'a mut [u64],
    pub(super) y_out: &'a mut [u64],
    pub(super) z_out: &'a mut [u64],
}

impl<'a> LinearShareEvaluator<'a> {
    #[inline]
    fn const_share(&self, c: u64) -> u64 {
        if self.is_party_zero { c } else { 0 }
    }

    #[inline]
    fn add_const(&self, x: u64, c: u64) -> u64 {
        if self.is_party_zero { gl_add(x, c) } else { x }
    }

    #[inline]
    fn mul_gate(&mut self, x: u64, y: u64) -> u64 {
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let z = self.z_shares[g];
        self.x_out[g] = x;
        self.y_out[g] = y;
        self.z_out[g] = z;
        z
    }

    #[inline]
    fn sbox7(&mut self, x: u64) -> u64 {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    pub(super) fn perm12(&mut self, message: &mut [u64]) {
        let mut state = SecretBuffer([0u64; 12]);
        for chunk in message.chunks(6) {
            for (wire, &value) in state.iter_mut().zip(chunk) {
                *wire = gl_add(*wire, value);
            }
            if chunk.len() < 6 {
                state[chunk.len()] = self.add_const(state[chunk.len()], 1);
            }
            self.raw_perm12(&mut state);
        }
        if message.len().is_multiple_of(6) {
            state[0] = self.add_const(state[0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state[..]);
    }

    pub(super) fn raw_perm12(&mut self, st: &mut [u64; 12]) {
        poseidon2_apply_me(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            if self.is_party_zero {
                for (lane, wire) in st.iter_mut().enumerate() {
                    *wire = gl_add(*wire, poseidon2_const_at(0, r, lane as u64));
                    *wire = self.sbox7(*wire);
                }
            } else {
                for wire in st.iter_mut() {
                    *wire = self.sbox7(*wire);
                }
            }
            poseidon2_apply_me(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            if self.is_party_zero {
                st[0] = gl_add(st[0], poseidon2_const_at(1, r, 0));
            }
            st[0] = self.sbox7(st[0]);
            poseidon2_apply_mi(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            if self.is_party_zero {
                for (lane, wire) in st.iter_mut().enumerate() {
                    *wire = gl_add(*wire, poseidon2_const_at(2, r, lane as u64));
                    *wire = self.sbox7(*wire);
                }
            } else {
                for wire in st.iter_mut() {
                    *wire = self.sbox7(*wire);
                }
            }
            poseidon2_apply_me(st);
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Explicit selective-disclosure statement and per-party additive wire share slices"
)]
pub(super) fn eval_sd_party_shares(
    party: usize,
    arity: usize,
    issuer_epoch: u64,
    schema_id: u64,
    verifier_scope_limbs: &[u64; 4],
    disclosed_attrs: &[(usize, u64)],
    expected_final_outs: &[u64; VC_FINAL_OUTPUTS],
    w_shares: &[u64],
    z_shares: &[u64],
    x_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
    y_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
    z_grid: &mut [u64; SD_GRID_B * SD_GRID_L],
) {
    let mut ev = LinearShareEvaluator {
        is_party_zero: party == 0,
        z_shares,
        gate_cursor: 0,
        x_out: x_grid,
        y_out: y_grid,
        z_out: z_grid,
    };

    let mut cursor = 0usize;
    let mut attr_wires = SecretBuffer([0u64; MAX_VC_ATTRS]);
    for (i, slot_w) in attr_wires.iter_mut().enumerate() {
        if i >= arity {
            *slot_w = 0;
        } else if let Some(&(_, pub_val)) = disclosed_attrs.iter().find(|&&(idx, _)| idx == i) {
            *slot_w = ev.const_share(pub_val);
        } else {
            *slot_w = w_shares[cursor];
            cursor += 1;
        }
    }
    let hb_wires: SecretBuffer<[u64; 4]> = SecretBuffer(core::array::from_fn(|_| {
        let v = w_shares[cursor];
        cursor += 1;
        v
    }));
    let pb_wires: SecretBuffer<[u64; 4]> = SecretBuffer(core::array::from_fn(|_| {
        let v = w_shares[cursor];
        cursor += 1;
        v
    }));
    let bit_wires: SecretBuffer<[u64; VC_ACCUMULATOR_DEPTH]> =
        SecretBuffer(core::array::from_fn(|_| {
            let v = w_shares[cursor];
            cursor += 1;
            v
        }));
    let sib_wires: SecretBuffer<[[u64; 6]; VC_ACCUMULATOR_DEPTH]> =
        SecretBuffer(core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                let v = w_shares[cursor];
                cursor += 1;
                v
            })
        }));
    debug_assert_eq!(cursor, w_shares.len());

    // Sized once: growing a `to_vec` copy would leave the wires in freed heap blocks.
    let mut st_attr = SecretBuffer(Vec::with_capacity(arity.max(6) + 7));
    st_attr.extend_from_slice(&attr_wires[..arity.max(6)]);
    st_attr.extend_from_slice(&hb_wires[..]);
    st_attr.extend_from_slice(&[
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG))),
        ev.const_share(arity as u64),
    ]);
    ev.perm12(&mut st_attr);
    let mut cur_node = SecretBuffer(core::array::from_fn::<u64, 6, _>(|j| st_attr[j]));

    let mut bool_zeros = SecretBuffer([0u64; VC_ACCUMULATOR_DEPTH]);
    for (lvl, (zero, &b)) in bool_zeros.iter_mut().zip(bit_wires.iter()).enumerate() {
        let one_share = ev.const_share(1);
        let one_minus_b = gl_sub(one_share, b);
        *zero = ev.mul_gate(b, one_minus_b);

        let mut left = SecretBuffer([0u64; 6]);
        let mut right = SecretBuffer([0u64; 6]);
        for (j, (left_slot, right_slot)) in left.iter_mut().zip(right.iter_mut()).enumerate() {
            let sib_j = sib_wires[lvl][j];
            let diff = gl_sub(sib_j, cur_node[j]);
            let delta = ev.mul_gate(b, diff);
            *left_slot = gl_add(cur_node[j], delta);
            *right_slot = gl_sub(sib_j, delta);
        }

        let mut st_mk = SecretBuffer([
            left[0],
            left[1],
            left[2],
            left[3],
            left[4],
            left[5],
            right[0],
            right[1],
            right[2],
            right[3],
            right[4],
            right[5],
            ev.const_share(issuer_epoch & 0xffff_ffff),
            ev.const_share(lvl as u64),
            ev.const_share(gl_reduce_u64(VC_MERKLE_NODE_TAG)),
            ev.const_share(gl_add(
                issuer_epoch >> 32,
                gl_reduce_u64(POSEIDON2_CONST_IV),
            )),
        ]);
        ev.perm12(&mut st_mk[..]);
        *cur_node = core::array::from_fn(|j| st_mk[j]);
    }

    // Sized once: growing a `to_vec` copy would leave the wires in freed heap blocks.
    let mut st_pres = SecretBuffer(Vec::with_capacity(arity.max(6) + 7));
    st_pres.extend_from_slice(&attr_wires[..arity.max(6)]);
    st_pres.extend_from_slice(&pb_wires[..]);
    st_pres.extend_from_slice(&[
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_PRES_COMMIT_TAG))),
        ev.const_share(arity as u64),
    ]);
    ev.perm12(&mut st_pres);

    let mut st_sc = SecretBuffer([
        hb_wires[0],
        hb_wires[1],
        hb_wires[2],
        hb_wires[3],
        ev.const_share(verifier_scope_limbs[0]),
        ev.const_share(verifier_scope_limbs[1]),
        ev.const_share(verifier_scope_limbs[2]),
        ev.const_share(verifier_scope_limbs[3]),
        0,
        0,
        ev.const_share(schema_id & 0xffff_ffff),
        ev.const_share(gl_add(schema_id >> 32, gl_reduce_u64(VC_SCOPE_TAG_DOM))),
    ]);
    ev.perm12(&mut st_sc[..]);
    debug_assert_eq!(
        ev.gate_cursor,
        SD_TOTAL_GATES
            - 2 * (attribute_commitment_gates(MAX_VC_ATTRS)
                - attribute_commitment_gates(arity.max(6)))
    );
    for (g, &z) in z_shares
        .iter()
        .enumerate()
        .take(SD_TOTAL_GATES)
        .skip(ev.gate_cursor)
    {
        ev.x_out[g] = 0;
        ev.y_out[g] = 0;
        ev.z_out[g] = z;
    }

    let mut final_outs = SecretBuffer([0u64; VC_FINAL_OUTPUTS]);
    final_outs[0..6].copy_from_slice(&cur_node[..]);
    final_outs[6..12].copy_from_slice(&st_pres[0..6]);
    final_outs[12..18].copy_from_slice(&st_sc[0..6]);
    final_outs[18..VC_FINAL_OUTPUTS].copy_from_slice(&bool_zeros[..]);

    let one_const = if party == 0 { 1 } else { 0 };
    for j in 0..VC_FINAL_OUTPUTS {
        let g = SD_TOTAL_GATES + j;
        x_grid[g] = one_const;
        y_grid[g] = final_outs[j];
        z_grid[g] = if party == 0 {
            expected_final_outs[j]
        } else {
            0
        };
    }
    for g in SD_CHECKED_GATES..(SD_GRID_B * SD_GRID_L) {
        x_grid[g] = 0;
        y_grid[g] = 0;
        z_grid[g] = 0;
    }
}

/// Evaluate `R~(r) = sum_{d=0..B-1} coeff[d]*r^d + sum_{d=B+1..=2B} coeff[d-1]*r^d`
/// (where the degree-`B` coefficient is identically zero).
pub(super) fn eval_r_poly_without_b(
    r_poly_without_b: &[[u64; 5]],
    r_powers: &[Fp5; 2 * SD_GRID_B + 1],
) -> Fp5 {
    debug_assert_eq!(r_poly_without_b.len(), SD_RPOLY_COEFFS);
    let mut acc = Fp5::ZERO;
    for (coeff, &pow) in r_poly_without_b[..SD_GRID_B]
        .iter()
        .zip(&r_powers[..SD_GRID_B])
    {
        acc = acc.add(Fp5::from_limbs(*coeff).mul(pow));
    }
    for (coeff, &pow) in r_poly_without_b[SD_GRID_B..SD_RPOLY_COEFFS]
        .iter()
        .zip(&r_powers[SD_GRID_B + 1..=SD_RPOLY_COEFFS])
    {
        acc = acc.add(Fp5::from_limbs(*coeff).mul(pow));
    }
    acc
}

pub(super) fn precompute_eval_powers(r: Fp5) -> [Fp5; 2 * SD_GRID_B + 1] {
    let mut powers = [Fp5::ZERO; 2 * SD_GRID_B + 1];
    powers[0] = Fp5::ONE;
    for d in 1..=2 * SD_GRID_B {
        powers[d] = powers[d - 1].mul(r);
    }
    powers
}

pub(super) struct EvalTables {
    pub(super) r_powers: [Fp5; 2 * SD_GRID_B + 1],
    theta_r_pow: [Fp5; SD_GRID_B],
    theta: [Fp5; SD_GRID_B],
    eta: [Fp5; SD_GRID_L],
}

impl EvalTables {
    pub(super) fn new(theta: [Fp5; SD_GRID_B], eta: [Fp5; SD_GRID_L], r: Fp5) -> Self {
        let r_powers = precompute_eval_powers(r);
        let mut theta_r_pow = [Fp5::ZERO; SD_GRID_B];
        for b in 0..SD_GRID_B {
            theta_r_pow[b] = theta[b].mul(r_powers[b + 1]);
        }
        Self {
            r_powers,
            theta_r_pow,
            theta,
            eta,
        }
    }
}

#[inline]
pub(super) fn gl_reduce_split_u192(lo: u128, hi: u128) -> Goldilocks {
    // Exact modulo p = 2^64 - 2^32 + 1 since 2^64 === 2^32 - 1 (mod p).
    const TWO_64: Goldilocks = Goldilocks::from_u64_reduced(GOLDILOCKS_EPSILON);
    Goldilocks::reduce128(lo).const_add(Goldilocks::reduce128(hi).const_mul(TWO_64))
}

#[inline]
pub(super) fn reduce_fp5_split(lo: &[u128; 5], hi: &[u128; 5]) -> Fp5 {
    Fp5([
        gl_reduce_split_u192(lo[0], hi[0]),
        gl_reduce_split_u192(lo[1], hi[1]),
        gl_reduce_split_u192(lo[2], hi[2]),
        gl_reduce_split_u192(lo[3], hi[3]),
        gl_reduce_split_u192(lo[4], hi[4]),
    ])
}

/// Evaluate one party's polynomial shares `(alpha^(i), beta^(i), sigma^(i))` at `r` using
/// lazy 192-bit `(lo, hi)` scalar-in-GF(p) accumulation across rows `b in 0..B` (`0` modular
/// reductions inside the 36,864-gate loop).
#[expect(
    clippy::too_many_arguments,
    reason = "Flat tape slice and precomputed folding/evaluation tables avoid extra heap copies"
)]
pub(super) fn eval_party_polynomial_shares(
    u_pad: &[Fp5; SD_GRID_L],
    v_pad: &[Fp5; SD_GRID_L],
    c_share: Fp5,
    poly_mask: &[Fp5; SD_RPOLY_COEFFS],
    x_grid: &[u64; SD_GRID_B * SD_GRID_L],
    y_grid: &[u64; SD_GRID_B * SD_GRID_L],
    z_grid: &[u64; SD_GRID_B * SD_GRID_L],
    tables: &EvalTables,
) -> ([Fp5; SD_GRID_L], [Fp5; SD_GRID_L], Fp5) {
    const MASK64: u128 = 0xffff_ffff_ffff_ffff;
    let mut x_lo = SecretBuffer([[0u128; 5]; SD_GRID_L]);
    let mut x_hi = SecretBuffer([[0u128; 5]; SD_GRID_L]);
    let mut y_lo = SecretBuffer([[0u128; 5]; SD_GRID_L]);
    let mut y_hi = SecretBuffer([[0u128; 5]; SD_GRID_L]);
    let mut z_lo = SecretBuffer([[0u128; 5]; SD_GRID_L]);
    let mut z_hi = SecretBuffer([[0u128; 5]; SD_GRID_L]);

    for b in 0..SD_GRID_B {
        let row_off = b * SD_GRID_L;
        let wx = tables.theta_r_pow[b].to_wide_limbs();
        let wy = tables.r_powers[SD_GRID_B - 1 - b].to_wide_limbs();
        let wz = tables.theta[b].to_wide_limbs();
        for l in 0..SD_GRID_L {
            let idx = row_off + l;
            let xv = x_grid[idx] as u128;
            if xv != 0 {
                for c in 0..5 {
                    let p = wx[c] * xv;
                    x_lo[l][c] += p & MASK64;
                    x_hi[l][c] += p >> 64;
                }
            }
            let yv = y_grid[idx] as u128;
            if yv != 0 {
                for c in 0..5 {
                    let p = wy[c] * yv;
                    y_lo[l][c] += p & MASK64;
                    y_hi[l][c] += p >> 64;
                }
            }
            let zv = z_grid[idx] as u128;
            if zv != 0 {
                for c in 0..5 {
                    let p = wz[c] * zv;
                    z_lo[l][c] += p & MASK64;
                    z_hi[l][c] += p >> 64;
                }
            }
        }
    }

    let r_b = tables.r_powers[SD_GRID_B];
    let mut alpha_i = [Fp5::ZERO; SD_GRID_L];
    let mut beta_i = [Fp5::ZERO; SD_GRID_L];
    let mut z_weighted = Fp5::ZERO;
    for l in 0..SD_GRID_L {
        let sum_x_l = reduce_fp5_split(&x_lo[l], &x_hi[l]);
        let sum_y_l = reduce_fp5_split(&y_lo[l], &y_hi[l]);
        let sum_z_l = reduce_fp5_split(&z_lo[l], &z_hi[l]);
        alpha_i[l] = u_pad[l].add(tables.eta[l].mul(sum_x_l));
        beta_i[l] = v_pad[l].mul(r_b).add(sum_y_l);
        z_weighted = z_weighted.add(tables.eta[l].mul(sum_z_l));
    }

    let mut mask_at_r = Fp5::ZERO;
    for (&m, &pow) in poly_mask[..SD_GRID_B]
        .iter()
        .zip(&tables.r_powers[..SD_GRID_B])
    {
        mask_at_r = mask_at_r.add(m.mul(pow));
    }
    for (&m, &pow) in poly_mask[SD_GRID_B..SD_RPOLY_COEFFS]
        .iter()
        .zip(&tables.r_powers[SD_GRID_B + 1..=SD_RPOLY_COEFFS])
    {
        mask_at_r = mask_at_r.add(m.mul(pow));
    }

    let sigma_i = c_share.add(z_weighted).mul(r_b).sub(mask_at_r);
    (alpha_i, beta_i, sigma_i)
}

/// Tape layout squeezed from `Shake256PartyBatch8` (after the 4-word `salt_1` prefix):
/// - `u_pad`: `SD_GRID_L * 5` (`960` limbs)
/// - `v_pad`: `SD_GRID_L * 5` (`960` limbs)
/// - `c_pad`: `5` limbs
/// - `poly_mask`: `SD_RPOLY_COEFFS * 5` (`1,810` limbs)
/// - `w_mask`: `num_secret_wires` limbs
/// - `z_mask`: `SD_TOTAL_GATES` (`36,484` limbs)
pub(super) const PARTY_EXT_LIMBS: usize = (SD_GRID_L + SD_GRID_L + 1 + SD_RPOLY_COEFFS) * 5; // 3,625

pub(super) fn unpack_party_ext_masks(
    tape: &[u64],
) -> (
    [Fp5; SD_GRID_L],
    [Fp5; SD_GRID_L],
    Fp5,
    [Fp5; SD_RPOLY_COEFFS],
) {
    let mut cur = 0usize;
    let mut u_pad = [Fp5::ZERO; SD_GRID_L];
    for slot in &mut u_pad {
        *slot = Fp5::from_limbs([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    let mut v_pad = [Fp5::ZERO; SD_GRID_L];
    for slot in &mut v_pad {
        *slot = Fp5::from_limbs([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    let c_pad = Fp5::from_limbs([
        tape[cur],
        tape[cur + 1],
        tape[cur + 2],
        tape[cur + 3],
        tape[cur + 4],
    ]);
    cur += 5;
    let mut poly_mask = [Fp5::ZERO; SD_RPOLY_COEFFS];
    for slot in &mut poly_mask {
        *slot = Fp5::from_limbs([
            tape[cur],
            tape[cur + 1],
            tape[cur + 2],
            tape[cur + 3],
            tape[cur + 4],
        ]);
        cur += 5;
    }
    debug_assert_eq!(cur, PARTY_EXT_LIMBS);
    (u_pad, v_pad, c_pad, poly_mask)
}

#[cfg(any(test, feature = "std"))]
pub(super) fn parallel_map_indexed<T, F>(len: usize, f: F) -> Vec<T>
where
    T: Send,
    F: Fn(usize) -> T + Sync,
{
    if len <= 1 {
        return (0..len).map(f).collect();
    }
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
        .min(16)
        .min(len);
    if workers <= 1 {
        return (0..len).map(f).collect();
    }
    let chunk_size = len.div_ceil(workers);
    std::thread::scope(|s| {
        let f_ref = &f;
        let mut handles = Vec::with_capacity(workers);
        let mut start = 0usize;
        while start < len {
            let end = (start + chunk_size).min(len);
            handles.push(s.spawn(move || (start..end).map(f_ref).collect::<Vec<T>>()));
            start = end;
        }
        let mut out = Vec::with_capacity(len);
        for h in handles {
            out.extend(h.join().expect("selective-disclosure worker panicked"));
        }
        out
    })
}

#[cfg(not(any(test, feature = "std")))]
pub(super) fn parallel_map_indexed<T, F>(len: usize, f: F) -> Vec<T>
where
    F: Fn(usize) -> T,
{
    (0..len).map(f).collect()
}
