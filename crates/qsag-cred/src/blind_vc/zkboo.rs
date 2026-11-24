use super::*;

// ============================================================================
// 3-Party Goldilocks ZKBoo Gate Engine
// ============================================================================

pub(super) struct ZkBooProverTape {
    r: [SecretBuffer<Vec<u64>>; 3],
    pub(super) out: [Vec<u64>; 3],
    pub(super) gate_cursor: usize,
}

impl Drop for ZkBooProverTape {
    fn drop(&mut self) {
        for row in self.out.iter_mut() {
            ct_zeroize_u64s(row);
        }
    }
}

impl ZkBooProverTape {
    pub(super) fn new(tape_seeds: &[[u8; 32]; 3], num_gates: usize) -> Self {
        let r0 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[0], &[0], num_gates);
        let r1 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[1], &[1], num_gates);
        let r2 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", &tape_seeds[2], &[2], num_gates);
        Self {
            r: [r0, r1, r2],
            out: [
                Vec::with_capacity(num_gates),
                Vec::with_capacity(num_gates),
                Vec::with_capacity(num_gates),
            ],
            gate_cursor: 0,
        }
    }

    #[inline]
    fn mul_gate(&mut self, x: [u64; 3], y: [u64; 3]) -> [u64; 3] {
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let mut z = [0u64; 3];
        for (m, slot) in z.iter_mut().enumerate() {
            let m1 = (m + 1) % 3;
            let cross = gl_add(
                gl_mul(x[m], y[m]),
                gl_add(gl_mul(x[m], y[m1]), gl_mul(x[m1], y[m])),
            );
            let masked = gl_sub(gl_add(cross, self.r[m][g]), self.r[m1][g]);
            *slot = masked;
            self.out[m].push(masked);
        }
        z
    }

    #[inline]
    fn sbox7(&mut self, x: [u64; 3]) -> [u64; 3] {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    pub(super) fn perm12(&mut self, message: &mut [[u64; 3]]) {
        // All three shares of every state wire: erased on every way out.
        let mut state = SecretBuffer([[0u64; 3]; 12]);
        for chunk in message.chunks(6) {
            for (wire, value) in state.iter_mut().zip(chunk) {
                for m in 0..3 {
                    wire[m] = gl_add(wire[m], value[m]);
                }
            }
            if chunk.len() < 6 {
                state[chunk.len()][0] = gl_add(state[chunk.len()][0], 1);
            }
            self.raw_perm12(&mut state);
        }
        if message.len().is_multiple_of(6) {
            state[0][0] = gl_add(state[0][0], 1);
            self.raw_perm12(&mut state);
        }
        message[..12].copy_from_slice(&state[..]);
    }
    pub(super) fn raw_perm12(&mut self, st: &mut [[u64; 3]; 12]) {
        apply_me_3(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                wire[0] = gl_add(wire[0], poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_3(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0][0] = gl_add(st[0][0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            apply_mi_3(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                wire[0] = gl_add(wire[0], poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_3(st);
        }
    }
}

pub(super) struct ZkBooVerifierTape<'a> {
    e: usize,
    e1: usize,
    r_e: SecretBuffer<Vec<u64>>,
    r_e1: SecretBuffer<Vec<u64>>,
    out_e: &'a [u64],
    out_e1: &'a [u64],
    pub(super) gate_cursor: usize,
    pub(super) ok: bool,
}

impl<'a> ZkBooVerifierTape<'a> {
    pub(super) fn new(
        e: usize,
        seed_e: &[u8; 32],
        seed_e1: &[u8; 32],
        out_e: &'a [u64],
        out_e1: &'a [u64],
        num_gates: usize,
    ) -> Self {
        let e1 = (e + 1) % 3;
        let ok = out_e.len() == num_gates && out_e1.len() == num_gates;
        let r_e = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", seed_e, &[e as u8], num_gates);
        let r_e1 = sample_canonical_gl_vec(b"QSAG.VC.ZKBOO_R.V1", seed_e1, &[e1 as u8], num_gates);
        Self {
            e,
            e1,
            r_e,
            r_e1,
            out_e,
            out_e1,
            gate_cursor: 0,
            ok,
        }
    }

    #[inline]
    pub(super) fn add_const(&self, mut x: [u64; 2], c: u64) -> [u64; 2] {
        if self.e == 0 {
            x[0] = gl_add(x[0], c);
        } else if self.e1 == 0 {
            x[1] = gl_add(x[1], c);
        }
        x
    }

    #[inline]
    fn mul_gate(&mut self, x: [u64; 2], y: [u64; 2]) -> [u64; 2] {
        if !self.ok {
            return [0, 0];
        }
        let g = self.gate_cursor;
        self.gate_cursor += 1;
        let cross = gl_add(
            gl_mul(x[0], y[0]),
            gl_add(gl_mul(x[0], y[1]), gl_mul(x[1], y[0])),
        );
        let expected_ze = gl_sub(gl_add(cross, self.r_e[g]), self.r_e1[g]);
        // Opened-view multiplication equation, including the adjacent mask shares.
        if gl_sub(self.out_e[g], expected_ze) != 0 {
            self.ok = false;
        }
        [self.out_e[g], self.out_e1[g]]
    }

    #[inline]
    fn sbox7(&mut self, x: [u64; 2]) -> [u64; 2] {
        let x2 = self.mul_gate(x, x);
        let x3 = self.mul_gate(x2, x);
        let x4 = self.mul_gate(x2, x2);
        self.mul_gate(x4, x3)
    }

    pub(super) fn perm12(&mut self, message: &mut [[u64; 2]]) {
        let mut state = [[0; 2]; 12];
        for chunk in message.chunks(6) {
            for (wire, value) in state.iter_mut().zip(chunk) {
                for m in 0..2 {
                    wire[m] = gl_add(wire[m], value[m]);
                }
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
        message[..12].copy_from_slice(&state);
    }
    pub(super) fn raw_perm12(&mut self, st: &mut [[u64; 2]; 12]) {
        apply_me_2(st);
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = self.add_const(*wire, poseidon2_const_at(0, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_2(st);
        }
        for r in 0..POSEIDON2_INTERNAL_ROUNDS {
            st[0] = self.add_const(st[0], poseidon2_const_at(1, r, 0));
            st[0] = self.sbox7(st[0]);
            apply_mi_2(st);
        }
        for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
            for (lane, wire) in st.iter_mut().enumerate() {
                *wire = self.add_const(*wire, poseidon2_const_at(2, r, lane as u64));
                *wire = self.sbox7(*wire);
            }
            apply_me_2(st);
        }
    }
}

pub(super) fn apply_me_3(st: &mut [[u64; 3]; 12]) {
    for m in 0..3 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_me(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

pub(super) fn apply_mi_3(st: &mut [[u64; 3]; 12]) {
    for m in 0..3 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_mi(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

pub(super) fn apply_me_2(st: &mut [[u64; 2]; 12]) {
    for m in 0..2 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_me(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

pub(super) fn apply_mi_2(st: &mut [[u64; 2]; 12]) {
    for m in 0..2 {
        let mut lane_m: [u64; 12] = core::array::from_fn(|i| st[i][m]);
        poseidon2_apply_mi(&mut lane_m);
        for (wire, value) in st.iter_mut().zip(lane_m) {
            wire[m] = value;
        }
    }
}

pub(super) const GATES_PER_PERM12: usize = (2 * (POSEIDON2_HALF_EXTERNAL_ROUNDS as usize) * 12
    + (POSEIDON2_INTERNAL_ROUNDS as usize))
    * 12; // Three permutations, four multiplication gates per S-box.

pub(super) fn split_secret_3(val: u64, s0: u64, s1: u64) -> [u64; 3] {
    let s2 = gl_sub(val, gl_add(s0, s1));
    [s0, s1, s2]
}

pub(super) fn digest_party_view(
    in_shares: &[u64],
    tape_seed: &[u8; 32],
    gate_outs: &[u64],
    final_outs: &[u64],
) -> [u8; 32] {
    let mut sp = Shake256::new();
    sp.absorb(b"QSAG.VC.VIEW_COM.V1");
    sp.absorb(tape_seed);
    sp.absorb(&(in_shares.len() as u32).to_le_bytes());
    for &x in in_shares {
        sp.absorb(&x.to_le_bytes());
    }
    sp.absorb(&(gate_outs.len() as u32).to_le_bytes());
    for &x in gate_outs {
        sp.absorb(&x.to_le_bytes());
    }
    sp.absorb(&(final_outs.len() as u32).to_le_bytes());
    for &x in final_outs {
        sp.absorb(&x.to_le_bytes());
    }
    sp.finalize(0x1F);
    let mut out = [0u8; 32];
    sp.squeeze(&mut out);
    out
}

/// Unbiased ternary challenge extractor (`byte < 243` yields 5 independent uniform `{0, 1, 2}` trits!).
pub(super) fn squeeze_ternary_challenges(
    tr: &mut InterleavedTranscript,
    count: usize,
) -> Vec<usize> {
    let mut out = Vec::with_capacity(count);
    let mut raw = [0u8; 64];
    tr.squeeze_bytes(b"VC_ZKBOO_OPEN_TRITS", &mut raw);
    let mut cursor = 0usize;
    let mut extra_round = 0u32;
    while out.len() < count {
        if cursor >= raw.len() {
            tr.absorb(b"VC_TRIT_EXTEND", &extra_round.to_le_bytes());
            extra_round += 1;
            tr.squeeze_bytes(b"VC_ZKBOO_OPEN_TRITS_MORE", &mut raw);
            cursor = 0;
        }
        let b = raw[cursor];
        cursor += 1;
        if b < 243 {
            let mut v = b;
            for _ in 0..5 {
                if out.len() < count {
                    out.push((v % 3) as usize);
                }
                v /= 3;
            }
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedZkBooRepetition {
    pub e: u8,
    pub unopened_commitment: [u8; 32],
    pub salt_e: [u8; 32],
    pub salt_e1: [u8; 32],
    pub in_shares_e: Vec<u64>,
    pub in_shares_e1: Vec<u64>,
    pub tape_seed_e: [u8; 32],
    pub tape_seed_e1: [u8; 32],
    pub gate_outs_e: Vec<u64>,
    pub gate_outs_e1: Vec<u64>,
    pub final_outs_all3: [[u64; 3]; VC_FINAL_OUTPUTS],
    pub num_active_final_outs: usize,
}
