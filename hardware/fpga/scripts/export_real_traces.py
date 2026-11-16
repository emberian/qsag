#!/usr/bin/env python3
"""Instrument an ISOLATED remote scratch copy of `qsag-agg` and export real proofs + verifier
operation traces for:
  1. `real_qsagsta1_ts` : Canonical Role-1 `QSAGSTA1` wire proof (`TurboShakeCdhz25JohnsonQrom128`)
  2. `real_qsagsta1_p2` : Role-2 algebraic `QSAGSTA1` wire proof (`Poseidon2Cdhz25JohnsonQrom128`)
  3. `real_duet_fold`   : `[CWYZ26]` `DuetFold` multi-statement folding proof (`verify_duet_folds`)

HARD SAFETY INVARIANT: Refuses to touch anything outside `/home/build/qsag-ni-fpga/work/`.
"""
from pathlib import Path
import sys

def replace_once(text: str, old: str, new: str, label: str) -> str:
    cnt = text.count(old)
    if cnt != 1:
        raise RuntimeError(f"[{label}] expected exactly 1 occurrence, found {cnt}:\n{old[:200]}")
    return text.replace(old, new, 1)

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: export_real_traces.py /home/build/qsag-ni-fpga/work/h3/repo")
    repo = Path(sys.argv[1]).resolve()
    if not str(repo).startswith("/home/build/qsag-ni-fpga/work/"):
        raise SystemExit(f"REFUSING non-scratch repo path: {repo}")

    agg = repo / "crates/qsag-agg/src"

    # ------------------------------------------------------------------ 1. fpga_trace.rs
    (agg / "fpga_trace.rs").write_text('''#![allow(dead_code)]
use crate::field::{Goldilocks, GoldilocksExt4 as E};
use std::cell::Cell;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};

static ACTIVE: AtomicBool = AtomicBool::new(false);
static TRACE: Mutex<Option<BufWriter<File>>> = Mutex::new(None);

std::thread_local! {
    static SUPPRESS: Cell<u32> = const { Cell::new(0) };
    static P2_BATCH: Cell<u32> = const { Cell::new(0) };
}

pub struct SuppressGuard {
    pub was_outer: bool,
}
impl Drop for SuppressGuard {
    fn drop(&mut self) {
        SUPPRESS.with(|c| c.set(c.get() - 1));
    }
}

pub struct BatchGuard;
impl Drop for BatchGuard {
    fn drop(&mut self) {
        P2_BATCH.with(|c| c.set(c.get() - 1));
    }
}

#[inline]
pub fn active() -> bool {
    ACTIVE.load(Ordering::Relaxed) && SUPPRESS.with(|c| c.get() == 0)
}

#[inline]
pub fn p2_batch_active() -> bool {
    active() && P2_BATCH.with(|c| c.get() > 0)
}

pub fn suppress() -> SuppressGuard {
    let was_outer = active();
    SUPPRESS.with(|c| c.set(c.get() + 1));
    SuppressGuard { was_outer }
}

pub fn enter_p2_batch() -> BatchGuard {
    P2_BATCH.with(|c| c.set(c.get() + 1));
    BatchGuard
}

pub fn start(path: &str) {
    *TRACE.lock().unwrap() = Some(BufWriter::new(File::create(path).unwrap()));
    ACTIVE.store(true, Ordering::SeqCst);
}

pub fn stop() {
    ACTIVE.store(false, Ordering::SeqCst);
    if let Some(mut w) = TRACE.lock().unwrap().take() {
        w.flush().unwrap();
    }
}

pub fn raw_line(line: &str) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        writeln!(w, "{line}").unwrap();
    }
}

pub fn words(tag: &str, xs: &[u64]) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        write!(w, "{tag}").unwrap();
        for &x in xs {
            write!(w, " {x:016x}").unwrap();
        }
        writeln!(w).unwrap();
    }
}

#[inline]
pub fn bytes32_to_u64s(b: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap()))
}

#[inline]
pub fn ext_to_u64s(e: E) -> [u64; 4] {
    e.to_limbs().map(Goldilocks::to_canonical_u64)
}

pub fn mid_id(mid: &[u64; 25]) -> u8 {
    match mid[0] {
        0x3977c693fff5d3b5 => 1, // FS_MIDSTATE
        0x460887f1cba4a839 => 2, // TURBOSHAKE_CANOPY_MIDSTATE
        0x05c2a834d12f320b => 3, // TURBOSHAKE_POW_MIDSTATE
        0xec954fc7c2fc5381 => 4, // CANOPY_MIDSTATE
        _ => 5,                  // custom midstate (e.g. POW_MIDSTATE)
    }
}

pub fn ks_sponge(midstate: &[u64; 25], input: &[u8], out_len: usize, nr12: bool, suffix: u8) {
    if !active() {
        return;
    }
    let _g = suppress();
    let mid = mid_id(midstate);
    if mid == 5 {
        words("KM", midstate);
    }
    let mut state = *midstate;
    let mut first = true;
    let (chunks, rem) = input.as_chunks::<136>();
    for blk in chunks {
        let mut lanes = [0u64; 17];
        for i in 0..17 {
            lanes[i] = u64::from_le_bytes(blk[8 * i..8 * i + 8].try_into().unwrap());
            state[i] ^= lanes[i];
        }
        if nr12 {
            crate::sponge::keccak_p1600_12(&mut state);
        } else {
            crate::sponge::keccak_f1600(&mut state);
        }
        if let Some(w) = TRACE.lock().unwrap().as_mut() {
            let init_flag = if first && mid != 5 { 1 } else { 0 };
            write!(w, "KS {} {} {} 0", mid, nr12 as u8, init_flag).unwrap();
            for &l in &lanes {
                write!(w, " {l:016x}").unwrap();
            }
            for i in 0..4 {
                write!(w, " {:016x}", state[i]).unwrap();
            }
            writeln!(w).unwrap();
        }
        first = false;
    }

    let mut pad = [0u8; 136];
    pad[..rem.len()].copy_from_slice(rem);
    pad[rem.len()] ^= suffix;
    pad[135] ^= 0x80;
    let mut lanes = [0u64; 17];
    for i in 0..17 {
        lanes[i] = u64::from_le_bytes(pad[8 * i..8 * i + 8].try_into().unwrap());
        state[i] ^= lanes[i];
    }
    if nr12 {
        crate::sponge::keccak_p1600_12(&mut state);
    } else {
        crate::sponge::keccak_f1600(&mut state);
    }
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        let init_flag = if first && mid != 5 { 1 } else { 0 };
        write!(w, "KS {} {} {} 1", mid, nr12 as u8, init_flag).unwrap();
        for &l in &lanes {
            write!(w, " {l:016x}").unwrap();
        }
        for i in 0..4 {
            write!(w, " {:016x}", state[i]).unwrap();
        }
        writeln!(w).unwrap();
    }

    let mut written = 0usize;
    while written < out_len {
        let rem_out = out_len - written;
        if rem_out <= 32 {
            break;
        }
        let take = rem_out.min(136);
        written += take;
        if written < out_len {
            if nr12 {
                crate::sponge::keccak_p1600_12(&mut state);
            } else {
                crate::sponge::keccak_f1600(&mut state);
            }
            if let Some(w) = TRACE.lock().unwrap().as_mut() {
                write!(w, "KS {} {} 0 1", mid, nr12 as u8).unwrap();
                for _ in 0..17 {
                    write!(w, " 0000000000000000").unwrap();
                }
                for i in 0..4 {
                    write!(w, " {:016x}", state[i]).unwrap();
                }
                writeln!(w).unwrap();
            }
        }
    }
}

pub fn tc(
    turbo: bool,
    log_leaves: u8,
    root: &[u8; 32],
    leaves: &[(usize, [u8; 32])],
    sibs: &[[u8; 32]],
) {
    let n = 1usize << (log_leaves as usize);
    let r4 = bytes32_to_u64s(root);
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        writeln!(
            w,
            "TC {} {} {} {} {:016x} {:016x} {:016x} {:016x}",
            turbo as u8,
            log_leaves,
            leaves.len(),
            sibs.len(),
            r4[0],
            r4[1],
            r4[2],
            r4[3]
        )
        .unwrap();
        for &(idx, ref h) in leaves {
            let l4 = bytes32_to_u64s(h);
            writeln!(
                w,
                "TCL {} {:016x} {:016x} {:016x} {:016x}",
                n + idx,
                l4[0],
                l4[1],
                l4[2],
                l4[3]
            )
            .unwrap();
        }
        for s in sibs {
            let s4 = bytes32_to_u64s(s);
            writeln!(
                w,
                "TCS {:016x} {:016x} {:016x} {:016x}",
                s4[0], s4[1], s4[2], s4[3]
            )
            .unwrap();
        }
    }
}

pub fn pl(init_cap: [u64; 4], blocks: &[[u64; 8]], out4: [u64; 4]) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        write!(
            w,
            "PL {} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
            blocks.len(),
            init_cap[0],
            init_cap[1],
            init_cap[2],
            init_cap[3],
            out4[0],
            out4[1],
            out4[2],
            out4[3]
        )
        .unwrap();
        for b in blocks {
            for &v in b {
                write!(w, " {v:016x}").unwrap();
            }
        }
        writeln!(w).unwrap();
    }
}

pub fn pc(
    key: [Goldilocks; 4],
    levels: &[std::vec::Vec<(u32, [u8; 32], [u8; 32], [u8; 32])>],
) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        let k4 = key.map(Goldilocks::to_canonical_u64);
        writeln!(
            w,
            "PC {} {:016x} {:016x} {:016x}",
            levels.len(),
            k4[0],
            k4[1],
            k4[2]
        )
        .unwrap();
        for lvl in levels {
            writeln!(w, "PCL {}", lvl.len()).unwrap();
            for &(node_idx, ref l, ref r, ref p) in lvl {
                let l4 = bytes32_to_u64s(l);
                let r4 = bytes32_to_u64s(r);
                let p4 = bytes32_to_u64s(p);
                writeln!(
                    w,
                    "PCN {} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
                    node_idx,
                    l4[0], l4[1], l4[2], l4[3],
                    r4[0], r4[1], r4[2], r4[3],
                    p4[0], p4[1], p4[2], p4[3]
                )
                .unwrap();
            }
        }
    }
}

pub fn sc(coeffs_low_to_high: &[E], prev_claim: E, chal: E, next_claim: E) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        let deg = coeffs_low_to_high.len() - 1;
        let pc4 = ext_to_u64s(prev_claim);
        let ch4 = ext_to_u64s(chal);
        let nc4 = ext_to_u64s(next_claim);
        write!(
            w,
            "SC {} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x} {:016x}",
            deg, pc4[0], pc4[1], pc4[2], pc4[3], ch4[0], ch4[1], ch4[2], ch4[3]
        )
        .unwrap();
        for &c in coeffs_low_to_high.iter().rev() {
            for v in ext_to_u64s(c) {
                write!(w, " {v:016x}").unwrap();
            }
        }
        for v in nc4 {
            write!(w, " {v:016x}").unwrap();
        }
        writeln!(w).unwrap();
    }
}

pub fn fd(table: &[E], point: &[E], res: E) {
    if let Some(w) = TRACE.lock().unwrap().as_mut() {
        writeln!(w, "FD {}", point.len()).unwrap();
        for &e in table {
            let v = ext_to_u64s(e);
            writeln!(w, "FDT {:016x} {:016x} {:016x} {:016x}", v[0], v[1], v[2], v[3]).unwrap();
        }
        for &r in point {
            let v = ext_to_u64s(r);
            writeln!(w, "FDR {:016x} {:016x} {:016x} {:016x}", v[0], v[1], v[2], v[3]).unwrap();
        }
        let o = ext_to_u64s(res);
        writeln!(w, "FDO {:016x} {:016x} {:016x} {:016x}", o[0], o[1], o[2], o[3]).unwrap();
    }
}

pub fn ext_mac(a: E, b: E, c: E, out: E) {
    if !active() {
        return;
    }
    let mut xs = [0u64; 16];
    xs[0..4].copy_from_slice(&ext_to_u64s(a));
    xs[4..8].copy_from_slice(&ext_to_u64s(b));
    xs[8..12].copy_from_slice(&ext_to_u64s(c));
    xs[12..16].copy_from_slice(&ext_to_u64s(out));
    words("E", &xs);
}
''')

    # ------------------------------------------------------------------ 2. lib.rs
    lib_p = agg / "lib.rs"
    lib_s = lib_p.read_text()
    if "pub mod fpga_trace;" not in lib_s:
        lib_p.write_text(lib_s + "\npub mod fpga_trace;\n")

    # ------------------------------------------------------------------ 3. sponge.rs
    sp_p = agg / "sponge.rs"
    sp = sp_p.read_text()

    # 3a. turboshake256_from_midstate_into + _lanes
    sp = replace_once(
        sp,
        "pub fn turboshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {\n    let mut state = *midstate;",
        "pub fn turboshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {\n    if crate::fpga_trace::active() {\n        crate::fpga_trace::ks_sponge(midstate, input, out.len(), true, TURBOSHAKE_SUFFIX);\n    }\n    let _fpga_g = crate::fpga_trace::suppress();\n    let mut state = *midstate;",
        "turboshake256_from_midstate_into",
    )
    sp = replace_once(
        sp,
        "fn turboshake256_from_midstate_32_lanes<const N: usize>(\n    midstate: &[u64; 25],\n    inputs: [&[u8]; N],\n) -> [[u8; 32]; N] {",
        "fn turboshake256_from_midstate_32_lanes<const N: usize>(\n    midstate: &[u64; 25],\n    inputs: [&[u8]; N],\n) -> [[u8; 32]; N] {\n    if crate::fpga_trace::active() {\n        return core::array::from_fn(|k| turboshake256_from_midstate_32(midstate, inputs[k]));\n    }",
        "turboshake256_from_midstate_32_lanes",
    )

    # 3b. cshake256_from_midstate_into + _x4 + _x8
    sp = replace_once(
        sp,
        "pub fn cshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {\n    absorb_and_squeeze_from_state(*midstate, input, 0x04, out);\n}",
        "pub fn cshake256_from_midstate_into(midstate: &[u64; 25], input: &[u8], out: &mut [u8]) {\n    if crate::fpga_trace::active() {\n        crate::fpga_trace::ks_sponge(midstate, input, out.len(), false, 0x04);\n    }\n    let _fpga_g = crate::fpga_trace::suppress();\n    absorb_and_squeeze_from_state(*midstate, input, 0x04, out);\n}",
        "cshake256_from_midstate_into",
    )
    sp = replace_once(
        sp,
        "pub fn cshake256_from_midstate_32_x4(midstate: &[u64; 25], inputs: [&[u8]; 4]) -> [[u8; 32]; 4] {",
        "pub fn cshake256_from_midstate_32_x4(midstate: &[u64; 25], inputs: [&[u8]; 4]) -> [[u8; 32]; 4] {\n    if crate::fpga_trace::active() {\n        return core::array::from_fn(|k| cshake256_from_midstate_32(midstate, inputs[k]));\n    }",
        "cshake256_from_midstate_32_x4",
    )
    sp = replace_once(
        sp,
        "pub fn cshake256_from_midstate_32_x8(midstate: &[u64; 25], inputs: [&[u8]; 8]) -> [[u8; 32]; 8] {",
        "pub fn cshake256_from_midstate_32_x8(midstate: &[u64; 25], inputs: [&[u8]; 8]) -> [[u8; 32]; 8] {\n    if crate::fpga_trace::active() {\n        return core::array::from_fn(|k| cshake256_from_midstate_32(midstate, inputs[k]));\n    }",
        "cshake256_from_midstate_32_x8",
    )

    # 3c. Poseidon2 permute + Jive + parallel sponge batch
    sp = replace_once(
        sp,
        "    pub(super) const fn permute(input: &[u64; 12]) -> [u64; 12] {",
        "    pub(super) fn permute(input: &[u64; 12]) -> [u64; 12] {",
        "permute sig",
    )
    a = sp.index("    pub(super) fn permute(input: &[u64; 12]) -> [u64; 12] {")
    b = sp.index("\n}\n", a)
    seg = replace_once(
        sp[a:b],
        "        st\n    }",
        '''        if crate::fpga_trace::active() {
            let mut tr = [0u64; 24];
            tr[..12].copy_from_slice(&input.map(|v| crate::field::Goldilocks::from_u64_reduced(v).to_canonical_u64()));
            tr[12..].copy_from_slice(&st.map(|v| crate::field::Goldilocks::from_u64_reduced(v).to_canonical_u64()));
            crate::fpga_trace::words("P", &tr);
        }
        st
    }''',
        "permute body",
    )
    sp = sp[:a] + seg + sp[b:]

    sp = replace_once(
        sp,
        "    let mut perm = perm_kernel::permute(&st.map(Goldilocks::to_canonical_u64));",
        "    let _fpga_g = crate::fpga_trace::suppress();\n    let mut perm = perm_kernel::permute(&st.map(Goldilocks::to_canonical_u64));",
        "compress12_ff suppress",
    )
    a = sp.index("pub fn poseidon2_compress12_ff(")
    b = sp.index("\n}\n", a)
    seg = replace_once(
        sp[a:b],
        "    qsag_asm::volatile_fill(&mut perm,",
        '''    drop(_fpga_g);
    if crate::fpga_trace::active() {
        let mut tr = [0u64; 16];
        tr[..12].copy_from_slice(&st.map(Goldilocks::to_canonical_u64));
        tr[12..].copy_from_slice(&out.map(Goldilocks::to_canonical_u64));
        crate::fpga_trace::words("J", &tr);
    }
    qsag_asm::volatile_fill(&mut perm,''',
        "compress12_ff emit",
    )
    sp = sp[:a] + seg + sp[b:]

    # Parallel sponge capture inside poseidon2_sponge_hash_limbs when p2_batch_active()
    sp = replace_once(
        sp,
        "pub fn poseidon2_sponge_hash_limbs(\n    domain_tag: u64,\n    init_cap: [Goldilocks; 4],\n    limbs: &[Goldilocks],\n) -> [Goldilocks; 4] {",
        '''pub fn poseidon2_sponge_hash_limbs(
    domain_tag: u64,
    init_cap: [Goldilocks; 4],
    limbs: &[Goldilocks],
) -> [Goldilocks; 4] {
    let batch_cap = crate::fpga_trace::p2_batch_active();
    let _batch_sup = batch_cap.then(crate::fpga_trace::suppress);
    let mut trace_blocks: Vec<[u64; 8]> = Vec::new();''',
        "poseidon2_sponge_hash_limbs sig",
    )
    a = sp.index("pub fn poseidon2_sponge_hash_limbs(")
    b = sp.index("\n/// Derive the per-tree salted capacity key", a)
    seg = sp[a:b]
    seg = replace_once(
        seg,
        "    let absorb = |st: &mut [u64; 12], block: &[u64; 8]| {",
        "    let mut absorb = |st: &mut [u64; 12], block: &[u64; 8]| {\n        if batch_cap { trace_blocks.push(*block); }",
        "sponge absorb block",
    )
    seg = replace_once(
        seg,
        "    core::array::from_fn(|i| Goldilocks::from_u64_reduced(st[i]))",
        '''    let res: [Goldilocks; 4] = core::array::from_fn(|i| Goldilocks::from_u64_reduced(st[i]));
    drop(_batch_sup);
    if batch_cap {
        crate::fpga_trace::pl(
            init_cap.map(Goldilocks::to_canonical_u64),
            &trace_blocks,
            res.map(Goldilocks::to_canonical_u64),
        );
    }
    res''',
        "sponge return",
    )
    sp = sp[:a] + seg + sp[b:]

    # Mark squeeze_ext4_vec and squeeze_query_indices as parallel Poseidon2 counter batches
    sp = replace_once(
        sp,
        "    pub fn squeeze_ext4_vec(&mut self, label: &[u8], count: usize) -> Vec<GoldilocksExt4> {\n        (0..count).map(|_| self.squeeze_ext4(label)).collect()\n    }",
        "    pub fn squeeze_ext4_vec(&mut self, label: &[u8], count: usize) -> Vec<GoldilocksExt4> {\n        let _bg = (count >= 2).then(crate::fpga_trace::enter_p2_batch);\n        (0..count).map(|_| self.squeeze_ext4(label)).collect()\n    }",
        "squeeze_ext4_vec batch",
    )
    sp = replace_once(
        sp,
        "        if let TranscriptBackend::Poseidon2 { p2_chain } = self.backend {\n            assert!(half_domain_len <= (1usize << 28));",
        "        if let TranscriptBackend::Poseidon2 { p2_chain } = self.backend {\n            let _bg = crate::fpga_trace::enter_p2_batch();\n            assert!(half_domain_len <= (1usize << 28));",
        "squeeze_query_indices batch",
    )
    sp_p.write_text(sp)

    # ------------------------------------------------------------------ 4. field.rs
    fl_p = agg / "field.rs"
    fl = fl_p.read_text()
    fl = fl.replace("self.mul_add(rhs, Self::ZERO)", "self.const_mul_add(rhs, Self::ZERO)")
    fl = replace_once(
        fl,
        "    pub const fn mul_add(self, rhs: Self, addend: Self) -> Self {",
        '''    pub fn mul_add(self, rhs: Self, addend: Self) -> Self {
        let out = self.const_mul_add(rhs, addend);
        crate::fpga_trace::ext_mac(self, rhs, addend, out);
        out
    }

    #[inline(always)]
    pub const fn const_mul_add(self, rhs: Self, addend: Self) -> Self {''',
        "field mul_add",
    )
    fl = replace_once(
        fl,
        "impl Mul for GoldilocksExt4 {\n    type Output = Self;\n    #[inline(always)]\n    fn mul(self, rhs: Self) -> Self {\n        self.const_mul(rhs)\n    }\n}\n\nimpl MulAssign for GoldilocksExt4 {\n    #[inline(always)]\n    fn mul_assign(&mut self, rhs: Self) {\n        *self = self.const_mul(rhs);\n    }\n}",
        "impl Mul for GoldilocksExt4 {\n    type Output = Self;\n    #[inline(always)]\n    fn mul(self, rhs: Self) -> Self {\n        self.mul_add(rhs, Self::ZERO)\n    }\n}\n\nimpl MulAssign for GoldilocksExt4 {\n    #[inline(always)]\n    fn mul_assign(&mut self, rhs: Self) {\n        *self = self.mul_add(rhs, Self::ZERO);\n    }\n}",
        "field Mul/MulAssign",
    )
    fl = replace_once(
        fl,
        "pub fn mle_eval_ext4(table: &[GoldilocksExt4], point: &[GoldilocksExt4]) -> GoldilocksExt4 {\n    assert_eq!(table.len(), 1usize << point.len());",
        '''pub fn mle_eval_ext4(table: &[GoldilocksExt4], point: &[GoldilocksExt4]) -> GoldilocksExt4 {
    assert_eq!(table.len(), 1usize << point.len());
    if crate::fpga_trace::active() && (1..=11).contains(&point.len()) {
        let _g = crate::fpga_trace::suppress();
        let eq_tab = build_eq_table_ext4(point);
        let mut acc = GoldilocksExt4::ZERO;
        for (&w, &e) in table.iter().zip(eq_tab.iter()) {
            acc += e * w;
        }
        drop(_g);
        crate::fpga_trace::fd(table, point, acc);
        return acc;
    }''',
        "mle_eval_ext4 FD",
    )
    fl_p.write_text(fl)

    # ------------------------------------------------------------------ 5. pcs.rs
    pcs_p = agg / "pcs.rs"
    pcs = pcs_p.read_text()

    # 5a. TC Canopy MultiProof (byte mode: TurboSHAKE256 & cSHAKE256)
    pcs = replace_once(
        pcs,
        "fn verify_canopy_multiproof_byte(\n    turbo: bool,\n    commitment: &CanopyCommitment,\n    sorted_leaves: &[(usize, [u8; 32])],\n    proof: &CanopyMultiProof,\n) -> bool {",
        '''fn verify_canopy_multiproof_byte(
    turbo: bool,
    commitment: &CanopyCommitment,
    sorted_leaves: &[(usize, [u8; 32])],
    proof: &CanopyMultiProof,
) -> bool {
    let _fpga_tc = crate::fpga_trace::suppress();
    if _fpga_tc.was_outer {
        crate::fpga_trace::tc(turbo, commitment.log_leaves, &commitment.root, sorted_leaves, &proof.auth_siblings);
    }''',
        "verify_canopy_multiproof_byte TC",
    )

    # 5b. PC Canopy MultiProof (Poseidon2 Steiner levels) + PL leaf sponges
    pcs = replace_once(
        pcs,
        "pub fn poseidon2_round0_leaf(",
        "pub fn poseidon2_round0_leaf_inner(",
        "poseidon2_round0_leaf rename",
    )
    pcs = replace_once(
        pcs,
        "pub fn poseidon2_round0_leaf_inner(\n    leaf_idx: u32,\n    salt: &[u8; 16],\n    num_polys: usize,\n    vals: &[Goldilocks],\n) -> [u8; 32] {",
        '''pub fn poseidon2_round0_leaf(
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {
    let _bg = crate::fpga_trace::enter_p2_batch();
    poseidon2_round0_leaf_inner(leaf_idx, salt, num_polys, vals)
}

pub fn poseidon2_round0_leaf_inner(
    leaf_idx: u32,
    salt: &[u8; 16],
    num_polys: usize,
    vals: &[Goldilocks],
) -> [u8; 32] {''',
        "poseidon2_round0_leaf wrapper",
    )
    pcs = replace_once(
        pcs,
        "pub fn poseidon2_ext4_leaf(stage_idx: u8, leaf_idx: u32, vals: &[GoldilocksExt4]) -> [u8; 32] {",
        "pub fn poseidon2_ext4_leaf(stage_idx: u8, leaf_idx: u32, vals: &[GoldilocksExt4]) -> [u8; 32] {\n    let _bg = crate::fpga_trace::enter_p2_batch();",
        "poseidon2_ext4_leaf batch",
    )

    old_p2_mp = '''    let key = poseidon2_canopy_key(stage_idx, commitment.log_leaves);
    let mut active: Vec<(usize, [u8; 32])> =
        sorted_leaves.iter().map(|&(idx, h)| (n + idx, h)).collect();
    let mut sib_cursor = 0usize;
    for _ in 0..log_leaves {
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let (u, hu) = active[k];
            let sib = u ^ 1;
            let hsib = if k + 1 < active.len() && active[k + 1].0 == sib {
                let coalesced = active[k + 1].1;
                k += 2;
                coalesced
            } else {
                let Some(&supplied) = proof.auth_siblings.get(sib_cursor) else {
                    return false;
                };
                sib_cursor += 1;
                k += 1;
                supplied
            };
            let Some(pair) = qsag_whir_verified::step_merkle_pair_order(u as u64, 0, hu, hsib)
            else {
                return false;
            };
            let Some(parent) = poseidon2_canopy_node(key, (u >> 1) as u32, &pair.left, &pair.right)
            else {
                return false;
            };
            active[write] = (u >> 1, parent);
            write += 1;
        }
        active.truncate(write);
    }'''
    new_p2_mp = '''    let key = poseidon2_canopy_key(stage_idx, commitment.log_leaves);
    let _fpga_pc = crate::fpga_trace::suppress();
    let mut pc_levels: Vec<Vec<(u32, [u8; 32], [u8; 32], [u8; 32])>> = Vec::with_capacity(log_leaves);
    let mut active: Vec<(usize, [u8; 32])> =
        sorted_leaves.iter().map(|&(idx, h)| (n + idx, h)).collect();
    let mut sib_cursor = 0usize;
    for _ in 0..log_leaves {
        let mut lvl_nodes = Vec::new();
        let mut write = 0usize;
        let mut k = 0usize;
        while k < active.len() {
            let (u, hu) = active[k];
            let sib = u ^ 1;
            let hsib = if k + 1 < active.len() && active[k + 1].0 == sib {
                let coalesced = active[k + 1].1;
                k += 2;
                coalesced
            } else {
                let Some(&supplied) = proof.auth_siblings.get(sib_cursor) else {
                    return false;
                };
                sib_cursor += 1;
                k += 1;
                supplied
            };
            let Some(pair) = qsag_whir_verified::step_merkle_pair_order(u as u64, 0, hu, hsib)
            else {
                return false;
            };
            let Some(parent) = poseidon2_canopy_node(key, (u >> 1) as u32, &pair.left, &pair.right)
            else {
                return false;
            };
            if _fpga_pc.was_outer {
                lvl_nodes.push(((u >> 1) as u32, pair.left, pair.right, parent));
            }
            active[write] = (u >> 1, parent);
            write += 1;
        }
        if _fpga_pc.was_outer {
            pc_levels.push(lvl_nodes);
        }
        active.truncate(write);
    }
    drop(_fpga_pc);
    if crate::fpga_trace::active() {
        crate::fpga_trace::pc(key, &pc_levels);
    }'''
    pcs = replace_once(pcs, old_p2_mp, new_p2_mp, "poseidon2 canopy multiproof")

    # 5c. Batch quadratic sumcheck round
    pcs = replace_once(
        pcs,
        "        let r = transcript.squeeze_ext4(b\"PCS_BATCH_SC_CHAL\");\n        claim = eval_quadratic_wire(wire, claim, r);",
        '''        let r = transcript.squeeze_ext4(b"PCS_BATCH_SC_CHAL");
        let prev_claim = claim;
        let _sc_g = crate::fpga_trace::suppress();
        claim = eval_quadratic_wire(wire, claim, r);
        drop(_sc_g);
        if crate::fpga_trace::active() {
            let c1 = prev_claim - (wire[0] + wire[0]) - wire[1];
            crate::fpga_trace::sc(&[wire[0], c1, wire[1]], prev_claim, r, claim);
        }''',
        "pcs batch sumcheck",
    )
    pcs_p.write_text(pcs)

    # ------------------------------------------------------------------ 6. zk_hem/protocol.rs
    pr_p = agg / "zk_hem/protocol.rs"
    pr = pr_p.read_text()
    pr = replace_once(
        pr,
        "        let c = tr.squeeze_ext4(label);\n        claim = eval_poly(round, c);\n        point.push(c);",
        '''        let c = tr.squeeze_ext4(label);
        let prev = claim;
        let _sc_g = crate::fpga_trace::suppress();
        claim = eval_poly(round, c);
        drop(_sc_g);
        if crate::fpga_trace::active() {
            crate::fpga_trace::sc(round, prev, c, claim);
        }
        point.push(c);''',
        "protocol verify_sumcheck",
    )
    pr = replace_once(
        pr,
        "        let c = tr.squeeze_ext4(b\"HOLO_MAT_ROUND\");\n        mat_claim = eval_poly(round, c);\n        r_mat.push(c);",
        '''        let c = tr.squeeze_ext4(b"HOLO_MAT_ROUND");
        let prev = mat_claim;
        let _sc_g = crate::fpga_trace::suppress();
        mat_claim = eval_poly(round, c);
        drop(_sc_g);
        if crate::fpga_trace::active() {
            crate::fpga_trace::sc(round, prev, c, mat_claim);
        }
        r_mat.push(c);''',
        "protocol mat_rounds",
    )
    pr = replace_once(
        pr,
        "                let c = tr.squeeze_ext4(b\"HOLO_GKR_ROUND\");\n                sc_claim = eval_poly(round, c);\n                u_star.push(c);",
        '''                let c = tr.squeeze_ext4(b"HOLO_GKR_ROUND");
                let prev = sc_claim;
                let _sc_g = crate::fpga_trace::suppress();
                sc_claim = eval_poly(round, c);
                drop(_sc_g);
                if crate::fpga_trace::active() {
                    crate::fpga_trace::sc(round, prev, c, sc_claim);
                }
                u_star.push(c);''',
        "protocol gkr_rounds",
    )
    pr_p.write_text(pr)

    # ------------------------------------------------------------------ 7. recursive_fold.rs
    rf_p = agg / "recursive_fold.rs"
    rf = rf_p.read_text()
    rf = replace_once(
        rf,
        "        let r = t.squeeze_ext4(b\"R\");\n        claim = eval_univariate_ext4(poly, r);\n        rx.push(r);",
        '''        let r = t.squeeze_ext4(b"R");
        let prev = claim;
        let _sc_g = crate::fpga_trace::suppress();
        claim = eval_univariate_ext4(poly, r);
        drop(_sc_g);
        if crate::fpga_trace::active() {
            crate::fpga_trace::sc(poly, prev, r, claim);
        }
        rx.push(r);''',
        "duet_fold sumcheck",
    )
    rf += '''
#[cfg(test)]
mod fpga_export_duet {
    use super::*;
    #[test]
    fn export_real_duet_fold_trace() {
        let Ok(out_dir) = std::env::var("QSAG_FPGA_OUT_DIR") else { return; };
        let mk = |seed: u64| {
            let e = |k: u64| {
                E::from_limbs(core::array::from_fn(|i| {
                    F::from_u64_reduced(seed * 97 + k + 17 * i as u64)
                }))
            };
            let mut s = DuetFoldStatement {
                v0: e(3),
                v1: e(7),
                theta: e(11),
                alpha: e(13),
                beta: e(19),
                inv_two: F::from_u64_reduced(2).inv(),
                inv_two_x: F::from_u64_reduced(14 + 2 * seed).inv(),
                x_sq: F::from_u64_reduced((7 + seed) * (7 + seed)),
                claimed: E::ZERO,
            };
            let even = (s.v0 + s.v1).mul_base(s.inv_two);
            let odd = (s.v0 - s.v1).mul_base(s.inv_two_x);
            s.claimed = odd + (s.alpha + s.beta.mul_base(s.x_sq)) * (even + s.theta * odd);
            s
        };
        let statements = [mk(0), mk(1), mk(2), mk(3)];
        let context = [0x42u8; 32];
        let salt = [0x99u8; 32];
        let proof = prove_duet_folds(&context, &statements, &salt).expect("valid DuetFold proof");
        let trace_path = std::format!("{out_dir}/real_duet_fold_trace.txt");
        crate::fpga_trace::start(&trace_path);
        assert!(verify_duet_folds(&context, &statements, &proof));
        crate::fpga_trace::stop();
        std::println!("EXPORTED_DUET_FOLD statements=4 trace={trace_path}");
    }
}
'''
    rf_p.write_text(rf)

    # ------------------------------------------------------------------ 8. recursive.rs (both QSAGSTA1 regimes!)
    rc_p = agg / "recursive.rs"
    rc = rc_p.read_text()
    rc = replace_once(
        rc,
        "                &root_hologram,\n                root_z,\n                SUBTREE_ROOT_LABEL,",
        "                &root_hologram,\n                root_z.clone(),\n                SUBTREE_ROOT_LABEL,",
        "clone root_z",
    )
    needle = '''        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &proof
        ));'''
    export_block = '''        assert!(verify_succinct_subtree_aggregate_against_roster_root(
            root_vk, &statement, &proof
        ));
        if let Ok(out_dir) = std::env::var("QSAG_FPGA_OUT_DIR") {
            let ts_wire = proof.to_bytes();
            assert_eq!(&ts_wire[..8], b"QSAGSTA1");
            std::fs::write(std::format!("{out_dir}/real_qsagsta1_ts.bin"), &ts_wire).unwrap();
            let ts_decoded = SuccinctSubtreeAggregate::from_bytes_canonical(root_vk, &ts_wire).unwrap();
            let ts_trace = std::format!("{out_dir}/real_qsagsta1_ts_trace.txt");
            crate::fpga_trace::start(&ts_trace);
            assert!(verify_succinct_subtree_aggregate_against_roster_root(
                root_vk, &statement, &ts_decoded
            ));
            crate::fpga_trace::stop();
            std::println!("EXPORTED_QSAGSTA1_TS bytes={} trace={ts_trace}", ts_wire.len());

            // Also prove, serialize, canonical-decode, and trace Role-2 Poseidon2 QSAGSTA1!
            let p2_hologram = protocol::ShapeHologram::compile_native(
                &root_shape,
                WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
            ).unwrap();
            let p2_vk = p2_hologram.verifier_key();
            let p2_proof = SuccinctSubtreeAggregate {
                total_active_signers: 2,
                min_key_idx: 1,
                max_key_idx: 4,
                total_active_weight: 5,
                proof: protocol::prove_public_hologram(
                    &root_shape,
                    &p2_hologram,
                    root_z.clone(),
                    SUBTREE_ROOT_LABEL,
                    &[65; 32],
                ).unwrap(),
            };
            let p2_wire = p2_proof.to_bytes();
            assert_eq!(&p2_wire[..8], b"QSAGSTA1");
            std::fs::write(std::format!("{out_dir}/real_qsagsta1_p2.bin"), &p2_wire).unwrap();
            let p2_decoded = SuccinctSubtreeAggregate::from_bytes_canonical(p2_vk, &p2_wire).unwrap();
            let p2_trace = std::format!("{out_dir}/real_qsagsta1_p2_trace.txt");
            crate::fpga_trace::start(&p2_trace);
            assert!(verify_succinct_subtree_aggregate_against_roster_root(
                p2_vk, &statement, &p2_decoded
            ));
            crate::fpga_trace::stop();
            std::println!("EXPORTED_QSAGSTA1_P2 bytes={} trace={p2_trace}", p2_wire.len());
        }'''
    rc = replace_once(rc, needle, export_block, "recursive QSAGSTA1 both regimes")
    rc_p.write_text(rc)
    print(f"Successfully instrumented isolated scratch repo at {repo}")

if __name__ == "__main__":
    main()
