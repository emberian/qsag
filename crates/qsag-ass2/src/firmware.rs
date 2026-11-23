//! The four QSAG microcode programs, their mailbox ABI and host-side runners.
//!
//! Each `fw_*` builder returns a standalone image. Load it at PC 0, populate its mailbox and
//! start it: it runs straight through to `HALT` and leaves its status in `R4` (`1` accept,
//! `0` reject). All addresses are byte addresses in the unified SRAM, every mailbox word is
//! an aligned little-endian `u64`, and `R0` is the only register value an image assumes.
//! The caller supplies the trusted protocol context (Fiat-Shamir midstate, frame, expected
//! commitments).
//!
//! No image branches on, jumps through or addresses memory with anything derived from a
//! secret mailbox field: the program counter trace, the cycle count and every memory address
//! are functions of the public fields alone. The `*Input::install` methods tag the fields
//! the way the DIT auditor should assume them, and [`run_to_halt`] runs in
//! [`DitMode::Trap`], so a run that returns `Ok` had no violation.

use crate::isa::{AluOp, AluiOp, Ass2Insn as I, BrOp, Imm20Mode, LoadMode, StoreMode, encode_insn};
use crate::vm::{Ass2Vm, DitMode, MemRangeError, RunExit, Taint};
use alloc::vec::Vec;
use core::fmt;

/// Size of the SRAM the images are laid out for: 8 KiB, 1024 words.
pub const SRAM_BYTES: usize = 0x2000;
/// Input and output base addresses shared by the four independent images.
pub const INPUT: usize = 0x1000;
pub const OUTPUT: usize = 0x1800;
/// Step budget of [`run_to_halt`]. The longest image (a depth-16 canopy path) retires
/// fewer than 4,000 instructions.
pub const STEP_LIMIT: u64 = 1 << 16;
/// Bytes in a `zk-Hem v2` digest.
pub const DIGEST_BYTES: usize = 50;
/// The Goldilocks prime `2^64 - 2^32 + 1`.
const GL_PRIME: u64 = 0xFFFF_FFFF_0000_0001;
/// `CMP` flags for unsigned `R[ra] >= R[rb]` (`EQ | GT`).
const GEU: u8 = 0b0011;

/// Mailbox addresses. Each 50-byte digest occupies seven words, with only the low
/// sixteen bits of the last word significant. Output padding is always zero.
pub mod abi {
    use super::{INPUT, OUTPUT};
    pub mod sumcheck {
        use super::*;
        pub const COEFFS: usize = INPUT;
        pub const CLAIM: usize = COEFFS + 10 * 40;
        pub const MIDSTATE: usize = CLAIM + 40;
        /// Exactly one pre-padded 136-byte rate block. XOR 0x07 after the frame
        /// and 0x80 at byte 135 (both bits can share the final byte).
        pub const BLOCK: usize = MIDSTATE + 200;
        pub const EXPECTED: usize = BLOCK + 136;
        pub const VALUE: usize = OUTPUT;
        pub const DIGEST: usize = VALUE + 40;
    }
    pub mod canopy {
        use super::*;
        pub const DEPTH: usize = INPUT; // public u8, 1..=16
        pub const STAGE: usize = INPUT + 1; // u8
        pub const INDEX: usize = INPUT + 8; // u64, must be < 2^depth
        pub const LEAF: usize = INPUT + 16;
        pub const EXPECTED: usize = LEAF + 56;
        pub const SIBLINGS: usize = EXPECTED + 56; // depth slots of 56 B, bottom-up
        /// Largest accepted depth, and the number of sibling slots.
        pub const MAX_DEPTH: usize = 16;
        pub const ROOT: usize = OUTPUT;
        pub const MIDSTATE_SCRATCH: usize = 0x1900; // 200 B, generated on entry
    }
    pub mod jive {
        use super::*;
        pub const LEFT: usize = INPUT;
        pub const RIGHT: usize = LEFT + 56;
        pub const TWEAK: usize = RIGHT + 56;
        pub const DIGEST: usize = OUTPUT;
    }
    pub mod cth {
        use super::*;
        pub const VALUES: usize = INPUT; // four LE u128
        pub const WEIGHTS: usize = VALUES + 64; // four pairs (w0,w1) of LE u128
        pub const TAGS: usize = WEIGHTS + 128; // two LE u128
        pub const START: usize = TAGS + 32; // four canonical limbs
        pub const SEED: usize = START + 32; // four canonical limbs
        pub const LAYER: usize = SEED + 32; // u64 < 64
        pub const TREE: usize = LAYER + 8; // full u64
        pub const KP: usize = TREE + 8; // u64 < 2^20
        pub const CHAIN: usize = KP + 8; // u64 < 256
        pub const DIGIT: usize = CHAIN + 8; // u64 in 0..=3
        /// Chain value after `DIGIT` steps, or four zero words when the MAC check rejects.
        pub const END: usize = OUTPUT;
        pub const STATUS: usize = END + 32;
    }
}

// The encoder checks every immediate. Offsets in these helpers are bytes;
// only the final ISA fields use scaled offsets. R3 is the packing temporary.
#[derive(Default)]
struct Image(Vec<u8>);
impl Image {
    fn emit(&mut self, i: I) {
        let word = encode_insn(&i).expect("valid firmware instruction");
        self.0.extend_from_slice(&word.to_le_bytes());
    }
    fn finish(mut self) -> Vec<u8> {
        self.emit(I::Halt);
        assert!(self.0.len() <= INPUT, "code overlaps mailbox");
        self.0
    }
    fn imm(&mut self, rd: u8, value: u64) {
        if value < 1 << 20 {
            self.emit(I::Imm20 {
                mode: Imm20Mode::Movz20,
                rd,
                imm20: value as u32,
            });
        } else {
            for n in (0..4).rev() {
                self.ui(
                    AluiOp::Slk16,
                    rd,
                    if n == 3 { 0 } else { rd },
                    (value >> (16 * n)) as u16,
                );
            }
        }
    }
    fn ui(&mut self, op: AluiOp, rd: u8, ra: u8, imm16: u16) {
        self.emit(I::Alui { op, rd, ra, imm16 });
    }
    fn lut(&mut self, m: u8, rd: u8, ra: u8, rb: u8) {
        self.emit(I::Lut4 { rd, ra, rb, m });
    }
    fn gl_add(&mut self, rd: u8, ra: u8, rb: u8) {
        self.emit(I::GlAdd { rd, ra, rb });
    }
    fn ld_from(&mut self, rd: u8, ra: u8, offset: usize) {
        assert_eq!(offset % 8, 0);
        self.emit(I::Load {
            mode: LoadMode::Ld64,
            rd,
            ra,
            simm16: (offset / 8).try_into().unwrap(),
        });
    }
    fn ld(&mut self, rd: u8, addr: usize) {
        self.ld_from(rd, 0, addr);
    }
    fn ldb(&mut self, rd: u8, addr: usize) {
        self.emit(I::Load {
            mode: LoadMode::Ldbu,
            rd,
            ra: 0,
            simm16: addr.try_into().unwrap(),
        });
    }
    fn st(&mut self, rs: u8, addr: usize) {
        assert_eq!(addr % 8, 0);
        self.emit(I::Store {
            mode: StoreMode::St64,
            rs,
            ra: 0,
            simm16: (addr / 8).try_into().unwrap(),
        });
    }
    fn sload(&mut self, first: u8, count: u8, ra: u8, offset: usize) {
        assert_eq!(offset % 8, 0);
        for i in 0..count {
            self.emit(I::Sld64 {
                sidx: first + i,
                ra,
                off8: (offset / 8 + usize::from(i)).try_into().unwrap(),
            });
        }
    }
    fn get(&mut self, rd: u8, sidx: u8) {
        self.emit(I::Sget { rd, sidx });
    }
    fn put(&mut self, sidx: u8, ra: u8) {
        self.emit(I::Sput { sidx, ra });
    }
    // OR a word mismatch into R4, which accumulates failures until status().
    fn compare_lane(&mut self, lane: u8, expected: usize, tail16: bool) {
        self.get(5, lane);
        self.ld(6, expected);
        self.lut(6, 6, 5, 6);
        if tail16 {
            self.ui(AluiOp::Andi, 6, 6, 0xffff);
        }
        self.lut(14, 4, 4, 6);
    }
    fn status(&mut self) {
        self.emit(I::Cmp {
            rd: 4,
            ra: 4,
            rb: 0,
            flags: 1,
        });
    }
    // OR `R[ra] >= R[bound]` into R4.
    fn reject_at_or_above(&mut self, ra: u8, bound: u8) {
        self.emit(I::Cmp {
            rd: 6,
            ra,
            rb: bound,
            flags: GEU,
        });
        self.lut(14, 4, 4, 6);
    }
    fn store_digest(&mut self, dst: usize) {
        for i in 0..7 {
            self.get(5, i);
            if i == 6 {
                self.ui(AluiOp::Andi, 5, 5, 0xffff);
            }
            self.st(5, dst + 8 * usize::from(i));
        }
    }
    // All 400 bits: six full words (bytes 0..48) and the low sixteen bits of the seventh
    // (bytes 48 and 49).
    fn compare_digest(&mut self, expected: usize) {
        for i in 0..7 {
            self.compare_lane(i, expected + 8 * usize::from(i), i == 6);
        }
    }
    fn turbo(&mut self) {
        self.emit(I::KeccakF1600 { rounds: 12 });
    }
    // XOR the low 'bytes' of an already zero-extended register into an
    // unaligned Keccak byte position. All shifts and lane indices are static.
    fn xor_at(&mut self, pos: usize, ra: u8, bytes: usize) {
        assert!(ra != 3 && (1..=8).contains(&bytes) && pos + bytes <= 136);
        let lane = (pos / 8) as u8;
        let shift = ((pos % 8) * 8) as u16;
        if shift == 0 {
            self.emit(I::Sxor { sidx: lane, ra });
            return;
        }
        self.ui(AluiOp::Shli, 3, ra, shift);
        self.emit(I::Sxor { sidx: lane, ra: 3 });
        if pos % 8 + bytes > 8 {
            self.ui(AluiOp::Shri, 3, ra, 64 - shift);
            self.emit(I::Sxor {
                sidx: lane + 1,
                ra: 3,
            });
        }
    }
    fn pad_and_permute(&mut self, msg_len: usize) {
        self.imm(5, 7);
        self.xor_at(msg_len, 5, 1);
        self.imm(5, 0x80);
        self.xor_at(135, 5, 1);
        self.turbo();
    }
}

/// Check a canonical degree-nine polynomial's round sum and all 400 squeeze bits, then
/// evaluate the polynomial at the squeezed point.
///
/// The round sum `p(0) + p(1) = 2 c0 + c1 + .. + c9` must equal `CLAIM` limb for limb. The
/// image absorbs `BLOCK` into `MIDSTATE`, runs `KECCAK.F1600 12` and compares the first 50
/// squeezed bytes with `EXPECTED`. The evaluation point is the first five squeezed words and
/// `VALUE` is the Horner evaluation there.
///
/// A v2 transcript redraws a `SQUEEZE_E` attempt that holds a limb `>= p`, so such a draw is
/// never a challenge: the image rejects it. Choosing the attempt (and framing and binding
/// the transcript) is upstream. On a reject, `VALUE` is the evaluation at the reduced draw
/// and is not a protocol value.
pub fn fw_zkhem_v2_fp5_sumcheck() -> Vec<u8> {
    use abi::sumcheck::*;
    let mut a = Image::default();
    a.imm(1, INPUT as u64);
    a.imm(4, 0);
    a.sload(0, 5, 1, 0);
    a.emit(I::Fp5Add {
        ed: 0,
        ea: 0,
        eb: 0,
    });
    for i in 1..10 {
        a.sload(5, 5, 1, 40 * i);
        a.emit(I::Fp5Add {
            ed: 0,
            ea: 0,
            eb: 1,
        });
    }
    for i in 0..5 {
        a.compare_lane(i, CLAIM + 8 * usize::from(i), false);
    }
    a.sload(0, 25, 1, MIDSTATE - INPUT);
    for i in 0..17 {
        a.ld(5, BLOCK + 8 * usize::from(i));
        a.emit(I::Sxor { sidx: i, ra: 5 });
    }
    a.turbo();
    a.store_digest(DIGEST);
    a.compare_digest(EXPECTED);
    a.imm(7, GL_PRIME);
    for i in 0..5 {
        a.get(5, i);
        a.reject_at_or_above(5, 7);
    }
    a.status();
    for i in 0..5 {
        a.get(5, i);
        a.gl_add(5, 5, 0);
        a.put(i, 5);
    }
    // E0 = x, E1 = Horner accumulator, E2 = next coefficient.
    a.sload(5, 5, 1, 9 * 40);
    for i in (0..9).rev() {
        a.emit(I::Fp5Mul {
            ed: 1,
            ea: 1,
            eb: 0,
        });
        a.sload(10, 5, 1, 40 * i);
        a.emit(I::Fp5Add {
            ed: 1,
            ea: 1,
            eb: 2,
        });
    }
    a.imm(2, VALUE as u64);
    for i in 0..5 {
        a.emit(I::Sst64 {
            sidx: 5 + i,
            ra: 2,
            off8: i as i8,
        });
    }
    a.finish()
}

/// Verify one bottom-up authentication path. Each iteration branches on the
/// remaining public depth and advances its sibling pointer by 56 bytes.
/// All index-dependent routing is by SEL. Invalid depth returns R4=0 before
/// reading a path. A valid depth always produces the computed root in SRAM.
///
/// An internal node hashes 105 bytes (tag `0`, the parent's 32-bit heap index, the two
/// 50-byte children) and the root hashes 53 bytes (tag `1`, stage, depth, the top node),
/// each as one `KECCAK.F1600 12` block from the tree-customization midstate.
pub fn fw_zkhem_v2_canopy50_verify() -> Vec<u8> {
    use abi::canopy::*;
    let mut a = Image::default();
    // R8 = heap node, R9 = levels remaining, R10 = sibling slot, R11 = midstate.
    a.imm(4, 0);
    a.ldb(9, DEPTH);
    a.emit(I::Br {
        op: BrOp::Bnez,
        cond: 9,
        off20: 1,
    });
    a.emit(I::Halt);
    a.imm(5, MAX_DEPTH as u64);
    a.emit(I::Cmp {
        rd: 5,
        ra: 9,
        rb: 5,
        flags: 2,
    });
    a.emit(I::Br {
        op: BrOp::Beqz,
        cond: 5,
        off20: 1,
    });
    a.emit(I::Halt);
    a.imm(5, 1);
    a.emit(I::Alu {
        op: AluOp::Shl,
        rd: 5,
        ra: 5,
        rb: 9,
    });
    a.ld(8, INDEX);
    a.emit(I::Cmp {
        rd: 12,
        ra: 5,
        rb: 8,
        flags: 2,
    }); // index in range
    a.emit(I::Alu {
        op: AluOp::Add,
        rd: 8,
        ra: 8,
        rb: 5,
    });
    a.imm(10, SIBLINGS as u64);
    a.imm(11, MIDSTATE_SCRATCH as u64);

    // bytepad(encode_string("") || encode_string(tree customization), 136).
    // Materialize it once, then reuse its 25 permuted lanes for every node.
    let domain = b"QSAG.ZKHEM2.TREE/v1";
    let mut prefix = [0u8; 32];
    prefix[..6].copy_from_slice(&[1, 136, 1, 0, 1, (domain.len() * 8) as u8]);
    prefix[6..6 + domain.len()].copy_from_slice(domain);
    a.emit(I::Szero);
    for (i, word) in prefix.as_chunks::<8>().0.iter().enumerate() {
        a.imm(5, u64::from_le_bytes(*word));
        a.put(i as u8, 5);
    }
    a.turbo();
    for i in 0..25 {
        a.emit(I::Sst64 {
            sidx: i,
            ra: 11,
            off8: i as i8,
        });
    }
    for i in 0..7 {
        a.ld(5, LEAF + 8 * i);
        a.st(5, ROOT + 8 * i);
    }

    let loop_pc = a.0.len() / 4;
    a.sload(0, 25, 11, 0);
    a.ui(AluiOp::Andi, 1, 8, 1);
    a.ui(AluiOp::Shri, 8, 8, 1);
    a.emit(I::Bextu {
        rd: 5,
        ra: 8,
        idx: 0,
        len: 4,
    });
    a.xor_at(1, 5, 4);
    for i in 0..7 {
        let bytes = if i == 6 { 2 } else { 8 };
        a.ld(5, ROOT + 8 * i);
        a.ld_from(6, 10, 8 * i);
        if bytes == 2 {
            a.ui(AluiOp::Andi, 5, 5, 0xffff);
            a.ui(AluiOp::Andi, 6, 6, 0xffff);
        }
        a.emit(I::Sel {
            rd: 7,
            ra: 5,
            rb: 6,
            rc: 1,
        });
        a.xor_at(5 + 8 * i, 7, bytes);
        a.emit(I::Sel {
            rd: 7,
            ra: 6,
            rb: 5,
            rc: 1,
        });
        a.xor_at(55 + 8 * i, 7, bytes);
    }
    a.pad_and_permute(105);
    a.store_digest(ROOT);
    a.ui(AluiOp::Addiu, 10, 10, 56);
    a.ui(AluiOp::Addi, 9, 9, 0xffff);
    let off20 = loop_pc as i32 - (a.0.len() / 4) as i32 - 1;
    a.emit(I::Br {
        op: BrOp::Bnez,
        cond: 9,
        off20,
    });

    a.sload(0, 25, 11, 0);
    a.imm(5, 1);
    a.xor_at(0, 5, 1);
    a.ldb(5, STAGE);
    a.xor_at(1, 5, 1);
    a.ldb(5, DEPTH);
    a.xor_at(2, 5, 1);
    for i in 0..7 {
        a.ld(5, ROOT + 8 * i); // store_digest already masked the tail
        a.xor_at(3 + 8 * i, 5, if i == 6 { 2 } else { 8 });
    }
    a.pad_and_permute(53);
    a.store_digest(ROOT);
    a.compare_digest(EXPECTED);
    a.status();
    a.lut(8, 4, 4, 12);
    a.finish()
}

/// Compress two seven-limb children with a two-limb tweak in one `POSEIDON2.GL24` call.
/// Accepts arbitrary u64 words, including noncanonical representatives of Goldilocks
/// elements. There is nothing to reject: `R4` is always `1`.
pub fn fw_poseidon2_gl24_jive() -> Vec<u8> {
    use abi::jive::*;
    let mut a = Image::default();
    a.emit(I::Szero);
    for i in 0..16 {
        a.ld(5, LEFT + 8 * usize::from(i));
        a.gl_add(5, 5, 0);
        a.put(i, 5);
    }
    for (i, value) in [
        (16, 16),
        (17, 8),
        (18, 7),
        (19, 0x4D52_4B4C_474C_3234),
        (23, 0x504F_5332_474C_3234),
    ] {
        a.imm(5, value);
        a.put(i, 5);
    }
    a.emit(I::Poseidon2Gl24);
    for i in 0..7 {
        let offset = 8 * usize::from(i);
        a.get(5, i);
        a.ld(6, LEFT + offset);
        a.gl_add(5, 5, 6);
        a.ld(6, RIGHT + offset);
        a.gl_add(6, 6, 6);
        a.gl_add(5, 5, 6);
        if i < 2 {
            a.ld(6, TWEAK + offset);
            a.gl_add(6, 6, 6);
            a.gl_add(6, 6, 6);
            a.gl_add(5, 5, 6);
        }
        a.st(5, DIGEST + offset);
    }
    a.imm(4, 1);
    a.finish()
}

/// Fold four opened field elements against two independent weight columns.
/// Tag j is XOR_i (value[i] * weights[i][j]) in the little-endian GF128 basis.
/// Advance the WOTS+C chain by its base-four digit: all three steps always run, and a
/// `SEL` on `digit > step` keeps or replaces the chain value, so the digit changes neither
/// the cycle count, the program counter trace nor any address.
/// The address coordinates must lie inside the injective packing (`LAYER < 64`,
/// `KP < 2^20`, `CHAIN < 256`) and the digit below four: anything else would hash under
/// another chain's tweak, and is rejected.
/// The chain value is released only on accept: after a tag mismatch or a range reject `END`
/// is four zero words. Store both results, wipe both register banks, and reload only the
/// released status bit.
pub fn fw_cth_gf128_and_wots() -> Vec<u8> {
    use abi::cth::*;
    let mut a = Image::default();
    a.imm(1, INPUT as u64);
    a.imm(4, 0);
    a.emit(I::Szero);
    // P0/P1 are tags, P2 is u_i, P3 is the weight and then the product.
    for i in 0..4 {
        a.sload(4, 2, 1, VALUES - INPUT + 16 * i);
        for j in 0..2u8 {
            a.sload(6, 2, 1, WEIGHTS - INPUT + 32 * i + 16 * usize::from(j));
            a.emit(I::Gf128Mul {
                pd: 3,
                pa: 2,
                pb: 3,
            });
            a.emit(I::Gf128Xor {
                pd: j,
                pa: j,
                pb: 3,
            });
        }
    }
    for i in 0..4 {
        a.compare_lane(i, TAGS + 8 * usize::from(i), false);
    }
    for (field, bound) in [(LAYER, 64), (KP, 1 << 20), (CHAIN, 256), (DIGIT, 4)] {
        a.ld(5, field);
        a.imm(7, bound);
        a.reject_at_or_above(5, 7);
    }
    a.status();

    // R8..11 hold the selected chain, canonical from here on. S12..15 save the tweak
    // across GL12.
    for i in 0..4 {
        a.ld(8 + i, START + 8 * usize::from(i));
        a.gl_add(8 + i, 8 + i, 0);
    }
    a.ld(12, DIGIT);
    a.imm(5, 0x5153_4147_5753_5450);
    a.put(12, 5);
    a.ld(13, LAYER);
    a.ui(AluiOp::Shli, 13, 13, 44);
    a.ld(5, KP);
    a.ui(AluiOp::Shli, 5, 5, 16);
    a.lut(14, 13, 13, 5);
    a.ld(5, CHAIN);
    a.ui(AluiOp::Shli, 5, 5, 4);
    a.lut(14, 13, 13, 5);
    a.ld(5, TREE);
    a.emit(I::Bextu {
        rd: 6,
        ra: 5,
        idx: 0,
        len: 4,
    });
    a.put(14, 6);
    a.ui(AluiOp::Shri, 6, 5, 32);
    a.put(15, 6);
    for step in 0..3 {
        a.ui(AluiOp::Ori, 5, 13, step);
        a.put(13, 5);
        for i in 0..4 {
            a.put(i, 8 + i);
            a.ld(5, SEED + 8 * usize::from(i));
            a.put(4 + i, 5);
            a.get(5, 12 + i);
            a.put(8 + i, 5);
        }
        a.emit(I::Poseidon2Gl12);
        a.imm(5, step.into());
        a.emit(I::Cmp {
            rd: 7,
            ra: 12,
            rb: 5,
            flags: 2,
        });
        for i in 0..4 {
            a.get(5, i);
            a.gl_add(5, 5, 8 + i);
            a.ld(6, SEED + 8 * usize::from(i));
            a.gl_add(6, 6, 6);
            a.gl_add(5, 5, 6);
            a.get(6, 12 + i);
            a.gl_add(6, 6, 6);
            a.gl_add(6, 6, 6);
            a.gl_add(5, 5, 6);
            a.emit(I::Sel {
                rd: 8 + i,
                ra: 8 + i,
                rb: 5,
                rc: 7,
            });
        }
    }
    for i in 0..4 {
        // Check before reveal: R4 is 0 on a tag mismatch and selects the zero register.
        a.emit(I::Sel {
            rd: 8 + i,
            ra: 0,
            rb: 8 + i,
            rc: 4,
        });
        a.st(8 + i, END + 8 * usize::from(i));
    }
    a.st(4, STATUS);
    a.emit(I::Zeroize);
    a.ld(4, STATUS);
    a.finish()
}

/// Why a firmware run did not produce a result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FirmwareError {
    /// The image or a mailbox field does not fit the machine's memory.
    Mem(MemRangeError),
    /// More sibling digests than the canopy mailbox has slots.
    TooManySiblings { count: usize },
    /// Canopy sibling count disagrees with the declared path `depth`.
    SiblingDepthMismatch { depth: u8, count: usize },
    /// The machine stopped on something other than `HALT`: a trap, a DIT violation or the
    /// step limit.
    Exit(RunExit),
}
impl fmt::Display for FirmwareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mem(e) => e.fmt(f),
            Self::TooManySiblings { count } => {
                write!(
                    f,
                    "{count} sibling digests exceed the {} slots",
                    abi::canopy::MAX_DEPTH
                )
            }
            Self::SiblingDepthMismatch { depth, count } => {
                write!(f, "canopy depth {depth} requires {depth} siblings, got {count}")
            }
            Self::Exit(exit) => write!(f, "firmware stopped with {exit:?} instead of HALT"),
        }
    }
}
impl core::error::Error for FirmwareError {}
impl From<MemRangeError> for FirmwareError {
    fn from(e: MemRangeError) -> Self {
        Self::Mem(e)
    }
}

/// A reset machine with [`SRAM_BYTES`] of zeroed memory, `image` at PC 0 (non-empty, 32-bit
/// word-aligned, and confined below the [`INPUT`] mailbox region) and the DIT auditor in trap mode.
pub fn boot(image: &[u8]) -> Result<Ass2Vm, FirmwareError> {
    if image.is_empty() || !image.len().is_multiple_of(4) || image.len() > INPUT {
        return Err(FirmwareError::Mem(MemRangeError {
            addr: 0,
            len: image.len(),
        }));
    }
    let mut vm = Ass2Vm::new(SRAM_BYTES);
    vm.load_image(0, image)?;
    vm.dit_mode = DitMode::Trap;
    Ok(vm)
}

/// Run to `HALT` within [`STEP_LIMIT`] steps in [`DitMode::Trap`]. Any pre-existing or new
/// DIT violation, trap, or exhausted budget is an error.
pub fn run_to_halt(vm: &mut Ass2Vm) -> Result<(), FirmwareError> {
    vm.dit_mode = DitMode::Trap;
    if let Some(&v) = vm.violations.first() {
        return Err(FirmwareError::Exit(RunExit::DitViolation(v)));
    }
    match vm.run(STEP_LIMIT) {
        RunExit::Halted => Ok(()),
        exit => Err(FirmwareError::Exit(exit)),
    }
}

fn put_words(vm: &mut Ass2Vm, addr: usize, words: &[u64], tag: Taint) -> Result<(), MemRangeError> {
    for (i, word) in words.iter().enumerate() {
        vm.load_tainted((addr + 8 * i) as u64, &word.to_le_bytes(), tag)?;
    }
    Ok(())
}
fn put_wide(
    vm: &mut Ass2Vm,
    addr: usize,
    values: &[u128],
    tag: Taint,
) -> Result<(), MemRangeError> {
    for (i, value) in values.iter().enumerate() {
        vm.load_tainted((addr + 16 * i) as u64, &value.to_le_bytes(), tag)?;
    }
    Ok(())
}
fn get_words<const N: usize>(vm: &Ass2Vm, addr: usize) -> Result<[u64; N], MemRangeError> {
    let mut words = [0; N];
    for (i, word) in words.iter_mut().enumerate() {
        *word = vm.read_word((addr + 8 * i) as u64)?;
    }
    Ok(words)
}
fn get_digest(vm: &Ass2Vm, addr: usize) -> Result<[u8; DIGEST_BYTES], MemRangeError> {
    Ok(vm
        .read_bytes(addr as u64, DIGEST_BYTES)?
        .try_into()
        .expect("digest length"))
}

/// Mailbox of [`fw_zkhem_v2_fp5_sumcheck`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SumcheckInput {
    /// Coefficients `c0..c9`, low degree first, five limbs each. Secret.
    pub coeffs: [[u64; 5]; 10],
    /// Claimed round sum `p(0) + p(1)` as canonical limbs. Secret.
    pub claim: [u64; 5],
    /// Fiat-Shamir sponge state before the squeeze frame. Public.
    pub midstate: [u64; 25],
    /// The padded 136-byte squeeze frame. Secret: it carries the transcript chain value.
    pub block: [u8; 136],
    /// The 50 squeezed bytes the frame must produce. Public.
    pub expected: [u8; DIGEST_BYTES],
}
/// Result of [`fw_zkhem_v2_fp5_sumcheck`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SumcheckOutput {
    /// The round sum and all 400 squeezed bits matched and the draw was canonical.
    pub accepted: bool,
    /// The polynomial at the squeezed point, canonical limbs.
    pub value: [u64; 5],
    /// The 50 bytes the image squeezed.
    pub digest: [u8; DIGEST_BYTES],
}
impl SumcheckInput {
    pub fn install(&self, vm: &mut Ass2Vm) -> Result<(), FirmwareError> {
        use abi::sumcheck::*;
        for (i, c) in self.coeffs.iter().enumerate() {
            put_words(vm, COEFFS + 40 * i, c, Taint::Secret)?;
        }
        put_words(vm, CLAIM, &self.claim, Taint::Secret)?;
        put_words(vm, MIDSTATE, &self.midstate, Taint::Public)?;
        vm.load_tainted(BLOCK as u64, &self.block, Taint::Secret)?;
        vm.load_tainted(EXPECTED as u64, &self.expected, Taint::Public)?;
        Ok(())
    }
}
impl SumcheckOutput {
    pub fn read(vm: &Ass2Vm) -> Result<Self, FirmwareError> {
        use abi::sumcheck::*;
        Ok(Self {
            accepted: vm.regs[4] == 1,
            value: get_words(vm, VALUE)?,
            digest: get_digest(vm, DIGEST)?,
        })
    }
}
/// Boot, install, run and read [`fw_zkhem_v2_fp5_sumcheck`].
pub fn run_zkhem_v2_fp5_sumcheck(input: &SumcheckInput) -> Result<SumcheckOutput, FirmwareError> {
    let mut vm = boot(&fw_zkhem_v2_fp5_sumcheck())?;
    input.install(&mut vm)?;
    run_to_halt(&mut vm)?;
    SumcheckOutput::read(&vm)
}

/// Mailbox of [`fw_zkhem_v2_canopy50_verify`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanopyInput {
    /// Path length, `1..=16`. Public.
    pub depth: u8,
    /// Commitment stage bound into the root hash. Public.
    pub stage: u8,
    /// Leaf position, below `2^depth`. Secret.
    pub index: u64,
    /// The leaf digest. Secret.
    pub leaf: [u8; DIGEST_BYTES],
    /// The committed root. Secret.
    pub expected_root: [u8; DIGEST_BYTES],
    /// Sibling digests, bottom-up, at most 16. Secret.
    pub siblings: Vec<[u8; DIGEST_BYTES]>,
}
/// Result of [`fw_zkhem_v2_canopy50_verify`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CanopyOutput {
    /// The depth and index were in range and the recomputed root matched in all 400 bits.
    pub accepted: bool,
    /// The recomputed root. Not written when the depth is out of range.
    pub root: [u8; DIGEST_BYTES],
}
impl CanopyInput {
    pub fn install(&self, vm: &mut Ass2Vm) -> Result<(), FirmwareError> {
        use abi::canopy::*;
        if self.siblings.len() > MAX_DEPTH {
            return Err(FirmwareError::TooManySiblings {
                count: self.siblings.len(),
            });
        }
        if (1..=MAX_DEPTH).contains(&usize::from(self.depth))
            && self.siblings.len() != usize::from(self.depth)
        {
            return Err(FirmwareError::SiblingDepthMismatch {
                depth: self.depth,
                count: self.siblings.len(),
            });
        }
        vm.load_tainted(DEPTH as u64, &[self.depth], Taint::Public)?;
        vm.load_tainted(STAGE as u64, &[self.stage], Taint::Public)?;
        put_words(vm, INDEX, &[self.index], Taint::Secret)?;
        vm.load_tainted(LEAF as u64, &self.leaf, Taint::Secret)?;
        vm.load_tainted(EXPECTED as u64, &self.expected_root, Taint::Secret)?;
        for (level, sibling) in self.siblings.iter().enumerate() {
            vm.load_tainted((SIBLINGS + 56 * level) as u64, sibling, Taint::Secret)?;
        }
        Ok(())
    }
}
impl CanopyOutput {
    pub fn read(vm: &Ass2Vm) -> Result<Self, FirmwareError> {
        Ok(Self {
            accepted: vm.regs[4] == 1,
            root: get_digest(vm, abi::canopy::ROOT)?,
        })
    }
}
/// Boot, install, run and read [`fw_zkhem_v2_canopy50_verify`].
pub fn run_zkhem_v2_canopy50_verify(input: &CanopyInput) -> Result<CanopyOutput, FirmwareError> {
    let mut vm = boot(&fw_zkhem_v2_canopy50_verify())?;
    input.install(&mut vm)?;
    run_to_halt(&mut vm)?;
    CanopyOutput::read(&vm)
}

/// Mailbox of [`fw_poseidon2_gl24_jive`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JiveInput {
    /// Left child. Secret.
    pub left: [u64; 7],
    /// Right child. Secret.
    pub right: [u64; 7],
    /// Node tweak. Public.
    pub tweak: [u64; 2],
}
impl JiveInput {
    pub fn install(&self, vm: &mut Ass2Vm) -> Result<(), FirmwareError> {
        use abi::jive::*;
        put_words(vm, LEFT, &self.left, Taint::Secret)?;
        put_words(vm, RIGHT, &self.right, Taint::Secret)?;
        put_words(vm, TWEAK, &self.tweak, Taint::Public)?;
        Ok(())
    }
}
/// The seven canonical digest limbs [`fw_poseidon2_gl24_jive`] stored.
pub fn read_jive_digest(vm: &Ass2Vm) -> Result<[u64; 7], FirmwareError> {
    Ok(get_words(vm, abi::jive::DIGEST)?)
}
/// Boot, install, run and read [`fw_poseidon2_gl24_jive`].
pub fn run_poseidon2_gl24_jive(input: &JiveInput) -> Result<[u64; 7], FirmwareError> {
    let mut vm = boot(&fw_poseidon2_gl24_jive())?;
    input.install(&mut vm)?;
    run_to_halt(&mut vm)?;
    read_jive_digest(&vm)
}

/// Mailbox of [`fw_cth_gf128_and_wots`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CthWotsInput {
    /// The four opened `GF(2^128)` values. Secret.
    pub values: [u128; 4],
    /// Per value, its weight in each of the two MAC columns. Public.
    pub weights: [[u128; 2]; 4],
    /// The two expected tags. Secret.
    pub tags: [u128; 2],
    /// Chain value to advance. Secret.
    pub start: [u64; 4],
    /// Public seed, canonical limbs.
    pub seed: [u64; 4],
    /// Hypertree layer, below 64. Public.
    pub layer: u64,
    /// Tree address. Public.
    pub tree: u64,
    /// Key pair, below `2^20`. Public.
    pub keypair: u64,
    /// Chain index, below 256. Public.
    pub chain: u64,
    /// Number of steps, `0..=3`. Secret.
    pub digit: u64,
}
/// Result of [`fw_cth_gf128_and_wots`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CthWotsOutput {
    /// Both tags matched and the address coordinates and digit were in range.
    pub accepted: bool,
    /// The advanced chain value as canonical limbs, or zero on a reject.
    pub end: [u64; 4],
}
impl CthWotsInput {
    pub fn install(&self, vm: &mut Ass2Vm) -> Result<(), FirmwareError> {
        use abi::cth::*;
        put_wide(vm, VALUES, &self.values, Taint::Secret)?;
        put_wide(vm, WEIGHTS, self.weights.as_flattened(), Taint::Public)?;
        put_wide(vm, TAGS, &self.tags, Taint::Secret)?;
        put_words(vm, START, &self.start, Taint::Secret)?;
        put_words(vm, SEED, &self.seed, Taint::Public)?;
        put_words(
            vm,
            LAYER,
            &[self.layer, self.tree, self.keypair, self.chain],
            Taint::Public,
        )?;
        put_words(vm, DIGIT, &[self.digit], Taint::Secret)?;
        Ok(())
    }
}
impl CthWotsOutput {
    pub fn read(vm: &Ass2Vm) -> Result<Self, FirmwareError> {
        Ok(Self {
            accepted: vm.regs[4] == 1,
            end: get_words(vm, abi::cth::END)?,
        })
    }
}
/// Boot, install, run and read [`fw_cth_gf128_and_wots`].
pub fn run_cth_gf128_and_wots(input: &CthWotsInput) -> Result<CthWotsOutput, FirmwareError> {
    let mut vm = boot(&fw_cth_gf128_and_wots())?;
    input.install(&mut vm)?;
    run_to_halt(&mut vm)?;
    CthWotsOutput::read(&vm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::encode_insn_le;
    use crate::vm::DitViolationKind;

    #[test]
    fn tooth_firmware_boot_run_to_halt_and_canopy_enforce_invariants() {
        // `#tooth`:
        // 1. `boot` must reject empty, unaligned, or mailbox-overlapping (`> INPUT`) images.
        assert!(matches!(boot(&[]), Err(FirmwareError::Mem(_))));
        assert!(matches!(boot(&[0, 0, 0]), Err(FirmwareError::Mem(_))));
        assert!(matches!(
            boot(&alloc::vec![0u8; INPUT + 4]),
            Err(FirmwareError::Mem(_))
        ));

        // 2. `run_to_halt` must enforce `DitMode::Trap` even on a caller-constructed `Ass2Vm::new`
        //    (which defaults to `DitMode::Audit`).
        let mut vm = Ass2Vm::new(SRAM_BYTES);
        let prog = [
            encode_insn_le(&I::Br {
                op: BrOp::Beqz,
                cond: 1,
                off20: 1,
            })
            .unwrap(),
            encode_insn_le(&I::Halt).unwrap(),
        ];
        vm.load_image(0, prog.as_flattened()).unwrap();
        vm.reg_taint[1] = Taint::Secret;
        let err = run_to_halt(&mut vm).unwrap_err();
        assert!(matches!(
            err,
            FirmwareError::Exit(RunExit::DitViolation(v))
                if v.kind == DitViolationKind::SecretBranchCond && v.reg == 1
        ));

        // 3. `CanopyInput::install` must reject `siblings.len() != depth` when `depth` is in `1..=16`.
        let mut vm = boot(&fw_zkhem_v2_canopy50_verify()).unwrap();
        let bad_canopy = CanopyInput {
            depth: 3,
            stage: 0,
            index: 0,
            leaf: [0x11; DIGEST_BYTES],
            expected_root: [0x22; DIGEST_BYTES],
            siblings: alloc::vec![[0x33; DIGEST_BYTES]; 2],
        };
        assert_eq!(
            bad_canopy.install(&mut vm),
            Err(FirmwareError::SiblingDepthMismatch { depth: 3, count: 2 })
        );

        // 4. `run_to_halt` must preserve latched unhandled traps on repeated invocation.
        let mut trap_vm = Ass2Vm::new(SRAM_BYTES);
        trap_vm.load_image(0, &0xFFFF_FFFFu32.to_le_bytes()).unwrap();
        assert_eq!(
            run_to_halt(&mut trap_vm),
            Err(FirmwareError::Exit(RunExit::Trap(crate::vm::VmTrap::IllegalInsn)))
        );
        assert_eq!(
            run_to_halt(&mut trap_vm),
            Err(FirmwareError::Exit(RunExit::Trap(crate::vm::VmTrap::IllegalInsn)))
        );
    }
}
