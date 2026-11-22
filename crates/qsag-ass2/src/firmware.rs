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
