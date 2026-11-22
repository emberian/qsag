//! Export the ASS2 cosimulation suite: for each case an initial machine state and the exact
//! state the reference machine [`Ass2Vm`] halts in.
//!
//! ```text
//! cargo run --release -p qsag-ass2 --example export_cosim_vectors -- export <file>
//! cargo run --release -p qsag-ass2 --example export_cosim_vectors -- verify <file>
//! ```
//!
//! `export` writes the suite and then re-reads its own output through the parser below.
//! `verify` parses a file and replays every case on a fresh [`Ass2Vm`] built from nothing but
//! the records, so the records alone determine each run. Its parser is the reference reader.
//! The output is a pure function of this source file and the crate: there is no clock,
//! no environment and no host randomness in it.
//!
//! # File format `ASS2-COSIM-V1`
//!
//! ASCII text, one record per line, fields separated by single spaces. The first field is
//! the record tag. **Every number is lowercase hexadecimal with no prefix**, so a C++
//! reader is `in >> tag` followed by `in >> std::hex >> value` for each field. A line that
//! starts with `#` is a comment. Comments only appear before the first `CASE`.
//!
//! ```text
//! ASS2-COSIM-V1 <cases> <sram_words>      first line; sram_words is 400 (1024 words, 8 KiB)
//! CASE <index> <name>                     index counts from 0; name is [a-z0-9-]+
//! IPC <pc>                                initial PC
//! IR <r0> .. <r15>                        initial R0..R15 (16 fields, r0 is always 0)
//! IS <s0> .. <s24>                        initial S0..S24 (25 fields)
//! IM <word> <value>                       initial SRAM word; zero or more, ascending <word>
//! STEPS <n>                               instruction attempts until the machine halts
//! XPC <pc>                                final PC
//! XHALT <0|1>                             final halted flag (1 in every case)
//! XECAUSE <cause>                         final ECAUSE CSR
//! XINSTRET <n>                            final INSTRET CSR
//! XCYCLES <n>                             final CYCLES CSR (architectural, not clock edges)
//! XR <r0> .. <r15>                        final R0..R15
//! XS <s0> .. <s24>                        final S0..S24
//! XM <word> <value>                       final SRAM word; zero or more, ascending <word>
//! END <index>                             closes the case
//! EOF <cases>                             last line; a file without it is truncated
//! ```
//!
//! The records of a case always appear in this order, and `IM` and `XM` are the only
//! repeated ones.
//!
//! **SRAM.** `sram_words` 64-bit words at byte addresses `0 .. 8 * sram_words`. Word `w` is
//! the little-endian `u64` at byte address `8 * w`: byte address `a` is bits
//! `8 * (a % 8) ..` of word `a / 8`, and the instruction at address `a` is the low half of
//! its word when `a % 8 == 0` and the high half when `a % 8 == 4`. A word with no `IM`
//! record starts as zero. Every access outside the SRAM, fetch or data, is a `MemFault`.
//!
//! **Running a case.** Reset the machine, so every CSR has its reset value (`EVEC`, `EPC`,
//! `ECAUSE`, `INSTRET` and `CYCLES` are 0 and `EXC_EN` is 0). Load the `IM` words, set
//! `R1..R15` from `IR` and `S0..S24` from `IS`, and start at `IPC`. Run until the machine
//! halts: on `HALT`, on a `CSRW POWER` with bit 0 set, or on a trap taken while
//! `EXC_EN == 0`. `STEPS` is the number of instruction attempts the reference took, each
//! one either a retirement or a trap, the last being the one that halts. It is a bound
//! for timeouts and, for a harness that counts retire and trap pulses, a lockstep check.
//!
//! **Checking a case.** All of `XPC`, `XHALT`, `XECAUSE`, `XINSTRET`, `XCYCLES`, `XR` and
//! `XS` must match. The final SRAM is the initial SRAM with each `XM` word replaced: `XM`
//! lists exactly the words whose final value differs from their initial value, so a word
//! without an `XM` record must still hold its initial value.
//!
//! # Contents
//!
//! [`RANDOM_CASES`] cases `rand-0000 ..` come first. Each is a generated program with random
//! initial registers, lanes and data drawn half from edge values (`0`, `1`, `p - 1`, `p`,
//! `p + 1`, `2^64 - 1`, shift amounts around 64, ..) and half from full-width words. A
//! program is a prologue, a straight body of instruction groups with forward branches,
//! short counted loops and deliberate traps, and a trap handler at `0x800` that skips the
//! faulting instruction a bounded number of times. Three of four cases enable the handler:
//! the others halt on their first trap. Some cases start at a non-zero, a misaligned or an
//! out-of-memory PC. The exporter refuses to write a suite that does not execute every
//! instruction form and take every trap cause at least once.
//!
//! The `fw-*` cases that follow run the four firmware images of [`qsag_ass2::firmware`] on
//! real protocol inputs, accepting and tampered, from junk-filled registers. They run with
//! the DIT auditor in trap mode and their secret inputs tagged, and the exporter checks
//! each result against the live protocol implementation before writing it.

#[path = "../tests/common/fixtures.rs"]
mod fixtures;

use fixtures::P;
use qsag_ass2::firmware::{
    self, CanopyOutput, CthWotsOutput, SRAM_BYTES, SumcheckOutput, abi, read_jive_digest,
};
use qsag_ass2::isa::{
    AluOp, AluiOp, Ass2Insn as I, BrOp, Imm20Mode, LoadMode, StoreMode, csr, decode_insn,
    disassemble_insn, encode_insn,
};
use qsag_ass2::vm::{Ass2Vm, StepOutcome, Taint, VmTrap};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::process::ExitCode;

const FORMAT: &str = "ASS2-COSIM-V1";
const SRAM_WORDS: usize = SRAM_BYTES / 8;
const RANDOM_CASES: usize = 1024;
/// Seed of the whole suite ("ASS2COSI").
const SEED: u64 = 0x4153_5332_434F_5349;
/// No case may take more instruction attempts than this.
const STEP_LIMIT: u64 = 20_000;

/// Memory map of a random case.
const HANDLER: u64 = 0x0800;
/// The handler's remaining-trap count.
const BUDGET: u64 = 0x0FF8;
/// `R14` throughout the body: the middle of the data region `0x1000 .. 0x2000`.
const BASE: u64 = 0x1800;
/// Words `DATA_LO .. DATA_HI` hold random data: every address the body reaches from `R14`.
const DATA_LO: usize = 0x1400 / 8;
const DATA_HI: usize = 0x1C00 / 8;
/// A body stops growing at this many instructions, so it ends below [`HANDLER`] from either
/// origin.
const BODY_INSNS: usize = 200;

const EDGE: [u64; 16] = [
    0,
    1,
    2,
    63,
    64,
    65,
    0xffff_ffff,
    1 << 32,
    1 << 40,
    i64::MAX as u64,
    1 << 63,
    P - 1,
    P,
    P + 1,
    u64::MAX - 1,
    u64::MAX,
];

/// Skip the faulting instruction (an `EXC` already continues after itself) until the budget
/// word runs out, then halt. `R9..R12` are the handler's scratch.
const HANDLER_SOURCE: &str = "
    CSRR R11, ECAUSE
    CSRR R12, EPC
    LD64 R9, [R0 + 0xFF8]
    ADDI R9, R9, -1
    ST64 [R0 + 0xFF8], R9
    BNEZ R9, 1
    HALT
    MOVZ20 R9, 2
    CMP.EQ R10, R11, R9
    ADDI R9, R12, 4
    SEL R12, R9, R12, R10
    CSRW R12, EPC
    ERET
";

/// Words with a reserved field set or a reserved sub-function, one or more per major opcode.
const ILLEGAL: [u32; 30] = [
    0x0000_0001,
    0x0001_0010,
    0x0002_0100,
    0x0003_0001,
    0x0015_0000,
    0x1000_1000,
    0x1010_0000,
    0x2009_0000,
    0x2000_1000,
    0x3004_0500,
    0x3000_0A00,
    0x4000_0030,
    0x5001_0000,
    0x6001_0800,
    0x6002_8000,
    0x6003_0100,
    0x7000_0200,
    0x8000_0200,
    0x9000_0040,
    0xB000_0100,
    0xC001_9000,
    0xC000_0310,
    0xC010_0100,
    0xC000_0401,
    0xD004_0005,
    0xD003_0100,
    0xE000_00C0,
    0xE000_1000,
    0xF170_0000,
    0xF011_0000,
];

/// SplitMix64.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    /// A value in `lo .. hi`.
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo) as u64) as i64
    }
    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
    fn one_in(&mut self, n: u64) -> bool {
        self.below(n) == 0
    }
    /// Half edge values, half full-width words.
    fn value(&mut self) -> u64 {
        if self.one_in(2) {
            self.pick(&EDGE)
        } else {
            self.next()
        }
    }
}

/// One instruction of a generated body. Targets are group indices, resolved at layout.
#[derive(Clone, Copy)]
enum Item {
    Insn(I),
    Raw(u32),
    Br {
        op: BrOp,
        cond: u8,
        group: usize,
    },
    Jal {
        rd: u8,
        group: usize,
    },
    /// `JAL` to an absolute byte address.
    JalTo {
        rd: u8,
        addr: u64,
    },
    /// `R[rd] := address of the group + 4 * bias`.
    Auipc {
        rd: u8,
        group: usize,
        bias: i32,
    },
}

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Lut4,
    Alu,
    Alui,
    Imm20,
    Cmp,
    Sel,
    Bext,
    Bswap,
    Load,
    Store,
    ByteViaTemp,
    Lane,
    LaneMem,
    Gl,
    Fp5,
    Gf128,
    Perm,
    Branch,
    Jal,
    Jalr,
    Li64,
    Csrr,
    Csrw,
    Counter,
    Nop,
    Trap,
    Zeroize,
    Control,
    Loop,
}

/// Relative frequency of each kind of group.
const MENU: [(u64, Kind); 29] = [
    (8, Kind::Lut4),
    (10, Kind::Alu),
    (8, Kind::Alui),
    (3, Kind::Imm20),
    (6, Kind::Cmp),
    (5, Kind::Sel),
    (5, Kind::Bext),
    (2, Kind::Bswap),
    (6, Kind::Load),
    (6, Kind::Store),
    (3, Kind::ByteViaTemp),
    (6, Kind::Lane),
    (5, Kind::LaneMem),
    (6, Kind::Gl),
    (4, Kind::Fp5),
    (4, Kind::Gf128),
    (3, Kind::Perm),
    (6, Kind::Branch),
    (2, Kind::Jal),
    (3, Kind::Jalr),
    (3, Kind::Li64),
    (3, Kind::Csrr),
    (2, Kind::Csrw),
    (1, Kind::Counter),
    (1, Kind::Nop),
    (5, Kind::Trap),
    (1, Kind::Zeroize),
    (2, Kind::Control),
    (2, Kind::Loop),
];

fn kind(rng: &mut Rng) -> Kind {
    let total: u64 = MENU.iter().map(|(weight, _)| weight).sum();
    let mut roll = rng.below(total);
    for (weight, kind) in MENU {
        if roll < weight {
            return kind;
        }
        roll -= weight;
    }
    unreachable!()
}

fn movz(rd: u8, value: u64) -> Item {
    Item::Insn(I::Imm20 {
        mode: Imm20Mode::Movz20,
        rd,
        imm20: value as u32,
    })
}
fn addi(rd: u8, ra: u8, value: i16) -> Item {
    Item::Insn(I::Alui {
        op: AluiOp::Addi,
        rd,
        ra,
        imm16: value as u16,
    })
}
fn csrw(ra: u8, csr: u8) -> Item {
    Item::Insn(I::Csrw { ra, csr })
}

/// One group of kind `kind` at group index `index`. A group runs from its first instruction
/// or not at all: branches only target group starts. No group writes `R14`, and inside a
/// loop none writes the counter `R13`.
fn group(rng: &mut Rng, kind: Kind, index: usize, in_loop: bool) -> Vec<Item> {
    use Item::Insn as X;
    let dst = |rng: &mut Rng| loop {
        let r = rng.below(16) as u8;
        if r != 14 && !(in_loop && r == 13) {
            break r;
        }
    };
    let temp = |rng: &mut Rng| loop {
        let r = dst(rng);
        if r != 0 {
            break r;
        }
    };
    // One group in five uses a single register for every operand.
    let rd = dst(rng);
    let alias = rng.one_in(5);
    let src = |rng: &mut Rng| if alias { rd } else { rng.below(16) as u8 };
    let (ra, rb, rc) = (src(rng), src(rng), src(rng));
    let lane = rng.below(25) as u8;
    let word_off = rng.range(-128, 128) as i16;
    let byte_off = rng.range(-1024, 1024) as i16;
    let odd = rng.range(1, 8) as i16;
    match kind {
        Kind::Lut4 => vec![X(I::Lut4 {
            rd,
            ra,
            rb,
            m: rng.below(16) as u8,
        })],
        Kind::Alu => vec![X(I::Alu {
            op: rng.pick(AluOp::ALL),
            rd,
            ra,
            rb,
        })],
        Kind::Alui => {
            let op = rng.pick(AluiOp::ALL);
            let imm16 = match (op.is_shift(), rng.one_in(2)) {
                (true, true) => rng.pick(&[0, 1, 31, 32, 63]),
                (true, false) => rng.below(64) as u16,
                (false, true) => rng.pick(&[0, 1, 0x7fff, 0x8000, 0xffff]),
                (false, false) => rng.next() as u16,
            };
            vec![X(I::Alui { op, rd, ra, imm16 })]
        }
        Kind::Imm20 => {
            let imm20 = if rng.one_in(2) {
                rng.pick(&[0, 1, 0x7_ffff, 0x8_0000, 0xf_ffff])
            } else {
                rng.below(1 << 20) as u32
            };
            vec![X(I::Imm20 {
                mode: rng.pick(Imm20Mode::ALL),
                rd,
                imm20,
            })]
        }
        Kind::Cmp => vec![X(I::Cmp {
            rd,
            ra,
            rb,
            flags: rng.below(16) as u8,
        })],
        Kind::Sel => vec![X(I::Sel { rd, ra, rb, rc })],
        Kind::Bext => {
            let (idx, len) = (rng.below(8) as u8, 1 + rng.below(8) as u8);
            vec![X(if rng.one_in(2) {
                I::Bextu { rd, ra, idx, len }
            } else {
                I::Bexts { rd, ra, idx, len }
            })]
        }
        Kind::Bswap => vec![X(I::Bswap64 { rd, ra })],
        Kind::Load => vec![X(if rng.one_in(2) {
            I::Load {
                mode: LoadMode::Ld64,
                rd,
                ra: 14,
                simm16: word_off,
            }
        } else {
            I::Load {
                mode: LoadMode::Ldbu,
                rd,
                ra: 14,
                simm16: byte_off,
            }
        })],
        Kind::Store => vec![X(if rng.one_in(2) {
            I::Store {
                mode: StoreMode::St64,
                rs: ra,
                ra: 14,
                simm16: word_off,
            }
        } else {
            I::Store {
                mode: StoreMode::Stb,
                rs: ra,
                ra: 14,
                simm16: byte_off,
            }
        })],
        // Byte accesses through an odd pointer: every byte strobe of a word.
        Kind::ByteViaTemp => {
            let t = temp(rng);
            let access = if rng.one_in(2) {
                I::Load {
                    mode: LoadMode::Ldbu,
                    rd,
                    ra: t,
                    simm16: byte_off / 2,
                }
            } else {
                I::Store {
                    mode: StoreMode::Stb,
                    rs: ra,
                    ra: t,
                    simm16: byte_off / 2,
                }
            };
            vec![addi(t, 14, odd), X(access)]
        }
        Kind::Lane => vec![X(match rng.below(12) {
            0 => I::Szero,
            1..=4 => I::Sget { rd, sidx: lane },
            5..=8 => I::Sput { sidx: lane, ra },
            _ => I::Sxor { sidx: lane, ra },
        })],
        Kind::LaneMem => {
            let off8 = word_off as i8;
            vec![X(if rng.one_in(2) {
                I::Sld64 {
                    sidx: lane,
                    ra: 14,
                    off8,
                }
            } else {
                I::Sst64 {
                    sidx: lane,
                    ra: 14,
                    off8,
                }
            })]
        }
        Kind::Gl => vec![X(match rng.below(4) {
            0 => I::GlMac { rd, ra, rb, rc },
            1 => I::GlAdd { rd, ra, rb },
            2 => I::GlSub { rd, ra, rb },
            _ => I::GlSbox7 { rd, ra },
        })],
        Kind::Fp5 => {
            let ed = rng.below(5) as u8;
            let (ea, eb) = if alias {
                (ed, ed)
            } else {
                (rng.below(5) as u8, rng.below(5) as u8)
            };
            vec![X(match rng.below(3) {
                0 => I::Fp5Mul { ed, ea, eb },
                1 => I::Fp5Add { ed, ea, eb },
                _ => I::Fp5Sub { ed, ea, eb },
            })]
        }
        Kind::Gf128 => {
            let pd = rng.below(12) as u8;
            let (pa, pb) = if alias {
                (pd, pd)
            } else {
                (rng.below(12) as u8, rng.below(12) as u8)
            };
            vec![X(if rng.one_in(2) {
                I::Gf128Mul { pd, pa, pb }
            } else {
                I::Gf128Xor { pd, pa, pb }
            })]
        }
        Kind::Perm => vec![X(match rng.below(4) {
            0 => I::KeccakF1600 { rounds: 12 },
            1 => I::KeccakF1600 { rounds: 24 },
            2 => I::Poseidon2Gl24,
            _ => I::Poseidon2Gl12,
        })],
        Kind::Branch => vec![Item::Br {
            op: rng.pick(BrOp::ALL),
            cond: ra,
            group: index + 1 + rng.below(4) as usize,
        }],
        Kind::Jal => vec![Item::Jal {
            rd,
            group: index + 1 + rng.below(3) as usize,
        }],
        // The link register is the base register in an aliased group.
        Kind::Jalr => {
            let t = temp(rng);
            let simm16 = rng.range(-4, 5) as i16;
            let target = index + 1 + rng.below(3) as usize;
            vec![
                Item::Auipc {
                    rd: t,
                    group: target,
                    bias: -i32::from(simm16),
                },
                X(I::Jalr {
                    rd: if alias { t } else { rd },
                    ra: t,
                    simm16,
                }),
            ]
        }
        Kind::Li64 => {
            let value = rng.pick(&EDGE);
            let mut items = vec![movz(rd, value >> 48)];
            for shift in [32, 16, 0] {
                let imm16 = (value >> shift) as u16;
                items.push(X(I::Alui {
                    op: AluiOp::Slk16,
                    rd,
                    ra: rd,
                    imm16,
                }));
            }
            items
        }
        Kind::Csrr => {
            let csr = rng.pick(&[
                csr::ARCH_ID,
                csr::WORD_BITS,
                csr::EVEC,
                csr::INSTRET,
                csr::CYCLES,
                csr::FEATURES,
                csr::EPC,
                csr::ECAUSE,
                csr::EXC_EN,
                csr::DIT,
            ]);
            vec![X(I::Csrr { rd, csr })]
        }
        Kind::Csrw => vec![csrw(ra, rng.pick(&[csr::EPC, csr::ECAUSE, csr::DBG_OUT]))],
        Kind::Counter => vec![csrw(ra, rng.pick(&[csr::INSTRET, csr::CYCLES]))],
        Kind::Nop => vec![X(I::Nop)],
        Kind::Trap => {
            let t = temp(rng);
            match rng.below(16) {
                0..=2 => vec![Item::Raw(rng.pick(&ILLEGAL))],
                3 => vec![Item::Raw(loop {
                    let word = rng.next() as u32;
                    if decode_insn(word).is_none() {
                        break word;
                    }
                })],
                4 | 5 => vec![X(I::Exc)],
                // Misaligned word accesses through an odd pointer.
                6 => vec![
                    addi(t, 14, odd),
                    X(I::Load {
                        mode: LoadMode::Ld64,
                        rd,
                        ra: t,
                        simm16: word_off,
                    }),
                ],
                7 => vec![
                    addi(t, 14, odd),
                    X(I::Store {
                        mode: StoreMode::St64,
                        rs: ra,
                        ra: t,
                        simm16: word_off,
                    }),
                ],
                8 => vec![
                    addi(t, 14, odd),
                    X(if rng.one_in(2) {
                        I::Sld64 {
                            sidx: lane,
                            ra: t,
                            off8: 0,
                        }
                    } else {
                        I::Sst64 {
                            sidx: lane,
                            ra: t,
                            off8: 0,
                        }
                    }),
                ],
                // The first address past the SRAM and the last one below zero.
                9 => vec![X(match rng.below(3) {
                    0 => I::Load {
                        mode: LoadMode::Ld64,
                        rd,
                        ra: 0,
                        simm16: 0x400,
                    },
                    1 => I::Load {
                        mode: LoadMode::Ldbu,
                        rd,
                        ra: 0,
                        simm16: -1,
                    },
                    _ => I::Load {
                        mode: LoadMode::Ld64,
                        rd,
                        ra: 0,
                        simm16: -1,
                    },
                })],
                10 => vec![X(match rng.below(3) {
                    0 => I::Store {
                        mode: StoreMode::St64,
                        rs: ra,
                        ra: 0,
                        simm16: 0x400,
                    },
                    1 => I::Store {
                        mode: StoreMode::Stb,
                        rs: ra,
                        ra: 0,
                        simm16: -1,
                    },
                    _ => I::Store {
                        mode: StoreMode::Stb,
                        rs: ra,
                        ra: 0,
                        simm16: 0x2000,
                    },
                })],
                // A lane transfer at the end of the SRAM: the last word is fine, the next
                // one faults.
                11 => {
                    let off8 = if rng.one_in(2) { 0 } else { -1 };
                    vec![
                        movz(t, SRAM_BYTES as u64),
                        X(if rng.one_in(2) {
                            I::Sld64 {
                                sidx: lane,
                                ra: t,
                                off8,
                            }
                        } else {
                            I::Sst64 {
                                sidx: lane,
                                ra: t,
                                off8,
                            }
                        }),
                    ]
                }
                12 => vec![
                    Item::Auipc {
                        rd: t,
                        group: index + 1,
                        bias: 0,
                    },
                    addi(t, t, rng.range(1, 4) as i16),
                    X(I::Jalr {
                        rd: if alias { t } else { rd },
                        ra: t,
                        simm16: 0,
                    }),
                ],
                13 => {
                    let csr = rng.pick(&[csr::POWER, csr::DBG_OUT, csr::ZEROIZE, 0x07, 0x3E, 0xFF]);
                    vec![X(I::Csrr { rd, csr })]
                }
                14 => {
                    let csr =
                        rng.pick(&[csr::ARCH_ID, csr::WORD_BITS, csr::FEATURES, csr::DIT, 0x0B]);
                    vec![csrw(ra, csr)]
                }
                // Leave the SRAM: the fetch faults.
                _ => {
                    if rng.one_in(4) {
                        vec![Item::JalTo {
                            rd,
                            addr: SRAM_BYTES as u64 + 4 * rng.below(4),
                        }]
                    } else {
                        vec![X(I::Exc)]
                    }
                }
            }
        }
        // Both wipes, each followed by the reload of the data pointer.
        Kind::Zeroize => {
            let wipe = if rng.one_in(2) {
                X(I::Zeroize)
            } else {
                csrw(ra, csr::ZEROIZE)
            };
            vec![wipe, movz(14, BASE)]
        }
        Kind::Control => {
            let t = temp(rng);
            match rng.below(8) {
                0..=2 => vec![csrw(ra, csr::EXC_EN)],
                3 | 4 => vec![movz(t, 1), csrw(t, csr::EXC_EN)],
                5 => vec![csrw(ra, csr::POWER)],
                // ERET as a forward jump that also enables traps.
                _ => vec![
                    Item::Auipc {
                        rd: t,
                        group: index + 1 + rng.below(3) as usize,
                        bias: 0,
                    },
                    csrw(t, csr::EPC),
                    X(I::Eret),
                ],
            }
        }
        Kind::Loop => unreachable!("loops are built by body()"),
    }
}

/// The groups of a body and its loops as `(counter-load group, closing group)`.
fn body(rng: &mut Rng) -> (Vec<Vec<Item>>, Vec<(usize, usize)>) {
    let mut groups: Vec<Vec<Item>> = Vec::new();
    let mut loops = Vec::new();
    let wanted = 24 + rng.below(33) as usize;
    let insns = |groups: &[Vec<Item>]| groups.iter().map(Vec::len).sum::<usize>();
    while groups.len() < wanted && insns(&groups) < BODY_INSNS {
        let next = kind(rng);
        if next != Kind::Loop {
            let index = groups.len();
            groups.push(group(rng, next, index, false));
            continue;
        }
        // One to three passes over a few groups that leave the counter and the wipes alone.
        let load = groups.len();
        groups.push(vec![movz(13, 1 + rng.below(3))]);
        for _ in 0..2 + rng.below(4) {
            let inner = loop {
                let inner = kind(rng);
                if !matches!(inner, Kind::Loop | Kind::Zeroize) {
                    break inner;
                }
            };
            let index = groups.len();
            groups.push(group(rng, inner, index, true));
        }
        groups.push(vec![
            addi(13, 13, -1),
            Item::Br {
                op: BrOp::Bnez,
                cond: 13,
                group: load + 1,
            },
        ]);
        loops.push((load, groups.len() - 1));
    }
    // A jump from before a loop may not enter it past its counter load.
    for (index, items) in groups.iter_mut().enumerate() {
        for item in items {
            if let Item::Br { group, .. } | Item::Jal { group, .. } | Item::Auipc { group, .. } =
                item
            {
                for &(load, close) in &loops {
                    if index < load && load < *group && *group <= close {
                        *group = load;
                    }
                }
            }
        }
    }
    (groups, loops)
}

fn word(insn: I) -> u32 {
    encode_insn(&insn).unwrap_or_else(|e| panic!("{insn:?}: {e}"))
}

/// Lay out prologue, body and the final `HALT` from `origin`.
fn layout(origin: u64, prologue: &[Item], groups: &[Vec<Item>]) -> Vec<u8> {
    let mut starts = Vec::new();
    let mut count = prologue.len();
    for items in groups {
        starts.push(count);
        count += items.len();
    }
    // A target past the last group is the final HALT.
    let address = |group: usize| origin + 4 * *starts.get(group).unwrap_or(&count) as u64;
    let mut code = Vec::new();
    let all = prologue.iter().chain(groups.iter().flatten());
    for (position, item) in all.enumerate() {
        let pc = origin + 4 * position as u64;
        let words_from = |from: u64, to: u64| ((to as i64 - from as i64) / 4) as i32;
        let encoded = match *item {
            Item::Insn(insn) => word(insn),
            Item::Raw(raw) => raw,
            Item::Br { op, cond, group } => word(I::Br {
                op,
                cond,
                off20: words_from(pc + 4, address(group)),
            }),
            Item::Jal { rd, group } => word(I::Jal {
                rd,
                off24: words_from(pc + 4, address(group)),
            }),
            Item::JalTo { rd, addr } => word(I::Jal {
                rd,
                off24: words_from(pc + 4, addr),
            }),
            Item::Auipc { rd, group, bias } => {
                let imm = words_from(pc, address(group)) + bias;
                word(I::Imm20 {
                    mode: Imm20Mode::Auipc,
                    rd,
                    imm20: imm as u32 & 0xf_ffff,
                })
            }
        };
        code.extend_from_slice(&encoded.to_le_bytes());
    }
    code.extend_from_slice(&word(I::Halt).to_le_bytes());
    assert!(
        origin + code.len() as u64 <= HANDLER,
        "body overlaps the handler"
    );
    code
}

struct Case {
    name: String,
    start: Ass2Vm,
}

/// Random case `index`. `attempt` reseeds a case whose program did not halt.
fn random_case(index: usize, attempt: u64) -> Case {
    let mut rng = Rng(SEED ^ ((index as u64) << 20) ^ (attempt << 52));
    let origin = if index % 8 == 5 { 0x400 } else { 0 };
    let mut prologue = vec![movz(14, BASE), movz(9, HANDLER), csrw(9, csr::EVEC)];
    if !rng.one_in(4) {
        prologue.extend([movz(9, 1), csrw(9, csr::EXC_EN)]);
    }
    let (groups, _) = body(&mut rng);
    let mut vm = Ass2Vm::new(SRAM_BYTES);
    vm.load_image(origin, &layout(origin, &prologue, &groups))
        .unwrap();
    vm.load_image(HANDLER, &qsag_ass2::assemble(HANDLER_SOURCE).unwrap())
        .unwrap();
    vm.load_image(BUDGET, &(2 + rng.below(5)).to_le_bytes())
        .unwrap();
    for w in DATA_LO..DATA_HI {
        if rng.one_in(4) {
            vm.load_image(8 * w as u64, &rng.value().to_le_bytes())
                .unwrap();
        }
    }
    vm.regs = core::array::from_fn(|i| if i == 0 { 0 } else { rng.value() });
    vm.spg = core::array::from_fn(|_| rng.value());
    vm.pc = match index % 64 {
        // A misaligned and an out-of-memory start: the first fetch traps.
        63 => origin + 1 + rng.below(3),
        31 => rng.pick(&[SRAM_BYTES as u64, 1 << 32, u64::MAX - 3]),
        _ => origin,
    };
    Case {
        name: format!("rand-{index:04}"),
        start: vm,
    }
}

/// What the suite executed: retired instructions per form and traps per cause.
#[derive(Default)]
struct Coverage {
    forms: BTreeMap<String, u64>,
    majors: [u64; 16],
    traps: [u64; 6],
    steps: u64,
}

fn form(insn: &I) -> String {
    let named = |addr: u8| {
        csr::name(addr)
            .map(String::from)
            .unwrap_or(format!("{addr:02X}"))
    };
    match *insn {
        I::Lut4 { m, .. } => format!("LUT4.{m:X}"),
        I::Cmp { flags, .. } => format!("CMP.{flags:X}"),
        I::Alu { op, .. } => op.mnemonic().into(),
        I::Alui { op, .. } => op.mnemonic().into(),
        I::Imm20 { mode, .. } => mode.mnemonic().into(),
        I::Load { mode, .. } => mode.mnemonic().into(),
        I::Store { mode, .. } => mode.mnemonic().into(),
        I::Br { op, .. } => op.mnemonic().into(),
        I::KeccakF1600 { rounds } => format!("KECCAK.F1600.{rounds}"),
        I::Csrr { csr, .. } => format!("CSRR.{}", named(csr)),
        I::Csrw { csr, .. } => format!("CSRW.{}", named(csr)),
        _ => disassemble_insn(insn)
            .split_whitespace()
            .next()
            .unwrap()
            .into(),
    }
}

/// Every instruction form the ISA defines.
fn all_forms() -> Vec<String> {
    let mut forms: Vec<String> = [
        "EXC",
        "ERET",
        "ZEROIZE",
        "HALT",
        "NOP",
        "SEL",
        "BEXTU",
        "BEXTS",
        "BSWAP64",
        "JAL",
        "JALR",
        "SGET",
        "SPUT",
        "SXOR",
        "SZERO",
        "SLD64",
        "SST64",
        "GL.MAC",
        "GL.ADD",
        "GL.SUB",
        "GL.SBOX7",
        "FP5.MUL",
        "FP5.ADD",
        "FP5.SUB",
        "GF128.MUL",
        "GF128.XOR",
        "KECCAK.F1600.12",
        "KECCAK.F1600.24",
        "POSEIDON2.GL24",
        "POSEIDON2.GL12",
    ]
    .map(String::from)
    .to_vec();
    for i in 0..16 {
        forms.extend([format!("LUT4.{i:X}"), format!("CMP.{i:X}")]);
    }
    forms.extend(AluOp::ALL.iter().map(|op| op.mnemonic().into()));
    forms.extend(AluiOp::ALL.iter().map(|op| op.mnemonic().into()));
    forms.extend(Imm20Mode::ALL.iter().map(|op| op.mnemonic().into()));
    forms.extend(LoadMode::ALL.iter().map(|op| op.mnemonic().into()));
    forms.extend(StoreMode::ALL.iter().map(|op| op.mnemonic().into()));
    forms.extend(BrOp::ALL.iter().map(|op| op.mnemonic().into()));
    for name in [
        "ARCH_ID",
        "WORD_BITS",
        "EVEC",
        "INSTRET",
        "CYCLES",
        "FEATURES",
        "EPC",
        "ECAUSE",
        "EXC_EN",
        "DIT",
    ] {
        forms.push(format!("CSRR.{name}"));
    }
    for name in [
        "EVEC", "POWER", "INSTRET", "CYCLES", "EPC", "ECAUSE", "DBG_OUT", "EXC_EN", "ZEROIZE",
    ] {
        forms.push(format!("CSRW.{name}"));
    }
    forms
}

/// Run to the halt. `None` when the step limit comes first.
fn execute(start: &Ass2Vm, coverage: &mut Coverage) -> Option<Ass2Vm> {
    let mut vm = start.clone();
    let mut local = Coverage::default();
    for _ in 0..STEP_LIMIT {
        let outcome = vm.step();
        local.steps += 1;
        let fetched = vm.trace.observations.last().and_then(|o| o.insn_word);
        match outcome {
            StepOutcome::Retired | StepOutcome::Halted => {
                let insn = decode_insn(fetched.expect("retired a word")).expect("decodable");
                *local.forms.entry(form(&insn)).or_default() += 1;
                local.majors[usize::from(insn.major_opcode())] += 1;
            }
            StepOutcome::Trap(cause) => local.traps[cause as usize] += 1,
            StepOutcome::DitViolation(v) => panic!("DIT violation {v:?}"),
        }
        if vm.halted {
            for (form, n) in local.forms {
                *coverage.forms.entry(form).or_default() += n;
            }
            for (total, n) in coverage.majors.iter_mut().zip(local.majors) {
                *total += n;
            }
            for (total, n) in coverage.traps.iter_mut().zip(local.traps) {
                *total += n;
            }
            coverage.steps += local.steps;
            return Some(vm);
        }
    }
    None
}

fn sram_words(vm: &Ass2Vm) -> impl Iterator<Item = u64> + '_ {
    vm.mem
        .as_chunks::<8>()
        .0
        .iter()
        .map(|bytes| u64::from_le_bytes(*bytes))
}

fn record(out: &mut String, tag: &str, values: &[u64]) {
    out.push_str(tag);
    for value in values {
        write!(out, " {value:x}").unwrap();
    }
    out.push('\n');
}

fn emit(out: &mut String, index: usize, case: &Case, end: &Ass2Vm) {
    let start = &case.start;
    assert!(end.halted && start.mem.len() == SRAM_BYTES && start.regs[0] == 0);
    writeln!(out, "CASE {index:x} {}", case.name).unwrap();
    record(out, "IPC", &[start.pc]);
    record(out, "IR", &start.regs);
    record(out, "IS", &start.spg);
    for (w, value) in sram_words(start).enumerate() {
        if value != 0 {
            record(out, "IM", &[w as u64, value]);
        }
    }
    record(out, "STEPS", &[end.trace.observations.len() as u64]);
    record(out, "XPC", &[end.pc]);
    record(out, "XHALT", &[end.halted.into()]);
    record(out, "XECAUSE", &[end.csrs.ecause]);
    record(out, "XINSTRET", &[end.csrs.instret]);
    record(out, "XCYCLES", &[end.csrs.cycles]);
    record(out, "XR", &end.regs);
    record(out, "XS", &end.spg);
    for (w, (before, after)) in sram_words(start).zip(sram_words(end)).enumerate() {
        if before != after {
            record(out, "XM", &[w as u64, after]);
        }
    }
    record(out, "END", &[index as u64]);
}

/// A firmware case and the check its final state must pass.
type Checked = (Case, Box<dyn Fn(&Ass2Vm)>);

/// `image` booted with junk in every register and lane, tagged secret, then `install`.
fn firmware_case(name: &str, image: &[u8], install: impl FnOnce(&mut Ass2Vm)) -> Case {
    let mut vm = firmware::boot(image).unwrap();
    vm.regs = [0xdead_beef_face_cafe; 16];
    vm.regs[0] = 0;
    vm.spg = [u64::MAX; 25];
    vm.reg_taint = [Taint::Secret; 16];
    vm.reg_taint[0] = Taint::Public;
    vm.spg_taint.fill(Taint::Secret);
    install(&mut vm);
    Case {
        name: name.into(),
        start: vm,
    }
}

fn flip(vm: &mut Ass2Vm, addr: usize, bit: u8) {
    vm.mem[addr] ^= 1 << bit;
}

fn firmware_cases() -> Vec<Checked> {
    let mut cases: Vec<Checked> = Vec::new();

    // zk-Hem v2 sumcheck round.
    {
        use abi::sumcheck::*;
        let image = firmware::fw_zkhem_v2_fp5_sumcheck();
        let fx = fixtures::sumcheck(0, &mut 0x1503_3871_aab0_cdef);
        let (value, digest) = (fx.value, fx.input.expected);
        let tampers: [(&str, Option<(usize, u8)>); 5] = [
            ("fw-sumcheck-valid", None),
            (
                "fw-sumcheck-tamper-digest-byte49-bit0",
                Some((EXPECTED + 49, 0)),
            ),
            (
                "fw-sumcheck-tamper-digest-byte32-bit7",
                Some((EXPECTED + 32, 7)),
            ),
            ("fw-sumcheck-tamper-claim-bit0", Some((CLAIM, 0))),
            ("fw-sumcheck-tamper-coeff9-bit0", Some((COEFFS + 9 * 40, 0))),
        ];
        for (name, tamper) in tampers {
            let case = firmware_case(name, &image, |vm| {
                fx.input.install(vm).unwrap();
                if let Some((addr, bit)) = tamper {
                    flip(vm, addr, bit);
                }
            });
            cases.push((
                case,
                Box::new(move |end| {
                    let out = SumcheckOutput::read(end).unwrap();
                    assert_eq!(
                        (out.accepted, out.digest),
                        (tamper.is_none(), digest),
                        "{name}"
                    );
                    if name != "fw-sumcheck-tamper-coeff9-bit0" {
                        assert_eq!(out.value, value, "{name}");
                    }
                }),
            ));
        }
        let draw = fixtures::sumcheck_noncanonical_draw();
        let expected = draw.expected;
        cases.push((
            firmware_case("fw-sumcheck-noncanonical-draw", &image, |vm| {
                draw.install(vm).unwrap()
            }),
            Box::new(move |end| {
                let out = SumcheckOutput::read(end).unwrap();
                assert_eq!((out.accepted, out.digest), (false, expected));
            }),
        ));
        let edge = fixtures::sumcheck_rate_boundary();
        let expected = edge.input.expected;
        cases.push((
            firmware_case("fw-sumcheck-rate-boundary", &image, |vm| {
                edge.input.install(vm).unwrap()
            }),
            Box::new(move |end| {
                let out = SumcheckOutput::read(end).unwrap();
                assert_eq!(
                    out,
                    SumcheckOutput {
                        accepted: true,
                        value: [0; 5],
                        digest: expected
                    }
                );
            }),
        ));
    }

    // zk-Hem v2 canopy path.
    {
        use abi::canopy::*;
        let image = firmware::fw_zkhem_v2_canopy50_verify();
        let (tree, leaves) = fixtures::canopy_tree(7);
        let root = tree.root();
        let tampers: [(&str, usize, Option<(usize, u8)>); 6] = [
            ("fw-canopy-valid-depth4-index5", 5, None),
            ("fw-canopy-valid-depth4-index10", 10, None),
            (
                "fw-canopy-tamper-root-byte49-bit0",
                5,
                Some((EXPECTED + 49, 0)),
            ),
            ("fw-canopy-tamper-leaf-bit0", 5, Some((LEAF, 0))),
            (
                "fw-canopy-tamper-sibling3-byte49-bit7",
                5,
                Some((SIBLINGS + 3 * 56 + 49, 7)),
            ),
            ("fw-canopy-tamper-index-bit0", 5, Some((INDEX, 0))),
        ];
        for (name, index, tamper) in tampers {
            let input = fixtures::canopy(&tree, &leaves, 7, index);
            let case = firmware_case(name, &image, |vm| {
                input.install(vm).unwrap();
                if let Some((addr, bit)) = tamper {
                    flip(vm, addr, bit);
                }
            });
            cases.push((
                case,
                Box::new(move |end| {
                    let out = CanopyOutput::read(end).unwrap();
                    assert_eq!(out.accepted, tamper.is_none(), "{name}");
                    // Only a tampered expectation leaves the recomputed root intact.
                    if tamper.is_none() || name == "fw-canopy-tamper-root-byte49-bit0" {
                        assert_eq!(out.root, root, "{name}");
                    } else {
                        assert_ne!(out.root, root, "{name}");
                    }
                }),
            ));
        }
        let deep = fixtures::canopy_synthetic_path(16);
        let deep_root = deep.expected_root;
        cases.push((
            firmware_case("fw-canopy-valid-depth16", &image, |vm| {
                deep.install(vm).unwrap()
            }),
            Box::new(move |end| {
                let out = CanopyOutput::read(end).unwrap();
                assert_eq!(
                    out,
                    CanopyOutput {
                        accepted: true,
                        root: deep_root
                    }
                );
            }),
        ));
        let mut shallow = fixtures::canopy_synthetic_path(1);
        shallow.depth = 17;
        cases.push((
            firmware_case("fw-canopy-reject-depth17", &image, |vm| {
                shallow.install(vm).unwrap()
            }),
            Box::new(|end| assert_eq!(end.regs[4], 0)),
        ));
    }

    // Poseidon2-GL-w24 Jive compression. Nothing to reject: a changed input is a
    // changed digest.
    {
        let image = firmware::fw_poseidon2_gl24_jive();
        let (kat, kat_digest) = fixtures::jive_kat();
        let mut tampered = kat;
        tampered.left[0] ^= 1;
        let mut boundary = kat;
        boundary.left = [P - 1, P, P + 1, u64::MAX, 0, 1, u64::MAX - 1];
        boundary.right = [u64::MAX; 7];
        boundary.tweak = [P, u64::MAX];
        for (name, input) in [
            ("fw-jive-kat", kat),
            ("fw-jive-tamper-left0-bit0", tampered),
            ("fw-jive-field-boundaries", boundary),
        ] {
            let want = fixtures::jive_digest(&input);
            assert_eq!(want == kat_digest, name == "fw-jive-kat");
            cases.push((
                firmware_case(name, &image, |vm| input.install(vm).unwrap()),
                Box::new(move |end| {
                    assert_eq!(
                        (end.regs[4], read_jive_digest(end).unwrap()),
                        (1, want),
                        "{name}"
                    );
                }),
            ));
        }
    }

    // Dual MAC check and the WOTS+C chain for each secret digit.
    {
        use abi::cth::*;
        let image = firmware::fw_cth_gf128_and_wots();
        let fixtures = fixtures::cth_wots(&mut 0x7be6_b753_fcc8_11d4);
        for (digit, (input, end_value)) in fixtures.into_iter().enumerate() {
            let name = format!("fw-cth-wots-digit{digit}");
            cases.push((
                firmware_case(&name, &image, |vm| input.install(vm).unwrap()),
                Box::new(move |end| {
                    let out = CthWotsOutput::read(end).unwrap();
                    assert_eq!(
                        out,
                        CthWotsOutput {
                            accepted: true,
                            end: end_value
                        },
                        "{name}"
                    );
                    assert_eq!(end.spg, [0; 25]);
                }),
            ));
        }
        let (input, _) = fixtures[2];
        let tampers: [(&str, usize, u8); 4] = [
            ("fw-cth-wots-tamper-tag0-bit0", TAGS, 0),
            ("fw-cth-wots-tamper-tag1-bit127", TAGS + 31, 7),
            ("fw-cth-wots-tamper-value3-bit127", VALUES + 63, 7),
            ("fw-cth-wots-reject-layer64", LAYER, 6),
        ];
        for (name, addr, bit) in tampers {
            let case = firmware_case(name, &image, |vm| {
                input.install(vm).unwrap();
                flip(vm, addr, bit);
            });
            cases.push((
                case,
                Box::new(move |end| {
                    let out = CthWotsOutput::read(end).unwrap();
                    assert_eq!(
                        out,
                        CthWotsOutput {
                            accepted: false,
                            end: [0; 4]
                        },
                        "{name}"
                    );
                    assert_eq!((end.regs, end.spg), ([0; 16], [0; 25]), "{name}");
                }),
            ));
        }
    }
    cases
}

/// The whole suite as text, and what it executed.
fn build() -> (String, Coverage) {
    let mut coverage = Coverage::default();
    let mut cases = String::new();
    let mut count = 0;
    let mut reseeded = Vec::new();
    for index in 0..RANDOM_CASES {
        let (case, end) = (0..8)
            .find_map(|attempt| {
                let case = random_case(index, attempt);
                let end = execute(&case.start, &mut coverage)?;
                if attempt > 0 {
                    reseeded.push(index);
                }
                Some((case, end))
            })
            .unwrap_or_else(|| panic!("case {index} does not halt"));
        emit(&mut cases, count, &case, &end);
        count += 1;
    }
    let random_steps = coverage.steps;
    let firmware = firmware_cases();
    let firmware_count = firmware.len();
    for (case, check) in firmware {
        let end = execute(&case.start, &mut coverage)
            .unwrap_or_else(|| panic!("{} does not halt", case.name));
        assert!(
            end.violations.is_empty() && end.csrs.ecause == 0,
            "{}",
            case.name
        );
        check(&end);
        eprintln!(
            "{}: R4={} steps={} cycles={}",
            case.name,
            end.regs[4],
            end.trace.observations.len(),
            end.csrs.cycles
        );
        emit(&mut cases, count, &case, &end);
        count += 1;
    }

    let missing: Vec<String> = all_forms()
        .into_iter()
        .filter(|form| !coverage.forms.contains_key(form))
        .collect();
    assert!(
        missing.is_empty(),
        "instruction forms never retired: {missing:?}"
    );
    assert!(
        coverage.majors.iter().all(|&n| n > 0),
        "{:?}",
        coverage.majors
    );
    assert!(
        coverage.traps[1..].iter().all(|&n| n > 0),
        "{:?}",
        coverage.traps
    );

    let mut text = String::new();
    writeln!(text, "{FORMAT} {count:x} {SRAM_WORDS:x}").unwrap();
    writeln!(
        text,
        "# crates/qsag-ass2/examples/export_cosim_vectors.rs documents this format."
    )
    .unwrap();
    writeln!(
        text,
        "# {RANDOM_CASES} random cases (seed {SEED:#x}), {firmware_count} firmware cases. \
         Counts in these comments are decimal."
    )
    .unwrap();
    writeln!(
        text,
        "# instruction attempts: {} random, {} firmware",
        random_steps,
        coverage.steps - random_steps
    )
    .unwrap();
    writeln!(
        text,
        "# reseeded random cases (first program did not halt): {reseeded:?}"
    )
    .unwrap();
    write!(text, "# retired per major opcode:").unwrap();
    for (op, n) in coverage.majors.iter().enumerate() {
        write!(text, " {op:x}={n}").unwrap();
    }
    write!(text, "\n# traps per cause:").unwrap();
    for (name, cause) in [
        ("IllegalInsn", VmTrap::IllegalInsn),
        ("EnvCall", VmTrap::EnvCall),
        ("MisalignedPc", VmTrap::MisalignedPc),
        ("MisalignedMem", VmTrap::MisalignedMem),
        ("MemFault", VmTrap::MemFault),
    ] {
        write!(text, " {name}={}", coverage.traps[cause as usize]).unwrap();
    }
    writeln!(
        text,
        "\n# distinct instruction forms retired: {}",
        coverage.forms.len()
    )
    .unwrap();
    text.push_str(&cases);
    writeln!(text, "EOF {count:x}").unwrap();
    (text, coverage)
}

/// The records of a suite, comments dropped.
struct Reader<'a> {
    /// One-based line number and text.
    lines: Vec<(usize, &'a str)>,
    at: usize,
}
impl<'a> Reader<'a> {
    fn new(text: &'a str) -> Self {
        let lines = text.lines().enumerate().map(|(i, line)| (i + 1, line));
        Self {
            lines: lines.filter(|(_, line)| !line.starts_with('#')).collect(),
            at: 0,
        }
    }
    /// The fields after the tag when the next record has tag `tag`.
    fn fields(&mut self, tag: &str) -> Option<(usize, Vec<&'a str>)> {
        let (number, line) = *self.lines.get(self.at)?;
        let mut fields = line.split(' ');
        if fields.next() != Some(tag) {
            return None;
        }
        self.at += 1;
        Some((number, fields.collect()))
    }
    /// The next record, which must be `tag` followed by `count` hexadecimal numbers.
    fn record(&mut self, tag: &str, count: usize) -> Result<Vec<u64>, String> {
        let at = self.lines.get(self.at).map_or(0, |(number, _)| *number);
        let (number, fields) = self
            .fields(tag)
            .ok_or(format!("line {at}: expected a {tag} record"))?;
        let values: Result<Vec<u64>, _> = fields
            .iter()
            .map(|field| u64::from_str_radix(field, 16))
            .collect();
        match values {
            Ok(values) if values.len() == count => Ok(values),
            _ => Err(format!(
                "line {number}: {tag} needs {count} hexadecimal fields"
            )),
        }
    }
    /// Apply a run of `IM` or `XM` records to `vm`.
    fn memory(&mut self, tag: &str, words: usize, vm: &mut Ass2Vm) -> Result<(), String> {
        let mut next = 0;
        while self
            .lines
            .get(self.at)
            .is_some_and(|(_, line)| line.starts_with(tag))
        {
            let number = self.lines[self.at].0;
            let record = self.record(tag, 2)?;
            let (w, value) = (record[0], record[1]);
            if w < next || w >= words as u64 {
                return Err(format!(
                    "line {number}: {tag} word out of order or out of range"
                ));
            }
            next = w + 1;
            vm.load_image(8 * w, &value.to_le_bytes())
                .map_err(|e| e.to_string())?;
        }
        Ok(())
    }
}

/// The reference reader: parse `text` and replay every case from its records alone.
/// Returns the number of cases and of instruction attempts.
fn verify(text: &str) -> Result<(usize, u64), String> {
    let mut reader = Reader::new(text);
    let header = reader.record(FORMAT, 2)?;
    let (cases, words) = (header[0] as usize, header[1] as usize);
    let mut total_steps = 0;
    for index in 0..cases {
        let name = match reader.fields("CASE") {
            Some((_, fields)) if fields.len() == 2 && fields[0] == format!("{index:x}") => {
                fields[1]
            }
            _ => return Err(format!("expected CASE {index:x}")),
        };
        let fail = |what: String| format!("case {index:x} {name}: {what}");
        let mut vm = Ass2Vm::new(8 * words);
        vm.pc = reader.record("IPC", 1)?[0];
        vm.regs.copy_from_slice(&reader.record("IR", 16)?);
        vm.spg.copy_from_slice(&reader.record("IS", 25)?);
        reader.memory("IM", words, &mut vm)?;
        let mut final_memory = vm.clone();
        let steps = reader.record("STEPS", 1)?[0];
        let mut expected = Vec::new();
        for tag in ["XPC", "XHALT", "XECAUSE", "XINSTRET", "XCYCLES"] {
            expected.push(reader.record(tag, 1)?[0]);
        }
        let regs = reader.record("XR", 16)?;
        let spg = reader.record("XS", 25)?;
        reader.memory("XM", words, &mut final_memory)?;
        if reader.record("END", 1)?[0] != index as u64 {
            return Err(fail("END names another case".into()));
        }

        for step in 0..steps {
            if vm.halted {
                return Err(fail(format!("halted after {step:x} of {steps:x} steps")));
            }
            vm.step();
        }
        let got = [
            vm.pc,
            vm.halted.into(),
            vm.csrs.ecause,
            vm.csrs.instret,
            vm.csrs.cycles,
        ];
        if got[..] != expected[..] {
            return Err(fail(format!(
                "PC, halted, ECAUSE, INSTRET, CYCLES are {got:x?}, expected {expected:x?}"
            )));
        }
        if vm.regs[..] != regs[..] {
            return Err(fail(format!("R is {:x?}, expected {regs:x?}", vm.regs)));
        }
        if vm.spg[..] != spg[..] {
            return Err(fail(format!("S is {:x?}, expected {spg:x?}", vm.spg)));
        }
        if vm.mem != final_memory.mem {
            return Err(fail("final SRAM differs".into()));
        }
        total_steps += steps;
    }
    if reader.record("EOF", 1)?[0] != cases as u64 || reader.at != reader.lines.len() {
        return Err("EOF record does not close the suite".into());
    }
    Ok((cases, total_steps))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args.as_slice() {
        ["export", path] => {
            let (text, _) = build();
            verify(&text).and_then(|summary| {
                std::fs::write(path, &text).map_err(|e| format!("{path}: {e}"))?;
                Ok(summary)
            })
        }
        ["verify", path] => std::fs::read_to_string(path)
            .map_err(|e| format!("{path}: {e}"))
            .and_then(|text| verify(&text)),
        _ => Err("usage: export_cosim_vectors (export|verify) <file>".into()),
    };
    match result {
        Ok((cases, steps)) => {
            println!("{cases} cases, {steps} instruction attempts: every final state reproduced");
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}
