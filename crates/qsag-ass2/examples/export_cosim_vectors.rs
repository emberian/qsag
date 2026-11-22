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
