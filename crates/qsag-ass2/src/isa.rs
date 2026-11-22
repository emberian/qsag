//! The `ASS2 / Dregg-64` instruction set: typed instructions, the 32-bit codec, the fixed
//! cycle-cost table and the disassembler.
//!
//! Every instruction is one little-endian 32-bit word `w` with major opcode `w >> 28` and the
//! standard fields `rd = w[3:0]`, `ra = w[7:4]`, `rb = w[11:8]`, `rc = w[15:12]`,
//! `sub = w[19:16]`, `imm8 = w[27:20]`. [`decode_insn`] is total: it returns `None` exactly for
//! the words whose encoding is illegal, and [`encode_insn`] is its inverse on every decodable
//! word. A `CSRR` or `CSRW` decodes for every 8-bit address; the machine raises `IllegalInsn`
//! when it executes one that names an undefined CSR or the wrong direction of a read-only or
//! write-only one.

use alloc::format;
use alloc::string::String;
use core::fmt::{self, Write};

/// Bytes per instruction.
pub const INSN_BYTES: usize = 4;
/// The canonical `NOP` word (`SYS` sub 6).
pub const NOP_WORD: u32 = 0x0006_0000;
/// Number of sponge lanes `S0..S24`.
pub const SPG_LANES: u8 = 25;
/// Number of quintic extension registers `E0..E4`.
pub const FP5_REGS: u8 = 5;
/// Number of `GF(2^128)` polynomial registers `P0..P11`.
pub const GF128_REGS: u8 = 12;

/// Control and system register addresses and their fixed values.
pub mod csr {
    /// Architecture identifier (read-only).
    pub const ARCH_ID: u8 = 0x00;
    /// Word width in bits (read-only, `64`).
    pub const WORD_BITS: u8 = 0x01;
    /// Trap handler base (read-write, stored as `val & !3`).
    pub const EVEC: u8 = 0x02;
    /// Power control (write-only): bit 0 halts the machine.
    pub const POWER: u8 = 0x03;
    /// Retired instruction counter (read-write).
    pub const INSTRET: u8 = 0x04;
    /// Cycle counter (read-write).
    pub const CYCLES: u8 = 0x05;
    /// Feature bits (read-only).
    pub const FEATURES: u8 = 0x06;
    /// Trap continuation PC (read-write).
    pub const EPC: u8 = 0x08;
    /// Trap cause (read-write).
    pub const ECAUSE: u8 = 0x09;
    /// Debug output byte (write-only).
    pub const DBG_OUT: u8 = 0x0A;
    /// Debug input byte and valid bit (`[8]=rx_valid, [7:0]=rx_byte`, read-only).
    #[cfg(feature = "vm-debug-rx")]
    pub const DBG_IN: u8 = 0x0B;
    /// Master trap enable, bit 0 (read-write).
    pub const EXC_EN: u8 = 0x3F;
    /// Data-independent timing flag (read-only, hardwired `1`).
    pub const DIT: u8 = 0x40;
    /// Tamper wipe (write-only): bit 0 clears `R1..R15` and `S0..S24`.
    pub const ZEROIZE: u8 = 0x41;

    /// Value of [`ARCH_ID`].
    pub const ARCH_ID_VALUE: u64 = 0x4153_5332_0000_0001;
    /// Value of [`WORD_BITS`].
    pub const WORD_BITS_VALUE: u64 = 64;
    /// Value of [`FEATURES`]: `LUT4 | GL64_FP5 | GF128 | KECCAK_POSEIDON2`.
    pub const FEATURES_VALUE: u64 = 0x0000_000F;

    const NAMES: &[(u8, &str)] = &[
        (ARCH_ID, "ARCH_ID"),
        (WORD_BITS, "WORD_BITS"),
        (EVEC, "EVEC"),
        (POWER, "POWER"),
        (INSTRET, "INSTRET"),
        (CYCLES, "CYCLES"),
        (FEATURES, "FEATURES"),
        (EPC, "EPC"),
        (ECAUSE, "ECAUSE"),
        (DBG_OUT, "DBG_OUT"),
        #[cfg(feature = "vm-debug-rx")]
        (DBG_IN, "DBG_IN"),
        (EXC_EN, "EXC_EN"),
        (DIT, "DIT"),
        (ZEROIZE, "ZEROIZE"),
    ];

    /// Name of a defined CSR address.
    pub fn name(addr: u8) -> Option<&'static str> {
        NAMES.iter().find(|(a, _)| *a == addr).map(|(_, n)| *n)
    }

    /// Address of a CSR by its upper-case name.
    pub fn from_name(name: &str) -> Option<u8> {
        NAMES.iter().find(|(_, n)| *n == name).map(|(a, _)| *a)
    }
}

/// Physical `ASS2-0P5` (`SLOT_0P5X0P5`) memory map, `SYS_MMIO` privilege fence, and host link constants.
pub mod mem_map {
    /// Resident Boot, Lifecycle & Crypto `I-ROM` base (`4 KiB`, `X R`).
    pub const IROM_BASE: u64 = 0x0000_0000;
    /// Resident `I-ROM` byte length (`1,024 × 32b`).
    pub const IROM_BYTES: usize = 0x0000_1000;
    /// Authenticated loadable `I-SRAM` (`SRAM1`) base (`512 B`, `X R` during `CMD_EXEC`).
    pub const ISRAM_BASE: u64 = 0x0000_1000;
    /// Authenticated loadable `I-SRAM` byte length (`128 × 32b`).
    pub const ISRAM_BYTES: usize = 0x0000_0200;
    /// Enclave `D-SRAM` (`SRAM0`) base (`512 B`, wiped by 64-cycle hardware scrub FSM).
    pub const DSRAM_BASE: u64 = 0x0001_0000;
    /// Enclave `D-SRAM` byte length (`64 × 64b`).
    pub const DSRAM_BYTES: usize = 0x0000_0200;
    /// Host -> enclave request mailbox base inside `D-SRAM` (`128 B`).
    pub const RX_MBOX_BASE: u64 = 0x0001_0100;
    /// Enclave -> host response mailbox base inside `D-SRAM` (`128 B`).
    pub const TX_MBOX_BASE: u64 = 0x0001_0180;
    /// Privileged `SYS_MMIO` window (`PC >= 0x1000` traps `MemFault` `ecause = 5`).
    pub const SYS_MMIO_BASE: u64 = 0xFFFF_0000;
    /// Privileged `SYS_MMIO` byte span (`128 B`).
    pub const SYS_MMIO_BYTES: usize = 0x0000_0080;
    /// `SYS_MMIO` register byte offsets.
    pub const MMIO_FRAM_XFER: u64 = 0x00;
    pub const MMIO_FRAM_STATUS: u64 = 0x08;
    pub const MMIO_PUF_SYNDROME: u64 = 0x20;
    pub const MMIO_TRNG_DATA: u64 = 0x40;
    pub const MMIO_TRNG_HEALTH: u64 = 0x48;
    pub const MMIO_VERDICT_CTRL: u64 = 0x60;
    pub const MMIO_GPIO_IO: u64 = 0x68;
    pub const MMIO_DBG_UART_DIV: u64 = 0x70;
    /// Host serial link op-prefixes and `QSAG-Wire` (`0x51`) command/error codes.
    pub const LINK_SPI_WRITE: u8 = 0x00;
    pub const LINK_SPI_READ: u8 = 0x02;
    pub const LINK_DIAG_RAW: u8 = 0x05;
    pub const LINK_QSPI_WRITE: u8 = 0x40;
    pub const LINK_QSPI_READ: u8 = 0x42;
    pub const LINK_OSPI_WRITE: u8 = 0x80;
    pub const LINK_OSPI_READ: u8 = 0x82;
    pub const WIRE_MAGIC: u8 = 0x51;
    pub const CMD_IDENT: u8 = 0x01;
    pub const CMD_LOAD_CODE: u8 = 0x30;
    pub const CMD_EXEC: u8 = 0x31;
    pub const E_BUDGET: u16 = 15;
    pub const E_TRAP: u16 = 16;
}

macro_rules! sub_enum {
    ($(#[$meta:meta])* $name:ident { $($(#[$vmeta:meta])* $var:ident = $code:literal => $mn:literal),+ $(,)? }) => {
        $(#[$meta])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        #[repr(u8)]
        pub enum $name { $($(#[$vmeta])* $var = $code),+ }

        impl $name {
            /// Every operation, in encoding order.
            pub const ALL: &'static [Self] = &[$(Self::$var),+];

            /// The 4-bit field value.
            pub const fn code(self) -> u8 {
                self as u8
            }

            /// The operation for a 4-bit field value; `None` for a reserved value.
            pub const fn from_code(code: u8) -> Option<Self> {
                match code {
                    $($code => Some(Self::$var),)+
                    _ => None,
                }
            }

            /// The canonical assembler mnemonic.
            pub const fn mnemonic(self) -> &'static str {
                match self { $(Self::$var => $mn),+ }
            }

            /// The operation for a canonical (upper-case) mnemonic.
            pub fn from_mnemonic(mnemonic: &str) -> Option<Self> {
                match mnemonic {
                    $($mn => Some(Self::$var),)+
                    _ => None,
                }
            }
        }
    };
}

sub_enum! {
    /// `0x2 ALU` operation (`sub` field).
    AluOp {
        /// `(R[ra] + R[rb]) mod 2^64`.
        Add = 0 => "ADD",
        /// `(R[ra] - R[rb]) mod 2^64`.
        Sub = 1 => "SUB",
        /// Logical left shift; `0` for a shift amount `>= 64`.
        Shl = 2 => "SHL",
        /// Logical right shift; `0` for a shift amount `>= 64`.
        Shr = 3 => "SHR",
        /// Arithmetic right shift; the sign fill for a shift amount `>= 64`.
        Asr = 4 => "ASR",
        /// Rotate left by `R[rb] & 63`.
        Rol = 5 => "ROL",
        /// Rotate right by `R[rb] & 63`.
        Ror = 6 => "ROR",
        /// Low 64 bits of the product.
        Mul64 = 7 => "MUL64",
        /// High 64 bits of the unsigned 128-bit product.
        Mulhu64 = 8 => "MULHU64",
    }
}

sub_enum! {
    /// `0x3 ALUI` operation (`fn4` in the `rb` field).
    AluiOp {
        /// Add the sign-extended immediate.
        Addi = 0 => "ADDI",
        /// Add the zero-extended immediate.
        Addiu = 1 => "ADDIU",
        /// XOR with the zero-extended immediate.
        Xori = 2 => "XORI",
        /// AND with the zero-extended immediate.
        Andi = 3 => "ANDI",
        /// OR with the zero-extended immediate.
        Ori = 4 => "ORI",
        /// Logical left shift by `imm16 < 64`.
        Shli = 5 => "SHLI",
        /// Logical right shift by `imm16 < 64`.
        Shri = 6 => "SHRI",
        /// Arithmetic right shift by `imm16 < 64`.
        Asri = 7 => "ASRI",
        /// Rotate left by `imm16 < 64`.
        Roli = 8 => "ROLI",
        /// `(R[ra] << 16) | imm16`.
        Slk16 = 9 => "SLK16",
    }
}

impl AluiOp {
    /// Whether the immediate is a shift amount and must be `< 64`.
    pub const fn is_shift(self) -> bool {
        matches!(self, Self::Shli | Self::Shri | Self::Asri | Self::Roli)
    }
}

sub_enum! {
    /// `0x4 IMM20` mode (`mode4` in the `ra` field).
    Imm20Mode {
        /// `R[rd] := zext20(imm20)`.
        Movz20 = 0 => "MOVZ20",
        /// `R[rd] := sext20(imm20)`.
        Movs20 = 1 => "MOVS20",
        /// `R[rd] := PC + (sext20(imm20) << 2)`.
        Auipc = 2 => "AUIPC",
    }
}

sub_enum! {
    /// `0x7 LOAD` mode (`mode4` in the `rb` field).
    LoadMode {
        /// Aligned 64-bit little-endian load at `R[ra] + (simm16 << 3)`.
        Ld64 = 0 => "LD64",
        /// Zero-extended byte load at `R[ra] + simm16`.
        Ldbu = 1 => "LDBU",
    }
}

sub_enum! {
    /// `0x8 STORE` mode (`mode4` in the `rb` field).
    StoreMode {
        /// Aligned 64-bit little-endian store at `R[ra] + (simm16 << 3)`.
        St64 = 0 => "ST64",
        /// Byte store at `R[ra] + simm16`.
        Stb = 1 => "STB",
    }
}

sub_enum! {
    /// `0x9 BR` condition (`bop4` in the `ra` field).
    BrOp {
        /// Taken when the register is zero.
        Beqz = 0 => "BEQZ",
        /// Taken when the register is non-zero.
        Bnez = 1 => "BNEZ",
        /// Taken when the register is negative as a signed 64-bit value.
        Bltz = 2 => "BLTZ",
        /// Taken when the register is non-negative as a signed 64-bit value.
        Bgez = 3 => "BGEZ",
    }
}

/// One `ASS2 / Dregg-64` instruction.
///
/// Register fields are 4-bit indices (`0..=15`); the other fields carry the ranges documented
/// on each variant. A value outside its range is rejected by [`encode_insn`] and is never
/// produced by [`decode_insn`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ass2Insn {
    // ---- 0x0 SYS -------------------------------------------------------------------------
    /// `EXC` (`0x0000_0000`): software trap.
    Exc,
    /// `ERET`: `PC := EPC & !3; EXC_EN := 1`.
    Eret,
    /// `CSRR rd, csr8`.
    Csrr { rd: u8, csr: u8 },
    /// `CSRW ra, csr8`.
    Csrw { ra: u8, csr: u8 },
    /// `ZEROIZE`: clear `R1..R15` and `S0..S24`.
    Zeroize,
    /// `HALT`.
    Halt,
    /// `NOP`.
    Nop,
    // ---- 0x1 LUT4 ------------------------------------------------------------------------
    /// `LUT4 rd, ra, rb, M`: bit `k` of the result is bit `2*ra[k] + rb[k]` of `m` (`m < 16`).
    Lut4 { rd: u8, ra: u8, rb: u8, m: u8 },
    // ---- 0x2 ALU -------------------------------------------------------------------------
    /// Three-register arithmetic.
    Alu { op: AluOp, rd: u8, ra: u8, rb: u8 },
    // ---- 0x3 ALUI ------------------------------------------------------------------------
    /// Register-immediate arithmetic; `imm16 < 64` for the shifts.
    Alui {
        op: AluiOp,
        rd: u8,
        ra: u8,
        imm16: u16,
    },
    // ---- 0x4 IMM20 -----------------------------------------------------------------------
    /// 20-bit immediate load; `imm20` is the raw field (`< 2^20`).
    Imm20 { mode: Imm20Mode, rd: u8, imm20: u32 },
    // ---- 0x5 CMP -------------------------------------------------------------------------
    /// `CMP rd, ra, rb, flags4` with `flags = EQ | GT << 1 | SN << 2 | IV << 3` (`< 16`).
    Cmp { rd: u8, ra: u8, rb: u8, flags: u8 },
    // ---- 0x6 SEL / byte manipulation -------------------------------------------------------
    /// `SEL rd, ra, rb, rc`: `R[rd] := if R[rc] == 0 { R[ra] } else { R[rb] }`.
    Sel { rd: u8, ra: u8, rb: u8, rc: u8 },
    /// `BEXTU rd, ra, idx, len`: zero-extended `len` bytes (`1..=8`) from byte `idx` (`0..=7`).
    Bextu { rd: u8, ra: u8, idx: u8, len: u8 },
    /// `BEXTS rd, ra, idx, len`: sign-extended `len` bytes (`1..=8`) from byte `idx` (`0..=7`).
    Bexts { rd: u8, ra: u8, idx: u8, len: u8 },
    /// `BSWAP64 rd, ra`.
    Bswap64 { rd: u8, ra: u8 },
    // ---- 0x7 LOAD / 0x8 STORE --------------------------------------------------------------
    /// `LD64` / `LDBU`; `simm16` is the raw field (scaled by 8 for `LD64`).
    Load {
        mode: LoadMode,
        rd: u8,
        ra: u8,
        simm16: i16,
    },
    /// `ST64` / `STB` of `R[rs]`; `simm16` is the raw field (scaled by 8 for `ST64`).
    Store {
        mode: StoreMode,
        rs: u8,
        ra: u8,
        simm16: i16,
    },
    // ---- 0x9 BR / 0xA JAL / 0xB JALR -------------------------------------------------------
    /// Conditional branch on `R[cond]` to `PC + 4 + (off20 << 2)`; `off20` in `-2^19..2^19`.
    Br { op: BrOp, cond: u8, off20: i32 },
    /// `JAL rd, off24`: link and jump to `PC + 4 + (off24 << 2)`; `off24` in `-2^23..2^23`.
    Jal { rd: u8, off24: i32 },
    /// `JALR rd, ra, simm16`: link and jump to `R[ra] + (simm16 << 2)`.
    Jalr { rd: u8, ra: u8, simm16: i16 },
    // ---- 0xC SPG ---------------------------------------------------------------------------
    /// `SGET rd, S[sidx]` (`sidx < 25`).
    Sget { rd: u8, sidx: u8 },
    /// `SPUT S[sidx], ra`.
    Sput { sidx: u8, ra: u8 },
    /// `SXOR S[sidx], ra`.
    Sxor { sidx: u8, ra: u8 },
    /// `SZERO`: clear `S0..S24`.
    Szero,
    /// `SLD64 S[sidx], [ra + off8 * 8]`.
    Sld64 { sidx: u8, ra: u8, off8: i8 },
    /// `SST64 [ra + off8 * 8], S[sidx]`.
    Sst64 { sidx: u8, ra: u8, off8: i8 },
    // ---- 0xD GL64 / FP5 --------------------------------------------------------------------
    /// `GL.MAC rd, ra, rb, rc`: `R[ra] * R[rb] + R[rc] mod p`.
    GlMac { rd: u8, ra: u8, rb: u8, rc: u8 },
    /// `GL.ADD rd, ra, rb`.
    GlAdd { rd: u8, ra: u8, rb: u8 },
    /// `GL.SUB rd, ra, rb`.
    GlSub { rd: u8, ra: u8, rb: u8 },
    /// `GL.SBOX7 rd, ra`: `R[ra]^7 mod p`.
    GlSbox7 { rd: u8, ra: u8 },
    /// `FP5.MUL ed, ea, eb` (indices `< 5`).
    Fp5Mul { ed: u8, ea: u8, eb: u8 },
    /// `FP5.ADD ed, ea, eb`.
    Fp5Add { ed: u8, ea: u8, eb: u8 },
    /// `FP5.SUB ed, ea, eb`.
    Fp5Sub { ed: u8, ea: u8, eb: u8 },
    // ---- 0xE GF128 -------------------------------------------------------------------------
    /// `GF128.MUL pd, pa, pb` (indices `< 12`).
    Gf128Mul { pd: u8, pa: u8, pb: u8 },
    /// `GF128.XOR pd, pa, pb`.
    Gf128Xor { pd: u8, pa: u8, pb: u8 },
    // ---- 0xF PERM --------------------------------------------------------------------------
    /// `KECCAK.F1600 rounds`: the last `rounds` (`12` or `24`) rounds of `Keccak-f[1600]`.
    KeccakF1600 { rounds: u8 },
    /// `POSEIDON2.GL24`: width-24 Poseidon2 on `S0..S23`.
    Poseidon2Gl24,
    /// `POSEIDON2.GL12`: width-12 Poseidon2 on `S0..S11`.
    Poseidon2Gl12,
}

/// A field of an [`Ass2Insn`] that does not fit its encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CodecError {
    /// A register index above 15.
    Register { field: &'static str, value: u8 },
    /// A small index or table field at or above its bound.
    Index {
        field: &'static str,
        value: u8,
        bound: u8,
    },
    /// An immediate outside its field.
    Immediate {
        field: &'static str,
        value: i64,
        bits: u32,
    },
    /// A `BEXTU`/`BEXTS` byte length outside `1..=8`.
    ByteLen { value: u8 },
    /// A `KECCAK.F1600` round count other than 12 or 24.
    KeccakRounds { value: u8 },
}

impl fmt::Display for CodecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Register { field, value } => {
                write!(f, "register field `{field}` = {value} is above 15")
            }
            Self::Index {
                field,
                value,
                bound,
            } => write!(f, "field `{field}` = {value} must be below {bound}"),
            Self::Immediate { field, value, bits } => {
                write!(
                    f,
                    "immediate `{field}` = {value} does not fit in {bits} bits"
                )
            }
            Self::ByteLen { value } => write!(f, "byte length {value} is outside 1..=8"),
            Self::KeccakRounds { value } => {
                write!(f, "Keccak round count {value} is neither 12 nor 24")
            }
        }
    }
}

impl core::error::Error for CodecError {}

const fn reg(field: &'static str, value: u8) -> Result<u32, CodecError> {
    if value < 16 {
        Ok(value as u32)
    } else {
        Err(CodecError::Register { field, value })
    }
}

const fn index(field: &'static str, value: u8, bound: u8) -> Result<u32, CodecError> {
    if value < bound {
        Ok(value as u32)
    } else {
        Err(CodecError::Index {
            field,
            value,
            bound,
        })
    }
}

const fn simm(field: &'static str, value: i32, bits: u32) -> Result<u32, CodecError> {
    let limit = 1i32 << (bits - 1);
    if value >= -limit && value < limit {
        Ok((value as u32) & ((1u32 << bits) - 1))
    } else {
        Err(CodecError::Immediate {
            field,
            value: value as i64,
            bits,
        })
    }
}

const fn byte_len_code(len: u8) -> Result<u32, CodecError> {
    if len >= 1 && len <= 8 {
        Ok((len & 7) as u32)
    } else {
        Err(CodecError::ByteLen { value: len })
    }
}

/// Standard-field word: `op | imm8 | sub | rc | rb | ra | rd`.
const fn word(op: u32, rd: u32, ra: u32, rb: u32, rc: u32, sub: u32, imm8: u32) -> u32 {
    (op << 28) | (imm8 << 20) | (sub << 16) | (rc << 12) | (rb << 8) | (ra << 4) | rd
}

/// 16-bit-immediate word: `op | imm16 | f8 | f4 | f0`.
const fn word16(op: u32, f0: u32, f4: u32, f8: u32, imm16: u16) -> u32 {
    (op << 28) | ((imm16 as u32) << 12) | (f8 << 8) | (f4 << 4) | f0
}

/// Encode an instruction into its 32-bit word.
///
/// Fails exactly when a field is outside its documented range; on success
/// `decode_insn(word) == Some(*insn)`.
pub fn encode_insn(insn: &Ass2Insn) -> Result<u32, CodecError> {
    use Ass2Insn::*;
    Ok(match *insn {
        Exc => 0,
        Eret => word(0x0, 0, 0, 0, 0, 1, 0),
        Csrr { rd, csr } => word(0x0, reg("rd", rd)?, 0, 0, 0, 2, csr as u32),
        Csrw { ra, csr } => word(0x0, 0, reg("ra", ra)?, 0, 0, 3, csr as u32),
        Zeroize => word(0x0, 0, 0, 0, 0, 4, 0),
        Halt => word(0x0, 0, 0, 0, 0, 5, 0),
        Nop => NOP_WORD,
        Lut4 { rd, ra, rb, m } => word(
            0x1,
            reg("rd", rd)?,
            reg("ra", ra)?,
            reg("rb", rb)?,
            0,
            index("M", m, 16)?,
            0,
        ),
        Alu { op, rd, ra, rb } => word(
            0x2,
            reg("rd", rd)?,
            reg("ra", ra)?,
            reg("rb", rb)?,
            0,
            op.code() as u32,
            0,
        ),
        Alui { op, rd, ra, imm16 } => {
            if op.is_shift() && imm16 >= 64 {
                return Err(CodecError::Immediate {
                    field: "shamt",
                    value: imm16 as i64,
                    bits: 6,
                });
            }
            word16(0x3, reg("rd", rd)?, reg("ra", ra)?, op.code() as u32, imm16)
        }
        Imm20 { mode, rd, imm20 } => {
            if imm20 >> 20 != 0 {
                return Err(CodecError::Immediate {
                    field: "imm20",
                    value: imm20 as i64,
                    bits: 20,
                });
            }
            (0x4 << 28) | (imm20 << 8) | ((mode.code() as u32) << 4) | reg("rd", rd)?
        }
        Cmp { rd, ra, rb, flags } => word(
            0x5,
            reg("rd", rd)?,
            reg("ra", ra)?,
            reg("rb", rb)?,
            index("flags4", flags, 16)?,
            0,
            0,
        ),
        Sel { rd, ra, rb, rc } => word(
            0x6,
            reg("rd", rd)?,
            reg("ra", ra)?,
            reg("rb", rb)?,
            reg("rc", rc)?,
            0,
            0,
        ),
        Bextu { rd, ra, idx, len } => word(
            0x6,
            reg("rd", rd)?,
            reg("ra", ra)?,
            index("byte_idx", idx, 8)?,
            byte_len_code(len)?,
            1,
            0,
        ),
        Bexts { rd, ra, idx, len } => word(
            0x6,
            reg("rd", rd)?,
            reg("ra", ra)?,
            index("byte_idx", idx, 8)?,
            byte_len_code(len)?,
            2,
            0,
        ),
        Bswap64 { rd, ra } => word(0x6, reg("rd", rd)?, reg("ra", ra)?, 0, 0, 3, 0),
        Load {
            mode,
            rd,
            ra,
            simm16,
        } => word16(
            0x7,
            reg("rd", rd)?,
            reg("ra", ra)?,
            mode.code() as u32,
            simm16 as u16,
        ),
        Store {
            mode,
            rs,
            ra,
            simm16,
        } => word16(
            0x8,
            reg("rs", rs)?,
            reg("ra", ra)?,
            mode.code() as u32,
            simm16 as u16,
        ),
        Br { op, cond, off20 } => {
            (0x9 << 28)
                | (simm("off20", off20, 20)? << 8)
                | ((op.code() as u32) << 4)
                | reg("cond", cond)?
        }
        Jal { rd, off24 } => (0xA << 28) | (simm("off24", off24, 24)? << 4) | reg("rd", rd)?,
        Jalr { rd, ra, simm16 } => word16(0xB, reg("rd", rd)?, reg("ra", ra)?, 0, simm16 as u16),
        Sget { rd, sidx } => (0xC << 28) | (index("sidx", sidx, SPG_LANES)? << 12) | reg("rd", rd)?,
        Sput { sidx, ra } => {
            (0xC << 28) | (index("sidx", sidx, SPG_LANES)? << 12) | (1 << 8) | (reg("ra", ra)? << 4)
        }
        Sxor { sidx, ra } => {
            (0xC << 28) | (index("sidx", sidx, SPG_LANES)? << 12) | (2 << 8) | (reg("ra", ra)? << 4)
        }
        Szero => (0xC << 28) | (3 << 8),
        Sld64 { sidx, ra, off8 } => {
            (0xC << 28)
                | ((off8 as u8 as u32) << 20)
                | (index("sidx", sidx, SPG_LANES)? << 12)
                | (4 << 8)
                | (reg("ra", ra)? << 4)
        }
        Sst64 { sidx, ra, off8 } => {
            (0xC << 28)
                | ((off8 as u8 as u32) << 20)
                | (index("sidx", sidx, SPG_LANES)? << 12)
                | (5 << 8)
                | (reg("ra", ra)? << 4)
        }
        GlMac { rd, ra, rb, rc } => word(
            0xD,
            reg("rd", rd)?,
            reg("ra", ra)?,
            reg("rb", rb)?,
            reg("rc", rc)?,
            0,
            0,
        ),
        GlAdd { rd, ra, rb } => word(0xD, reg("rd", rd)?, reg("ra", ra)?, reg("rb", rb)?, 0, 1, 0),
        GlSub { rd, ra, rb } => word(0xD, reg("rd", rd)?, reg("ra", ra)?, reg("rb", rb)?, 0, 2, 0),
        GlSbox7 { rd, ra } => word(0xD, reg("rd", rd)?, reg("ra", ra)?, 0, 0, 3, 0),
        Fp5Mul { ed, ea, eb } => fp5_word(4, ed, ea, eb)?,
        Fp5Add { ed, ea, eb } => fp5_word(5, ed, ea, eb)?,
        Fp5Sub { ed, ea, eb } => fp5_word(6, ed, ea, eb)?,
        Gf128Mul { pd, pa, pb } => gf128_word(0, pd, pa, pb)?,
        Gf128Xor { pd, pa, pb } => gf128_word(1, pd, pa, pb)?,
        KeccakF1600 { rounds } => {
            if rounds != 12 && rounds != 24 {
                return Err(CodecError::KeccakRounds { value: rounds });
            }
            word(0xF, 0, 0, 0, 0, 0, rounds as u32)
        }
        Poseidon2Gl24 => word(0xF, 0, 0, 0, 0, 1, 0),
        Poseidon2Gl12 => word(0xF, 0, 0, 0, 0, 2, 0),
    })
}

fn fp5_word(sub: u32, ed: u8, ea: u8, eb: u8) -> Result<u32, CodecError> {
    Ok(word(
        0xD,
        index("ed", ed, FP5_REGS)?,
        index("ea", ea, FP5_REGS)?,
        index("eb", eb, FP5_REGS)?,
        0,
        sub,
        0,
    ))
}

fn gf128_word(sub: u32, pd: u8, pa: u8, pb: u8) -> Result<u32, CodecError> {
    Ok(word(
        0xE,
        index("pd", pd, GF128_REGS)?,
        index("pa", pa, GF128_REGS)?,
        index("pb", pb, GF128_REGS)?,
        0,
        sub,
        0,
    ))
}

/// Sign-extend the low `bits` bits of `value`.
const fn sext(value: u32, bits: u32) -> i32 {
    let shift = 32 - bits;
    ((value << shift) as i32) >> shift
}

/// Decode a 32-bit word. `None` means `IllegalInsn` by encoding: a reserved opcode
/// sub-function, a non-zero reserved field or an out-of-range index.
pub fn decode_insn(w: u32) -> Option<Ass2Insn> {
    use Ass2Insn::*;
    let rd = (w & 0xF) as u8;
    let ra = ((w >> 4) & 0xF) as u8;
    let rb = ((w >> 8) & 0xF) as u8;
    let rc = ((w >> 12) & 0xF) as u8;
    let sub = ((w >> 16) & 0xF) as u8;
    let imm8 = ((w >> 20) & 0xFF) as u8;
    let imm16 = ((w >> 12) & 0xFFFF) as u16;
    match w >> 28 {
        0x0 => match sub {
            0 => (w == 0).then_some(Exc),
            1 => (w & 0x0FF0_FFFF == 0).then_some(Eret),
            2 => (ra == 0 && rb == 0 && rc == 0).then_some(Csrr { rd, csr: imm8 }),
            3 => (rd == 0 && rb == 0 && rc == 0).then_some(Csrw { ra, csr: imm8 }),
            4 => (w & 0x0FF0_FFFF == 0).then_some(Zeroize),
            5 => (w & 0x0FF0_FFFF == 0).then_some(Halt),
            6 => (w == NOP_WORD).then_some(Nop),
            _ => None,
        },
        0x1 => (rc == 0 && imm8 == 0).then_some(Lut4 { rd, ra, rb, m: sub }),
        0x2 => {
            if rc != 0 || imm8 != 0 {
                return None;
            }
            Some(Alu {
                op: AluOp::from_code(sub)?,
                rd,
                ra,
                rb,
            })
        }
        0x3 => {
            let op = AluiOp::from_code(rb)?;
            if op.is_shift() && (imm16 >> 6) != 0 {
                return None;
            }
            Some(Alui { op, rd, ra, imm16 })
        }
        0x4 => Some(Imm20 {
            mode: Imm20Mode::from_code(ra)?,
            rd,
            imm20: (w >> 8) & 0xF_FFFF,
        }),
        0x5 => (sub == 0 && imm8 == 0).then_some(Cmp {
            rd,
            ra,
            rb,
            flags: rc,
        }),
        0x6 => {
            if imm8 != 0 {
                return None;
            }
            let len = if rc & 7 == 0 { 8 } else { rc & 7 };
            match sub {
                0 => Some(Sel { rd, ra, rb, rc }),
                1 => ((rb >> 3) == 0 && (rc >> 3) == 0).then_some(Bextu {
                    rd,
                    ra,
                    idx: rb,
                    len,
                }),
                2 => ((rb >> 3) == 0 && (rc >> 3) == 0).then_some(Bexts {
                    rd,
                    ra,
                    idx: rb,
                    len,
                }),
                3 => (rb == 0 && rc == 0).then_some(Bswap64 { rd, ra }),
                _ => None,
            }
        }
        0x7 => Some(Load {
            mode: LoadMode::from_code(rb)?,
            rd,
            ra,
            simm16: imm16 as i16,
        }),
        0x8 => Some(Store {
            mode: StoreMode::from_code(rb)?,
            rs: rd,
            ra,
            simm16: imm16 as i16,
        }),
        0x9 => Some(Br {
            op: BrOp::from_code(ra)?,
            cond: rd,
            off20: sext((w >> 8) & 0xF_FFFF, 20),
        }),
        0xA => Some(Jal {
            rd,
            off24: sext((w >> 4) & 0xFF_FFFF, 24),
        }),
        0xB => (rb == 0).then_some(Jalr {
            rd,
            ra,
            simm16: imm16 as i16,
        }),
        0xC => {
            let sidx = ((w >> 12) & 0xFF) as u8;
            let off8 = imm8;
            match rb {
                3 => (rd == 0 && ra == 0 && sidx == 0 && off8 == 0).then_some(Szero),
                0..=5 if sidx >= SPG_LANES => None,
                0 => (ra == 0 && off8 == 0).then_some(Sget { rd, sidx }),
                1 => (rd == 0 && off8 == 0).then_some(Sput { sidx, ra }),
                2 => (rd == 0 && off8 == 0).then_some(Sxor { sidx, ra }),
                4 => (rd == 0).then_some(Sld64 {
                    sidx,
                    ra,
                    off8: off8 as i8,
                }),
                5 => (rd == 0).then_some(Sst64 {
                    sidx,
                    ra,
                    off8: off8 as i8,
                }),
                _ => None,
            }
        }
        0xD => {
            if imm8 != 0 {
                return None;
            }
            let ext = rd < FP5_REGS && ra < FP5_REGS && rb < FP5_REGS && rc == 0;
            match sub {
                0 => Some(GlMac { rd, ra, rb, rc }),
                1 => (rc == 0).then_some(GlAdd { rd, ra, rb }),
                2 => (rc == 0).then_some(GlSub { rd, ra, rb }),
                3 => (rb == 0 && rc == 0).then_some(GlSbox7 { rd, ra }),
                4 => ext.then_some(Fp5Mul {
                    ed: rd,
                    ea: ra,
                    eb: rb,
                }),
                5 => ext.then_some(Fp5Add {
                    ed: rd,
                    ea: ra,
                    eb: rb,
                }),
                6 => ext.then_some(Fp5Sub {
                    ed: rd,
                    ea: ra,
                    eb: rb,
                }),
                _ => None,
            }
        }
        0xE => {
            if imm8 != 0 || rc != 0 || rd >= GF128_REGS || ra >= GF128_REGS || rb >= GF128_REGS {
                return None;
            }
            match sub {
                0 => Some(Gf128Mul {
                    pd: rd,
                    pa: ra,
                    pb: rb,
                }),
                1 => Some(Gf128Xor {
                    pd: rd,
                    pa: ra,
                    pb: rb,
                }),
                _ => None,
            }
        }
        _ => {
            if rd != 0 || ra != 0 || rb != 0 || rc != 0 {
                return None;
            }
            match sub {
                0 => (imm8 == 12 || imm8 == 24).then_some(KeccakF1600 { rounds: imm8 }),
                1 => (imm8 == 0).then_some(Poseidon2Gl24),
                2 => (imm8 == 0).then_some(Poseidon2Gl12),
                _ => None,
            }
        }
    }
}

/// Encode an instruction as its four little-endian bytes.
pub fn encode_insn_le(insn: &Ass2Insn) -> Result<[u8; 4], CodecError> {
    encode_insn(insn).map(u32::to_le_bytes)
}

/// Decode four little-endian bytes.
pub fn decode_insn_le(bytes: [u8; 4]) -> Option<Ass2Insn> {
    decode_insn(u32::from_le_bytes(bytes))
}

/// Fixed latency of an instruction in clock cycles. It depends only on the opcode and
/// sub-function (and, for `KECCAK.F1600`, on the public round count), never on operand values.
pub const fn cycle_cost(insn: &Ass2Insn) -> u64 {
    use Ass2Insn::*;
    match *insn {
        Alu {
            op: AluOp::Mul64 | AluOp::Mulhu64,
            ..
        } => 4,
        Load { .. } | Store { .. } | Sld64 { .. } | Sst64 { .. } => 2,
        GlMac { .. } => 4,
        GlSbox7 { .. } => 12,
        Fp5Mul { .. } => 104,
        Fp5Add { .. } | Fp5Sub { .. } => 5,
        Gf128Mul { .. } => 4,
        KeccakF1600 { rounds } => rounds as u64,
        Poseidon2Gl24 => 216,
        Poseidon2Gl12 => 120,
        _ => 1,
    }
}

impl Ass2Insn {
    /// The major opcode `0x0..=0xF`.
    pub const fn major_opcode(&self) -> u8 {
        use Ass2Insn::*;
        match self {
            Exc | Eret | Csrr { .. } | Csrw { .. } | Zeroize | Halt | Nop => 0x0,
            Lut4 { .. } => 0x1,
            Alu { .. } => 0x2,
            Alui { .. } => 0x3,
            Imm20 { .. } => 0x4,
            Cmp { .. } => 0x5,
            Sel { .. } | Bextu { .. } | Bexts { .. } | Bswap64 { .. } => 0x6,
            Load { .. } => 0x7,
            Store { .. } => 0x8,
            Br { .. } => 0x9,
            Jal { .. } => 0xA,
            Jalr { .. } => 0xB,
            Sget { .. } | Sput { .. } | Sxor { .. } | Szero | Sld64 { .. } | Sst64 { .. } => 0xC,
            GlMac { .. }
            | GlAdd { .. }
            | GlSub { .. }
            | GlSbox7 { .. }
            | Fp5Mul { .. }
            | Fp5Add { .. }
            | Fp5Sub { .. } => 0xD,
            Gf128Mul { .. } | Gf128Xor { .. } => 0xE,
            KeccakF1600 { .. } | Poseidon2Gl24 | Poseidon2Gl12 => 0xF,
        }
    }
}

/// `CMP` predicate aliases: `(suffix, flags4)`.
pub const CMP_ALIASES: [(&str, u8); 10] = [
    ("EQ", 0b0001),
    ("NE", 0b1001),
    ("LTU", 0b1011),
    ("GEU", 0b0011),
    ("GTU", 0b0010),
    ("LEU", 0b1010),
    ("LTS", 0b1111),
    ("GES", 0b0111),
    ("GTS", 0b0110),
    ("LES", 0b1110),
];

fn mem_operand(ra: u8, disp: i64) -> String {
    match disp {
        0 => format!("[R{ra}]"),
        d if d > 0 => format!("[R{ra} + {d}]"),
        d => format!("[R{ra} - {}]", -d),
    }
}

fn csr_operand(csr: u8) -> String {
    match csr::name(csr) {
        Some(name) => String::from(name),
        None => format!("0x{csr:02X}"),
    }
}

/// Canonical assembly text of one instruction; [`crate::asm::assemble`] maps it back to the
/// same word. Memory displacements are printed in bytes, branch and jump offsets in
/// instruction words.
pub fn disassemble_insn(insn: &Ass2Insn) -> String {
    use Ass2Insn::*;
    match *insn {
        Exc => String::from("EXC"),
        Eret => String::from("ERET"),
        Csrr { rd, csr } => format!("CSRR R{rd}, {}", csr_operand(csr)),
        Csrw { ra, csr } => format!("CSRW R{ra}, {}", csr_operand(csr)),
        Zeroize => String::from("ZEROIZE"),
        Halt => String::from("HALT"),
        Nop => String::from("NOP"),
        Lut4 { rd, ra, rb, m } => match (m, rb) {
            (12, 0) => format!("MOV R{rd}, R{ra}"),
            (3, 0) => format!("NOT R{rd}, R{ra}"),
            (6, _) => format!("XOR R{rd}, R{ra}, R{rb}"),
            (8, _) => format!("AND R{rd}, R{ra}, R{rb}"),
            (14, _) => format!("OR R{rd}, R{ra}, R{rb}"),
            (9, _) => format!("XNOR R{rd}, R{ra}, R{rb}"),
            _ => format!("LUT4 R{rd}, R{ra}, R{rb}, 0x{m:X}"),
        },
        Alu { op, rd, ra, rb } => format!("{} R{rd}, R{ra}, R{rb}", op.mnemonic()),
        Alui { op, rd, ra, imm16 } => match op {
            AluiOp::Addi => format!("ADDI R{rd}, R{ra}, {}", imm16 as i16),
            _ if op.is_shift() => format!("{} R{rd}, R{ra}, {imm16}", op.mnemonic()),
            _ => format!("{} R{rd}, R{ra}, 0x{imm16:04X}", op.mnemonic()),
        },
        Imm20 { mode, rd, imm20 } => match mode {
            Imm20Mode::Movz20 => format!("MOVZ20 R{rd}, 0x{imm20:05X}"),
            _ => format!("{} R{rd}, {}", mode.mnemonic(), sext(imm20, 20)),
        },
        Cmp { rd, ra, rb, flags } => match CMP_ALIASES.iter().find(|(_, f)| *f == flags) {
            Some((suffix, _)) => format!("CMP.{suffix} R{rd}, R{ra}, R{rb}"),
            None => format!("CMP R{rd}, R{ra}, R{rb}, 0x{flags:X}"),
        },
        Sel { rd, ra, rb, rc } => format!("SEL R{rd}, R{ra}, R{rb}, R{rc}"),
        Bextu { rd, ra, idx, len } => format!("BEXTU R{rd}, R{ra}, {idx}, {len}"),
        Bexts { rd, ra, idx, len } => format!("BEXTS R{rd}, R{ra}, {idx}, {len}"),
        Bswap64 { rd, ra } => format!("BSWAP64 R{rd}, R{ra}"),
        Load {
            mode,
            rd,
            ra,
            simm16,
        } => {
            let scale = if matches!(mode, LoadMode::Ld64) { 8 } else { 1 };
            format!(
                "{} R{rd}, {}",
                mode.mnemonic(),
                mem_operand(ra, i64::from(simm16) * scale)
            )
        }
        Store {
            mode,
            rs,
            ra,
            simm16,
        } => {
            let scale = if matches!(mode, StoreMode::St64) {
                8
            } else {
                1
            };
            format!(
                "{} {}, R{rs}",
                mode.mnemonic(),
                mem_operand(ra, i64::from(simm16) * scale)
            )
        }
        Br { op, cond, off20 } => format!("{} R{cond}, {off20}", op.mnemonic()),
        Jal { rd, off24 } => format!("JAL R{rd}, {off24}"),
        Jalr { rd, ra, simm16 } => format!("JALR R{rd}, R{ra}, {simm16}"),
        Sget { rd, sidx } => format!("SGET R{rd}, S{sidx}"),
        Sput { sidx, ra } => format!("SPUT S{sidx}, R{ra}"),
        Sxor { sidx, ra } => format!("SXOR S{sidx}, R{ra}"),
        Szero => String::from("SZERO"),
        Sld64 { sidx, ra, off8 } => {
            format!("SLD64 S{sidx}, {}", mem_operand(ra, i64::from(off8) * 8))
        }
        Sst64 { sidx, ra, off8 } => {
            format!("SST64 {}, S{sidx}", mem_operand(ra, i64::from(off8) * 8))
        }
        GlMac { rd, ra, rb, rc } => format!("GL.MAC R{rd}, R{ra}, R{rb}, R{rc}"),
        GlAdd { rd, ra, rb } => format!("GL.ADD R{rd}, R{ra}, R{rb}"),
        GlSub { rd, ra, rb } => format!("GL.SUB R{rd}, R{ra}, R{rb}"),
        GlSbox7 { rd, ra } => format!("GL.SBOX7 R{rd}, R{ra}"),
        Fp5Mul { ed, ea, eb } => format!("FP5.MUL E{ed}, E{ea}, E{eb}"),
        Fp5Add { ed, ea, eb } => format!("FP5.ADD E{ed}, E{ea}, E{eb}"),
        Fp5Sub { ed, ea, eb } => format!("FP5.SUB E{ed}, E{ea}, E{eb}"),
        Gf128Mul { pd, pa, pb } => format!("GF128.MUL P{pd}, P{pa}, P{pb}"),
        Gf128Xor { pd, pa, pb } => format!("GF128.XOR P{pd}, P{pa}, P{pb}"),
        KeccakF1600 { rounds } => format!("KECCAK.F1600 {rounds}"),
        Poseidon2Gl24 => String::from("POSEIDON2.GL24"),
        Poseidon2Gl12 => String::from("POSEIDON2.GL12"),
    }
}

/// Disassemble a little-endian image, one line per 32-bit word with its offset and raw word in
/// a trailing comment. A word that does not decode is listed as `.WORD32`, and up to three
/// trailing bytes as `.BYTES`, so the listing assembles back to exactly `bytes`.
pub fn disassemble_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    let (words, tail) = bytes.as_chunks::<INSN_BYTES>();
    for (i, chunk) in words.iter().enumerate() {
        let w = u32::from_le_bytes(*chunk);
        let text = match decode_insn(w) {
            Some(insn) => disassemble_insn(&insn),
            None => format!(".WORD32 0x{w:08X}"),
        };
        // Writing to a `String` cannot fail.
        let _ = writeln!(out, "{text:<32}; {:08X}: {w:08X}", i * INSN_BYTES);
    }
    if !tail.is_empty() {
        out.push_str(".BYTES ");
        for (i, byte) in tail.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            let _ = write!(out, "0x{byte:02X}");
        }
        out.push('\n');
    }
    out
}
