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
