//! Two-pass assembler. Labels denote absolute byte addresses. Memory displacements
//! are bytes, and literal branch/jump displacements are signed instruction counts.

use crate::isa::*;
use alloc::{collections::BTreeMap, string::String, vec::Vec};
use core::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assembly {
    pub origin: u64,
    pub bytes: Vec<u8>,
    pub labels: BTreeMap<String, u64>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsmErrorKind {
    Syntax(&'static str),
    UnknownMnemonic(String),
    InvalidOperand(String),
    DuplicateLabel(String),
    UnknownLabel(String),
    Range,
    Alignment,
    Encoding(CodecError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AsmError {
    /// One-based source line.
    pub line: usize,
    pub kind: AsmErrorKind,
}

impl fmt::Display for AsmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "assembly error on line {}: ", self.line)?;
        match &self.kind {
            AsmErrorKind::Syntax(message) => f.write_str(message),
            AsmErrorKind::UnknownMnemonic(s) => write!(f, "unknown mnemonic {s}"),
            AsmErrorKind::InvalidOperand(s) => write!(f, "invalid operand {s}"),
            AsmErrorKind::DuplicateLabel(s) => write!(f, "duplicate label {s}"),
            AsmErrorKind::UnknownLabel(s) => write!(f, "unknown label {s}"),
            AsmErrorKind::Range => f.write_str("value or image size out of range"),
            AsmErrorKind::Alignment => {
                f.write_str("misaligned instruction, target, or displacement")
            }
            AsmErrorKind::Encoding(e) => e.fmt(f),
        }
    }
}
impl core::error::Error for AsmError {}

type Parsed<T> = Result<T, AsmErrorKind>;
type Labels = BTreeMap<String, u64>;

fn invalid(token: &str) -> AsmErrorKind {
    AsmErrorKind::InvalidOperand(token.into())
}

fn integer(token: &str) -> Parsed<i128> {
    let (negative, digits) = match token.as_bytes().first() {
        Some(b'-') => (true, &token[1..]),
        Some(b'+') => (false, &token[1..]),
        _ => (false, token),
    };
    let (radix, digits) = match digits.as_bytes() {
        [b'0', b'x' | b'X', ..] => (16, &digits[2..]),
        [b'0', b'b' | b'B', ..] => (2, &digits[2..]),
        [b'0', b'o' | b'O', ..] => (8, &digits[2..]),
        _ => (10, digits),
    };
    let digits = digits.replace('_', "");
    if !digits.bytes().all(|c| (c as char).is_digit(radix)) {
        return Err(invalid(token));
    }
    let value = u64::from_str_radix(&digits, radix).map_err(|_| invalid(token))? as i128;
    Ok(if negative { -value } else { value })
}

fn number<T: TryFrom<i128>>(s: &str) -> Parsed<T> {
    integer(s)?.try_into().map_err(|_| AsmErrorKind::Range)
}

fn bits(value: i128, width: u32) -> Parsed<u64> {
    // Data and raw signed fields accept either a signed value or the bit pattern.
    if (-(1i128 << (width - 1))..(1i128 << width)).contains(&value) {
        Ok((value & ((1i128 << width) - 1)) as u64)
    } else {
        Err(AsmErrorKind::Range)
    }
}

fn identifier(s: &str) -> bool {
    let mut chars = s.bytes();
    chars
        .next()
        .is_some_and(|c| c.is_ascii_alphabetic() || c == b'_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == b'_')
}

fn address_or_literal(s: &str, labels: &Labels) -> Parsed<i128> {
    if identifier(s) {
        labels
            .get(s)
            .map(|&v| v as i128)
            .ok_or_else(|| AsmErrorKind::UnknownLabel(s.into()))
    } else {
        integer(s)
    }
}

fn relative(s: &str, labels: &Labels, base: u64, width: u32) -> Parsed<i32> {
    let mut v = address_or_literal(s, labels)?;
    if identifier(s) {
        v -= i128::from(base);
        if v % 4 != 0 {
            return Err(AsmErrorKind::Alignment);
        }
        v /= 4;
    }
    let limit = 1i128 << (width - 1);
    if (-limit..limit).contains(&v) {
        Ok(v as i32)
    } else {
        Err(AsmErrorKind::Range)
    }
}

fn bank(s: &str, prefix: u8, size: u8) -> Parsed<u8> {
    let (first, rest) = s.as_bytes().split_first().ok_or_else(|| invalid(s))?;
    if first.to_ascii_uppercase() == prefix
        && !rest.is_empty()
        && rest.iter().all(u8::is_ascii_digit)
    {
        if let Some(n) = s[1..].parse::<u8>().ok().filter(|n| *n < size) {
            return Ok(n);
        }
    }
    Err(invalid(s))
}

fn reg(s: &str) -> Parsed<u8> {
    match s.to_ascii_uppercase().as_str() {
        "ZERO" => Ok(0),
        "SP" => Ok(1),
        "FP" => Ok(2),
        "RA" => Ok(3),
        name if name.starts_with('A') => Ok(bank(s, b'A', 6)? + 4),
        name if name.starts_with('T') => Ok(bank(s, b'T', 6)? + 10),
        _ => bank(s, b'R', 16),
    }
}

fn memory(s: &str, scale: i128) -> Parsed<(u8, i128)> {
    let expr = s
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| invalid(s))?
        .trim();
    let (base, displacement) = match expr.find(['+', '-']) {
        Some(i) => {
            let amount = integer(expr[i + 1..].trim())?;
            if expr[i + 1..].trim().starts_with(['+', '-']) {
                return Err(invalid(s));
            }
            (
                &expr[..i],
                if expr.as_bytes()[i] == b'-' {
                    -amount
                } else {
                    amount
                },
            )
        }
        None => (expr, 0),
    };
    if displacement % scale != 0 {
        return Err(AsmErrorKind::Alignment);
    }
    Ok((reg(base.trim())?, displacement / scale))
}

fn instruction(mn: &str, operands: &[&str], pc: u64, labels: &Labels) -> Parsed<Ass2Insn> {
    use Ass2Insn::*;
    let r = reg;
    let s = |v| bank(v, b'S', SPG_LANES);
    let e = |v| bank(v, b'E', FP5_REGS);
    let p = |v| bank(v, b'P', GF128_REGS);
    let csr_addr = |v: &str| {
        csr::from_name(&v.to_ascii_uppercase())
            .map(Ok)
            .unwrap_or_else(|| number(v))
    };
    let insn = match (mn, operands) {
        ("EXC", []) => Exc,
        ("ERET", []) => Eret,
        ("HALT", []) => Halt,
        ("NOP", []) => Nop,
        ("ZEROIZE", []) => Zeroize,
        ("SZERO", []) => Szero,
        ("CSRR", [d, c]) => Csrr {
            rd: r(d)?,
            csr: csr_addr(c)?,
        },
        ("CSRW", [a, c]) => Csrw {
            ra: r(a)?,
            csr: csr_addr(c)?,
        },
        ("LUT4", [d, a, b, m]) => Lut4 {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
            m: number(m)?,
        },
        ("MOV" | "NOT", [d, a]) => Lut4 {
            rd: r(d)?,
            ra: r(a)?,
            rb: 0,
            m: if mn == "MOV" { 12 } else { 3 },
        },
        ("AND" | "OR" | "XOR" | "XNOR", [d, a, b]) => Lut4 {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
            m: match mn {
                "AND" => 8,
                "OR" => 14,
                "XOR" => 6,
                _ => 9,
            },
        },
        (_, [d, a, b]) if let Some(op) = AluOp::from_mnemonic(mn) => Alu {
            op,
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
        },
        (_, [d, a, i]) if let Some(op) = AluiOp::from_mnemonic(mn) => Alui {
            op,
            rd: r(d)?,
            ra: r(a)?,
            imm16: if op == AluiOp::Addi {
                bits(integer(i)?, 16)? as u16
            } else {
                number(i)?
            },
        },
        (_, [d, i]) if let Some(mode) = Imm20Mode::from_mnemonic(mn) => {
            let imm20 = match mode {
                Imm20Mode::Movz20 => number(i)?,
                Imm20Mode::Movs20 => bits(integer(i)?, 20)? as u32,
                Imm20Mode::Auipc => relative(i, labels, pc, 20)? as u32 & 0xF_FFFF,
            };
            Imm20 {
                mode,
                rd: r(d)?,
                imm20,
            }
        }
        ("CMP", [d, a, b, f]) => Cmp {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
            flags: number(f)?,
        },
        (_, [d, a, b]) if let Some(suffix) = mn.strip_prefix("CMP.") => {
            let flags = CMP_ALIASES
                .iter()
                .find(|(name, _)| *name == suffix)
                .ok_or_else(|| AsmErrorKind::UnknownMnemonic(mn.into()))?
                .1;
            Cmp {
                rd: r(d)?,
                ra: r(a)?,
                rb: r(b)?,
                flags,
            }
        }
        ("SEL", [d, a, b, c]) => Sel {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
            rc: r(c)?,
        },
        ("BEXTU" | "BEXTS", [d, a, i, l]) => {
            let (rd, ra, idx, len) = (r(d)?, r(a)?, number(i)?, number(l)?);
            if mn == "BEXTU" {
                Bextu { rd, ra, idx, len }
            } else {
                Bexts { rd, ra, idx, len }
            }
        }
        ("BSWAP64", [d, a]) => Bswap64 {
            rd: r(d)?,
            ra: r(a)?,
        },
        (_, [d, addr]) if let Some(mode) = LoadMode::from_mnemonic(mn) => {
            let (ra, disp) = memory(addr, if mode == LoadMode::Ld64 { 8 } else { 1 })?;
            Load {
                mode,
                rd: r(d)?,
                ra,
                simm16: disp.try_into().map_err(|_| AsmErrorKind::Range)?,
            }
        }
        (_, [addr, v]) if let Some(mode) = StoreMode::from_mnemonic(mn) => {
            let (ra, disp) = memory(addr, if mode == StoreMode::St64 { 8 } else { 1 })?;
            Store {
                mode,
                rs: r(v)?,
                ra,
                simm16: disp.try_into().map_err(|_| AsmErrorKind::Range)?,
            }
        }
        (_, [c, t]) if let Some(op) = BrOp::from_mnemonic(mn) => Br {
            op,
            cond: r(c)?,
            off20: relative(t, labels, pc.wrapping_add(4), 20)?,
        },
        ("BR", [c, op, t]) => Br {
            op: BrOp::from_code(number(op)?).ok_or_else(|| invalid(op))?,
            cond: r(c)?,
            off20: relative(t, labels, pc.wrapping_add(4), 20)?,
        },
        ("JAL", [d, t]) => Jal {
            rd: r(d)?,
            off24: relative(t, labels, pc.wrapping_add(4), 24)?,
        },
        ("JALR", [d, a, i]) => Jalr {
            rd: r(d)?,
            ra: r(a)?,
            simm16: number(i)?,
        },
        ("SGET", [d, l]) => Sget {
            rd: r(d)?,
            sidx: s(l)?,
        },
        ("SPUT", [l, a]) => Sput {
            sidx: s(l)?,
            ra: r(a)?,
        },
        ("SXOR", [l, a]) => Sxor {
            sidx: s(l)?,
            ra: r(a)?,
        },
        ("SLD64", [l, addr]) | ("SST64", [addr, l]) => {
            let (ra, disp) = memory(addr, 8)?;
            let off8 = disp.try_into().map_err(|_| AsmErrorKind::Range)?;
            let sidx = s(l)?;
            if mn == "SLD64" {
                Sld64 { sidx, ra, off8 }
            } else {
                Sst64 { sidx, ra, off8 }
            }
        }
        ("GL.MAC", [d, a, b, c]) => GlMac {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
            rc: r(c)?,
        },
        ("GL.ADD", [d, a, b]) => GlAdd {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
        },
        ("GL.SUB", [d, a, b]) => GlSub {
            rd: r(d)?,
            ra: r(a)?,
            rb: r(b)?,
        },
        ("GL.SBOX7", [d, a]) => GlSbox7 {
            rd: r(d)?,
            ra: r(a)?,
        },
        ("FP5.MUL", [d, a, b]) => Fp5Mul {
            ed: e(d)?,
            ea: e(a)?,
            eb: e(b)?,
        },
        ("FP5.ADD", [d, a, b]) => Fp5Add {
            ed: e(d)?,
            ea: e(a)?,
            eb: e(b)?,
        },
        ("FP5.SUB", [d, a, b]) => Fp5Sub {
            ed: e(d)?,
            ea: e(a)?,
            eb: e(b)?,
        },
        ("GF128.MUL", [d, a, b]) => Gf128Mul {
            pd: p(d)?,
            pa: p(a)?,
            pb: p(b)?,
        },
        ("GF128.XOR", [d, a, b]) => Gf128Xor {
            pd: p(d)?,
            pa: p(a)?,
            pb: p(b)?,
        },
        ("KECCAK.F1600", [i]) => KeccakF1600 { rounds: number(i)? },
        ("POSEIDON2.GL12", []) => Poseidon2Gl12,
        ("POSEIDON2.GL24", []) => Poseidon2Gl24,
        _ => {
            return Err(AsmErrorKind::Syntax(
                "unknown instruction or wrong operand count",
            ));
        }
    };
    Ok(insn)
}

// Pass one records each statement's address and size. Emission uses those same
// boundaries for relocations and padding, including padding at nonzero origins.
struct Statement<'a> {
    pc: u64,
    size: u64,
    line: usize,
    mnemonic: String,
    args: Vec<&'a str>,
}

impl Statement<'_> {
    fn size(&self) -> Parsed<u64> {
        match (self.mnemonic.as_str(), self.args.as_slice()) {
            (".ORG", [v]) => number::<u64>(v)?
                .checked_sub(self.pc)
                .ok_or(AsmErrorKind::Range),
            (".ALIGN4", []) => Ok(self.pc.wrapping_neg() & 3),
            (".ALIGN8", []) => Ok(self.pc.wrapping_neg() & 7),
            (".WORD32", [..]) | (".WORD64", [..]) | (".BYTES", [..]) if !self.args.is_empty() => {
                let width = match self.mnemonic.as_str() {
                    ".WORD32" => 4,
                    ".WORD64" => 8,
                    _ => 1,
                };
                (self.args.len() as u64)
                    .checked_mul(width)
                    .ok_or(AsmErrorKind::Range)
            }
            (m, _) if m.starts_with('.') => {
                Err(AsmErrorKind::Syntax("unknown or malformed directive"))
            }
            _ if self.pc % 4 != 0 => Err(AsmErrorKind::Alignment),
            ("LI64", [_, _]) => Ok(16),
            _ => Ok(4),
        }
    }

    fn emit(&self, labels: &Labels, out: &mut Vec<u8>) -> Parsed<()> {
        let emit_insn = |out: &mut Vec<u8>, insn: Ass2Insn| -> Parsed<()> {
            out.extend(encode_insn_le(&insn).map_err(AsmErrorKind::Encoding)?);
            Ok(())
        };
        match self.mnemonic.as_str() {
            ".ORG" | ".ALIGN4" | ".ALIGN8" => {
                let mut pc = self.pc;
                let end = pc + self.size;
                while pc < end {
                    if pc % 4 == 0 && end - pc >= 4 {
                        out.extend(NOP_WORD.to_le_bytes());
                        pc += 4;
                    } else {
                        out.push(0);
                        pc += 1;
                    }
                }
            }
            ".BYTES" | ".WORD32" | ".WORD64" => {
                for arg in &self.args {
                    match self.mnemonic.as_str() {
                        ".BYTES" => out.push(number(arg)?),
                        ".WORD32" => out.extend(
                            (bits(address_or_literal(arg, labels)?, 32)? as u32).to_le_bytes(),
                        ),
                        _ => out.extend(bits(address_or_literal(arg, labels)?, 64)?.to_le_bytes()),
                    }
                }
            }
            "LI64" => {
                let [d, i] = self.args.as_slice() else {
                    return Err(AsmErrorKind::Syntax("expected LI64 rd, value"));
                };
                let rd = reg(d)?;
                let value = bits(address_or_literal(i, labels)?, 64)?;
                emit_insn(
                    out,
                    Ass2Insn::Imm20 {
                        mode: Imm20Mode::Movz20,
                        rd,
                        imm20: (value >> 48) as u32,
                    },
                )?;
                for shift in [32, 16, 0] {
                    emit_insn(
                        out,
                        Ass2Insn::Alui {
                            op: AluiOp::Slk16,
                            rd,
                            ra: rd,
                            imm16: (value >> shift) as u16,
                        },
                    )?;
                }
            }
            m => emit_insn(out, instruction(m, &self.args, self.pc, labels)?)?,
        }
        Ok(())
    }
}

/// Assemble an image based at byte address zero.
pub fn assemble(source: &str) -> Result<Vec<u8>, AsmError> {
    Ok(assemble_at(source, 0)?.bytes)
}

/// Assemble a contiguous image beginning at `origin`. Forward `.ORG` directives
/// pad the image. The first byte in the result always corresponds to `origin`.
pub fn assemble_at(source: &str, origin: u64) -> Result<Assembly, AsmError> {
    let mut labels = Labels::new();
    let mut statements = Vec::new();
    let mut pc = origin;
    for (i, raw) in source.lines().enumerate() {
        let line = i + 1;
        let error = |kind| AsmError { line, kind };
        let end = [raw.find(';'), raw.find('#'), raw.find("//")]
            .into_iter()
            .flatten()
            .min()
            .unwrap_or(raw.len());
        let mut content = raw[..end].trim();
        while let Some((name, rest)) = content.split_once(':') {
            let name = name.trim();
            if !identifier(name) {
                return Err(error(invalid(name)));
            }
            if labels.insert(name.into(), pc).is_some() {
                return Err(error(AsmErrorKind::DuplicateLabel(name.into())));
            }
            content = rest.trim();
        }
        if content.is_empty() {
            continue;
        }
        let (mn, args) = content
            .split_once(char::is_whitespace)
            .unwrap_or((content, ""));
        let args = if args.trim().is_empty() {
            Vec::new()
        } else {
            args.split(',').map(str::trim).collect()
        };
        let mut stmt = Statement {
            pc,
            line,
            size: 0,
            mnemonic: mn.to_ascii_uppercase(),
            args,
        };
        stmt.size = stmt.size().map_err(error)?;
        pc = pc
            .checked_add(stmt.size)
            .ok_or_else(|| error(AsmErrorKind::Range))?;
        statements.push(stmt);
    }
    let mut bytes = Vec::new();
    let size_error = || AsmError {
        line: statements.last().map_or(1, |s| s.line),
        kind: AsmErrorKind::Range,
    };
    let capacity = usize::try_from(pc - origin).map_err(|_| size_error())?;
    bytes
        .try_reserve_exact(capacity)
        .map_err(|_| size_error())?;
    for stmt in statements {
        stmt.emit(&labels, &mut bytes).map_err(|kind| AsmError {
            line: stmt.line,
            kind,
        })?;
    }
    Ok(Assembly {
        origin,
        bytes,
        labels,
    })
}
