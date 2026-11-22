//! Architectural reference machine. A step attempts one fetch and records its
//! public observation, including accesses that fault. Cycle counts model the ISA.
//!
//! Counter rules, shared with the RTL core: a retired instruction adds one to `INSTRET` and
//! its [`cycle_cost`] to `CYCLES`, except that `CSRW INSTRET` and `CSRW CYCLES` leave the
//! written counter at exactly the written value. A trap of any cause adds one cycle and no
//! retirement. `EXC` with `EXC_EN == 0` retires as a `NOP`.
//!
//! The DIT auditor tags every register, lane, memory byte and writable CSR as [`Taint::Public`]
//! or [`Taint::Secret`] and reports each use of a secret where it would reach the public
//! observation: the program counter, a memory address, the fetched word or a counter. A run
//! with no [`DitViolation`] has a [`Trace`] that is the same for every value of its secrets.
//! Values the program releases on purpose (registers at `HALT`, `DBG_OUT` bytes, stored
//! results) are outside the audit.
use crate::isa::*;
use alloc::{vec, vec::Vec};
use core::{
    fmt,
    ops::{BitOr, Range},
};
use qsag_accel::{
    gf2_128::gf2_128_mul_const,
    goldilocks::{gl_add, gl_mul, gl_sub},
    keccak::KECCAK_RC,
    poseidon2::{poseidon2_gl24_perm, poseidon2_perm12, poseidon2_sbox7},
};
use qsag_core::sponge::keccak::KECCAK_ROTATION_OFFSETS;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Taint {
    #[default]
    Public,
    Secret,
}
impl BitOr for Taint {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        if self == Self::Secret || rhs == Self::Secret {
            Self::Secret
        } else {
            Self::Public
        }
    }
}
fn combined(tags: &[Taint]) -> Taint {
    tags.iter().copied().fold(Taint::Public, BitOr::bitor)
}

/// Trap mode stops the host interpreter before the violating instruction
/// executes. There is no guest ECAUSE code for an auditor stop.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum DitMode {
    #[default]
    Audit,
    Trap,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DitViolationKind {
    /// `BR` on a secret condition register.
    SecretBranchCond,
    /// `JALR` through a secret base register, or `ERET` to a secret `EPC`.
    SecretJumpTarget,
    /// `LD64`, `LDBU`, `ST64`, `STB`, `SLD64` or `SST64` through a secret base register.
    SecretMemAddr,
    /// `CSRW` of a secret into a CSR that steers control flow or the public counters:
    /// `EVEC`, `POWER`, `INSTRET`, `CYCLES`, `EXC_EN` or `ZEROIZE`.
    SecretControlCsr,
    /// The instruction word was fetched from secret memory.
    SecretInsnFetch,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DitViolation {
    pub pc: u64,
    pub kind: DitViolationKind,
    /// The secret register. `0` when the secret is not a register (`EPC`, fetched bytes):
    /// `R0` itself is never secret.
    pub reg: u8,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum VmTrap {
    IllegalInsn = 1,
    EnvCall = 2,
    MisalignedPc = 3,
    MisalignedMem = 4,
    MemFault = 5,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemAccess {
    pub addr: u64,
    pub size: u8,
    pub write: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Observation {
    pub pc: u64,
    /// Absent on a fetch fault.
    pub insn_word: Option<u32>,
    pub mem_access: Option<MemAccess>,
    pub cycles_after: u64,
    pub instret_after: u64,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trace {
    pub observations: Vec<Observation>,
}

/// A trapped instruction may have transferred control to the guest handler.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepOutcome {
    Retired,
    Halted,
    Trap(VmTrap),
    DitViolation(DitViolation),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunExit {
    Halted,
    StepLimit,
    Trap(VmTrap),
    DitViolation(DitViolation),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemRangeError {
    pub addr: u64,
    pub len: usize,
}
impl fmt::Display for MemRangeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "memory range at {:#x} of length {} is out of bounds",
            self.addr, self.len
        )
    }
}
impl core::error::Error for MemRangeError {}

/// Writable architectural CSRs, all zero at reset. Fixed CSRs are decoded on read.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Csrs {
    pub evec: u64,
    pub instret: u64,
    pub cycles: u64,
    pub epc: u64,
    pub ecause: u64,
    pub exc_en: bool,
}

#[derive(Clone, Debug)]
pub struct Ass2Vm {
    pub pc: u64,
    pub regs: [u64; 16],
    pub spg: [u64; 25],
    pub mem: Vec<u8>,
    pub csrs: Csrs,
    pub halted: bool,
    pub debug_out: Vec<u8>,
    #[cfg(feature = "vm-debug-rx")]
    pub debug_in: Vec<u8>,
    #[cfg(feature = "vm-debug-rx")]
    debug_in_pos: usize,
    pub reg_taint: [Taint; 16],
    pub spg_taint: [Taint; 25],
    pub mem_taint: Vec<Taint>,
    pub dit_mode: DitMode,
    pub violations: Vec<DitViolation>,
    pub trace: Trace,
    csr_taint: [Taint; 256],
}

impl Ass2Vm {
    pub fn new(memory_size: usize) -> Self {
        Self {
            pc: 0,
            regs: [0; 16],
            spg: [0; 25],
            mem: vec![0; memory_size],
            csrs: Csrs::default(),
            halted: false,
            debug_out: Vec::new(),
            #[cfg(feature = "vm-debug-rx")]
            debug_in: Vec::new(),
            #[cfg(feature = "vm-debug-rx")]
            debug_in_pos: 0,
            reg_taint: [Taint::Public; 16],
            spg_taint: [Taint::Public; 25],
            mem_taint: vec![Taint::Public; memory_size],
            dit_mode: DitMode::Audit,
            violations: Vec::new(),
            trace: Trace::default(),
            csr_taint: [Taint::Public; 256],
        }
    }
    fn range(&self, addr: u64, len: usize) -> Result<Range<usize>, MemRangeError> {
        let err = MemRangeError { addr, len };
        let start = usize::try_from(addr).map_err(|_| err)?;
        let end = start
            .checked_add(len)
            .filter(|&end| end <= self.mem.len())
            .ok_or(err)?;
        Ok(start..end)
    }
    /// Install public code or data. All bytes are range-checked before writing.
    pub fn load_image(&mut self, addr: u64, image: &[u8]) -> Result<(), MemRangeError> {
        self.load_tainted(addr, image, Taint::Public)
    }
    /// Install bytes with the given tag. All bytes are range-checked before writing.
    pub fn load_tainted(
        &mut self,
        addr: u64,
        data: &[u8],
        tag: Taint,
    ) -> Result<(), MemRangeError> {
        let range = self.range(addr, data.len())?;
        self.mem_taint.resize(self.mem.len(), Taint::Public);
        self.mem[range.clone()].copy_from_slice(data);
        self.mem_taint[range].fill(tag);
        Ok(())
    }
    /// Read `len` bytes at `addr`.
    pub fn read_bytes(&self, addr: u64, len: usize) -> Result<&[u8], MemRangeError> {
        Ok(&self.mem[self.range(addr, len)?])
    }
    /// Read the little-endian 64-bit word at `addr`.
    pub fn read_word(&self, addr: u64) -> Result<u64, MemRangeError> {
        let bytes = self.read_bytes(addr, 8)?;
        Ok(u64::from_le_bytes(bytes.try_into().expect("eight bytes")))
    }
    fn set_reg(&mut self, rd: u8, value: u64, tag: Taint) {
        if rd != 0 {
            self.regs[rd as usize] = value;
            self.reg_taint[rd as usize] = tag;
        }
    }
    fn zeroize(&mut self) {
        self.regs.fill(0);
        self.reg_taint.fill(Taint::Public);
        self.spg.fill(0);
        self.spg_taint.fill(Taint::Public);
    }
    /// Enqueue a byte on the non-blocking debug RX channel (`CSR 0x0B DBG_IN`).
    #[cfg(feature = "vm-debug-rx")]
    pub fn push_debug_in(&mut self, byte: u8) {
        self.debug_in.push(byte);
    }
    fn csr_read(&mut self, addr: u8) -> Result<u64, VmTrap> {
        Ok(match addr {
            csr::ARCH_ID => csr::ARCH_ID_VALUE,
            csr::WORD_BITS => 64,
            csr::FEATURES => csr::FEATURES_VALUE,
            csr::DIT => 1,
            csr::EVEC => self.csrs.evec,
            csr::EPC => self.csrs.epc,
            csr::ECAUSE => self.csrs.ecause,
            csr::EXC_EN => self.csrs.exc_en as u64,
            csr::CYCLES => self.csrs.cycles,
            csr::INSTRET => self.csrs.instret,
            #[cfg(feature = "vm-debug-rx")]
            csr::DBG_IN => {
                if let Some(&b) = self.debug_in.get(self.debug_in_pos) {
                    self.debug_in_pos += 1;
                    (1u64 << 8) | u64::from(b)
                } else {
                    0
                }
            }
            _ => return Err(VmTrap::IllegalInsn),
        })
    }
    fn csr_write(&mut self, addr: u8, v: u64, tag: Taint) -> Result<(), VmTrap> {
        match addr {
            csr::EVEC => self.csrs.evec = v & !3,
            csr::EPC => self.csrs.epc = v,
            csr::ECAUSE => self.csrs.ecause = v,
            csr::EXC_EN => self.csrs.exc_en = v & 1 != 0,
            csr::CYCLES => self.csrs.cycles = v,
            csr::INSTRET => self.csrs.instret = v,
            csr::POWER => self.halted = v & 1 != 0,
            csr::DBG_OUT => self.debug_out.push(v as u8),
            csr::ZEROIZE => {
                if v & 1 != 0 {
                    self.zeroize();
                }
            }
            _ => return Err(VmTrap::IllegalInsn),
        }
        self.csr_taint[addr as usize] = tag;
        Ok(())
    }

    fn trap(&mut self, cause: VmTrap) -> StepOutcome {
        self.csrs.cycles = self.csrs.cycles.wrapping_add(1);
        self.csrs.ecause = cause as u64;
        self.csr_taint[csr::ECAUSE as usize] = Taint::Public;
        if self.csrs.exc_en {
            self.csrs.epc = if cause == VmTrap::EnvCall {
                self.pc.wrapping_add(4)
            } else {
                self.pc
            };
            self.csrs.exc_en = false;
            self.csr_taint[csr::EPC as usize] = Taint::Public;
            self.csr_taint[csr::EXC_EN as usize] = Taint::Public;
            self.pc = self.csrs.evec & !3;
        } else {
            self.halted = true;
        }
        StepOutcome::Trap(cause)
    }
    fn audit(&mut self, insn: Ass2Insn) -> Option<DitViolation> {
        use Ass2Insn::*;
        let (reg, kind) = match insn {
            Br { cond, .. } => (cond, DitViolationKind::SecretBranchCond),
            Jalr { ra, .. } => (ra, DitViolationKind::SecretJumpTarget),
            Load { ra, .. } | Store { ra, .. } | Sld64 { ra, .. } | Sst64 { ra, .. } => {
                (ra, DitViolationKind::SecretMemAddr)
            }
            Csrw {
                ra,
                csr:
                    csr::EVEC | csr::POWER | csr::INSTRET | csr::CYCLES | csr::EXC_EN | csr::ZEROIZE,
            } => (ra, DitViolationKind::SecretControlCsr),
            // EPC may carry data between CSRW and CSRR. It is a jump target only here.
            Eret if self.csr_taint[csr::EPC as usize] == Taint::Secret => {
                return self.violation(0, DitViolationKind::SecretJumpTarget);
            }
            _ => return None,
        };
        if self.reg_taint[reg as usize] == Taint::Public {
            return None;
        }
        self.violation(reg, kind)
    }
    /// Record a violation at the current PC. `Some` asks the caller to stop before executing.
    fn violation(&mut self, reg: u8, kind: DitViolationKind) -> Option<DitViolation> {
        let violation = DitViolation {
            pc: self.pc,
            kind,
            reg,
        };
        self.violations.push(violation);
        (self.dit_mode == DitMode::Trap).then_some(violation)
    }

    pub fn step(&mut self) -> StepOutcome {
        // The public machine state can be seeded by a debugger between steps.
        self.regs[0] = 0;
        self.reg_taint[0] = Taint::Public;
        if self.halted {
            return StepOutcome::Halted;
        }
        self.mem_taint.resize(self.mem.len(), Taint::Public);
        let pc = self.pc;
        let mut word = None;
        let mut access = None;
        let attempt = (|| {
            if pc & 3 != 0 {
                return Err(VmTrap::MisalignedPc);
            }
            let range = self.range(pc, 4).map_err(|_| VmTrap::MemFault)?;
            let raw = u32::from_le_bytes(self.mem[range.clone()].try_into().unwrap());
            word = Some(raw);
            if combined(&self.mem_taint[range]) == Taint::Secret
                && let Some(v) = self.violation(0, DitViolationKind::SecretInsnFetch)
            {
                return Ok(StepOutcome::DitViolation(v));
            }
            let insn = decode_insn(raw).ok_or(VmTrap::IllegalInsn)?;
            if let Some(v) = self.audit(insn) {
                return Ok(StepOutcome::DitViolation(v));
            }
            self.execute(insn, &mut access)?;
            if !matches!(
                insn,
                Ass2Insn::Csrw {
                    csr: csr::INSTRET,
                    ..
                }
            ) {
                self.csrs.instret = self.csrs.instret.wrapping_add(1);
            }
            if !matches!(
                insn,
                Ass2Insn::Csrw {
                    csr: csr::CYCLES,
                    ..
                }
            ) {
                self.csrs.cycles = self.csrs.cycles.wrapping_add(cycle_cost(&insn));
            }
            Ok(if self.halted {
                StepOutcome::Halted
            } else {
                StepOutcome::Retired
            })
        })();
        let outcome = attempt.unwrap_or_else(|trap| self.trap(trap));
        self.trace.observations.push(Observation {
            pc,
            insn_word: word,
            mem_access: access,
            cycles_after: self.csrs.cycles,
            instret_after: self.csrs.instret,
        });
        outcome
    }

    /// Run through handled guest traps. The budget counts attempted steps,
    /// so repeated faults and guest writes to the counters cannot evade it.
    pub fn run(&mut self, max_steps: u64) -> RunExit {
        if self.halted {
            return RunExit::Halted;
        }
        for _ in 0..max_steps {
            match self.step() {
                StepOutcome::Halted => return RunExit::Halted,
                StepOutcome::Trap(cause) if self.halted => return RunExit::Trap(cause),
                StepOutcome::DitViolation(v) => return RunExit::DitViolation(v),
                _ => {}
            }
        }
        RunExit::StepLimit
    }

    fn execute(&mut self, insn: Ass2Insn, access: &mut Option<MemAccess>) -> Result<(), VmTrap> {
        use Ass2Insn::*;
        let r = |i: u8| self.regs[i as usize];
        let t = |i: u8| self.reg_taint[i as usize];
        let mut next = self.pc.wrapping_add(4);
        match insn {
            Exc if self.csrs.exc_en => return Err(VmTrap::EnvCall),
            Exc | Nop => {}
            Eret => {
                next = self.csrs.epc & !3;
                self.csrs.exc_en = true;
                self.csr_taint[csr::EXC_EN as usize] = Taint::Public;
            }
            Halt => self.halted = true,
            Zeroize => self.zeroize(),
            Csrr { rd, csr } => {
                let v = self.csr_read(csr)?;
                self.set_reg(rd, v, self.csr_taint[csr as usize]);
            }
            Csrw { ra, csr } => self.csr_write(csr, r(ra), t(ra))?,
            Lut4 { rd, ra, rb, m } => {
                let (a, b) = (r(ra), r(rb));
                let mut value = 0;
                for (bit, term) in [!a & !b, !a & b, a & !b, a & b].into_iter().enumerate() {
                    if m & (1 << bit) != 0 {
                        value |= term;
                    }
                }
                let mut tag = Taint::Public;
                if (m ^ (m >> 2)) & 3 != 0 {
                    tag = tag | t(ra);
                }
                if (m ^ (m >> 1)) & 5 != 0 {
                    tag = tag | t(rb);
                }
                self.set_reg(rd, value, tag);
            }
            Alu { op, rd, ra, rb } => {
                let (a, b) = (r(ra), r(rb));
                let v = match op {
                    AluOp::Add => a.wrapping_add(b),
                    AluOp::Sub => a.wrapping_sub(b),
                    AluOp::Shl => {
                        if b < 64 {
                            a << b
                        } else {
                            0
                        }
                    }
                    AluOp::Shr => {
                        if b < 64 {
                            a >> b
                        } else {
                            0
                        }
                    }
                    AluOp::Asr => ((a as i64) >> b.min(63)) as u64,
                    AluOp::Rol => a.rotate_left(b as u32),
                    AluOp::Ror => a.rotate_right(b as u32),
                    AluOp::Mul64 => a.wrapping_mul(b),
                    AluOp::Mulhu64 => ((a as u128 * b as u128) >> 64) as u64,
                };
                self.set_reg(rd, v, t(ra) | t(rb));
            }
            Alui { op, rd, ra, imm16 } => {
                let a = r(ra);
                let i = u64::from(imm16);
                let v = match op {
                    AluiOp::Addi => a.wrapping_add_signed(i64::from(imm16 as i16)),
                    AluiOp::Addiu => a.wrapping_add(i),
                    AluiOp::Xori => a ^ i,
                    AluiOp::Andi => a & i,
                    AluiOp::Ori => a | i,
                    AluiOp::Shli => a << i,
                    AluiOp::Shri => a >> i,
                    AluiOp::Asri => ((a as i64) >> i) as u64,
                    AluiOp::Roli => a.rotate_left(i as u32),
                    AluiOp::Slk16 => (a << 16) | i,
                };
                self.set_reg(rd, v, t(ra));
            }
            Imm20 { mode, rd, imm20 } => {
                let signed = i64::from(((imm20 << 12) as i32) >> 12);
                self.set_reg(
                    rd,
                    match mode {
                        Imm20Mode::Movz20 => u64::from(imm20),
                        Imm20Mode::Movs20 => signed as u64,
                        Imm20Mode::Auipc => self.pc.wrapping_add_signed(signed * 4),
                    },
                    Taint::Public,
                );
            }
            Cmp { rd, ra, rb, flags } => {
                let (a, b) = (r(ra), r(rb));
                let gt = if flags & 4 != 0 {
                    (a as i64) > (b as i64)
                } else {
                    a > b
                };
                let result = (flags & 1 != 0 && a == b || flags & 2 != 0 && gt) ^ (flags & 8 != 0);
                self.set_reg(rd, result as u64, t(ra) | t(rb));
            }
            Sel { rd, ra, rb, rc } => {
                let mask = 0u64.wrapping_sub((r(rc) != 0) as u64);
                self.set_reg(rd, (r(ra) & !mask) | (r(rb) & mask), t(ra) | t(rb) | t(rc));
            }
            Bextu { rd, ra, idx, len } | Bexts { rd, ra, idx, len } => {
                let shift = 64 - 8 * len;
                let aligned = (r(ra) >> (8 * idx)) << shift;
                let v = if matches!(insn, Bexts { .. }) {
                    ((aligned as i64) >> shift) as u64
                } else {
                    aligned >> shift
                };
                self.set_reg(rd, v, t(ra));
            }
            Bswap64 { rd, ra } => self.set_reg(rd, r(ra).swap_bytes(), t(ra)),
            Load {
                mode,
                rd,
                ra,
                simm16,
            } => {
                let size = if mode == LoadMode::Ld64 { 8 } else { 1 };
                self.transfer(ra, i64::from(simm16), size, Slot::Reg(rd), false, access)?;
            }
            Store {
                mode,
                rs,
                ra,
                simm16,
            } => {
                let size = if mode == StoreMode::St64 { 8 } else { 1 };
                self.transfer(ra, i64::from(simm16), size, Slot::Reg(rs), true, access)?;
            }
            Sld64 { sidx, ra, off8 } | Sst64 { sidx, ra, off8 } => {
                self.transfer(
                    ra,
                    i64::from(off8),
                    8,
                    Slot::Lane(sidx),
                    matches!(insn, Sst64 { .. }),
                    access,
                )?;
            }
            Br { op, cond, off20 } => {
                let v = r(cond);
                let take = match op {
                    BrOp::Beqz => v == 0,
                    BrOp::Bnez => v != 0,
                    BrOp::Bltz => (v as i64) < 0,
                    BrOp::Bgez => (v as i64) >= 0,
                };
                if take {
                    next = next.wrapping_add_signed(i64::from(off20) * 4);
                }
            }
            Jal { rd, off24 } => {
                self.set_reg(rd, next, Taint::Public);
                next = next.wrapping_add_signed(i64::from(off24) * 4);
            }
            Jalr { rd, ra, simm16 } => {
                let target = r(ra).wrapping_add_signed(i64::from(simm16) * 4);
                if target & 3 != 0 {
                    return Err(VmTrap::MisalignedPc);
                }
                self.set_reg(rd, next, Taint::Public);
                next = target;
            }
            Sget { rd, sidx } => {
                self.set_reg(rd, self.spg[sidx as usize], self.spg_taint[sidx as usize])
            }
            Sput { sidx, ra } => {
                self.spg[sidx as usize] = r(ra);
                self.spg_taint[sidx as usize] = t(ra);
            }
            Sxor { sidx, ra } => {
                self.spg[sidx as usize] ^= r(ra);
                self.spg_taint[sidx as usize] = self.spg_taint[sidx as usize] | t(ra);
            }
            Szero => {
                self.spg.fill(0);
                self.spg_taint.fill(Taint::Public);
            }
            GlMac { rd, ra, rb, rc } => self.set_reg(
                rd,
                gl_add(gl_mul(r(ra), r(rb)), r(rc)),
                t(ra) | t(rb) | t(rc),
            ),
            GlAdd { rd, ra, rb } => self.set_reg(rd, gl_add(r(ra), r(rb)), t(ra) | t(rb)),
            GlSub { rd, ra, rb } => self.set_reg(rd, gl_sub(r(ra), r(rb)), t(ra) | t(rb)),
            GlSbox7 { rd, ra } => self.set_reg(rd, poseidon2_sbox7(r(ra)), t(ra)),
            Fp5Mul { ed, ea, eb } | Fp5Add { ed, ea, eb } | Fp5Sub { ed, ea, eb } => {
                let lanes = |e: u8| {
                    let start = 5 * usize::from(e);
                    start..start + 5
                };
                let a = &self.spg[lanes(ea)];
                let b = &self.spg[lanes(eb)];
                let ta = &self.spg_taint[lanes(ea)];
                let tb = &self.spg_taint[lanes(eb)];
                let mut product = [0; 5];
                let mut tags = [Taint::Public; 5];
                if matches!(insn, Fp5Mul { .. }) {
                    for (i, &x) in a.iter().enumerate() {
                        for (j, &y) in b.iter().enumerate() {
                            let term = gl_mul(x, y);
                            let k = (i + j) % 5;
                            product[k] =
                                gl_add(product[k], if i + j >= 5 { gl_mul(3, term) } else { term });
                        }
                    }
                    tags.fill(combined(ta) | combined(tb));
                } else {
                    for i in 0..5 {
                        product[i] = if matches!(insn, Fp5Add { .. }) {
                            gl_add(a[i], b[i])
                        } else {
                            gl_sub(a[i], b[i])
                        };
                        tags[i] = ta[i] | tb[i];
                    }
                }
                self.spg[lanes(ed)].copy_from_slice(&product);
                self.spg_taint[lanes(ed)].copy_from_slice(&tags);
            }
            Gf128Mul { pd, pa, pb } | Gf128Xor { pd, pa, pb } => {
                let pair = |p: u8| {
                    let i = 2 * usize::from(p);
                    (
                        u128::from(self.spg[i]) | (u128::from(self.spg[i + 1]) << 64),
                        self.spg_taint[i],
                        self.spg_taint[i + 1],
                    )
                };
                let (a, al, ah) = pair(pa);
                let (b, bl, bh) = pair(pb);
                let (v, lo, hi) = if matches!(insn, Gf128Mul { .. }) {
                    let tag = al | ah | bl | bh;
                    (gf2_128_mul_const(a, b), tag, tag)
                } else {
                    (a ^ b, al | bl, ah | bh)
                };
                let d = 2 * usize::from(pd);
                self.spg[d..d + 2].copy_from_slice(&[v as u64, (v >> 64) as u64]);
                self.spg_taint[d..d + 2].copy_from_slice(&[lo, hi]);
            }
            KeccakF1600 { rounds } => {
                keccak(&mut self.spg, rounds);
                let tag = combined(&self.spg_taint);
                self.spg_taint.fill(tag);
            }
            Poseidon2Gl12 | Poseidon2Gl24 => {
                let width = if matches!(insn, Poseidon2Gl12) {
                    poseidon2_perm12(self.spg.first_chunk_mut::<12>().unwrap());
                    12
                } else {
                    poseidon2_gl24_perm(self.spg.first_chunk_mut::<24>().unwrap());
                    24
                };
                let tags = &mut self.spg_taint[..width];
                tags.fill(combined(tags));
            }
        }
        self.pc = next;
        Ok(())
    }

    fn transfer(
        &mut self,
        ra: u8,
        offset: i64,
        size: u8,
        slot: Slot,
        write: bool,
        access: &mut Option<MemAccess>,
    ) -> Result<(), VmTrap> {
        let addr = self.regs[ra as usize].wrapping_add_signed(offset * i64::from(size));
        *access = Some(MemAccess { addr, size, write });
        if addr % u64::from(size) != 0 {
            return Err(VmTrap::MisalignedMem);
        }
        let range = self
            .range(addr, usize::from(size))
            .map_err(|_| VmTrap::MemFault)?;
        if write {
            let (value, tag) = match slot {
                Slot::Reg(i) => (self.regs[i as usize], self.reg_taint[i as usize]),
                Slot::Lane(i) => (self.spg[i as usize], self.spg_taint[i as usize]),
            };
            self.mem[range.clone()].copy_from_slice(&value.to_le_bytes()[..usize::from(size)]);
            self.mem_taint[range].fill(tag | self.reg_taint[ra as usize]);
        } else {
            let mut bytes = [0; 8];
            bytes[..usize::from(size)].copy_from_slice(&self.mem[range.clone()]);
            let value = u64::from_le_bytes(bytes);
            let tag = combined(&self.mem_taint[range]) | self.reg_taint[ra as usize];
            match slot {
                Slot::Reg(i) => self.set_reg(i, value, tag),
                Slot::Lane(i) => {
                    self.spg[i as usize] = value;
                    self.spg_taint[i as usize] = tag;
                }
            }
        }
        Ok(())
    }
}

enum Slot {
    Reg(u8),
    Lane(u8),
}

fn keccak(state: &mut [u64; 25], rounds: u8) {
    for &rc in &KECCAK_RC[24 - usize::from(rounds)..] {
        let parity: [u64; 5] = core::array::from_fn(|x| {
            state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
        });
        let mut b = [0; 25];
        for (i, &lane) in state.iter().enumerate() {
            let (x, y) = (i % 5, i / 5);
            let d = parity[(x + 4) % 5] ^ parity[(x + 1) % 5].rotate_left(1);
            b[y + 5 * ((2 * x + 3 * y) % 5)] = (lane ^ d).rotate_left(KECCAK_ROTATION_OFFSETS[i]);
        }
        for (row, input) in state.chunks_exact_mut(5).zip(b.chunks_exact(5)) {
            for x in 0..5 {
                row[x] = input[x] ^ (!input[(x + 1) % 5] & input[(x + 2) % 5]);
            }
        }
        state[0] ^= rc;
    }
}
