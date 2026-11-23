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
use crate::wire::{
    Ass2WireError, OwnerOp, WOTSC_PROOF_BYTES, compute_code_hash, derive_applet_key,
    parse_and_verify_load_code_wotsc_frame, parse_load_code_open_frame, verify_wotsc_proof,
};
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

/// Hardware trap / fault cause alias matching the RTL `Cause` nomenclature (`Cause::MemFault = 5`).
pub type Cause = VmTrap;

/// Locked `ASS2-0P5` hardware lifecycle state governing `CMD_LOAD_CODE` (`0x30`) and Ring-3 applets.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LcState {
    /// Factory/unprovisioned state: allows open `<= 64`-insn Ring-3 applets (`flags = 0`).
    #[default]
    Blank,
    /// Owner-provisioned state:
    /// * `rom_lock == true`: rejects `CMD_LOAD_CODE` (`0x30`) unconditionally;
    /// * `rom_lock == false && allow_signed_applets`: requires owner `WOTS+C` signature over
    ///   `code_hash` (`<= 64` insns) and injects `cSHAKE256(K_root, "ASS2.APPLET" || code_hash)`
    ///   into `r1..r2` after scrubbing `r3..r15` and `spg`.
    Provisioned {
        allow_signed_applets: bool,
        rom_lock: bool,
    },
}

impl LcState {
    pub const PROVISIONED_SIGNED_APPLETS: Self = Self::Provisioned {
        allow_signed_applets: true,
        rom_lock: false,
    };
    pub const PROVISIONED_ROM_LOCKED: Self = Self::Provisioned {
        allow_signed_applets: false,
        rom_lock: true,
    };

    /// Canonical 64-bit `MMIO_LC_STATE` (`0xFFFF_0050`) register encoding.
    pub const fn to_mmio_u64(self) -> u64 {
        match self {
            Self::Blank => 0,
            Self::Provisioned {
                allow_signed_applets,
                rom_lock,
            } => 1 | ((allow_signed_applets as u64) << 1) | ((rom_lock as u64) << 2),
        }
    }
}

/// Ring-0 privileged `SYS_MMIO` (`0xFFFF_0000..=0xFFFF_007F`) backing state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnclaveMmio {
    pub k_root: [u8; 32],
    pub puf_syndrome: [u64; 2],
    pub fram_xfer: u64,
    pub fram_status: u64,
    pub trng_data: u64,
    pub trng_health: u64,
    pub verdict_ctrl: u64,
    pub gpio_io: u64,
    pub dbg_uart_div: u64,
}

impl Default for EnclaveMmio {
    fn default() -> Self {
        Self {
            k_root: [0; 32],
            puf_syndrome: [0; 2],
            fram_xfer: 0,
            fram_status: 1,
            trng_data: 0,
            trng_health: 1,
            verdict_ctrl: 0,
            gpio_io: 0,
            dbg_uart_div: 0,
        }
    }
}

/// Errors returned by the enclave `CMD_LOAD_CODE` (`0x30`) loader.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnclaveError {
    NotEnclaveMode,
    RomLocked,
    AppletsDisabled,
    SignatureRequired,
    OpenAppletNotAllowed,
    AppletWordCountOutOfRange,
    Wire(Ass2WireError),
}

impl fmt::Display for EnclaveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotEnclaveMode => f.write_str("VM is not configured in Two-Ring enclave mode"),
            Self::RomLocked => f.write_str("CMD_LOAD_CODE (0x30) rejected: rom_lock is active"),
            Self::AppletsDisabled => f.write_str("CMD_LOAD_CODE (0x30) rejected: applets disabled"),
            Self::SignatureRequired => {
                f.write_str("Provisioned enclave requires Owner WOTS+C signed applet")
            }
            Self::OpenAppletNotAllowed => {
                f.write_str("open unsigned applet rejected outside LcState::Blank")
            }
            Self::AppletWordCountOutOfRange => {
                f.write_str("Ring-3 applet word count outside 1..=64")
            }
            Self::Wire(e) => fmt::Display::fmt(e, f),
        }
    }
}

impl core::error::Error for EnclaveError {}
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
    /// Two-Ring W^X privilege bit (`false` = Ring 0 `I-ROM`, `true` = Ring 3 SRAM applet).
    pub applet_exec: bool,
    /// Hardware enclave lifecycle mode (`Blank` vs `Provisioned { allow_signed_applets, rom_lock }`).
    pub lc_state: LcState,
    /// Ring-0 privileged `SYS_MMIO` (`0xFFFF_0000`) state when `mpu_enabled` is active.
    pub mmio: EnclaveMmio,
    mpu_enabled: bool,
    irom: Vec<u8>,
    irom_taint: Vec<Taint>,
    sram: Vec<u8>,
    sram_taint: Vec<Taint>,
    csr_taint: [Taint; 256],
    unhandled_trap: Option<VmTrap>,
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
            applet_exec: false,
            lc_state: LcState::Blank,
            mmio: EnclaveMmio::default(),
            mpu_enabled: false,
            irom: Vec::new(),
            irom_taint: Vec::new(),
            sram: Vec::new(),
            sram_taint: Vec::new(),
            csr_taint: [Taint::Public; 256],
            unhandled_trap: None,
        }
    }

    /// Construct a hardware-faithful `ASS2-0P5` Two-Ring W^X enclave VM starting in Ring 0
    /// (`applet_exec = false`, `pc = 0x0000` in `4 KiB` `I-ROM`, `512 B` SRAM at `0x10000..=0x101FF`,
    /// and `128 B` Ring-0 `SYS_MMIO` at `0xFFFF_0000..=0xFFFF_007F`).
    pub fn new_enclave(k_root: [u8; 32], lc_state: LcState) -> Self {
        let mmio = EnclaveMmio {
            k_root,
            ..EnclaveMmio::default()
        };
        Self {
            pc: mem_map::IROM_BASE,
            regs: [0; 16],
            spg: [0; 25],
            mem: Vec::new(),
            csrs: Csrs::default(),
            halted: false,
            debug_out: Vec::new(),
            #[cfg(feature = "vm-debug-rx")]
            debug_in: Vec::new(),
            #[cfg(feature = "vm-debug-rx")]
            debug_in_pos: 0,
            reg_taint: [Taint::Public; 16],
            spg_taint: [Taint::Public; 25],
            mem_taint: Vec::new(),
            dit_mode: DitMode::Audit,
            violations: Vec::new(),
            trace: Trace::default(),
            applet_exec: false,
            lc_state,
            mmio,
            mpu_enabled: true,
            irom: vec![0; mem_map::IROM_BYTES],
            irom_taint: vec![Taint::Public; mem_map::IROM_BYTES],
            sram: vec![0; mem_map::SRAM_BYTES],
            sram_taint: vec![Taint::Public; mem_map::SRAM_BYTES],
            csr_taint: [Taint::Public; 256],
            unhandled_trap: None,
        }
    }

    fn install_ring3_applet_words(&mut self, words: &[u32]) {
        self.sram[..mem_map::APPLET_CODE_BYTES].fill(0);
        self.sram_taint[..mem_map::APPLET_CODE_BYTES].fill(Taint::Public);
        for (i, &w) in words.iter().enumerate() {
            let off = 4 * i;
            self.sram[off..off + 4].copy_from_slice(&w.to_le_bytes());
        }
        self.csrs.evec = 0;
        self.csrs.epc = 0;
        self.csrs.ecause = 0;
        self.csrs.exc_en = false;
        self.csr_taint[csr::EVEC as usize] = Taint::Public;
        self.csr_taint[csr::EPC as usize] = Taint::Public;
        self.csr_taint[csr::ECAUSE as usize] = Taint::Public;
        self.csr_taint[csr::EXC_EN as usize] = Taint::Public;
        self.pc = mem_map::APPLET_CODE_BASE;
        self.applet_exec = true;
        self.halted = false;
        self.unhandled_trap = None;
    }

    fn check_cmd_load_code_allowed(&self) -> Result<(), EnclaveError> {
        if !self.mpu_enabled {
            return Err(EnclaveError::NotEnclaveMode);
        }
        match self.lc_state {
            LcState::Blank => Ok(()),
            LcState::Provisioned { rom_lock: true, .. } => Err(EnclaveError::RomLocked),
            LcState::Provisioned {
                allow_signed_applets: false,
                rom_lock: false,
            } => Err(EnclaveError::AppletsDisabled),
            LcState::Provisioned {
                allow_signed_applets: true,
                rom_lock: false,
            } => Ok(()),
        }
    }

    /// Load an open (unsigned) `1..=64`-instruction Ring-3 applet into `0x10000..=0x100FF`.
    /// Permitted **strictly** in `LcState::Blank`; rejected in all `LcState::Provisioned` modes.
    pub fn load_open_applet(&mut self, words: &[u32]) -> Result<[u8; 32], EnclaveError> {
        self.check_cmd_load_code_allowed()?;
        if self.lc_state != LcState::Blank {
            return Err(EnclaveError::SignatureRequired);
        }
        if !(1..=mem_map::MAX_APPLET_WORDS).contains(&words.len()) {
            return Err(EnclaveError::AppletWordCountOutOfRange);
        }
        let code_hash = compute_code_hash(words);
        self.zeroize();
        self.install_ring3_applet_words(words);
        Ok(code_hash)
    }

    /// Verify an Owner `WOTS+C` signature over `code_hash = compute_code_hash(words)` (`1..=64` insns)
    /// in `LcState::Provisioned { allow_signed_applets: true, rom_lock: false }`, advance `(owner_pk, record)`,
    /// scrub `r3..r15` and `spg`, and inject `cSHAKE256(K_root, "ASS2.APPLET" || code_hash)` into `r1..r2`.
    pub fn load_signed_applet(
        &mut self,
        words: &[u32],
        owner_pk: &mut [u8; 32],
        enclave_id: &[u8; 32],
        nonce: &[u8; 16],
        record: &mut u64,
        proof: &[u8; WOTSC_PROOF_BYTES],
    ) -> Result<[u8; 32], EnclaveError> {
        self.check_cmd_load_code_allowed()?;
        match self.lc_state {
            LcState::Blank => return Err(EnclaveError::OpenAppletNotAllowed),
            LcState::Provisioned { rom_lock: true, .. } => return Err(EnclaveError::RomLocked),
            LcState::Provisioned {
                allow_signed_applets: false,
                ..
            } => return Err(EnclaveError::AppletsDisabled),
            LcState::Provisioned {
                allow_signed_applets: true,
                rom_lock: false,
            } => {}
        }
        if !(1..=mem_map::MAX_APPLET_WORDS).contains(&words.len()) {
            return Err(EnclaveError::AppletWordCountOutOfRange);
        }
        let code_hash = compute_code_hash(words);
        let mut cap_prefix = [0u8; 16];
        cap_prefix.copy_from_slice(&code_hash[..16]);
        let next_root = verify_wotsc_proof(
            owner_pk,
            enclave_id,
            OwnerOp::LoadCode {
                word_count: words.len() as u32,
                code_hash,
            },
            nonce,
            *record,
            &cap_prefix,
            proof,
        )
        .map_err(EnclaveError::Wire)?;
        *owner_pk = next_root;
        *record += 1u64 << 32;

        // Scrub r0, r3..r15, and all 25 sponge lanes before injecting derived applet key into r1..r2.
        self.regs[0] = 0;
        self.reg_taint[0] = Taint::Public;
        self.regs[3..16].fill(0);
        self.reg_taint[3..16].fill(Taint::Public);
        self.spg.fill(0);
        self.spg_taint.fill(Taint::Public);

        let applet_key = derive_applet_key(&self.mmio.k_root, &code_hash);
        self.regs[1] = u64::from_le_bytes(applet_key[0..8].try_into().unwrap());
        self.regs[2] = u64::from_le_bytes(applet_key[8..16].try_into().unwrap());
        self.reg_taint[1] = Taint::Secret;
        self.reg_taint[2] = Taint::Secret;

        self.install_ring3_applet_words(words);
        Ok(code_hash)
    }

    /// Process a raw `CMD_LOAD_CODE` (`0x30`) wire frame (`flags = 0` open in `LcState::Blank`,
    /// `flags = 2` `WOTS+C`-signed in `LcState::Provisioned { allow_signed_applets: true, rom_lock: false }`,
    /// and unconditionally rejected under `rom_lock`).
    pub fn execute_cmd_load_code(
        &mut self,
        frame: &[u8],
        owner_pk: &mut [u8; 32],
        enclave_id: &[u8; 32],
        nonce: &[u8; 16],
        record: &mut u64,
    ) -> Result<[u8; 32], EnclaveError> {
        self.check_cmd_load_code_allowed()?;
        if frame.len() < 9 {
            return Err(EnclaveError::Wire(Ass2WireError::LengthMismatch));
        }
        let header = u64::from_le_bytes(frame[1..9].try_into().unwrap());
        let magic = (header & 0xFF) as u8;
        let opcode = ((header >> 8) & 0xFF) as u8;
        let flags = ((header >> 16) & 0xFF) as u8;
        if magic != mem_map::WIRE_MAGIC || opcode != mem_map::CMD_LOAD_CODE {
            return Err(EnclaveError::Wire(Ass2WireError::InvalidHeader));
        }
        match self.lc_state {
            LcState::Blank => {
                if flags != 0 {
                    return Err(EnclaveError::OpenAppletNotAllowed);
                }
                let (_prefix, words) =
                    parse_load_code_open_frame(frame).map_err(EnclaveError::Wire)?;
                self.load_open_applet(&words)
            }
            LcState::Provisioned { rom_lock: true, .. } => Err(EnclaveError::RomLocked),
            LcState::Provisioned {
                allow_signed_applets: false,
                ..
            } => Err(EnclaveError::AppletsDisabled),
            LcState::Provisioned {
                allow_signed_applets: true,
                rom_lock: false,
            } => {
                if flags != 2 {
                    return Err(EnclaveError::SignatureRequired);
                }
                let (_prefix, words, code_hash, next_root) =
                    parse_and_verify_load_code_wotsc_frame(
                        frame, owner_pk, enclave_id, nonce, *record,
                    )
                    .map_err(EnclaveError::Wire)?;
                *owner_pk = next_root;
                *record += 1u64 << 32;

                self.regs[0] = 0;
                self.reg_taint[0] = Taint::Public;
                self.regs[3..16].fill(0);
                self.reg_taint[3..16].fill(Taint::Public);
                self.spg.fill(0);
                self.spg_taint.fill(Taint::Public);

                let applet_key = derive_applet_key(&self.mmio.k_root, &code_hash);
                self.regs[1] = u64::from_le_bytes(applet_key[0..8].try_into().unwrap());
                self.regs[2] = u64::from_le_bytes(applet_key[8..16].try_into().unwrap());
                self.reg_taint[1] = Taint::Secret;
                self.reg_taint[2] = Taint::Secret;

                self.install_ring3_applet_words(&words);
                Ok(code_hash)
            }
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

    fn enclave_host_slice_mut(
        &mut self,
        addr: u64,
        len: usize,
    ) -> Result<(&mut [u8], &mut [Taint]), MemRangeError> {
        let err = MemRangeError { addr, len };
        let end_addr = addr.checked_add(len as u64).ok_or(err)?;
        if end_addr <= mem_map::IROM_BASE + mem_map::IROM_BYTES as u64 {
            let s = addr as usize;
            let e = end_addr as usize;
            Ok((&mut self.irom[s..e], &mut self.irom_taint[s..e]))
        } else if addr >= mem_map::SRAM_BASE
            && end_addr <= mem_map::SRAM_BASE + mem_map::SRAM_BYTES as u64
        {
            let s = (addr - mem_map::SRAM_BASE) as usize;
            let e = (end_addr - mem_map::SRAM_BASE) as usize;
            Ok((&mut self.sram[s..e], &mut self.sram_taint[s..e]))
        } else {
            Err(err)
        }
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
        if self.mpu_enabled {
            let (buf, tags) = self.enclave_host_slice_mut(addr, data.len())?;
            buf.copy_from_slice(data);
            tags.fill(tag);
            return Ok(());
        }
        let range = self.range(addr, data.len())?;
        self.mem_taint.resize(self.mem.len(), Taint::Public);
        self.mem[range.clone()].copy_from_slice(data);
        self.mem_taint[range].fill(tag);
        Ok(())
    }
    /// Read `len` bytes at `addr`.
    pub fn read_bytes(&self, addr: u64, len: usize) -> Result<&[u8], MemRangeError> {
        if self.mpu_enabled {
            let err = MemRangeError { addr, len };
            let end_addr = addr.checked_add(len as u64).ok_or(err)?;
            if end_addr <= mem_map::IROM_BASE + mem_map::IROM_BYTES as u64 {
                return Ok(&self.irom[addr as usize..end_addr as usize]);
            }
            if addr >= mem_map::SRAM_BASE
                && end_addr <= mem_map::SRAM_BASE + mem_map::SRAM_BYTES as u64
            {
                let s = (addr - mem_map::SRAM_BASE) as usize;
                let e = (end_addr - mem_map::SRAM_BASE) as usize;
                return Ok(&self.sram[s..e]);
            }
            return Err(err);
        }
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
        if self.mpu_enabled
            && self.applet_exec
            && matches!(addr, csr::EVEC | csr::EXC_EN)
        {
            return Err(VmTrap::IllegalInsn);
        }
        match addr {
            csr::EVEC => self.csrs.evec = v & !3,
            csr::EPC => self.csrs.epc = v,
            csr::ECAUSE => self.csrs.ecause = v,
            csr::EXC_EN => self.csrs.exc_en = v & 1 != 0,
            csr::CYCLES => self.csrs.cycles = v,
            csr::INSTRET => self.csrs.instret = v,
            csr::POWER => {
                self.halted = v & 1 != 0;
                self.unhandled_trap = None;
            }
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
            self.unhandled_trap = None;
        } else {
            self.halted = true;
            self.unhandled_trap = Some(cause);
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

    fn fetch_insn(&self, pc: u64) -> Result<(u32, Taint), VmTrap> {
        if !self.mpu_enabled {
            let range = self.range(pc, 4).map_err(|_| VmTrap::MemFault)?;
            let raw = u32::from_le_bytes(self.mem[range.clone()].try_into().unwrap());
            return Ok((raw, combined(&self.mem_taint[range])));
        }
        let end = pc.checked_add(4).ok_or(VmTrap::MemFault)?;
        if !self.applet_exec {
            // Ring 0 (`applet_exec = false`): ONLY 0x0000..=0x0FFF (`I-ROM`) is executable (`R+X, !W`);
            // SRAM (`0x10000..=0x101FF`) and `SYS_MMIO` (`0xFFFF_0000`) are strictly `!X`.
            if end <= mem_map::IROM_BASE + mem_map::IROM_BYTES as u64 {
                let s = pc as usize;
                let raw = u32::from_le_bytes(self.irom[s..s + 4].try_into().unwrap());
                Ok((raw, combined(&self.irom_taint[s..s + 4])))
            } else {
                Err(VmTrap::MemFault)
            }
        } else {
            // Ring 3 (`applet_exec = true`): ONLY lower 256 B (`0x10000..=0x100FF`, 64 insns) is `R+X, !W`;
            // upper 256 B (`0x10100..=0x101FF`), `I-ROM`, and `SYS_MMIO` fault with `Cause::MemFault`.
            if pc >= mem_map::APPLET_CODE_BASE
                && end <= mem_map::APPLET_CODE_BASE + mem_map::APPLET_CODE_BYTES as u64
            {
                let s = (pc - mem_map::SRAM_BASE) as usize;
                let raw = u32::from_le_bytes(self.sram[s..s + 4].try_into().unwrap());
                Ok((raw, combined(&self.sram_taint[s..s + 4])))
            } else {
                Err(VmTrap::MemFault)
            }
        }
    }

    pub fn step(&mut self) -> StepOutcome {
        // The public machine state can be seeded by a debugger between steps.
        self.regs[0] = 0;
        self.reg_taint[0] = Taint::Public;
        if self.halted {
            if let Some(cause) = self.unhandled_trap {
                return StepOutcome::Trap(cause);
            }
            return StepOutcome::Halted;
        }
        self.unhandled_trap = None;
        if !self.mpu_enabled {
            self.mem_taint.resize(self.mem.len(), Taint::Public);
        }
        let pc = self.pc;
        let mut word = None;
        let mut access = None;
        let attempt = (|| {
            if pc & 3 != 0 {
                return Err(VmTrap::MisalignedPc);
            }
            let (raw, fetch_taint) = self.fetch_insn(pc)?;
            word = Some(raw);
            if fetch_taint == Taint::Secret
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
            if let Some(cause) = self.unhandled_trap {
                return RunExit::Trap(cause);
            }
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
            Halt => {
                self.halted = true;
                self.unhandled_trap = None;
            }
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

    fn mmio_image(&self) -> ([u8; mem_map::SYS_MMIO_BYTES], [Taint; mem_map::SYS_MMIO_BYTES]) {
        let mut buf = [0u8; mem_map::SYS_MMIO_BYTES];
        let mut tags = [Taint::Public; mem_map::SYS_MMIO_BYTES];
        let put_u64 =
            |buf: &mut [u8; mem_map::SYS_MMIO_BYTES],
             tags: &mut [Taint; mem_map::SYS_MMIO_BYTES],
             off: u64,
             val: u64,
             taint: Taint| {
                let s = off as usize;
                buf[s..s + 8].copy_from_slice(&val.to_le_bytes());
                tags[s..s + 8].fill(taint);
            };
        put_u64(&mut buf, &mut tags, mem_map::MMIO_FRAM_XFER, self.mmio.fram_xfer, Taint::Public);
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_FRAM_STATUS,
            self.mmio.fram_status,
            Taint::Public,
        );
        let vk = mem_map::MMIO_VAULT_KEY as usize;
        buf[vk..vk + 32].copy_from_slice(&self.mmio.k_root);
        tags[vk..vk + 32].fill(Taint::Secret);
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_PUF_SYNDROME,
            self.mmio.puf_syndrome[0],
            Taint::Secret,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_PUF_SYNDROME + 8,
            self.mmio.puf_syndrome[1],
            Taint::Secret,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_TRNG_DATA,
            self.mmio.trng_data,
            Taint::Secret,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_TRNG_HEALTH,
            self.mmio.trng_health,
            Taint::Public,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_LC_STATE,
            self.lc_state.to_mmio_u64(),
            Taint::Public,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_VERDICT_CTRL,
            self.mmio.verdict_ctrl,
            Taint::Public,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_GPIO_IO,
            self.mmio.gpio_io,
            Taint::Public,
        );
        put_u64(
            &mut buf,
            &mut tags,
            mem_map::MMIO_DBG_UART_DIV,
            self.mmio.dbg_uart_div,
            Taint::Public,
        );
        (buf, tags)
    }

    fn mmio_write(&mut self, off: u64, size: u8, value: u64) -> Result<(), VmTrap> {
        let aligned = off & !7;
        let reg = match aligned {
            mem_map::MMIO_FRAM_XFER => &mut self.mmio.fram_xfer,
            mem_map::MMIO_FRAM_STATUS => &mut self.mmio.fram_status,
            mem_map::MMIO_VERDICT_CTRL => &mut self.mmio.verdict_ctrl,
            mem_map::MMIO_GPIO_IO => &mut self.mmio.gpio_io,
            mem_map::MMIO_DBG_UART_DIV => &mut self.mmio.dbg_uart_div,
            // Read-only hardware roots/fuses (`VAULT_KEY`, `PUF_SYNDROME`, `TRNG`, `LC_STATE`) fault on write.
            _ => return Err(VmTrap::MemFault),
        };
        if size == 8 {
            *reg = value;
        } else {
            let mut bytes = reg.to_le_bytes();
            bytes[(off & 7) as usize] = value as u8;
            *reg = u64::from_le_bytes(bytes);
        }
        Ok(())
    }

    fn transfer_mpu(
        &mut self,
        ra: u8,
        addr: u64,
        size: u8,
        slot: Slot,
        write: bool,
    ) -> Result<(), VmTrap> {
        let len = usize::from(size);
        let end = addr.checked_add(u64::from(size)).ok_or(VmTrap::MemFault)?;
        let addr_taint = self.reg_taint[ra as usize];

        if self.applet_exec {
            // Ring 3 (`applet_exec = true`):
            // * 0x10000..=0x100FF: R+X, !W
            // * 0x10100..=0x101FF: R+W, !X
            // * 0xFFFF_0000 MMIO, 0x0000..=0x0FFF I-ROM, and all other ranges: Cause::MemFault!
            let in_code = addr >= mem_map::APPLET_CODE_BASE
                && end <= mem_map::APPLET_CODE_BASE + mem_map::APPLET_CODE_BYTES as u64;
            let in_data = addr >= mem_map::APPLET_DATA_BASE
                && end <= mem_map::APPLET_DATA_BASE + mem_map::APPLET_DATA_BYTES as u64;
            if write {
                if !in_data {
                    return Err(VmTrap::MemFault);
                }
            } else if !(in_code || in_data) {
                return Err(VmTrap::MemFault);
            }
            if addr % u64::from(size) != 0 {
                return Err(VmTrap::MisalignedMem);
            }
            let s = (addr - mem_map::SRAM_BASE) as usize;
            if write {
                let (value, tag) = match slot {
                    Slot::Reg(i) => (self.regs[i as usize], self.reg_taint[i as usize]),
                    Slot::Lane(i) => (self.spg[i as usize], self.spg_taint[i as usize]),
                };
                self.sram[s..s + len].copy_from_slice(&value.to_le_bytes()[..len]);
                self.sram_taint[s..s + len].fill(tag | addr_taint);
            } else {
                let mut bytes = [0u8; 8];
                bytes[..len].copy_from_slice(&self.sram[s..s + len]);
                let value = u64::from_le_bytes(bytes);
                let tag = combined(&self.sram_taint[s..s + len]) | addr_taint;
                match slot {
                    Slot::Reg(i) => self.set_reg(i, value, tag),
                    Slot::Lane(i) => {
                        self.spg[i as usize] = value;
                        self.spg_taint[i as usize] = tag;
                    }
                }
            }
            return Ok(());
        }

        // Ring 0 (`applet_exec = false`):
        // * 0x0000..=0x0FFF (`I-ROM`): R+X, !W
        // * 0x10000..=0x101FF (`SRAM`): R+W, !X
        // * 0xFFFF_0000..=0xFFFF_007F (`SYS_MMIO`): accessible (R+W on control regs, R-only on Vault/PUF/LC_STATE)
        if end <= mem_map::IROM_BASE + mem_map::IROM_BYTES as u64 {
            if write {
                return Err(VmTrap::MemFault);
            }
            if addr % u64::from(size) != 0 {
                return Err(VmTrap::MisalignedMem);
            }
            let s = addr as usize;
            let mut bytes = [0u8; 8];
            bytes[..len].copy_from_slice(&self.irom[s..s + len]);
            let value = u64::from_le_bytes(bytes);
            let tag = combined(&self.irom_taint[s..s + len]) | addr_taint;
            match slot {
                Slot::Reg(i) => self.set_reg(i, value, tag),
                Slot::Lane(i) => {
                    self.spg[i as usize] = value;
                    self.spg_taint[i as usize] = tag;
                }
            }
            return Ok(());
        }
        if addr >= mem_map::SRAM_BASE && end <= mem_map::SRAM_BASE + mem_map::SRAM_BYTES as u64 {
            if addr % u64::from(size) != 0 {
                return Err(VmTrap::MisalignedMem);
            }
            let s = (addr - mem_map::SRAM_BASE) as usize;
            if write {
                let (value, tag) = match slot {
                    Slot::Reg(i) => (self.regs[i as usize], self.reg_taint[i as usize]),
                    Slot::Lane(i) => (self.spg[i as usize], self.spg_taint[i as usize]),
                };
                self.sram[s..s + len].copy_from_slice(&value.to_le_bytes()[..len]);
                self.sram_taint[s..s + len].fill(tag | addr_taint);
            } else {
                let mut bytes = [0u8; 8];
                bytes[..len].copy_from_slice(&self.sram[s..s + len]);
                let value = u64::from_le_bytes(bytes);
                let tag = combined(&self.sram_taint[s..s + len]) | addr_taint;
                match slot {
                    Slot::Reg(i) => self.set_reg(i, value, tag),
                    Slot::Lane(i) => {
                        self.spg[i as usize] = value;
                        self.spg_taint[i as usize] = tag;
                    }
                }
            }
            return Ok(());
        }
        if addr >= mem_map::SYS_MMIO_BASE
            && end <= mem_map::SYS_MMIO_BASE + mem_map::SYS_MMIO_BYTES as u64
        {
            if addr % u64::from(size) != 0 {
                return Err(VmTrap::MisalignedMem);
            }
            let off = addr - mem_map::SYS_MMIO_BASE;
            if write {
                let value = match slot {
                    Slot::Reg(i) => self.regs[i as usize],
                    Slot::Lane(i) => self.spg[i as usize],
                };
                self.mmio_write(off, size, value)?;
            } else {
                let (img, tags) = self.mmio_image();
                let s = off as usize;
                let mut bytes = [0u8; 8];
                bytes[..len].copy_from_slice(&img[s..s + len]);
                let value = u64::from_le_bytes(bytes);
                let tag = combined(&tags[s..s + len]) | addr_taint;
                match slot {
                    Slot::Reg(i) => self.set_reg(i, value, tag),
                    Slot::Lane(i) => {
                        self.spg[i as usize] = value;
                        self.spg_taint[i as usize] = tag;
                    }
                }
            }
            return Ok(());
        }
        Err(VmTrap::MemFault)
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
        if self.mpu_enabled {
            return self.transfer_mpu(ra, addr, size, slot, write);
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tooth_vm_unhandled_trap_stays_latched_across_subsequent_step_and_run() {
        // `#tooth`: Previously an unhandled trap set `self.halted = true` without latching
        // the trap cause, so a second `vm.step()` or `vm.run(...)` returned `Halted` instead of `Trap`.
        let mut vm = Ass2Vm::new(64);
        vm.load_image(0, &0xFFFF_FFFFu32.to_le_bytes()).unwrap();
        assert_eq!(vm.run(8), RunExit::Trap(VmTrap::IllegalInsn));
        assert_eq!(vm.step(), StepOutcome::Trap(VmTrap::IllegalInsn));
        assert_eq!(vm.run(8), RunExit::Trap(VmTrap::IllegalInsn));
    }
}
