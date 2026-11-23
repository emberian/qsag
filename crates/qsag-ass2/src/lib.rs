//! `ASS2 / Dregg-64`: a fixed-width 32-bit, little-endian, constant-time-by-construction
//! cryptographic RISC.
//!
//! * [`isa`]: the typed instruction set [`Ass2Insn`], the total codec ([`encode_insn`],
//!   [`decode_insn`]) with every reserved-bit and range rule, the fixed [`cycle_cost`] table
//!   and the disassembler.
//! * [`asm`]: the two-pass assembler ([`assemble`]).
//! * [`vm`]: the cycle-accurate reference machine [`Ass2Vm`] with its DIT taint auditor.
//! * [`firmware`]: the four QSAG microcode programs ([`fw_zkhem_v2_fp5_sumcheck`],
//!   [`fw_zkhem_v2_canopy50_verify`], [`fw_poseidon2_gl24_jive`], [`fw_cth_gf128_and_wots`]),
//!   their mailbox ABI and the runners that execute them on [`Ass2Vm`].
//!
//! The crate is `no_std` + `alloc`, has no dependency outside the workspace and forbids
//! `unsafe`.

#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod asm;
pub mod firmware;
pub mod isa;
pub mod vm;

pub use asm::{AsmError, AsmErrorKind, Assembly, MAX_ASM_IMAGE_BYTES, assemble, assemble_at};
pub use firmware::{
    CanopyInput, CanopyOutput, CthWotsInput, CthWotsOutput, FirmwareError, JiveInput,
    SumcheckInput, SumcheckOutput, fw_cth_gf128_and_wots, fw_poseidon2_gl24_jive,
    fw_zkhem_v2_canopy50_verify, fw_zkhem_v2_fp5_sumcheck, run_cth_gf128_and_wots,
    run_poseidon2_gl24_jive, run_zkhem_v2_canopy50_verify, run_zkhem_v2_fp5_sumcheck,
};
pub use isa::{
    AluOp, AluiOp, Ass2Insn, BrOp, CodecError, Imm20Mode, LoadMode, StoreMode, csr, cycle_cost,
    decode_insn, decode_insn_le, disassemble_bytes, disassemble_insn, encode_insn, encode_insn_le,
    mem_map,
};
pub use vm::{
    Ass2Vm, Cause, Csrs, DitMode, DitViolation, DitViolationKind, EnclaveError, EnclaveMmio,
    LcState, MemAccess, MemRangeError, Observation, RunExit, StepOutcome, Taint, Trace, VmTrap,
};
pub mod wire;
