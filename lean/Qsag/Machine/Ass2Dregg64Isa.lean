module
/-
# Qsag.Machine.Ass2Dregg64Isa — `ASS2 / Dregg-64` architectural state and total step function

The operational semantics of the `ASS2 / Dregg-64` enclave ISA (`ass2-dregg64-canonical-spec.md`)
over the instruction syntax and codec of `Qsag.Machine.Ass2Dregg64Codec`.

* `Ass2State`: `PC`, `R0..R15`, the sponge / wide-field bank `S0..S24`, the control registers and
  a byte-addressed little-endian memory. `R0` reads as `0` (`Ass2State.rget`) and a write to it
  changes no register (`Ass2State.setReg`).
* `execAss2`: the effect of one decoded instruction. `stepAss2`: fetch, decode, execute; total and
  deterministic. `runAss2`: iteration.
* The cryptographic instructions are the library's field and permutation definitions applied to
  views of the bank: `GL.*` is `Goldilocks.mul` / `add` / `sub` and `Poseidon2Gl24.sbox7`; `FP5.*`
  is `QuinticGoldilocks.mul` / `add` / `sub` on `E_k = S[5k..5k+4]`; `GF128.*` is
  `Math.Gf2Pow128.mul` / `add` on `P_k = (S[2k], S[2k+1])`; `KECCAK.F1600` is the last `rounds`
  rounds of `keccakF1600` (`keccakRounds`); `POSEIDON2.GL24` is `Poseidon2Gl24.poseidon2Gl24Perm`
  and `POSEIDON2.GL12` is `poseidon2Perm12`.
* `ass2_r0_always_zero`, `ass2_slk16_four_step_loads_any_u64`, `ass2_zeroize_wipes_all_secrets`,
  `ass2_fp5_mul_self_alias_safe`, `ass2_jalr_self_alias_safe`: the architectural invariants.
* `runAss2_straight`: a loaded straight-line program runs as the fold of `execAss2` over it.

Choices where the spec is silent, matching the reference model `hardware/ass2/sim/ass2_model.py`:
a trap charges one cycle and does not retire; `CSRR` of a write-only or unassigned register and
`CSRW` of a read-only or unassigned register are `IllegalInsn`; `CSRR INSTRET` / `CYCLES` read
the value before the instruction's own increment; a taken `EXC` adds one cycle and does not
retire. The full address-space step assumes mapped memory.
`stepAss2InRam` raises `MemFault` (cause 5) on out-of-bounds fetches and data accesses. `EXC` with
`EXC_EN = 0` follows the spec's formula `PC := PC + 4` (`ass2_exc_untaken_advances`).
-/

public import Qsag.Machine.Ass2Dregg64Codec
public import Qsag.Math.Goldilocks
public import Qsag.Math.QuinticExt5
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Poseidon2Gl24
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Ass2

set_option autoImplicit false

/-! ## 1. Architectural state -/

/-- The architectural state. `mem` is byte addressed; 64-bit and 32-bit accesses are
    little-endian (`read64`, `write64`, `fetch32`). `dbgOut` is the stream written to `DBG_OUT`. -/
structure Ass2State where
  pc : UInt64
  regs : Reg → UInt64
  spg : Fin 25 → UInt64
  mem : UInt64 → UInt8
  evec : UInt64
  epc : UInt64
  ecause : UInt64
  excEn : Bool
  halted : Bool
  instret : UInt64
  cycles : UInt64
  dbgOut : List UInt8
  /-- The base core has no receiver. An attached UART supplies the pending public bytes. -/
  dbgIn : Option (List UInt8) := none

namespace Ass2State

/-- Register read: `R0` is `0`. -/
abbrev rget (s : Ass2State) (r : Reg) : UInt64 := if r = 0 then 0 else s.regs r

/-- Register write: a write to `R0` changes no register. -/
abbrev setReg (s : Ass2State) (rd : Reg) (v : UInt64) : Ass2State :=
  { s with regs := fun r => if r = rd ∧ rd ≠ 0 then v else s.regs r }

/-- Replace the sponge / wide-field bank. -/
abbrev setSpg (s : Ass2State) (σ : Fin 25 → UInt64) : Ass2State := { s with spg := σ }

/-- Clear every register and every lane. -/
abbrev wipe (s : Ass2State) : Ass2State := { s with regs := fun _ => 0, spg := fun _ => 0 }

/-- Replace the memory. -/
abbrev setMem (s : Ass2State) (m : UInt64 → UInt8) : Ass2State := { s with mem := m }

/-- Retire an instruction of latency `cost` and continue at `npc`. -/
abbrev retireTo (s : Ass2State) (npc cost : UInt64) : Ass2State :=
  { s with pc := npc, instret := s.instret + 1, cycles := s.cycles + cost }

/-- Retire an instruction of latency `cost` and continue at `PC + 4`. -/
abbrev retire (s : Ass2State) (cost : UInt64) : Ass2State := s.retireTo (s.pc + 4) cost

/-- Trap with `cause` at the current instruction: vector to `EVEC` when `EXC_EN = 1`, halt
    otherwise. -/
abbrev trap (s : Ass2State) (cause : UInt64) : Ass2State :=
  if s.excEn then { s with epc := s.pc, ecause := cause, excEn := false, pc := s.evec, cycles := s.cycles + 1 }
  else { s with halted := true, ecause := cause, cycles := s.cycles + 1 }

end Ass2State

/-- Lane `k` of the bank; an index `≥ 25` reads as `0`. -/
abbrev lane (σ : Fin 25 → UInt64) (k : Nat) : UInt64 := if h : k < 25 then σ ⟨k, h⟩ else 0

/-- Write lane `k`; an index `≥ 25` writes nothing. -/
abbrev setLane (σ : Fin 25 → UInt64) (k : Nat) (v : UInt64) : Fin 25 → UInt64 :=
  fun j => if j.val = k then v else σ j

/-- Byte `k` of the little-endian 64-bit word at `a`, in position. -/
abbrev byteAt (m : UInt64 → UInt8) (a : UInt64) (k : Nat) : UInt64 :=
  (m (a + UInt64.ofNat k)).toUInt64 <<< UInt64.ofNat (8 * k)

/-- `mem_read_le64`. -/
abbrev read64 (m : UInt64 → UInt8) (a : UInt64) : UInt64 :=
  byteAt m a 0 ||| byteAt m a 1 ||| byteAt m a 2 ||| byteAt m a 3 |||
  byteAt m a 4 ||| byteAt m a 5 ||| byteAt m a 6 ||| byteAt m a 7

/-- `mem_write_le64`: the eight bytes `a .. a + 7` (addresses wrap modulo `2^64`). -/
abbrev write64 (m : UInt64 → UInt8) (a v : UInt64) : UInt64 → UInt8 :=
  fun x => if (x - a).toNat < 8 then (v >>> UInt64.ofNat (8 * (x - a).toNat)).toUInt8 else m x

/-- The little-endian 32-bit instruction word at `a`. -/
abbrev fetch32 (m : UInt64 → UInt8) (a : UInt64) : UInt32 :=
  (m (a + UInt64.ofNat 0)).toUInt32 ||| ((m (a + UInt64.ofNat 1)).toUInt32 <<< 8) |||
  ((m (a + UInt64.ofNat 2)).toUInt32 <<< 16) ||| ((m (a + UInt64.ofNat 3)).toUInt32 <<< 24)

/-- Zero extension to 64 bits. -/
abbrev zext {w : Nat} (x : BitVec w) : UInt64 := UInt64.ofBitVec (x.setWidth 64)
/-- Sign extension to 64 bits. -/
abbrev sext {w : Nat} (x : BitVec w) : UInt64 := UInt64.ofBitVec (x.signExtend 64)

/-! ## 2. Datapath -/

/-- `LUT4`: bit `k` of the result is bit `2 * a[k] + b[k]` of the truth table `m`. -/
def lut4Eval (m : Fin 16) (a b : UInt64) : UInt64 :=
  (if m.val.testBit 0 then ~~~a &&& ~~~b else 0) ||| (if m.val.testBit 1 then ~~~a &&& b else 0) |||
  (if m.val.testBit 2 then a &&& ~~~b else 0) ||| (if m.val.testBit 3 then a &&& b else 0)

/-- `ALU`. -/
def aluEval : AluOp → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .shl, a, b => if b.toNat < 64 then a <<< b else 0
  | .shr, a, b => if b.toNat < 64 then a >>> b else 0
  | .asr, a, b => UInt64.ofBitVec (a.toBitVec.sshiftRight b.toNat)
  | .rol, a, b => UInt64.ofBitVec (a.toBitVec.rotateLeft (b.toNat % 64))
  | .ror, a, b => UInt64.ofBitVec (a.toBitVec.rotateRight (b.toNat % 64))
  | .mul64, a, b => a * b
  | .mulhu64, a, b => UInt64.ofNat (a.toNat * b.toNat / 18446744073709551616)

/-- `ALUI`. The immediate shift amounts are below 64 on well-formed instructions. -/
def aluiEval : AluiOp → UInt64 → BitVec 16 → UInt64
  | .addi, a, imm => a + sext imm
  | .addiu, a, imm => a + zext imm
  | .xori, a, imm => a ^^^ zext imm
  | .andi, a, imm => a &&& zext imm
  | .ori, a, imm => a ||| zext imm
  | .shli, a, imm => UInt64.ofBitVec (a.toBitVec <<< (imm.toNat % 64))
  | .shri, a, imm => UInt64.ofBitVec (a.toBitVec >>> (imm.toNat % 64))
  | .asri, a, imm => UInt64.ofBitVec (a.toBitVec.sshiftRight (imm.toNat % 64))
  | .roli, a, imm => UInt64.ofBitVec (a.toBitVec.rotateLeft (imm.toNat % 64))
  | .slk16, a, imm => (a <<< 16) ||| zext imm

/-- `CMP`: `flags = IV | SN | GT | EQ`. -/
def cmpEval (flags : Fin 16) (a b : UInt64) : UInt64 :=
  let e := flags.val.testBit 0 && decide (a = b)
  let g := flags.val.testBit 1 &&
    (if flags.val.testBit 2 then b.toBitVec.slt a.toBitVec else decide (b < a))
  if (if flags.val.testBit 3 then !(e || g) else (e || g)) then 1 else 0

/-- Byte length of `BEXTU` / `BEXTS`: a zero length field means 8. -/
abbrev bextLen (len : Nat) : Nat := if len % 8 = 0 then 8 else len % 8

/-- `BEXTU`: `len` bytes of `a` from byte `idx`, zero extended. -/
def bextuEval (a : UInt64) (idx len : Nat) : UInt64 :=
  UInt64.ofNat (a.toNat / 2 ^ (8 * (idx % 8)) % 2 ^ (8 * bextLen len))

/-- `BEXTS`: `len` bytes of `a` from byte `idx`, sign extended from bit `8 * len - 1`. -/
def bextsEval (a : UInt64) (idx len : Nat) : UInt64 :=
  sext (BitVec.ofNat (8 * bextLen len) (a.toNat / 2 ^ (8 * (idx % 8))))

/-- `BSWAP64`. -/
def bswap64Eval (a : UInt64) : UInt64 :=
  ((a &&& 0xFF) <<< 56) ||| (((a >>> 8) &&& 0xFF) <<< 48) ||| (((a >>> 16) &&& 0xFF) <<< 40) |||
  (((a >>> 24) &&& 0xFF) <<< 32) ||| (((a >>> 32) &&& 0xFF) <<< 24) |||
  (((a >>> 40) &&& 0xFF) <<< 16) ||| (((a >>> 48) &&& 0xFF) <<< 8) ||| (a >>> 56)

/-- `BR` condition. -/
abbrev brTake (op : BrOp) (v : UInt64) : Bool :=
  match op with
  | .beqz => v == 0
  | .bnez => v != 0
  | .bltz => v.toBitVec.msb
  | .bgez => !v.toBitVec.msb

/-! ### Goldilocks, quintic extension, `GF(2^128)` and permutation views -/

/-- A 64-bit word as a Goldilocks element (`x mod p`). -/
abbrev glOf (x : UInt64) : Goldilocks := Goldilocks.ofNat x.toNat
/-- The canonical representative of a Goldilocks element. -/
abbrev glTo (g : Goldilocks) : UInt64 := UInt64.ofNat g.val

/-- `GL.MAC`: `a * b + c` in `Goldilocks`. -/
def glMac (a b c : UInt64) : UInt64 := glTo (Goldilocks.add (Goldilocks.mul (glOf a) (glOf b)) (glOf c))
/-- `GL.ADD`. -/
def glAdd (a b : UInt64) : UInt64 := glTo (Goldilocks.add (glOf a) (glOf b))
/-- `GL.SUB`. -/
def glSub (a b : UInt64) : UInt64 := glTo (Goldilocks.sub (glOf a) (glOf b))
/-- `GL.SBOX7`: `a^7` in `Goldilocks`, the S-box of `Poseidon2Gl24`. -/
def glSbox7 (a : UInt64) : UInt64 := glTo (Poseidon2Gl24.sbox7 (glOf a))

/-- Quintic register `E_e = S[5e .. 5e + 4]`. -/
def fp5Read (σ : Fin 25 → UInt64) (e : Nat) : QuinticGoldilocks :=
  ⟨glOf (lane σ (5 * e + 0)), glOf (lane σ (5 * e + 1)), glOf (lane σ (5 * e + 2)),
   glOf (lane σ (5 * e + 3)), glOf (lane σ (5 * e + 4))⟩

/-- Limb `t` of a quintic element as a canonical word. -/
def fp5Limb (q : QuinticGoldilocks) : Nat → UInt64
  | 0 => glTo q.c0
  | 1 => glTo q.c1
  | 2 => glTo q.c2
  | 3 => glTo q.c3
  | _ => glTo q.c4

/-- `E_e := q`. -/
def fp5Write (σ : Fin 25 → UInt64) (e : Nat) (q : QuinticGoldilocks) : Fin 25 → UInt64 :=
  fun j => if j.val / 5 = e then fp5Limb q (j.val % 5) else σ j

/-- Polynomial register `P_k = (lo: S[2k], hi: S[2k + 1])`. -/
def gfRead (σ : Fin 25 → UInt64) (k : Nat) : Math.Gf2Pow128 :=
  ⟨(lane σ (2 * k + 1)).toBitVec ++ (lane σ (2 * k + 0)).toBitVec⟩

/-- Half `t` of a `GF(2^128)` element: `0` is the low word, anything else the high word. -/
def gfLimb (x : Math.Gf2Pow128) (t : Nat) : UInt64 :=
  if t = 0 then UInt64.ofBitVec (x.bits.extractLsb' 0 64)
  else UInt64.ofBitVec (x.bits.extractLsb' 64 64)

/-- `P_k := x`. -/
def gfWrite (σ : Fin 25 → UInt64) (k : Nat) (x : Math.Gf2Pow128) : Fin 25 → UInt64 :=
  fun j => if j.val / 2 = k then gfLimb x (j.val % 2) else σ j

/-- The bank as a `Keccak-f[1600]` state. -/
def kRead (σ : Fin 25 → UInt64) : KState :=
  ⟨lane σ 0, lane σ 1, lane σ 2, lane σ 3, lane σ 4,
   lane σ 5, lane σ 6, lane σ 7, lane σ 8, lane σ 9,
   lane σ 10, lane σ 11, lane σ 12, lane σ 13, lane σ 14,
   lane σ 15, lane σ 16, lane σ 17, lane σ 18, lane σ 19,
   lane σ 20, lane σ 21, lane σ 22, lane σ 23, lane σ 24⟩

/-- Lane `j` of a `Keccak-f[1600]` state. -/
def kLane (k : KState) (j : Fin 25) : UInt64 :=
  match j.val with
  | 0 => k.a0
  | 1 => k.a1
  | 2 => k.a2
  | 3 => k.a3
  | 4 => k.a4
  | 5 => k.a5
  | 6 => k.a6
  | 7 => k.a7
  | 8 => k.a8
  | 9 => k.a9
  | 10 => k.a10
  | 11 => k.a11
  | 12 => k.a12
  | 13 => k.a13
  | 14 => k.a14
  | 15 => k.a15
  | 16 => k.a16
  | 17 => k.a17
  | 18 => k.a18
  | 19 => k.a19
  | 20 => k.a20
  | 21 => k.a21
  | 22 => k.a22
  | 23 => k.a23
  | _ => k.a24

/-- The last `n` rounds of `Keccak-f[1600]`: `n = 24` is `keccakF1600` (`keccakRounds_24`) and
    `n = 12` is rounds `12..23`, the permutation of `TurboSHAKE`. -/
def keccakRounds (n : Nat) (st : KState) : KState :=
  (keccakRoundConstants.drop (24 - n)).foldl roundS st

theorem keccakRounds_24 (st : KState) : keccakRounds 24 st = keccakF1600 st := by
  unfold keccakRounds keccakF1600
  rfl

/-- Lanes `S[0..23]` as a `Poseidon2-GL-w24` state. -/
def p24Read (σ : Fin 25 → UInt64) : Poseidon2Gl24.Poseidon2State24 :=
  ⟨⟨glOf (lane σ 0), glOf (lane σ 1), glOf (lane σ 2), glOf (lane σ 3)⟩,
   ⟨glOf (lane σ 4), glOf (lane σ 5), glOf (lane σ 6), glOf (lane σ 7)⟩,
   ⟨glOf (lane σ 8), glOf (lane σ 9), glOf (lane σ 10), glOf (lane σ 11)⟩,
   ⟨glOf (lane σ 12), glOf (lane σ 13), glOf (lane σ 14), glOf (lane σ 15)⟩,
   ⟨glOf (lane σ 16), glOf (lane σ 17), glOf (lane σ 18), glOf (lane σ 19)⟩,
   ⟨glOf (lane σ 20), glOf (lane σ 21), glOf (lane σ 22), glOf (lane σ 23)⟩⟩

/-- Lane `j < 24` of a `Poseidon2-GL-w24` state as a canonical word. -/
def p24Lane (st : Poseidon2Gl24.Poseidon2State24) : Nat → UInt64
  | 0 => glTo st.b0.x0
  | 1 => glTo st.b0.x1
  | 2 => glTo st.b0.x2
  | 3 => glTo st.b0.x3
  | 4 => glTo st.b1.x0
  | 5 => glTo st.b1.x1
  | 6 => glTo st.b1.x2
  | 7 => glTo st.b1.x3
  | 8 => glTo st.b2.x0
  | 9 => glTo st.b2.x1
  | 10 => glTo st.b2.x2
  | 11 => glTo st.b2.x3
  | 12 => glTo st.b3.x0
  | 13 => glTo st.b3.x1
  | 14 => glTo st.b3.x2
  | 15 => glTo st.b3.x3
  | 16 => glTo st.b4.x0
  | 17 => glTo st.b4.x1
  | 18 => glTo st.b4.x2
  | 19 => glTo st.b4.x3
  | 20 => glTo st.b5.x0
  | 21 => glTo st.b5.x1
  | 22 => glTo st.b5.x2
  | _ => glTo st.b5.x3

/-- Lanes `S[0..11]` as a width-12 `Poseidon2` state. -/
def p12Read (σ : Fin 25 → UInt64) : Poseidon2State12 :=
  ⟨⟨glOf (lane σ 0), glOf (lane σ 1), glOf (lane σ 2), glOf (lane σ 3)⟩,
   ⟨glOf (lane σ 4), glOf (lane σ 5), glOf (lane σ 6), glOf (lane σ 7)⟩,
   ⟨glOf (lane σ 8), glOf (lane σ 9), glOf (lane σ 10), glOf (lane σ 11)⟩⟩

/-- Lane `j < 12` of a width-12 `Poseidon2` state as a canonical word. -/
def p12Lane (st : Poseidon2State12) : Nat → UInt64
  | 0 => glTo st.b0.x0
  | 1 => glTo st.b0.x1
  | 2 => glTo st.b0.x2
  | 3 => glTo st.b0.x3
  | 4 => glTo st.b1.x0
  | 5 => glTo st.b1.x1
  | 6 => glTo st.b1.x2
  | 7 => glTo st.b1.x3
  | 8 => glTo st.b2.x0
  | 9 => glTo st.b2.x1
  | 10 => glTo st.b2.x2
  | _ => glTo st.b2.x3

/-! ## 3. Control registers -/

/-- The readable control registers. -/
inductive CsrR where
  | archId | wordBits | evec | instret | cycles | features | epc | ecause | excEn | dit | dbgIn
  deriving DecidableEq, Repr

/-- The readable register at an 8-bit address; `none` is `IllegalInsn`. -/
@[expose] def csrROf : Nat → Option CsrR
  | 0 => some .archId
  | 1 => some .wordBits
  | 2 => some .evec
  | 4 => some .instret
  | 5 => some .cycles
  | 6 => some .features
  | 8 => some .epc
  | 9 => some .ecause
  | 63 => some .excEn
  | 64 => some .dit
  | _ => none

/-- UART-equipped cores add the read-only DBG_IN register at 0x0B. -/
abbrev csrReadAddr (rx : Option (List UInt8)) (a : Nat) : Option CsrR :=
  if a = 11 ∧ rx.isSome = true then some .dbgIn else csrROf a

abbrev debugInputValue : Option (List UInt8) → UInt64
  | some (b :: _) => 0x100 + b.toUInt64
  | _ => 0

/-- A DBG_IN read acknowledges the sampled byte even when its destination is R0. -/
abbrev afterCsrRead (s : Ass2State) (c : CsrR) : Ass2State :=
  { s with dbgIn := match c with
    | .dbgIn => s.dbgIn.map List.tail
    | _ => s.dbgIn }

/-- `csr_read`. `DIT` reads `1` in every state. -/
@[expose] def csrGet (s : Ass2State) : CsrR → UInt64
  | .archId => 0x4153533200000001
  | .wordBits => 64
  | .evec => s.evec
  | .instret => s.instret
  | .cycles => s.cycles
  | .features => 0xF
  | .epc => s.epc
  | .ecause => s.ecause
  | .excEn => if s.excEn then 1 else 0
  | .dit => 1
  | .dbgIn => debugInputValue s.dbgIn

/-- The writable control registers. -/
inductive CsrW where
  | evec | power | instret | cycles | epc | ecause | dbgOut | excEn | zeroize
  deriving DecidableEq, Repr

/-- The writable register at an 8-bit address; `none` is `IllegalInsn`. -/
@[expose] def csrWOf : Nat → Option CsrW
  | 2 => some .evec
  | 3 => some .power
  | 4 => some .instret
  | 5 => some .cycles
  | 8 => some .epc
  | 9 => some .ecause
  | 10 => some .dbgOut
  | 63 => some .excEn
  | 65 => some .zeroize
  | _ => none

/-- `CSRW`: `csr_write` and retirement. A write to `INSTRET` or `CYCLES` replaces that counter
    instead of incrementing it. -/
@[expose] def csrApply (s : Ass2State) (c : CsrW) (v : UInt64) : Ass2State :=
  match c with
  | .evec => Ass2State.retire { s with evec := v &&& ~~~3 } 1
  | .power => Ass2State.retire { s with halted := s.halted || decide (v.toNat % 2 = 1) } 1
  | .instret => { s with pc := s.pc + 4, instret := v, cycles := s.cycles + 1 }
  | .cycles => { s with pc := s.pc + 4, instret := s.instret + 1, cycles := v }
  | .epc => Ass2State.retire { s with epc := v } 1
  | .ecause => Ass2State.retire { s with ecause := v } 1
  | .dbgOut => Ass2State.retire { s with dbgOut := s.dbgOut ++ [v.toUInt8] } 1
  | .excEn => Ass2State.retire { s with excEn := decide (v.toNat % 2 = 1) } 1
  | .zeroize => Ass2State.retire (if v.toNat % 2 = 1 then s.wipe else s) 1

/-! ## 4. Execution -/

/-- The effect of one decoded instruction. -/
@[expose] def execAss2 (i : Ass2Insn) (s : Ass2State) : Ass2State :=
  match i with
  | .exc =>
    if s.excEn then
      { s with epc := s.pc + 4, ecause := 2, excEn := false, pc := s.evec,
               cycles := s.cycles + cycleCost i }
    else s.retire (cycleCost i)
  | .eret =>
    { s with pc := s.epc &&& ~~~3, excEn := true, instret := s.instret + 1,
             cycles := s.cycles + cycleCost i }
  | .csrr rd a =>
    match csrReadAddr s.dbgIn a.toNat with
    | some c => ((afterCsrRead s c).setReg rd (csrGet s c)).retire (cycleCost i)
    | none => s.trap 1
  | .csrw ra a =>
    match csrWOf a.toNat with
    | some c => csrApply s c (s.rget ra)
    | none => s.trap 1
  | .zeroize => (s.wipe).retire (cycleCost i)
  | .halt => { s.retire (cycleCost i) with halted := true }
  | .nop => s.retire (cycleCost i)
  | .lut4 m rd ra rb => (s.setReg rd (lut4Eval m (s.rget ra) (s.rget rb))).retire (cycleCost i)
  | .alu op rd ra rb => (s.setReg rd (aluEval op (s.rget ra) (s.rget rb))).retire (cycleCost i)
  | .alui op rd ra imm => (s.setReg rd (aluiEval op (s.rget ra) imm)).retire (cycleCost i)
  | .movz20 rd imm => (s.setReg rd (zext imm)).retire (cycleCost i)
  | .movs20 rd imm => (s.setReg rd (sext imm)).retire (cycleCost i)
  | .auipc rd imm => (s.setReg rd (s.pc + (sext imm <<< (2 : UInt64)))).retire (cycleCost i)
  | .cmp flags rd ra rb =>
    (s.setReg rd (cmpEval flags (s.rget ra) (s.rget rb))).retire (cycleCost i)
  | .sel rd ra rb rc =>
    (s.setReg rd (if s.rget rc = 0 then s.rget ra else s.rget rb)).retire (cycleCost i)
  | .bextu rd ra idx len => (s.setReg rd (bextuEval (s.rget ra) idx.val len.val)).retire (cycleCost i)
  | .bexts rd ra idx len => (s.setReg rd (bextsEval (s.rget ra) idx.val len.val)).retire (cycleCost i)
  | .bswap64 rd ra => (s.setReg rd (bswap64Eval (s.rget ra))).retire (cycleCost i)
  | .ld64 rd ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      (s.setReg rd (read64 s.mem (s.rget ra + (sext off <<< (3 : UInt64))))).retire (cycleCost i)
    else s.trap 4
  | .ldbu rd ra off => (s.setReg rd (s.mem (s.rget ra + sext off)).toUInt64).retire (cycleCost i)
  | .st64 rv ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      (s.setMem (write64 s.mem (s.rget ra + (sext off <<< (3 : UInt64))) (s.rget rv))).retire (cycleCost i)
    else s.trap 4
  | .stb rv ra off =>
    (s.setMem (fun x => if x = s.rget ra + sext off then (s.rget rv).toUInt8 else s.mem x)).retire (cycleCost i)
  | .br op rc off =>
    s.retireTo (if brTake op (s.rget rc) then s.pc + 4 + (sext off <<< (2 : UInt64)) else s.pc + 4)
      (cycleCost i)
  | .jal rd off => (s.setReg rd (s.pc + 4)).retireTo (s.pc + 4 + (sext off <<< (2 : UInt64))) (cycleCost i)
  | .jalr rd ra off =>
    if (s.rget ra + (sext off <<< (2 : UInt64))).toNat % 4 = 0 then
      (s.setReg rd (s.pc + 4)).retireTo ((s.rget ra + (sext off <<< (2 : UInt64))) &&& ~~~3) (cycleCost i)
    else s.trap 3
  | .sget rd k => (s.setReg rd (lane s.spg k.toNat)).retire (cycleCost i)
  | .sput k ra =>
    (s.setSpg (setLane s.spg k.toNat (s.rget ra))).retire (cycleCost i)
  | .sxor k ra =>
    (s.setSpg (setLane s.spg k.toNat (lane s.spg k.toNat ^^^ s.rget ra))).retire (cycleCost i)
  | .szero => (s.setSpg (fun _ => 0)).retire (cycleCost i)
  | .sld64 k ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      (s.setSpg (setLane s.spg k.toNat (read64 s.mem (s.rget ra + (sext off <<< (3 : UInt64)))))).retire (cycleCost i)
    else s.trap 4
  | .sst64 k ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      (s.setMem (write64 s.mem (s.rget ra + (sext off <<< (3 : UInt64))) (lane s.spg k.toNat))).retire (cycleCost i)
    else s.trap 4
  | .glMac rd ra rb rc =>
    (s.setReg rd (glMac (s.rget ra) (s.rget rb) (s.rget rc))).retire (cycleCost i)
  | .glAdd rd ra rb => (s.setReg rd (glAdd (s.rget ra) (s.rget rb))).retire (cycleCost i)
  | .glSub rd ra rb => (s.setReg rd (glSub (s.rget ra) (s.rget rb))).retire (cycleCost i)
  | .glSbox7 rd ra => (s.setReg rd (glSbox7 (s.rget ra))).retire (cycleCost i)
  | .fp5Mul ed ea eb =>
    (s.setSpg (fp5Write s.spg ed.val
      (QuinticGoldilocks.mul (fp5Read s.spg ea.val) (fp5Read s.spg eb.val)))).retire (cycleCost i)
  | .fp5Add ed ea eb =>
    (s.setSpg (fp5Write s.spg ed.val
      (QuinticGoldilocks.add (fp5Read s.spg ea.val) (fp5Read s.spg eb.val)))).retire (cycleCost i)
  | .fp5Sub ed ea eb =>
    (s.setSpg (fp5Write s.spg ed.val
      (QuinticGoldilocks.sub (fp5Read s.spg ea.val) (fp5Read s.spg eb.val)))).retire (cycleCost i)
  | .gf128Mul pd pa pb =>
    (s.setSpg (gfWrite s.spg pd.val
      (Math.Gf2Pow128.mul (gfRead s.spg pa.val) (gfRead s.spg pb.val)))).retire (cycleCost i)
  | .gf128Xor pd pa pb =>
    (s.setSpg (gfWrite s.spg pd.val
      (Math.Gf2Pow128.add (gfRead s.spg pa.val) (gfRead s.spg pb.val)))).retire (cycleCost i)
  | .keccak rounds =>
    (s.setSpg (kLane (keccakRounds rounds.toNat (kRead s.spg)))).retire (cycleCost i)
  | .poseidon2Gl24 =>
    let result := Poseidon2Gl24.poseidon2Gl24Perm (p24Read s.spg)
    (s.setSpg (fun j => if j.val < 24 then p24Lane result j.val else s.spg j)).retire (cycleCost i)
  | .poseidon2Gl12 =>
    let result := poseidon2Perm12 (p12Read s.spg)
    (s.setSpg (fun j => if j.val < 12 then p12Lane result j.val else s.spg j)).retire (cycleCost i)

/-- One step: a halted machine stays put; a misaligned `PC` is `MisalignedPc`; a word the decoder
    rejects is `IllegalInsn`; otherwise the decoded instruction executes. -/
@[expose] def stepAss2 (s : Ass2State) : Ass2State :=
  if s.halted then s
  else if s.pc.toNat % 4 = 0 then
    match decodeAss2 (fetch32 s.mem s.pc) with
    | some i => execAss2 i s
    | none => s.trap 1
  else s.trap 3

/-- `n` steps. -/
@[expose] def runAss2 : Nat → Ass2State → Ass2State
  | 0, s => s
  | n + 1, s => runAss2 n (stepAss2 s)

/-- The effective address of the data access of `i` in state `s`, if it makes one. -/
@[expose] def effAddr (i : Ass2Insn) (s : Ass2State) : Option UInt64 :=
  match i with
  | .ld64 _ ra off => some (s.rget ra + (sext off <<< (3 : UInt64)))
  | .ldbu _ ra off => some (s.rget ra + sext off)
  | .st64 _ ra off => some (s.rget ra + (sext off <<< (3 : UInt64)))
  | .stb _ ra off => some (s.rget ra + sext off)
  | .sld64 _ ra off => some (s.rget ra + (sext off <<< (3 : UInt64)))
  | .sst64 _ ra off => some (s.rget ra + (sext off <<< (3 : UInt64)))
  | _ => none

/-- Major opcodes `0x1 .. 0x8` and `0xC .. 0xF`: every instruction other than `SYS`, `BR`, `JAL`
    and `JALR`. -/
@[expose] def Ass2Insn.isDataPath : Ass2Insn → Bool
  | .exc | .eret | .csrr _ _ | .csrw _ _ | .zeroize | .halt | .nop => false
  | .br _ _ _ | .jal _ _ | .jalr _ _ _ => false
  | _ => true

/-- Instructions that neither transfer control, trap, access memory nor touch a control
    register. -/
@[expose] def Ass2Insn.isStraight : Ass2Insn → Bool
  | .exc | .eret | .csrr _ _ | .csrw _ _ | .zeroize | .halt => false
  | .br _ _ _ | .jal _ _ | .jalr _ _ _ => false
  | .ld64 _ _ _ | .ldbu _ _ _ | .st64 _ _ _ | .stb _ _ _ | .sld64 _ _ _ | .sst64 _ _ _ => false
  | _ => true

/-! ## 5. Step and run lemmas -/

/-- A trap changes no register, lane or memory byte. -/
theorem trap_frame (s : Ass2State) (c : UInt64) :
    (s.trap c).regs = s.regs ∧ (s.trap c).spg = s.spg ∧ (s.trap c).mem = s.mem ∧
    (s.trap c).instret = s.instret ∧ (s.trap c).cycles = s.cycles + 1 := by
  unfold Ass2State.trap
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stepAss2_eq_exec {s : Ass2State} {i : Ass2Insn} (hh : s.halted = false)
    (hpc : s.pc.toNat % 4 = 0) (hf : decodeAss2 (fetch32 s.mem s.pc) = some i) :
    stepAss2 s = execAss2 i s := by
  unfold stepAss2
  rw [ite_eq_right (by rw [hh]; decide), ite_eq_left hpc, hf]

theorem stepAss2_halted {s : Ass2State} (hh : s.halted = true) : stepAss2 s = s := by
  unfold stepAss2
  rw [ite_eq_left hh]

/-- The instruction the next step executes: `none` when the machine is halted, `PC` is
    misaligned or the fetched word is illegal. -/
def currentInsn (s : Ass2State) : Option Ass2Insn :=
  if s.halted then none
  else if s.pc.toNat % 4 = 0 then decodeAss2 (fetch32 s.mem s.pc) else none

/-- Byte extent of a data transaction. Used only when `effAddr` supplies an address. -/
abbrev dataBytes : Ass2Insn → Nat
  | .ldbu .. | .stb .. => 1
  | _ => 8

/-- Fetch outside a contiguous RAM of `size` bytes. A halted or misaligned fetch
    never submits a request. Natural addition also handles the top of the address space. -/
abbrev fetchFault (size : Nat) (s : Ass2State) : Bool :=
  !s.halted && decide (s.pc.toNat % 4 = 0) && decide (size < s.pc.toNat + 4)

/-- Aligned, out-of-bounds data access. The base step handles misalignment first. -/
abbrev dataFault (size width : Nat) (addr : Option UInt64) : Bool :=
  match addr with
  | none => false
  | some a => decide (a.toNat % width = 0) && decide (size < a.toNat + width)

/-- Whether the bounded-memory realization takes `MemFault` on this step. -/
abbrev ramFault (size : Nat) (s : Ass2State) : Bool :=
  fetchFault size s || (match currentInsn s with
    | none => false
    | some i => dataFault size (dataBytes i) (effAddr i s))

/-- Execute on a contiguous byte RAM, as in the Rust VM and the RTL lockstep bus.
    A failed fetch or data transaction traps before any destination or memory write. -/
def stepAss2InRam (size : Nat) (s : Ass2State) : Ass2State :=
  if ramFault size s then s.trap 5 else stepAss2 s

theorem stepAss2InRam_eq (size : Nat) (s : Ass2State) :
    stepAss2InRam size s = if ramFault size s then s.trap 5 else stepAss2 s := by
  unfold stepAss2InRam
  rfl

/-- A RAM spanning the full address space realizes the original total-memory ISA for
    every state. Aligned accesses of widths 1, 4 and 8 fit even at the last legal address. -/
theorem stepAss2InRam_full (s : Ass2State) : stepAss2InRam (2^64) s = stepAss2 s := by
  have fetch : fetchFault (2^64) s = false := by
    unfold fetchFault
    by_cases h : s.pc.toNat % 4 = 0
    · have := s.pc.toNat_lt
      have bound : ¬ 2^64 < s.pc.toNat + 4 := by omega
      simp only [bound, decide_false, Bool.and_false]
    · simp only [h, decide_false, Bool.and_false, Bool.false_and]
  have data : ∀ (i : Ass2Insn) (a : UInt64), dataFault (2^64) (dataBytes i) (some a) = false := by
    intro i a
    have hw : dataBytes i = 1 ∨ dataBytes i = 8 := by
      cases i <;> first | exact Or.inl rfl | exact Or.inr rfl
    have := a.toNat_lt
    rcases hw with h | h
    · have bound : ¬ 2^64 < a.toNat + 1 := by omega
      simp only [h, dataFault, bound, decide_false, Bool.and_false]
    · by_cases hal : a.toNat % 8 = 0
      · have bound : ¬ 2^64 < a.toNat + 8 := by omega
        simp only [h, dataFault, bound, decide_false, Bool.and_false]
      · simp only [h, dataFault, hal, decide_false, Bool.false_and]
  have ok : ramFault (2^64) s = false := by
    simp only [ramFault, fetch, Bool.false_or]
    cases currentInsn s with
    | none => rfl
    | some i =>
      change dataFault (2^64) (dataBytes i) (effAddr i s) = false
      cases effAddr i s with
      | none => rfl
      | some a => exact data i a
  rw [stepAss2InRam_eq, ok]
  rfl

theorem currentInsn_eq (s : Ass2State) :
    currentInsn s =
      if s.halted then none
      else if s.pc.toNat % 4 = 0 then decodeAss2 (fetch32 s.mem s.pc) else none := by
  rfl

theorem currentInsn_of_fetch {s : Ass2State} {i : Ass2Insn} (hh : s.halted = false)
    (hpc : s.pc.toNat % 4 = 0) (hf : decodeAss2 (fetch32 s.mem s.pc) = some i) :
    currentInsn s = some i := by
  unfold currentInsn
  rw [ite_eq_right (by rw [hh]; decide), ite_eq_left hpc, hf]

/-- A step that executes an instruction is `execAss2` of it. -/
theorem stepAss2_of_currentInsn_some {s : Ass2State} {i : Ass2Insn}
    (h : currentInsn s = some i) : stepAss2 s = execAss2 i s := by
  unfold currentInsn at h
  unfold stepAss2
  split
  · rename_i hh; rw [ite_eq_left hh] at h; cases h
  · rename_i hh
    rw [ite_eq_right hh] at h
    split
    · rename_i hpc; rw [ite_eq_left hpc] at h; rw [h]
    · rename_i hpc; rw [ite_eq_right hpc] at h; cases h

/-- A step that executes no instruction leaves a halted machine unchanged and otherwise traps:
    `IllegalInsn` at an aligned `PC`, `MisalignedPc` at a misaligned one. -/
theorem stepAss2_of_currentInsn_none {s : Ass2State} (h : currentInsn s = none) :
    stepAss2 s = if s.halted then s else s.trap (if s.pc.toNat % 4 = 0 then 1 else 3) := by
  unfold currentInsn at h
  unfold stepAss2
  split
  · rfl
  · rename_i hh
    rw [ite_eq_right hh] at h
    split
    · rename_i hpc; rw [ite_eq_left hpc] at h; rw [h]
    · rfl

theorem runAss2_succ (n : Nat) (s : Ass2State) : runAss2 (n + 1) s = runAss2 n (stepAss2 s) := by
  rfl

theorem aligned_add4 (a : UInt64) (h : a.toNat % 4 = 0) : (a + 4).toNat % 4 = 0 := by
  rw [UInt64.toNat_add]
  have h4 : (4 : UInt64).toNat = 4 := by decide
  rw [h4]
  omega

/-- A straight instruction continues at `PC + 4` and leaves memory and `halted` unchanged. -/
theorem execAss2_straight {i : Ass2Insn} (hi : i.isStraight = true) (s : Ass2State) :
    (execAss2 i s).pc = s.pc + 4 ∧ (execAss2 i s).mem = s.mem ∧
    (execAss2 i s).halted = s.halted := by
  cases i <;> first | exact ⟨rfl, rfl, rfl⟩ | exact absurd hi Bool.false_ne_true

/-- `prog` sits in memory `m` at `a`, one encoded word per instruction. -/
@[expose] def LoadedAt (m : UInt64 → UInt8) : UInt64 → List Ass2Insn → Prop
  | _, [] => True
  | a, i :: rest => fetch32 m a = encodeAss2 i ∧ LoadedAt m (a + 4) rest

/-- A loaded program of well-formed straight instructions runs as the fold of `execAss2`. -/
theorem runAss2_straight (prog : List Ass2Insn) :
    ∀ (s : Ass2State), s.halted = false → s.pc.toNat % 4 = 0 → LoadedAt s.mem s.pc prog →
      (∀ i, i ∈ prog → i.WellFormed ∧ i.isStraight = true) →
      runAss2 prog.length s = prog.foldl (fun t i => execAss2 i t) s := by
  induction prog with
  | nil => intro s _ _ _ _; rfl
  | cons i rest ih =>
    intro s hh hpc hl hs
    obtain ⟨hwf, hst⟩ := hs i (List.mem_cons_self ..)
    obtain ⟨hf, hrest⟩ := hl
    have hstep : stepAss2 s = execAss2 i s :=
      stepAss2_eq_exec hh hpc (by rw [hf]; exact decodeAss2_encodeAss2 i hwf)
    obtain ⟨epc, emem, ehalt⟩ := execAss2_straight hst s
    show runAss2 rest.length (stepAss2 s) = rest.foldl (fun t i => execAss2 i t) (execAss2 i s)
    rw [hstep]
    refine ih (execAss2 i s) (by rw [ehalt]; exact hh) (by rw [epc]; exact aligned_add4 _ hpc)
      (by rw [epc, emem]; exact hrest) (fun j hj => hs j (List.mem_cons_of_mem _ hj))

/-! ## 6. Views: congruence and read-after-write -/

theorem read64_congr {m₁ m₂ : UInt64 → UInt8} {a : UInt64}
    (h : ∀ k, k < 8 → m₁ (a + UInt64.ofNat k) = m₂ (a + UInt64.ofNat k)) :
    read64 m₁ a = read64 m₂ a := by
  simp only [read64, byteAt, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

theorem fetch32_congr {m₁ m₂ : UInt64 → UInt8} {a : UInt64}
    (h : ∀ k, k < 4 → m₁ (a + UInt64.ofNat k) = m₂ (a + UInt64.ofNat k)) :
    fetch32 m₁ a = fetch32 m₂ a := by
  simp only [fetch32, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem fp5Read_congr {σ₁ σ₂ : Fin 25 → UInt64} {e : Nat}
    (h : ∀ t, t < 5 → lane σ₁ (5 * e + t) = lane σ₂ (5 * e + t)) :
    fp5Read σ₁ e = fp5Read σ₂ e := by
  simp only [fp5Read, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem gfRead_congr {σ₁ σ₂ : Fin 25 → UInt64} {k : Nat}
    (h : ∀ t, t < 2 → lane σ₁ (2 * k + t) = lane σ₂ (2 * k + t)) :
    gfRead σ₁ k = gfRead σ₂ k := by
  simp only [gfRead, h 0 (by decide), h 1 (by decide)]

theorem kRead_congr {σ₁ σ₂ : Fin 25 → UInt64} (h : ∀ k, k < 25 → lane σ₁ k = lane σ₂ k) :
    kRead σ₁ = kRead σ₂ := by
  simp only [kRead, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide)]

theorem p24Read_congr {σ₁ σ₂ : Fin 25 → UInt64} (h : ∀ k, k < 24 → lane σ₁ k = lane σ₂ k) :
    p24Read σ₁ = p24Read σ₂ := by
  simp only [p24Read, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide)]

theorem p12Read_congr {σ₁ σ₂ : Fin 25 → UInt64} (h : ∀ k, k < 12 → lane σ₁ k = lane σ₂ k) :
    p12Read σ₁ = p12Read σ₂ := by
  simp only [p12Read, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]

theorem glOf_glTo (g : Goldilocks) : glOf (glTo g) = g := by
  apply Goldilocks.ext
  show (UInt64.ofNat g.val).toNat % goldilocksPrime = g.val
  rw [UInt64.toNat_ofNat_of_lt' (Goldilocks.val_lt_two_pow_64 g)]
  exact Nat.mod_eq_of_lt g.isLt

theorem lane_setLane_same (σ : Fin 25 → UInt64) {k : Nat} (hk : k < 25) (v : UInt64) :
    lane (setLane σ k v) k = v := by
  show (if h : k < 25 then (if (⟨k, h⟩ : Fin 25).val = k then v else σ ⟨k, h⟩) else 0) = v
  rw [dite_eq_left hk, ite_eq_left rfl]

theorem lane_setLane_other (σ : Fin 25 → UInt64) {k j : Nat} (hj : j ≠ k) (v : UInt64) :
    lane (setLane σ k v) j = lane σ j := by
  show (if h : j < 25 then (if (⟨j, h⟩ : Fin 25).val = k then v else σ ⟨j, h⟩) else 0) =
    (if h : j < 25 then σ ⟨j, h⟩ else 0)
  by_cases h : j < 25
  · rw [dite_eq_left h, dite_eq_left h, ite_eq_right hj]
  · rw [dite_eq_right h, dite_eq_right h]

theorem lane_fp5Write_same (σ : Fin 25 → UInt64) {d : Nat} (hd : d < 5) (q : QuinticGoldilocks)
    {t : Nat} (ht : t < 5) : lane (fp5Write σ d q) (5 * d + t) = fp5Limb q t := by
  have hlt : 5 * d + t < 25 := by omega
  show (if h : 5 * d + t < 25 then fp5Write σ d q ⟨5 * d + t, h⟩ else 0) = fp5Limb q t
  rw [dite_eq_left hlt]
  show (if (5 * d + t) / 5 = d then fp5Limb q ((5 * d + t) % 5) else σ ⟨5 * d + t, hlt⟩) =
    fp5Limb q t
  rw [ite_eq_left (by omega), show (5 * d + t) % 5 = t by omega]

theorem lane_fp5Write_other (σ : Fin 25 → UInt64) (d : Nat) (q : QuinticGoldilocks) {k : Nat}
    (hk : k / 5 ≠ d) : lane (fp5Write σ d q) k = lane σ k := by
  show (if h : k < 25 then fp5Write σ d q ⟨k, h⟩ else 0) = (if h : k < 25 then σ ⟨k, h⟩ else 0)
  by_cases h : k < 25
  · rw [dite_eq_left h, dite_eq_left h]
    show (if k / 5 = d then fp5Limb q (k % 5) else σ ⟨k, h⟩) = σ ⟨k, h⟩
    rw [ite_eq_right hk]
  · rw [dite_eq_right h, dite_eq_right h]

theorem fp5Write_in (σ : Fin 25 → UInt64) (d : Nat) (q : QuinticGoldilocks) (j : Fin 25)
    (hj : j.val / 5 = d) : fp5Write σ d q j = fp5Limb q (j.val % 5) := by
  show (if j.val / 5 = d then fp5Limb q (j.val % 5) else σ j) = _
  rw [ite_eq_left hj]

theorem fp5Write_out (σ : Fin 25 → UInt64) (d : Nat) (q : QuinticGoldilocks) (j : Fin 25)
    (hj : ¬ j.val / 5 = d) : fp5Write σ d q j = σ j := by
  show (if j.val / 5 = d then fp5Limb q (j.val % 5) else σ j) = _
  rw [ite_eq_right hj]

theorem gfWrite_in (σ : Fin 25 → UInt64) (k : Nat) (x : Math.Gf2Pow128) (j : Fin 25)
    (hj : j.val / 2 = k) : gfWrite σ k x j = gfLimb x (j.val % 2) := by
  show (if j.val / 2 = k then gfLimb x (j.val % 2) else σ j) = _
  rw [ite_eq_left hj]

theorem gfWrite_out (σ : Fin 25 → UInt64) (k : Nat) (x : Math.Gf2Pow128) (j : Fin 25)
    (hj : ¬ j.val / 2 = k) : gfWrite σ k x j = σ j := by
  show (if j.val / 2 = k then gfLimb x (j.val % 2) else σ j) = _
  rw [ite_eq_right hj]

/-- The limbs of a quintic element as canonical words. -/
theorem fp5Limb_eq (q : QuinticGoldilocks) :
    fp5Limb q 0 = glTo q.c0 ∧ fp5Limb q 1 = glTo q.c1 ∧ fp5Limb q 2 = glTo q.c2 ∧
    fp5Limb q 3 = glTo q.c3 ∧ fp5Limb q 4 = glTo q.c4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The Keccak view lists the lanes in order. -/
theorem kRead_eq (σ : Fin 25 → UInt64) :
    kRead σ =
      ⟨lane σ 0, lane σ 1, lane σ 2, lane σ 3, lane σ 4,
       lane σ 5, lane σ 6, lane σ 7, lane σ 8, lane σ 9,
       lane σ 10, lane σ 11, lane σ 12, lane σ 13, lane σ 14,
       lane σ 15, lane σ 16, lane σ 17, lane σ 18, lane σ 19,
       lane σ 20, lane σ 21, lane σ 22, lane σ 23, lane σ 24⟩ := by
  rfl

/-- The `ALUI` functions other than `ASRI` and `ROLI` as word operations. -/
theorem aluiEval_eq (a : UInt64) (imm : BitVec 16) :
    aluiEval .shli a imm = UInt64.ofBitVec (a.toBitVec <<< (imm.toNat % 64)) ∧
    aluiEval .shri a imm = UInt64.ofBitVec (a.toBitVec >>> (imm.toNat % 64)) ∧
    aluiEval .slk16 a imm = (a <<< 16) ||| zext imm ∧
    aluiEval .addi a imm = a + sext imm ∧ aluiEval .addiu a imm = a + zext imm ∧
    aluiEval .xori a imm = a ^^^ zext imm ∧ aluiEval .andi a imm = a &&& zext imm ∧
    aluiEval .ori a imm = a ||| zext imm :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A bank whose lanes are the fields of `K` reads as `K`. -/
theorem kRead_eq_mk (σ : Fin 25 → UInt64) (K : KState)
    (h0 : lane σ 0 = K.a0) (h1 : lane σ 1 = K.a1) (h2 : lane σ 2 = K.a2) (h3 : lane σ 3 = K.a3) (h4 : lane σ 4 = K.a4) (h5 : lane σ 5 = K.a5) (h6 : lane σ 6 = K.a6) (h7 : lane σ 7 = K.a7) (h8 : lane σ 8 = K.a8) (h9 : lane σ 9 = K.a9) (h10 : lane σ 10 = K.a10) (h11 : lane σ 11 = K.a11) (h12 : lane σ 12 = K.a12) (h13 : lane σ 13 = K.a13) (h14 : lane σ 14 = K.a14) (h15 : lane σ 15 = K.a15) (h16 : lane σ 16 = K.a16) (h17 : lane σ 17 = K.a17) (h18 : lane σ 18 = K.a18) (h19 : lane σ 19 = K.a19) (h20 : lane σ 20 = K.a20) (h21 : lane σ 21 = K.a21) (h22 : lane σ 22 = K.a22) (h23 : lane σ 23 = K.a23) (h24 : lane σ 24 = K.a24) :
    kRead σ = K := by
  cases K
  rw [kRead_eq, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24]

/-- A straight-line program advances `PC` by four per instruction and leaves memory and
    `halted` unchanged. -/
theorem foldl_straight_frame (prog : List Ass2Insn) :
    ∀ (s : Ass2State), (∀ i, i ∈ prog → i.isStraight = true) →
      (prog.foldl (fun t i => execAss2 i t) s).pc = s.pc + UInt64.ofNat (4 * prog.length) ∧
      (prog.foldl (fun t i => execAss2 i t) s).mem = s.mem ∧
      (prog.foldl (fun t i => execAss2 i t) s).halted = s.halted := by
  induction prog with
  | nil =>
    intro s _
    refine ⟨?_, rfl, rfl⟩
    show s.pc = s.pc + UInt64.ofNat 0
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']
    have := s.pc.toNat_lt
    omega
  | cons i rest ih =>
    intro s hs
    obtain ⟨epc, emem, ehalt⟩ := execAss2_straight (hs i (List.mem_cons_self ..)) s
    obtain ⟨ipc, imem, ihalt⟩ := ih (execAss2 i s) (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    refine ⟨?_, imem.trans emem, ihalt.trans ehalt⟩
    show (rest.foldl (fun t i => execAss2 i t) (execAss2 i s)).pc =
      s.pc + UInt64.ofNat (4 * (rest.length + 1))
    rw [ipc, epc]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat',
      UInt64.toNat_ofNat']
    have h4 : (4 : UInt64).toNat = 4 := by decide
    rw [h4]
    omega

/-- Reading back the quintic register just written. -/
theorem fp5Read_fp5Write_same (σ : Fin 25 → UInt64) {d : Nat} (hd : d < 5)
    (q : QuinticGoldilocks) : fp5Read (fp5Write σ d q) d = q := by
  unfold fp5Read
  rw [lane_fp5Write_same σ hd q (by decide : 0 < 5), lane_fp5Write_same σ hd q (by decide : 1 < 5),
    lane_fp5Write_same σ hd q (by decide : 2 < 5), lane_fp5Write_same σ hd q (by decide : 3 < 5),
    lane_fp5Write_same σ hd q (by decide : 4 < 5)]
  show (⟨glOf (glTo q.c0), glOf (glTo q.c1), glOf (glTo q.c2), glOf (glTo q.c3),
    glOf (glTo q.c4)⟩ : QuinticGoldilocks) = q
  rw [glOf_glTo, glOf_glTo, glOf_glTo, glOf_glTo, glOf_glTo]

/-- A write to one quintic register leaves the others unchanged. -/
theorem fp5Read_fp5Write_other (σ : Fin 25 → UInt64) {d e : Nat} (hne : e ≠ d)
    (q : QuinticGoldilocks) : fp5Read (fp5Write σ d q) e = fp5Read σ e :=
  fp5Read_congr fun t ht => lane_fp5Write_other σ d q (by omega)

/-! ## 7. The Goldilocks instructions as the spec's formulas -/

theorem glOf_val (x : UInt64) : (glOf x).val = x.toNat % goldilocksPrime := rfl

theorem glTo_toNat (g : Goldilocks) : (glTo g).toNat = g.val :=
  UInt64.toNat_ofNat_of_lt' (Goldilocks.val_lt_two_pow_64 g)

/-- `GL.MAC`: `((a mod p) * (b mod p) + (c mod p)) mod p`. -/
theorem glMac_toNat (a b c : UInt64) :
    (glMac a b c).toNat =
      (a.toNat % goldilocksPrime * (b.toNat % goldilocksPrime) + c.toNat % goldilocksPrime) %
        goldilocksPrime := by
  unfold glMac
  rw [glTo_toNat, Goldilocks.add_val, Goldilocks.mul_val, glOf_val, glOf_val, glOf_val,
    Nat.mod_add_mod]

/-- `GL.ADD`: `((a mod p) + (b mod p)) mod p`. -/
theorem glAdd_toNat (a b : UInt64) :
    (glAdd a b).toNat =
      (a.toNat % goldilocksPrime + b.toNat % goldilocksPrime) % goldilocksPrime := by
  unfold glAdd
  rw [glTo_toNat, Goldilocks.add_val, glOf_val, glOf_val]

/-- `GL.SUB`: `((a mod p) + p - (b mod p)) mod p`. -/
theorem glSub_toNat (a b : UInt64) :
    (glSub a b).toNat =
      (a.toNat % goldilocksPrime + goldilocksPrime - b.toNat % goldilocksPrime) %
        goldilocksPrime := by
  unfold glSub
  rw [glTo_toNat, Goldilocks.sub_val, glOf_val, glOf_val]

/-! ## 8. Architectural invariants -/

theorem csrApply_regs_zero (s : Ass2State) (c : CsrW) (v : UInt64) (h0 : s.regs 0 = 0) :
    (csrApply s c v).regs 0 = 0 := by
  cases c
  case zeroize =>
    show (if v.toNat % 2 = 1 then s.wipe else s).regs 0 = 0
    split
    · rfl
    · exact h0
  all_goals exact h0

theorem execAss2_regs_zero (i : Ass2Insn) (s : Ass2State) (h0 : s.regs 0 = 0) :
    (execAss2 i s).regs 0 = 0 := by
  have hset : ∀ (rd : Reg) (v : UInt64), (if (0 : Reg) = rd ∧ rd ≠ 0 then v else s.regs 0) = 0 := by
    intro rd v
    by_cases hc : (0 : Reg) = rd ∧ rd ≠ 0
    · exact absurd hc.1.symm hc.2
    · rw [ite_eq_right hc]; exact h0
  have htrap : ∀ c, (s.trap c).regs 0 = 0 := fun c => by rw [(trap_frame s c).1]; exact h0
  cases i
  case exc => unfold execAss2; dsimp only; split <;> exact h0
  case csrr rd a =>
    unfold execAss2; dsimp only
    split
    · exact hset _ _
    · exact htrap 1
  case csrw ra a =>
    unfold execAss2; dsimp only
    split
    · exact csrApply_regs_zero s _ _ h0
    · exact htrap 1
  case zeroize => rfl
  case ld64 => unfold execAss2; dsimp only; split <;> first | exact hset _ _ | exact htrap 4
  case st64 => unfold execAss2; dsimp only; split <;> first | exact h0 | exact htrap 4
  case sld64 => unfold execAss2; dsimp only; split <;> first | exact h0 | exact htrap 4
  case sst64 => unfold execAss2; dsimp only; split <;> first | exact h0 | exact htrap 4
  case jalr => unfold execAss2; dsimp only; split <;> first | exact hset _ _ | exact htrap 3
  all_goals first
    | exact hset _ _
    | exact h0

/-- **`R0` is always zero, and the data path cannot redirect `PC`.** A step preserves `R0 = 0`
    in the register file, a read of `R0` yields `0` in every state, and every instruction outside
    `SYS`, `BR`, `JAL` and `JALR` either continues at `PC + 4` or traps with `MisalignedMem`: no
    `LUT4`, `ALU`, `ALUI`, `IMM20`, `CMP`, `SEL`, `LOAD`, `STORE`, `SPG`, `GL64`, `FP5`, `GF128`
    or `PERM` instruction writes `PC`, whatever its destination field. -/
theorem ass2_r0_always_zero (s : Ass2State) :
    (s.regs 0 = 0 → (stepAss2 s).regs 0 = 0) ∧
    (stepAss2 s).rget 0 = 0 ∧
    (∀ i : Ass2Insn, i.isDataPath = true →
      (execAss2 i s).pc = s.pc + 4 ∨ execAss2 i s = s.trap 4) := by
  refine ⟨fun h0 => ?_, rfl, fun i hi => ?_⟩
  · have htrap : ∀ c, (s.trap c).regs 0 = 0 := fun c => by rw [(trap_frame s c).1]; exact h0
    unfold stepAss2
    split
    · exact h0
    · split
      · split
        · exact execAss2_regs_zero _ s h0
        · exact htrap 1
      · exact htrap 3
  · cases i
    case ld64 => unfold execAss2; dsimp only; split <;> first | exact Or.inl rfl | exact Or.inr rfl
    case st64 => unfold execAss2; dsimp only; split <;> first | exact Or.inl rfl | exact Or.inr rfl
    case sld64 => unfold execAss2; dsimp only; split <;> first | exact Or.inl rfl | exact Or.inr rfl
    case sst64 => unfold execAss2; dsimp only; split <;> first | exact Or.inl rfl | exact Or.inr rfl
    all_goals first
      | exact Or.inl rfl
      | exact absurd hi Bool.false_ne_true

/-- With `EXC_EN = 0` the all-zero word `EXC` continues at `PC + 4`, as the spec's formula
    says; with `EXC_EN = 1` it vectors to `EVEC` with `ECAUSE = 2` and `EPC = PC + 4`. -/
theorem ass2_exc_untaken_advances (s : Ass2State) :
    (s.excEn = false → (execAss2 .exc s).pc = s.pc + 4 ∧ (execAss2 .exc s).halted = s.halted) ∧
    (s.excEn = true → (execAss2 .exc s).pc = s.evec ∧ (execAss2 .exc s).ecause = 2 ∧
      (execAss2 .exc s).epc = s.pc + 4 ∧ (execAss2 .exc s).excEn = false) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold execAss2; dsimp only; rw [ite_eq_right (by rw [h]; decide)]; exact ⟨rfl, rfl⟩
  · unfold execAss2; dsimp only; rw [ite_eq_left h]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`ZEROIZE` wipes every register and lane in one step.** Both the `ZEROIZE` instruction and
    `CSRW ra, 0x41` with bit 0 of `R[ra]` set leave `R0..R15` and `S0..S24` zero. -/
theorem ass2_zeroize_wipes_all_secrets (s : Ass2State) :
    ((∀ r, (execAss2 .zeroize s).regs r = 0) ∧ (∀ k, (execAss2 .zeroize s).spg k = 0)) ∧
    (∀ ra : Reg, (s.rget ra).toNat % 2 = 1 →
      (∀ r, (execAss2 (.csrw ra 0x41#8) s).regs r = 0) ∧
      (∀ k, (execAss2 (.csrw ra 0x41#8) s).spg k = 0)) ∧
    (s.halted = false → s.pc.toNat % 4 = 0 → fetch32 s.mem s.pc = encodeAss2 .zeroize →
      (∀ r, (stepAss2 s).regs r = 0) ∧ (∀ k, (stepAss2 s).spg k = 0)) := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun ra hb => ?_, fun hh hpc hf => ?_⟩
  · have e : execAss2 (.csrw ra 0x41#8) s =
        Ass2State.retire
          (if (s.rget ra).toNat % 2 = 1 then s.wipe else s) 1 := rfl
    rw [e, ite_eq_left hb]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [stepAss2_eq_exec hh hpc (by rw [hf]; exact decodeAss2_encodeAss2 .zeroize trivial)]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **`FP5.MUL` is alias safe.** For quintic registers `ed, ea, eb < 5`, in any aliasing pattern
    (`ed = ea`, `ed = eb`, `ea = eb`), `E[ed]` after the instruction is the product of the
    pre-state `E[ea]` and `E[eb]`, and every other quintic register is unchanged. -/
theorem ass2_fp5_mul_self_alias_safe (s : Ass2State) (ed ea eb : Reg) (hd : ed.val < 5) :
    fp5Read (execAss2 (.fp5Mul ed ea eb) s).spg ed.val =
      QuinticGoldilocks.mul (fp5Read s.spg ea.val) (fp5Read s.spg eb.val) ∧
    fp5Read (execAss2 (.fp5Mul ed ed eb) s).spg ed.val =
      QuinticGoldilocks.mul (fp5Read s.spg ed.val) (fp5Read s.spg eb.val) ∧
    (∀ e : Nat, e ≠ ed.val →
      fp5Read (execAss2 (.fp5Mul ed ea eb) s).spg e = fp5Read s.spg e) :=
  ⟨fp5Read_fp5Write_same s.spg hd _, fp5Read_fp5Write_same s.spg hd _,
    fun _ hne => fp5Read_fp5Write_other s.spg hne _⟩

/-- **`JALR rd, rd, simm16` is alias safe.** The target comes from the pre-state `R[rd]` and the
    link register receives `PC + 4`. -/
theorem ass2_jalr_self_alias_safe (s : Ass2State) (rd : Reg) (off : BitVec 16)
    (hal : (s.rget rd + (sext off <<< (2 : UInt64))).toNat % 4 = 0) :
    (execAss2 (.jalr rd rd off) s).pc = (s.rget rd + (sext off <<< (2 : UInt64))) &&& ~~~3 ∧
    (rd ≠ 0 → (execAss2 (.jalr rd rd off) s).rget rd = s.pc + 4) := by
  have e : execAss2 (.jalr rd rd off) s =
      (s.setReg rd (s.pc + 4)).retireTo ((s.rget rd + (sext off <<< (2 : UInt64))) &&& ~~~3) 1 := by
    unfold execAss2; dsimp only; rw [ite_eq_left hal]; rfl
  rw [e]
  refine ⟨rfl, fun hrd => ?_⟩
  show (if rd = 0 then 0 else (if rd = rd ∧ rd ≠ 0 then s.pc + 4 else s.regs rd)) = s.pc + 4
  rw [ite_eq_right hrd, ite_eq_left ⟨rfl, hrd⟩]

/-! ### Loading a 64-bit constant -/

/-- `MOVZ20` then three `SLK16`: the four 16-bit chunks of `x`, most significant first. -/
@[expose] def loadImm64 (rd : Reg) (x : UInt64) : List Ass2Insn :=
  [.movz20 rd (BitVec.ofNat 20 (x.toNat / 281474976710656)),
   .alui .slk16 rd rd (BitVec.ofNat 16 (x.toNat / 4294967296)),
   .alui .slk16 rd rd (BitVec.ofNat 16 (x.toNat / 65536)),
   .alui .slk16 rd rd (BitVec.ofNat 16 x.toNat)]

theorem slk16_toNat (a : UInt64) (imm : BitVec 16) :
    (aluiEval .slk16 a imm).toNat = (a.toNat * 65536 + imm.toNat) % 18446744073709551616 := by
  show ((a <<< 16) ||| zext imm).toNat = _
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h16 : (16 : UInt64).toNat % 64 = 16 := by decide
  have hz : (zext imm).toNat = imm.toNat := by
    show (BitVec.setWidth 64 imm).toNat = imm.toNat
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans imm.isLt (by decide))
  rw [h16, hz, Nat.shiftLeft_eq]
  have hi := imm.isLt
  have hsh : a.toNat * 2 ^ 16 % 2 ^ 64 = (a.toNat % 2 ^ 48) <<< 16 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [hsh, ← Nat.shiftLeft_add_eq_or_of_lt hi, Nat.shiftLeft_eq]
  omega

/-- **Four steps load any 64-bit constant.** With `loadImm64 rd x` loaded at `PC`, four steps
    leave `x` in `R[rd]`, memory unchanged and `PC` advanced by 16; none of the four instructions
    makes a memory access. -/
theorem ass2_slk16_four_step_loads_any_u64 (x : UInt64) (rd : Reg) (hrd : rd ≠ 0)
    (s : Ass2State) (hh : s.halted = false) (hpc : s.pc.toNat % 4 = 0)
    (hl : LoadedAt s.mem s.pc (loadImm64 rd x)) :
    (runAss2 4 s).rget rd = x ∧ (runAss2 4 s).mem = s.mem ∧
    (runAss2 4 s).pc = s.pc + 4 + 4 + 4 + 4 ∧
    (∀ i, i ∈ loadImm64 rd x → ∀ t, effAddr i t = none) := by
  have hmem : ∀ i, i ∈ loadImm64 rd x → i.WellFormed ∧ i.isStraight = true ∧
      ∀ t, effAddr i t = none := by
    intro i hi
    simp only [loadImm64, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact ⟨trivial, rfl, fun _ => rfl⟩
  have hrun := runAss2_straight (loadImm64 rd x) s hh hpc hl (fun i hi => ⟨(hmem i hi).1, (hmem i hi).2.1⟩)
  have hrun' : runAss2 4 s = (loadImm64 rd x).foldl (fun t i => execAss2 i t) s := hrun
  refine ⟨?_, by rw [hrun']; rfl, by rw [hrun']; rfl, fun i hi => (hmem i hi).2.2⟩
  rw [hrun']
  have hval : ((loadImm64 rd x).foldl (fun t i => execAss2 i t) s).rget rd =
      aluiEval .slk16 (aluiEval .slk16 (aluiEval .slk16
        (zext (BitVec.ofNat 20 (x.toNat / 281474976710656)))
        (BitVec.ofNat 16 (x.toNat / 4294967296))) (BitVec.ofNat 16 (x.toNat / 65536)))
        (BitVec.ofNat 16 x.toNat) := by
    show (if rd = 0 then 0 else (if rd = rd ∧ rd ≠ 0 then
      aluiEval .slk16 (if rd = 0 then 0 else (if rd = rd ∧ rd ≠ 0 then
        aluiEval .slk16 (if rd = 0 then 0 else (if rd = rd ∧ rd ≠ 0 then
          aluiEval .slk16 (if rd = 0 then 0 else (if rd = rd ∧ rd ≠ 0 then
            zext (BitVec.ofNat 20 (x.toNat / 281474976710656)) else _))
            (BitVec.ofNat 16 (x.toNat / 4294967296)) else _))
          (BitVec.ofNat 16 (x.toNat / 65536)) else _))
        (BitVec.ofNat 16 x.toNat) else _)) = _
    have hc : True ∧ rd ≠ 0 := ⟨trivial, hrd⟩
    simp only [ite_eq_right hrd, ite_eq_left hc]
  rw [hval]
  apply UInt64.toNat_inj.mp
  rw [slk16_toNat, slk16_toNat, slk16_toNat]
  have hz : (zext (BitVec.ofNat 20 (x.toNat / 281474976710656))).toNat =
      x.toNat / 281474976710656 % 1048576 := by
    show (BitVec.setWidth 64 (BitVec.ofNat 20 (x.toNat / 281474976710656))).toNat = _
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [hz, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.toNat_lt
  omega

/-! ## 9. Known answers from the reference model

Values computed by `hardware/ass2/sim/ass2_model.py`, the model the RTL is co-simulated against
(`tools/gen_ass2_kats.py` regenerates this section). -/

/-- `ALU` on three operand pairs, including shift amounts `≥ 64`. -/
theorem kat_alu :
    aluEval .add 0x8123456789ABCDEF 0x0000000000000007 = 0x8123456789ABCDF6 ∧
    aluEval .sub 0x8123456789ABCDEF 0x0000000000000007 = 0x8123456789ABCDE8 ∧
    aluEval .shl 0x8123456789ABCDEF 0x0000000000000007 = 0x91A2B3C4D5E6F780 ∧
    aluEval .shr 0x8123456789ABCDEF 0x0000000000000007 = 0x0102468ACF13579B ∧
    aluEval .asr 0x8123456789ABCDEF 0x0000000000000007 = 0xFF02468ACF13579B ∧
    aluEval .rol 0x8123456789ABCDEF 0x0000000000000007 = 0x91A2B3C4D5E6F7C0 ∧
    aluEval .ror 0x8123456789ABCDEF 0x0000000000000007 = 0xDF02468ACF13579B ∧
    aluEval .mul64 0x8123456789ABCDEF 0x0000000000000007 = 0x87F6E5D4C3B2A189 ∧
    aluEval .mulhu64 0x8123456789ABCDEF 0x0000000000000007 = 0x0000000000000003 ∧
    aluEval .add 0xFEDCBA9876543210 0x00000000000000C5 = 0xFEDCBA98765432D5 ∧
    aluEval .sub 0xFEDCBA9876543210 0x00000000000000C5 = 0xFEDCBA987654314B ∧
    aluEval .shl 0xFEDCBA9876543210 0x00000000000000C5 = 0x0000000000000000 ∧
    aluEval .shr 0xFEDCBA9876543210 0x00000000000000C5 = 0x0000000000000000 ∧
    aluEval .asr 0xFEDCBA9876543210 0x00000000000000C5 = 0xFFFFFFFFFFFFFFFF ∧
    aluEval .rol 0xFEDCBA9876543210 0x00000000000000C5 = 0xDB97530ECA86421F ∧
    aluEval .ror 0xFEDCBA9876543210 0x00000000000000C5 = 0x87F6E5D4C3B2A190 ∧
    aluEval .mul64 0xFEDCBA9876543210 0x00000000000000C5 = 0x1FDB97530ECA8650 ∧
    aluEval .mulhu64 0xFEDCBA9876543210 0x00000000000000C5 = 0x00000000000000C4 ∧
    aluEval .add 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x7FFFFFFFFFFFFFFE ∧
    aluEval .sub 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x8000000000000000 ∧
    aluEval .shl 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x0000000000000000 ∧
    aluEval .shr 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x0000000000000000 ∧
    aluEval .asr 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x0000000000000000 ∧
    aluEval .rol 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0xBFFFFFFFFFFFFFFF ∧
    aluEval .ror 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0xFFFFFFFFFFFFFFFE ∧
    aluEval .mul64 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x8000000000000001 ∧
    aluEval .mulhu64 0x7FFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = 0x7FFFFFFFFFFFFFFE := by
  decide

/-- `ALUI`, with a negative 16-bit immediate for the arithmetic and logic functions. -/
theorem kat_alui :
    aluiEval .addi 0x8123456789ABCDEF 0x8001#16 = 0x8123456789AB4DF0 ∧
    aluiEval .addiu 0x8123456789ABCDEF 0x8001#16 = 0x8123456789AC4DF0 ∧
    aluiEval .xori 0x8123456789ABCDEF 0x8001#16 = 0x8123456789AB4DEE ∧
    aluiEval .andi 0x8123456789ABCDEF 0x8001#16 = 0x0000000000008001 ∧
    aluiEval .ori 0x8123456789ABCDEF 0x8001#16 = 0x8123456789ABCDEF ∧
    aluiEval .shli 0x8123456789ABCDEF 0x000D#16 = 0x68ACF13579BDE000 ∧
    aluiEval .shri 0x8123456789ABCDEF 0x000D#16 = 0x0004091A2B3C4D5E ∧
    aluiEval .asri 0x8123456789ABCDEF 0x000D#16 = 0xFFFC091A2B3C4D5E ∧
    aluiEval .roli 0x8123456789ABCDEF 0x000D#16 = 0x68ACF13579BDF024 ∧
    aluiEval .slk16 0x8123456789ABCDEF 0x8001#16 = 0x456789ABCDEF8001 ∧
    aluiEval .roli 0x8123456789ABCDEF 0x0000#16 = 0x8123456789ABCDEF ∧
    aluiEval .addi 0x00000000FFFF7FFF 0x8001#16 = 0x00000000FFFF0000 ∧
    aluiEval .addiu 0x00000000FFFF7FFF 0x8001#16 = 0x0000000100000000 ∧
    aluiEval .xori 0x00000000FFFF7FFF 0x8001#16 = 0x00000000FFFFFFFE ∧
    aluiEval .andi 0x00000000FFFF7FFF 0x8001#16 = 0x0000000000000001 ∧
    aluiEval .ori 0x00000000FFFF7FFF 0x8001#16 = 0x00000000FFFFFFFF ∧
    aluiEval .shli 0x00000000FFFF7FFF 0x000D#16 = 0x00001FFFEFFFE000 ∧
    aluiEval .shri 0x00000000FFFF7FFF 0x000D#16 = 0x000000000007FFFB ∧
    aluiEval .asri 0x00000000FFFF7FFF 0x000D#16 = 0x000000000007FFFB ∧
    aluiEval .roli 0x00000000FFFF7FFF 0x000D#16 = 0x00001FFFEFFFE000 ∧
    aluiEval .slk16 0x00000000FFFF7FFF 0x8001#16 = 0x0000FFFF7FFF8001 ∧
    aluiEval .roli 0x00000000FFFF7FFF 0x0000#16 = 0x00000000FFFF7FFF := by
  decide

/-- `MOVS20` and `MOVZ20` extension. -/
theorem kat_imm20 :
    (sext (0x80000#20) : UInt64) = 0xFFFFFFFFFFF80000 ∧
    (sext (0x7FFFF#20) : UInt64) = 0x000000000007FFFF ∧
    (sext (0xFFFFF#20) : UInt64) = 0xFFFFFFFFFFFFFFFF ∧
    (zext (0x80000#20) : UInt64) = 0x0000000000080000 ∧
    (zext (0xFFFFF#20) : UInt64) = 0x00000000000FFFFF := by
  decide

/-- `CMP`: all 16 predicates on three operand pairs. -/
theorem kat_cmp :
    cmpEval 0 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 1 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 2 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 3 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 4 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 5 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 6 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 7 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 8 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 9 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 10 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 11 0x8000000000000000 0x0000000000000001 = 0 ∧
    cmpEval 12 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 13 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 14 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 15 0x8000000000000000 0x0000000000000001 = 1 ∧
    cmpEval 0 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 1 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 2 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 3 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 4 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 5 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 6 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 7 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 8 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 9 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 10 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 11 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 12 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 13 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 14 0x0000000000000005 0x0000000000000005 = 1 ∧
    cmpEval 15 0x0000000000000005 0x0000000000000005 = 0 ∧
    cmpEval 0 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 1 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 2 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 3 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 4 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 5 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 6 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 7 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 8 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 9 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 10 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 11 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 12 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 13 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 1 ∧
    cmpEval 14 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 ∧
    cmpEval 15 0x0000000000000003 0xFFFFFFFFFFFFFFFE = 0 := by
  decide

/-- `LUT4`: all 16 truth tables. -/
theorem kat_lut4 :
    lut4Eval 0 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x0000000000000000 ∧
    lut4Eval 1 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x0303030303030303 ∧
    lut4Eval 2 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x0C0C0C0C0C0C0C0C ∧
    lut4Eval 3 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x0F0F0F0F0F0F0F0F ∧
    lut4Eval 4 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x3030303030303030 ∧
    lut4Eval 5 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x3333333333333333 ∧
    lut4Eval 6 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x3C3C3C3C3C3C3C3C ∧
    lut4Eval 7 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0x3F3F3F3F3F3F3F3F ∧
    lut4Eval 8 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xC0C0C0C0C0C0C0C0 ∧
    lut4Eval 9 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xC3C3C3C3C3C3C3C3 ∧
    lut4Eval 10 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xCCCCCCCCCCCCCCCC ∧
    lut4Eval 11 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xCFCFCFCFCFCFCFCF ∧
    lut4Eval 12 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xF0F0F0F0F0F0F0F0 ∧
    lut4Eval 13 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xF3F3F3F3F3F3F3F3 ∧
    lut4Eval 14 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xFCFCFCFCFCFCFCFC ∧
    lut4Eval 15 0xF0F0F0F0F0F0F0F0 0xCCCCCCCCCCCCCCCC = 0xFFFFFFFFFFFFFFFF := by
  decide

/-- `BEXTU`, `BEXTS` and `BSWAP64`. -/
theorem kat_bext_bswap :
    bextuEval 0x1122334455667788 0 0 = 0x1122334455667788 ∧
    bextsEval 0x1122334455667788 0 0 = 0x1122334455667788 ∧
    bextuEval 0x1122334455667788 1 1 = 0x0000000000000077 ∧
    bextsEval 0x1122334455667788 1 1 = 0x0000000000000077 ∧
    bextuEval 0x1122334455667788 3 2 = 0x0000000000004455 ∧
    bextsEval 0x1122334455667788 3 2 = 0x0000000000004455 ∧
    bextuEval 0x1122334455667788 7 1 = 0x0000000000000011 ∧
    bextsEval 0x1122334455667788 7 1 = 0x0000000000000011 ∧
    bextuEval 0x1122334455667788 2 5 = 0x0000002233445566 ∧
    bextsEval 0x1122334455667788 2 5 = 0x0000002233445566 ∧
    bextuEval 0x1122334455667788 5 3 = 0x0000000000112233 ∧
    bextsEval 0x1122334455667788 5 3 = 0x0000000000112233 ∧
    bextuEval 0x1122334455667788 0 7 = 0x0022334455667788 ∧
    bextsEval 0x1122334455667788 0 7 = 0x0022334455667788 ∧
    bswap64Eval 0x1122334455667788 = 0x8877665544332211 ∧
    bextuEval 0x80FF807F81F0E0C3 0 0 = 0x80FF807F81F0E0C3 ∧
    bextsEval 0x80FF807F81F0E0C3 0 0 = 0x80FF807F81F0E0C3 ∧
    bextuEval 0x80FF807F81F0E0C3 1 1 = 0x00000000000000E0 ∧
    bextsEval 0x80FF807F81F0E0C3 1 1 = 0xFFFFFFFFFFFFFFE0 ∧
    bextuEval 0x80FF807F81F0E0C3 3 2 = 0x0000000000007F81 ∧
    bextsEval 0x80FF807F81F0E0C3 3 2 = 0x0000000000007F81 ∧
    bextuEval 0x80FF807F81F0E0C3 7 1 = 0x0000000000000080 ∧
    bextsEval 0x80FF807F81F0E0C3 7 1 = 0xFFFFFFFFFFFFFF80 ∧
    bextuEval 0x80FF807F81F0E0C3 2 5 = 0x000000FF807F81F0 ∧
    bextsEval 0x80FF807F81F0E0C3 2 5 = 0xFFFFFFFF807F81F0 ∧
    bextuEval 0x80FF807F81F0E0C3 5 3 = 0x000000000080FF80 ∧
    bextsEval 0x80FF807F81F0E0C3 5 3 = 0xFFFFFFFFFF80FF80 ∧
    bextuEval 0x80FF807F81F0E0C3 0 7 = 0x00FF807F81F0E0C3 ∧
    bextsEval 0x80FF807F81F0E0C3 0 7 = 0xFFFF807F81F0E0C3 ∧
    bswap64Eval 0x80FF807F81F0E0C3 = 0xC3E0F0817F80FF80 := by
  decide

/-- `GL.MAC`, `GL.ADD`, `GL.SUB`, `GL.SBOX7` on non-canonical inputs (`≥ p`). -/
theorem kat_gl :
    glMac 0xFFFFFFFFFFFFFFFF 0xFFFFFFFF00000002 0x123456789ABCDEF0 = 0x123456799ABCDEEE ∧
    glAdd 0xFFFFFFFFFFFFFFFF 0xFFFFFFFF00000002 = 0x00000000FFFFFFFF ∧
    glSub 0xFFFFFFFFFFFFFFFF 0xFFFFFFFF00000002 = 0x00000000FFFFFFFD ∧
    glSbox7 0xFFFFFFFFFFFFFFFF = 0xFFFFFFE400000037 ∧
    glMac 0x0123456789ABCDEF 0xFEDCBA9876543210 0xFFFFFFFF00000001 = 0xCFAEAFD136C7BBAE ∧
    glAdd 0x0123456789ABCDEF 0xFEDCBA9876543210 = 0x00000000FFFFFFFE ∧
    glSub 0x0123456789ABCDEF 0xFEDCBA9876543210 = 0x02468ACE13579BE0 ∧
    glSbox7 0x0123456789ABCDEF = 0x197248EA2E971FEE := by
  decide +kernel

/-- The bank `S[k] = k * 0x9E3779B97F4A7C15 + 0x0123456789ABCDEF` of the bank vectors. -/
def katBank : Fin 25 → UInt64 := fun k => UInt64.ofNat k.val * 0x9E3779B97F4A7C15 + 0x0123456789ABCDEF

/-- `FP5.MUL E1, E1, E3` on `katBank`: the five limbs written to `S[5..9]`. -/
theorem kat_fp5_mul :
    fp5Limb (QuinticGoldilocks.mul (fp5Read katBank 1) (fp5Read katBank 3)) 0 = 0x146016628D2A501D ∧
    fp5Limb (QuinticGoldilocks.mul (fp5Read katBank 1) (fp5Read katBank 3)) 1 = 0x310713BE9F65AA03 ∧
    fp5Limb (QuinticGoldilocks.mul (fp5Read katBank 1) (fp5Read katBank 3)) 2 = 0x6485A9BD040450D1 ∧
    fp5Limb (QuinticGoldilocks.mul (fp5Read katBank 1) (fp5Read katBank 3)) 3 = 0x78A2FB10B2E02A33 ∧
    fp5Limb (QuinticGoldilocks.mul (fp5Read katBank 1) (fp5Read katBank 3)) 4 = 0x9DD24F6E4B397757 := by
  decide +kernel

/-- `FP5.ADD E1, E1, E3` on `katBank`: the five limbs written to `S[5..9]`. -/
theorem kat_fp5_add :
    fp5Limb (QuinticGoldilocks.add (fp5Read katBank 1) (fp5Read katBank 3)) 0 = 0x5E9C0D4D05294D82 ∧
    fp5Limb (QuinticGoldilocks.add (fp5Read katBank 1) (fp5Read katBank 3)) 1 = 0x9B0B00C103BE45AB ∧
    fp5Limb (QuinticGoldilocks.add (fp5Read katBank 1) (fp5Read katBank 3)) 2 = 0xD779F43302533DD6 ∧
    fp5Limb (QuinticGoldilocks.add (fp5Read katBank 1) (fp5Read katBank 3)) 3 = 0x13E8E7A700E835FF ∧
    fp5Limb (QuinticGoldilocks.add (fp5Read katBank 1) (fp5Read katBank 3)) 4 = 0x5057DB19FF7D2E29 := by
  decide +kernel

/-- `FP5.SUB E1, E1, E3` on `katBank`: the five limbs written to `S[5..9]`. -/
theorem kat_fp5_sub :
    fp5Limb (QuinticGoldilocks.sub (fp5Read katBank 1) (fp5Read katBank 3)) 0 = 0xD1D53EC00717272F ∧
    fp5Limb (QuinticGoldilocks.sub (fp5Read katBank 1) (fp5Read katBank 3)) 1 = 0xD1D53EC00717272F ∧
    fp5Limb (QuinticGoldilocks.sub (fp5Read katBank 1) (fp5Read katBank 3)) 2 = 0xD1D53EC00717272F ∧
    fp5Limb (QuinticGoldilocks.sub (fp5Read katBank 1) (fp5Read katBank 3)) 3 = 0xD1D53EC10717272E ∧
    fp5Limb (QuinticGoldilocks.sub (fp5Read katBank 1) (fp5Read katBank 3)) 4 = 0xD1D53EC00717272F := by
  decide +kernel

/-- `KECCAK.F1600 12` on `katBank`, lane by lane. -/
theorem kat_keccak_12 :
    (keccakRounds 12 (kRead katBank)).a0 = 0x2C5C9F7033CA6B25 ∧
    (keccakRounds 12 (kRead katBank)).a1 = 0x7BE172CD5A77DB71 ∧
    (keccakRounds 12 (kRead katBank)).a2 = 0x77C9A199B800B99D ∧
    (keccakRounds 12 (kRead katBank)).a3 = 0xAB0AAF0209128880 ∧
    (keccakRounds 12 (kRead katBank)).a4 = 0x3163DB5FDDE89FEC ∧
    (keccakRounds 12 (kRead katBank)).a5 = 0x5974AA5D958FF371 ∧
    (keccakRounds 12 (kRead katBank)).a6 = 0x20D065622F6F1990 ∧
    (keccakRounds 12 (kRead katBank)).a7 = 0x6EC53782B9DF5B2A ∧
    (keccakRounds 12 (kRead katBank)).a8 = 0x0C4154D4808A2D0A ∧
    (keccakRounds 12 (kRead katBank)).a9 = 0xA85EFC0A465E99C8 ∧
    (keccakRounds 12 (kRead katBank)).a10 = 0xEB4D829BEBFD9EFD ∧
    (keccakRounds 12 (kRead katBank)).a11 = 0xA25FB7927259AB0E ∧
    (keccakRounds 12 (kRead katBank)).a12 = 0x3EDCACAC41F286A5 ∧
    (keccakRounds 12 (kRead katBank)).a13 = 0x2A80B379014930F6 ∧
    (keccakRounds 12 (kRead katBank)).a14 = 0x6A55AAB4238ECE51 ∧
    (keccakRounds 12 (kRead katBank)).a15 = 0x15B2126407209991 ∧
    (keccakRounds 12 (kRead katBank)).a16 = 0xA988F65B62852862 ∧
    (keccakRounds 12 (kRead katBank)).a17 = 0xABC6873B91124D71 ∧
    (keccakRounds 12 (kRead katBank)).a18 = 0x7146CCCA64FCB894 ∧
    (keccakRounds 12 (kRead katBank)).a19 = 0x23222C460322EE41 ∧
    (keccakRounds 12 (kRead katBank)).a20 = 0x1E0FED496C1CE039 ∧
    (keccakRounds 12 (kRead katBank)).a21 = 0x0F8C9EA7D922DC8E ∧
    (keccakRounds 12 (kRead katBank)).a22 = 0x5A94B2BF5AA06548 ∧
    (keccakRounds 12 (kRead katBank)).a23 = 0xF02CE920D76402C4 ∧
    (keccakRounds 12 (kRead katBank)).a24 = 0x325610B4D2FAB51B := by
  unfold keccakRounds
  rw [keccakRoundConstants_eq]
  decide +kernel

/-- `KECCAK.F1600 24` on `katBank`, lane by lane. -/
theorem kat_keccak_24 :
    (keccakRounds 24 (kRead katBank)).a0 = 0xAB83CCFF5DD9F1BF ∧
    (keccakRounds 24 (kRead katBank)).a1 = 0xEF6C00611A4677DD ∧
    (keccakRounds 24 (kRead katBank)).a2 = 0x3FC3BB55E64B0632 ∧
    (keccakRounds 24 (kRead katBank)).a3 = 0x16C209888F71E717 ∧
    (keccakRounds 24 (kRead katBank)).a4 = 0x291CD37C10C775F9 ∧
    (keccakRounds 24 (kRead katBank)).a5 = 0xD69868AC7A19300C ∧
    (keccakRounds 24 (kRead katBank)).a6 = 0x6B5292EAB34499EC ∧
    (keccakRounds 24 (kRead katBank)).a7 = 0x37CB83177141C74D ∧
    (keccakRounds 24 (kRead katBank)).a8 = 0x5B1C5124ACEDA1D2 ∧
    (keccakRounds 24 (kRead katBank)).a9 = 0x9F65593FF2F66241 ∧
    (keccakRounds 24 (kRead katBank)).a10 = 0xDB8CE9FD20A9CB15 ∧
    (keccakRounds 24 (kRead katBank)).a11 = 0x33521D38EB6C14EB ∧
    (keccakRounds 24 (kRead katBank)).a12 = 0x4DFB68B2C9516E63 ∧
    (keccakRounds 24 (kRead katBank)).a13 = 0x9EF1CC149E27AFA6 ∧
    (keccakRounds 24 (kRead katBank)).a14 = 0xAFA828C679EEF796 ∧
    (keccakRounds 24 (kRead katBank)).a15 = 0x93AD6E7F009F765E ∧
    (keccakRounds 24 (kRead katBank)).a16 = 0x4012EA7D3795DB71 ∧
    (keccakRounds 24 (kRead katBank)).a17 = 0xDA8F346BB27B1086 ∧
    (keccakRounds 24 (kRead katBank)).a18 = 0x49EC40E6D76C6A0F ∧
    (keccakRounds 24 (kRead katBank)).a19 = 0x93B029F45E4EDC74 ∧
    (keccakRounds 24 (kRead katBank)).a20 = 0x26E41FDCA167265F ∧
    (keccakRounds 24 (kRead katBank)).a21 = 0x4DFEDAE72480A90D ∧
    (keccakRounds 24 (kRead katBank)).a22 = 0xE3E9D5FAA8032FA3 ∧
    (keccakRounds 24 (kRead katBank)).a23 = 0x8B5B8E8606B34C6A ∧
    (keccakRounds 24 (kRead katBank)).a24 = 0x44779EB8EC1FDD06 := by
  unfold keccakRounds
  rw [keccakRoundConstants_eq]
  decide +kernel

/-- RFC 9861: the first eight output bytes of `TurboSHAKE256(M = "", D = 0x1F)` are
    `36 7a 32 9d af ea 87 1c`. -/
theorem kat_turboshake256_empty :
    (keccakRounds 12 ⟨0x1F, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000,
      0, 0, 0, 0, 0, 0, 0, 0⟩).a0 = 0x1C87EAAF9D327A36 := by
  unfold keccakRounds
  rw [keccakRoundConstants_eq]
  decide +kernel

#verify_constructive
  Qsag.Ass2.stepAss2InRam_full
  Qsag.Ass2.keccakRounds_24
  Qsag.Ass2.trap_frame
  Qsag.Ass2.stepAss2_eq_exec
  Qsag.Ass2.stepAss2_halted
  Qsag.Ass2.currentInsn_of_fetch
  Qsag.Ass2.stepAss2_of_currentInsn_some
  Qsag.Ass2.stepAss2_of_currentInsn_none
  Qsag.Ass2.fp5Write_in
  Qsag.Ass2.fp5Write_out
  Qsag.Ass2.gfWrite_in
  Qsag.Ass2.gfWrite_out
  Qsag.Ass2.fp5Limb_eq
  Qsag.Ass2.kRead_eq
  Qsag.Ass2.kRead_eq_mk
  Qsag.Ass2.foldl_straight_frame
  Qsag.Ass2.aluiEval_eq
  Qsag.Ass2.csrApply_regs_zero
  Qsag.Ass2.aligned_add4
  Qsag.Ass2.execAss2_straight
  Qsag.Ass2.runAss2_straight
  Qsag.Ass2.read64_congr
  Qsag.Ass2.fetch32_congr
  Qsag.Ass2.fp5Read_congr
  Qsag.Ass2.gfRead_congr
  Qsag.Ass2.kRead_congr
  Qsag.Ass2.p24Read_congr
  Qsag.Ass2.p12Read_congr
  Qsag.Ass2.glOf_glTo
  Qsag.Ass2.lane_setLane_same
  Qsag.Ass2.lane_setLane_other
  Qsag.Ass2.fp5Read_fp5Write_same
  Qsag.Ass2.fp5Read_fp5Write_other
  Qsag.Ass2.glMac_toNat
  Qsag.Ass2.glAdd_toNat
  Qsag.Ass2.glSub_toNat
  Qsag.Ass2.execAss2_regs_zero
  Qsag.Ass2.ass2_r0_always_zero
  Qsag.Ass2.ass2_exc_untaken_advances
  Qsag.Ass2.ass2_zeroize_wipes_all_secrets
  Qsag.Ass2.ass2_fp5_mul_self_alias_safe
  Qsag.Ass2.ass2_jalr_self_alias_safe
  Qsag.Ass2.slk16_toNat
  Qsag.Ass2.ass2_slk16_four_step_loads_any_u64
  Qsag.Ass2.kat_alu
  Qsag.Ass2.kat_alui
  Qsag.Ass2.kat_imm20
  Qsag.Ass2.kat_cmp
  Qsag.Ass2.kat_lut4
  Qsag.Ass2.kat_bext_bswap
  Qsag.Ass2.kat_gl
  Qsag.Ass2.kat_fp5_mul
  Qsag.Ass2.kat_fp5_add
  Qsag.Ass2.kat_fp5_sub
  Qsag.Ass2.kat_keccak_12
  Qsag.Ass2.kat_keccak_24
  Qsag.Ass2.kat_turboshake256_empty

end Qsag.Ass2
