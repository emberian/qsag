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

