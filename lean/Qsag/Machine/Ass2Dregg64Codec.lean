module
/-
# Qsag.Machine.Ass2Dregg64Codec — `ASS2 / Dregg-64` instruction syntax and 32-bit codec

The instruction AST of the fixed-width 32-bit little-endian `ASS2 / Dregg-64` enclave ISA
(`ass2-dregg64-canonical-spec.md` §2), its well-formedness predicate, the encoder and the decoder,
and the two round-trip theorems that make the codec a bijection between well-formed instructions
and the accepted 32-bit words.

Word layout (bit 0 is the least significant):

    [31:28] op   [27:20] imm8   [19:16] sub   [15:12] rc   [11:8] rb   [7:4] ra   [3:0] rd

with the overlays `imm16 = [27:12]`, `imm20 = [27:8]`, `imm24 = [27:4]` and, for major opcode
`0xC`, `off8 = [27:20]`, `sidx = [19:12]`, `sub = [11:8]`.

* `Ass2Insn`: one constructor per mnemonic; the ALU, ALUI and BR families carry their sub-operation.
* `Ass2Insn.WellFormed`: the range conditions that the field types do not already enforce.
* `encodeAss2`, `decodeAss2`: the codec. `decodeAss2` rejects every word with a reserved
  sub-opcode or a nonzero reserved field.
* `decodeAss2_encodeAss2`, `encodeAss2_decodeAss2`: the round trips. Together they determine
  `decodeAss2` from `encodeAss2` and `WellFormed` (`decodeAss2_eq_some_iff`).
* `cycleCost`: the fixed latency of each instruction, a function of the instruction word alone.
-/

public import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Ass2

set_option autoImplicit false

/-- A 4-bit register (or 4-bit field) index. -/
abbrev Reg := Fin 16

/-- The 4-bit field with value `n mod 16`. -/
abbrev reg (n : Nat) : Reg := ⟨n % 16, Nat.mod_lt n (by decide)⟩

theorem reg_val (r : Reg) : reg r.val = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)

theorem bv_ofNat_toNat {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

/-! ## 1. Sub-operations -/

/-- `0x2 ALU` sub-operations (`sub` field). -/
inductive AluOp where
  | add | sub | shl | shr | asr | rol | ror | mul64 | mulhu64
  deriving DecidableEq, Repr

/-- `0x3 ALUI` functions (`fn4 = rb` field). -/
inductive AluiOp where
  | addi | addiu | xori | andi | ori | shli | shri | asri | roli | slk16
  deriving DecidableEq, Repr

/-- `0x9 BR` conditions (`bop4 = ra` field). -/
inductive BrOp where
  | beqz | bnez | bltz | bgez
  deriving DecidableEq, Repr

@[expose] def AluOp.code : AluOp → Nat
  | .add => 0 | .sub => 1 | .shl => 2 | .shr => 3 | .asr => 4
  | .rol => 5 | .ror => 6 | .mul64 => 7 | .mulhu64 => 8

@[expose] def AluiOp.code : AluiOp → Nat
  | .addi => 0 | .addiu => 1 | .xori => 2 | .andi => 3 | .ori => 4
  | .shli => 5 | .shri => 6 | .asri => 7 | .roli => 8 | .slk16 => 9

@[expose] def BrOp.code : BrOp → Nat
  | .beqz => 0 | .bnez => 1 | .bltz => 2 | .bgez => 3

theorem AluOp.code_lt (op : AluOp) : op.code < 16 := by cases op <;> decide
theorem AluiOp.code_lt (op : AluiOp) : op.code < 16 := by cases op <;> decide
theorem BrOp.code_lt (op : BrOp) : op.code < 16 := by cases op <;> decide

/-! ## 2. Instruction AST -/

/-- `ASS2 / Dregg-64` instructions, grouped by major opcode `0x0 .. 0xF`. -/
inductive Ass2Insn where
  -- `0x0 SYS`
  | exc
  | eret
  | csrr (rd : Reg) (csr : BitVec 8)
  | csrw (ra : Reg) (csr : BitVec 8)
  | zeroize
  | halt
  | nop
  -- `0x1 LUT4`
  | lut4 (m : Fin 16) (rd ra rb : Reg)
  -- `0x2 ALU`
  | alu (op : AluOp) (rd ra rb : Reg)
  -- `0x3 ALUI`
  | alui (op : AluiOp) (rd ra : Reg) (imm : BitVec 16)
  -- `0x4 IMM20`
  | movz20 (rd : Reg) (imm : BitVec 20)
  | movs20 (rd : Reg) (imm : BitVec 20)
  | auipc (rd : Reg) (imm : BitVec 20)
  -- `0x5 CMP`
  | cmp (flags : Fin 16) (rd ra rb : Reg)
  -- `0x6 SEL / BEXT / BSWAP`
  | sel (rd ra rb rc : Reg)
  | bextu (rd ra : Reg) (idx len : Fin 16)
  | bexts (rd ra : Reg) (idx len : Fin 16)
  | bswap64 (rd ra : Reg)
  -- `0x7 LOAD`
  | ld64 (rd ra : Reg) (off : BitVec 16)
  | ldbu (rd ra : Reg) (off : BitVec 16)
  -- `0x8 STORE`
  | st64 (rv ra : Reg) (off : BitVec 16)
  | stb (rv ra : Reg) (off : BitVec 16)
  -- `0x9 BR`
  | br (op : BrOp) (rc : Reg) (off : BitVec 20)
  -- `0xA JAL`
  | jal (rd : Reg) (off : BitVec 24)
  -- `0xB JALR`
  | jalr (rd ra : Reg) (off : BitVec 16)
  -- `0xC SPG`
  | sget (rd : Reg) (sidx : BitVec 8)
  | sput (sidx : BitVec 8) (ra : Reg)
  | sxor (sidx : BitVec 8) (ra : Reg)
  | szero
  | sld64 (sidx : BitVec 8) (ra : Reg) (off : BitVec 8)
  | sst64 (sidx : BitVec 8) (ra : Reg) (off : BitVec 8)
  -- `0xD GL64 / FP5`
  | glMac (rd ra rb rc : Reg)
  | glAdd (rd ra rb : Reg)
  | glSub (rd ra rb : Reg)
  | glSbox7 (rd ra : Reg)
  | fp5Mul (ed ea eb : Reg)
  | fp5Add (ed ea eb : Reg)
  | fp5Sub (ed ea eb : Reg)
  -- `0xE GF128`
  | gf128Mul (pd pa pb : Reg)
  | gf128Xor (pd pa pb : Reg)
  -- `0xF PERM`
  | keccak (rounds : BitVec 8)
  | poseidon2Gl24
  | poseidon2Gl12
  deriving DecidableEq, Repr

/-- The range conditions of the spec that the field widths do not enforce: immediate shift
    amounts below 64, byte indices and lengths below 8, sponge lanes below 25, quintic registers
    below 5, `GF(2^128)` registers below 12, and 12 or 24 Keccak rounds. -/
@[expose] def Ass2Insn.WellFormed : Ass2Insn → Prop
  | .exc => True
  | .eret => True
  | .csrr _ _ => True
  | .csrw _ _ => True
  | .zeroize => True
  | .halt => True
  | .nop => True
  | .lut4 _ _ _ _ => True
  | .alu _ _ _ _ => True
  | .alui op _ _ imm =>
    match op with
    | .addi => True
    | .addiu => True
    | .xori => True
    | .andi => True
    | .ori => True
    | .shli => imm.toNat < 64
    | .shri => imm.toNat < 64
    | .asri => imm.toNat < 64
    | .roli => imm.toNat < 64
    | .slk16 => True
  | .movz20 _ _ => True
  | .movs20 _ _ => True
  | .auipc _ _ => True
  | .cmp _ _ _ _ => True
  | .sel _ _ _ _ => True
  | .bextu _ _ idx len => idx.val < 8 ∧ len.val < 8
  | .bexts _ _ idx len => idx.val < 8 ∧ len.val < 8
  | .bswap64 _ _ => True
  | .ld64 _ _ _ => True
  | .ldbu _ _ _ => True
  | .st64 _ _ _ => True
  | .stb _ _ _ => True
  | .br _ _ _ => True
  | .jal _ _ => True
  | .jalr _ _ _ => True
  | .sget _ sidx => sidx.toNat < 25
  | .sput sidx _ => sidx.toNat < 25
  | .sxor sidx _ => sidx.toNat < 25
  | .szero => True
  | .sld64 sidx _ _ => sidx.toNat < 25
  | .sst64 sidx _ _ => sidx.toNat < 25
  | .glMac _ _ _ _ => True
  | .glAdd _ _ _ => True
  | .glSub _ _ _ => True
  | .glSbox7 _ _ => True
  | .fp5Mul ed ea eb => ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5
  | .fp5Add ed ea eb => ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5
  | .fp5Sub ed ea eb => ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5
  | .gf128Mul pd pa pb => pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12
  | .gf128Xor pd pa pb => pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12
  | .keccak rounds => rounds.toNat = 12 ∨ rounds.toNat = 24
  | .poseidon2Gl24 => True
  | .poseidon2Gl12 => True

instance Ass2Insn.instDecidableWellFormed : DecidablePred Ass2Insn.WellFormed := fun i => by
  cases i with
  | alui op _ _ imm =>
    cases op <;>
      first
      | exact isTrue trivial
      | exact inferInstanceAs (Decidable (imm.toNat < 64))
  | bextu _ _ idx len => exact inferInstanceAs (Decidable (idx.val < 8 ∧ len.val < 8))
  | bexts _ _ idx len => exact inferInstanceAs (Decidable (idx.val < 8 ∧ len.val < 8))
  | sget _ sidx => exact inferInstanceAs (Decidable (sidx.toNat < 25))
  | sput sidx _ => exact inferInstanceAs (Decidable (sidx.toNat < 25))
  | sxor sidx _ => exact inferInstanceAs (Decidable (sidx.toNat < 25))
  | sld64 sidx _ _ => exact inferInstanceAs (Decidable (sidx.toNat < 25))
  | sst64 sidx _ _ => exact inferInstanceAs (Decidable (sidx.toNat < 25))
  | fp5Mul ed ea eb => exact inferInstanceAs (Decidable (ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5))
  | fp5Add ed ea eb => exact inferInstanceAs (Decidable (ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5))
  | fp5Sub ed ea eb => exact inferInstanceAs (Decidable (ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5))
  | gf128Mul pd pa pb =>
    exact inferInstanceAs (Decidable (pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12))
  | gf128Xor pd pa pb =>
    exact inferInstanceAs (Decidable (pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12))
  | keccak rounds => exact inferInstanceAs (Decidable (rounds.toNat = 12 ∨ rounds.toNat = 24))
  | _ => exact isTrue trivial

/-! ## 3. Field packing -/

/-- Standard layout `op | imm8 | sub | rc | rb | ra | rd`. -/
abbrev packStd (op imm8 sub rc rb ra rd : Nat) : Nat :=
  op * 268435456 + imm8 * 1048576 + sub * 65536 + rc * 4096 + rb * 256 + ra * 16 + rd

/-- Layout `op | imm16 | rb | ra | rd`. -/
abbrev packI16 (op imm16 rb ra rd : Nat) : Nat :=
  op * 268435456 + imm16 * 4096 + rb * 256 + ra * 16 + rd

/-- Layout `op | imm20 | ra | rd`. -/
abbrev packI20 (op imm20 ra rd : Nat) : Nat :=
  op * 268435456 + imm20 * 256 + ra * 16 + rd

/-- Layout `op | imm24 | rd`. -/
abbrev packI24 (op imm24 rd : Nat) : Nat :=
  op * 268435456 + imm24 * 16 + rd

/-- `0xC SPG` layout `0xC | off8 | sidx | sub | ra | rd`. -/
abbrev packSpg (off8 sidx sub ra rd : Nat) : Nat :=
  12 * 268435456 + off8 * 1048576 + sidx * 4096 + sub * 256 + ra * 16 + rd

/-! ## 4. Encoder -/

/-- The instruction word as a natural number below `2^32`. -/
@[expose] def encodeNat : Ass2Insn → Nat
  | .exc => packStd 0 0 0 0 0 0 0
  | .eret => packStd 0 0 1 0 0 0 0
  | .csrr rd csr => packStd 0 csr.toNat 2 0 0 0 rd.val
  | .csrw ra csr => packStd 0 csr.toNat 3 0 0 ra.val 0
  | .zeroize => packStd 0 0 4 0 0 0 0
  | .halt => packStd 0 0 5 0 0 0 0
  | .nop => packStd 0 0 6 0 0 0 0
  | .lut4 m rd ra rb => packStd 1 0 m.val 0 rb.val ra.val rd.val
  | .alu op rd ra rb => packStd 2 0 op.code 0 rb.val ra.val rd.val
  | .alui op rd ra imm => packI16 3 imm.toNat op.code ra.val rd.val
  | .movz20 rd imm => packI20 4 imm.toNat 0 rd.val
  | .movs20 rd imm => packI20 4 imm.toNat 1 rd.val
  | .auipc rd imm => packI20 4 imm.toNat 2 rd.val
  | .cmp flags rd ra rb => packStd 5 0 0 flags.val rb.val ra.val rd.val
  | .sel rd ra rb rc => packStd 6 0 0 rc.val rb.val ra.val rd.val
  | .bextu rd ra idx len => packStd 6 0 1 len.val idx.val ra.val rd.val
  | .bexts rd ra idx len => packStd 6 0 2 len.val idx.val ra.val rd.val
  | .bswap64 rd ra => packStd 6 0 3 0 0 ra.val rd.val
  | .ld64 rd ra off => packI16 7 off.toNat 0 ra.val rd.val
  | .ldbu rd ra off => packI16 7 off.toNat 1 ra.val rd.val
  | .st64 rv ra off => packI16 8 off.toNat 0 ra.val rv.val
  | .stb rv ra off => packI16 8 off.toNat 1 ra.val rv.val
  | .br op rc off => packI20 9 off.toNat op.code rc.val
  | .jal rd off => packI24 10 off.toNat rd.val
  | .jalr rd ra off => packI16 11 off.toNat 0 ra.val rd.val
  | .sget rd sidx => packSpg 0 sidx.toNat 0 0 rd.val
  | .sput sidx ra => packSpg 0 sidx.toNat 1 ra.val 0
  | .sxor sidx ra => packSpg 0 sidx.toNat 2 ra.val 0
  | .szero => packSpg 0 0 3 0 0
  | .sld64 sidx ra off => packSpg off.toNat sidx.toNat 4 ra.val 0
  | .sst64 sidx ra off => packSpg off.toNat sidx.toNat 5 ra.val 0
  | .glMac rd ra rb rc => packStd 13 0 0 rc.val rb.val ra.val rd.val
  | .glAdd rd ra rb => packStd 13 0 1 0 rb.val ra.val rd.val
  | .glSub rd ra rb => packStd 13 0 2 0 rb.val ra.val rd.val
  | .glSbox7 rd ra => packStd 13 0 3 0 0 ra.val rd.val
  | .fp5Mul ed ea eb => packStd 13 0 4 0 eb.val ea.val ed.val
  | .fp5Add ed ea eb => packStd 13 0 5 0 eb.val ea.val ed.val
  | .fp5Sub ed ea eb => packStd 13 0 6 0 eb.val ea.val ed.val
  | .gf128Mul pd pa pb => packStd 14 0 0 0 pb.val pa.val pd.val
  | .gf128Xor pd pa pb => packStd 14 0 1 0 pb.val pa.val pd.val
  | .keccak rounds => packStd 15 rounds.toNat 0 0 0 0 0
  | .poseidon2Gl24 => packStd 15 0 1 0 0 0 0
  | .poseidon2Gl12 => packStd 15 0 2 0 0 0 0

/-- The 32-bit instruction word. -/
@[expose] def encodeAss2 (i : Ass2Insn) : UInt32 := UInt32.ofNat (encodeNat i)

/-! ## 5. Decoder -/

/-- Decoder on the numeric value of the word. Each major opcode has its own field decoder; a
    reserved sub-opcode or a nonzero reserved field yields `none` (`IllegalInsn`). -/
@[expose] def decodeNat (n : Nat) : Option Ass2Insn :=
  let rd := n % 16
  let ra := n / 16 % 16
  let rb := n / 256 % 16
  let rc := n / 4096 % 16
  let sub := n / 65536 % 16
  let imm8 := n / 1048576 % 256
  let imm16 := n / 4096 % 65536
  let imm20 := n / 256 % 1048576
  let imm24 := n / 16 % 16777216
  let sidx := n / 4096 % 256
  match n / 268435456 with
  | 0 => decSys imm8 sub rc rb ra rd
  | 1 => decLut4 imm8 sub rc rb ra rd
  | 2 => decAlu imm8 sub rc rb ra rd
  | 3 => decAlui imm16 rb ra rd
  | 4 => decImm20 imm20 ra rd
  | 5 => decCmp imm8 sub rc rb ra rd
  | 6 => decSel imm8 sub rc rb ra rd
  | 7 => decLoad imm16 rb ra rd
  | 8 => decStore imm16 rb ra rd
  | 9 => decBr imm20 ra rd
  | 10 => some (.jal (reg rd) (BitVec.ofNat 24 imm24))
  | 11 => decJalr imm16 rb ra rd
  | 12 => decSpg imm8 sidx rb ra rd
  | 13 => decGl imm8 sub rc rb ra rd
  | 14 => decGf128 imm8 sub rc rb ra rd
  | 15 => decPerm imm8 sub rc rb ra rd
  | _ => none
where
  /-- `0x0 SYS`. -/
  decSys (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    match sub with
    | 0 => if imm8 = 0 ∧ rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then some .exc else none
    | 1 => if imm8 = 0 ∧ rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then some .eret else none
    | 2 => if rc = 0 ∧ rb = 0 ∧ ra = 0 then some (.csrr (reg rd) (BitVec.ofNat 8 imm8)) else none
    | 3 => if rc = 0 ∧ rb = 0 ∧ rd = 0 then some (.csrw (reg ra) (BitVec.ofNat 8 imm8)) else none
    | 4 => if imm8 = 0 ∧ rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then some .zeroize else none
    | 5 => if imm8 = 0 ∧ rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then some .halt else none
    | 6 => if imm8 = 0 ∧ rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then some .nop else none
    | _ => none
  /-- `0x1 LUT4`. -/
  decLut4 (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 ∧ rc = 0 then some (.lut4 (reg sub) (reg rd) (reg ra) (reg rb)) else none
  /-- `0x2 ALU`. -/
  decAlu (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 ∧ rc = 0 then
      match sub with
      | 0 => some (.alu .add (reg rd) (reg ra) (reg rb))
      | 1 => some (.alu .sub (reg rd) (reg ra) (reg rb))
      | 2 => some (.alu .shl (reg rd) (reg ra) (reg rb))
      | 3 => some (.alu .shr (reg rd) (reg ra) (reg rb))
      | 4 => some (.alu .asr (reg rd) (reg ra) (reg rb))
      | 5 => some (.alu .rol (reg rd) (reg ra) (reg rb))
      | 6 => some (.alu .ror (reg rd) (reg ra) (reg rb))
      | 7 => some (.alu .mul64 (reg rd) (reg ra) (reg rb))
      | 8 => some (.alu .mulhu64 (reg rd) (reg ra) (reg rb))
      | _ => none
    else none
  /-- `0x3 ALUI`. -/
  decAlui (imm16 fn ra rd : Nat) : Option Ass2Insn :=
    match fn with
    | 0 => some (.alui .addi (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 1 => some (.alui .addiu (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 2 => some (.alui .xori (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 3 => some (.alui .andi (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 4 => some (.alui .ori (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 5 => if imm16 < 64 then some (.alui .shli (reg rd) (reg ra) (BitVec.ofNat 16 imm16)) else none
    | 6 => if imm16 < 64 then some (.alui .shri (reg rd) (reg ra) (BitVec.ofNat 16 imm16)) else none
    | 7 => if imm16 < 64 then some (.alui .asri (reg rd) (reg ra) (BitVec.ofNat 16 imm16)) else none
    | 8 => if imm16 < 64 then some (.alui .roli (reg rd) (reg ra) (BitVec.ofNat 16 imm16)) else none
    | 9 => some (.alui .slk16 (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | _ => none
  /-- `0x4 IMM20`. -/
  decImm20 (imm20 mode rd : Nat) : Option Ass2Insn :=
    match mode with
    | 0 => some (.movz20 (reg rd) (BitVec.ofNat 20 imm20))
    | 1 => some (.movs20 (reg rd) (BitVec.ofNat 20 imm20))
    | 2 => some (.auipc (reg rd) (BitVec.ofNat 20 imm20))
    | _ => none
  /-- `0x5 CMP`. -/
  decCmp (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 ∧ sub = 0 then some (.cmp (reg rc) (reg rd) (reg ra) (reg rb)) else none
  /-- `0x6 SEL / BEXT / BSWAP`. -/
  decSel (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 then
      match sub with
      | 0 => some (.sel (reg rd) (reg ra) (reg rb) (reg rc))
      | 1 => if rb < 8 ∧ rc < 8 then some (.bextu (reg rd) (reg ra) (reg rb) (reg rc)) else none
      | 2 => if rb < 8 ∧ rc < 8 then some (.bexts (reg rd) (reg ra) (reg rb) (reg rc)) else none
      | 3 => if rb = 0 ∧ rc = 0 then some (.bswap64 (reg rd) (reg ra)) else none
      | _ => none
    else none
  /-- `0x7 LOAD`. -/
  decLoad (imm16 mode ra rd : Nat) : Option Ass2Insn :=
    match mode with
    | 0 => some (.ld64 (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | 1 => some (.ldbu (reg rd) (reg ra) (BitVec.ofNat 16 imm16))
    | _ => none
  /-- `0x8 STORE` (the value register sits in the `rd` field). -/
  decStore (imm16 mode ra rv : Nat) : Option Ass2Insn :=
    match mode with
    | 0 => some (.st64 (reg rv) (reg ra) (BitVec.ofNat 16 imm16))
    | 1 => some (.stb (reg rv) (reg ra) (BitVec.ofNat 16 imm16))
    | _ => none
  /-- `0x9 BR` (the condition register sits in the `rd` field). -/
  decBr (imm20 bop rcond : Nat) : Option Ass2Insn :=
    match bop with
    | 0 => some (.br .beqz (reg rcond) (BitVec.ofNat 20 imm20))
    | 1 => some (.br .bnez (reg rcond) (BitVec.ofNat 20 imm20))
    | 2 => some (.br .bltz (reg rcond) (BitVec.ofNat 20 imm20))
    | 3 => some (.br .bgez (reg rcond) (BitVec.ofNat 20 imm20))
    | _ => none
  /-- `0xB JALR`. -/
  decJalr (imm16 rb ra rd : Nat) : Option Ass2Insn :=
    if rb = 0 then some (.jalr (reg rd) (reg ra) (BitVec.ofNat 16 imm16)) else none
  /-- `0xC SPG`. -/
  decSpg (off8 sidx sub ra rd : Nat) : Option Ass2Insn :=
    match sub with
    | 0 => if off8 = 0 ∧ ra = 0 ∧ sidx < 25 then some (.sget (reg rd) (BitVec.ofNat 8 sidx))
           else none
    | 1 => if off8 = 0 ∧ rd = 0 ∧ sidx < 25 then some (.sput (BitVec.ofNat 8 sidx) (reg ra))
           else none
    | 2 => if off8 = 0 ∧ rd = 0 ∧ sidx < 25 then some (.sxor (BitVec.ofNat 8 sidx) (reg ra))
           else none
    | 3 => if off8 = 0 ∧ rd = 0 ∧ ra = 0 ∧ sidx = 0 then some .szero else none
    | 4 => if rd = 0 ∧ sidx < 25 then
             some (.sld64 (BitVec.ofNat 8 sidx) (reg ra) (BitVec.ofNat 8 off8))
           else none
    | 5 => if rd = 0 ∧ sidx < 25 then
             some (.sst64 (BitVec.ofNat 8 sidx) (reg ra) (BitVec.ofNat 8 off8))
           else none
    | _ => none
  /-- `0xD GL64 / FP5`. -/
  decGl (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 then
      match sub with
      | 0 => some (.glMac (reg rd) (reg ra) (reg rb) (reg rc))
      | 1 => if rc = 0 then some (.glAdd (reg rd) (reg ra) (reg rb)) else none
      | 2 => if rc = 0 then some (.glSub (reg rd) (reg ra) (reg rb)) else none
      | 3 => if rc = 0 ∧ rb = 0 then some (.glSbox7 (reg rd) (reg ra)) else none
      | 4 => if rc = 0 ∧ rd < 5 ∧ ra < 5 ∧ rb < 5 then some (.fp5Mul (reg rd) (reg ra) (reg rb))
             else none
      | 5 => if rc = 0 ∧ rd < 5 ∧ ra < 5 ∧ rb < 5 then some (.fp5Add (reg rd) (reg ra) (reg rb))
             else none
      | 6 => if rc = 0 ∧ rd < 5 ∧ ra < 5 ∧ rb < 5 then some (.fp5Sub (reg rd) (reg ra) (reg rb))
             else none
      | _ => none
    else none
  /-- `0xE GF128`. -/
  decGf128 (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if imm8 = 0 ∧ rc = 0 ∧ rd < 12 ∧ ra < 12 ∧ rb < 12 then
      match sub with
      | 0 => some (.gf128Mul (reg rd) (reg ra) (reg rb))
      | 1 => some (.gf128Xor (reg rd) (reg ra) (reg rb))
      | _ => none
    else none
  /-- `0xF PERM`. -/
  decPerm (imm8 sub rc rb ra rd : Nat) : Option Ass2Insn :=
    if rc = 0 ∧ rb = 0 ∧ ra = 0 ∧ rd = 0 then
      match sub with
      | 0 => if imm8 = 12 ∨ imm8 = 24 then some (.keccak (BitVec.ofNat 8 imm8)) else none
      | 1 => if imm8 = 0 then some .poseidon2Gl24 else none
      | 2 => if imm8 = 0 then some .poseidon2Gl12 else none
      | _ => none
    else none

/-- Decode a 32-bit instruction word; `none` is `IllegalInsn`. -/
@[expose] def decodeAss2 (w : UInt32) : Option Ass2Insn := decodeNat w.toNat

/-! ## 6. Fixed instruction latency -/

/-- `cycle_cost(op, sub)`: the latency in clock cycles. It depends on the instruction word only,
    never on an operand value. -/
@[expose] def cycleCost : Ass2Insn → UInt64
  | .alu .mul64 _ _ _ => 4
  | .alu .mulhu64 _ _ _ => 4
  | .ld64 _ _ _ => 2
  | .ldbu _ _ _ => 2
  | .st64 _ _ _ => 2
  | .stb _ _ _ => 2
  | .sld64 _ _ _ => 2
  | .sst64 _ _ _ => 2
  | .glMac _ _ _ _ => 4
  | .glSbox7 _ _ => 12
  | .fp5Mul _ _ _ => 104
  | .fp5Add _ _ _ => 5
  | .fp5Sub _ _ _ => 5
  | .gf128Mul _ _ _ => 4
  | .keccak rounds => UInt64.ofNat rounds.toNat
  | .poseidon2Gl24 => 216
  | .poseidon2Gl12 => 120
  | _ => 1

/-! ## 7. Round trips -/

theorem encodeNat_lt (i : Ass2Insn) : encodeNat i < 4294967296 := by
  cases i with
  | alu op rd ra rb =>
    have := op.code_lt
    simp only [encodeNat, packStd]; omega
  | alui op rd ra imm =>
    have := op.code_lt
    simp only [encodeNat, packI16]; omega
  | br op rc off =>
    have := op.code_lt
    simp only [encodeNat, packI20]; omega
  | _ => simp only [encodeNat, packStd, packI16, packI20, packI24, packSpg]; omega

private theorem fields_std {op imm8 sub rc rb ra rd : Nat} (h8 : imm8 < 256)
    (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    packStd op imm8 sub rc rb ra rd / 268435456 = op ∧
    packStd op imm8 sub rc rb ra rd / 1048576 % 256 = imm8 ∧
    packStd op imm8 sub rc rb ra rd / 65536 % 16 = sub ∧
    packStd op imm8 sub rc rb ra rd / 4096 % 16 = rc ∧
    packStd op imm8 sub rc rb ra rd / 256 % 16 = rb ∧
    packStd op imm8 sub rc rb ra rd / 16 % 16 = ra ∧
    packStd op imm8 sub rc rb ra rd % 16 = rd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [packStd] <;> omega

private theorem fields_i16 {op imm16 rb ra rd : Nat} (hi : imm16 < 65536)
    (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    packI16 op imm16 rb ra rd / 268435456 = op ∧
    packI16 op imm16 rb ra rd / 4096 % 65536 = imm16 ∧
    packI16 op imm16 rb ra rd / 256 % 16 = rb ∧
    packI16 op imm16 rb ra rd / 16 % 16 = ra ∧
    packI16 op imm16 rb ra rd % 16 = rd := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [packI16] <;> omega

private theorem fields_i20 {op imm20 ra rd : Nat} (hi : imm20 < 1048576)
    (hra : ra < 16) (hrd : rd < 16) :
    packI20 op imm20 ra rd / 268435456 = op ∧
    packI20 op imm20 ra rd / 256 % 1048576 = imm20 ∧
    packI20 op imm20 ra rd / 16 % 16 = ra ∧
    packI20 op imm20 ra rd % 16 = rd := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [packI20] <;> omega

private theorem fields_i24 {op imm24 rd : Nat} (hi : imm24 < 16777216)
    (hrd : rd < 16) :
    packI24 op imm24 rd / 268435456 = op ∧
    packI24 op imm24 rd / 16 % 16777216 = imm24 ∧
    packI24 op imm24 rd % 16 = rd := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [packI24] <;> omega

private theorem fields_spg {off8 sidx sub ra rd : Nat} (ho : off8 < 256) (hx : sidx < 256)
    (hs : sub < 16) (hra : ra < 16) (hrd : rd < 16) :
    packSpg off8 sidx sub ra rd / 268435456 = 12 ∧
    packSpg off8 sidx sub ra rd / 1048576 % 256 = off8 ∧
    packSpg off8 sidx sub ra rd / 4096 % 256 = sidx ∧
    packSpg off8 sidx sub ra rd / 256 % 16 = sub ∧
    packSpg off8 sidx sub ra rd / 16 % 16 = ra ∧
    packSpg off8 sidx sub ra rd % 16 = rd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [packSpg] <;> omega

section FieldDecoders
variable {imm8 sub rc rb ra rd imm16 imm20 : Nat}

private theorem decodeNat_op0 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 0 imm8 sub rc rb ra rd) = decodeNat.decSys imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 0) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op1 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 1 imm8 sub rc rb ra rd) = decodeNat.decLut4 imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 1) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op2 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 2 imm8 sub rc rb ra rd) = decodeNat.decAlu imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 2) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op3 (hi : imm16 < 65536) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packI16 3 imm16 rb ra rd) = decodeNat.decAlui imm16 rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := fields_i16 (op := 3) hi hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4]
private theorem decodeNat_op4 (hi : imm20 < 1048576) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packI20 4 imm20 ra rd) = decodeNat.decImm20 imm20 ra rd := by
  obtain ⟨h0, h1, h2, h3⟩ := fields_i20 (op := 4) hi hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3]
private theorem decodeNat_op5 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 5 imm8 sub rc rb ra rd) = decodeNat.decCmp imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 5) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op6 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 6 imm8 sub rc rb ra rd) = decodeNat.decSel imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 6) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op7 (hi : imm16 < 65536) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packI16 7 imm16 rb ra rd) = decodeNat.decLoad imm16 rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := fields_i16 (op := 7) hi hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4]
private theorem decodeNat_op8 (hi : imm16 < 65536) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packI16 8 imm16 rb ra rd) = decodeNat.decStore imm16 rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := fields_i16 (op := 8) hi hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4]
private theorem decodeNat_op9 (hi : imm20 < 1048576) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packI20 9 imm20 ra rd) = decodeNat.decBr imm20 ra rd := by
  obtain ⟨h0, h1, h2, h3⟩ := fields_i20 (op := 9) hi hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3]
private theorem decodeNat_op10 {imm24 : Nat} (hi : imm24 < 16777216) (hrd : rd < 16) :
    decodeNat (packI24 10 imm24 rd) = some (.jal (reg rd) (BitVec.ofNat 24 imm24)) := by
  obtain ⟨h0, h1, h2⟩ := fields_i24 (op := 10) hi hrd
  unfold decodeNat
  simp only [h0, h1, h2]
private theorem decodeNat_op11 (hi : imm16 < 65536) (hrb : rb < 16) (hra : ra < 16)
    (hrd : rd < 16) :
    decodeNat (packI16 11 imm16 rb ra rd) = decodeNat.decJalr imm16 rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := fields_i16 (op := 11) hi hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4]
private theorem decodeNat_op12 {off8 sidx : Nat} (ho : off8 < 256) (hx : sidx < 256)
    (hs : sub < 16) (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packSpg off8 sidx sub ra rd) = decodeNat.decSpg off8 sidx sub ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := fields_spg ho hx hs hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5]
private theorem decodeNat_op13 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 13 imm8 sub rc rb ra rd) = decodeNat.decGl imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 13) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op14 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 14 imm8 sub rc rb ra rd) = decodeNat.decGf128 imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 14) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]
private theorem decodeNat_op15 (h8 : imm8 < 256) (hs : sub < 16) (hrc : rc < 16) (hrb : rb < 16)
    (hra : ra < 16) (hrd : rd < 16) :
    decodeNat (packStd 15 imm8 sub rc rb ra rd) = decodeNat.decPerm imm8 sub rc rb ra rd := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := fields_std (op := 15) h8 hs hrc hrb hra hrd
  unfold decodeNat
  simp only [h0, h1, h2, h3, h4, h5, h6]

end FieldDecoders

/-- Evaluate a field decoder on the fields of an encoded instruction. -/
local macro "dec_close" : tactic => `(tactic|
  first
  | rfl
  | (simp only [decodeNat.decSys, decodeNat.decLut4, decodeNat.decAlu, decodeNat.decAlui,
      decodeNat.decImm20, decodeNat.decCmp, decodeNat.decSel, decodeNat.decLoad,
      decodeNat.decStore, decodeNat.decBr, decodeNat.decJalr, decodeNat.decSpg, decodeNat.decGl,
      decodeNat.decGf128, decodeNat.decPerm, AluOp.code, AluiOp.code, BrOp.code, reg_val,
      bv_ofNat_toNat, and_self, ↓reduceIte]))

/-- `decodeNat` inverts `encodeNat` on well-formed instructions. -/
theorem decodeNat_encodeNat (i : Ass2Insn) (hwf : i.WellFormed) :
    decodeNat (encodeNat i) = some i := by
  have z : (0 : Nat) < 16 := by decide
  have z8 : (0 : Nat) < 256 := by decide
  cases i with
  | exc => rfl
  | eret => rfl
  | csrr rd csr =>
    rw [encodeNat, decodeNat_op0 csr.isLt (by decide) z z z rd.isLt]; dec_close
  | csrw ra csr =>
    rw [encodeNat, decodeNat_op0 csr.isLt (by decide) z z ra.isLt z]; dec_close
  | zeroize => rfl
  | halt => rfl
  | nop => rfl
  | lut4 m rd ra rb =>
    rw [encodeNat, decodeNat_op1 z8 m.isLt z rb.isLt ra.isLt rd.isLt]; dec_close
  | alu op rd ra rb =>
    rw [encodeNat, decodeNat_op2 z8 op.code_lt z rb.isLt ra.isLt rd.isLt]
    cases op <;> dec_close
  | alui op rd ra imm =>
    rw [encodeNat, decodeNat_op3 imm.isLt op.code_lt ra.isLt rd.isLt]
    cases op <;>
      first
      | (have hlt : imm.toNat < 64 := hwf
         simp only [decodeNat.decAlui, AluiOp.code, reg_val, bv_ofNat_toNat, hlt, ↓reduceIte])
      | dec_close
  | movz20 rd imm => rw [encodeNat, decodeNat_op4 imm.isLt z rd.isLt]; dec_close
  | movs20 rd imm => rw [encodeNat, decodeNat_op4 imm.isLt (by decide) rd.isLt]; dec_close
  | auipc rd imm => rw [encodeNat, decodeNat_op4 imm.isLt (by decide) rd.isLt]; dec_close
  | cmp flags rd ra rb =>
    rw [encodeNat, decodeNat_op5 z8 z flags.isLt rb.isLt ra.isLt rd.isLt]; dec_close
  | sel rd ra rb rc =>
    rw [encodeNat, decodeNat_op6 z8 z rc.isLt rb.isLt ra.isLt rd.isLt]; dec_close
  | bextu rd ra idx len =>
    have hwf' : idx.val < 8 ∧ len.val < 8 := hwf
    rw [encodeNat, decodeNat_op6 z8 (by decide) len.isLt idx.isLt ra.isLt rd.isLt]
    simp only [decodeNat.decSel, reg_val, hwf'.1, hwf'.2, and_self, ↓reduceIte]
  | bexts rd ra idx len =>
    have hwf' : idx.val < 8 ∧ len.val < 8 := hwf
    rw [encodeNat, decodeNat_op6 z8 (by decide) len.isLt idx.isLt ra.isLt rd.isLt]
    simp only [decodeNat.decSel, reg_val, hwf'.1, hwf'.2, and_self, ↓reduceIte]
  | bswap64 rd ra =>
    rw [encodeNat, decodeNat_op6 z8 (by decide) z z ra.isLt rd.isLt]; dec_close
  | ld64 rd ra off => rw [encodeNat, decodeNat_op7 off.isLt z ra.isLt rd.isLt]; dec_close
  | ldbu rd ra off =>
    rw [encodeNat, decodeNat_op7 off.isLt (by decide) ra.isLt rd.isLt]; dec_close
  | st64 rv ra off => rw [encodeNat, decodeNat_op8 off.isLt z ra.isLt rv.isLt]; dec_close
  | stb rv ra off =>
    rw [encodeNat, decodeNat_op8 off.isLt (by decide) ra.isLt rv.isLt]; dec_close
  | br op rc off =>
    rw [encodeNat, decodeNat_op9 off.isLt op.code_lt rc.isLt]
    cases op <;> dec_close
  | jal rd off =>
    rw [encodeNat, decodeNat_op10 off.isLt rd.isLt, reg_val, bv_ofNat_toNat]
  | jalr rd ra off => rw [encodeNat, decodeNat_op11 off.isLt z ra.isLt rd.isLt]; dec_close
  | sget rd sidx =>
    have hwf' : sidx.toNat < 25 := hwf
    rw [encodeNat, decodeNat_op12 z8 sidx.isLt z z rd.isLt]
    simp only [decodeNat.decSpg, reg_val, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | sput sidx ra =>
    have hwf' : sidx.toNat < 25 := hwf
    rw [encodeNat, decodeNat_op12 z8 sidx.isLt (by decide) ra.isLt z]
    simp only [decodeNat.decSpg, reg_val, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | sxor sidx ra =>
    have hwf' : sidx.toNat < 25 := hwf
    rw [encodeNat, decodeNat_op12 z8 sidx.isLt (by decide) ra.isLt z]
    simp only [decodeNat.decSpg, reg_val, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | szero => rfl
  | sld64 sidx ra off =>
    have hwf' : sidx.toNat < 25 := hwf
    rw [encodeNat, decodeNat_op12 off.isLt sidx.isLt (by decide) ra.isLt z]
    simp only [decodeNat.decSpg, reg_val, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | sst64 sidx ra off =>
    have hwf' : sidx.toNat < 25 := hwf
    rw [encodeNat, decodeNat_op12 off.isLt sidx.isLt (by decide) ra.isLt z]
    simp only [decodeNat.decSpg, reg_val, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | glMac rd ra rb rc =>
    rw [encodeNat, decodeNat_op13 z8 z rc.isLt rb.isLt ra.isLt rd.isLt]; dec_close
  | glAdd rd ra rb =>
    rw [encodeNat, decodeNat_op13 z8 (by decide) z rb.isLt ra.isLt rd.isLt]; dec_close
  | glSub rd ra rb =>
    rw [encodeNat, decodeNat_op13 z8 (by decide) z rb.isLt ra.isLt rd.isLt]; dec_close
  | glSbox7 rd ra =>
    rw [encodeNat, decodeNat_op13 z8 (by decide) z z ra.isLt rd.isLt]; dec_close
  | fp5Mul ed ea eb =>
    have hwf' : ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5 := hwf
    rw [encodeNat, decodeNat_op13 z8 (by decide) z eb.isLt ea.isLt ed.isLt]
    simp only [decodeNat.decGl, reg_val, hwf'.1, hwf'.2.1, hwf'.2.2, and_self, ↓reduceIte]
  | fp5Add ed ea eb =>
    have hwf' : ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5 := hwf
    rw [encodeNat, decodeNat_op13 z8 (by decide) z eb.isLt ea.isLt ed.isLt]
    simp only [decodeNat.decGl, reg_val, hwf'.1, hwf'.2.1, hwf'.2.2, and_self, ↓reduceIte]
  | fp5Sub ed ea eb =>
    have hwf' : ed.val < 5 ∧ ea.val < 5 ∧ eb.val < 5 := hwf
    rw [encodeNat, decodeNat_op13 z8 (by decide) z eb.isLt ea.isLt ed.isLt]
    simp only [decodeNat.decGl, reg_val, hwf'.1, hwf'.2.1, hwf'.2.2, and_self, ↓reduceIte]
  | gf128Mul pd pa pb =>
    have hwf' : pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12 := hwf
    rw [encodeNat, decodeNat_op14 z8 z z pb.isLt pa.isLt pd.isLt]
    simp only [decodeNat.decGf128, reg_val, hwf'.1, hwf'.2.1, hwf'.2.2, and_self, ↓reduceIte]
  | gf128Xor pd pa pb =>
    have hwf' : pd.val < 12 ∧ pa.val < 12 ∧ pb.val < 12 := hwf
    rw [encodeNat, decodeNat_op14 z8 (by decide) z pb.isLt pa.isLt pd.isLt]
    simp only [decodeNat.decGf128, reg_val, hwf'.1, hwf'.2.1, hwf'.2.2, and_self, ↓reduceIte]
  | keccak rounds =>
    have hwf' : rounds.toNat = 12 ∨ rounds.toNat = 24 := hwf
    rw [encodeNat, decodeNat_op15 rounds.isLt z z z z z]
    simp only [decodeNat.decPerm, bv_ofNat_toNat, hwf', and_self, ↓reduceIte]
  | poseidon2Gl24 => rfl
  | poseidon2Gl12 => rfl

/-- Close one accepted branch of a field decoder: well-formedness and the re-encoded word. -/
local macro "sound_close" : tactic => `(tactic|
  (refine ⟨?_, ?_⟩
   · first
     | trivial
     | (simp only [Ass2Insn.WellFormed, BitVec.toNat_ofNat]
        first
        | (refine ⟨?_, ?_, ?_⟩ <;> omega)
        | (refine ⟨?_, ?_⟩ <;> omega)
        | omega)
   · simp only [encodeNat, packStd, packI16, packI20, packI24, packSpg, AluOp.code, AluiOp.code,
       BrOp.code, BitVec.toNat_ofNat]
     omega))

section FieldSoundness
variable {imm8 sub rc rb ra rd imm16 imm20 : Nat} {i : Ass2Insn}

private theorem decSys_sound (h : decodeNat.decSys imm8 sub rc rb ra rd = some i)
    (h8 : imm8 < 256) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 0 imm8 sub rc rb ra rd := by
  unfold decodeNat.decSys at h
  split at h <;> (try split at h) <;> cases h <;> sound_close

private theorem decLut4_sound (h : decodeNat.decLut4 imm8 sub rc rb ra rd = some i)
    (hs : sub < 16) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 1 imm8 sub rc rb ra rd := by
  unfold decodeNat.decLut4 at h
  split at h <;> cases h <;> sound_close

private theorem decAlu_sound (h : decodeNat.decAlu imm8 sub rc rb ra rd = some i)
    (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 2 imm8 sub rc rb ra rd := by
  unfold decodeNat.decAlu at h
  split at h <;> (try split at h) <;> cases h <;> sound_close

private theorem decAlui_sound (h : decodeNat.decAlui imm16 rb ra rd = some i)
    (hi : imm16 < 65536) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI16 3 imm16 rb ra rd := by
  unfold decodeNat.decAlui at h
  split at h <;> (try split at h) <;> cases h <;> sound_close

private theorem decImm20_sound (h : decodeNat.decImm20 imm20 ra rd = some i)
    (hi : imm20 < 1048576) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI20 4 imm20 ra rd := by
  unfold decodeNat.decImm20 at h
  split at h <;> cases h <;> sound_close

private theorem decCmp_sound (h : decodeNat.decCmp imm8 sub rc rb ra rd = some i)
    (hrc : rc < 16) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 5 imm8 sub rc rb ra rd := by
  unfold decodeNat.decCmp at h
  split at h <;> cases h <;> sound_close

private theorem decSel_sound (h : decodeNat.decSel imm8 sub rc rb ra rd = some i)
    (hrc : rc < 16) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 6 imm8 sub rc rb ra rd := by
  unfold decodeNat.decSel at h
  split at h <;> (try split at h) <;> (try split at h) <;> cases h <;> sound_close

private theorem decLoad_sound (h : decodeNat.decLoad imm16 rb ra rd = some i)
    (hi : imm16 < 65536) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI16 7 imm16 rb ra rd := by
  unfold decodeNat.decLoad at h
  split at h <;> cases h <;> sound_close

private theorem decStore_sound (h : decodeNat.decStore imm16 rb ra rd = some i)
    (hi : imm16 < 65536) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI16 8 imm16 rb ra rd := by
  unfold decodeNat.decStore at h
  split at h <;> cases h <;> sound_close

private theorem decBr_sound (h : decodeNat.decBr imm20 ra rd = some i)
    (hi : imm20 < 1048576) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI20 9 imm20 ra rd := by
  unfold decodeNat.decBr at h
  split at h <;> cases h <;> sound_close

private theorem decJalr_sound (h : decodeNat.decJalr imm16 rb ra rd = some i)
    (hi : imm16 < 65536) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packI16 11 imm16 rb ra rd := by
  unfold decodeNat.decJalr at h
  split at h <;> cases h <;> sound_close

private theorem decSpg_sound {off8 sidx : Nat} (h : decodeNat.decSpg off8 sidx sub ra rd = some i)
    (ho : off8 < 256) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packSpg off8 sidx sub ra rd := by
  unfold decodeNat.decSpg at h
  split at h <;> (try split at h) <;> cases h <;> sound_close

private theorem decGl_sound (h : decodeNat.decGl imm8 sub rc rb ra rd = some i)
    (hrc : rc < 16) (hrb : rb < 16) (hra : ra < 16) (hrd : rd < 16) :
    i.WellFormed ∧ encodeNat i = packStd 13 imm8 sub rc rb ra rd := by
  unfold decodeNat.decGl at h
  split at h <;> (try split at h) <;> (try split at h) <;> cases h <;> sound_close

private theorem decGf128_sound (h : decodeNat.decGf128 imm8 sub rc rb ra rd = some i) :
    i.WellFormed ∧ encodeNat i = packStd 14 imm8 sub rc rb ra rd := by
  unfold decodeNat.decGf128 at h
  split at h <;> (try split at h) <;> cases h <;> sound_close

private theorem decPerm_sound (h : decodeNat.decPerm imm8 sub rc rb ra rd = some i) :
    i.WellFormed ∧ encodeNat i = packStd 15 imm8 sub rc rb ra rd := by
  unfold decodeNat.decPerm at h
  split at h <;> (try split at h) <;> (try split at h) <;> cases h <;> sound_close

end FieldSoundness

/-- Every accepted natural number is the encoding of the well-formed instruction it decodes
    to. -/
theorem decodeNat_sound {n : Nat} {i : Ass2Insn}
    (h : decodeNat n = some i) : i.WellFormed ∧ encodeNat i = n := by
  unfold decodeNat at h
  dsimp only at h
  generalize hq : n / 268435456 = q at h
  match q, hq, h with
  | 0, hq, h =>
    obtain ⟨hw, he⟩ := decSys_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 1, hq, h =>
    obtain ⟨hw, he⟩ := decLut4_sound h (by omega) (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 2, hq, h =>
    obtain ⟨hw, he⟩ := decAlu_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 3, hq, h =>
    obtain ⟨hw, he⟩ := decAlui_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI16]; omega⟩
  | 4, hq, h =>
    obtain ⟨hw, he⟩ := decImm20_sound h (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI20]; omega⟩
  | 5, hq, h =>
    obtain ⟨hw, he⟩ := decCmp_sound h (by omega) (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 6, hq, h =>
    obtain ⟨hw, he⟩ := decSel_sound h (by omega) (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 7, hq, h =>
    obtain ⟨hw, he⟩ := decLoad_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI16]; omega⟩
  | 8, hq, h =>
    obtain ⟨hw, he⟩ := decStore_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI16]; omega⟩
  | 9, hq, h =>
    obtain ⟨hw, he⟩ := decBr_sound h (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI20]; omega⟩
  | 10, hq, h =>
    cases h
    refine ⟨trivial, ?_⟩
    simp only [encodeNat, packI24, BitVec.toNat_ofNat]
    omega
  | 11, hq, h =>
    obtain ⟨hw, he⟩ := decJalr_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packI16]; omega⟩
  | 12, hq, h =>
    obtain ⟨hw, he⟩ := decSpg_sound h (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packSpg]; omega⟩
  | 13, hq, h =>
    obtain ⟨hw, he⟩ := decGl_sound h (by omega) (by omega) (by omega) (by omega)
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 14, hq, h =>
    obtain ⟨hw, he⟩ := decGf128_sound h
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | 15, hq, h =>
    obtain ⟨hw, he⟩ := decPerm_sound h
    exact ⟨hw, by rw [he]; simp only [packStd]; omega⟩
  | _ + 16, _, h => nomatch h

/-- **Codec round trip, encode then decode.** Every well-formed instruction encodes to a word
    that decodes back to it. -/
theorem decodeAss2_encodeAss2 (i : Ass2Insn) (h : i.WellFormed) :
    decodeAss2 (encodeAss2 i) = some i := by
  unfold decodeAss2 encodeAss2
  rw [UInt32.toNat_ofNat_of_lt' (encodeNat_lt i)]
  exact decodeNat_encodeNat i h

/-- **Codec round trip, decode then encode.** A word accepted by the decoder yields a well-formed
    instruction whose encoding is that word: no two words decode to the same instruction and no
    word with a nonzero reserved field is accepted. -/
theorem encodeAss2_decodeAss2 (w : UInt32) (i : Ass2Insn) (h : decodeAss2 w = some i) :
    i.WellFormed ∧ encodeAss2 i = w := by
  obtain ⟨hw, he⟩ := decodeNat_sound h
  refine ⟨hw, ?_⟩
  unfold encodeAss2
  rw [he]
  exact UInt32.ofNat_toNat

/-- The round trips determine the decoder: `w` decodes to `i` exactly when `i` is well formed and
    encodes to `w`. -/
theorem decodeAss2_eq_some_iff (w : UInt32) (i : Ass2Insn) :
    decodeAss2 w = some i ↔ i.WellFormed ∧ encodeAss2 i = w :=
  ⟨encodeAss2_decodeAss2 w i, fun h => h.2 ▸ decodeAss2_encodeAss2 i h.1⟩

/-- The encoder is injective on well-formed instructions. -/
theorem encodeAss2_injective {i j : Ass2Insn} (hi : i.WellFormed) (hj : j.WellFormed)
    (h : encodeAss2 i = encodeAss2 j) : i = j := by
  have h1 := decodeAss2_encodeAss2 i hi
  rw [h, decodeAss2_encodeAss2 j hj] at h1
  exact (Option.some.inj h1).symm

/-! ## 8. The spec's shift-and-mask field extraction -/

private theorem u32_field (w : UInt32) (k : UInt32) (m : UInt32) (kn mn : Nat)
    (hk : k.toNat % 32 = kn) (hm : m.toNat = 2 ^ mn - 1) :
    ((w >>> k) &&& m).toNat = w.toNat / 2 ^ kn % 2 ^ mn := by
  rw [UInt32.toNat_and, UInt32.toNat_shiftRight, hk, hm, Qsag.Constructive.and_mask,
    Nat.shiftRight_eq_div_pow]

/-- `op = (w >> 28) & 0xF`. -/
theorem ass2_field_op (w : UInt32) : ((w >>> 28) &&& 0xF).toNat = w.toNat / 268435456 % 16 :=
  u32_field w 28 0xF 28 4 (by decide) (by decide)
/-- `rd = w & 0xF`. -/
theorem ass2_field_rd (w : UInt32) : (w &&& 0xF).toNat = w.toNat % 16 := by
  rw [UInt32.toNat_and]
  exact Qsag.Constructive.and_mask w.toNat 4
/-- `ra = (w >> 4) & 0xF`. -/
theorem ass2_field_ra (w : UInt32) : ((w >>> 4) &&& 0xF).toNat = w.toNat / 16 % 16 :=
  u32_field w 4 0xF 4 4 (by decide) (by decide)
/-- `rb = (w >> 8) & 0xF`. -/
theorem ass2_field_rb (w : UInt32) : ((w >>> 8) &&& 0xF).toNat = w.toNat / 256 % 16 :=
  u32_field w 8 0xF 8 4 (by decide) (by decide)
/-- `rc = (w >> 12) & 0xF`. -/
theorem ass2_field_rc (w : UInt32) : ((w >>> 12) &&& 0xF).toNat = w.toNat / 4096 % 16 :=
  u32_field w 12 0xF 12 4 (by decide) (by decide)
/-- `sub = (w >> 16) & 0xF`. -/
theorem ass2_field_sub (w : UInt32) : ((w >>> 16) &&& 0xF).toNat = w.toNat / 65536 % 16 :=
  u32_field w 16 0xF 16 4 (by decide) (by decide)
/-- `imm8 = (w >> 20) & 0xFF`. -/
theorem ass2_field_imm8 (w : UInt32) : ((w >>> 20) &&& 0xFF).toNat = w.toNat / 1048576 % 256 :=
  u32_field w 20 0xFF 20 8 (by decide) (by decide)
/-- `imm16 = (w >> 12) & 0xFFFF`. -/
theorem ass2_field_imm16 (w : UInt32) :
    ((w >>> 12) &&& 0xFFFF).toNat = w.toNat / 4096 % 65536 :=
  u32_field w 12 0xFFFF 12 16 (by decide) (by decide)
/-- `imm20 = (w >> 8) & 0xFFFFF`. -/
theorem ass2_field_imm20 (w : UInt32) :
    ((w >>> 8) &&& 0xFFFFF).toNat = w.toNat / 256 % 1048576 :=
  u32_field w 8 0xFFFFF 8 20 (by decide) (by decide)
/-- `imm24 = (w >> 4) & 0xFFFFFF`. -/
theorem ass2_field_imm24 (w : UInt32) :
    ((w >>> 4) &&& 0xFFFFFF).toNat = w.toNat / 16 % 16777216 :=
  u32_field w 4 0xFFFFFF 4 24 (by decide) (by decide)

/-! ## 9. Known encodings and rejected words -/

/-- The all-zero word is `EXC`, the software trap. -/
theorem decodeAss2_zero : decodeAss2 0x00000000 = some .exc := by decide
/-- `NOP` is `0x0006_0000`. -/
theorem decodeAss2_nop : decodeAss2 0x00060000 = some .nop := by decide
/-- A `NOP` with a nonzero reserved field is illegal. -/
theorem decodeAss2_nop_reserved_bit : decodeAss2 0x00060001 = none := by decide
/-- `SYS` sub-opcode 7 is reserved. -/
theorem decodeAss2_sys_reserved_sub : decodeAss2 0x00070000 = none := by decide
/-- `KECCAK.F1600` with a round count other than 12 or 24 is illegal. -/
theorem decodeAss2_keccak_13_rounds : decodeAss2 0xF0D00000 = none := by decide
/-- `SGET` from lane 25 is illegal. -/
theorem decodeAss2_sget_lane_25 : decodeAss2 0xC0019001 = none := by decide
/-- `FP5.MUL` naming quintic register 5 is illegal. -/
theorem decodeAss2_fp5_mul_register_5 : decodeAss2 0xD0040005 = none := by decide

/-- Words produced by the encoders of the reference model `ass2_model.py`, one or more per
    major opcode, decode to the instruction they were built from. -/
theorem decodeAss2_reference_model_words :
    decodeAss2 0x04020005 = some (.csrr 5 0x40#8) ∧
    decodeAss2 0x04130070 = some (.csrw 7 0x41#8) ∧
    decodeAss2 0x10060321 = some (.lut4 6 1 2 3) ∧
    decodeAss2 0x20080321 = some (.alu .mulhu64 1 2 3) ∧
    decodeAss2 0x3BEEF954 = some (.alui .slk16 4 5 0xBEEF#16) ∧
    decodeAss2 0x3003F754 = some (.alui .asri 4 5 63#16) ∧
    decodeAss2 0x4ABCDE29 = some (.auipc 9 0xABCDE#20) ∧
    decodeAss2 0x5000D321 = some (.cmp 13 1 2 3) ∧
    decodeAss2 0x60004321 = some (.sel 1 2 3 4) ∧
    decodeAss2 0x60025321 = some (.bexts 1 2 3 5) ∧
    decodeAss2 0x60010721 = some (.bextu 1 2 7 0) ∧
    decodeAss2 0x60030076 = some (.bswap64 6 7) ∧
    decodeAss2 0x7FFFD021 = some (.ld64 1 2 0xFFFD#16) ∧
    decodeAss2 0x70005121 = some (.ldbu 1 2 5#16) ∧
    decodeAss2 0x8FFFF029 = some (.st64 9 2 0xFFFF#16) ∧
    decodeAss2 0x80007129 = some (.stb 9 2 7#16) ∧
    decodeAss2 0x9FFFFE16 = some (.br .bnez 6 0xFFFFE#20) ∧
    decodeAss2 0x90000936 = some (.br .bgez 6 9#20) ∧
    decodeAss2 0xAFFFFFC3 = some (.jal 3 0xFFFFFC#24) ∧
    decodeAss2 0xB0000033 = some (.jalr 3 3 0#16) ∧
    decodeAss2 0xC0018005 = some (.sget 5 24#8) ∧
    decodeAss2 0xC0007160 = some (.sput 7#8 6) ∧
    decodeAss2 0xC00102E0 = some (.sxor 16#8 14) ∧
    decodeAss2 0xC0000300 = some (.szero) ∧
    decodeAss2 0xC8003420 = some (.sld64 3#8 2 0x80#8) ∧
    decodeAss2 0xC0104520 = some (.sst64 4#8 2 1#8) ∧
    decodeAss2 0xD0004321 = some (.glMac 1 2 3 4) ∧
    decodeAss2 0xD0030021 = some (.glSbox7 1 2) ∧
    decodeAss2 0xD0040011 = some (.fp5Mul 1 1 0) ∧
    decodeAss2 0xD0060234 = some (.fp5Sub 4 3 2) ∧
    decodeAss2 0xE00009AB = some (.gf128Mul 11 10 9) ∧
    decodeAss2 0xE0010210 = some (.gf128Xor 0 1 2) ∧
    decodeAss2 0xF0C00000 = some (.keccak 12#8) ∧
    decodeAss2 0xF1800000 = some (.keccak 24#8) ∧
    decodeAss2 0xF0010000 = some (.poseidon2Gl24) ∧
    decodeAss2 0xF0020000 = some (.poseidon2Gl12) := by
  decide

#verify_constructive
  Qsag.Ass2.encodeNat_lt
  Qsag.Ass2.decodeNat_encodeNat
  Qsag.Ass2.decodeNat_sound
  Qsag.Ass2.decodeAss2_encodeAss2
  Qsag.Ass2.encodeAss2_decodeAss2
  Qsag.Ass2.decodeAss2_eq_some_iff
  Qsag.Ass2.encodeAss2_injective
  Qsag.Ass2.ass2_field_op
  Qsag.Ass2.ass2_field_rd
  Qsag.Ass2.ass2_field_ra
  Qsag.Ass2.ass2_field_rb
  Qsag.Ass2.ass2_field_rc
  Qsag.Ass2.ass2_field_sub
  Qsag.Ass2.ass2_field_imm8
  Qsag.Ass2.ass2_field_imm16
  Qsag.Ass2.ass2_field_imm20
  Qsag.Ass2.ass2_field_imm24
  Qsag.Ass2.decodeAss2_zero
  Qsag.Ass2.decodeAss2_nop
  Qsag.Ass2.decodeAss2_nop_reserved_bit
  Qsag.Ass2.decodeAss2_sys_reserved_sub
  Qsag.Ass2.decodeAss2_keccak_13_rounds
  Qsag.Ass2.decodeAss2_sget_lane_25
  Qsag.Ass2.decodeAss2_fp5_mul_register_5
  Qsag.Ass2.decodeAss2_reference_model_words

end Qsag.Ass2
