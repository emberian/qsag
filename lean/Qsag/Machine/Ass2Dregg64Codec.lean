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

