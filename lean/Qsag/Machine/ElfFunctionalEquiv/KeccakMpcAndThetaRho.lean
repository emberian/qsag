module

public import Qsag.Machine.ElfFunctionalEquiv.SimdAndScalarKernels
import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd String.instLawfulEqOrd
  Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

/-- Refutes an equation between concrete Keccak states by exhibiting a differing lane. -/
local macro "kstate_ne" : tactic => `(tactic| first | exact fun h => absurd (congrArg KState.a0 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a1 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a2 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a3 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a4 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a5 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a6 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a7 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a8 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a9 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a10 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a11 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a12 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a13 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a14 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a15 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a16 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a17 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a18 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a19 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a20 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a21 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a22 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a23 h) (by decide +kernel) | exact fun h => absurd (congrArg KState.a24 h) (by decide +kernel))

attribute [local simp]
  X86BvState.ofX86State Arm64BvState.ofArm64State bank16OfU64 bank32OfU64
  b16get_0 b16get_1 b16get_2 b16get_3 b16get_4 b16get_5 b16get_6 b16get_7
  b16get_8 b16get_9 b16get_10 b16get_11 b16get_12 b16get_13 b16get_14 b16get_15
  b32get_0 b32get_1 b32get_2


section KeccakMpcFreshVerification
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def keccakChiMpcName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 99, 104, 105, 95, 109, 112, 99, 95, 97, 118, 120, 50]

def keccakChiMpcProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨4, 5, .vload true 1 (.baseDisp 6 32)⟩,
  ⟨9, 5, .vload true 2 (.baseDisp 6 64)⟩,
  ⟨14, 5, .vload true 3 (.baseDisp 6 96)⟩,
  ⟨19, 8, .vload true 4 (.baseDisp 6 128)⟩,
  ⟨27, 4, .vload true 5 (.baseDisp 2 0)⟩,
  ⟨31, 5, .vload true 6 (.baseDisp 2 32)⟩,
  ⟨36, 5, .vload true 7 (.baseDisp 2 64)⟩,
  ⟨41, 5, .vload true 8 (.baseDisp 2 96)⟩,
  ⟨46, 8, .vload true 9 (.baseDisp 2 128)⟩,
  ⟨54, 4, .vbinOp .vpxor true 10 2 7⟩,
  ⟨58, 4, .vbinOp .vpand true 10 10 1⟩,
  ⟨62, 4, .vbinOp .vpand true 11 6 2⟩,
  ⟨66, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨71, 4, .vbinOp .vpxor true 11 0 2⟩,
  ⟨75, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨80, 4, .vpxorLoad256 10 10 (.baseDisp 1 0)⟩,
  ⟨84, 4, .vstore true 10 (.baseDisp 7 0)⟩,
  ⟨88, 4, .vbinOp .vpxor true 10 8 3⟩,
  ⟨92, 4, .vbinOp .vpand true 10 10 2⟩,
  ⟨96, 4, .vbinOp .vpand true 11 7 3⟩,
  ⟨100, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨105, 4, .vbinOp .vpxor true 11 1 3⟩,
  ⟨109, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨114, 5, .vpxorLoad256 10 10 (.baseDisp 1 32)⟩,
  ⟨119, 5, .vstore true 10 (.baseDisp 7 32)⟩,
  ⟨124, 4, .vbinOp .vpxor true 10 9 4⟩,
  ⟨128, 4, .vbinOp .vpand true 10 10 3⟩,
  ⟨132, 4, .vbinOp .vpand true 11 8 4⟩,
  ⟨136, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨141, 4, .vbinOp .vpxor true 11 2 4⟩,
  ⟨145, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨150, 5, .vpxorLoad256 10 10 (.baseDisp 1 64)⟩,
  ⟨155, 5, .vstore true 10 (.baseDisp 7 64)⟩,
  ⟨160, 4, .vbinOp .vpxor true 10 0 5⟩,
  ⟨164, 4, .vbinOp .vpand true 10 10 4⟩,
  ⟨168, 4, .vbinOp .vpand true 11 9 0⟩,
  ⟨172, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨177, 4, .vbinOp .vpxor true 11 3 0⟩,
  ⟨181, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨186, 5, .vpxorLoad256 10 10 (.baseDisp 1 96)⟩,
  ⟨191, 5, .vstore true 10 (.baseDisp 7 96)⟩,
  ⟨196, 4, .vbinOp .vpxor true 10 1 6⟩,
  ⟨200, 4, .vbinOp .vpand true 10 10 0⟩,
  ⟨204, 4, .vbinOp .vpand true 11 5 1⟩,
  ⟨208, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨213, 4, .vbinOp .vpxor true 11 4 1⟩,
  ⟨217, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨222, 8, .vpxorLoad256 10 10 (.baseDisp 1 128)⟩,
  ⟨230, 8, .vstore true 10 (.baseDisp 7 128)⟩,
  ⟨238, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨242, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨246, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨250, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨254, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨258, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨262, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨266, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨270, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨275, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨280, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨285, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨290, 3, .vzeroall⟩,
  ⟨293, 3, .vzeroupper⟩,
  ⟨296, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨298, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨300, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨302, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨304, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨307, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨310, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨313, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨316, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨318, 1, .ret⟩
]

theorem keccakChiMpc_decoded :
    (findSliceByNameBytes currentX86ExtractedSlices keccakChiMpcName).bind
      (fun sl => decodeX86Stream sl.code) = some keccakChiMpcProg := by decide +kernel


/-- One party's RSS share of a Keccak chi gate. `a,b,c` belong to its first
share, and `bNext,cNext` to the next party's share; `r` is its zero-share mask. -/
def keccakChiMpcShareWord (a b c bNext cNext r : UInt64) : UInt64 :=
  (((c ^^^ cNext) &&& b) ^^^ (bNext &&& c)) ^^^ (a ^^^ c) ^^^ r

private theorem keccakChiMpc_bool_identity :
    ∀ (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : Bool),
    ((((((c0 ^^ c1) && b0) ^^ (b1 && c0)) ^^ (a0 ^^ c0)) ^^ r0) ^^
    (((((c1 ^^ c2) && b1) ^^ (b2 && c1)) ^^ (a1 ^^ c1)) ^^ r1) ^^
    (((((c2 ^^ c0) && b2) ^^ (b0 && c2)) ^^ (a2 ^^ c2)) ^^ r2)) =
      (keccakChiBit (a0 ^^ a1 ^^ a2) (b0 ^^ b1 ^^ b2) (c0 ^^ c1 ^^ c2) ^^
        (r0 ^^ r1 ^^ r2)) := by
  decide +kernel

/-- Three cyclic RSS parties reconstruct ordinary chi, with all masks exposed. -/
theorem keccakChiMpcShareWord_reconstruct
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : UInt64)
    (hr : r0 ^^^ r1 ^^^ r2 = 0) :
    keccakChiMpcShareWord a0 b0 c0 b1 c1 r0 ^^^
      keccakChiMpcShareWord a1 b1 c1 b2 c2 r1 ^^^
      keccakChiMpcShareWord a2 b2 c2 b0 c0 r2 =
    (a0 ^^^ a1 ^^^ a2) ^^^ ((~~~(b0 ^^^ b1 ^^^ b2)) &&& (c0 ^^^ c1 ^^^ c2)) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm := congrArg (fun x : UInt64 => x.toBitVec.getLsbD i) hr
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor] at hm
  have hzero : (0 : UInt64).toBitVec.getLsbD i = false := by simp
  rw [hzero] at hm
  rw [chiWordBit_eq_keccakChiBit _ _ _ i hi]
  simp only [keccakChiMpcShareWord, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]
  rw [keccakChiMpc_bool_identity, hm, Bool.xor_false]

/-- All 64 bits of each reconstructed word are the canonical boolean chi gate. -/
theorem keccakChiMpcShareWord_reconstruct_bit
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : UInt64)
    (hr : r0 ^^^ r1 ^^^ r2 = 0) (i : Nat) (hi : i < 64) :
    (keccakChiMpcShareWord a0 b0 c0 b1 c1 r0 ^^^
      keccakChiMpcShareWord a1 b1 c1 b2 c2 r1 ^^^
      keccakChiMpcShareWord a2 b2 c2 b0 c0 r2).toBitVec.getLsbD i =
    keccakChiBit ((a0 ^^^ a1 ^^^ a2).toBitVec.getLsbD i)
      ((b0 ^^^ b1 ^^^ b2).toBitVec.getLsbD i)
      ((c0 ^^^ c1 ^^^ c2).toBitVec.getLsbD i) := by
  rw [keccakChiMpcShareWord_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ hr]
  exact chiWordBit_eq_keccakChiBit _ _ _ i hi

/-- The five 256-bit vectors are five chi row coordinates, each containing four
independent 64-bit words. They are not two XOR-reconstructed shares of a state. -/
def keccakChiMpcRowWord (s t r : Nat → Nat → UInt64) (x q : Nat) : UInt64 :=
  keccakChiMpcShareWord (s x q) (s ((x + 1) % 5) q) (s ((x + 2) % 5) q)
    (t ((x + 1) % 5) q) (t ((x + 2) % 5) q) (r x q)

/-- Embed any one of the four independent input rows in the first row of a
Keccak state. The unused rows are zero and stay zero under chi. -/
def keccakChiMpcRowState (s : Nat → Nat → UInt64) (q : Nat) : KState :=
  ⟨s 0 q, s 1 q, s 2 q, s 3 q, s 4 q,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Every one of the four rows (all 5 × 256 boolean gates) reconstructs to
`Keccak.chiS`; masks may vary independently between coordinates and words. -/
theorem keccakChiMpcRow_reconstruct
    (s0 s1 s2 r0 r1 r2 : Nat → Nat → UInt64)
    (hr : ∀ x q : Nat, x < 5 → q < 4 → r0 x q ^^^ r1 x q ^^^ r2 x q = 0)
    (q : Nat) (hq : q < 4) :
    keccakChiMpcRowState (fun x j =>
      keccakChiMpcRowWord s0 s1 r0 x j ^^^ keccakChiMpcRowWord s1 s2 r1 x j ^^^
        keccakChiMpcRowWord s2 s0 r2 x j) q =
    chiS (keccakChiMpcRowState (fun x j => s0 x j ^^^ s1 x j ^^^ s2 x j) q) := by
  unfold keccakChiMpcRowState chiS keccakChiMpcRowWord
  dsimp only
  congr 1
  all_goals first
    | exact keccakChiMpcShareWord_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ (hr _ q (by decide) hq)
    | rfl

/-- Omitting the linear `c` contribution is a wrong specification: even a
single set input bit with zero neighbours must survive the NOT term. -/
theorem keccakChiMpcShareWord_tooth :
    keccakChiMpcShareWord 0 0 1 0 0 0 ≠ (0 : UInt64) := by
  decide +kernel

theorem keccakChiMpcRow_inhabited :
    ∃ (s0 s1 s2 r0 r1 r2 : Nat → Nat → UInt64) (q : Nat),
      (∀ x j : Nat, x < 5 → j < 4 → r0 x j ^^^ r1 x j ^^^ r2 x j = 0) ∧
      q < 4 ∧ keccakChiMpcRowState s0 q = zeroKState ∧
      keccakChiMpcRowState s1 q = zeroKState ∧ keccakChiMpcRowState s2 q = zeroKState := by
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0),
    (fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0), 0, ?_, by decide, (by rw [zeroKState_eq]; rfl), (by rw [zeroKState_eq]; rfl), (by rw [zeroKState_eq]; rfl)⟩
  intro _ _ _ _
  change (0 : UInt64) ^^^ 0 ^^^ 0 = 0
  decide +kernel

#tooth_pair keccakChiMpcRow_reconstruct vs keccakChiMpcShareWord_tooth
#verify_inhabited keccakChiMpcRow_reconstruct keccakChiMpcRow_inhabited

theorem keccakChiMpc_readMem64_writeMem256_disjoint
    (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec256)
    (hd : ∀ i k : Nat, i < 8 → k < 32 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem64 (writeMem256 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem256_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 7 · (by decide))]

theorem keccakChiMpc_readMem256_writeMem256_disjoint
    (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec256)
    (hd : ∀ i k : Nat, i < 32 → k < 32 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem256 (writeMem256 mem a2 v) a1 = readMem256 mem a1 := by
  have h (off : Nat) (ho : off ≤ 24) :
      readMem64 (writeMem256 mem a2 v) (a1 + UInt64.ofNat off) =
        readMem64 mem (a1 + UInt64.ofNat off) := by
    apply keccakChiMpc_readMem64_writeMem256_disjoint
    intro i k hi hk heq
    rw [u64_add_ofNat_assoc a1 off i (by omega)] at heq
    exact hd (off + i) k (by omega) hk heq
  unfold readMem256
  have h0 := h 0 (by decide)
  have hz : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  rw [hz, UInt64.add_zero] at h0
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have h16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have h24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [← h8, ← h16, ← h24]
  rw [h0, h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem keccakChiMpc_readMem256_writeMem256_same
    (mem : UInt64 → UInt8) (a : UInt64) (v : Vec256) :
    readMem256 (writeMem256 mem a v) a = v := by
  have hd (o1 o2 : Nat) (h1 : o1 ≤ 24) (h2 : o2 ≤ 24)
      (hne : o1 + 8 ≤ o2 ∨ o2 + 8 ≤ o1)
      (m : UInt64 → UInt8) (w : UInt64) :
      readMem64 (writeMem64 m (a + UInt64.ofNat o2) w) (a + UInt64.ofNat o1) =
        readMem64 m (a + UInt64.ofNat o1) := by
    apply readMem64_writeMem64_disjoint
    intro i j hi hj heq
    rw [u64_add_ofNat_assoc a o1 i (by omega),
      u64_add_ofNat_assoc a o2 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  have hd0 (o2 : Nat) (h2 : o2 ≤ 24) (hne : 8 ≤ o2)
      (m : UInt64 → UInt8) (w : UInt64) :
      readMem64 (writeMem64 m (a + UInt64.ofNat o2) w) a = readMem64 m a := by
    have hz : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
    simpa only [hz, UInt64.add_zero] using hd 0 o2 (by decide) h2 (Or.inl hne) m w
  unfold readMem256 writeMem256
  dsimp only
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have h16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have h24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [← h8, ← h16, ← h24]
  rw [hd0 24 (by decide) (by decide), hd0 16 (by decide) (by decide),
    hd0 8 (by decide) (by decide), readMem64_writeMem64_same,
    hd 8 24 (by decide) (by decide) (by omega),
    hd 8 16 (by decide) (by decide) (by omega), readMem64_writeMem64_same,
    hd 16 24 (by decide) (by decide) (by omega), readMem64_writeMem64_same,
    readMem64_writeMem64_same]


/-- Output stores may alias the two input share rows (which are loaded first),
but not the mask row, which is read incrementally. -/
def keccakChiMpcSeparated (dst mask : UInt64) : Prop :=
  ∀ i j : Nat, i < 160 → j < 160 → dst + UInt64.ofNat i ≠ mask + UInt64.ofNat j

private theorem keccakChiMpc_maskRead (mem : UInt64 → UInt8) (dst mask : UInt64)
    (h : keccakChiMpcSeparated dst mask) (i j : Nat) (hi : i ≤ 128) (hj : j ≤ 128)
    (v : Vec256) :
    readMem256 (writeMem256 mem (dst + UInt64.ofNat i) v) (mask + UInt64.ofNat j) =
      readMem256 mem (mask + UInt64.ofNat j) := by
  apply keccakChiMpc_readMem256_writeMem256_disjoint
  intro k l hk hl he
  rw [u64_add_ofNat_assoc mask j k (by omega),
    u64_add_ofNat_assoc dst i l (by omega)] at he
  exact h (i + l) (j + k) (by omega) (by omega) he.symm

/-- Four independent words of a single RSS output coordinate. -/
def keccakChiMpcShareVec (a b c bn cn r : Vec256) : Vec256 :=
  ⟨keccakChiMpcShareWord a.w0 b.w0 c.w0 bn.w0 cn.w0 r.w0,
   keccakChiMpcShareWord a.w1 b.w1 c.w1 bn.w1 cn.w1 r.w1,
   keccakChiMpcShareWord a.w2 b.w2 c.w2 bn.w2 cn.w2 r.w2,
   keccakChiMpcShareWord a.w3 b.w3 c.w3 bn.w3 cn.w3 r.w3⟩

def keccakChiMpcOutVec (mem : UInt64 → UInt8) (s0 s1 mask : UInt64) (x : Nat) : Vec256 :=
  keccakChiMpcShareVec (readMem256 mem (s0 + UInt64.ofNat (32 * x)))
    (readMem256 mem (s0 + UInt64.ofNat (32 * ((x + 1) % 5))))
    (readMem256 mem (s0 + UInt64.ofNat (32 * ((x + 2) % 5))))
    (readMem256 mem (s1 + UInt64.ofNat (32 * ((x + 1) % 5))))
    (readMem256 mem (s1 + UInt64.ofNat (32 * ((x + 2) % 5))))
    (readMem256 mem (mask + UInt64.ofNat (32 * x)))

/-- The entire 160-byte RSS chi output, all five coordinates and all four words. -/
def keccakChiMpcOutMem (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64) : UInt64 → UInt8 :=
  let m0 := writeMem256 mem (dst + 0) (keccakChiMpcOutVec mem s0 s1 mask 0)
  let m1 := writeMem256 m0 (dst + 32) (keccakChiMpcOutVec mem s0 s1 mask 1)
  let m2 := writeMem256 m1 (dst + 64) (keccakChiMpcOutVec mem s0 s1 mask 2)
  let m3 := writeMem256 m2 (dst + 96) (keccakChiMpcOutVec mem s0 s1 mask 3)
  let m4 := writeMem256 m3 (dst + 128) (keccakChiMpcOutVec mem s0 s1 mask 4)
  m4

private theorem keccakChiMpc_xor_comm (a b : UInt64) : a ^^^ b = b ^^^ a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_xor, BitVec.xor_comm]

private theorem keccakChiMpc_loads (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 10
      ⟨0, g, y, cf, o, zf, dy, false, m⟩
      ⟨54, g, ⟨readMem256 m (g.get 6 + 0), readMem256 m (g.get 6 + 32), readMem256 m (g.get 6 + 64), readMem256 m (g.get 6 + 96), readMem256 m (g.get 6 + 128), readMem256 m (g.get 2 + 0), readMem256 m (g.get 2 + 32), readMem256 m (g.get 2 + 64), readMem256 m (g.get 2 + 96), readMem256 m (g.get 2 + 128), y.get 10, y.get 11, y.get 12, y.get 13, y.get 14, y.get 15⟩, cf, o, zf, true, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 10
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, Bool.or_true]
      rfl
  exact StepsX86.zero _

private theorem keccakChiMpc_lane0 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨54, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨88, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (g.get 1 + 0))), (evalVecBin256 .vpxor a0 a2), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 0) (keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (g.get 1 + 0))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_lane1 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨88, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨124, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (g.get 1 + 32))), (evalVecBin256 .vpxor a1 a3), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 32) (keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (g.get 1 + 32))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  rw [keccakChiMpc_xor_comm b3.w0 a3.w0]
  rw [keccakChiMpc_xor_comm b3.w1 a3.w1]
  rw [keccakChiMpc_xor_comm b3.w2 a3.w2]
  rw [keccakChiMpc_xor_comm b3.w3 a3.w3]
  exact StepsX86.zero _

private theorem keccakChiMpc_lane2 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨124, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨160, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (g.get 1 + 64))), (evalVecBin256 .vpxor a2 a4), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 64) (keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (g.get 1 + 64))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  rw [keccakChiMpc_xor_comm b4.w0 a4.w0]
  rw [keccakChiMpc_xor_comm b4.w1 a4.w1]
  rw [keccakChiMpc_xor_comm b4.w2 a4.w2]
  rw [keccakChiMpc_xor_comm b4.w3 a4.w3]
  exact StepsX86.zero _

private theorem keccakChiMpc_lane3 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨160, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨196, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (g.get 1 + 96))), (evalVecBin256 .vpxor a3 a0), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 96) (keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (g.get 1 + 96))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_lane4 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨196, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨238, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (g.get 1 + 128))), (evalVecBin256 .vpxor a4 a1), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 128) (keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (g.get 1 + 128))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_cleanup
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 24
      ⟨238, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, true, false, m⟩
      ⟨(readMem64 m r4).toNat, ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero, false, false, true, false, true, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 12
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get,
        evalVecBin256, u64_xor_self]
      rfl
  iterate 11
    apply StepsX86.cons rfl rfl
    · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR,
        mask32_xor_self, u64_zero_beq_zero,
        b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
        b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  apply StepsX86.cons rfl rfl rfl
  exact StepsX86.zero _

private theorem keccakChiMpc_reaches
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8)
    (h : keccakChiMpcSeparated r7 r1) :
    ExecReachesX86 keccakChiMpcProg 74
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩
      ⟨(readMem64 (keccakChiMpcOutMem m r7 r6 r2 r1) r4).toNat, ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero, false, false, true, false, true, (keccakChiMpcOutMem m r7 r6 r2 r1)⟩ := by
  let g : Bank16 UInt64 := ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩

  let a0 := readMem256 m (r6 + 0)
  let a1 := readMem256 m (r6 + 32)
  let a2 := readMem256 m (r6 + 64)
  let a3 := readMem256 m (r6 + 96)
  let a4 := readMem256 m (r6 + 128)
  let b0 := readMem256 m (r2 + 0)
  let b1 := readMem256 m (r2 + 32)
  let b2 := readMem256 m (r2 + 64)
  let b3 := readMem256 m (r2 + 96)
  let b4 := readMem256 m (r2 + 128)
  let v0 := keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (r1 + 0))
  let t0 := evalVecBin256 .vpxor a0 a2
  let m0 := writeMem256 m (r7 + 0) v0
  let v1 := keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (r1 + 32))
  let t1 := evalVecBin256 .vpxor a1 a3
  let m1 := writeMem256 m0 (r7 + 32) v1
  let v2 := keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (r1 + 64))
  let t2 := evalVecBin256 .vpxor a2 a4
  let m2 := writeMem256 m1 (r7 + 64) v2
  let v3 := keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (r1 + 96))
  let t3 := evalVecBin256 .vpxor a3 a0
  let m3 := writeMem256 m2 (r7 + 96) v3
  let v4 := keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (r1 + 128))
  let t4 := evalVecBin256 .vpxor a4 a1
  let m4 := writeMem256 m3 (r7 + 128) v4
  have hn0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have hn32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
  have hn64 : UInt64.ofNat 64 = (64 : UInt64) := by decide +kernel
  have hn96 : UInt64.ofNat 96 = (96 : UInt64) := by decide +kernel
  have hn128 : UInt64.ofNat 128 = (128 : UInt64) := by decide +kernel
  have hr0_1 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 32) = readMem256 mm (r1 + 32) := by
    simpa only [hn0, hn32] using
      keccakChiMpc_maskRead mm r7 r1 h 0 32 (by decide) (by decide) v
  have hr0_2 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 64) = readMem256 mm (r1 + 64) := by
    simpa only [hn0, hn64] using
      keccakChiMpc_maskRead mm r7 r1 h 0 64 (by decide) (by decide) v
  have hr1_2 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 64) = readMem256 mm (r1 + 64) := by
    simpa only [hn32, hn64] using
      keccakChiMpc_maskRead mm r7 r1 h 32 64 (by decide) (by decide) v
  have hr0_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn0, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 0 96 (by decide) (by decide) v
  have hr1_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn32, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 32 96 (by decide) (by decide) v
  have hr2_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 64) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn64, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 64 96 (by decide) (by decide) v
  have hr0_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn0, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 0 128 (by decide) (by decide) v
  have hr1_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn32, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 32 128 (by decide) (by decide) v
  have hr2_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 64) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn64, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 64 128 (by decide) (by decide) v
  have hr3_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 96) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn96, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 96 128 (by decide) (by decide) v
  have hp := keccakChiMpc_loads g y cf o zf dy m
  have he0 := keccakChiMpc_lane0 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (y.get 10) (y.get 11) (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m
  have he1 := keccakChiMpc_lane1 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v0 t0 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m0
  simp only [g, Bank16.get, m0, hr0_1] at he1
  have he2 := keccakChiMpc_lane2 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v1 t1 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m1
  simp only [g, Bank16.get, m0, m1, hr1_2, hr0_2] at he2
  have he3 := keccakChiMpc_lane3 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v2 t2 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m2
  simp only [g, Bank16.get, m0, m1, m2, hr2_3, hr1_3, hr0_3] at he3
  have he4 := keccakChiMpc_lane4 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v3 t3 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m3
  simp only [g, Bank16.get, m0, m1, m2, m3, hr3_4, hr2_4, hr1_4, hr0_4] at he4
  have ht := keccakChiMpc_cleanup r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, v4, t4, (y.get 12), (y.get 13), (y.get 14), (y.get 15)⟩ cf o zf m4
  have hall := ExecReachesX86_trans hp (ExecReachesX86_trans he0 (ExecReachesX86_trans he1
    (ExecReachesX86_trans he2 (ExecReachesX86_trans he3 (ExecReachesX86_trans he4 ht)))))
  have hm4 : m4 = keccakChiMpcOutMem m r7 r6 r2 r1 := by
    simp only [m4, m3, m2, m1, m0, v0, v1, v2, v3, v4,
      a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, keccakChiMpcOutMem, keccakChiMpcOutVec]
    simp only [hn0, hn32, hn64, hn96, hn128]
  rw [hm4] at hall
  exact hall


/-- Entry and aliasing preconditions, with no restriction on secret data or registers. -/
def keccakChiMpcInitial (s : X86State) : Prop :=
  s.pc = 0 ∧ s.halted = false ∧ keccakChiMpcSeparated (s.gpr.get 7) (s.gpr.get 1)

/-- Fresh AVX2 execution computes every byte of all five 256-bit RSS chi shares. -/
theorem keccakChiMpc_current_functional (s : X86State) (h : keccakChiMpcInitial s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices
        keccakChiMpcName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        (runX86 prog (74 + extra) s).1.halted = true ∧
        (runX86 prog (74 + extra) s).1.mem =
          keccakChiMpcOutMem s.mem (s.gpr.get 7) (s.gpr.get 6) (s.gpr.get 2) (s.gpr.get 1) := by
  have hd := keccakChiMpc_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices
      keccakChiMpcName with
  | none => rw [hf] at hd; contradiction
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccakChiMpcProg, rfl, hd, ?_⟩
    rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    rcases h with ⟨hp, hh, hdisj⟩
    dsimp only at hp hh
    subst pc hlt
    intro extra
    have he := (keccakChiMpc_reaches r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
      r12 r13 r14 r15 y cf o zf dy mem hdisj).run extra |>.1
    let t : X86State :=
      ⟨(readMem64 (keccakChiMpcOutMem mem r7 r6 r2 r1) r4).toNat,
        ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        Bank16.const Vec256.zero, false, false, true, false, true,
        keccakChiMpcOutMem mem r7 r6 r2 r1⟩
    rw [runX86_halted_fst keccakChiMpcProg extra t rfl] at he
    rw [he]
    exact ⟨rfl, rfl⟩

theorem keccakChiMpc_inhabited : ∃ s : X86State, keccakChiMpcInitial s := by
  refine ⟨⟨0, Bank16.ofFn (fun i => if i == 1 then 256 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, ?_⟩
  change keccakChiMpcSeparated 0 256
  intro i j hi hj he
  have hn := congrArg UInt64.toNat he
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
  omega

/-- The wrong specification that always writes zero fails on a single set input bit. -/
theorem keccakChiMpc_current_tooth :
    keccakChiMpcOutMem (fun a => if a == 64 then 1 else 0) 1024 0 256 512 1024 ≠ 0 := by
  decide +kernel

#tooth_pair keccakChiMpc_current_functional vs keccakChiMpc_current_tooth
#verify_inhabited keccakChiMpc_current_functional keccakChiMpc_inhabited

/-- Select one of the four 64-bit words of a vector (`q < 4` at callers). -/
def keccakChiMpcVecWord (v : Vec256) : Nat → UInt64
  | 0 => v.w0
  | 1 => v.w1
  | 2 => v.w2
  | _ => v.w3

def keccakChiMpcReadRows (mem : UInt64 → UInt8) (ptr : UInt64) (x q : Nat) : UInt64 :=
  keccakChiMpcVecWord (readMem256 mem (ptr + UInt64.ofNat (32 * x))) q

theorem keccakChiMpcOutVec_word (mem : UInt64 → UInt8) (s0 s1 mask : UInt64) (x q : Nat) :
    keccakChiMpcVecWord (keccakChiMpcOutVec mem s0 s1 mask x) q =
      keccakChiMpcRowWord (keccakChiMpcReadRows mem s0)
        (keccakChiMpcReadRows mem s1) (keccakChiMpcReadRows mem mask) x q := by
  match q with
  | 0 | 1 | 2 | _ + 3 => rfl

/-- All five vector stores read back in their entirety, including wrapping
addresses; distinct offsets below 160 remain distinct modulo 2^64. -/
theorem keccakChiMpcOutMem_readback (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64)
    (x : Nat) (hx : x < 5) :
    readMem256 (keccakChiMpcOutMem mem dst s0 s1 mask)
      (dst + UInt64.ofNat (32 * x)) = keccakChiMpcOutVec mem s0 s1 mask x := by
  have hd (o1 o2 : Nat) (h1 : o1 ≤ 128) (h2 : o2 ≤ 128)
      (hgap : o1 + 32 ≤ o2 ∨ o2 + 32 ≤ o1)
      (m : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 m (dst + UInt64.ofNat o2) v) (dst + UInt64.ofNat o1) =
        readMem256 m (dst + UInt64.ofNat o1) := by
    apply keccakChiMpc_readMem256_writeMem256_disjoint
    intro i j hi hj heq
    rw [u64_add_ofNat_assoc dst o1 i (by omega),
      u64_add_ofNat_assoc dst o2 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  unfold keccakChiMpcOutMem
  dsimp only
  have hn0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have hn32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
  have hn64 : UInt64.ofNat 64 = (64 : UInt64) := by decide +kernel
  have hn96 : UInt64.ofNat 96 = (96 : UInt64) := by decide +kernel
  have hn128 : UInt64.ofNat 128 = (128 : UInt64) := by decide +kernel
  rw [← hn0, ← hn32, ← hn64, ← hn96, ← hn128]
  match x, hx with
  | 0, _ =>
    rw [hd 0 128 (by decide) (by decide) (by omega),
      hd 0 96 (by decide) (by decide) (by omega),
      hd 0 64 (by decide) (by decide) (by omega),
      hd 0 32 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 1, _ =>
    rw [hd 32 128 (by decide) (by decide) (by omega),
      hd 32 96 (by decide) (by decide) (by omega),
      hd 32 64 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 2, _ =>
    rw [hd 64 128 (by decide) (by decide) (by omega),
      hd 64 96 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 3, _ =>
    rw [hd 96 128 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 4, _ => exact keccakChiMpc_readMem256_writeMem256_same _ _ _
  | _ + 5, h => omega

theorem keccakChiMpcOutMem_readRows (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64)
    (x q : Nat) (hx : x < 5) :
    keccakChiMpcReadRows (keccakChiMpcOutMem mem dst s0 s1 mask) dst x q =
      keccakChiMpcRowWord (keccakChiMpcReadRows mem s0)
        (keccakChiMpcReadRows mem s1) (keccakChiMpcReadRows mem mask) x q := by
  unfold keccakChiMpcReadRows
  rw [keccakChiMpcOutMem_readback _ _ _ _ _ x hx]
  exact keccakChiMpcOutVec_word mem s0 s1 mask x q

/-- Cyclic replicated shares agree only on the 160 bytes actually read, with no
constraints on unrelated memory, scratch registers, or output values. -/
def keccakChiMpcSharesMatch (s t : X86State) : Prop :=
  ∀ x q : Nat, x < 5 → q < 4 →
    keccakChiMpcReadRows s.mem (s.gpr.get 2) x q =
      keccakChiMpcReadRows t.mem (t.gpr.get 6) x q

def keccakChiMpcMasksZero (s0 s1 s2 : X86State) : Prop :=
  ∀ x q : Nat, x < 5 → q < 4 →
    keccakChiMpcReadRows s0.mem (s0.gpr.get 1) x q ^^^
      keccakChiMpcReadRows s1.mem (s1.gpr.get 1) x q ^^^
      keccakChiMpcReadRows s2.mem (s2.gpr.get 1) x q = 0

/-- The mathematical reconstruction of all five stored vectors, independent of
machine scheduling. This composes the byte-memory readback with the RSS identity. -/
theorem keccakChiMpcOutMem_reconstruct
    (s0 s1 s2 : X86State)
    (h01 : keccakChiMpcSharesMatch s0 s1)
    (h12 : keccakChiMpcSharesMatch s1 s2)
    (h20 : keccakChiMpcSharesMatch s2 s0)
    (hm : keccakChiMpcMasksZero s0 s1 s2) (q : Nat) (hq : q < 4) :
    keccakChiMpcRowState (fun x j =>
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s0.mem (s0.gpr.get 7) (s0.gpr.get 6) (s0.gpr.get 2) (s0.gpr.get 1))
        (s0.gpr.get 7) x j ^^^
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s1.mem (s1.gpr.get 7) (s1.gpr.get 6) (s1.gpr.get 2) (s1.gpr.get 1))
        (s1.gpr.get 7) x j ^^^
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s2.mem (s2.gpr.get 7) (s2.gpr.get 6) (s2.gpr.get 2) (s2.gpr.get 1))
        (s2.gpr.get 7) x j) q =
    chiS (keccakChiMpcRowState (fun x j =>
      keccakChiMpcReadRows s0.mem (s0.gpr.get 6) x j ^^^
      keccakChiMpcReadRows s1.mem (s1.gpr.get 6) x j ^^^
      keccakChiMpcReadRows s2.mem (s2.gpr.get 6) x j) q) := by
  let a0 := keccakChiMpcReadRows s0.mem (s0.gpr.get 6)
  let a1 := keccakChiMpcReadRows s1.mem (s1.gpr.get 6)
  let a2 := keccakChiMpcReadRows s2.mem (s2.gpr.get 6)
  let r0 := keccakChiMpcReadRows s0.mem (s0.gpr.get 1)
  let r1 := keccakChiMpcReadRows s1.mem (s1.gpr.get 1)
  let r2 := keccakChiMpcReadRows s2.mem (s2.gpr.get 1)
  have ho (s t : X86State) (hst : keccakChiMpcSharesMatch s t) (x : Nat) (hx : x < 5) :
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s.mem (s.gpr.get 7) (s.gpr.get 6) (s.gpr.get 2) (s.gpr.get 1))
        (s.gpr.get 7) x q =
      keccakChiMpcRowWord (keccakChiMpcReadRows s.mem (s.gpr.get 6))
        (keccakChiMpcReadRows t.mem (t.gpr.get 6)) (keccakChiMpcReadRows s.mem (s.gpr.get 1)) x q := by
    rw [keccakChiMpcOutMem_readRows _ _ _ _ _ x q hx]
    unfold keccakChiMpcRowWord
    rw [hst ((x + 1) % 5) q (Nat.mod_lt _ (by decide)) hq,
      hst ((x + 2) % 5) q (Nat.mod_lt _ (by decide)) hq]
  have hrecon := keccakChiMpcRow_reconstruct a0 a1 a2 r0 r1 r2 hm q hq
  calc
    _ = keccakChiMpcRowState (fun x j =>
          keccakChiMpcRowWord a0 a1 r0 x j ^^^ keccakChiMpcRowWord a1 a2 r1 x j ^^^
            keccakChiMpcRowWord a2 a0 r2 x j) q := by
      unfold keccakChiMpcRowState
      dsimp only
      congr 1
      all_goals rw [ho s0 s1 h01 _ (by decide), ho s1 s2 h12 _ (by decide),
        ho s2 s0 h20 _ (by decide)]
    _ = _ := hrecon


/-- Fresh machine-code RSS chi reconstruction for all 1,280 gates: three
cyclic-party executions halt and their complete four rows reconstruct `chiS`.
Only the input replicated shares and correlated masks are related. -/
theorem keccakChiMpc_current_reconstruct
    (s0 s1 s2 : X86State)
    (h0 : keccakChiMpcInitial s0) (h1 : keccakChiMpcInitial s1) (h2 : keccakChiMpcInitial s2)
    (h01 : keccakChiMpcSharesMatch s0 s1)
    (h12 : keccakChiMpcSharesMatch s1 s2)
    (h20 : keccakChiMpcSharesMatch s2 s0)
    (hm : keccakChiMpcMasksZero s0 s1 s2) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccakChiMpcName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        (runX86 prog (74 + extra) s0).1.halted = true ∧
        (runX86 prog (74 + extra) s1).1.halted = true ∧
        (runX86 prog (74 + extra) s2).1.halted = true ∧
        ∀ q : Nat, q < 4 →
          keccakChiMpcRowState (fun x j =>
            keccakChiMpcReadRows (runX86 prog (74 + extra) s0).1.mem (s0.gpr.get 7) x j ^^^
            keccakChiMpcReadRows (runX86 prog (74 + extra) s1).1.mem (s1.gpr.get 7) x j ^^^
            keccakChiMpcReadRows (runX86 prog (74 + extra) s2).1.mem (s2.gpr.get 7) x j) q =
          chiS (keccakChiMpcRowState (fun x j =>
            keccakChiMpcReadRows s0.mem (s0.gpr.get 6) x j ^^^
            keccakChiMpcReadRows s1.mem (s1.gpr.get 6) x j ^^^
            keccakChiMpcReadRows s2.mem (s2.gpr.get 6) x j) q) := by
  obtain ⟨sl0, p0, hf0, hd0, he0⟩ := keccakChiMpc_current_functional s0 h0
  obtain ⟨sl1, p1, hf1, hd1, he1⟩ := keccakChiMpc_current_functional s1 h1
  obtain ⟨sl2, p2, hf2, hd2, he2⟩ := keccakChiMpc_current_functional s2 h2
  have hs1 : sl1 = sl0 := Option.some.inj (hf1.symm.trans hf0)
  have hs2 : sl2 = sl0 := Option.some.inj (hf2.symm.trans hf0)
  subst sl1 sl2
  have hp1 : p1 = p0 := Option.some.inj (hd1.symm.trans hd0)
  have hp2 : p2 = p0 := Option.some.inj (hd2.symm.trans hd0)
  subst p1 p2
  refine ⟨sl0, p0, hf0, hd0, ?_⟩
  intro extra
  obtain ⟨hh0, he0⟩ := he0 extra
  obtain ⟨hh1, he1⟩ := he1 extra
  obtain ⟨hh2, he2⟩ := he2 extra
  refine ⟨hh0, hh1, hh2, ?_⟩
  intro q hq
  rw [he0, he1, he2]
  exact keccakChiMpcOutMem_reconstruct s0 s1 s2 h01 h12 h20 hm q hq

/-- A concrete valid party: disjoint output/mask buffers and zero input shares. -/
def keccakChiMpcZeroParty : X86State :=
  ⟨0, Bank16.ofFn (fun i => if i == 1 then 256 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩

theorem keccakChiMpc_reconstruct_inhabited :
    ∃ s0 s1 s2 : X86State,
      keccakChiMpcInitial s0 ∧ keccakChiMpcInitial s1 ∧ keccakChiMpcInitial s2 ∧
      keccakChiMpcSharesMatch s0 s1 ∧ keccakChiMpcSharesMatch s1 s2 ∧
      keccakChiMpcSharesMatch s2 s0 ∧ keccakChiMpcMasksZero s0 s1 s2 := by
  have hi : keccakChiMpcInitial keccakChiMpcZeroParty := by
    refine ⟨rfl, rfl, ?_⟩
    change keccakChiMpcSeparated 0 256
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  have hs : keccakChiMpcSharesMatch keccakChiMpcZeroParty keccakChiMpcZeroParty := by
    intro x q _ _
    rfl
  have hz (p : UInt64) (x q : Nat) (hq : q < 4) :
      keccakChiMpcReadRows (fun _ => 0) p x q = 0 := by
    unfold keccakChiMpcReadRows readMem256 readMem64
    dsimp only
    match q, hq with
    | 0, _ | 1, _ | 2, _ | 3, _ =>
      dsimp only [keccakChiMpcVecWord]
      decide +kernel
    | n + 4, h => omega
  refine ⟨keccakChiMpcZeroParty, keccakChiMpcZeroParty, keccakChiMpcZeroParty,
    hi, hi, hi, hs, hs, hs, ?_⟩
  intro x q _ hq
  change keccakChiMpcReadRows (fun _ => 0) 256 x q ^^^
    keccakChiMpcReadRows (fun _ => 0) 256 x q ^^^
    keccakChiMpcReadRows (fun _ => 0) 256 x q = 0
  rw [hz _ _ _ hq]
  decide +kernel

/-- The zero-output specification is refuted by a nonzero reconstructed row. -/
theorem keccakChiMpc_reconstruct_tooth :
    chiS (keccakChiMpcRowState (fun x _ => if x == 2 then 1 else 0) 0) ≠ zeroKState := by
  rw [zeroKState_eq]; kstate_ne

#tooth_pair keccakChiMpc_current_reconstruct vs keccakChiMpc_reconstruct_tooth
#verify_inhabited keccakChiMpc_current_reconstruct keccakChiMpc_reconstruct_inhabited

end KeccakMpcFreshVerification

section KeccakThetaRhoFreshVerification
set_option linter.unusedSimpArgs false

/-! Full two-sponge theta/rho/pi kernel. -/

def keccakThetaRhoProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldrQ 0 1 0⟩,
  ⟨4, 4, .ldrQ 5 1 80⟩,
  ⟨8, 4, .ldrQ 6 1 160⟩,
  ⟨12, 4, .veor3_16b 0 0 5 6⟩,
  ⟨16, 4, .ldrQ 5 1 240⟩,
  ⟨20, 4, .ldrQ 6 1 320⟩,
  ⟨24, 4, .veor3_16b 0 0 5 6⟩,
  ⟨28, 4, .ldrQ 1 1 16⟩,
  ⟨32, 4, .ldrQ 5 1 96⟩,
  ⟨36, 4, .ldrQ 6 1 176⟩,
  ⟨40, 4, .veor3_16b 1 1 5 6⟩,
  ⟨44, 4, .ldrQ 5 1 256⟩,
  ⟨48, 4, .ldrQ 6 1 336⟩,
  ⟨52, 4, .veor3_16b 1 1 5 6⟩,
  ⟨56, 4, .ldrQ 2 1 32⟩,
  ⟨60, 4, .ldrQ 5 1 112⟩,
  ⟨64, 4, .ldrQ 6 1 192⟩,
  ⟨68, 4, .veor3_16b 2 2 5 6⟩,
  ⟨72, 4, .ldrQ 5 1 272⟩,
  ⟨76, 4, .ldrQ 6 1 352⟩,
  ⟨80, 4, .veor3_16b 2 2 5 6⟩,
  ⟨84, 4, .ldrQ 3 1 48⟩,
  ⟨88, 4, .ldrQ 5 1 128⟩,
  ⟨92, 4, .ldrQ 6 1 208⟩,
  ⟨96, 4, .veor3_16b 3 3 5 6⟩,
  ⟨100, 4, .ldrQ 5 1 288⟩,
  ⟨104, 4, .ldrQ 6 1 368⟩,
  ⟨108, 4, .veor3_16b 3 3 5 6⟩,
  ⟨112, 4, .ldrQ 4 1 64⟩,
  ⟨116, 4, .ldrQ 5 1 144⟩,
  ⟨120, 4, .ldrQ 6 1 224⟩,
  ⟨124, 4, .veor3_16b 4 4 5 6⟩,
  ⟨128, 4, .ldrQ 5 1 304⟩,
  ⟨132, 4, .ldrQ 6 1 384⟩,
  ⟨136, 4, .veor3_16b 4 4 5 6⟩,
  ⟨140, 4, .vrax1_2d 16 4 1⟩,
  ⟨144, 4, .vrax1_2d 17 0 2⟩,
  ⟨148, 4, .vrax1_2d 18 1 3⟩,
  ⟨152, 4, .vrax1_2d 19 2 4⟩,
  ⟨156, 4, .vrax1_2d 20 3 0⟩,
  ⟨160, 4, .ldrQ 0 1 0⟩,
  ⟨164, 4, .vxar_2d 0 0 16 0⟩,
  ⟨168, 4, .strQ 0 0 0⟩,
  ⟨172, 4, .ldrQ 0 1 16⟩,
  ⟨176, 4, .vxar_2d 0 0 17 63⟩,
  ⟨180, 4, .strQ 0 0 160⟩,
  ⟨184, 4, .ldrQ 0 1 32⟩,
  ⟨188, 4, .vxar_2d 0 0 18 2⟩,
  ⟨192, 4, .strQ 0 0 320⟩,
  ⟨196, 4, .ldrQ 0 1 48⟩,
  ⟨200, 4, .vxar_2d 0 0 19 36⟩,
  ⟨204, 4, .strQ 0 0 80⟩,
  ⟨208, 4, .ldrQ 0 1 64⟩,
  ⟨212, 4, .vxar_2d 0 0 20 37⟩,
  ⟨216, 4, .strQ 0 0 240⟩,
  ⟨220, 4, .ldrQ 0 1 80⟩,
  ⟨224, 4, .vxar_2d 0 0 16 28⟩,
  ⟨228, 4, .strQ 0 0 256⟩,
  ⟨232, 4, .ldrQ 0 1 96⟩,
  ⟨236, 4, .vxar_2d 0 0 17 20⟩,
  ⟨240, 4, .strQ 0 0 16⟩,
  ⟨244, 4, .ldrQ 0 1 112⟩,
  ⟨248, 4, .vxar_2d 0 0 18 58⟩,
  ⟨252, 4, .strQ 0 0 176⟩,
  ⟨256, 4, .ldrQ 0 1 128⟩,
  ⟨260, 4, .vxar_2d 0 0 19 9⟩,
  ⟨264, 4, .strQ 0 0 336⟩,
  ⟨268, 4, .ldrQ 0 1 144⟩,
  ⟨272, 4, .vxar_2d 0 0 20 44⟩,
  ⟨276, 4, .strQ 0 0 96⟩,
  ⟨280, 4, .ldrQ 0 1 160⟩,
  ⟨284, 4, .vxar_2d 0 0 16 61⟩,
  ⟨288, 4, .strQ 0 0 112⟩,
  ⟨292, 4, .ldrQ 0 1 176⟩,
  ⟨296, 4, .vxar_2d 0 0 17 54⟩,
  ⟨300, 4, .strQ 0 0 272⟩,
  ⟨304, 4, .ldrQ 0 1 192⟩,
  ⟨308, 4, .vxar_2d 0 0 18 21⟩,
  ⟨312, 4, .strQ 0 0 32⟩,
  ⟨316, 4, .ldrQ 0 1 208⟩,
  ⟨320, 4, .vxar_2d 0 0 19 39⟩,
  ⟨324, 4, .strQ 0 0 192⟩,
  ⟨328, 4, .ldrQ 0 1 224⟩,
  ⟨332, 4, .vxar_2d 0 0 20 25⟩,
  ⟨336, 4, .strQ 0 0 352⟩,
  ⟨340, 4, .ldrQ 0 1 240⟩,
  ⟨344, 4, .vxar_2d 0 0 16 23⟩,
  ⟨348, 4, .strQ 0 0 368⟩,
  ⟨352, 4, .ldrQ 0 1 256⟩,
  ⟨356, 4, .vxar_2d 0 0 17 19⟩,
  ⟨360, 4, .strQ 0 0 128⟩,
  ⟨364, 4, .ldrQ 0 1 272⟩,
  ⟨368, 4, .vxar_2d 0 0 18 49⟩,
  ⟨372, 4, .strQ 0 0 288⟩,
  ⟨376, 4, .ldrQ 0 1 288⟩,
  ⟨380, 4, .vxar_2d 0 0 19 43⟩,
  ⟨384, 4, .strQ 0 0 48⟩,
  ⟨388, 4, .ldrQ 0 1 304⟩,
  ⟨392, 4, .vxar_2d 0 0 20 56⟩,
  ⟨396, 4, .strQ 0 0 208⟩,
  ⟨400, 4, .ldrQ 0 1 320⟩,
  ⟨404, 4, .vxar_2d 0 0 16 46⟩,
  ⟨408, 4, .strQ 0 0 224⟩,
  ⟨412, 4, .ldrQ 0 1 336⟩,
  ⟨416, 4, .vxar_2d 0 0 17 62⟩,
  ⟨420, 4, .strQ 0 0 384⟩,
  ⟨424, 4, .ldrQ 0 1 352⟩,
  ⟨428, 4, .vxar_2d 0 0 18 3⟩,
  ⟨432, 4, .strQ 0 0 144⟩,
  ⟨436, 4, .ldrQ 0 1 368⟩,
  ⟨440, 4, .vxar_2d 0 0 19 8⟩,
  ⟨444, 4, .strQ 0 0 304⟩,
  ⟨448, 4, .ldrQ 0 1 384⟩,
  ⟨452, 4, .vxar_2d 0 0 20 50⟩,
  ⟨456, 4, .strQ 0 0 64⟩,
  ⟨460, 4, .veor16b 0 0 0⟩,
  ⟨464, 4, .veor16b 1 1 1⟩,
  ⟨468, 4, .veor16b 2 2 2⟩,
  ⟨472, 4, .veor16b 3 3 3⟩,
  ⟨476, 4, .veor16b 4 4 4⟩,
  ⟨480, 4, .veor16b 5 5 5⟩,
  ⟨484, 4, .veor16b 6 6 6⟩,
  ⟨488, 4, .veor16b 16 16 16⟩,
  ⟨492, 4, .veor16b 17 17 17⟩,
  ⟨496, 4, .veor16b 18 18 18⟩,
  ⟨500, 4, .veor16b 19 19 19⟩,
  ⟨504, 4, .veor16b 20 20 20⟩,
  ⟨508, 4, .ret⟩]

def keccakThetaRhoName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 116, 104, 101, 116, 97, 95, 114, 104, 111, 95, 115, 104, 97, 51, 95, 110, 101, 111, 110]

theorem keccakThetaRho_decode :
    (findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName).bind
      (fun s => decodeArm64Slice s.code) = some keccakThetaRhoProg := by decide +kernel

/-- Bytewise disjoint input and output regions, including modular addresses. -/
def keccakThetaRhoDisjoint (outPtr inPtr : UInt64) : Prop :=
  ∀ i j : Nat, i < 400 → j < 400 →
    inPtr + UInt64.ofNat i ≠ outPtr + UInt64.ofNat j

theorem keccakThetaRho_readWrite (outPtr inPtr : UInt64)
    (hd : keccakThetaRhoDisjoint outPtr inPtr)
    (m : UInt64 → UInt8) (v : Vec128) (i j : Nat) (hi : i ≤ 384) (hj : j ≤ 384) :
    readMem128 (writeMem128 m (outPtr + UInt64.ofNat j) v) (inPtr + UInt64.ofNat i) =
      readMem128 m (inPtr + UInt64.ofNat i) := by
  unfold readMem128
  congr 1
  · apply readMem64_writeMem128_disjoint
    intro a b ha hb he
    rw [u64_add_ofNat_assoc inPtr i a (by omega),
      u64_add_ofNat_assoc outPtr j b (by omega)] at he
    exact hd (i+a) (j+b) (by omega) (by omega) he
  · apply readMem64_writeMem128_disjoint
    intro a b ha hb he
    change ((inPtr + UInt64.ofNat i) + UInt64.ofNat 8) + UInt64.ofNat a = _ at he
    rw [u64_add_ofNat_assoc inPtr i 8 (by omega),
      u64_add_ofNat_assoc inPtr (i+8) a (by omega),
      u64_add_ofNat_assoc outPtr j b (by omega)] at he
    exact hd (i+8+a) (j+b) (by omega) (by omega) he

def keccakThetaRhoLoad (m : UInt64 → UInt8) (p : UInt64) (block : Nat) : KState :=
  ⟨(if block == 0 then (readMem128 m (p + 0)).w0 else (readMem128 m (p + 0)).w1),
   (if block == 0 then (readMem128 m (p + 16)).w0 else (readMem128 m (p + 16)).w1),
   (if block == 0 then (readMem128 m (p + 32)).w0 else (readMem128 m (p + 32)).w1),
   (if block == 0 then (readMem128 m (p + 48)).w0 else (readMem128 m (p + 48)).w1),
   (if block == 0 then (readMem128 m (p + 64)).w0 else (readMem128 m (p + 64)).w1),
   (if block == 0 then (readMem128 m (p + 80)).w0 else (readMem128 m (p + 80)).w1),
   (if block == 0 then (readMem128 m (p + 96)).w0 else (readMem128 m (p + 96)).w1),
   (if block == 0 then (readMem128 m (p + 112)).w0 else (readMem128 m (p + 112)).w1),
   (if block == 0 then (readMem128 m (p + 128)).w0 else (readMem128 m (p + 128)).w1),
   (if block == 0 then (readMem128 m (p + 144)).w0 else (readMem128 m (p + 144)).w1),
   (if block == 0 then (readMem128 m (p + 160)).w0 else (readMem128 m (p + 160)).w1),
   (if block == 0 then (readMem128 m (p + 176)).w0 else (readMem128 m (p + 176)).w1),
   (if block == 0 then (readMem128 m (p + 192)).w0 else (readMem128 m (p + 192)).w1),
   (if block == 0 then (readMem128 m (p + 208)).w0 else (readMem128 m (p + 208)).w1),
   (if block == 0 then (readMem128 m (p + 224)).w0 else (readMem128 m (p + 224)).w1),
   (if block == 0 then (readMem128 m (p + 240)).w0 else (readMem128 m (p + 240)).w1),
   (if block == 0 then (readMem128 m (p + 256)).w0 else (readMem128 m (p + 256)).w1),
   (if block == 0 then (readMem128 m (p + 272)).w0 else (readMem128 m (p + 272)).w1),
   (if block == 0 then (readMem128 m (p + 288)).w0 else (readMem128 m (p + 288)).w1),
   (if block == 0 then (readMem128 m (p + 304)).w0 else (readMem128 m (p + 304)).w1),
   (if block == 0 then (readMem128 m (p + 320)).w0 else (readMem128 m (p + 320)).w1),
   (if block == 0 then (readMem128 m (p + 336)).w0 else (readMem128 m (p + 336)).w1),
   (if block == 0 then (readMem128 m (p + 352)).w0 else (readMem128 m (p + 352)).w1),
   (if block == 0 then (readMem128 m (p + 368)).w0 else (readMem128 m (p + 368)).w1),
   (if block == 0 then (readMem128 m (p + 384)).w0 else (readMem128 m (p + 384)).w1)⟩

def keccakThetaRhoOut (m : UInt64 → UInt8) (outPtr inPtr : UInt64) : UInt64 → UInt8 :=
  let k0 := rhoPiS (thetaS (keccakThetaRhoLoad m inPtr 0))
  let k1 := rhoPiS (thetaS (keccakThetaRhoLoad m inPtr 1))
  let m1 := writeMem128 m (outPtr + 0) ⟨k0.a0, k1.a0⟩
  let m2 := writeMem128 m1 (outPtr + 160) ⟨k0.a10, k1.a10⟩
  let m3 := writeMem128 m2 (outPtr + 320) ⟨k0.a20, k1.a20⟩
  let m4 := writeMem128 m3 (outPtr + 80) ⟨k0.a5, k1.a5⟩
  let m5 := writeMem128 m4 (outPtr + 240) ⟨k0.a15, k1.a15⟩
  let m6 := writeMem128 m5 (outPtr + 256) ⟨k0.a16, k1.a16⟩
  let m7 := writeMem128 m6 (outPtr + 16) ⟨k0.a1, k1.a1⟩
  let m8 := writeMem128 m7 (outPtr + 176) ⟨k0.a11, k1.a11⟩
  let m9 := writeMem128 m8 (outPtr + 336) ⟨k0.a21, k1.a21⟩
  let m10 := writeMem128 m9 (outPtr + 96) ⟨k0.a6, k1.a6⟩
  let m11 := writeMem128 m10 (outPtr + 112) ⟨k0.a7, k1.a7⟩
  let m12 := writeMem128 m11 (outPtr + 272) ⟨k0.a17, k1.a17⟩
  let m13 := writeMem128 m12 (outPtr + 32) ⟨k0.a2, k1.a2⟩
  let m14 := writeMem128 m13 (outPtr + 192) ⟨k0.a12, k1.a12⟩
  let m15 := writeMem128 m14 (outPtr + 352) ⟨k0.a22, k1.a22⟩
  let m16 := writeMem128 m15 (outPtr + 368) ⟨k0.a23, k1.a23⟩
  let m17 := writeMem128 m16 (outPtr + 128) ⟨k0.a8, k1.a8⟩
  let m18 := writeMem128 m17 (outPtr + 288) ⟨k0.a18, k1.a18⟩
  let m19 := writeMem128 m18 (outPtr + 48) ⟨k0.a3, k1.a3⟩
  let m20 := writeMem128 m19 (outPtr + 208) ⟨k0.a13, k1.a13⟩
  let m21 := writeMem128 m20 (outPtr + 224) ⟨k0.a14, k1.a14⟩
  let m22 := writeMem128 m21 (outPtr + 384) ⟨k0.a24, k1.a24⟩
  let m23 := writeMem128 m22 (outPtr + 144) ⟨k0.a9, k1.a9⟩
  let m24 := writeMem128 m23 (outPtr + 304) ⟨k0.a19, k1.a19⟩
  let m25 := writeMem128 m24 (outPtr + 64) ⟨k0.a4, k1.a4⟩
  m25

theorem keccakThetaRho_or_comm (a b : UInt64) : a ||| b = b ||| a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_or, BitVec.or_comm]


def keccakThetaRhoPerm (i : Nat) : Nat := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

def keccakThetaRhoRor : Nat → Nat
  | 0 => 0
  | 1 => 63
  | 2 => 2
  | 3 => 36
  | 4 => 37
  | 5 => 28
  | 6 => 20
  | 7 => 58
  | 8 => 9
  | 9 => 44
  | 10 => 61
  | 11 => 54
  | 12 => 21
  | 13 => 39
  | 14 => 25
  | 15 => 23
  | 16 => 19
  | 17 => 49
  | 18 => 43
  | 19 => 56
  | 20 => 46
  | 21 => 62
  | 22 => 3
  | 23 => 8
  | 24 => 50
  | _ => 0

def keccakThetaRhoGet (k : KState) : Nat → UInt64
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

def keccakThetaRhoVec (m : UInt64 → UInt8) (p : UInt64) (i : Nat) : Vec128 :=
  ⟨keccakThetaRhoGet (rhoPiS (thetaS (keccakThetaRhoLoad m p 0))) (keccakThetaRhoPerm i),
   keccakThetaRhoGet (rhoPiS (thetaS (keccakThetaRhoLoad m p 1))) (keccakThetaRhoPerm i)⟩

def keccakThetaRhoD (m : UInt64 → UInt8) (p : UInt64) (x : Nat) : Vec128 :=
  let c00 := (readMem128 m (p + 0)).w0 ^^^ (readMem128 m (p + 80)).w0 ^^^ (readMem128 m (p + 160)).w0 ^^^ (readMem128 m (p + 240)).w0 ^^^ (readMem128 m (p + 320)).w0
  let c01 := (readMem128 m (p + 0)).w1 ^^^ (readMem128 m (p + 80)).w1 ^^^ (readMem128 m (p + 160)).w1 ^^^ (readMem128 m (p + 240)).w1 ^^^ (readMem128 m (p + 320)).w1
  let c10 := (readMem128 m (p + 16)).w0 ^^^ (readMem128 m (p + 96)).w0 ^^^ (readMem128 m (p + 176)).w0 ^^^ (readMem128 m (p + 256)).w0 ^^^ (readMem128 m (p + 336)).w0
  let c11 := (readMem128 m (p + 16)).w1 ^^^ (readMem128 m (p + 96)).w1 ^^^ (readMem128 m (p + 176)).w1 ^^^ (readMem128 m (p + 256)).w1 ^^^ (readMem128 m (p + 336)).w1
  let c20 := (readMem128 m (p + 32)).w0 ^^^ (readMem128 m (p + 112)).w0 ^^^ (readMem128 m (p + 192)).w0 ^^^ (readMem128 m (p + 272)).w0 ^^^ (readMem128 m (p + 352)).w0
  let c21 := (readMem128 m (p + 32)).w1 ^^^ (readMem128 m (p + 112)).w1 ^^^ (readMem128 m (p + 192)).w1 ^^^ (readMem128 m (p + 272)).w1 ^^^ (readMem128 m (p + 352)).w1
  let c30 := (readMem128 m (p + 48)).w0 ^^^ (readMem128 m (p + 128)).w0 ^^^ (readMem128 m (p + 208)).w0 ^^^ (readMem128 m (p + 288)).w0 ^^^ (readMem128 m (p + 368)).w0
  let c31 := (readMem128 m (p + 48)).w1 ^^^ (readMem128 m (p + 128)).w1 ^^^ (readMem128 m (p + 208)).w1 ^^^ (readMem128 m (p + 288)).w1 ^^^ (readMem128 m (p + 368)).w1
  let c40 := (readMem128 m (p + 64)).w0 ^^^ (readMem128 m (p + 144)).w0 ^^^ (readMem128 m (p + 224)).w0 ^^^ (readMem128 m (p + 304)).w0 ^^^ (readMem128 m (p + 384)).w0
  let c41 := (readMem128 m (p + 64)).w1 ^^^ (readMem128 m (p + 144)).w1 ^^^ (readMem128 m (p + 224)).w1 ^^^ (readMem128 m (p + 304)).w1 ^^^ (readMem128 m (p + 384)).w1
  match x with
  | 0 => ⟨c40 ^^^ rotlK c10 1 63, c41 ^^^ rotlK c11 1 63⟩
  | 1 => ⟨c00 ^^^ rotlK c20 1 63, c01 ^^^ rotlK c21 1 63⟩
  | 2 => ⟨c10 ^^^ rotlK c30 1 63, c11 ^^^ rotlK c31 1 63⟩
  | 3 => ⟨c20 ^^^ rotlK c40 1 63, c21 ^^^ rotlK c41 1 63⟩
  | 4 => ⟨c30 ^^^ rotlK c00 1 63, c31 ^^^ rotlK c01 1 63⟩
  | _ => Vec128.zero

def keccakThetaRhoXar (a b : Vec128) (imm : Nat) : Vec128 :=
  let r (x : UInt64) := if imm % 64 == 0 then x
    else (x >>> UInt64.ofNat (imm % 64)) ||| (x <<< UInt64.ofNat (64 - imm % 64))
  ⟨r (a.w0 ^^^ b.w0), r (a.w1 ^^^ b.w1)⟩

def keccakThetaRhoPrefix (m : UInt64 → UInt8) (outPtr inPtr : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem128 (keccakThetaRhoPrefix m outPtr inPtr n)
      (outPtr + UInt64.ofNat (16 * keccakThetaRhoPerm n)) (keccakThetaRhoVec m inPtr n)

theorem keccakThetaRhoPerm_bound (i : Nat) (hi : i < 25) :
    16 * keccakThetaRhoPerm i ≤ 384 := by
  unfold keccakThetaRhoPerm
  have hm := Nat.mod_lt (2 * (i % 5) + 3 * (i / 5)) (by decide : 0 < 5)
  omega

theorem keccakThetaRhoPrefix_read (m : UInt64 → UInt8) (outPtr inPtr : UInt64)
    (hd : keccakThetaRhoDisjoint outPtr inPtr) (n : Nat) (hn : n ≤ 25)
    (i : Nat) (hi : i ≤ 384) :
    readMem128 (keccakThetaRhoPrefix m outPtr inPtr n) (inPtr + UInt64.ofNat i) =
      readMem128 m (inPtr + UInt64.ofNat i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccakThetaRhoPrefix, keccakThetaRho_readWrite outPtr inPtr hd _ _ i
      (16 * keccakThetaRhoPerm n) hi (keccakThetaRhoPerm_bound n (by omega))]
    exact ih (by omega)

theorem keccakThetaRhoPrefix_full (m : UInt64 → UInt8) (outPtr inPtr : UInt64) :
    keccakThetaRhoPrefix m outPtr inPtr 25 = keccakThetaRhoOut m outPtr inPtr := by rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem keccakThetaRho_math (m : UInt64 → UInt8) (p : UInt64) (n : Nat) (hn : n < 25) :
    keccakThetaRhoXar (readMem128 m (p + UInt64.ofNat (16 * n)))
      (keccakThetaRhoD m p (n % 5)) (keccakThetaRhoRor n) = keccakThetaRhoVec m p n := by
  match n, hn with
  | 0, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 1, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 2, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 3, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 4, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 5, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 6, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 7, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 8, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 9, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 10, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 11, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 12, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 13, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 14, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 15, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 16, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 17, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 18, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 19, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 20, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 21, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 22, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 23, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 24, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | n+25, hn => omega

def keccakThetaRhoInv (s t : Arm64State) (n : Nat) : Prop :=
  t.pc = 160 + 12*n ∧ t.gpr = s.gpr ∧ t.halted = false ∧
  (∀ x : Nat, x < 5 → t.vec.get (16+x) = keccakThetaRhoD s.mem (s.gpr.get 1) x) ∧
  t.mem = keccakThetaRhoPrefix s.mem (s.gpr.get 0) (s.gpr.get 1) n

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem keccakThetaRho_parity (s : Arm64State) (hp : s.pc = 0) (hh : s.halted = false) :
    ∃ t, StepsArm64 keccakThetaRhoProg 40 s t ∧ keccakThetaRhoInv s t 0 := by
  rcases s with ⟨pc, ⟨⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩, hi⟩,
    ⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15⟩,
      ⟨v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31⟩⟩,
    cf,zf,dit,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 40
    apply StepsArm64_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepArm64, getArmGpr, Bank32.get, Bank32.set, Bank16.get, Bank16.set]
      all_goals rfl
  refine ⟨_, StepsArm64.zero _, rfl, rfl, rfl, ?_, rfl⟩
  intro x hx
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [keccakThetaRhoD, rotlK, Bank32.get, Bank16.get]
  | x+5, hx => omega

theorem keccakThetaRho_fetch (n : Nat) (hn : n < 25) :
    findInstrAtPc (160+12*n) keccakThetaRhoProg =
      some ⟨160+12*n, 4, .ldrQ 0 1 (UInt64.ofNat (16*n))⟩ ∧
    findInstrAtPc (160+12*n+4) keccakThetaRhoProg =
      some ⟨160+12*n+4, 4, .vxar_2d 0 0 (16+n%5) (keccakThetaRhoRor n)⟩ ∧
    findInstrAtPc (160+12*n+8) keccakThetaRhoProg =
      some ⟨160+12*n+8, 4, .strQ 0 0 (UInt64.ofNat (16*keccakThetaRhoPerm n))⟩ := by
  have hall : ∀ n : Fin 25,
    findInstrAtPc (160+12*n.val) keccakThetaRhoProg =
      some ⟨160+12*n.val, 4, .ldrQ 0 1 (UInt64.ofNat (16*n.val))⟩ ∧
    findInstrAtPc (160+12*n.val+4) keccakThetaRhoProg =
      some ⟨160+12*n.val+4, 4, .vxar_2d 0 0 (16+n.val%5) (keccakThetaRhoRor n.val)⟩ ∧
    findInstrAtPc (160+12*n.val+8) keccakThetaRhoProg =
      some ⟨160+12*n.val+8, 4, .strQ 0 0 (UInt64.ofNat (16*keccakThetaRhoPerm n.val))⟩ := by decide +kernel
  exact hall ⟨n, hn⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem keccakThetaRho_block (s t : Arm64State) (n : Nat) (hn : n < 25)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1))
    (h : keccakThetaRhoInv s t n) :
    ∃ u, StepsArm64 keccakThetaRhoProg 3 t u ∧ keccakThetaRhoInv s u (n+1) := by
  rcases t with ⟨pc,gpr,vec,cf,zf,dit,hlt,mem⟩
  rcases h with ⟨hp,hg,hh,hv,hm⟩
  dsimp only at hp hg hh hv hm
  subst pc gpr hlt mem
  have hmod : n % 5 < 5 := Nat.mod_lt n (by decide)
  have hvn := hv (n%5) hmod
  have hmath := keccakThetaRho_math s.mem (s.gpr.get 1) n hn
  dsimp only [keccakThetaRhoXar] at hmath
  have hf := keccakThetaRho_fetch n hn
  have hget1 : ∀ st : Arm64State, getArmGpr st 1 = st.gpr.get 1 := fun _ => rfl
  have hget0 : ∀ st : Arm64State, getArmGpr st 0 = st.gpr.get 0 := fun _ => rfl
  apply StepsArm64_step_ex rfl hf.1
  · conv =>
      lhs
      simp only [stepArm64, hget1]
      rw [keccakThetaRhoPrefix_read s.mem (s.gpr.get 0) (s.gpr.get 1) hd n (by omega)
        (16*n) (by omega)]
    all_goals rfl
  apply StepsArm64_step_ex rfl hf.2.1
  · conv =>
      lhs
      simp (disch := omega) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne, hvn]
      rw [hmath]
    all_goals rfl
  apply StepsArm64_step_ex rfl (by simpa only [Nat.add_assoc] using hf.2.2)
  · conv =>
      lhs
      simp only [stepArm64, hget0, Bank32.get_set_eq]
    all_goals rfl
  refine ⟨_, StepsArm64.zero _, ?_, rfl, rfl, ?_, rfl⟩
  · dsimp only
    omega
  · intro x hx
    dsimp only
    simp (disch := omega) only [Bank32.get_set_ne]
    exact hv x hx

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
theorem keccakThetaRho_wipe (s : Arm64State) (hp : s.pc = 460) (hh : s.halted = false) :
    ∃ t, StepsArm64 keccakThetaRhoProg 13 s t ∧ t.halted = true ∧ t.mem = s.mem := by
  rcases s with ⟨pc,gpr,⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15⟩,
    ⟨v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31⟩⟩,cf,zf,dit,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 13
    apply StepsArm64_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepArm64, Bank32.get, Bank32.set, Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsArm64.zero _, rfl, rfl⟩

theorem keccakThetaRho_steps_trans {m n : Nat} {s t u : Arm64State}
    (h : StepsArm64 keccakThetaRhoProg m s t)
    (h' : StepsArm64 keccakThetaRhoProg n t u) :
    StepsArm64 keccakThetaRhoProg (m+n) s u := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | cons hh hf hs h ih =>
    simpa only [Nat.add_right_comm] using StepsArm64.cons hh hf hs (ih h')

theorem keccakThetaRho_blocks (s t : Arm64State)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1))
    (n : Nat) (hn : n ≤ 25) (h : keccakThetaRhoInv s t 0) :
    ∃ u, StepsArm64 keccakThetaRhoProg (3*n) t u ∧ keccakThetaRhoInv s u n := by
  induction n with
  | zero => exact ⟨t, StepsArm64.zero _, h⟩
  | succ n ih =>
    obtain ⟨u, hu, hi⟩ := ih (by omega)
    obtain ⟨v, hv, hi'⟩ := keccakThetaRho_block s u n (by omega) hd hi
    refine ⟨v, ?_, hi'⟩
    simpa only [Nat.mul_add, Nat.mul_one] using keccakThetaRho_steps_trans hu hv

theorem keccakThetaRho_steps (s : Arm64State)
    (hp : s.pc = 0) (hh : s.halted = false)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1)) :
    ∃ t, StepsArm64 keccakThetaRhoProg 128 s t ∧ t.halted = true ∧
      t.mem = keccakThetaRhoOut s.mem (s.gpr.get 0) (s.gpr.get 1) := by
  obtain ⟨s40, h40, hi⟩ := keccakThetaRho_parity s hp hh
  obtain ⟨s115, h75, hi'⟩ := keccakThetaRho_blocks s s40 hd 25 (by decide) hi
  obtain ⟨s128, h13, hh', hm⟩ := keccakThetaRho_wipe s115 hi'.1 hi'.2.2.1
  refine ⟨s128, keccakThetaRho_steps_trans (keccakThetaRho_steps_trans h40 h75) h13, hh', ?_⟩
  rw [hm, hi'.2.2.2.2, keccakThetaRhoPrefix_full]

/-- Complete ABI preconditions: entry PC, live machine, disjoint 400-byte buffers. -/
def keccakThetaRhoInitial (s : Arm64State) : Prop :=
  s.pc = 0 ∧ s.halted = false ∧ keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1)

/-- Fresh decoded machine code computes theta, rho and pi on both full Keccak states.
`keccakThetaRhoOut` writes all 25 lanes of each state and preserves every other byte. -/
theorem keccakThetaRho_current_functional (s : Arm64State) (h : keccakThetaRhoInitial s) :
    ∃ slice prog,
      findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName = some slice ∧
      decodeArm64Slice slice.code = some prog ∧
      ∀ extra : Nat,
        (runArm64 prog (128 + extra) s).1.halted = true ∧
        (runArm64 prog (128 + extra) s).1.mem =
          keccakThetaRhoOut s.mem (s.gpr.get 0) (s.gpr.get 1) := by
  have hd := keccakThetaRho_decode
  cases hf : findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName with
  | none => rw [hf] at hd; contradiction
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccakThetaRhoProg, rfl, hd, ?_⟩
    obtain ⟨t, ht, hh, hm⟩ := keccakThetaRho_steps s h.1 h.2.1 h.2.2
    intro extra
    have he := (ht.toExecReaches.run extra).1
    rw [runArm64_halted_fst keccakThetaRhoProg extra t hh] at he
    rw [he]
    exact ⟨hh, hm⟩

theorem keccakThetaRho_inhabited : ∃ s : Arm64State, keccakThetaRhoInitial s := by
  refine ⟨⟨0, Bank32.ofFn (fun i => if i == 1 then 1024 else 0),
    Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩, rfl, rfl, ?_⟩
  change keccakThetaRhoDisjoint 0 1024
  intro i j hi hj he
  have hn := congrArg UInt64.toNat he
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
  omega

/-- A wrong implementation omitting theta cannot satisfy the full-state specification. -/
theorem keccakThetaRho_tooth :
    rhoPiS (thetaS { zeroKState with a1 := 1 }) ≠
      rhoPiS { zeroKState with a1 := 1 } := by
  simp only [zeroKState_eq]; kstate_ne

#tooth_pair keccakThetaRho_current_functional vs keccakThetaRho_tooth
#verify_inhabited keccakThetaRho_current_functional keccakThetaRho_inhabited

end KeccakThetaRhoFreshVerification

section Keccak4xFreshVerification
set_option linter.unusedSimpArgs false
def keccak4xName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 102, 49, 54, 48, 48, 95, 97, 118, 120, 50, 95, 52, 120]

@[expose] def keccak4xProg : List (DecodedInstr X86Instr) := [
  ⟨0, 1, .pushReg 5⟩,
  ⟨1, 3, .movRegReg true 5 4⟩,
  ⟨4, 4, .aluImm .andOp true 4 18446744073709551584⟩,
  ⟨8, 7, .aluImm .sub true 4 832⟩,
  ⟨15, 5, .movImm false 1 24⟩,
  ⟨20, 4, .vload true 0 (.baseDisp 7 0)⟩,
  ⟨24, 8, .vpxorLoad256 0 0 (.baseDisp 7 160)⟩,
  ⟨32, 8, .vpxorLoad256 0 0 (.baseDisp 7 320)⟩,
  ⟨40, 8, .vpxorLoad256 0 0 (.baseDisp 7 480)⟩,
  ⟨48, 8, .vpxorLoad256 0 0 (.baseDisp 7 640)⟩,
  ⟨56, 5, .vload true 1 (.baseDisp 7 32)⟩,
  ⟨61, 8, .vpxorLoad256 1 1 (.baseDisp 7 192)⟩,
  ⟨69, 8, .vpxorLoad256 1 1 (.baseDisp 7 352)⟩,
  ⟨77, 8, .vpxorLoad256 1 1 (.baseDisp 7 512)⟩,
  ⟨85, 8, .vpxorLoad256 1 1 (.baseDisp 7 672)⟩,
  ⟨93, 5, .vload true 2 (.baseDisp 7 64)⟩,
  ⟨98, 8, .vpxorLoad256 2 2 (.baseDisp 7 224)⟩,
  ⟨106, 8, .vpxorLoad256 2 2 (.baseDisp 7 384)⟩,
  ⟨114, 8, .vpxorLoad256 2 2 (.baseDisp 7 544)⟩,
  ⟨122, 8, .vpxorLoad256 2 2 (.baseDisp 7 704)⟩,
  ⟨130, 5, .vload true 3 (.baseDisp 7 96)⟩,
  ⟨135, 8, .vpxorLoad256 3 3 (.baseDisp 7 256)⟩,
  ⟨143, 8, .vpxorLoad256 3 3 (.baseDisp 7 416)⟩,
  ⟨151, 8, .vpxorLoad256 3 3 (.baseDisp 7 576)⟩,
  ⟨159, 8, .vpxorLoad256 3 3 (.baseDisp 7 736)⟩,
  ⟨167, 8, .vload true 4 (.baseDisp 7 128)⟩,
  ⟨175, 8, .vpxorLoad256 4 4 (.baseDisp 7 288)⟩,
  ⟨183, 8, .vpxorLoad256 4 4 (.baseDisp 7 448)⟩,
  ⟨191, 8, .vpxorLoad256 4 4 (.baseDisp 7 608)⟩,
  ⟨199, 8, .vpxorLoad256 4 4 (.baseDisp 7 768)⟩,
  ⟨207, 5, .vshiftImm .vpsllq true 10 1 1⟩,
  ⟨212, 5, .vshiftImm .vpsrlq true 11 1 63⟩,
  ⟨217, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨222, 4, .vbinOp .vpxor true 5 10 4⟩,
  ⟨226, 5, .vshiftImm .vpsllq true 10 2 1⟩,
  ⟨231, 5, .vshiftImm .vpsrlq true 11 2 63⟩,
  ⟨236, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨241, 4, .vbinOp .vpxor true 6 10 0⟩,
  ⟨245, 5, .vshiftImm .vpsllq true 10 3 1⟩,
  ⟨250, 5, .vshiftImm .vpsrlq true 11 3 63⟩,
  ⟨255, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨260, 4, .vbinOp .vpxor true 7 10 1⟩,
  ⟨264, 5, .vshiftImm .vpsllq true 10 4 1⟩,
  ⟨269, 5, .vshiftImm .vpsrlq true 11 4 63⟩,
  ⟨274, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨279, 4, .vbinOp .vpxor true 8 10 2⟩,
  ⟨283, 5, .vshiftImm .vpsllq true 10 0 1⟩,
  ⟨288, 5, .vshiftImm .vpsrlq true 11 0 63⟩,
  ⟨293, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨298, 4, .vbinOp .vpxor true 9 10 3⟩,
  ⟨302, 4, .vpxorLoad256 0 5 (.baseDisp 7 0)⟩,
  ⟨306, 5, .vstore true 0 (.baseDisp 4 0)⟩,
  ⟨311, 5, .vpxorLoad256 0 6 (.baseDisp 7 32)⟩,
  ⟨316, 5, .vshiftImm .vpsllq true 1 0 1⟩,
  ⟨321, 5, .vshiftImm .vpsrlq true 2 0 63⟩,
  ⟨326, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨330, 9, .vstore true 0 (.baseDisp 4 320)⟩,
  ⟨339, 5, .vpxorLoad256 0 7 (.baseDisp 7 64)⟩,
  ⟨344, 5, .vshiftImm .vpsllq true 1 0 62⟩,
  ⟨349, 5, .vshiftImm .vpsrlq true 2 0 2⟩,
  ⟨354, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨358, 9, .vstore true 0 (.baseDisp 4 640)⟩,
  ⟨367, 5, .vpxorLoad256 0 8 (.baseDisp 7 96)⟩,
  ⟨372, 5, .vshiftImm .vpsllq true 1 0 28⟩,
  ⟨377, 5, .vshiftImm .vpsrlq true 2 0 36⟩,
  ⟨382, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨386, 9, .vstore true 0 (.baseDisp 4 160)⟩,
  ⟨395, 8, .vpxorLoad256 0 9 (.baseDisp 7 128)⟩,
  ⟨403, 5, .vshiftImm .vpsllq true 1 0 27⟩,
  ⟨408, 5, .vshiftImm .vpsrlq true 2 0 37⟩,
  ⟨413, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨417, 9, .vstore true 0 (.baseDisp 4 480)⟩,
  ⟨426, 8, .vpxorLoad256 0 5 (.baseDisp 7 160)⟩,
  ⟨434, 5, .vshiftImm .vpsllq true 1 0 36⟩,
  ⟨439, 5, .vshiftImm .vpsrlq true 2 0 28⟩,
  ⟨444, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨448, 9, .vstore true 0 (.baseDisp 4 512)⟩,
  ⟨457, 8, .vpxorLoad256 0 6 (.baseDisp 7 192)⟩,
  ⟨465, 5, .vshiftImm .vpsllq true 1 0 44⟩,
  ⟨470, 5, .vshiftImm .vpsrlq true 2 0 20⟩,
  ⟨475, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨479, 6, .vstore true 0 (.baseDisp 4 32)⟩,
  ⟨485, 8, .vpxorLoad256 0 7 (.baseDisp 7 224)⟩,
  ⟨493, 5, .vshiftImm .vpsllq true 1 0 6⟩,
  ⟨498, 5, .vshiftImm .vpsrlq true 2 0 58⟩,
  ⟨503, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨507, 9, .vstore true 0 (.baseDisp 4 352)⟩,
  ⟨516, 8, .vpxorLoad256 0 8 (.baseDisp 7 256)⟩,
  ⟨524, 5, .vshiftImm .vpsllq true 1 0 55⟩,
  ⟨529, 5, .vshiftImm .vpsrlq true 2 0 9⟩,
  ⟨534, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨538, 9, .vstore true 0 (.baseDisp 4 672)⟩,
  ⟨547, 8, .vpxorLoad256 0 9 (.baseDisp 7 288)⟩,
  ⟨555, 5, .vshiftImm .vpsllq true 1 0 20⟩,
  ⟨560, 5, .vshiftImm .vpsrlq true 2 0 44⟩,
  ⟨565, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨569, 9, .vstore true 0 (.baseDisp 4 192)⟩,
  ⟨578, 8, .vpxorLoad256 0 5 (.baseDisp 7 320)⟩,
  ⟨586, 5, .vshiftImm .vpsllq true 1 0 3⟩,
  ⟨591, 5, .vshiftImm .vpsrlq true 2 0 61⟩,
  ⟨596, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨600, 9, .vstore true 0 (.baseDisp 4 224)⟩,
  ⟨609, 8, .vpxorLoad256 0 6 (.baseDisp 7 352)⟩,
  ⟨617, 5, .vshiftImm .vpsllq true 1 0 10⟩,
  ⟨622, 5, .vshiftImm .vpsrlq true 2 0 54⟩,
  ⟨627, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨631, 9, .vstore true 0 (.baseDisp 4 544)⟩,
  ⟨640, 8, .vpxorLoad256 0 7 (.baseDisp 7 384)⟩,
  ⟨648, 5, .vshiftImm .vpsllq true 1 0 43⟩,
  ⟨653, 5, .vshiftImm .vpsrlq true 2 0 21⟩,
  ⟨658, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨662, 6, .vstore true 0 (.baseDisp 4 64)⟩,
  ⟨668, 8, .vpxorLoad256 0 8 (.baseDisp 7 416)⟩,
  ⟨676, 5, .vshiftImm .vpsllq true 1 0 25⟩,
  ⟨681, 5, .vshiftImm .vpsrlq true 2 0 39⟩,
  ⟨686, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨690, 9, .vstore true 0 (.baseDisp 4 384)⟩,
  ⟨699, 8, .vpxorLoad256 0 9 (.baseDisp 7 448)⟩,
  ⟨707, 5, .vshiftImm .vpsllq true 1 0 39⟩,
  ⟨712, 5, .vshiftImm .vpsrlq true 2 0 25⟩,
  ⟨717, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨721, 9, .vstore true 0 (.baseDisp 4 704)⟩,
  ⟨730, 8, .vpxorLoad256 0 5 (.baseDisp 7 480)⟩,
  ⟨738, 5, .vshiftImm .vpsllq true 1 0 41⟩,
  ⟨743, 5, .vshiftImm .vpsrlq true 2 0 23⟩,
  ⟨748, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨752, 9, .vstore true 0 (.baseDisp 4 736)⟩,
  ⟨761, 8, .vpxorLoad256 0 6 (.baseDisp 7 512)⟩,
  ⟨769, 5, .vshiftImm .vpsllq true 1 0 45⟩,
  ⟨774, 5, .vshiftImm .vpsrlq true 2 0 19⟩,
  ⟨779, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨783, 9, .vstore true 0 (.baseDisp 4 256)⟩,
  ⟨792, 8, .vpxorLoad256 0 7 (.baseDisp 7 544)⟩,
  ⟨800, 5, .vshiftImm .vpsllq true 1 0 15⟩,
  ⟨805, 5, .vshiftImm .vpsrlq true 2 0 49⟩,
  ⟨810, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨814, 9, .vstore true 0 (.baseDisp 4 576)⟩,
  ⟨823, 8, .vpxorLoad256 0 8 (.baseDisp 7 576)⟩,
  ⟨831, 5, .vshiftImm .vpsllq true 1 0 21⟩,
  ⟨836, 5, .vshiftImm .vpsrlq true 2 0 43⟩,
  ⟨841, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨845, 6, .vstore true 0 (.baseDisp 4 96)⟩,
  ⟨851, 8, .vpxorLoad256 0 9 (.baseDisp 7 608)⟩,
  ⟨859, 5, .vshiftImm .vpsllq true 1 0 8⟩,
  ⟨864, 5, .vshiftImm .vpsrlq true 2 0 56⟩,
  ⟨869, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨873, 9, .vstore true 0 (.baseDisp 4 416)⟩,
  ⟨882, 8, .vpxorLoad256 0 5 (.baseDisp 7 640)⟩,
  ⟨890, 5, .vshiftImm .vpsllq true 1 0 18⟩,
  ⟨895, 5, .vshiftImm .vpsrlq true 2 0 46⟩,
  ⟨900, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨904, 9, .vstore true 0 (.baseDisp 4 448)⟩,
  ⟨913, 8, .vpxorLoad256 0 6 (.baseDisp 7 672)⟩,
  ⟨921, 5, .vshiftImm .vpsllq true 1 0 2⟩,
  ⟨926, 5, .vshiftImm .vpsrlq true 2 0 62⟩,
  ⟨931, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨935, 9, .vstore true 0 (.baseDisp 4 768)⟩,
  ⟨944, 8, .vpxorLoad256 0 7 (.baseDisp 7 704)⟩,
  ⟨952, 5, .vshiftImm .vpsllq true 1 0 61⟩,
  ⟨957, 5, .vshiftImm .vpsrlq true 2 0 3⟩,
  ⟨962, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨966, 9, .vstore true 0 (.baseDisp 4 288)⟩,
  ⟨975, 8, .vpxorLoad256 0 8 (.baseDisp 7 736)⟩,
  ⟨983, 5, .vshiftImm .vpsllq true 1 0 56⟩,
  ⟨988, 5, .vshiftImm .vpsrlq true 2 0 8⟩,
  ⟨993, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨997, 9, .vstore true 0 (.baseDisp 4 608)⟩,
  ⟨1006, 8, .vpxorLoad256 0 9 (.baseDisp 7 768)⟩,
  ⟨1014, 5, .vshiftImm .vpsllq true 1 0 14⟩,
  ⟨1019, 5, .vshiftImm .vpsrlq true 2 0 50⟩,
  ⟨1024, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨1028, 9, .vstore true 0 (.baseDisp 4 128)⟩,
  ⟨1037, 5, .vload true 0 (.baseDisp 4 0)⟩,
  ⟨1042, 6, .vload true 1 (.baseDisp 4 32)⟩,
  ⟨1048, 6, .vload true 2 (.baseDisp 4 64)⟩,
  ⟨1054, 6, .vload true 3 (.baseDisp 4 96)⟩,
  ⟨1060, 9, .vload true 4 (.baseDisp 4 128)⟩,
  ⟨1069, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1073, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1077, 5, .vpbroadcastLoad64 10 (.baseDisp 6 0)⟩,
  ⟨1082, 4, .vbinOp .vpxor true 5 10 5⟩,
  ⟨1086, 4, .vstore true 5 (.baseDisp 7 0)⟩,
  ⟨1090, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1094, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1098, 5, .vstore true 6 (.baseDisp 7 32)⟩,
  ⟨1103, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1107, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1111, 5, .vstore true 7 (.baseDisp 7 64)⟩,
  ⟨1116, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1120, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1124, 5, .vstore true 8 (.baseDisp 7 96)⟩,
  ⟨1129, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1133, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1137, 8, .vstore true 9 (.baseDisp 7 128)⟩,
  ⟨1145, 9, .vload true 0 (.baseDisp 4 160)⟩,
  ⟨1154, 9, .vload true 1 (.baseDisp 4 192)⟩,
  ⟨1163, 9, .vload true 2 (.baseDisp 4 224)⟩,
  ⟨1172, 9, .vload true 3 (.baseDisp 4 256)⟩,
  ⟨1181, 9, .vload true 4 (.baseDisp 4 288)⟩,
  ⟨1190, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1194, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1198, 8, .vstore true 5 (.baseDisp 7 160)⟩,
  ⟨1206, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1210, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1214, 8, .vstore true 6 (.baseDisp 7 192)⟩,
  ⟨1222, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1226, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1230, 8, .vstore true 7 (.baseDisp 7 224)⟩,
  ⟨1238, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1242, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1246, 8, .vstore true 8 (.baseDisp 7 256)⟩,
  ⟨1254, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1258, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1262, 8, .vstore true 9 (.baseDisp 7 288)⟩,
  ⟨1270, 9, .vload true 0 (.baseDisp 4 320)⟩,
  ⟨1279, 9, .vload true 1 (.baseDisp 4 352)⟩,
  ⟨1288, 9, .vload true 2 (.baseDisp 4 384)⟩,
  ⟨1297, 9, .vload true 3 (.baseDisp 4 416)⟩,
  ⟨1306, 9, .vload true 4 (.baseDisp 4 448)⟩,
  ⟨1315, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1319, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1323, 8, .vstore true 5 (.baseDisp 7 320)⟩,
  ⟨1331, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1335, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1339, 8, .vstore true 6 (.baseDisp 7 352)⟩,
  ⟨1347, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1351, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1355, 8, .vstore true 7 (.baseDisp 7 384)⟩,
  ⟨1363, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1367, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1371, 8, .vstore true 8 (.baseDisp 7 416)⟩,
  ⟨1379, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1383, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1387, 8, .vstore true 9 (.baseDisp 7 448)⟩,
  ⟨1395, 9, .vload true 0 (.baseDisp 4 480)⟩,
  ⟨1404, 9, .vload true 1 (.baseDisp 4 512)⟩,
  ⟨1413, 9, .vload true 2 (.baseDisp 4 544)⟩,
  ⟨1422, 9, .vload true 3 (.baseDisp 4 576)⟩,
  ⟨1431, 9, .vload true 4 (.baseDisp 4 608)⟩,
  ⟨1440, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1444, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1448, 8, .vstore true 5 (.baseDisp 7 480)⟩,
  ⟨1456, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1460, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1464, 8, .vstore true 6 (.baseDisp 7 512)⟩,
  ⟨1472, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1476, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1480, 8, .vstore true 7 (.baseDisp 7 544)⟩,
  ⟨1488, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1492, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1496, 8, .vstore true 8 (.baseDisp 7 576)⟩,
  ⟨1504, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1508, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1512, 8, .vstore true 9 (.baseDisp 7 608)⟩,
  ⟨1520, 9, .vload true 0 (.baseDisp 4 640)⟩,
  ⟨1529, 9, .vload true 1 (.baseDisp 4 672)⟩,
  ⟨1538, 9, .vload true 2 (.baseDisp 4 704)⟩,
  ⟨1547, 9, .vload true 3 (.baseDisp 4 736)⟩,
  ⟨1556, 9, .vload true 4 (.baseDisp 4 768)⟩,
  ⟨1565, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1569, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1573, 8, .vstore true 5 (.baseDisp 7 640)⟩,
  ⟨1581, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1585, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1589, 8, .vstore true 6 (.baseDisp 7 672)⟩,
  ⟨1597, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1601, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1605, 8, .vstore true 7 (.baseDisp 7 704)⟩,
  ⟨1613, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1617, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1621, 8, .vstore true 8 (.baseDisp 7 736)⟩,
  ⟨1629, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1633, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1637, 8, .vstore true 9 (.baseDisp 7 768)⟩,
  ⟨1645, 4, .aluImm .add true 6 8⟩,
  ⟨1649, 2, .incDec false false 1⟩,
  ⟨1651, 6, .jcc 5 20⟩,
  ⟨1657, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨1661, 5, .movImm false 1 25⟩,
  ⟨1666, 3, .movRegReg true 0 4⟩,
  ⟨1669, 4, .vstore true 0 (.baseDisp 0 0)⟩,
  ⟨1673, 4, .aluImm .add true 0 32⟩,
  ⟨1677, 2, .incDec false false 1⟩,
  ⟨1679, 2, .jcc 5 1669⟩,
  ⟨1681, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨1685, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨1689, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨1693, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨1697, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨1701, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨1705, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨1709, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨1714, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨1719, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨1724, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨1729, 3, .vzeroall⟩,
  ⟨1732, 3, .vzeroupper⟩,
  ⟨1735, 3, .movRegReg true 4 5⟩,
  ⟨1738, 1, .popReg 5⟩,
  ⟨1739, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨1741, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨1743, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨1745, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨1747, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨1750, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨1753, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨1756, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨1759, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨1761, 1, .ret⟩
]

theorem keccak4x_decoded :
    (findSliceByNameBytes currentX86ExtractedSlices keccak4xName).bind
      (fun sl => decodeX86Stream sl.code) = some keccak4xProg := by decide +kernel

theorem keccak4x_instruction_count : keccak4xProg.length = 309 := by rfl

end Keccak4xFreshVerification

end Qsag
end
