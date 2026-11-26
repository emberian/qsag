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

