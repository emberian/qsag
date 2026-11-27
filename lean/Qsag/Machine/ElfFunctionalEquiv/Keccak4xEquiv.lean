module

public import Qsag.Machine.ElfFunctionalEquiv.KeccakMpcAndThetaRho
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


section Keccak4xFreshVerification
set_option linter.unusedSimpArgs false

/-- One of the four words in an interleaved AVX2 Keccak lane. -/
def keccak4xWord (v : Vec256) : Nat → UInt64
  | 0 => v.w0 | 1 => v.w1 | 2 => v.w2 | _ => v.w3

/-- All 25 coordinates of any one of the four independent sponges. -/
def keccak4xLaneState (v : Nat → Vec256) (q : Nat) : KState :=
  ⟨keccak4xWord (v 0) q, keccak4xWord (v 1) q, keccak4xWord (v 2) q, keccak4xWord (v 3) q, keccak4xWord (v 4) q, keccak4xWord (v 5) q, keccak4xWord (v 6) q, keccak4xWord (v 7) q, keccak4xWord (v 8) q, keccak4xWord (v 9) q, keccak4xWord (v 10) q, keccak4xWord (v 11) q, keccak4xWord (v 12) q, keccak4xWord (v 13) q, keccak4xWord (v 14) q, keccak4xWord (v 15) q, keccak4xWord (v 16) q, keccak4xWord (v 17) q, keccak4xWord (v 18) q, keccak4xWord (v 19) q, keccak4xWord (v 20) q, keccak4xWord (v 21) q, keccak4xWord (v 22) q, keccak4xWord (v 23) q, keccak4xWord (v 24) q⟩

def keccak4xXor (a b : Vec256) : Vec256 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

def keccak4xRotl (a : Vec256) (k j : UInt64) : Vec256 :=
  ⟨rotlK a.w0 k j, rotlK a.w1 k j, rotlK a.w2 k j, rotlK a.w3 k j⟩

def keccak4xColumn (v : Nat → Vec256) (x : Nat) : Vec256 :=
  keccak4xXor (keccak4xXor (keccak4xXor (keccak4xXor (v x) (v (x+5)))
    (v (x+10))) (v (x+15))) (v (x+20))

def keccak4xD (v : Nat → Vec256) (x : Nat) : Vec256 :=
  keccak4xXor (keccak4xColumn v ((x+4)%5)) (keccak4xRotl (keccak4xColumn v ((x+1)%5)) 1 63)

def keccak4xTheta (v : Nat → Vec256) (i : Nat) : Vec256 :=
  keccak4xXor (v i) (keccak4xD v (i%5))

def keccak4xRhoPi (v : Nat → Vec256) : Nat → Vec256
  | 0 => v 0
  | 1 => keccak4xRotl (v 6) 44 20
  | 2 => keccak4xRotl (v 12) 43 21
  | 3 => keccak4xRotl (v 18) 21 43
  | 4 => keccak4xRotl (v 24) 14 50
  | 5 => keccak4xRotl (v 3) 28 36
  | 6 => keccak4xRotl (v 9) 20 44
  | 7 => keccak4xRotl (v 10) 3 61
  | 8 => keccak4xRotl (v 16) 45 19
  | 9 => keccak4xRotl (v 22) 61 3
  | 10 => keccak4xRotl (v 1) 1 63
  | 11 => keccak4xRotl (v 7) 6 58
  | 12 => keccak4xRotl (v 13) 25 39
  | 13 => keccak4xRotl (v 19) 8 56
  | 14 => keccak4xRotl (v 20) 18 46
  | 15 => keccak4xRotl (v 4) 27 37
  | 16 => keccak4xRotl (v 5) 36 28
  | 17 => keccak4xRotl (v 11) 10 54
  | 18 => keccak4xRotl (v 17) 15 49
  | 19 => keccak4xRotl (v 23) 56 8
  | 20 => keccak4xRotl (v 2) 62 2
  | 21 => keccak4xRotl (v 8) 55 9
  | 22 => keccak4xRotl (v 14) 39 25
  | 23 => keccak4xRotl (v 15) 41 23
  | 24 => keccak4xRotl (v 21) 2 62
  | _ => Vec256.zero

def keccak4xChiVec (a b c : Vec256) : Vec256 :=
  ⟨a.w0 ^^^ ((~~~b.w0) &&& c.w0), a.w1 ^^^ ((~~~b.w1) &&& c.w1),
   a.w2 ^^^ ((~~~b.w2) &&& c.w2), a.w3 ^^^ ((~~~b.w3) &&& c.w3)⟩

def keccak4xChi (v : Nat → Vec256) (i : Nat) : Vec256 :=
  keccak4xChiVec (v i) (v (5*(i/5) + (i+1)%5)) (v (5*(i/5) + (i+2)%5))

/-- SIMD round specification, acting on every word of every one of the 25 lanes. -/
def keccak4xRoundVec (v : Nat → Vec256) (rc : UInt64) (i : Nat) : Vec256 :=
  let c := keccak4xChi (keccak4xRhoPi (keccak4xTheta v)) i
  if i == 0 then keccak4xXor c ⟨rc,rc,rc,rc⟩ else c

/-- SIMD representation commutes with the canonical Keccak round on all four sponges. -/
theorem keccak4xRoundVec_reconstruct (v : Nat → Vec256) (rc : UInt64)
    (q : Nat) (hq : q < 4) :
    keccak4xLaneState (keccak4xRoundVec v rc) q = roundS (keccak4xLaneState v q) rc := by
  match q, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | n+4, h => exact False.elim (by omega)

theorem keccak4xRoundVec_tooth :
    keccak4xLaneState (keccak4xRoundVec (fun _ => Vec256.zero) 1) 0 ≠ zeroKState := by
  rw [zeroKState_eq]; kstate_ne

theorem keccak4xRoundVec_inhabited :
    ∃ (v : Nat → Vec256) (rc : UInt64) (q : Nat),
      q < 4 ∧ keccak4xLaneState v q = zeroKState ∧ rc = 0 := by
  exact ⟨fun _ => Vec256.zero, 0, 0, by decide, (by rw [zeroKState_eq]; rfl), rfl⟩

#tooth_pair keccak4xRoundVec_reconstruct vs keccak4xRoundVec_tooth
#verify_inhabited keccak4xRoundVec_reconstruct keccak4xRoundVec_inhabited

/-- Initial lane memory, in the machine's four-word interleaved layout. -/
def keccak4xSource (mem : UInt64 → UInt8) (p : UInt64) : Nat → Vec256
  | 0 => readMem256 mem (p + 0)
  | 1 => readMem256 mem (p + 32)
  | 2 => readMem256 mem (p + 64)
  | 3 => readMem256 mem (p + 96)
  | 4 => readMem256 mem (p + 128)
  | 5 => readMem256 mem (p + 160)
  | 6 => readMem256 mem (p + 192)
  | 7 => readMem256 mem (p + 224)
  | 8 => readMem256 mem (p + 256)
  | 9 => readMem256 mem (p + 288)
  | 10 => readMem256 mem (p + 320)
  | 11 => readMem256 mem (p + 352)
  | 12 => readMem256 mem (p + 384)
  | 13 => readMem256 mem (p + 416)
  | 14 => readMem256 mem (p + 448)
  | 15 => readMem256 mem (p + 480)
  | 16 => readMem256 mem (p + 512)
  | 17 => readMem256 mem (p + 544)
  | 18 => readMem256 mem (p + 576)
  | 19 => readMem256 mem (p + 608)
  | 20 => readMem256 mem (p + 640)
  | 21 => readMem256 mem (p + 672)
  | 22 => readMem256 mem (p + 704)
  | 23 => readMem256 mem (p + 736)
  | 24 => readMem256 mem (p + 768)
  | _ => Vec256.zero

private theorem keccak4x_u64xor_comm (a b : UInt64) : a ^^^ b = b ^^^ a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_xor, BitVec.xor_comm]


set_option maxHeartbeats 1000000 in
/-- The first 45 round-body instructions compute all five theta corrections,
for every word of all four interleaved sponges, without changing memory. -/
theorem keccak4x_parity_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf ofl zf dy : Bool) (mem : UInt64 → UInt8) :
    ∃ t, StepsX86 keccak4xProg 45 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 302 ∧ t.halted = false ∧ t.gpr = g ∧ t.mem = mem ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = keccak4xD (keccak4xSource mem (g.get 7)) x) := by
  have h1 : UInt64.ofNat 1 = (1 : UInt64) := by decide +kernel
  have h63 : UInt64.ofNat 63 = (63 : UInt64) := by decide +kernel
  iterate 45
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepX86, evalX86Addr, Bank16.get, Bank16.set, clampVecWidth,
          evalVecBin256, evalVecShift256, h1, h63]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, ?_⟩
  intro x hx
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [keccak4xD, keccak4xColumn, keccak4xSource, keccak4xRotl,
      keccak4xXor, rotlK, Bank16.get, keccak4x_u64xor_comm]
  | n+5, h => exact False.elim (by omega)


/-- Source-to-destination lane permutation used by the compiled rho/pi stores. -/
def keccak4xPerm : Nat → Nat
  | 0 => 0
  | 1 => 10
  | 2 => 20
  | 3 => 5
  | 4 => 15
  | 5 => 16
  | 6 => 1
  | 7 => 11
  | 8 => 21
  | 9 => 6
  | 10 => 7
  | 11 => 17
  | 12 => 2
  | 13 => 12
  | 14 => 22
  | 15 => 23
  | 16 => 8
  | 17 => 18
  | 18 => 3
  | 19 => 13
  | 20 => 14
  | 21 => 24
  | 22 => 9
  | 23 => 19
  | 24 => 4
  | _ => 0

def keccak4xPermInv : Nat → Nat
  | 0 => 0
  | 1 => 6
  | 2 => 12
  | 3 => 18
  | 4 => 24
  | 5 => 3
  | 6 => 9
  | 7 => 10
  | 8 => 16
  | 9 => 22
  | 10 => 1
  | 11 => 7
  | 12 => 13
  | 13 => 19
  | 14 => 20
  | 15 => 4
  | 16 => 5
  | 17 => 11
  | 18 => 17
  | 19 => 23
  | 20 => 2
  | 21 => 8
  | 22 => 14
  | 23 => 15
  | 24 => 21
  | _ => 0

theorem keccak4x_perm_lt (i : Nat) (hi : i < 25) : keccak4xPerm i < 25 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_permInv_lt (i : Nat) (hi : i < 25) : keccak4xPermInv i < 25 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_perm_leftInv (i : Nat) (hi : i < 25) : keccak4xPermInv (keccak4xPerm i) = i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_perm_rightInv (i : Nat) (hi : i < 25) : keccak4xPerm (keccak4xPermInv i) = i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

def keccak4xRhoRot (a : Vec256) : Nat → Vec256
  | 0 => a
  | 1 => keccak4xRotl a 1 63
  | 2 => keccak4xRotl a 62 2
  | 3 => keccak4xRotl a 28 36
  | 4 => keccak4xRotl a 27 37
  | 5 => keccak4xRotl a 36 28
  | 6 => keccak4xRotl a 44 20
  | 7 => keccak4xRotl a 6 58
  | 8 => keccak4xRotl a 55 9
  | 9 => keccak4xRotl a 20 44
  | 10 => keccak4xRotl a 3 61
  | 11 => keccak4xRotl a 10 54
  | 12 => keccak4xRotl a 43 21
  | 13 => keccak4xRotl a 25 39
  | 14 => keccak4xRotl a 39 25
  | 15 => keccak4xRotl a 41 23
  | 16 => keccak4xRotl a 45 19
  | 17 => keccak4xRotl a 15 49
  | 18 => keccak4xRotl a 21 43
  | 19 => keccak4xRotl a 8 56
  | 20 => keccak4xRotl a 18 46
  | 21 => keccak4xRotl a 2 62
  | 22 => keccak4xRotl a 61 3
  | 23 => keccak4xRotl a 56 8
  | 24 => keccak4xRotl a 14 50
  | _ => Vec256.zero

theorem keccak4x_rho_mapping (v : Nat → Vec256) (i : Nat) (hi : i < 25) :
    keccak4xRhoRot (keccak4xTheta v i) i =
      keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => rfl
  | n+25, h => exact False.elim (by omega)

/-- Modular disjointness: valid even when a region wraps around the address space. -/
def keccak4xDisjoint (a : UInt64) (n : Nat) (b : UInt64) (m : Nat) : Prop :=
  ∀ i j : Nat, i < n → j < m → a + UInt64.ofNat i ≠ b + UInt64.ofNat j

/-- Scratch writes are ordered exactly as rho/pi visits the source lanes. -/
def keccak4xScratchPrefix (m : UInt64 → UInt8) (sp : UInt64) (v : Nat → Vec256) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xScratchPrefix m sp v n)
      (sp + UInt64.ofNat (32 * keccak4xPerm n)) (keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm n))

private theorem keccak4x_read256_write_other (m : UInt64 → UInt8) (p : UInt64)
    (i j : Nat) (hi : i < 25) (hj : j < 25) (hne : i ≠ j) (v : Vec256) :
    readMem256 (writeMem256 m (p + UInt64.ofNat (32*i)) v) (p + UInt64.ofNat (32*j)) =
      readMem256 m (p + UInt64.ofNat (32*j)) := by
  apply keccakChiMpc_readMem256_writeMem256_disjoint
  intro a b ha hb he
  rw [u64_add_ofNat_assoc p (32*j) a (by omega),
    u64_add_ofNat_assoc p (32*i) b (by omega)] at he
  have := u64_add_ofNat_inj (by omega) (by omega) he
  omega

theorem keccak4xScratchPrefix_read (m : UInt64 → UInt8) (sp : UInt64) (v : Nat → Vec256)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v n) (sp + UInt64.ofNat (32*j)) =
      if keccak4xPermInv j < n then keccak4xRhoPi (keccak4xTheta v) j
      else readMem256 m (sp + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => simp [keccak4xScratchPrefix]
  | succ n ih =>
    have hlt : n < 25 := by omega
    rw [keccak4xScratchPrefix]
    by_cases he : keccak4xPerm n = j
    · rw [he, keccakChiMpc_readMem256_writeMem256_same]
      have hinv : keccak4xPermInv j = n := by
        rw [← he]
        exact keccak4x_perm_leftInv n hlt
      simp [hinv]
    · rw [keccak4x_read256_write_other _ sp (keccak4xPerm n) j
        (keccak4x_perm_lt n hlt) hj he, ih (by omega)]
      have hne : keccak4xPermInv j ≠ n := by
        intro e
        have hperm := congrArg keccak4xPerm e
        rw [keccak4x_perm_rightInv j hj] at hperm
        exact he hperm.symm
      by_cases hl : keccak4xPermInv j < n
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]

theorem keccak4xScratchPrefix_complete (m : UInt64 → UInt8) (sp : UInt64)
    (v : Nat → Vec256) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v 25) (sp + UInt64.ofNat (32*j)) =
      keccak4xRhoPi (keccak4xTheta v) j := by
  rw [keccak4xScratchPrefix_read _ _ _ 25 (by decide) j hj,
    ite_eq_left (keccak4x_permInv_lt j hj)]

/-- Rho/pi scratch writes preserve every input-state vector. -/
theorem keccak4xScratchPrefix_input (m : UInt64 → UInt8) (sp p : UInt64)
    (v : Nat → Vec256) (hd : keccak4xDisjoint p 800 sp 800)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v n) (p + UInt64.ofNat (32*j)) =
      readMem256 m (p + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix]
    have hlt := keccak4x_perm_lt n (by omega)
    rw [keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc p (32*j) a (by omega),
        u64_add_ofNat_assoc sp (32*keccak4xPerm n) b (by omega)] at he
      exact hd (32*j+a) (32*keccak4xPerm n+b) (by omega) (by omega) he

theorem keccak4xSource_eq (m : UInt64 → UInt8) (p : UInt64) (j : Nat) (hj : j < 25) :
    keccak4xSource m p j = readMem256 m (p + UInt64.ofNat (32*j)) := by
  match j, hj with
  | 0, _ =>
    change readMem256 m (p + 0) = readMem256 m (p + UInt64.ofNat (32*0))
    have h : UInt64.ofNat (32*0) = (0 : UInt64) := by decide +kernel
    rw [h]
  | 1, _ =>
    change readMem256 m (p + 32) = readMem256 m (p + UInt64.ofNat (32*1))
    have h : UInt64.ofNat (32*1) = (32 : UInt64) := by decide +kernel
    rw [h]
  | 2, _ =>
    change readMem256 m (p + 64) = readMem256 m (p + UInt64.ofNat (32*2))
    have h : UInt64.ofNat (32*2) = (64 : UInt64) := by decide +kernel
    rw [h]
  | 3, _ =>
    change readMem256 m (p + 96) = readMem256 m (p + UInt64.ofNat (32*3))
    have h : UInt64.ofNat (32*3) = (96 : UInt64) := by decide +kernel
    rw [h]
  | 4, _ =>
    change readMem256 m (p + 128) = readMem256 m (p + UInt64.ofNat (32*4))
    have h : UInt64.ofNat (32*4) = (128 : UInt64) := by decide +kernel
    rw [h]
  | 5, _ =>
    change readMem256 m (p + 160) = readMem256 m (p + UInt64.ofNat (32*5))
    have h : UInt64.ofNat (32*5) = (160 : UInt64) := by decide +kernel
    rw [h]
  | 6, _ =>
    change readMem256 m (p + 192) = readMem256 m (p + UInt64.ofNat (32*6))
    have h : UInt64.ofNat (32*6) = (192 : UInt64) := by decide +kernel
    rw [h]
  | 7, _ =>
    change readMem256 m (p + 224) = readMem256 m (p + UInt64.ofNat (32*7))
    have h : UInt64.ofNat (32*7) = (224 : UInt64) := by decide +kernel
    rw [h]
  | 8, _ =>
    change readMem256 m (p + 256) = readMem256 m (p + UInt64.ofNat (32*8))
    have h : UInt64.ofNat (32*8) = (256 : UInt64) := by decide +kernel
    rw [h]
  | 9, _ =>
    change readMem256 m (p + 288) = readMem256 m (p + UInt64.ofNat (32*9))
    have h : UInt64.ofNat (32*9) = (288 : UInt64) := by decide +kernel
    rw [h]
  | 10, _ =>
    change readMem256 m (p + 320) = readMem256 m (p + UInt64.ofNat (32*10))
    have h : UInt64.ofNat (32*10) = (320 : UInt64) := by decide +kernel
    rw [h]
  | 11, _ =>
    change readMem256 m (p + 352) = readMem256 m (p + UInt64.ofNat (32*11))
    have h : UInt64.ofNat (32*11) = (352 : UInt64) := by decide +kernel
    rw [h]
  | 12, _ =>
    change readMem256 m (p + 384) = readMem256 m (p + UInt64.ofNat (32*12))
    have h : UInt64.ofNat (32*12) = (384 : UInt64) := by decide +kernel
    rw [h]
  | 13, _ =>
    change readMem256 m (p + 416) = readMem256 m (p + UInt64.ofNat (32*13))
    have h : UInt64.ofNat (32*13) = (416 : UInt64) := by decide +kernel
    rw [h]
  | 14, _ =>
    change readMem256 m (p + 448) = readMem256 m (p + UInt64.ofNat (32*14))
    have h : UInt64.ofNat (32*14) = (448 : UInt64) := by decide +kernel
    rw [h]
  | 15, _ =>
    change readMem256 m (p + 480) = readMem256 m (p + UInt64.ofNat (32*15))
    have h : UInt64.ofNat (32*15) = (480 : UInt64) := by decide +kernel
    rw [h]
  | 16, _ =>
    change readMem256 m (p + 512) = readMem256 m (p + UInt64.ofNat (32*16))
    have h : UInt64.ofNat (32*16) = (512 : UInt64) := by decide +kernel
    rw [h]
  | 17, _ =>
    change readMem256 m (p + 544) = readMem256 m (p + UInt64.ofNat (32*17))
    have h : UInt64.ofNat (32*17) = (544 : UInt64) := by decide +kernel
    rw [h]
  | 18, _ =>
    change readMem256 m (p + 576) = readMem256 m (p + UInt64.ofNat (32*18))
    have h : UInt64.ofNat (32*18) = (576 : UInt64) := by decide +kernel
    rw [h]
  | 19, _ =>
    change readMem256 m (p + 608) = readMem256 m (p + UInt64.ofNat (32*19))
    have h : UInt64.ofNat (32*19) = (608 : UInt64) := by decide +kernel
    rw [h]
  | 20, _ =>
    change readMem256 m (p + 640) = readMem256 m (p + UInt64.ofNat (32*20))
    have h : UInt64.ofNat (32*20) = (640 : UInt64) := by decide +kernel
    rw [h]
  | 21, _ =>
    change readMem256 m (p + 672) = readMem256 m (p + UInt64.ofNat (32*21))
    have h : UInt64.ofNat (32*21) = (672 : UInt64) := by decide +kernel
    rw [h]
  | 22, _ =>
    change readMem256 m (p + 704) = readMem256 m (p + UInt64.ofNat (32*22))
    have h : UInt64.ofNat (32*22) = (704 : UInt64) := by decide +kernel
    rw [h]
  | 23, _ =>
    change readMem256 m (p + 736) = readMem256 m (p + UInt64.ofNat (32*23))
    have h : UInt64.ofNat (32*23) = (736 : UInt64) := by decide +kernel
    rw [h]
  | 24, _ =>
    change readMem256 m (p + 768) = readMem256 m (p + UInt64.ofNat (32*24))
    have h : UInt64.ofNat (32*24) = (768 : UInt64) := by decide +kernel
    rw [h]
  | n+25, h => exact False.elim (by omega)

theorem keccak4xLaneState_congr (v w : Nat → Vec256)
    (h : ∀ j : Nat, j < 25 → v j = w j) (q : Nat) :
    keccak4xLaneState v q = keccak4xLaneState w q := by
  unfold keccak4xLaneState
  simp only [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide)]

/-- The public round-constant read survives all rho/pi scratch writes. -/
theorem keccak4xScratchPrefix_constant (m : UInt64 → UInt8) (sp rp : UInt64)
    (v : Nat → Vec256) (hd : keccak4xDisjoint rp 8 sp 800)
    (n : Nat) (hn : n ≤ 25) :
    readMem64 (keccak4xScratchPrefix m sp v n) rp = readMem64 m rp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix]
    have hlt := keccak4x_perm_lt n (by omega)
    rw [keccakChiMpc_readMem64_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc sp (32*keccak4xPerm n) b (by omega)] at he
      exact hd a (32*keccak4xPerm n+b) ha (by omega) he

/-- Final state writes are ordered in chi row order. -/
def keccak4xStatePrefix (m : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xStatePrefix m p v rc n)
      (p + UInt64.ofNat (32*n)) (keccak4xRoundVec v rc n)

theorem keccak4xStatePrefix_read (m : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xStatePrefix m p v rc n) (p + UInt64.ofNat (32*j)) =
      if j < n then keccak4xRoundVec v rc j
      else readMem256 m (p + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => simp [keccak4xStatePrefix]
  | succ n ih =>
    rw [keccak4xStatePrefix]
    by_cases he : n = j
    · rw [he, keccakChiMpc_readMem256_writeMem256_same]
      simp
    · rw [keccak4x_read256_write_other _ p n j (by omega) hj he, ih (by omega)]
      by_cases hl : j < n
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]

/-- State writes do not disturb the 25 rho/pi scratch vectors needed by later rows. -/
theorem keccak4xStatePrefix_scratch (m : UInt64 → UInt8) (p sp : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (hd : keccak4xDisjoint sp 800 p 800)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xStatePrefix m p v rc n) (sp + UInt64.ofNat (32*j)) =
      readMem256 m (sp + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xStatePrefix]
    rw [keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc sp (32*j) a (by omega),
        u64_add_ofNat_assoc p (32*n) b (by omega)] at he
      exact hd (32*j+a) (32*n+b) (by omega) (by omega) he

/-- Whole-memory specification of one round, including its scratch-buffer effects. -/
def keccak4xRoundMem (m : UInt64 → UInt8) (p sp rp : UInt64) : UInt64 → UInt8 :=
  let v := keccak4xSource m p
  keccak4xStatePrefix (keccak4xScratchPrefix m sp v 25) p v (readMem64 m rp) 25

/-- Full readback of the round memory specification, all 25 lanes of all four states. -/
theorem keccak4xRoundMem_readback (m : UInt64 → UInt8) (p sp rp : UInt64)
    (q : Nat) (hq : q < 4) :
    keccak4xLaneState (keccak4xSource (keccak4xRoundMem m p sp rp) p) q =
      roundS (keccak4xLaneState (keccak4xSource m p) q) (readMem64 m rp) := by
  calc
    _ = keccak4xLaneState (keccak4xRoundVec (keccak4xSource m p) (readMem64 m rp)) q := by
      apply keccak4xLaneState_congr
      intro j hj
      rw [keccak4xSource_eq _ _ j hj]
      unfold keccak4xRoundMem
      rw [keccak4xStatePrefix_read _ _ _ _ 25 (by decide) j hj, ite_eq_left hj]
    _ = _ := keccak4xRoundVec_reconstruct _ _ q hq

def keccak4xOffset : Nat → UInt64
  | 0 => 0
  | 1 => 32
  | 2 => 64
  | 3 => 96
  | 4 => 128
  | 5 => 160
  | 6 => 192
  | 7 => 224
  | 8 => 256
  | 9 => 288
  | 10 => 320
  | 11 => 352
  | 12 => 384
  | 13 => 416
  | 14 => 448
  | 15 => 480
  | 16 => 512
  | 17 => 544
  | 18 => 576
  | 19 => 608
  | 20 => 640
  | 21 => 672
  | 22 => 704
  | 23 => 736
  | 24 => 768
  | _ => 0

theorem keccak4xOffset_eq (i : Nat) (hi : i < 25) :
    keccak4xOffset i = UInt64.ofNat (32*i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

def keccak4xRhoPc : Nat → Nat
  | 0 => 302
  | 1 => 311
  | 2 => 339
  | 3 => 367
  | 4 => 395
  | 5 => 426
  | 6 => 457
  | 7 => 485
  | 8 => 516
  | 9 => 547
  | 10 => 578
  | 11 => 609
  | 12 => 640
  | 13 => 668
  | 14 => 699
  | 15 => 730
  | 16 => 761
  | 17 => 792
  | 18 => 823
  | 19 => 851
  | 20 => 882
  | 21 => 913
  | 22 => 944
  | 23 => 975
  | 24 => 1006
  | 25 => 1037
  | _ => 1037

def keccak4xRhoCount (i : Nat) : Nat := if i == 0 then 2 else 5

theorem keccak4x_rho0_steps (s : X86State) (hp : s.pc = 302) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 0) = a) :
    ∃ t, StepsX86 keccak4xProg 2 s t ∧
      t.pc = 311 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 0)
        (keccak4xRhoRot (keccak4xXor d a) 0) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  iterate 2
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho1_steps (s : X86State) (hp : s.pc = 311) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 32) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 339 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 320)
        (keccak4xRhoRot (keccak4xXor d a) 1) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 1 = (1 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 63 = (63 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho2_steps (s : X86State) (hp : s.pc = 339) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 64) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 367 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 640)
        (keccak4xRhoRot (keccak4xXor d a) 2) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 62 = (62 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 2 = (2 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho3_steps (s : X86State) (hp : s.pc = 367) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 96) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 395 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 160)
        (keccak4xRhoRot (keccak4xXor d a) 3) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 28 = (28 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 36 = (36 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho4_steps (s : X86State) (hp : s.pc = 395) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 128) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 426 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 480)
        (keccak4xRhoRot (keccak4xXor d a) 4) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 27 = (27 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 37 = (37 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho5_steps (s : X86State) (hp : s.pc = 426) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 160) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 457 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 512)
        (keccak4xRhoRot (keccak4xXor d a) 5) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 36 = (36 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 28 = (28 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho6_steps (s : X86State) (hp : s.pc = 457) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 192) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 485 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 32)
        (keccak4xRhoRot (keccak4xXor d a) 6) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 44 = (44 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 20 = (20 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho7_steps (s : X86State) (hp : s.pc = 485) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 224) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 516 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 352)
        (keccak4xRhoRot (keccak4xXor d a) 7) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 6 = (6 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 58 = (58 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho8_steps (s : X86State) (hp : s.pc = 516) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 256) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 547 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 672)
        (keccak4xRhoRot (keccak4xXor d a) 8) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 55 = (55 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 9 = (9 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho9_steps (s : X86State) (hp : s.pc = 547) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 288) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 578 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 192)
        (keccak4xRhoRot (keccak4xXor d a) 9) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 20 = (20 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 44 = (44 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho10_steps (s : X86State) (hp : s.pc = 578) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 320) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 609 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 224)
        (keccak4xRhoRot (keccak4xXor d a) 10) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 3 = (3 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 61 = (61 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho11_steps (s : X86State) (hp : s.pc = 609) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 352) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 640 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 544)
        (keccak4xRhoRot (keccak4xXor d a) 11) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 10 = (10 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 54 = (54 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho12_steps (s : X86State) (hp : s.pc = 640) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 384) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 668 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 64)
        (keccak4xRhoRot (keccak4xXor d a) 12) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 43 = (43 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 21 = (21 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho13_steps (s : X86State) (hp : s.pc = 668) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 416) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 699 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 384)
        (keccak4xRhoRot (keccak4xXor d a) 13) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 39 = (39 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho14_steps (s : X86State) (hp : s.pc = 699) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 448) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 730 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 704)
        (keccak4xRhoRot (keccak4xXor d a) 14) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 39 = (39 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho15_steps (s : X86State) (hp : s.pc = 730) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 480) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 761 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 736)
        (keccak4xRhoRot (keccak4xXor d a) 15) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 41 = (41 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 23 = (23 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho16_steps (s : X86State) (hp : s.pc = 761) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 512) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 792 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 256)
        (keccak4xRhoRot (keccak4xXor d a) 16) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 45 = (45 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 19 = (19 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho17_steps (s : X86State) (hp : s.pc = 792) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 544) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 823 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 576)
        (keccak4xRhoRot (keccak4xXor d a) 17) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 15 = (15 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 49 = (49 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho18_steps (s : X86State) (hp : s.pc = 823) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 576) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 851 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 96)
        (keccak4xRhoRot (keccak4xXor d a) 18) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 21 = (21 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 43 = (43 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho19_steps (s : X86State) (hp : s.pc = 851) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 608) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 882 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 416)
        (keccak4xRhoRot (keccak4xXor d a) 19) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 56 = (56 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho20_steps (s : X86State) (hp : s.pc = 882) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 640) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 913 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 448)
        (keccak4xRhoRot (keccak4xXor d a) 20) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 18 = (18 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 46 = (46 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho21_steps (s : X86State) (hp : s.pc = 913) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 672) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 944 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 768)
        (keccak4xRhoRot (keccak4xXor d a) 21) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 2 = (2 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 62 = (62 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho22_steps (s : X86State) (hp : s.pc = 944) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 704) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 975 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 288)
        (keccak4xRhoRot (keccak4xXor d a) 22) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 61 = (61 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 3 = (3 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho23_steps (s : X86State) (hp : s.pc = 975) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 736) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 1006 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 608)
        (keccak4xRhoRot (keccak4xXor d a) 23) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 56 = (56 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho24_steps (s : X86State) (hp : s.pc = 1006) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 768) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 1037 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 128)
        (keccak4xRhoRot (keccak4xXor d a) 24) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 14 = (14 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 50 = (50 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho_steps (s : X86State) (i : Nat) (hi : i < 25)
    (hp : s.pc = keccak4xRhoPc i) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get (5+i%5) = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + keccak4xOffset i) = a) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoCount i) s t ∧
      t.pc = keccak4xRhoPc (i+1) ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + keccak4xOffset (keccak4xPerm i))
        (keccak4xRhoRot (keccak4xXor d a) i) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  match i, hi with
  | 0, _ => exact keccak4x_rho0_steps s hp hh a d hd ha
  | 1, _ => exact keccak4x_rho1_steps s hp hh a d hd ha
  | 2, _ => exact keccak4x_rho2_steps s hp hh a d hd ha
  | 3, _ => exact keccak4x_rho3_steps s hp hh a d hd ha
  | 4, _ => exact keccak4x_rho4_steps s hp hh a d hd ha
  | 5, _ => exact keccak4x_rho5_steps s hp hh a d hd ha
  | 6, _ => exact keccak4x_rho6_steps s hp hh a d hd ha
  | 7, _ => exact keccak4x_rho7_steps s hp hh a d hd ha
  | 8, _ => exact keccak4x_rho8_steps s hp hh a d hd ha
  | 9, _ => exact keccak4x_rho9_steps s hp hh a d hd ha
  | 10, _ => exact keccak4x_rho10_steps s hp hh a d hd ha
  | 11, _ => exact keccak4x_rho11_steps s hp hh a d hd ha
  | 12, _ => exact keccak4x_rho12_steps s hp hh a d hd ha
  | 13, _ => exact keccak4x_rho13_steps s hp hh a d hd ha
  | 14, _ => exact keccak4x_rho14_steps s hp hh a d hd ha
  | 15, _ => exact keccak4x_rho15_steps s hp hh a d hd ha
  | 16, _ => exact keccak4x_rho16_steps s hp hh a d hd ha
  | 17, _ => exact keccak4x_rho17_steps s hp hh a d hd ha
  | 18, _ => exact keccak4x_rho18_steps s hp hh a d hd ha
  | 19, _ => exact keccak4x_rho19_steps s hp hh a d hd ha
  | 20, _ => exact keccak4x_rho20_steps s hp hh a d hd ha
  | 21, _ => exact keccak4x_rho21_steps s hp hh a d hd ha
  | 22, _ => exact keccak4x_rho22_steps s hp hh a d hd ha
  | 23, _ => exact keccak4x_rho23_steps s hp hh a d hd ha
  | 24, _ => exact keccak4x_rho24_steps s hp hh a d hd ha
  | n+25, h => exact False.elim (by omega)

private theorem keccak4xXor_comm (a b : Vec256) : keccak4xXor a b = keccak4xXor b a := by
  cases a
  cases b
  unfold keccak4xXor
  congr 1 <;> exact keccak4x_u64xor_comm _ _

/-- The progressively filled rho/pi scratch area and the five live theta corrections. -/
structure keccak4xRhoInv (mem : UInt64 → UInt8) (g : Bank16 UInt64) (n : Nat) (s : X86State) : Prop where
  pc : s.pc = keccak4xRhoPc n
  halted : s.halted = false
  gpr : s.gpr = g
  memory : s.mem = keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) n
  corrections : ∀ x : Nat, x < 5 → s.ymm.get (5+x) = keccak4xD (keccak4xSource mem (g.get 7)) x

private theorem keccak4x_rho_value (v : Nat → Vec256) (n : Nat) (hn : n < 25) :
    keccak4xRhoRot (keccak4xXor (keccak4xD v (n%5)) (v n)) n =
      keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm n) := by
  rw [keccak4xXor_comm]
  exact keccak4x_rho_mapping v n hn

theorem keccak4xRhoInv_step (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (n : Nat) (hn : n < 25) (s : X86State) (h : keccak4xRhoInv mem g n s) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoCount n) s t ∧ keccak4xRhoInv mem g (n+1) t := by
  let v := keccak4xSource mem (g.get 7)
  have ha : readMem256 s.mem (s.gpr.get 7 + keccak4xOffset n) = v n := by
    rw [h.gpr, h.memory, keccak4xOffset_eq n hn,
      keccak4xScratchPrefix_input mem (g.get 4) (g.get 7) v hd n (by omega) n hn]
    exact (keccak4xSource_eq mem (g.get 7) n hn).symm
  obtain ⟨t, ht, hp, hh, hg, hm, hv⟩ := keccak4x_rho_steps s n hn h.pc h.halted
    (v n) (keccak4xD v (n%5)) (h.corrections (n%5) (Nat.mod_lt _ (by decide))) ha
  refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_, ?_⟩
  · rw [hm, h.gpr, h.memory, keccak4xOffset_eq (keccak4xPerm n) (keccak4x_perm_lt n hn),
      keccak4x_rho_value v n hn]
    rfl
  · intro x hx
    rw [hv x hx]
    exact h.corrections x hx

def keccak4xRhoFuel : Nat → Nat
  | 0 => 0
  | n+1 => keccak4xRhoFuel n + keccak4xRhoCount n

theorem keccak4xRhoInv_iter (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (s : X86State) (h : keccak4xRhoInv mem g 0 s) (n : Nat) (hn : n ≤ 25) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoFuel n) s t ∧ keccak4xRhoInv mem g n t := by
  induction n with
  | zero => exact ⟨s, StepsX86.zero _, h⟩
  | succ n ih =>
    obtain ⟨t, ht, hi⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4xRhoInv_step mem g hd n (by omega) t hi
    exact ⟨u, StepsX86_trans ht hu, hiu⟩

theorem keccak4xRhoFuel_full : keccak4xRhoFuel 25 = 122 := by decide +kernel

/-- The 167-instruction theta/rho/pi prefix on four complete Keccak states. -/
theorem keccak4x_theta_rho_pi_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 167 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 1037 ∧ t.halted = false ∧ t.gpr = g ∧
      t.mem = keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) 25 := by
  obtain ⟨t, ht, hp, hh, hg, hm, hv⟩ := keccak4x_parity_steps g y cf ofl zf dy mem
  have hi : keccak4xRhoInv mem g 0 t := ⟨hp, hh, hg, hm, hv⟩
  obtain ⟨u, hu, hiu⟩ := keccak4xRhoInv_iter mem g hd t hi 25 (by decide)
  rw [keccak4xRhoFuel_full] at hu
  exact ⟨u, StepsX86_trans ht hu, hiu.pc, hiu.halted, hiu.gpr, hiu.memory⟩

def keccak4xRowMem0 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xXor (keccak4xChiVec a0 a1 a2) ⟨rc,rc,rc,rc⟩
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 0) c0
  let m1 := writeMem256 m0 (p + 32) c1
  let m2 := writeMem256 m1 (p + 64) c2
  let m3 := writeMem256 m2 (p + 96) c3
  let m4 := writeMem256 m3 (p + 128) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row0_steps (s : X86State) (hp : s.pc = 1037) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 0) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 32) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 64) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 96) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 128) = a4)
    (hr : readMem64 s.mem (s.gpr.get 6 + 0) = rc)
    : ∃ t, StepsX86 keccak4xProg 22 s t ∧
      t.pc = 1145 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem0 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4 hr
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4 hr
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  have hrc0 := keccak4x_u64xor_comm rc (a0.w0 ^^^ ((~~~a1.w0) &&& a2.w0))
  have hrc1 := keccak4x_u64xor_comm rc (a0.w1 ^^^ ((~~~a1.w1) &&& a2.w1))
  have hrc2 := keccak4x_u64xor_comm rc (a0.w2 ^^^ ((~~~a1.w2) &&& a2.w2))
  have hrc3 := keccak4x_u64xor_comm rc (a0.w3 ^^^ ((~~~a1.w3) &&& a2.w3))
  iterate 22
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4, hr]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3, hrc0, hrc1, hrc2, hrc3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem0, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem1 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 160) c0
  let m1 := writeMem256 m0 (p + 192) c1
  let m2 := writeMem256 m1 (p + 224) c2
  let m3 := writeMem256 m2 (p + 256) c3
  let m4 := writeMem256 m3 (p + 288) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row1_steps (s : X86State) (hp : s.pc = 1145) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 160) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 192) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 224) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 256) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 288) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1270 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem1 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem1, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem2 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 320) c0
  let m1 := writeMem256 m0 (p + 352) c1
  let m2 := writeMem256 m1 (p + 384) c2
  let m3 := writeMem256 m2 (p + 416) c3
  let m4 := writeMem256 m3 (p + 448) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row2_steps (s : X86State) (hp : s.pc = 1270) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 320) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 352) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 384) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 416) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 448) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1395 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem2 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem2, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem3 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 480) c0
  let m1 := writeMem256 m0 (p + 512) c1
  let m2 := writeMem256 m1 (p + 544) c2
  let m3 := writeMem256 m2 (p + 576) c3
  let m4 := writeMem256 m3 (p + 608) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row3_steps (s : X86State) (hp : s.pc = 1395) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 480) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 512) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 544) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 576) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 608) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1520 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem3 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem3, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem4 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 640) c0
  let m1 := writeMem256 m0 (p + 672) c1
  let m2 := writeMem256 m1 (p + 704) c2
  let m3 := writeMem256 m2 (p + 736) c3
  let m4 := writeMem256 m3 (p + 768) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row4_steps (s : X86State) (hp : s.pc = 1520) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 640) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 672) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 704) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 736) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 768) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1645 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem4 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem4, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]


private theorem keccak4xDisjoint_symm (a b : UInt64) (n m : Nat)
    (h : keccak4xDisjoint a n b m) : keccak4xDisjoint b m a n := by
  intro i j hi hj he
  exact h j i hj hi he.symm

theorem keccak4xRowMem0_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem0 (keccak4xStatePrefix m p v rc 0) p
      (keccak4xRhoPi (keccak4xTheta v) 0) (keccak4xRhoPi (keccak4xTheta v) 1) (keccak4xRhoPi (keccak4xTheta v) 2) (keccak4xRhoPi (keccak4xTheta v) 3) (keccak4xRhoPi (keccak4xTheta v) 4) rc =
    keccak4xStatePrefix m p v rc 5 := by
  have h0 : UInt64.ofNat (32*0) = (0 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*1) = (32 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*2) = (64 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*3) = (96 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*4) = (128 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem0, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem1_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem1 (keccak4xStatePrefix m p v rc 5) p
      (keccak4xRhoPi (keccak4xTheta v) 5) (keccak4xRhoPi (keccak4xTheta v) 6) (keccak4xRhoPi (keccak4xTheta v) 7) (keccak4xRhoPi (keccak4xTheta v) 8) (keccak4xRhoPi (keccak4xTheta v) 9) rc =
    keccak4xStatePrefix m p v rc 10 := by
  have h0 : UInt64.ofNat (32*5) = (160 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*6) = (192 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*7) = (224 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*8) = (256 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*9) = (288 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem1, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem2_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem2 (keccak4xStatePrefix m p v rc 10) p
      (keccak4xRhoPi (keccak4xTheta v) 10) (keccak4xRhoPi (keccak4xTheta v) 11) (keccak4xRhoPi (keccak4xTheta v) 12) (keccak4xRhoPi (keccak4xTheta v) 13) (keccak4xRhoPi (keccak4xTheta v) 14) rc =
    keccak4xStatePrefix m p v rc 15 := by
  have h0 : UInt64.ofNat (32*10) = (320 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*11) = (352 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*12) = (384 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*13) = (416 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*14) = (448 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem2, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem3_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem3 (keccak4xStatePrefix m p v rc 15) p
      (keccak4xRhoPi (keccak4xTheta v) 15) (keccak4xRhoPi (keccak4xTheta v) 16) (keccak4xRhoPi (keccak4xTheta v) 17) (keccak4xRhoPi (keccak4xTheta v) 18) (keccak4xRhoPi (keccak4xTheta v) 19) rc =
    keccak4xStatePrefix m p v rc 20 := by
  have h0 : UInt64.ofNat (32*15) = (480 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*16) = (512 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*17) = (544 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*18) = (576 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*19) = (608 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem3, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem4_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem4 (keccak4xStatePrefix m p v rc 20) p
      (keccak4xRhoPi (keccak4xTheta v) 20) (keccak4xRhoPi (keccak4xTheta v) 21) (keccak4xRhoPi (keccak4xTheta v) 22) (keccak4xRhoPi (keccak4xTheta v) 23) (keccak4xRhoPi (keccak4xTheta v) 24) rc =
    keccak4xStatePrefix m p v rc 25 := by
  have h0 : UInt64.ofNat (32*20) = (640 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*21) = (672 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*22) = (704 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*23) = (736 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*24) = (768 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem4, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

def keccak4xRowPc : Nat → Nat
  | 0 => 1037 | 1 => 1145 | 2 => 1270 | 3 => 1395 | 4 => 1520 | _ => 1645

def keccak4xRowCount (r : Nat) : Nat := if r == 0 then 22 else 20

structure keccak4xRowInv (mem : UInt64 → UInt8) (g : Bank16 UInt64) (r : Nat) (s : X86State) : Prop where
  pc : s.pc = keccak4xRowPc r
  halted : s.halted = false
  gpr : s.gpr = g
  memory : s.mem = keccak4xStatePrefix
    (keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) 25)
    (g.get 7) (keccak4xSource mem (g.get 7)) (readMem64 mem (g.get 6)) (5*r)

theorem keccak4xRowInv_read (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (r : Nat) (hr : r ≤ 5) (s : X86State) (h : keccak4xRowInv mem g r s)
    (j : Nat) (hj : j < 25) :
    readMem256 s.mem (s.gpr.get 4 + keccak4xOffset j) =
      keccak4xRhoPi (keccak4xTheta (keccak4xSource mem (g.get 7))) j := by
  rw [h.gpr, h.memory, keccak4xOffset_eq j hj,
    keccak4xStatePrefix_scratch _ _ _ _ _
      (keccak4xDisjoint_symm _ _ _ _ hd) (5*r) (by omega) j hj,
    keccak4xScratchPrefix_complete _ _ _ j hj]

theorem keccak4xRowInv_step (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800)
    (r : Nat) (hr : r < 5) (s : X86State) (h : keccak4xRowInv mem g r s) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRowCount r) s t ∧ keccak4xRowInv mem g (r+1) t := by
  let v := keccak4xSource mem (g.get 7)
  have hread := keccak4xRowInv_read mem g hd r (by omega) s h
  match r, hr with
  | 0, _ =>
    have hconst : readMem64 s.mem (s.gpr.get 6 + 0) = readMem64 mem (g.get 6) := by
      rw [UInt64.add_zero, h.gpr, h.memory]
      exact keccak4xScratchPrefix_constant mem (g.get 4) (g.get 6) v hc 25 (by decide)
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row0_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 0) (keccak4xRhoPi (keccak4xTheta v) 1) (keccak4xRhoPi (keccak4xTheta v) 2) (keccak4xRhoPi (keccak4xTheta v) 3) (keccak4xRhoPi (keccak4xTheta v) 4) (readMem64 mem (g.get 6))
      (hread 0 (by decide)) (hread 1 (by decide)) (hread 2 (by decide)) (hread 3 (by decide)) (hread 4 (by decide)) hconst
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem0_prefix]
  | 1, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row1_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 5) (keccak4xRhoPi (keccak4xTheta v) 6) (keccak4xRhoPi (keccak4xTheta v) 7) (keccak4xRhoPi (keccak4xTheta v) 8) (keccak4xRhoPi (keccak4xTheta v) 9) (readMem64 mem (g.get 6))
      (hread 5 (by decide)) (hread 6 (by decide)) (hread 7 (by decide)) (hread 8 (by decide)) (hread 9 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem1_prefix]
  | 2, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row2_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 10) (keccak4xRhoPi (keccak4xTheta v) 11) (keccak4xRhoPi (keccak4xTheta v) 12) (keccak4xRhoPi (keccak4xTheta v) 13) (keccak4xRhoPi (keccak4xTheta v) 14) (readMem64 mem (g.get 6))
      (hread 10 (by decide)) (hread 11 (by decide)) (hread 12 (by decide)) (hread 13 (by decide)) (hread 14 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem2_prefix]
  | 3, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row3_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 15) (keccak4xRhoPi (keccak4xTheta v) 16) (keccak4xRhoPi (keccak4xTheta v) 17) (keccak4xRhoPi (keccak4xTheta v) 18) (keccak4xRhoPi (keccak4xTheta v) 19) (readMem64 mem (g.get 6))
      (hread 15 (by decide)) (hread 16 (by decide)) (hread 17 (by decide)) (hread 18 (by decide)) (hread 19 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem3_prefix]
  | 4, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row4_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 20) (keccak4xRhoPi (keccak4xTheta v) 21) (keccak4xRhoPi (keccak4xTheta v) 22) (keccak4xRhoPi (keccak4xTheta v) 23) (keccak4xRhoPi (keccak4xTheta v) 24) (readMem64 mem (g.get 6))
      (hread 20 (by decide)) (hread 21 (by decide)) (hread 22 (by decide)) (hread 23 (by decide)) (hread 24 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem4_prefix]
  | n+5, hh => exact False.elim (by omega)

def keccak4xRowFuel : Nat → Nat
  | 0 => 0
  | r+1 => keccak4xRowFuel r + keccak4xRowCount r

theorem keccak4xRowInv_iter (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800)
    (s : X86State) (h : keccak4xRowInv mem g 0 s) (r : Nat) (hr : r ≤ 5) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRowFuel r) s t ∧ keccak4xRowInv mem g r t := by
  induction r with
  | zero => exact ⟨s, StepsX86.zero _, h⟩
  | succ r ih =>
    obtain ⟨t, ht, hi⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4xRowInv_step mem g hd hc r (by omega) t hi
    exact ⟨u, StepsX86_trans ht hu, hiu⟩

theorem keccak4xRowFuel_full : keccak4xRowFuel 5 = 102 := by decide +kernel

/-- Every instruction computing one round, stopping before public counter maintenance. -/
theorem keccak4x_round_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 269 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 1645 ∧ t.halted = false ∧ t.gpr = g ∧
      t.mem = keccak4xRoundMem mem (g.get 7) (g.get 4) (g.get 6) := by
  obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_theta_rho_pi_steps g y cf ofl zf dy mem hd
  have hi : keccak4xRowInv mem g 0 t := ⟨hp, hh, hg, hm⟩
  obtain ⟨u, hu, hiu⟩ := keccak4xRowInv_iter mem g hd hc t hi 5 (by decide)
  rw [keccak4xRowFuel_full] at hu
  exact ⟨u, StepsX86_trans ht hu, hiu.pc, hiu.halted, hiu.gpr, hiu.memory⟩

/-- Entry to the decoded round body after the prologue, with honest buffer separation.
The selected public table word may be any UInt64; round selection is handled by the loop. -/
def keccak4xRoundEntry (s : X86State) : Prop :=
  s.pc = 20 ∧ s.halted = false ∧
    keccak4xDisjoint (s.gpr.get 7) 800 (s.gpr.get 4) 800 ∧
    keccak4xDisjoint (s.gpr.get 6) 8 (s.gpr.get 4) 800

/-- Fresh bytes execute one mathematical Keccak round on all 100 interleaved words.
This theorem stops at PC1645, before the three counter-maintenance instructions;
it is a round-body lemma, not the complete 24-round function theorem. -/
theorem keccak4x_current_round (s : X86State) (h : keccak4xRoundEntry s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccak4xName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 269 s).1.pc = 1645 ∧ (runX86 prog 269 s).1.halted = false ∧
      (runX86 prog 269 s).1.gpr = s.gpr ∧
      (runX86 prog 269 s).1.mem =
        keccak4xRoundMem s.mem (s.gpr.get 7) (s.gpr.get 4) (s.gpr.get 6) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource (runX86 prog 269 s).1.mem (s.gpr.get 7)) q =
          roundS (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)
            (readMem64 s.mem (s.gpr.get 6))) := by
  have hd := keccak4x_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices keccak4xName with
  | none => rw [hf] at hd; cases hd
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccak4xProg, rfl, hd, ?_⟩
    rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
    rcases h with ⟨hp, hh, hds, hcs⟩
    dsimp only at hp hh
    subst pc hlt
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_round_steps g y cf ofl zf dy mem hds hcs
    have he := (ht.toExecReaches.run 0).1
    change (runX86 keccak4xProg 269 _).1 = t at he
    rw [he]
    refine ⟨hp, hh, hg, hm, ?_⟩
    intro q hq
    rw [hm]
    exact keccak4xRoundMem_readback mem (g.get 7) (g.get 4) (g.get 6) q hq

theorem keccak4x_round_inhabited : ∃ s : X86State, keccak4xRoundEntry s := by
  refine ⟨⟨20, Bank16.ofFn (fun i => if i == 4 then 1024 else if i == 6 then 2048 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, ?_, ?_⟩
  · change keccak4xDisjoint 0 800 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 2048 8 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega

theorem keccak4x_round_tooth : roundS zeroKState 1 ≠ zeroKState := by
  rw [zeroKState_eq]; kstate_ne

#tooth_pair keccak4x_current_round vs keccak4x_round_tooth
#verify_inhabited keccak4x_current_round keccak4x_round_inhabited

theorem keccak4xScratchPrefix_outside (mem : UInt64 → UInt8) (sp : UInt64)
    (v : Nat → Vec256) (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ j : Nat, j < 800 → a ≠ sp + UInt64.ofNat j) :
    keccak4xScratchPrefix mem sp v n a = mem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix, writeMem256_outside]
    · exact ih (by omega)
    · intro k hk he
      have hp := keccak4x_perm_lt n (by omega)
      rw [u64_add_ofNat_assoc sp (32*keccak4xPerm n) k (by omega)] at he
      exact ha (32*keccak4xPerm n+k) (by omega) he

theorem keccak4xStatePrefix_outside (mem : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ j : Nat, j < 800 → a ≠ p + UInt64.ofNat j) :
    keccak4xStatePrefix mem p v rc n a = mem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xStatePrefix, writeMem256_outside]
    · exact ih (by omega)
    · intro k hk he
      rw [u64_add_ofNat_assoc p (32*n) k (by omega)] at he
      exact ha (32*n+k) (by omega) he

theorem keccak4xRoundMem_outside (mem : UInt64 → UInt8) (p sp rp a : UInt64)
    (hp : ∀ j : Nat, j < 800 → a ≠ p + UInt64.ofNat j)
    (hs : ∀ j : Nat, j < 800 → a ≠ sp + UInt64.ofNat j) :
    keccak4xRoundMem mem p sp rp a = mem a := by
  unfold keccak4xRoundMem
  rw [keccak4xStatePrefix_outside _ _ _ _ 25 (by decide) a hp,
    keccak4xScratchPrefix_outside _ _ _ 25 (by decide) a hs]

/-- Exact architectural DEC32 result, ZF and OF for the bounded public counters
used by the 24-round loop and the 25-vector scratch wipe. -/
theorem keccak4x_dec32_small (k : Nat) (hk : k < 25) :
    maskGprWidth false (maskGprWidth false (UInt64.ofNat (k + 1)) + (0 - 1)) = UInt64.ofNat k ∧
    (UInt64.ofNat k == 0) = decide (k = 0) ∧
    evalX86IncDecOf false false (UInt64.ofNat (k + 1)) = false := by
  have h : ∀ k : Fin 25,
      maskGprWidth false (maskGprWidth false (UInt64.ofNat (k.val + 1)) + (0 - 1)) = UInt64.ofNat k.val ∧
      (UInt64.ofNat k.val == 0) = decide (k.val = 0) ∧
      evalX86IncDecOf false false (UInt64.ofNat (k.val + 1)) = false := by
    decide +kernel
  exact h ⟨k, hk⟩

theorem keccak4x_control_steps (s : X86State) (k : Nat) (hk : k < 25)
    (hp : s.pc = 1645) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k + 1)) :
    ∃ t, StepsX86 keccak4xProg 3 s t ∧
      t.pc = (if k = 0 then 1657 else 20) ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 6 (s.gpr.get 6 + 8)).set 1 (UInt64.ofNat k) ∧
      t.mem = s.mem ∧ t.ymm = s.ymm := by
  rcases s with ⟨pc, g, y, cf, ofl, zf, dy, halted, mem⟩
  dsimp only at hp hh hc
  subst pc halted
  obtain ⟨hdec, hzf, hof⟩ := keccak4x_dec32_small k hk
  suffices he : ∃ t, StepsX86 keccak4xProg 3
      ⟨1645,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = (if k = 0 then 1657 else 20) ∧ t.halted = false ∧
      t.gpr = (g.set 6 (g.get 6 + 8)).set 1 (UInt64.ofNat k) ∧
      t.mem = mem ∧ t.ymm = y by exact he
  apply StepsX86_step_ex rfl rfl
  · simp only [stepX86, ite_true, ite_false, evalX86Alu, maskGprWidth_true,
      uint64_evalAdd_eq]
    rfl
  apply StepsX86_step_ex rfl rfl
  · simp only [stepX86_dec, Bank16.get, Bank16.set] at hc ⊢
    simp only [hc, hdec, hzf, hof]
    rfl
  apply StepsX86_step_ex rfl rfl
  · rw [stepX86_jnz]
  refine ⟨_, StepsX86.zero _, ?_, rfl, rfl, rfl, rfl⟩
  cases k with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, decide_false, Bool.not_false, jccPc, ite_true, ite_false]
    rfl

/-- The public register invariant. The counter and RC pointer are explicit;
all other registers retain their values from the loop's entry bank. -/
def keccak4xLoopBank (g : Bank16 UInt64) (table : UInt64) (i k : Nat) : Bank16 UInt64 :=
  ⟨g.r0, UInt64.ofNat k, g.r2, g.r3, g.r4, g.r5,
    table + UInt64.ofNat (8*i), g.r7, g.r8, g.r9, g.r10, g.r11, g.r12, g.r13, g.r14, g.r15⟩

theorem keccak4xLoopBank_get1 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 1 = UInt64.ofNat k := by rfl

theorem keccak4xLoopBank_get4 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 4 = g.get 4 := by rfl

theorem keccak4xLoopBank_get6 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 6 = table + UInt64.ofNat (8*i) := by rfl

theorem keccak4xLoopBank_get7 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 7 = g.get 7 := by rfl

def keccak4xCanonicalTable (mem : UInt64 → UInt8) (table : UInt64) : Prop :=
  ∀ j : Nat, j < 24 → readMem64 mem (table + UInt64.ofNat (8*j)) = keccakRoundConstants.getD j 0

/-- Each finite canonical suffix exposes precisely the next round constant. -/
theorem keccak4x_constants_drop (i : Nat) (hi : i < 24) :
    keccakRoundConstants.drop i =
      keccakRoundConstants.getD i 0 :: keccakRoundConstants.drop (i+1) := by
  have h : ∀ i : Fin 24, keccakRoundConstants.drop i.val =
      keccakRoundConstants.getD i.val 0 :: keccakRoundConstants.drop (i.val+1) := by
    rw [keccakRoundConstants_eq]; decide +kernel
  exact h ⟨i, hi⟩

theorem keccak4x_constants_drop24 : keccakRoundConstants.drop 24 = [] := by
  rw [keccakRoundConstants_eq]; decide +kernel

theorem keccak4xLoopBank_advance (g : Bank16 UInt64) (table : UInt64)
    (i k : Nat) (hi : i < 24) :
    ((keccak4xLoopBank g table i (k+1)).set 6
      ((keccak4xLoopBank g table i (k+1)).get 6 + 8)).set 1 (UInt64.ofNat k) =
      keccak4xLoopBank g table (i+1) k := by
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have hp : (table + UInt64.ofNat (8*i)) + 8 = table + UInt64.ofNat (8*(i+1)) := by
    rw [← h8, u64_add_ofNat_assoc table (8*i) 8 (by omega)]
    congr 1
  simp only [keccak4xLoopBank, Bank16.get, Bank16.set, hp]

/-- The entire public RC table survives a round, not merely the word just read. -/
theorem keccak4xCanonicalTable_after_round (mem : UInt64 → UInt8)
    (p sp table current : UInt64)
    (hp : keccak4xDisjoint table 192 p 800)
    (hs : keccak4xDisjoint table 192 sp 800)
    (ht : keccak4xCanonicalTable mem table) :
    keccak4xCanonicalTable (keccak4xRoundMem mem p sp current) table := by
  intro j hj
  have hb (off : Nat) (hoff : off < 192) :
      keccak4xRoundMem mem p sp current (table + UInt64.ofNat off) =
        mem (table + UInt64.ofNat off) := by
    exact keccak4xRoundMem_outside mem p sp current _
      (fun n hn => hp off n hoff hn) (fun n hn => hs off n hoff hn)
  have hbyte (k : Nat) (hk : k < 8) :
      keccak4xRoundMem mem p sp current ((table + UInt64.ofNat (8*j)) + UInt64.ofNat k) =
        mem ((table + UInt64.ofNat (8*j)) + UInt64.ofNat k) := by
    rw [u64_add_ofNat_assoc table (8*j) k (by omega)]
    exact hb (8*j+k) (by omega)
  have hword : readMem64 (keccak4xRoundMem mem p sp current) (table + UInt64.ofNat (8*j)) =
      readMem64 mem (table + UInt64.ofNat (8*j)) := by
    rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
    unfold mapBytes64
    simp only [hbyte 0 (by decide), hbyte 1 (by decide), hbyte 2 (by decide), hbyte 3 (by decide),
      hbyte 4 (by decide), hbyte 5 (by decide), hbyte 6 (by decide), hbyte 7 (by decide)]
  exact hword.trans (ht j hj)

/-- Bounded remaining-round induction. A zero remaining count starts at the
post-branch exit PC1657; it never pretends that a zero counter at PC20 executes
zero rounds. Every positive stage executes the decoded 269-instruction round
and all three public counter instructions. -/
theorem keccak4x_loop_steps (k : Nat) :
    ∀ (g : Bank16 UInt64) (table : UInt64) (i : Nat) (s : X86State),
    i + k = 24 → s.pc = (if k = 0 then 1657 else 20) → s.halted = false →
    s.gpr = keccak4xLoopBank g table i k →
    keccak4xDisjoint (g.get 7) 800 (g.get 4) 800 →
    keccak4xDisjoint table 192 (g.get 7) 800 →
    keccak4xDisjoint table 192 (g.get 4) 800 →
    keccak4xCanonicalTable s.mem table →
    ∃ t, StepsX86 keccak4xProg (272*k) s t ∧
      t.pc = 1657 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table 24 0 ∧
      (∀ a : UInt64,
        (∀ j : Nat, j < 800 → a ≠ g.get 7 + UInt64.ofNat j) →
        (∀ j : Nat, j < 800 → a ≠ g.get 4 + UInt64.ofNat j) → t.mem a = s.mem a) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (g.get 7)) q =
          (keccakRoundConstants.drop i).foldl roundS
            (keccak4xLaneState (keccak4xSource s.mem (g.get 7)) q)) := by
  induction k with
  | zero =>
    intro g table i s hi hp hh hg hd htp hts ht
    have hi24 : i = 24 := by omega
    subst i
    refine ⟨s, StepsX86.zero _, ?_, hh, hg, ?_, ?_⟩
    · simpa only [ite_true] using hp
    · intro a _ _; rfl
    · intro q _
      rw [keccak4x_constants_drop24]
      rfl
  | succ k ih =>
    intro g table i s hcount hp hh hg hd htp hts ht
    have hik : i < 24 := by omega
    have hk : k < 25 := by omega
    have hpc : s.pc = 20 := by simpa only [Nat.succ_ne_zero, ite_false] using hp
    have hrc : keccak4xDisjoint (table + UInt64.ofNat (8*i)) 8 (g.get 4) 800 := by
      intro a b ha hb he
      rw [u64_add_ofNat_assoc table (8*i) a (by omega)] at he
      exact hts (8*i+a) b (by omega) hb he
    have hr : ∃ t, StepsX86 keccak4xProg 269 s t ∧
        t.pc = 1645 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table i (k+1) ∧
        t.mem = keccak4xRoundMem s.mem (g.get 7) (g.get 4) (table + UInt64.ofNat (8*i)) := by
      rcases s with ⟨pc, gs, ys, cf, ofl, zf, dy, halted, mem⟩
      dsimp only at hpc hh hg
      subst pc halted gs
      simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get6, keccak4xLoopBank_get7] using
        keccak4x_round_steps (keccak4xLoopBank g table i (k+1)) ys cf ofl zf dy mem
          (by simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get7] using hd)
          (by simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get6] using hrc)
    obtain ⟨r, hr, hrp, hrh, hrg, hrm⟩ := hr
    obtain ⟨u, hcontrol, hup, huh, hug, hum, _⟩ :=
      keccak4x_control_steps r k hk hrp hrh (by rw [hrg, keccak4xLoopBank_get1])
    have hug' : u.gpr = keccak4xLoopBank g table (i+1) k := by
      rw [hug, hrg, keccak4xLoopBank_advance g table i k hik]
    have hum' : u.mem = keccak4xRoundMem s.mem (g.get 7) (g.get 4)
        (table + UInt64.ofNat (8*i)) := hum.trans hrm
    have hut : keccak4xCanonicalTable u.mem table := by
      rw [hum']
      exact keccak4xCanonicalTable_after_round _ _ _ _ _ htp hts ht
    obtain ⟨t, hloop, htp', hth, htg, hout, hmath⟩ :=
      ih g table (i+1) u (by omega) hup huh hug' hd htp hts hut
    have hsteps := StepsX86_trans (StepsX86_trans hr hcontrol) hloop
    have hlen : 269 + 3 + 272*k = 272*(k+1) := by omega
    rw [hlen] at hsteps
    refine ⟨t, hsteps, htp', hth, htg, ?_, ?_⟩
    · intro a hap has
      rw [hout a hap has, hum']
      exact keccak4xRoundMem_outside _ _ _ _ a hap has
    · intro q hq
      rw [hmath q hq, hum', keccak4xRoundMem_readback _ _ _ _ q hq, ht i hik,
        keccak4x_constants_drop i hik]
      rfl

/-- Exactly the 24 rounds allowed by the kernel ABI: 6,528 decoded instructions
between the prologue and epilogue, computing the full permutation on all four states. -/
theorem keccak4x_loop24_steps (g : Bank16 UInt64) (table : UInt64) (s : X86State)
    (hp : s.pc = 20) (hh : s.halted = false)
    (hg : s.gpr = keccak4xLoopBank g table 0 24)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (htp : keccak4xDisjoint table 192 (g.get 7) 800)
    (hts : keccak4xDisjoint table 192 (g.get 4) 800)
    (ht : keccak4xCanonicalTable s.mem table) :
    ∃ t, StepsX86 keccak4xProg 6528 s t ∧
      t.pc = 1657 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table 24 0 ∧
      (∀ a : UInt64,
        (∀ j : Nat, j < 800 → a ≠ g.get 7 + UInt64.ofNat j) →
        (∀ j : Nat, j < 800 → a ≠ g.get 4 + UInt64.ofNat j) → t.mem a = s.mem a) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (g.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (g.get 7)) q)) := by
  simpa only [List.drop_zero, keccakF1600] using
    keccak4x_loop_steps 24 g table 0 s (by decide) hp hh hg hd htp hts ht

/-- The actual aligned 832-byte frame selected by the five-instruction prologue. -/
def keccak4xStackBase (g : Bank16 UInt64) : UInt64 :=
  ((g.get 4 - 8) &&& 0xffffffffffffffe0) - 832

def keccak4xSavedBp (g : Bank16 UInt64) : UInt64 := g.get 4 - 8

def keccak4xPrologueGpr (g : Bank16 UInt64) : Bank16 UInt64 :=
  ((g.set 4 (keccak4xStackBase g)).set 5 (keccak4xSavedBp g)).set 1 24

def keccak4xPrologueMem (mem : UInt64 → UInt8) (g : Bank16 UInt64) : UInt64 → UInt8 :=
  writeMem64 mem (keccak4xSavedBp g) (g.get 5)

set_option linter.unusedSimpArgs false in
/-- Entry prologue, including the saved caller frame pointer. -/
theorem keccak4x_prologue_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8) :
    ∃ t, StepsX86 keccak4xProg 5 ⟨0,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 20 ∧ t.halted = false ∧ t.gpr = keccak4xPrologueGpr g ∧ t.ymm = y ∧
      t.mem = keccak4xPrologueMem mem g := by
  have h24 : maskGprWidth false 24 = 24 := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalX86Alu, maskGprWidth_true, h24, uint64_evalSub_eq, ite_true, ite_false,
          Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, rfl⟩

private theorem keccak4x_read256_write64_disjoint (mem : UInt64 → UInt8)
    (a b w : UInt64)
    (hd : ∀ i j : Nat, i < 32 → j < 8 → a + UInt64.ofNat i ≠ b + UInt64.ofNat j) :
    readMem256 (writeMem64 mem b w) a = readMem256 mem a := by
  have h (off : Nat) (ho : off ≤ 24) :
      readMem64 (writeMem64 mem b w) (a + UInt64.ofNat off) = readMem64 mem (a + UInt64.ofNat off) := by
    apply readMem64_writeMem64_disjoint
    intro i j hi hj he
    rw [u64_add_ofNat_assoc a off i (by omega)] at he
    exact hd (off+i) j (by omega) hj he
  have h0 := h 0 (by decide)
  have e0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have e8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have e16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have e24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [e0, UInt64.add_zero] at h0
  unfold readMem256
  rw [← e8, ← e16, ← e24, h0, h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem keccak4xPrologueMem_source (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (keccak4xSavedBp g) 8)
    (j : Nat) (hj : j < 25) :
    keccak4xSource (keccak4xPrologueMem mem g) (g.get 7) j = keccak4xSource mem (g.get 7) j := by
  rw [keccak4xSource_eq _ _ j hj, keccak4xSource_eq _ _ j hj]
  unfold keccak4xPrologueMem
  apply keccak4x_read256_write64_disjoint
  intro i k hi hk he
  rw [u64_add_ofNat_assoc (g.get 7) (32*j) i (by omega)] at he
  exact hd (32*j+i) k (by omega) hk he

theorem keccak4xPrologueMem_table (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 6) 192 (keccak4xSavedBp g) 8)
    (j : Nat) (hj : j < 24) :
    readMem64 (keccak4xPrologueMem mem g) (g.get 6 + UInt64.ofNat (8*j)) =
      readMem64 mem (g.get 6 + UInt64.ofNat (8*j)) := by
  unfold keccak4xPrologueMem
  apply readMem64_writeMem64_disjoint
  intro i k hi hk he
  rw [u64_add_ofNat_assoc (g.get 6) (8*j) i (by omega)] at he
  exact hd (8*j+i) k (by omega) hk he


/-- Ascending stores performed by the scratch-wipe loop. -/
def keccak4xWipePrefix (m : UInt64 → UInt8) (sp : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xWipePrefix m sp n)
      (sp + UInt64.ofNat (32*n)) Vec256.zero

theorem keccak4xWipePrefix_outside (m : UInt64 → UInt8) (sp : UInt64)
    (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ i : Nat, i < 32*n → a ≠ sp + UInt64.ofNat i) :
    keccak4xWipePrefix m sp n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, writeMem256_outside]
    · exact ih (by omega) (fun i hi => ha i (by omega))
    · intro i hi he
      rw [u64_add_ofNat_assoc sp (32*n) i (by omega)] at he
      exact ha (32*n+i) (by omega) he

theorem keccak4xWipePrefix_saved (m : UInt64 → UInt8) (sp bp : UInt64)
    (hd : keccak4xDisjoint bp 8 sp 800) (n : Nat) (hn : n ≤ 25) :
    readMem64 (keccak4xWipePrefix m sp n) bp = readMem64 m bp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, keccakChiMpc_readMem64_writeMem256_disjoint]
    · exact ih (by omega)
    · intro i j hi hj he
      rw [u64_add_ofNat_assoc sp (32*n) j (by omega)] at he
      exact hd i (32*n+j) hi (by omega) he

theorem keccak4xWipePrefix_source (m : UInt64 → UInt8) (sp p : UInt64)
    (hd : keccak4xDisjoint p 800 sp 800) (n : Nat) (hn : n ≤ 25)
    (j : Nat) (hj : j < 25) :
    keccak4xSource (keccak4xWipePrefix m sp n) p j = keccak4xSource m p j := by
  rw [keccak4xSource_eq _ _ j hj, keccak4xSource_eq _ _ j hj]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro i k hi hk he
      rw [u64_add_ofNat_assoc p (32*j) i (by omega),
        u64_add_ofNat_assoc sp (32*n) k (by omega)] at he
      exact hd (32*j+i) (32*n+k) (by omega) (by omega) he

set_option linter.unusedSimpArgs false in
theorem keccak4x_epilogue_init (s : X86State) (hp : s.pc = 1657) (hh : s.halted = false) :
    ∃ t, StepsX86 keccak4xProg 3 s t ∧ t.pc = 1669 ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 1 25).set 0 (s.gpr.get 4) ∧
      t.ymm = s.ymm.set 0 Vec256.zero ∧ t.mem = s.mem := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  have h25 : maskGprWidth false 25 = 25 := by decide +kernel
  iterate 3
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalVecBin256, clampVecWidth, ite_true, ite_false,
          u64_xor_self, h25, maskGprWidth_true, Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem keccak4x_wipe_body (s : X86State) (k : Nat) (hk : k < 25)
    (hp : s.pc = 1669) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k+1)) (hy : s.ymm.get 0 = Vec256.zero) :
    ∃ t, StepsX86 keccak4xProg 4 s t ∧
      t.pc = (if k = 0 then 1681 else 1669) ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 0 (s.gpr.get 0 + 32)).set 1 (UInt64.ofNat k) ∧
      t.ymm = s.ymm ∧ t.mem = writeMem256 s.mem (s.gpr.get 0) Vec256.zero := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  change r1 = UInt64.ofNat (k+1) at hc
  change y.r0 = Vec256.zero at hy
  subst pc hlt r1
  obtain ⟨hdec,hzf,hof⟩ := keccak4x_dec32_small k hk
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86, evalX86Addr, ite_true, Bank16.get, UInt64.add_zero, hy]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_addImm64, Bank16.get, Bank16.set]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_dec, Bank16.get, Bank16.set, hdec, hzf, hof]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      rw [stepX86_jnz]
    all_goals rfl
  refine ⟨_, StepsX86.zero _, ?_, rfl, rfl, rfl, rfl⟩
  cases k with
  | zero => simp [jccPc]
  | succ k => simp [jccPc]

/-- The scalar ABI result after restoring the caller's stack frame. -/
def keccak4xRestoredGpr (g : Bank16 UInt64) (m : UInt64 → UInt8) : Bank16 UInt64 :=
  ⟨0,0,0,g.get 3,g.get 5 + 16,readMem64 m (g.get 5),0,0,0,0,0,0,
    g.get 12,g.get 13,g.get 14,g.get 15⟩

set_option linter.unusedSimpArgs false in
theorem keccak4x_epilogue_cleanup (s : X86State) (hp : s.pc = 1681) (hh : s.halted = false) :
    ∃ t, StepsX86 keccak4xProg 25 s t ∧ t.pc = (readMem64 t.mem (s.gpr.get 5 + 8)).toNat ∧ t.halted = true ∧
      t.gpr = keccak4xRestoredGpr s.gpr s.mem ∧ t.ymm = Bank16.const Vec256.zero ∧
      t.ymmDirty = false ∧ t.mem = s.mem := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 11
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalVecBin256, clampVecWidth, ite_true, ite_false,
          u64_xor_self, Bank16.get, Bank16.set]
      all_goals rfl
  iterate 2
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [current_vzeroall_step, current_vzeroupper_zero_step]
      all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_movRR, maskGprWidth_true, Bank16.get, Bank16.set]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86, Bank16.get, Bank16.set]
    all_goals rfl
  iterate 9
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero, Bank16.get, Bank16.set]
      all_goals rfl
  apply StepsX86_step_ex rfl rfl rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, ?_, rfl, rfl, rfl⟩
  have h16 : r5 + 8 + 8 = r5 + 16 := by rw [UInt64.add_assoc]; rfl
  simp only [stepX86_ret, b16get_4, b16set_4, keccak4xRestoredGpr, Bank16.get, h16]

/-- Loop invariant after `i` of the fixed 25 scratch-vector stores. -/
def keccak4xWipeInv (s t : X86State) (i : Nat) : Prop :=
  t.pc = (if i < 25 then 1669 else 1681) ∧ t.halted = false ∧
  t.gpr = (s.gpr.set 0 (s.gpr.get 0 + UInt64.ofNat (32*i))).set 1 (UInt64.ofNat (25-i)) ∧
  t.ymm = s.ymm ∧ t.mem = keccak4xWipePrefix s.mem (s.gpr.get 0) i

theorem keccak4x_wipe_advance (s t : X86State) (i : Nat) (hi : i < 25)
    (hy : s.ymm.get 0 = Vec256.zero) (h : keccak4xWipeInv s t i) :
    ∃ u, StepsX86 keccak4xProg 4 t u ∧ keccak4xWipeInv s u (i+1) := by
  have hp : t.pc = 1669 := h.1.trans (ite_eq_left hi)
  have hc : t.gpr.get 1 = UInt64.ofNat ((24-i)+1) := by
    rw [h.2.2.1]
    change UInt64.ofNat (25-i) = UInt64.ofNat ((24-i)+1)
    congr 1
    omega
  have hy' : t.ymm.get 0 = Vec256.zero := by rw [h.2.2.2.1]; exact hy
  obtain ⟨u, hu, hup, huh, hug, huy, hum⟩ :=
    keccak4x_wipe_body t (24-i) (by omega) hp h.2.1 hc hy'
  refine ⟨u, hu, ?_, huh, ?_, huy.trans h.2.2.2.1, ?_⟩
  · rw [hup]
    by_cases he : i+1 < 25
    · rw [ite_eq_right (by omega), ite_eq_left he]
    · rw [ite_eq_left (by omega), ite_eq_right he]
  · rw [hug, h.2.2.1]
    have e32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
    have ha : (s.gpr.get 0 + UInt64.ofNat (32*i)) + 32 =
        s.gpr.get 0 + UInt64.ofNat (32*(i+1)) := by
      rw [← e32, u64_add_ofNat_assoc _ (32*i) 32 (by omega),
        show 32*i+32 = 32*(i+1) from by omega]
    change (s.gpr.set 0 ((s.gpr.get 0 + UInt64.ofNat (32*i)) + 32)).set 1
        (UInt64.ofNat (24-i)) = _
    rw [ha, show 24-i = 25-(i+1) from by omega]
  · rw [hum, h.2.2.2.2, h.2.2.1]
    rfl

theorem keccak4x_wipe_prefix_steps (s : X86State) (hp : s.pc = 1669)
    (hh : s.halted = false) (hc : s.gpr.get 1 = 25) (hy : s.ymm.get 0 = Vec256.zero)
    (i : Nat) (hi : i ≤ 25) :
    ∃ t, StepsX86 keccak4xProg (4*i) s t ∧ keccak4xWipeInv s t i := by
  induction i with
  | zero =>
    refine ⟨s, StepsX86.zero _, ?_, hh, ?_, rfl, rfl⟩
    · simpa using hp
    · have e0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
      have e25 : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
      have hs0 (g : Bank16 UInt64) : g.set 0 (g.get 0) = g := by cases g; rfl
      have hs1 (g : Bank16 UInt64) : g.set 1 (g.get 1) = g := by cases g; rfl
      change s.gpr = (s.gpr.set 0 (s.gpr.get 0 + UInt64.ofNat 0)).set 1 (UInt64.ofNat 25)
      rw [e0, e25, UInt64.add_zero, hs0, ← hc, hs1]
  | succ i ih =>
    obtain ⟨t, ht, hit⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4x_wipe_advance s t i (by omega) hy hit
    refine ⟨u, ?_, hiu⟩
    simpa only [Nat.mul_add, Nat.mul_one] using StepsX86_trans ht hu

/-- The complete epilogue executes the 25-iteration wipe, restores the saved frame,
and executes all vector/scalar cleanup instructions and RET. -/
theorem keccak4x_epilogue_steps (s : X86State) (hp : s.pc = 1657) (hh : s.halted = false)
    (hd : keccak4xDisjoint (s.gpr.get 5) 8 (s.gpr.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 128 s t ∧ t.pc = (readMem64 t.mem (s.gpr.get 5 + 8)).toNat ∧ t.halted = true ∧
      t.gpr = keccak4xRestoredGpr s.gpr s.mem ∧ t.ymm = Bank16.const Vec256.zero ∧
      t.ymmDirty = false ∧ t.mem = keccak4xWipePrefix s.mem (s.gpr.get 4) 25 := by
  obtain ⟨a, ha, hap, hah, hag, hay, ham⟩ := keccak4x_epilogue_init s hp hh
  have hac : a.gpr.get 1 = 25 := by rw [hag]; rfl
  have hay0 : a.ymm.get 0 = Vec256.zero := by rw [hay]; exact Bank16.get_set_eq _ _ _
  obtain ⟨b, hb, hib⟩ := keccak4x_wipe_prefix_steps a hap hah hac hay0 25 (by decide)
  have hbp : b.pc = 1681 := hib.1
  obtain ⟨t, ht, htp, hth, htg, hty, htd, htm⟩ := keccak4x_epilogue_cleanup b hbp hib.2.1
  have hb5 : b.gpr.get 5 = s.gpr.get 5 := by rw [hib.2.2.1, hag]; rfl
  rw [hb5] at htp
  refine ⟨t, StepsX86_trans (StepsX86_trans ha hb) ht, htp, hth, ?_, hty, htd, ?_⟩
  · rw [htg, hib.2.2.1, hib.2.2.2.2, hag, ham]
    change keccak4xRestoredGpr s.gpr (keccak4xWipePrefix s.mem (s.gpr.get 4) 25) = _
    unfold keccak4xRestoredGpr
    rw [keccak4xWipePrefix_saved _ _ _ hd 25 (by decide)]
  · rw [htm, hib.2.2.2.2, ham, hag]
    rfl

/-- Every byte in the wiped prefix is zero; addresses may wrap modulo 2^64. -/
theorem keccak4xWipePrefix_zero (m : UInt64 → UInt8) (sp : UInt64)
    (n : Nat) (hn : n ≤ 25) (i : Nat) (hi : i < 32*n) :
    keccak4xWipePrefix m sp n (sp + UInt64.ofNat i) = 0 := by
  induction n with
  | zero => exact False.elim (by omega)
  | succ n ih =>
    rw [keccak4xWipePrefix]
    by_cases hlow : i < 32*n
    · rw [writeMem256_outside]
      · exact ih (by omega) hlow
      · intro k hk he
        rw [u64_add_ofNat_assoc sp (32*n) k (by omega)] at he
        have he' := u64_add_ofNat_inj (by omega) (by omega) he
        omega
    · have hrange : i-32*n < 32 := by omega
      have haddr : sp + UInt64.ofNat i =
          (sp + UInt64.ofNat (32*n)) + UInt64.ofNat (i-32*n) := by
        rw [u64_add_ofNat_assoc sp (32*n) (i-32*n) (by omega),
          show 32*n+(i-32*n) = i from by omega]
      rw [haddr, writeMem256_at _ _ _ _ hrange]
      simp [Vec256.zero, getByte64]

theorem keccak4xWipePrefix_states (m : UInt64 → UInt8) (sp p : UInt64)
    (hd : keccak4xDisjoint p 800 sp 800) (q : Nat) :
    keccak4xLaneState (keccak4xSource (keccak4xWipePrefix m sp 25) p) q =
      keccak4xLaneState (keccak4xSource m p) q := by
  apply keccak4xLaneState_congr
  exact fun j hj => keccak4xWipePrefix_source m sp p hd 25 (by decide) j hj

/-- ABI entry conditions: the state, public constants, aligned scratch frame,
and saved frame pointer occupy disjoint byte ranges. -/
structure keccak4xFullEntry (s : X86State) : Prop where
  pc : s.pc = 0
  live : s.halted = false
  stateScratch : keccak4xDisjoint (s.gpr.get 7) 800 (keccak4xStackBase s.gpr) 800
  tableState : keccak4xDisjoint (s.gpr.get 6) 192 (s.gpr.get 7) 800
  tableScratch : keccak4xDisjoint (s.gpr.get 6) 192 (keccak4xStackBase s.gpr) 800
  stateSaved : keccak4xDisjoint (s.gpr.get 7) 800 (keccak4xSavedBp s.gpr) 8
  tableSaved : keccak4xDisjoint (s.gpr.get 6) 192 (keccak4xSavedBp s.gpr) 8
  savedScratch : keccak4xDisjoint (keccak4xSavedBp s.gpr) 8 (keccak4xStackBase s.gpr) 800
  constants : keccak4xCanonicalTable s.mem (s.gpr.get 6)

theorem keccak4x_full_steps (s : X86State) (h : keccak4xFullEntry s) :
    ∃ t, StepsX86 keccak4xProg 6661 s t ∧ t.pc = (readMem64 t.mem (s.gpr.get 4)).toNat ∧ t.halted = true ∧
      t.ymm = Bank16.const Vec256.zero ∧ t.ymmDirty = false ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (s.gpr.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,halted,mem⟩
  have hp := h.pc
  have hh := h.live
  dsimp only at hp hh
  subst pc halted
  obtain ⟨a, ha, hap, hah, hag, hay, ham⟩ := keccak4x_prologue_steps g y cf ofl zf dy mem
  have he : keccak4xPrologueGpr g =
      keccak4xLoopBank (keccak4xPrologueGpr g) (g.get 6) 0 24 := by
    cases g
    simp [keccak4xPrologueGpr, keccak4xLoopBank, Bank16.get, Bank16.set]
  have hat : keccak4xCanonicalTable a.mem (g.get 6) := by
    intro j hj
    rw [ham, keccak4xPrologueMem_table mem g h.tableSaved j hj]
    exact h.constants j hj
  obtain ⟨b, hb, hbp, hbh, hbg, hbm, hbf⟩ :=
    keccak4x_loop24_steps (keccak4xPrologueGpr g) (g.get 6) a hap hah
      (hag.trans he) h.stateScratch h.tableState h.tableScratch hat
  have hbd : keccak4xDisjoint (b.gpr.get 5) 8 (b.gpr.get 4) 800 := by
    rw [hbg]
    exact h.savedScratch
  obtain ⟨t, ht, htp, hth, htg, hty, htd, htm⟩ := keccak4x_epilogue_steps b hbp hbh hbd
  have hb5 : b.gpr.get 5 + 8 = g.get 4 := by
    rw [hbg]
    change g.get 4 - 8 + 8 = g.get 4
    rw [UInt64.sub_add_cancel]
  rw [hb5] at htp
  refine ⟨t, StepsX86_trans (StepsX86_trans ha hb) ht, htp, hth, hty, htd, ?_⟩
  intro q hq
  rw [htm, hbg]
  change keccak4xLaneState (keccak4xSource
    (keccak4xWipePrefix b.mem (keccak4xStackBase g) 25) (g.get 7)) q = _
  rw [keccak4xWipePrefix_states _ _ _ h.stateScratch q]
  have hf := hbf q hq
  change keccak4xLaneState (keccak4xSource b.mem (g.get 7)) q =
    keccakF1600 (keccak4xLaneState (keccak4xSource a.mem (g.get 7)) q) at hf
  rw [hf, ham]
  congr 1
  apply keccak4xLaneState_congr
  exact fun j hj => keccak4xPrologueMem_source mem g h.stateSaved j hj

/-- The fresh 309-instruction symbol executes all 24 rounds on each of its four
interleaved 25-lane states, then wipes its vector scratch and returns. -/
theorem current_rlib_keccak_f1600_avx2_4x_functional (s : X86State)
    (h : keccak4xFullEntry s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccak4xName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 6661 s).1.pc = (readMem64 (runX86 prog 6661 s).1.mem (s.gpr.get 4)).toNat ∧
      (runX86 prog 6661 s).1.halted = true ∧
      (runX86 prog 6661 s).1.ymm = Bank16.const Vec256.zero ∧
      (runX86 prog 6661 s).1.ymmDirty = false ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource (runX86 prog 6661 s).1.mem (s.gpr.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)) := by
  have hd := keccak4x_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices keccak4xName with
  | none => rw [hf] at hd; cases hd
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccak4xProg, rfl, hd, ?_⟩
    obtain ⟨t, ht, hp, hh, hy, hdy, hout⟩ := keccak4x_full_steps s h
    have he := (ht.toExecReaches.run 0).1
    change (runX86 keccak4xProg 6661 s).1 = t at he
    rw [he]
    exact ⟨hp, hh, hy, hdy, hout⟩

/-- A concrete public constant table, independent of all state bytes. -/
def keccak4xWitnessMem (a : UInt64) : UInt8 :=
  if a.toNat < 192 then
    getByte64 (keccakRoundConstants.getD (a.toNat / 8) 0) (a.toNat % 8)
  else 0

theorem keccak4xWitnessMem_table : keccak4xCanonicalTable keccak4xWitnessMem 0 := by
  have hf : ∀ j : Fin 24,
      readMem64 keccak4xWitnessMem (0 + UInt64.ofNat (8*j.val)) =
        keccakRoundConstants.getD j.val 0 := by
    delta keccak4xWitnessMem
    simp only [keccakRoundConstants_eq]
    decide +kernel
  exact fun j hj => hf ⟨j,hj⟩

theorem keccak4x_full_inhabited : ∃ s : X86State, keccak4xFullEntry s := by
  refine ⟨⟨0, Bank16.ofFn (fun i => if i == 4 then 4096 else if i == 7 then 1024 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, keccak4xWitnessMem⟩,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change keccak4xDisjoint 1024 800 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 1024 800 4088 8
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 4088 8
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 4088 8 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · exact keccak4xWitnessMem_table

theorem keccak4x_full_tooth : keccakF1600 zeroKState ≠ zeroKState := by
  rw [keccakF1600_eq, keccakRoundConstants_eq, zeroKState_eq]; kstate_ne

#tooth_pair current_rlib_keccak_f1600_avx2_4x_functional vs keccak4x_full_tooth
#verify_inhabited current_rlib_keccak_f1600_avx2_4x_functional keccak4x_full_inhabited

end Keccak4xFreshVerification

end Qsag
end
