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

