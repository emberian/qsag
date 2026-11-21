module
/-
# Qsag.Poseidon2 — Algebraic Width-12 Goldilocks `Poseidon2` Permutation & 256-Bit Sponge

Self-contained Lean 4.35 algebraic sponge specification (`Init` + `Qsag.Goldilocks` + `Qsag.Keccak`):
1. Degree-7 S-box bijection (`sbox7_bijective`) via $d_{\text{inv}} = \frac{4(p - 1) + 1}{7}$
   and Fermat's Little Theorem (`IsPrimeNat.pow_sub_one_mod`).
2. Full Width-12 (`rate = 8, capacity = 4` = 256-bit capacity) `Poseidon2` permutation (`poseidon2Perm12`)
   with proved invertible external diffusion $M_E = M_4 \otimes P_3$
   ($4 \times 4$ MDS $M_4$ of branch number $5$, external branch number $7$; `applyMEInv_applyME`,
   `applyME_applyMEInv`), Sherman–Morrison invertible internal $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(v)$
   (`applyMIInv_applyMI`, `applyMI_applyMIInv`), non-affine round constants
   (`poseidon2ConstAt_not_affine`), and full permutation bijection (`poseidon2Perm12_bijective`).
3. Canonical `< 2^56` limb framing (`bytesToLimbs56_injective`), multi-rate `10*1` sponge padding
   (`poseidon2Pad_injective`, `poseidon2PadBytes_injective`), and 32-byte `poseidon2Hash32` with
   build-time conformance vectors matching `crates/qsag-core/src/sponge/poseidon2.rs`.
-/

public import Qsag.Math.Goldilocks
public import Qsag.Math.Tactic.CommRing
public import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## 1. Goldilocks Power Map $x \mapsto x^7 \pmod p$ & Exact Inverse $d_{\text{inv}}$ (`sbox7_bijective`) -/

def poseidon2DInv : Nat := 10540996611094048183

theorem goldilocksPred_coprime_seven (x : Goldilocks) :
    7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 ∧
    Nat.gcd 7 (goldilocksPrime - 1) = 1 ∧
    goldilocksPrime - 1 = (2 ^ 32) * 3 * 5 * 17 * 257 * 65537 ∧
    x.val < goldilocksPrime := by
  have hBez : 7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 := rfl
  refine ⟨hBez, ?_, rfl, x.isLt⟩
  obtain ⟨k1, hk1⟩ := Nat.gcd_dvd_left 7 (goldilocksPrime - 1)
  obtain ⟨k2, hk2⟩ := Nat.gcd_dvd_right 7 (goldilocksPrime - 1)
  let g := Nat.gcd 7 (goldilocksPrime - 1)
  have h1 : g ∣ 1 := ⟨k1 * poseidon2DInv - 4 * k2, by
    have h7 : 7 * poseidon2DInv = g * (k1 * poseidon2DInv) := by
      calc 7 * poseidon2DInv = (g * k1) * poseidon2DInv := by rw [← hk1]
      _ = g * (k1 * poseidon2DInv) := Nat.mul_assoc _ _ _
    have h4 : 4 * (goldilocksPrime - 1) = g * (4 * k2) := by
      calc 4 * (goldilocksPrime - 1) = 4 * (g * k2) := by rw [← hk2]
      _ = g * (4 * k2) := by rw [← Nat.mul_assoc, Nat.mul_comm 4 g, Nat.mul_assoc]
    rw [Nat.mul_sub_left_distrib, ← h7, ← h4]
    omega⟩
  exact Nat.eq_one_of_dvd_one h1

/-- Degree-7 algebraic S-box $x \mapsto x^7$ over `Goldilocks` (depth-3 multiplication tree). -/
@[expose] def sbox7 (x : Goldilocks) : Goldilocks :=
  let x2 := Goldilocks.mul x x
  let x3 := Goldilocks.mul x2 x
  let x4 := Goldilocks.mul x2 x2
  Goldilocks.mul x3 x4

theorem sbox7_val (x : Goldilocks) :
    (sbox7 x).val = (x.val ^ 7) % goldilocksPrime := by
  have hx2 : (Goldilocks.mul x x).val = (x.val * x.val) % goldilocksPrime := Goldilocks.mul_val x x
  have hx3 : (Goldilocks.mul (Goldilocks.mul x x) x).val = (x.val * x.val * x.val) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mod_mul_mod]
  have hx4 : (Goldilocks.mul (Goldilocks.mul x x) (Goldilocks.mul x x)).val =
      ((x.val * x.val) * (x.val * x.val)) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  unfold sbox7
  dsimp only
  rw [Goldilocks.mul_val, hx3, hx4, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
  congr 1
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

def goldilocksPowAux : Nat → Goldilocks → Nat → Goldilocks
  | 0, _, _ => Goldilocks.one
  | fuel + 1, base, exp =>
    if exp = 0 then Goldilocks.one
    else
      let half := goldilocksPowAux fuel base (exp / 2)
      let sq := Goldilocks.mul half half
      if exp % 2 = 1 then Goldilocks.mul sq base else sq

def goldilocksPow (x : Goldilocks) (exp : Nat) : Goldilocks :=
  if x.val == 0 then
    if exp == 0 then Goldilocks.one else Goldilocks.zero
  else
    goldilocksPowAux (Nat.log2 exp + 1) x exp

@[expose] def sbox7Inv (x : Goldilocks) : Goldilocks :=
  goldilocksPow x poseidon2DInv

private theorem pow_two_mul_nat (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem goldilocksPowAux_val (fuel : Nat) (base : Goldilocks) :
    ∀ (exp : Nat), exp < 2 ^ fuel →
      (goldilocksPowAux fuel base exp).val = (base.val ^ exp) % goldilocksPrime := by
  induction fuel with
  | zero =>
    intro exp hlt
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0
    rfl
  | succ fuel ih =>
    intro exp hlt
    simp only [goldilocksPowAux]
    if h0 : exp = 0 then
      subst h0
      rfl
    else
      simp only [h0, ↓reduceIte]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt
        omega
      have ihHalf := ih (exp / 2) hexpHalf
      let half := goldilocksPowAux fuel base (exp / 2)
      have hsq : (Goldilocks.mul half half).val = (base.val ^ (2 * (exp / 2))) % goldilocksPrime := by
        rw [Goldilocks.mul_val, ihHalf, ← Nat.mul_mod, ← pow_two_mul_nat]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide +kernel, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        change (Goldilocks.mul (Goldilocks.mul half half) base).val = _
        rw [Goldilocks.mul_val, hsq, Nat.mod_mul_mod]
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one]

theorem goldilocksPow_val (x : Goldilocks) (exp : Nat) :
    (goldilocksPow x exp).val = (x.val ^ exp) % goldilocksPrime := by
  unfold goldilocksPow
  cases hx0 : (x.val == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hFuel : exp < 2 ^ (Nat.log2 exp + 1) := by
      by_cases he : exp = 0
      · subst he; decide
      · exact Nat.lt_log2_self
    exact goldilocksPowAux_val (Nat.log2 exp + 1) x exp hFuel
  · simp only [↓reduceIte]
    have hxEq : x.val = 0 := eq_of_beq hx0
    rw [hxEq]
    cases he0 : (exp == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have heNe : exp ≠ 0 := by intro h; subst h; simp at he0
      rw [Nat.zero_pow (Nat.pos_of_ne_zero heNe), Nat.zero_mod]
      rfl
    · simp only [↓reduceIte]
      have heEq : exp = 0 := eq_of_beq he0
      rw [heEq, Nat.pow_zero]
      rfl

theorem sbox7Inv_val (x : Goldilocks) :
    (sbox7Inv x).val = (x.val ^ poseidon2DInv) % goldilocksPrime :=
  goldilocksPow_val x poseidon2DInv

private theorem pow_mod_congr_nat {x y m : Nat} (h : x % m = y % m) (k : Nat) :
    (x ^ k) % m = (y ^ k) % m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

private theorem pow4_mod_one {u p : Nat} (hp : 1 < p) (hu : u % p = 1) :
    (u ^ 4) % p = 1 := by
  have h2 : u ^ 2 = u * u := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  have h4 : u ^ 4 = (u * u) * (u * u) := by
    rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, h2]
  have hu2 : (u * u) % p = 1 := by
    rw [Nat.mul_mod, hu, Nat.one_mul, Nat.mod_eq_of_lt hp]
  rw [h4, Nat.mul_mod, hu2, Nat.one_mul, Nat.mod_eq_of_lt hp]

private theorem pow_seven_dInv_mod (a : Goldilocks) :
    (a.val ^ (7 * poseidon2DInv)) % goldilocksPrime = a.val := by
  if ha0 : a.val = 0 then
    have hexp0 : 7 * poseidon2DInv = (4 * (goldilocksPrime - 1)) + 1 := rfl
    rw [ha0, hexp0, Nat.zero_pow (by omega), Nat.zero_mod]
  else
    have hndvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hlt := a.isLt
      omega
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod hndvd
    have hexp : 7 * poseidon2DInv = (goldilocksPrime - 1) * 4 + 1 := rfl
    have hp1 : 1 < goldilocksPrime := by decide +kernel
    have hu4 : ((a.val ^ (goldilocksPrime - 1)) ^ 4) % goldilocksPrime = 1 :=
      pow4_mod_one hp1 hflt
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.pow_one, Nat.mul_mod, hu4,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

theorem sbox7Inv_sbox7 (x : Goldilocks) : sbox7Inv (sbox7 x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7 x).val % goldilocksPrime = (x.val ^ 7) % goldilocksPrime := by
    rw [sbox7_val, Nat.mod_mod]
  rw [sbox7Inv_val, pow_mod_congr_nat hCongr poseidon2DInv, ← Nat.pow_mul, pow_seven_dInv_mod]

theorem sbox7_sbox7Inv (x : Goldilocks) : sbox7 (sbox7Inv x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7Inv x).val % goldilocksPrime = (x.val ^ poseidon2DInv) % goldilocksPrime := by
    rw [sbox7Inv_val, Nat.mod_mod]
  rw [sbox7_val, pow_mod_congr_nat hCongr 7, ← Nat.pow_mul, Nat.mul_comm poseidon2DInv 7, pow_seven_dInv_mod]

/-- **Goldilocks Degree-7 S-Box Bijection Theorem (`sbox7_bijective`)**. -/
theorem sbox7_bijective (x y : Goldilocks) :
    sbox7Inv (sbox7 x) = x ∧
    sbox7 (sbox7Inv y) = y ∧
    (sbox7 x = sbox7 y ↔ x = y) ∧
    (∃ z : Goldilocks, sbox7 z = y) := by
  refine ⟨sbox7Inv_sbox7 x, sbox7_sbox7Inv y, ?_, ⟨sbox7Inv y, sbox7_sbox7Inv y⟩⟩
  constructor
  · intro h
    have hInv := congrArg sbox7Inv h
    rwa [sbox7Inv_sbox7, sbox7Inv_sbox7] at hInv
  · intro h
    subst h
    rfl

/-! ## 2. Width-12 State (`rate = 8, capacity = 4`) & Invertible Linear Layers $M_E, M_I$ -/

structure Lane4 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane4.ext {a b : Lane4}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2) (h3 : a.x3 = b.x3) : a = b := by
  cases a; cases b; simp only at *; subst h0 h1 h2 h3; rfl

structure Poseidon2State12 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State12.ext {s t : Poseidon2State12}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2; rfl

def Poseidon2State12.toList (s : Poseidon2State12) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3]

def lane4Zero : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane4Add (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1,
   Goldilocks.add a.x2 b.x2, Goldilocks.add a.x3 b.x3⟩

def lane4Sub (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
   Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩

def lane4Scale (c : Goldilocks) (a : Lane4) : Lane4 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1,
   Goldilocks.mul c a.x2, Goldilocks.mul c a.x3⟩

def lane4Sum (a : Lane4) : Goldilocks :=
  Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3)

private def inv4G : Goldilocks := ⟨13835058052060938241, by decide +kernel⟩
private def inv7G : Goldilocks := ⟨2635249152773512046, by decide +kernel⟩
private def inv15G : Goldilocks := ⟨17216961131453612033, by decide +kernel⟩
private def inv1024G : Goldilocks := ⟨18428729670909296641, by decide +kernel⟩
private def inv3055G : Goldilocks := ⟨10802365021336396514, by decide +kernel⟩

private theorem ofNat_eq_goldOfInt (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

private theorem mul_cancel_of_prod_one {u k : Goldilocks} (h : Goldilocks.mul u k = Goldilocks.one)
    (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv4G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.mul (Goldilocks.ofNat 4) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv4G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.mul inv4G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv7G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv7G (Goldilocks.mul (Goldilocks.ofNat 7) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv7G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv15G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv15G (Goldilocks.mul (Goldilocks.ofNat 15) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv1024G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (Goldilocks.ofNat 1024) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv3055G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv3055G (Goldilocks.mul (Goldilocks.ofNat 3055) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv3055G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 3055) (Goldilocks.mul inv3055G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

def applyM4 (b : Lane4) : Lane4 :=
  let s := lane4Sum b
  let c2 := Goldilocks.ofNat 2
  ⟨Goldilocks.add s (Goldilocks.add b.x0 (Goldilocks.mul c2 b.x1)),
   Goldilocks.add s (Goldilocks.add b.x1 (Goldilocks.mul c2 b.x2)),
   Goldilocks.add s (Goldilocks.add b.x2 (Goldilocks.mul c2 b.x3)),
   Goldilocks.add s (Goldilocks.add b.x3 (Goldilocks.mul c2 b.x0))⟩

private def makeM4InvRaw (y : Lane4) (s : Goldilocks) : Lane4 :=
  let u0 := Goldilocks.sub y.x0 s
  let u1 := Goldilocks.sub y.x1 s
  let u2 := Goldilocks.sub y.x2 s
  let u3 := Goldilocks.sub y.x3 s
  let c2 := Goldilocks.ofNat 2
  let c4 := Goldilocks.ofNat 4
  let c8 := Goldilocks.ofNat 8
  ⟨Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u3) (Goldilocks.mul c4 u2)) (Goldilocks.mul c2 u1)) u0,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u0) (Goldilocks.mul c4 u3)) (Goldilocks.mul c2 u2)) u1,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u1) (Goldilocks.mul c4 u0)) (Goldilocks.mul c2 u3)) u2,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u2) (Goldilocks.mul c4 u1)) (Goldilocks.mul c2 u0)) u3⟩

def applyM4Inv (y : Lane4) : Lane4 :=
  lane4Scale inv15G (makeM4InvRaw y (Goldilocks.mul inv7G (lane4Sum y)))

private theorem lane4Sum_applyM4 (b : Lane4) :
    lane4Sum (applyM4 b) = Goldilocks.mul (Goldilocks.ofNat 7) (lane4Sum b) := by
  unfold applyM4 lane4Sum
  dsimp only
  rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3,
      ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_add, goldOfInt_mul]
  congr 1
  omega

private theorem makeM4InvRaw_applyM4 (b : Lane4) :
    makeM4InvRaw (applyM4 b) (lane4Sum b) = lane4Scale (Goldilocks.ofNat 15) b := by
  unfold makeM4InvRaw applyM4 lane4Sum lane4Scale
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4Inv_applyM4 (b : Lane4) : applyM4Inv (applyM4 b) = b := by
  unfold applyM4Inv
  rw [lane4Sum_applyM4, inv7G_mul_cancel, makeM4InvRaw_applyM4]
  unfold lane4Scale
  exact Lane4.ext
    (inv15G_mul_cancel b.x0)
    (inv15G_mul_cancel b.x1)
    (inv15G_mul_cancel b.x2)
    (inv15G_mul_cancel b.x3)

private theorem applyM4_scale (c : Goldilocks) (b : Lane4) :
    applyM4 (lane4Scale c b) = lane4Scale c (applyM4 b) := by
  have h2 : ∀ x : Int, (c.val : Int) * (((2 : Nat) : Int) * x) =
      ((2 : Nat) : Int) * ((c.val : Int) * x) := fun x => by
    rw [← Int.mul_assoc, Int.mul_comm (c.val : Int) ((2 : Nat) : Int), Int.mul_assoc]
  unfold applyM4 lane4Scale lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat c, ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1,
         ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul, Int.mul_add, h2])

private theorem applyM4_makeM4InvRaw (y : Lane4) (s : Goldilocks) :
    applyM4 (makeM4InvRaw y s) =
      let rem := Goldilocks.mul (Goldilocks.ofNat 5)
        (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) s))
      ⟨Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x0) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x1) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x2) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x3) rem⟩ := by
  unfold applyM4 makeM4InvRaw lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat y.x0, ← goldOfInt_nat y.x1, ← goldOfInt_nat y.x2,
         ← goldOfInt_nat y.x3, ← goldOfInt_nat s];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4_applyM4Inv (y : Lane4) : applyM4 (applyM4Inv y) = y := by
  unfold applyM4Inv
  rw [applyM4_scale, applyM4_makeM4InvRaw]
  have hs7 : Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)) = lane4Sum y :=
    mul_inv7G_cancel (lane4Sum y)
  have hRemZero : Goldilocks.mul (Goldilocks.ofNat 5)
      (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)))) =
      Goldilocks.zero := by
    rw [hs7]
    have hz : Goldilocks.sub (lane4Sum y) (lane4Sum y) = Goldilocks.zero := by
      change CommRingOps.sub (lane4Sum y) (lane4Sum y) = CommRingOps.zero
      exact LawfulCommRing.sub_self _
    rw [hz]
    change CommRingOps.mul (Goldilocks.ofNat 5) CommRingOps.zero = CommRingOps.zero
    exact LawfulCommRing.mul_zero _
  unfold lane4Scale
  dsimp only at *
  rw [hRemZero]
  have hAddZero : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a := fun a => by
    change CommRingOps.add a CommRingOps.zero = a
    exact LawfulCommRing.add_zero a
  rw [hAddZero, hAddZero, hAddZero, hAddZero]
  exact Lane4.ext
    (inv15G_mul_cancel y.x0)
    (inv15G_mul_cancel y.x1)
    (inv15G_mul_cancel y.x2)
    (inv15G_mul_cancel y.x3)

@[expose] def applyMEStd (st : Poseidon2State12) : Poseidon2State12 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let s := lane4Add (lane4Add y0 y1) y2
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s⟩

def applyMEStdInv (st : Poseidon2State12) : Poseidon2State12 :=
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  let s := lane4Scale inv4G sumAll
  ⟨applyM4Inv (lane4Sub st.b0 s),
   applyM4Inv (lane4Sub st.b1 s),
   applyM4Inv (lane4Sub st.b2 s)⟩

private theorem scalar_sum_four_cancel (a b c : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c))) =
      Goldilocks.add (Goldilocks.add a b) c := by
  have h : Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c)) =
      Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.add (Goldilocks.add a b) c) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  rw [h, inv4G_mul_cancel]

private theorem lane4_sum_four_cancel (y0 y1 y2 : Lane4) :
    lane4Scale inv4G (lane4Add (lane4Add (lane4Add y0 (lane4Add (lane4Add y0 y1) y2))
      (lane4Add y1 (lane4Add (lane4Add y0 y1) y2)))
      (lane4Add y2 (lane4Add (lane4Add y0 y1) y2))) =
    lane4Add (lane4Add y0 y1) y2 := by
  unfold lane4Scale lane4Add
  exact Lane4.ext
    (scalar_sum_four_cancel y0.x0 y1.x0 y2.x0)
    (scalar_sum_four_cancel y0.x1 y1.x1 y2.x1)
    (scalar_sum_four_cancel y0.x2 y1.x2 y2.x2)
    (scalar_sum_four_cancel y0.x3 y1.x3 y2.x3)

private theorem lane4Sub_add_right (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _;
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyMEStdInv_applyMEStd (st : Poseidon2State12) : applyMEStdInv (applyMEStd st) = st := by
  unfold applyMEStdInv applyMEStd
  dsimp only
  rw [lane4_sum_four_cancel]
  rw [lane4Sub_add_right, lane4Sub_add_right, lane4Sub_add_right]
  rw [applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4]

private theorem lane4SubSumId (b0 b1 b2 s : Lane4) :
    lane4Add (lane4Add (lane4Sub b0 s) (lane4Sub b1 s)) (lane4Sub b2 s) =
      lane4Add s (lane4Sub (lane4Add (lane4Add b0 b1) b2) (lane4Scale (Goldilocks.ofNat 4) s)) := by
  unfold lane4Add lane4Sub lane4Scale
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b0.x0, ← goldOfInt_nat b0.x1, ← goldOfInt_nat b0.x2, ← goldOfInt_nat b0.x3,
         ← goldOfInt_nat b1.x0, ← goldOfInt_nat b1.x1, ← goldOfInt_nat b1.x2, ← goldOfInt_nat b1.x3,
         ← goldOfInt_nat b2.x0, ← goldOfInt_nat b2.x1, ← goldOfInt_nat b2.x2, ← goldOfInt_nat b2.x3,
         ← goldOfInt_nat s.x0, ← goldOfInt_nat s.x1, ← goldOfInt_nat s.x2, ← goldOfInt_nat s.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyMEStd_applyMEStdInv (st : Poseidon2State12) : applyMEStd (applyMEStdInv st) = st := by
  unfold applyMEStd applyMEStdInv
  dsimp only
  rw [applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv]
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  have h4 : lane4Scale (Goldilocks.ofNat 4) (lane4Scale inv4G sumAll) = sumAll := by
    unfold lane4Scale
    exact Lane4.ext
      (mul_inv4G_cancel sumAll.x0)
      (mul_inv4G_cancel sumAll.x1)
      (mul_inv4G_cancel sumAll.x2)
      (mul_inv4G_cancel sumAll.x3)
  have hSumSub : lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)) =
      lane4Scale inv4G sumAll := by
    rw [lane4SubSumId st.b0 st.b1 st.b2 (lane4Scale inv4G sumAll), h4]
    have hZero : lane4Sub sumAll sumAll = lane4Zero := by
      unfold lane4Sub lane4Zero
      apply Lane4.ext <;> exact LawfulCommRing.sub_self _
    rw [hZero]
    unfold lane4Add lane4Zero
    apply Lane4.ext <;> exact LawfulCommRing.add_zero _
  change Poseidon2State12.mk
    (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b1 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b2 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)))) = st
  rw [hSumSub]
  have hAddSub : ∀ a b : Lane4, lane4Add (lane4Sub a b) b = a := fun a b => by
    unfold lane4Add lane4Sub
    apply Lane4.ext <;>
      (change CommRingOps.add (CommRingOps.sub _ _) _ = _;
       rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left])
  rw [hAddSub, hAddSub, hAddSub]

/-- Lane transposition for the canonical M4 tensor P3 external layer. -/
def poseidon2Transpose4x3 (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨⟨s.b0.x0, s.b0.x3, s.b1.x2, s.b2.x1⟩,
   ⟨s.b0.x1, s.b1.x0, s.b1.x3, s.b2.x2⟩,
   ⟨s.b0.x2, s.b1.x1, s.b2.x0, s.b2.x3⟩⟩

def poseidon2Transpose3x4 (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨⟨s.b0.x0, s.b1.x0, s.b2.x0, s.b0.x1⟩,
   ⟨s.b1.x1, s.b2.x1, s.b0.x2, s.b1.x2⟩,
   ⟨s.b2.x2, s.b0.x3, s.b1.x3, s.b2.x3⟩⟩

@[simp] theorem poseidon2Transpose34_43 (s : Poseidon2State12) :
    poseidon2Transpose3x4 (poseidon2Transpose4x3 s) = s := by
  cases s with | mk a b c => cases a; cases b; cases c; rfl

@[simp] theorem poseidon2Transpose43_34 (s : Poseidon2State12) :
    poseidon2Transpose4x3 (poseidon2Transpose3x4 s) = s := by
  cases s with | mk a b c => cases a; cases b; cases c; rfl

@[expose] def applyME (s : Poseidon2State12) : Poseidon2State12 :=
  poseidon2Transpose3x4 (applyMEStd (poseidon2Transpose4x3 s))

def applyMEInv (s : Poseidon2State12) : Poseidon2State12 :=
  poseidon2Transpose3x4 (applyMEStdInv (poseidon2Transpose4x3 s))

theorem applyMEInv_applyME (s : Poseidon2State12) : applyMEInv (applyME s) = s := by
  simp only [applyMEInv, applyME, poseidon2Transpose43_34, applyMEStdInv_applyMEStd,
    poseidon2Transpose34_43]

theorem applyME_applyMEInv (s : Poseidon2State12) : applyME (applyMEInv s) = s := by
  simp only [applyMEInv, applyME, poseidon2Transpose43_34, applyMEStd_applyMEStdInv,
    poseidon2Transpose34_43]

def state12Sum (st : Poseidon2State12) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1)) (lane4Sum st.b2)

@[expose] def applyMI (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  let b0 := st.b0
  let b1 := st.b1
  let b2 := st.b2
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-64)) b0.x0) s,
    Goldilocks.add b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) b2.x3) s⟩⟩

private def weightedSumMI (y : Poseidon2State12) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt (-16)) y.b0.x0) (Goldilocks.mul (goldOfInt 1024) y.b0.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 512) y.b0.x2) (Goldilocks.mul (goldOfInt 256) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 128) y.b1.x0) (Goldilocks.mul (goldOfInt 64) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.b1.x2) (Goldilocks.mul (goldOfInt 16) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8) y.b2.x0) (Goldilocks.mul (goldOfInt 4) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.b2.x2) y.b2.x3)
  Goldilocks.add (Goldilocks.add t0 t1) t2

private def makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) : Poseidon2State12 :=
  let scale (w : Int) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))
  ⟨⟨scale (-16) y.b0.x0, scale 1024 y.b0.x1, scale 512 y.b0.x2, scale 256 y.b0.x3⟩,
   ⟨scale 128 y.b1.x0, scale 64 y.b1.x1, scale 32 y.b1.x2, scale 16 y.b1.x3⟩,
   ⟨scale 8 y.b2.x0, scale 4 y.b2.x1, scale 2 y.b2.x2, scale 1 y.b2.x3⟩⟩

def applyMIInv (y : Poseidon2State12) : Poseidon2State12 :=
  makeMIInvRaw y inv1024G (Goldilocks.mul inv3055G (weightedSumMI y))

private theorem weightedSumMI_applyMI (st : Poseidon2State12) :
    weightedSumMI (applyMI st) = Goldilocks.mul (Goldilocks.ofNat 3055) (state12Sum st) := by
  unfold weightedSumMI applyMI state12Sum lane4Sum
  dsimp only
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
  congr 1; omega

private theorem mi_lane_recover (v w : Int) (hv : v * w = 1024) (x s : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s)) = x := by
  have hProd : Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : w * (v * (x.val : Int) + (s.val : Int) - (s.val : Int)) = (v * w) * (x.val : Int) := by
      rw [Int.add_sub_cancel, ← Int.mul_assoc, Int.mul_comm w v]
    rw [hEq, hv]
    omega
  rw [hProd, inv1024G_mul_cancel x]

theorem applyMIInv_applyMI (st : Poseidon2State12) : applyMIInv (applyMI st) = st := by
  unfold applyMIInv
  rw [weightedSumMI_applyMI, inv3055G_mul_cancel (state12Sum st)]
  unfold makeMIInvRaw applyMI
  dsimp only
  have h1 : Goldilocks.add st.b0.x1 (state12Sum st) =
      Goldilocks.add (Goldilocks.mul (goldOfInt 1) st.b0.x1) (state12Sum st) := by
    have hone : goldOfInt 1 = CommRingOps.one := rfl
    change _ = Goldilocks.add (CommRingOps.mul (goldOfInt 1) st.b0.x1) _
    rw [hone, LawfulCommRing.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_recover (-64) (-16) rfl st.b0.x0 (state12Sum st)
    · rw [h1]; exact mi_lane_recover 1 1024 rfl st.b0.x1 (state12Sum st)
    · exact mi_lane_recover 2 512 rfl st.b0.x2 (state12Sum st)
    · exact mi_lane_recover 4 256 rfl st.b0.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 8 128 rfl st.b1.x0 (state12Sum st)
    · exact mi_lane_recover 16 64 rfl st.b1.x1 (state12Sum st)
    · exact mi_lane_recover 32 32 rfl st.b1.x2 (state12Sum st)
    · exact mi_lane_recover 64 16 rfl st.b1.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 128 8 rfl st.b2.x0 (state12Sum st)
    · exact mi_lane_recover 256 4 rfl st.b2.x1 (state12Sum st)
    · exact mi_lane_recover 512 2 rfl st.b2.x2 (state12Sum st)
    · exact mi_lane_recover 1024 1 rfl st.b2.x3 (state12Sum st)

private theorem mi_lane_assoc_aux (v w : Int) (hv : v * w = 1024) (inv1024 yi s : Goldilocks) :
    Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))) =
      Goldilocks.mul inv1024 (Goldilocks.mul (Goldilocks.ofNat 1024) (Goldilocks.sub yi s)) := by
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat yi, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1
  have hEq : v * ((inv1024.val : Int) * (w * ((yi.val : Int) - (s.val : Int)))) =
      (inv1024.val : Int) * ((v * w) * ((yi.val : Int) - (s.val : Int))) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v (inv1024.val : Int),
        Int.mul_assoc (inv1024.val : Int) v w, Int.mul_assoc]
  rw [hEq, hv]
  rfl

private theorem mi_lane_forward (v w : Int) (hv : v * w = 1024) (yi s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s)))) s = yi := by
  rw [mi_lane_assoc_aux v w hv inv1024G yi s, inv1024G_mul_cancel (Goldilocks.sub yi s)]
  change CommRingOps.add (CommRingOps.sub yi s) s = yi
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

private theorem state12Sum_makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) :
    state12Sum (makeMIInvRaw y inv1024 s) =
      Goldilocks.mul inv1024 (Goldilocks.sub (weightedSumMI y) (Goldilocks.mul (goldOfInt 2031) s)) := by
  unfold state12Sum makeMIInvRaw lane4Sum weightedSumMI
  dsimp only
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat s,
      ← goldOfInt_nat y.b0.x0, ← goldOfInt_nat y.b0.x1, ← goldOfInt_nat y.b0.x2, ← goldOfInt_nat y.b0.x3,
      ← goldOfInt_nat y.b1.x0, ← goldOfInt_nat y.b1.x1, ← goldOfInt_nat y.b1.x2, ← goldOfInt_nat y.b1.x3,
      ← goldOfInt_nat y.b2.x0, ← goldOfInt_nat y.b2.x1, ← goldOfInt_nat y.b2.x2, ← goldOfInt_nat y.b2.x3]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
  congr 1
  congr 1
  omega

private theorem mi_3055_sub_2031 (s : Goldilocks) :
    Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 3055) s) (Goldilocks.mul (goldOfInt 2031) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) s := by
  rw [← goldOfInt_nat s, ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

private theorem applyMI_makeMIInvRaw_helper (y : Poseidon2State12) (s : Goldilocks)
    (hSum : state12Sum (makeMIInvRaw y inv1024G s) = s) :
    applyMI (makeMIInvRaw y inv1024G s) = y := by
  unfold applyMI
  rw [hSum]
  unfold makeMIInvRaw
  dsimp only
  have h1 : ∀ a : Goldilocks, a = Goldilocks.mul (goldOfInt 1) a := fun a => by
    rw [← goldOfInt_nat a, goldOfInt_mul, Int.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_forward (-64) (-16) rfl y.b0.x0 s
    · rw [h1 (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt 1024) (Goldilocks.sub y.b0.x1 s)))]
      exact mi_lane_forward 1 1024 rfl y.b0.x1 s
    · exact mi_lane_forward 2 512 rfl y.b0.x2 s
    · exact mi_lane_forward 4 256 rfl y.b0.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 8 128 rfl y.b1.x0 s
    · exact mi_lane_forward 16 64 rfl y.b1.x1 s
    · exact mi_lane_forward 32 32 rfl y.b1.x2 s
    · exact mi_lane_forward 64 16 rfl y.b1.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 128 8 rfl y.b2.x0 s
    · exact mi_lane_forward 256 4 rfl y.b2.x1 s
    · exact mi_lane_forward 512 2 rfl y.b2.x2 s
    · exact mi_lane_forward 1024 1 rfl y.b2.x3 s

theorem applyMI_applyMIInv (y : Poseidon2State12) : applyMI (applyMIInv y) = y := by
  have hs3055 : Goldilocks.mul (Goldilocks.ofNat 3055) (Goldilocks.mul inv3055G (weightedSumMI y)) =
      weightedSumMI y :=
    mul_inv3055G_cancel (weightedSumMI y)
  have hSumEq : state12Sum (makeMIInvRaw y inv1024G (Goldilocks.mul inv3055G (weightedSumMI y))) =
      Goldilocks.mul inv3055G (weightedSumMI y) := by
    rw [state12Sum_makeMIInvRaw]
    conv => lhs; arg 2; arg 1; rw [← hs3055]
    rw [mi_3055_sub_2031, inv1024G_mul_cancel]
  exact applyMI_makeMIInvRaw_helper y (Goldilocks.mul inv3055G (weightedSumMI y)) hSumEq

/-! ## 3. Full Width-12 `Poseidon2` Permutation ($R_F = 8, R_P = 22$) & `poseidon2Perm12_bijective` -/

def state12Zero : Poseidon2State12 :=
  ⟨lane4Zero, lane4Zero, lane4Zero⟩

def state12Add (a b : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Add a.b0 b.b0, lane4Add a.b1 b.b1, lane4Add a.b2 b.b2⟩

def state12Sub (a b : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Sub a.b0 b.b0, lane4Sub a.b1 b.b1, lane4Sub a.b2 b.b2⟩

def state12Scale (c : Goldilocks) (a : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Scale c a.b0, lane4Scale c a.b1, lane4Scale c a.b2⟩

theorem state12Zero_eq : state12Zero = ⟨lane4Zero, lane4Zero, lane4Zero⟩ := by rfl
theorem lane4Zero_eq : lane4Zero = ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ := by rfl
theorem state12Add_eq (a b : Poseidon2State12) :
    state12Add a b = ⟨lane4Add a.b0 b.b0, lane4Add a.b1 b.b1, lane4Add a.b2 b.b2⟩ := by rfl
theorem state12Scale_eq (c : Goldilocks) (a : Poseidon2State12) :
    state12Scale c a = ⟨lane4Scale c a.b0, lane4Scale c a.b1, lane4Scale c a.b2⟩ := by rfl
theorem lane4Add_eq (a b : Lane4) :
    lane4Add a b = ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1, Goldilocks.add a.x2 b.x2, Goldilocks.add a.x3 b.x3⟩ := by rfl
theorem lane4Scale_eq (c : Goldilocks) (a : Lane4) :
    lane4Scale c a = ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1, Goldilocks.mul c a.x2, Goldilocks.mul c a.x3⟩ := by rfl

private theorem goldilocks_add_add_add_comm (a b c d : Goldilocks) :
    Goldilocks.add (Goldilocks.add a b) (Goldilocks.add c d) =
    Goldilocks.add (Goldilocks.add a c) (Goldilocks.add b d) := by
  apply Goldilocks.ext
  simp only [Goldilocks.add_val, Nat.add_mod_mod, Nat.mod_add_mod]
  exact congrArg (· % goldilocksPrime) (by omega)

private theorem goldilocks_mul_add (c a b : Goldilocks) :
    Goldilocks.mul c (Goldilocks.add a b) =
    Goldilocks.add (Goldilocks.mul c a) (Goldilocks.mul c b) := by
  apply Goldilocks.ext
  simp only [Goldilocks.mul_val, Goldilocks.add_val]
  rw [Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.left_distrib]

private theorem lane4Add_add_add_comm (a b c d : Lane4) :
    lane4Add (lane4Add a b) (lane4Add c d) = lane4Add (lane4Add a c) (lane4Add b d) := by
  unfold lane4Add
  exact Lane4.ext
    (goldilocks_add_add_add_comm _ _ _ _)
    (goldilocks_add_add_add_comm _ _ _ _)
    (goldilocks_add_add_add_comm _ _ _ _)
    (goldilocks_add_add_add_comm _ _ _ _)

private theorem applyM4_add (a b : Lane4) :
    applyM4 (lane4Add a b) = lane4Add (applyM4 a) (applyM4 b) := by
  unfold applyM4 lane4Add lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat a.x0, ← goldOfInt_nat a.x1, ← goldOfInt_nat a.x2, ← goldOfInt_nat a.x3,
         ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul];
     congr 1; omega)

theorem applyMEStd_zero : applyMEStd state12Zero = state12Zero := by
  unfold applyMEStd state12Zero applyM4 lane4Zero lane4Add lane4Sum
  dsimp only
  have hz : Goldilocks.zero = goldOfInt 0 := rfl
  apply Poseidon2State12.ext <;> apply Lane4.ext <;>
    (simp only [hz, ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]; congr 1)

theorem applyMEStd_add (a b : Poseidon2State12) :
    applyMEStd (state12Add a b) = state12Add (applyMEStd a) (applyMEStd b) := by
  unfold applyMEStd state12Add
  dsimp only
  rw [applyM4_add, applyM4_add, applyM4_add]
  have hs :
      lane4Add (lane4Add (lane4Add (applyM4 a.b0) (applyM4 b.b0))
                         (lane4Add (applyM4 a.b1) (applyM4 b.b1)))
               (lane4Add (applyM4 a.b2) (applyM4 b.b2)) =
      lane4Add (lane4Add (lane4Add (applyM4 a.b0) (applyM4 a.b1)) (applyM4 a.b2))
               (lane4Add (lane4Add (applyM4 b.b0) (applyM4 b.b1)) (applyM4 b.b2)) := by
    rw [lane4Add_add_add_comm (applyM4 a.b0) (applyM4 b.b0) (applyM4 a.b1) (applyM4 b.b1),
        lane4Add_add_add_comm]
  rw [hs]
  exact Poseidon2State12.ext
    (lane4Add_add_add_comm _ _ _ _).symm
    (lane4Add_add_add_comm _ _ _ _).symm
    (lane4Add_add_add_comm _ _ _ _).symm

theorem applyMEStd_scale (c : Goldilocks) (a : Poseidon2State12) :
    applyMEStd (state12Scale c a) = state12Scale c (applyMEStd a) := by
  unfold applyMEStd state12Scale
  dsimp only
  rw [applyM4_scale, applyM4_scale, applyM4_scale]
  unfold lane4Add lane4Scale
  dsimp only
  apply Poseidon2State12.ext <;> apply Lane4.ext <;>
    simp only [goldilocks_mul_add]

theorem applyME_zero : applyME state12Zero = state12Zero := by
  unfold applyME
  change poseidon2Transpose3x4 (applyMEStd state12Zero) = state12Zero
  rw [applyMEStd_zero]
  rfl

theorem applyME_add (a b : Poseidon2State12) :
    applyME (state12Add a b) = state12Add (applyME a) (applyME b) := by
  have ht : poseidon2Transpose4x3 (state12Add a b) =
      state12Add (poseidon2Transpose4x3 a) (poseidon2Transpose4x3 b) := rfl
  have hu (x y : Poseidon2State12) : poseidon2Transpose3x4 (state12Add x y) =
      state12Add (poseidon2Transpose3x4 x) (poseidon2Transpose3x4 y) := rfl
  exact (congrArg (fun x => poseidon2Transpose3x4 (applyMEStd x)) ht).trans
    ((congrArg poseidon2Transpose3x4
      (applyMEStd_add (poseidon2Transpose4x3 a) (poseidon2Transpose4x3 b))).trans (hu _ _))

theorem applyME_scale (c : Goldilocks) (a : Poseidon2State12) :
    applyME (state12Scale c a) = state12Scale c (applyME a) := by
  have ht : poseidon2Transpose4x3 (state12Scale c a) =
      state12Scale c (poseidon2Transpose4x3 a) := rfl
  have hu (x : Poseidon2State12) : poseidon2Transpose3x4 (state12Scale c x) =
      state12Scale c (poseidon2Transpose3x4 x) := rfl
  exact (congrArg (fun x => poseidon2Transpose3x4 (applyMEStd x)) ht).trans
    ((congrArg poseidon2Transpose3x4
      (applyMEStd_scale c (poseidon2Transpose4x3 a))).trans (hu _))

theorem applyMI_zero : applyMI state12Zero = state12Zero := by
  unfold applyMI state12Zero state12Sum lane4Zero lane4Sum
  dsimp only
  have hz : Goldilocks.zero = goldOfInt 0 := rfl
  apply Poseidon2State12.ext <;> apply Lane4.ext <;>
    (simp only [hz, goldOfInt_add, goldOfInt_mul]; congr 1)

theorem applyMI_add (a b : Poseidon2State12) :
    applyMI (state12Add a b) = state12Add (applyMI a) (applyMI b) := by
  have hLane : ∀ (d u v sa sb : Goldilocks),
      Goldilocks.add (Goldilocks.mul d (Goldilocks.add u v)) (Goldilocks.add sa sb) =
      Goldilocks.add (Goldilocks.add (Goldilocks.mul d u) sa) (Goldilocks.add (Goldilocks.mul d v) sb) :=
    fun d u v sa sb => by
      rw [goldilocks_mul_add d u v]
      exact goldilocks_add_add_add_comm _ _ _ _
  have hSum : state12Sum (state12Add a b) = Goldilocks.add (state12Sum a) (state12Sum b) := by
    unfold state12Sum state12Add lane4Sum lane4Add
    dsimp only
    apply Goldilocks.ext
    simp only [Goldilocks.add_val, Nat.add_mod_mod, Nat.mod_add_mod]
    exact congrArg (· % goldilocksPrime) (by omega)
  unfold applyMI
  rw [hSum]
  unfold state12Add lane4Add
  dsimp only
  exact Poseidon2State12.ext
    (Lane4.ext (hLane _ _ _ _ _) (goldilocks_add_add_add_comm _ _ _ _) (hLane _ _ _ _ _) (hLane _ _ _ _ _))
    (Lane4.ext (hLane _ _ _ _ _) (hLane _ _ _ _ _) (hLane _ _ _ _ _) (hLane _ _ _ _ _))
    (Lane4.ext (hLane _ _ _ _ _) (hLane _ _ _ _ _) (hLane _ _ _ _ _) (hLane _ _ _ _ _))

theorem applyMI_scale (c : Goldilocks) (a : Poseidon2State12) :
    applyMI (state12Scale c a) = state12Scale c (applyMI a) := by
  have hLane : ∀ (d x s : Goldilocks),
      Goldilocks.add (Goldilocks.mul d (Goldilocks.mul c x)) (Goldilocks.mul c s) =
      Goldilocks.mul c (Goldilocks.add (Goldilocks.mul d x) s) := fun d x s => by
    have hComm : Goldilocks.mul d (Goldilocks.mul c x) = Goldilocks.mul c (Goldilocks.mul d x) := by
      apply Goldilocks.ext
      simp only [Goldilocks.mul_val]
      rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_comm d.val c.val, Nat.mul_assoc, ← Nat.mul_mod_mod]
    rw [hComm, ← goldilocks_mul_add]
  have hSum : state12Sum (state12Scale c a) = Goldilocks.mul c (state12Sum a) := by
    unfold state12Sum state12Scale lane4Sum lane4Scale
    dsimp only
    simp only [goldilocks_mul_add]
  unfold applyMI
  rw [hSum]
  unfold state12Scale lane4Scale
  dsimp only
  exact Poseidon2State12.ext
    (Lane4.ext (hLane _ _ _) (goldilocks_mul_add _ _ _).symm (hLane _ _ _) (hLane _ _ _))
    (Lane4.ext (hLane _ _ _) (hLane _ _ _) (hLane _ _ _) (hLane _ _ _))
    (Lane4.ext (hLane _ _ _) (hLane _ _ _) (hLane _ _ _) (hLane _ _ _))

private theorem state12Sub_add_right (a c : Poseidon2State12) : state12Sub (state12Add a c) c = a := by
  unfold state12Sub state12Add
  exact Poseidon2State12.ext (lane4Sub_add_right _ _) (lane4Sub_add_right _ _) (lane4Sub_add_right _ _)

private theorem state12Add_sub_right (a c : Poseidon2State12) : state12Add (state12Sub a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Add (lane4Sub x y) y = x := fun x y => by
    unfold lane4Add lane4Sub
    apply Lane4.ext <;>
      (change CommRingOps.add (CommRingOps.sub _ _) _ = _;
       rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left])
  unfold state12Add state12Sub
  exact Poseidon2State12.ext (h4 _ _) (h4 _ _) (h4 _ _)

def sboxLane4 (b : Lane4) : Lane4 :=
  ⟨sbox7 b.x0, sbox7 b.x1, sbox7 b.x2, sbox7 b.x3⟩

def sboxLane4Inv (b : Lane4) : Lane4 :=
  ⟨sbox7Inv b.x0, sbox7Inv b.x1, sbox7Inv b.x2, sbox7Inv b.x3⟩

def sboxState12 (st : Poseidon2State12) : Poseidon2State12 :=
  ⟨sboxLane4 st.b0, sboxLane4 st.b1, sboxLane4 st.b2⟩

def sboxState12Inv (st : Poseidon2State12) : Poseidon2State12 :=
  ⟨sboxLane4Inv st.b0, sboxLane4Inv st.b1, sboxLane4Inv st.b2⟩

private theorem sboxState12Inv_sboxState12 (st : Poseidon2State12) :
    sboxState12Inv (sboxState12 st) = st := by
  unfold sboxState12Inv sboxState12 sboxLane4Inv sboxLane4
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact sbox7Inv_sbox7 _

private theorem sboxState12_sboxState12Inv (st : Poseidon2State12) :
    sboxState12 (sboxState12Inv st) = st := by
  unfold sboxState12 sboxState12Inv sboxLane4 sboxLane4Inv
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact sbox7_sbox7Inv _

def externalRound (rc : Poseidon2State12) (st : Poseidon2State12) : Poseidon2State12 :=
  applyME (sboxState12 (state12Add st rc))

def externalRoundInv (rc : Poseidon2State12) (st : Poseidon2State12) : Poseidon2State12 :=
  state12Sub (sboxState12Inv (applyMEInv st)) rc

private theorem externalRoundInv_externalRound (rc st : Poseidon2State12) :
    externalRoundInv rc (externalRound rc st) = st := by
  unfold externalRoundInv externalRound
  rw [applyMEInv_applyME, sboxState12Inv_sboxState12, state12Sub_add_right]

private theorem externalRound_externalRoundInv (rc st : Poseidon2State12) :
    externalRound rc (externalRoundInv rc st) = st := by
  unfold externalRound externalRoundInv
  rw [state12Add_sub_right, sboxState12_sboxState12Inv, applyME_applyMEInv]

def internalRound (rc : Goldilocks) (st : Poseidon2State12) : Poseidon2State12 :=
  let x0' := sbox7 (Goldilocks.add st.b0.x0 rc)
  applyMI ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2⟩

def internalRoundInv (rc : Goldilocks) (st : Poseidon2State12) : Poseidon2State12 :=
  let u := applyMIInv st
  let x0 := Goldilocks.sub (sbox7Inv u.b0.x0) rc
  ⟨⟨x0, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2⟩

private theorem internalRoundInv_internalRound (rc : Goldilocks) (st : Poseidon2State12) :
    internalRoundInv rc (internalRound rc st) = st := by
  unfold internalRoundInv internalRound
  rw [applyMIInv_applyMI]
  dsimp only
  rw [sbox7Inv_sbox7]
  have hSub : Goldilocks.sub (Goldilocks.add st.b0.x0 rc) rc = st.b0.x0 := by
    change CommRingOps.sub (CommRingOps.add st.b0.x0 rc) rc = st.b0.x0
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  rw [hSub]

private theorem internalRound_step_cancel (rc : Goldilocks) (u : Poseidon2State12) :
    internalRound rc ⟨⟨Goldilocks.sub (sbox7Inv u.b0.x0) rc, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2⟩ =
      applyMI u := by
  cases u with | mk b0 b1 b2 =>
    cases b0 with | mk x0 x1 x2 x3 =>
      unfold internalRound
      dsimp only
      have hAdd : Goldilocks.add (Goldilocks.sub (sbox7Inv x0) rc) rc = sbox7Inv x0 := by
        change CommRingOps.add (CommRingOps.sub (sbox7Inv x0) rc) rc = sbox7Inv x0
        rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
      rw [hAdd, sbox7_sbox7Inv]

private theorem internalRound_internalRoundInv (rc : Goldilocks) (st : Poseidon2State12) :
    internalRound rc (internalRoundInv rc st) = st := by
  change internalRound rc
    ⟨⟨Goldilocks.sub (sbox7Inv (applyMIInv st).b0.x0) rc,
      (applyMIInv st).b0.x1, (applyMIInv st).b0.x2, (applyMIInv st).b0.x3⟩,
     (applyMIInv st).b1, (applyMIInv st).b2⟩ = st
  rw [internalRound_step_cancel rc (applyMIInv st), applyMI_applyMIInv]

def splitMix64Mix (x : UInt64) : UInt64 :=
  let z0 := x + 0x9E3779B97F4A7C15
  let z1 := (z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9
  let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
  z2 ^^^ (z2 >>> 31)

def poseidon2ConstIV : UInt64 := 0x504F53325F474C31

def poseidon2ConstWord (tag round lane : Nat) : UInt64 :=
  splitMix64Mix (splitMix64Mix (splitMix64Mix (poseidon2ConstIV ^^^ UInt64.ofNat tag) ^^^ UInt64.ofNat round) ^^^
    UInt64.ofNat lane)

def poseidon2ConstAt (tag round lane : Nat) : Goldilocks :=
  Goldilocks.ofNat (poseidon2ConstWord tag round lane).toNat

/-- Non-affinity of the round-constant generator across rounds. -/
theorem poseidon2ConstAt_not_affine (a b : Goldilocks) :
    ¬ ∀ r : Nat, poseidon2ConstAt 1 r 0 = Goldilocks.add a (Goldilocks.mul b (Goldilocks.ofNat r)) := by
  intro h
  have key : ((poseidon2ConstAt 1 0 0).val + (poseidon2ConstAt 1 2 0).val) % goldilocksPrime ≠
      (2 * (poseidon2ConstAt 1 1 0).val) % goldilocksPrime := by decide +kernel
  have h0 := congrArg Goldilocks.val (h 0)
  have h1 := congrArg Goldilocks.val (h 1)
  have h2 := congrArg Goldilocks.val (h 2)
  rw [Goldilocks.add_val, Goldilocks.mul_val] at h0 h1 h2
  have o0 : (Goldilocks.ofNat 0).val = 0 := by decide +kernel
  have o1 : (Goldilocks.ofNat 1).val = 1 := by decide +kernel
  have o2 : (Goldilocks.ofNat 2).val = 2 := by decide +kernel
  rw [o0] at h0; rw [o1] at h1; rw [o2] at h2
  apply key; rw [h0, h1, h2]
  have ha := a.isLt
  have hb := b.isLt
  simp only [goldilocksPrime] at *
  omega

def poseidon2ExtRoundConst (tag round : Nat) : Poseidon2State12 :=
  ⟨⟨poseidon2ConstAt tag round 0, poseidon2ConstAt tag round 1,
    poseidon2ConstAt tag round 2, poseidon2ConstAt tag round 3⟩,
   ⟨poseidon2ConstAt tag round 4, poseidon2ConstAt tag round 5,
    poseidon2ConstAt tag round 6, poseidon2ConstAt tag round 7⟩,
   ⟨poseidon2ConstAt tag round 8, poseidon2ConstAt tag round 9,
    poseidon2ConstAt tag round 10, poseidon2ConstAt tag round 11⟩⟩

def poseidon2InitialExtConsts : List Poseidon2State12 :=
  (List.range 4).map (poseidon2ExtRoundConst 0)

def poseidon2InternalConsts : List Goldilocks :=
  (List.range 22).map (fun r => poseidon2ConstAt 1 r 0)

def poseidon2TerminalExtConsts : List Poseidon2State12 :=
  (List.range 4).map (poseidon2ExtRoundConst 2)

def runRounds {α σ : Type} (step : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => runRounds step cs (step c s)

theorem sboxState12_eq (st : Poseidon2State12) :
    sboxState12 st =
      ⟨⟨sbox7 st.b0.x0, sbox7 st.b0.x1, sbox7 st.b0.x2, sbox7 st.b0.x3⟩,
       ⟨sbox7 st.b1.x0, sbox7 st.b1.x1, sbox7 st.b1.x2, sbox7 st.b1.x3⟩,
       ⟨sbox7 st.b2.x0, sbox7 st.b2.x1, sbox7 st.b2.x2, sbox7 st.b2.x3⟩⟩ := by rfl

theorem externalRound_eq (rc st : Poseidon2State12) :
    externalRound rc st = applyME (sboxState12 (state12Add st rc)) := by rfl

theorem internalRound_eq (rc : Goldilocks) (st : Poseidon2State12) :
    internalRound rc st =
      applyMI ⟨⟨sbox7 (Goldilocks.add st.b0.x0 rc), st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2⟩ := by rfl

theorem runRounds_nil {α σ : Type} (step : α → σ → σ) (s : σ) :
    runRounds step [] s = s := by rfl

theorem runRounds_cons {α σ : Type} (step : α → σ → σ) (c : α) (cs : List α) (s : σ) :
    runRounds step (c :: cs) s = runRounds step cs (step c s) := by rfl

def runRoundsInv {α σ : Type} (stepInv : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => stepInv c (runRoundsInv stepInv cs s)

private theorem runRoundsInv_runRounds {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, stepInv c (step c s) = s) (cs : List α) :
    ∀ (s : σ), runRoundsInv stepInv cs (runRounds step cs s) = s := by
  induction cs with
  | nil => intro s; rfl
  | cons c cs ih =>
    intro s
    simp only [runRounds, runRoundsInv, ih (step c s), hInv]

private theorem runRounds_runRoundsInv {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, step c (stepInv c s) = s) (cs : List α) :
    ∀ (s : σ), runRounds step cs (runRoundsInv stepInv cs s) = s := by
  induction cs with
  | nil => intro s; rfl
  | cons c cs ih =>
    intro s
    simp only [runRoundsInv, runRounds, hInv, ih s]

/-- **Full Width-12 `Poseidon2` Permutation (`poseidon2Perm12`, $R_F = 8, R_P = 22$)**. -/
@[expose] def poseidon2Perm12 (st : Poseidon2State12) : Poseidon2State12 :=
  let s0 := applyME st
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  runRounds externalRound poseidon2TerminalExtConsts s2

@[expose] def poseidon2Perm12Inv (st : Poseidon2State12) : Poseidon2State12 :=
  let s2 := runRoundsInv externalRoundInv poseidon2TerminalExtConsts st
  let s1 := runRoundsInv internalRoundInv poseidon2InternalConsts s2
  let s0 := runRoundsInv externalRoundInv poseidon2InitialExtConsts s1
  applyMEInv s0

theorem poseidon2Perm12Inv_left_inv (st : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 st) = st := by
  unfold poseidon2Perm12Inv poseidon2Perm12
  dsimp only
  rw [runRoundsInv_runRounds externalRound externalRoundInv externalRoundInv_externalRound,
      runRoundsInv_runRounds internalRound internalRoundInv internalRoundInv_internalRound,
      runRoundsInv_runRounds externalRound externalRoundInv externalRoundInv_externalRound,
      applyMEInv_applyME]

theorem poseidon2Perm12Inv_right_inv (st : Poseidon2State12) :
    poseidon2Perm12 (poseidon2Perm12Inv st) = st := by
  unfold poseidon2Perm12 poseidon2Perm12Inv
  dsimp only
  rw [applyME_applyMEInv,
      runRounds_runRoundsInv externalRound externalRoundInv externalRound_externalRoundInv,
      runRounds_runRoundsInv internalRound internalRoundInv internalRound_internalRoundInv,
      runRounds_runRoundsInv externalRound externalRoundInv externalRound_externalRoundInv]

/-- **Width-12 Goldilocks `Poseidon2` Permutation Bijection Theorem (`poseidon2Perm12_bijective`)**. -/
theorem poseidon2Perm12_bijective (s t : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 s) = s ∧
    poseidon2Perm12 (poseidon2Perm12Inv t) = t ∧
    (poseidon2Perm12 s = poseidon2Perm12 t ↔ s = t) ∧
    (∃ pre : Poseidon2State12, poseidon2Perm12 pre = t) := by
  refine ⟨poseidon2Perm12Inv_left_inv s, poseidon2Perm12Inv_right_inv t, ?_,
          ⟨poseidon2Perm12Inv t, poseidon2Perm12Inv_right_inv t⟩⟩
  constructor
  · intro h
    have hInv := congrArg poseidon2Perm12Inv h
    rwa [poseidon2Perm12Inv_left_inv, poseidon2Perm12Inv_left_inv] at hInv
  · intro h
    subst h
    rfl

/-! ## 4. Canonical `< 2^56` Limb Framing, Injective `10*1` Sponge Padding & `poseidon2Hash32` -/

private theorem pad7_length (bs : List UInt8) :
    ((bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7).length = 7 := by
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

def pack7BytesLimb (bs : List UInt8) : Goldilocks :=
  let chunk : List UInt8 := (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7
  have hLt256 : ofBE chunk < 256 ^ 7 := pad7_length bs ▸ ofBE_lt chunk
  have hLtP : ofBE chunk < goldilocksPrime :=
    Nat.lt_trans hLt256 (by decide +kernel)
  ⟨ofBE chunk, hLtP⟩

theorem pack7BytesLimb_lt_two_pow_56 (bs : List UInt8) :
    (pack7BytesLimb bs).val < 2 ^ 56 := by
  unfold pack7BytesLimb
  dsimp only
  let chunk : List UInt8 := (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7
  have hLt : ofBE chunk < 256 ^ 7 := pad7_length bs ▸ ofBE_lt chunk
  have hPow : (256 : Nat) ^ 7 = 2 ^ 56 := rfl
  exact hPow ▸ hLt

theorem be_foldl_acc :
    ∀ (bs : List UInt8) (w acc : Nat),
      be (w + bs.length) (bs.foldl (fun a b => a * 256 + b.toNat) acc) = be w acc ++ bs
  | [], w, acc => by simp
  | b :: rest, w, acc => by
    have hLen : w + (b :: rest).length = (w + 1) + rest.length := by simp; omega
    rw [List.foldl_cons, hLen, be_foldl_acc rest (w + 1) (acc * 256 + b.toNat)]
    have hb : b.toNat < 256 := b.toNat_lt
    have hDiv : (acc * 256 + b.toNat) / 256 = acc := by omega
    have hMod : UInt8.ofNat ((acc * 256 + b.toNat) % 256) = b := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8]; omega
    simp only [be, hDiv, hMod, List.append_assoc, List.singleton_append]

theorem be7_pack7BytesLimb_of_length_eq {bs : List UInt8} (hLen : bs.length = 7) :
    be 7 (pack7BytesLimb bs).val = bs := by
  unfold pack7BytesLimb
  dsimp only
  have hChunk : (bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7 = bs := by
    rw [hLen]
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    exact List.take_of_length_le (Nat.le_of_eq hLen)
  rw [hChunk, ← hLen]
  simpa [ofBE, be] using be_foldl_acc bs 0 0

def chunk7Exact : List UInt8 → List Goldilocks
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest =>
    pack7BytesLimb [b0, b1, b2, b3, b4, b5, b6] :: chunk7Exact rest
  | _ => []

def unchunk7Exact : List Goldilocks → List UInt8
  | [] => []
  | x :: xs => be 7 x.val ++ unchunk7Exact xs

private theorem unchunk7Exact_chunk7Exact :
    ∀ (bs : List UInt8), bs.length % 7 = 0 → unchunk7Exact (chunk7Exact bs) = bs
  | [], _ => rfl
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest, hMod => by
    have hRest : rest.length % 7 = 0 := by
      simp only [List.length_cons] at hMod
      omega
    simp only [chunk7Exact, unchunk7Exact,
      be7_pack7BytesLimb_of_length_eq (bs := [b0, b1, b2, b3, b4, b5, b6]) rfl,
      unchunk7Exact_chunk7Exact rest hRest]
    rfl
  | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h
  | [_, _, _, _, _], h | [_, _, _, _, _, _], h => by simp at h

private theorem chunk7Exact_lt_two_pow_56 :
    ∀ (bs : List UInt8) (x : Goldilocks), x ∈ chunk7Exact bs → x.val < 2 ^ 56
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest, x, hx => by
    simp only [chunk7Exact, List.mem_cons] at hx
    rcases hx with rfl | hmem
    · exact pack7BytesLimb_lt_two_pow_56 _
    · exact chunk7Exact_lt_two_pow_56 rest x hmem
  | [], _, hx => by cases hx
  | [_], _, hx | [_, _], _, hx | [_, _, _], _, hx | [_, _, _, _], _, hx
  | [_, _, _, _, _], _, hx | [_, _, _, _, _, _], _, hx => by simp [chunk7Exact] at hx

def bytesToLimbs56 (msg : List UInt8) : List Goldilocks :=
  let marked := msg ++ [(0x01 : UInt8)]
  let padLen := (7 - marked.length % 7) % 7
  chunk7Exact (marked ++ List.replicate padLen (0x00 : UInt8))

theorem bytesToLimbs56_lt_two_pow_56 (msg : List UInt8) (x : Goldilocks)
    (hx : x ∈ bytesToLimbs56 msg) : x.val < 2 ^ 56 :=
  chunk7Exact_lt_two_pow_56 _ x hx

private def stripLeadingZeroBytes : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if b == (0x00 : UInt8) then stripLeadingZeroBytes bs else b :: bs

private theorem stripLeadingZeroBytes_replicate (k : Nat) (b : UInt8) (rest : List UInt8)
    (hb : b ≠ 0x00) :
    stripLeadingZeroBytes (List.replicate k (0x00 : UInt8) ++ (b :: rest)) = b :: rest := by
  induction k with
  | zero =>
    have hne : (b == (0x00 : UInt8)) = false := beq_false_of_ne hb
    simp only [List.replicate_zero, List.nil_append, stripLeadingZeroBytes, hne, Bool.false_eq_true, ↓reduceIte]
  | succ k ih =>
    simpa only [List.replicate_succ, List.cons_append, stripLeadingZeroBytes,
      show ((0 : UInt8) == 0) = true from rfl, ↓reduceIte] using ih

def limbs56ToBytes (limbs : List Goldilocks) : List UInt8 :=
  match stripLeadingZeroBytes (unchunk7Exact limbs).reverse with
  | _ :: revMsg => revMsg.reverse
  | [] => []

theorem limbs56ToBytes_bytesToLimbs56 (msg : List UInt8) :
    limbs56ToBytes (bytesToLimbs56 msg) = msg := by
  unfold bytesToLimbs56 limbs56ToBytes
  let marked := msg ++ [(0x01 : UInt8)]
  let padLen := (7 - marked.length % 7) % 7
  have hMod : (marked ++ List.replicate padLen (0x00 : UInt8)).length % 7 = 0 := by
    simp only [List.length_append, List.length_replicate, padLen]
    omega
  rw [unchunk7Exact_chunk7Exact _ hMod]
  have hRev : (marked ++ List.replicate padLen (0x00 : UInt8)).reverse =
      List.replicate padLen (0x00 : UInt8) ++ ((0x01 : UInt8) :: msg.reverse) := by
    simp [marked, List.reverse_append, List.reverse_replicate]
  rw [hRev, stripLeadingZeroBytes_replicate padLen 0x01 msg.reverse (by decide +kernel)]
  exact List.reverse_reverse msg

theorem bytesToLimbs56_injective {m₁ m₂ : List UInt8}
    (h : bytesToLimbs56 m₁ = bytesToLimbs56 m₂) : m₁ = m₂ := by
  have hInv := congrArg limbs56ToBytes h
  rwa [limbs56ToBytes_bytesToLimbs56, limbs56ToBytes_bytesToLimbs56] at hInv

def padEndMarker : Goldilocks := ⟨2 ^ 56, by decide +kernel⟩
def padBothMarker : Goldilocks := ⟨2 ^ 56 + 1, by decide +kernel⟩

def pad101Suffix : Nat → List Goldilocks
  | 0 => [padBothMarker]
  | k + 1 => [Goldilocks.one] ++ List.replicate k Goldilocks.zero ++ [padEndMarker]

@[expose] def poseidon2Pad (xs : List Goldilocks) : List Goldilocks :=
  let z := (8 - (xs.length + 1) % 8) % 8
  xs ++ pad101Suffix z

theorem poseidon2Pad_length_mod (xs : List Goldilocks) :
    0 < (poseidon2Pad xs).length ∧ (poseidon2Pad xs).length % 8 = 0 := by
  unfold poseidon2Pad
  let z := (8 - (xs.length + 1) % 8) % 8
  have hSuffixLen : (pad101Suffix z).length = z + 1 := by
    cases z <;> simp [pad101Suffix]
  rw [List.length_append, hSuffixLen]
  refine ⟨by omega, ?_⟩
  dsimp only [z]
  omega

private def stripLeadingZeroLimbs : List Goldilocks → List Goldilocks
  | [] => []
  | x :: xs => if x == Goldilocks.zero then stripLeadingZeroLimbs xs else x :: xs

private theorem stripLeadingZeroLimbs_replicate (k : Nat) (rest : List Goldilocks) :
    stripLeadingZeroLimbs (List.replicate k Goldilocks.zero ++ (Goldilocks.one :: rest)) =
      Goldilocks.one :: rest := by
  induction k with
  | zero =>
    have hne : (Goldilocks.one == Goldilocks.zero) = false :=
      beq_eq_false_iff_ne.2 fun h => by
        have hv := congrArg Goldilocks.val h
        dsimp only [Goldilocks.one, Goldilocks.zero] at hv
        omega
    simp [stripLeadingZeroLimbs, hne]
  | succ k ih =>
    simp [List.replicate_succ, stripLeadingZeroLimbs, ih]

def poseidon2Unpad (ys : List Goldilocks) : List Goldilocks :=
  match ys.reverse with
  | last :: revInit =>
    if last == padBothMarker then
      revInit.reverse
    else
      match stripLeadingZeroLimbs revInit with
      | _ :: revMsg => revMsg.reverse
      | [] => []
  | [] => []

theorem poseidon2Unpad_poseidon2Pad (xs : List Goldilocks) :
    poseidon2Unpad (poseidon2Pad xs) = xs := by
  unfold poseidon2Pad poseidon2Unpad
  let z := (8 - (xs.length + 1) % 8) % 8
  change (match (xs ++ pad101Suffix z).reverse with
    | last :: revInit =>
      if last == padBothMarker then revInit.reverse
      else match stripLeadingZeroLimbs revInit with
      | _ :: revMsg => revMsg.reverse
      | [] => []
    | [] => []) = xs
  cases z with
  | zero =>
    have hRev : (xs ++ pad101Suffix 0).reverse = padBothMarker :: xs.reverse := by
      simp [pad101Suffix]
    rw [hRev]
    simp [List.reverse_reverse]
  | succ k =>
    have hRev : (xs ++ pad101Suffix (k + 1)).reverse =
        padEndMarker :: (List.replicate k Goldilocks.zero ++ (Goldilocks.one :: xs.reverse)) := by
      simp [pad101Suffix, List.reverse_append, List.reverse_replicate, List.append_assoc]
    have hNe : (padEndMarker == padBothMarker) = false :=
      beq_eq_false_iff_ne.2 fun h => by
        have hv := congrArg Goldilocks.val h
        dsimp only [padEndMarker, padBothMarker] at hv
        omega
    rw [hRev]
    simp [hNe, stripLeadingZeroLimbs_replicate, List.reverse_reverse]

theorem poseidon2Pad_injective {xs ys : List Goldilocks}
    (h : poseidon2Pad xs = poseidon2Pad ys) : xs = ys := by
  have hInv := congrArg poseidon2Unpad h
  rwa [poseidon2Unpad_poseidon2Pad, poseidon2Unpad_poseidon2Pad] at hInv

def poseidon2PadBytes (msg : List UInt8) : List Goldilocks :=
  poseidon2Pad (bytesToLimbs56 msg)

theorem poseidon2PadBytes_injective {m₁ m₂ : List UInt8}
    (h : poseidon2PadBytes m₁ = poseidon2PadBytes m₂) : m₁ = m₂ :=
  bytesToLimbs56_injective (poseidon2Pad_injective h)

def poseidon2InitState : Poseidon2State12 :=
  ⟨lane4Zero,
   lane4Zero,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 4,
    Goldilocks.ofNat 32, Goldilocks.ofNat 0x504F53325F474C31⟩⟩

def absorbRate8Block (st : Poseidon2State12) (r0 r1 : Lane4) : Poseidon2State12 :=
  poseidon2Perm12 ⟨lane4Add st.b0 r0, lane4Add st.b1 r1, st.b2⟩

def absorbLimbStream (st : Poseidon2State12) : List Goldilocks → Poseidon2State12
  | m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: rest =>
    let st' := absorbRate8Block st ⟨m0, m1, m2, m3⟩ ⟨m4, m5, m6, m7⟩
    absorbLimbStream st' rest
  | _ => st

def squeeze32Bytes (st : Poseidon2State12) : List UInt8 :=
  be 8 st.b0.x0.val ++ be 8 st.b0.x1.val ++ be 8 st.b0.x2.val ++ be 8 st.b0.x3.val

theorem squeeze32Bytes_b0_injective {s₁ s₂ : Poseidon2State12}
    (h : squeeze32Bytes s₁ = squeeze32Bytes s₂) : s₁.b0 = s₂.b0 := by
  unfold squeeze32Bytes at h
  simp only [List.append_assoc] at h
  obtain ⟨hx0, hrest1⟩ := List.append_inj h (by simp)
  obtain ⟨hx1, hrest2⟩ := List.append_inj hrest1 (by simp)
  obtain ⟨hx2, hx3⟩ := List.append_inj hrest2 (by simp)
  have hPow : (2 : Nat) ^ 64 = 256 ^ 8 := rfl
  exact Lane4.ext
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx0))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx1))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx2))
    (Goldilocks.ext (be_injective (hPow ▸ Goldilocks.val_lt_two_pow_64 _) (hPow ▸ Goldilocks.val_lt_two_pow_64 _) hx3))

/-- **256-Bit Algebraic Goldilocks `Poseidon2` Sponge Hash (`poseidon2Hash32`)**. -/
@[expose] def poseidon2Hash32 : Hash := fun msg =>
  let finalSt := absorbLimbStream poseidon2InitState (poseidon2PadBytes msg)
  squeeze32Bytes finalSt

theorem poseidon2Hash32_length (msg : List UInt8) :
    (poseidon2Hash32 msg).length = 32 := by
  unfold poseidon2Hash32 squeeze32Bytes
  simp [length_be]

/-- Weighted Jive input contribution, binding both rate blocks and the complete tweak. -/
def poseidon2WeightedFeedForward (s : Poseidon2State12) : Lane4 :=
  lane4Add (lane4Add s.b0 (lane4Scale (Goldilocks.ofNat 2) s.b1))
    (lane4Scale (Goldilocks.ofNat 4) s.b2)

def poseidon2CompressWeighted (s : Poseidon2State12) : Lane4 :=
  lane4Add (poseidon2Perm12 s).b0 (poseidon2WeightedFeedForward s)

theorem poseidon2WeightedFeedForward_eq (s : Poseidon2State12) :
    poseidon2WeightedFeedForward s =
      lane4Add (lane4Add s.b0 (lane4Scale (Goldilocks.ofNat 2) s.b1))
        (lane4Scale (Goldilocks.ofNat 4) s.b2) := by rfl

theorem poseidon2CompressWeighted_eq (s : Poseidon2State12) :
    poseidon2CompressWeighted s =
      lane4Add (poseidon2Perm12 s).b0 (poseidon2WeightedFeedForward s) := by rfl

end Qsag
end

public section
namespace Qsag
open RoundPoly
/-! ## 1. Power Maps on `Goldilocks`: Fermat, Exponent Inverses, and Minimality of `d = 7` -/

private theorem gold_ne_of_val_ne {a b : Goldilocks} (h : a.val ≠ b.val) : a ≠ b :=
  fun e => h (congrArg Goldilocks.val e)

private theorem gold_not_dvd_val {a : Goldilocks} (h0 : a.val ≠ 0) :
    ¬ (goldilocksPrime ∣ a.val) := fun hd => by
  have hle := Nat.le_of_dvd (by omega) hd
  have hlt := a.isLt
  omega

/-- **Fermat's little theorem on the `Goldilocks` carrier**: `a ^ (p - 1) = 1` for `a ≠ 0`. -/
theorem goldilocksPow_fermat {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    goldilocksPow a (goldilocksPrime - 1) = Goldilocks.one := by
  apply Goldilocks.ext
  rw [goldilocksPow_val]
  exact (goldilocksPrime_isPrime ()).pow_sub_one_mod
    (gold_not_dvd_val (fun h => ha (Goldilocks.ext h)))

private theorem pow_cycle_mod (a : Goldilocks) (k : Nat) :
    (a.val ^ (k * (goldilocksPrime - 1) + 1)) % goldilocksPrime = a.val := by
  if h0 : a.val = 0 then
    rw [h0, Nat.zero_pow (Nat.succ_pos _), Nat.zero_mod]
  else
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod (gold_not_dvd_val h0)
    have h1 : ((a.val ^ (goldilocksPrime - 1)) ^ k) % goldilocksPrime = 1 := by
      rw [Nat.pow_mod, hflt, Nat.one_pow]
      decide +kernel
    rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm k, Nat.pow_mul, Nat.mul_mod, h1,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

/-- **Exponent-inverse law**: if `d * e ≡ 1 (mod p - 1)` then `x ↦ x ^ e` undoes `x ↦ x ^ d` on
    all of `Goldilocks`, including `0`. -/
theorem goldilocksPow_pow_of_exponent_inverse (x : Goldilocks) (d e k : Nat)
    (h : d * e = k * (goldilocksPrime - 1) + 1) :
    goldilocksPow (goldilocksPow x d) e = x := by
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val, ← Nat.pow_mod, ← Nat.pow_mul, h]
  exact pow_cycle_mod x k

/-- A power map with an exponent inverse modulo `p - 1` is injective. -/
theorem goldilocksPow_injective_of_exponent_inverse (d e k : Nat)
    (h : d * e = k * (goldilocksPrime - 1) + 1) (x y : Goldilocks) :
    goldilocksPow x d = goldilocksPow y d ↔ x = y := by
  constructor
  · intro hxy
    have hx := goldilocksPow_pow_of_exponent_inverse x d e k h
    have hy := goldilocksPow_pow_of_exponent_inverse y d e k h
    rw [hxy] at hx
    exact hx.symm.trans hy
  · intro hxy
    rw [hxy]

theorem poseidon2DInv_exponent_inverse :
    7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 := by decide +kernel

theorem goldilocksPow_seven_eq_sbox7 (x : Goldilocks) : goldilocksPow x 7 = sbox7 x := by
  apply Goldilocks.ext
  rw [goldilocksPow_val, sbox7_val]

/-- `(x ^ 7) ^ d_inv = x` for every `x : Goldilocks`. -/
theorem sbox7_dInv_roundtrip (x : Goldilocks) :
    goldilocksPow (sbox7 x) poseidon2DInv = x := by
  rw [← goldilocksPow_seven_eq_sbox7]
  exact goldilocksPow_pow_of_exponent_inverse x 7 poseidon2DInv 4 poseidon2DInv_exponent_inverse

/-- `x ^ 7 = y ^ 7 ↔ x = y` on `Goldilocks`. -/
theorem goldilocksPow_seven_injective (x y : Goldilocks) :
    goldilocksPow x 7 = goldilocksPow y 7 ↔ x = y :=
  goldilocksPow_injective_of_exponent_inverse 7 poseidon2DInv 4 poseidon2DInv_exponent_inverse x y

/-- Primitive cube root of unity `7 ^ ((p - 1) / 3)`. -/
def goldilocksOmega3 : Goldilocks := ⟨18446744065119617025, by decide +kernel⟩

/-- Primitive fifth root of unity `7 ^ ((p - 1) / 5)`. -/
def goldilocksOmega5 : Goldilocks := ⟨1373043270956696022, by decide +kernel⟩

/-- `-1` in `Goldilocks`. -/
def goldilocksNegOne : Goldilocks := ⟨18446744069414584320, by decide +kernel⟩

private theorem pow_collision_with_one (w : Goldilocks) (d : Nat)
    (hne : w.val ≠ 1) (hpow : w.val ^ d % goldilocksPrime = 1 ^ d % goldilocksPrime) :
    ∃ x y : Goldilocks, x ≠ y ∧ goldilocksPow x d = goldilocksPow y d :=
  ⟨w, Goldilocks.one, gold_ne_of_val_ne hne, by
    apply Goldilocks.ext
    rw [goldilocksPow_val, goldilocksPow_val]
    exact hpow⟩

/-- **`d = 7` is the least exponent `d ≥ 2` whose power map permutes `Goldilocks`**: every
    `2 ≤ d < 7` has a collision (`-1` for even `d`, `ω₃` for `d = 3`, `ω₅` for `d = 5`), while
    `goldilocksPow_seven_injective` holds for `d = 7`. -/
theorem sbox7_is_minimal_nontrivial_power_permutation (d : Nat) (h2 : 2 ≤ d) (h7 : d < 7) :
    ∃ x y : Goldilocks, x ≠ y ∧ goldilocksPow x d = goldilocksPow y d := by
  have hd : d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 := by omega
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact pow_collision_with_one goldilocksNegOne 2 (by decide +kernel) (by decide +kernel)
  · exact pow_collision_with_one goldilocksOmega3 3 (by decide +kernel) (by decide +kernel)
  · exact pow_collision_with_one goldilocksNegOne 4 (by decide +kernel) (by decide +kernel)
  · exact pow_collision_with_one goldilocksOmega5 5 (by decide +kernel) (by decide +kernel)
  · exact pow_collision_with_one goldilocksNegOne 6 (by decide +kernel) (by decide +kernel)


/-! ## 2. Width-16 External Layer `M_E = circ(2 M_4, M_4, M_4, M_4)` -/

private theorem ofNat_eq_goldOfInt16 (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

/-- `applyM4` is multiplication by the circulant matrix `circ(2, 3, 1, 1)`. -/
theorem applyM4_eq_circ_2_3_1_1 (b : Lane4) :
    applyM4 b =
      ⟨Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x0)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x1)) (Goldilocks.add b.x2 b.x3),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x1)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x2)) (Goldilocks.add b.x3 b.x0),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x2)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x3)) (Goldilocks.add b.x0 b.x1),
       Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 2) b.x3)
          (Goldilocks.mul (Goldilocks.ofNat 3) b.x0)) (Goldilocks.add b.x1 b.x2)⟩ := by
  unfold applyM4 lane4Sum
  apply Lane4.ext <;>
    (dsimp only
     rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3]
     simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_mul]
     congr 1
     omega)

/-- Width-16 Poseidon2 state as four `Lane4` blocks. -/
structure Poseidon2State16 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  b3 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State16.ext {s t : Poseidon2State16}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2) (h3 : s.b3 = t.b3) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2 h3; rfl

def state16Zero : Poseidon2State16 := ⟨lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩

private def inv5Gold : Goldilocks := ⟨14757395255531667457, by decide +kernel⟩

/-- Width-16 external layer: block `i` of the output is `M_4 b_i + Σ_j M_4 b_j`. -/
def applyME16 (st : Poseidon2State16) : Poseidon2State16 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let y3 := applyM4 st.b3
  let s := lane4Add (lane4Add (lane4Add y0 y1) y2) y3
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s, lane4Add y3 s⟩

/-- Explicit inverse of `applyME16`: the block sum is recovered as `5⁻¹ · Σ_i y_i`. -/
def applyME16Inv (st : Poseidon2State16) : Poseidon2State16 :=
  let s := lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3)
  ⟨applyM4Inv (lane4Sub st.b0 s), applyM4Inv (lane4Sub st.b1 s),
   applyM4Inv (lane4Sub st.b2 s), applyM4Inv (lane4Sub st.b3 s)⟩

private theorem gold_mul_cancel_of_prod_one {u k : Goldilocks}
    (h : Goldilocks.mul u k = Goldilocks.one) (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv5Gold_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv5Gold (Goldilocks.mul (Goldilocks.ofNat 5) x) = x :=
  gold_mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem mul_inv5Gold_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 5) (Goldilocks.mul inv5Gold x) = x :=
  gold_mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem scalar_sum_five_cancel (a b c d : Goldilocks) :
    Goldilocks.mul inv5Gold (Goldilocks.add (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add d (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))) =
      Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d := by
  have h : Goldilocks.add (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)))
      (Goldilocks.add d (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)) =
      Goldilocks.mul (Goldilocks.ofNat 5)
        (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c, ← goldOfInt_nat d]
    simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [h, inv5Gold_mul_cancel]

private theorem lane4_sum_five_cancel (y0 y1 y2 y3 : Lane4) :
    lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add
      (lane4Add y0 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3))
      (lane4Add y1 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3)))
      (lane4Add y2 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3)))
      (lane4Add y3 (lane4Add (lane4Add (lane4Add y0 y1) y2) y3))) =
    lane4Add (lane4Add (lane4Add y0 y1) y2) y3 := by
  unfold lane4Scale lane4Add
  exact Lane4.ext
    (scalar_sum_five_cancel y0.x0 y1.x0 y2.x0 y3.x0)
    (scalar_sum_five_cancel y0.x1 y1.x1 y2.x1 y3.x1)
    (scalar_sum_five_cancel y0.x2 y1.x2 y2.x2 y3.x2)
    (scalar_sum_five_cancel y0.x3 y1.x3 y2.x3 y3.x3)

private theorem lane4Sub_add_cancel (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyME16Inv_applyME16 (st : Poseidon2State16) : applyME16Inv (applyME16 st) = st := by
  unfold applyME16Inv applyME16
  dsimp only
  rw [lane4_sum_five_cancel]
  rw [lane4Sub_add_cancel, lane4Sub_add_cancel, lane4Sub_add_cancel, lane4Sub_add_cancel]
  rw [applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4]

private theorem scalar_block_recover (y a b c d s : Goldilocks)
    (h : Goldilocks.mul (Goldilocks.ofNat 5) s =
      Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d) :
    Goldilocks.add (Goldilocks.sub y s)
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.sub a s) (Goldilocks.sub b s))
        (Goldilocks.sub c s)) (Goldilocks.sub d s)) = y := by
  have e : Goldilocks.add (Goldilocks.sub y s)
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.sub a s) (Goldilocks.sub b s))
        (Goldilocks.sub c s)) (Goldilocks.sub d s)) =
      Goldilocks.add y (Goldilocks.sub (Goldilocks.add (Goldilocks.add (Goldilocks.add a b) c) d)
        (Goldilocks.mul (Goldilocks.ofNat 5) s)) := by
    rw [← goldOfInt_nat y, ← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c,
        ← goldOfInt_nat d, ← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt16, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    omega
  rw [e, h]
  change CommRingOps.add y (CommRingOps.sub _ _) = y
  rw [LawfulCommRing.sub_self, LawfulCommRing.add_zero]

private theorem lane4_block_recover (y a b c d s : Lane4)
    (h : lane4Scale (Goldilocks.ofNat 5) s = lane4Add (lane4Add (lane4Add a b) c) d) :
    lane4Add (lane4Sub y s)
      (lane4Add (lane4Add (lane4Add (lane4Sub a s) (lane4Sub b s)) (lane4Sub c s))
        (lane4Sub d s)) = y := by
  have h0 := congrArg Lane4.x0 h
  have h1 := congrArg Lane4.x1 h
  have h2 := congrArg Lane4.x2 h
  have h3 := congrArg Lane4.x3 h
  unfold lane4Scale lane4Add at h0 h1 h2 h3
  unfold lane4Add lane4Sub
  exact Lane4.ext
    (scalar_block_recover y.x0 a.x0 b.x0 c.x0 d.x0 s.x0 h0)
    (scalar_block_recover y.x1 a.x1 b.x1 c.x1 d.x1 s.x1 h1)
    (scalar_block_recover y.x2 a.x2 b.x2 c.x2 d.x2 s.x2 h2)
    (scalar_block_recover y.x3 a.x3 b.x3 c.x3 d.x3 s.x3 h3)

theorem applyME16_applyME16Inv (st : Poseidon2State16) : applyME16 (applyME16Inv st) = st := by
  have h5 : lane4Scale (Goldilocks.ofNat 5)
      (lane4Scale inv5Gold (lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3)) =
      lane4Add (lane4Add (lane4Add st.b0 st.b1) st.b2) st.b3 := by
    unfold lane4Scale
    exact Lane4.ext (mul_inv5Gold_cancel _) (mul_inv5Gold_cancel _)
      (mul_inv5Gold_cancel _) (mul_inv5Gold_cancel _)
  unfold applyME16 applyME16Inv
  dsimp only
  rw [applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv]
  exact Poseidon2State16.ext
    (lane4_block_recover st.b0 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b1 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b2 st.b0 st.b1 st.b2 st.b3 _ h5)
    (lane4_block_recover st.b3 st.b0 st.b1 st.b2 st.b3 _ h5)

theorem applyME16_injective {s t : Poseidon2State16} (h : applyME16 s = applyME16 t) : s = t := by
  have hInv := congrArg applyME16Inv h
  rwa [applyME16Inv_applyME16, applyME16Inv_applyME16] at hInv

theorem applyME16Inv_zero : applyME16Inv state16Zero = state16Zero := by decide +kernel

/-- **Non-singular width-16 external layer**: two-sided inverse, surjectivity, and no non-zero
    state in the kernel. -/
theorem applyME16_nonsingular (s y : Poseidon2State16) :
    applyME16Inv (applyME16 s) = s ∧
    applyME16 (applyME16Inv y) = y ∧
    (∃ z : Poseidon2State16, applyME16 z = y) ∧
    (s ≠ state16Zero → applyME16 s ≠ state16Zero) := by
  refine ⟨applyME16Inv_applyME16 s, applyME16_applyME16Inv y,
    ⟨applyME16Inv y, applyME16_applyME16Inv y⟩, ?_⟩
  intro hne hz
  apply hne
  have hInv := congrArg applyME16Inv hz
  rwa [applyME16Inv_applyME16, applyME16Inv_zero] at hInv


/-! ## 3. Round-Count Arithmetic for `d = 7`, `R_F = 8`, `R_P = 22` -/

/-- The deployed permutation runs `4 + 4` external and `22` internal rounds. -/
theorem poseidon2_deployed_round_counts :
    poseidon2InitialExtConsts.length + poseidon2TerminalExtConsts.length = 8 ∧
    poseidon2InternalConsts.length = 22 := by
  simp [poseidon2InitialExtConsts, poseidon2TerminalExtConsts, poseidon2InternalConsts]

/-- **Nominal degree threshold**: `7 ^ r` stays below `p` for every `r ≤ 22` and reaches `p` at
    `r = 23`, seven rounds before the `30`-round total. -/
theorem poseidon2_nominal_degree_threshold :
    (∀ r : Nat, r ≤ 22 → 7 ^ r < goldilocksPrime) ∧
    goldilocksPrime ≤ 7 ^ 23 ∧ 23 + 7 = 8 + 22 ∧
    goldilocksPrime < 2 ^ 84 ∧ 2 ^ 84 < 7 ^ (8 + 22) := by
  refine ⟨fun r hr => ?_, by decide +kernel, rfl, by decide +kernel, by decide +kernel⟩
  exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide +kernel) hr) (by decide +kernel)

/-- Interpolation round inequality `1 + a + b ≤ R_F + R_P` with `7 ^ a ≥ 2 ^ 64`
    (`a ≥ ⌈64 log_7 2⌉`) and `7 ^ b ≥ t` (`b ≥ ⌈log_7 t⌉`), together with the statistical floor
    `R_F ≥ 6`. -/
def Poseidon2InterpolationMargin (t rF rP : Nat) : Prop :=
  6 ≤ rF ∧ ∃ a b : Nat, 2 ^ 64 ≤ 7 ^ a ∧ t ≤ 7 ^ b ∧ 1 + a + b ≤ rF + rP

theorem poseidon2_interpolation_margin_width12 : Poseidon2InterpolationMargin 12 8 22 :=
  ⟨by decide +kernel, 23, 2, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem poseidon2_interpolation_margin_width16 : Poseidon2InterpolationMargin 16 8 22 :=
  ⟨by decide +kernel, 23, 2, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Any witness of the margin needs `26` rounds once `t > 7`: the slack at `8 + 22` is `4`. -/
theorem poseidon2_interpolation_margin_needs_26 (t rF rP : Nat) (ht : 7 < t)
    (h : Poseidon2InterpolationMargin t rF rP) : 26 ≤ rF + rP := by
  obtain ⟨_, a, b, ha, hb, hsum⟩ := h
  have ha' : 23 ≤ a := Nat.le_of_not_lt (fun hlt =>
    Nat.not_lt.mpr ha (Nat.lt_of_le_of_lt
      (Nat.pow_le_pow_right (by decide +kernel) (Nat.le_of_lt_succ hlt)) (by decide +kernel)))
  have hb' : 2 ≤ b := Nat.le_of_not_lt (fun hlt => by
    have h7 : 7 ^ b ≤ 7 ^ 1 := Nat.pow_le_pow_right (by decide +kernel) (Nat.le_of_lt_succ hlt)
    omega)
  omega

/-- **Sample lower bound for univariate interpolation over `Goldilocks`**: for any sample set `S`
    and any point `x₀` outside it there is a polynomial with `|S| + 1` coefficients that vanishes
    on all of `S` and not at `x₀`. Adding it to a target changes the target off `S` only, so `|S|`
    evaluations do not determine a polynomial whose degree is at least `|S|`. -/
theorem univariate_interpolation_underdetermined (S : List Goldilocks) (x₀ : Goldilocks)
    (hx₀ : x₀ ∉ S) :
    ∃ cs : List Goldilocks, cs.length = S.length + 1 ∧
      (∀ s ∈ S, evalCoeffs cs s = Goldilocks.zero) ∧
      evalCoeffs cs x₀ ≠ Goldilocks.zero :=
  ⟨vanishingCoeffs S, vanishingCoeffs_length S,
    fun s hs => evalCoeffs_vanishingCoeffs_of_mem S s hs,
    evalCoeffs_vanishingCoeffs_ne_zero (R := Goldilocks) (gold_ne_of_val_ne (by decide +kernel)) S x₀ hx₀⟩


/-! ## 5. Deployed width-12 inverses and exact four-lane diffusion -/

/-- The deployed external linear layer, on the actual three-block state. -/
abbrev poseidon2ExternalLinear12 := applyME

/-- The deployed internal linear layer, including its nonuniform diagonal. -/
abbrev poseidon2InternalLinear12 := applyMI

theorem poseidon2ExternalLinear12_two_sided_inverse (x : Poseidon2State12) :
    applyMEInv (poseidon2ExternalLinear12 x) = x ∧
    poseidon2ExternalLinear12 (applyMEInv x) = x :=
  ⟨applyMEInv_applyME x, applyME_applyMEInv x⟩

theorem poseidon2InternalLinear12_two_sided_inverse (x : Poseidon2State12) :
    applyMIInv (poseidon2InternalLinear12 x) = x ∧
    poseidon2InternalLinear12 (applyMIInv x) = x :=
  ⟨applyMIInv_applyMI x, applyMI_applyMIInv x⟩

theorem poseidon2_full_round_two_sided_inverse (rc x : Poseidon2State12) :
    externalRoundInv rc (externalRound rc x) = x ∧
    externalRound rc (externalRoundInv rc x) = x :=
  ⟨externalRoundInv_externalRound rc x, externalRound_externalRoundInv rc x⟩

theorem poseidon2_partial_round_two_sided_inverse (rc : Goldilocks) (x : Poseidon2State12) :
    internalRoundInv rc (internalRound rc x) = x ∧
    internalRound rc (internalRoundInv rc x) = x :=
  ⟨internalRoundInv_internalRound rc x, internalRound_internalRoundInv rc x⟩

theorem poseidon2_deployed_permutation_injective (x y : Poseidon2State12) :
    poseidon2Perm12 x = poseidon2Perm12 y ↔ x = y :=
  (poseidon2Perm12_bijective x y).2.2.1

/-- Number of nonzero coordinates; this counts field elements, not bits. -/
def laneWeight4 (x : Lane4) : Nat :=
  (if x.x0 = Goldilocks.zero then 0 else 1) +
  (if x.x1 = Goldilocks.zero then 0 else 1) +
  (if x.x2 = Goldilocks.zero then 0 else 1) +
  (if x.x3 = Goldilocks.zero then 0 else 1)

private theorem minor_scalar_cancel (d : Int) (hd : goldOfInt d ≠ Goldilocks.zero)
    (x : Goldilocks) (h : Goldilocks.mul (goldOfInt d) x = Goldilocks.zero) :
    x = Goldilocks.zero := by
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  · exact False.elim (hd h)
  · exact h

/-- Cofactor certificates below cover every equally sized set of input columns and output rows.
    Each certificate recovers one supported input coordinate from the selected zero outputs.
    The determinants are small nonzero integers, hence units in the Goldilocks field. -/
private theorem m4_minor_0_0 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy0] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_0_1 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy1] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_0_2 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy2] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_0_3 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hx3, hy3] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_1_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy0] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_1_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy1] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_1_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy2] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_1_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hx3, hy3] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_2_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy0] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_2_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy1] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_2_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy2] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_2_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx3, hy3] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_3_0 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy0] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x3
  exact he.trans (by decide +kernel)

private theorem m4_minor_3_1 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (-3)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy1] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x3
  exact he.trans (by decide +kernel)

private theorem m4_minor_3_2 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy2] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x3
  exact he.trans (by decide +kernel)

private theorem m4_minor_3_3 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x3 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x3) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hx2, hy3] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x3
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_01 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) x.x2)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_02 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) x.x2)) (Goldilocks.mul (goldOfInt (8)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_03 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-7)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (2)) x.x2)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (-7) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_12 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) x.x2)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_13 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-5) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_01_23 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) (Goldilocks.mul (goldOfInt (-1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-2) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_01 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-7)) x.x1)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_02 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_03 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-2)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_12 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (7)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_13 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-8)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-8) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_02_23 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-5) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_01 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) (Goldilocks.mul (goldOfInt (2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_02 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-8)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy2] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_03 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy0, hy3] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_12 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) (Goldilocks.mul (goldOfInt (-7)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy1, hy2] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_13 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) (Goldilocks.mul (goldOfInt (-5)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy1, hy3] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_03_23 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-7)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x1)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hx2, hy2, hy3] at he
  apply minor_scalar_cancel (-7) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (7)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-2)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy1] at he
  apply minor_scalar_cancel (7) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-3)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy2] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (2)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy0, hy3] at he
  apply minor_scalar_cancel (2) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (7)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy1, hy2] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (8)) x.x0)) (Goldilocks.mul (goldOfInt (5)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy1, hy3] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_12_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (5)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx3, hy2, hy3] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (2)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy1] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (8)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy2] at he
  apply minor_scalar_cancel (8) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy0, hy3] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-7)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy1, hy2] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy1, hy3] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_13_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-1)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (7)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx2, hy2, hy3] at he
  apply minor_scalar_cancel (-1) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_01 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-2)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-1)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy1] at he
  apply minor_scalar_cancel (-2) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_02 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-5)) x.x0)) (Goldilocks.mul (goldOfInt (-8)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy2] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_03 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-1)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy0, hy3] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_12 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (7)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-2)) x.x0)) (Goldilocks.mul (goldOfInt (-5)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy1, hy2] at he
  apply minor_scalar_cancel (7) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_13 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (5)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (1)) x.x0)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy1, hy3] at he
  apply minor_scalar_cancel (5) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_23_23 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x2 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (1)) x.x2) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (2)) (applyM4 x).x2) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (7)) x.x0)) (Goldilocks.mul (goldOfInt (1)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hx1, hy2, hy3] at he
  apply minor_scalar_cancel (1) (by decide +kernel) x.x2
  exact he.trans (by decide +kernel)

private theorem m4_minor_012_012 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (4) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_012_013 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-11)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (17) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_012_023 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (11) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_012_123 (x : Lane4)
    (hx3 : x.x3 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx3, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_013_012 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-8)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (17)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_013_013 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (3)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (11)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (4) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_013_023 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (8)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (3)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (17) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_013_123 (x : Lane4)
    (hx2 : x.x2 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (4)) x.x2)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx2, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (11) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_023_012 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (11) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_023_013 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-11)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_023_023 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (4) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_023_123 (x : Lane4)
    (hx1 : x.x1 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x1)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx1, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (17) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

private theorem m4_minor_123_012 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (17)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-11)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy1, hy2] at he
  apply minor_scalar_cancel (17) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_123_013 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (11)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (5)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (-2)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-3)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy1, hy3] at he
  apply minor_scalar_cancel (11) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_123_023 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (3)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-1)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-4)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy0, hy2, hy3] at he
  apply minor_scalar_cancel (3) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_123_123 (x : Lane4)
    (hx0 : x.x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x1 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (4)) x.x1) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (1)) (applyM4 x).x1) (Goldilocks.mul (goldOfInt (-5)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (7)) (applyM4 x).x3)) (Goldilocks.mul (goldOfInt (-17)) x.x0)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hx0, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (4) (by decide +kernel) x.x1
  exact he.trans (by decide +kernel)

private theorem m4_minor_0123_0123 (x : Lane4)
    (hy0 : (applyM4 x).x0 = Goldilocks.zero)
    (hy1 : (applyM4 x).x1 = Goldilocks.zero)
    (hy2 : (applyM4 x).x2 = Goldilocks.zero)
    (hy3 : (applyM4 x).x3 = Goldilocks.zero)
    : x.x0 = Goldilocks.zero := by
  have he : (Goldilocks.mul (goldOfInt (-35)) x.x0) =
      (Goldilocks.add (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (4)) (applyM4 x).x0) (Goldilocks.mul (goldOfInt (-3)) (applyM4 x).x1)) (Goldilocks.mul (goldOfInt (11)) (applyM4 x).x2)) (Goldilocks.mul (goldOfInt (-17)) (applyM4 x).x3)) := by
    unfold applyM4 lane4Sum
    dsimp only
    rw [← goldOfInt_nat x.x0, ← goldOfInt_nat x.x1,
      ← goldOfInt_nat x.x2, ← goldOfInt_nat x.x3]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1
    omega
  rw [hy0, hy1, hy2, hy3] at he
  apply minor_scalar_cancel (-35) (by decide +kernel) x.x0
  exact he.trans (by decide +kernel)

/-- Any nonzero input has input/output support sum at least five. -/
theorem m4_mds_branch_lower (x : Lane4) (hne : x ≠ lane4Zero) :
    5 ≤ laneWeight4 x + laneWeight4 (applyM4 x) := by
  by_cases hx0 : x.x0 = Goldilocks.zero <;>
    by_cases hx1 : x.x1 = Goldilocks.zero <;>
    by_cases hx2 : x.x2 = Goldilocks.zero <;>
    by_cases hx3 : x.x3 = Goldilocks.zero
  · exact False.elim (hne (Lane4.ext hx0 hx1 hx2 hx3))
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_0 x hx0 hx1 hx2 hy0))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_1 x hx0 hx1 hx2 hy1))
    · exact False.elim (hx3 (m4_minor_3_2 x hx0 hx1 hx2 hy2))
    · exact False.elim (hx3 (m4_minor_3_2 x hx0 hx1 hx2 hy2))
    · exact False.elim (hx3 (m4_minor_3_3 x hx0 hx1 hx2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_0 x hx0 hx1 hx3 hy0))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_1 x hx0 hx1 hx3 hy1))
    · exact False.elim (hx2 (m4_minor_2_2 x hx0 hx1 hx3 hy2))
    · exact False.elim (hx2 (m4_minor_2_2 x hx0 hx1 hx3 hy2))
    · exact False.elim (hx2 (m4_minor_2_3 x hx0 hx1 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_01 x hx0 hx1 hy0 hy1))
    · exact False.elim (hx2 (m4_minor_23_02 x hx0 hx1 hy0 hy2))
    · exact False.elim (hx2 (m4_minor_23_02 x hx0 hx1 hy0 hy2))
    · exact False.elim (hx2 (m4_minor_23_03 x hx0 hx1 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx2 (m4_minor_23_12 x hx0 hx1 hy1 hy2))
    · exact False.elim (hx2 (m4_minor_23_12 x hx0 hx1 hy1 hy2))
    · exact False.elim (hx2 (m4_minor_23_13 x hx0 hx1 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx2 (m4_minor_23_23 x hx0 hx1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_0 x hx0 hx2 hx3 hy0))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_1 x hx0 hx2 hx3 hy1))
    · exact False.elim (hx1 (m4_minor_1_2 x hx0 hx2 hx3 hy2))
    · exact False.elim (hx1 (m4_minor_1_2 x hx0 hx2 hx3 hy2))
    · exact False.elim (hx1 (m4_minor_1_3 x hx0 hx2 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_01 x hx0 hx2 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_13_02 x hx0 hx2 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_13_02 x hx0 hx2 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_13_03 x hx0 hx2 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_13_12 x hx0 hx2 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_13_12 x hx0 hx2 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_13_13 x hx0 hx2 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_13_23 x hx0 hx2 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_01 x hx0 hx3 hy0 hy1))
    · exact False.elim (hx1 (m4_minor_12_02 x hx0 hx3 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_12_02 x hx0 hx3 hy0 hy2))
    · exact False.elim (hx1 (m4_minor_12_03 x hx0 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_12_12 x hx0 hx3 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_12_12 x hx0 hx3 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_12_13 x hx0 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_12_23 x hx0 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx1 (m4_minor_123_012 x hx0 hy0 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_123_012 x hx0 hy0 hy1 hy2))
    · exact False.elim (hx1 (m4_minor_123_013 x hx0 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_123_023 x hx0 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx1 (m4_minor_123_123 x hx0 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_0 x hx1 hx2 hx3 hy0))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_1 x hx1 hx2 hx3 hy1))
    · exact False.elim (hx0 (m4_minor_0_2 x hx1 hx2 hx3 hy2))
    · exact False.elim (hx0 (m4_minor_0_2 x hx1 hx2 hx3 hy2))
    · exact False.elim (hx0 (m4_minor_0_3 x hx1 hx2 hx3 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_01 x hx1 hx2 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_03_02 x hx1 hx2 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_03_02 x hx1 hx2 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_03_03 x hx1 hx2 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_03_12 x hx1 hx2 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_03_12 x hx1 hx2 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_03_13 x hx1 hx2 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_03_23 x hx1 hx2 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_01 x hx1 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_02_02 x hx1 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_02_02 x hx1 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_02_03 x hx1 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_02_12 x hx1 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_02_12 x hx1 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_02_13 x hx1 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_02_23 x hx1 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_023_012 x hx1 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_023_012 x hx1 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_023_013 x hx1 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_023_023 x hx1 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_023_123 x hx1 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_01 x hx2 hx3 hy0 hy1))
    · exact False.elim (hx0 (m4_minor_01_02 x hx2 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_01_02 x hx2 hx3 hy0 hy2))
    · exact False.elim (hx0 (m4_minor_01_03 x hx2 hx3 hy0 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_01_12 x hx2 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_01_12 x hx2 hx3 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_01_13 x hx2 hx3 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_01_23 x hx2 hx3 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_013_012 x hx2 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_013_012 x hx2 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_013_013 x hx2 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_013_023 x hx2 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_013_123 x hx2 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_012_012 x hx3 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_012_012 x hx3 hy0 hy1 hy2))
    · exact False.elim (hx0 (m4_minor_012_013 x hx3 hy0 hy1 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_012_023 x hx3 hy0 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · exact False.elim (hx0 (m4_minor_012_123 x hx3 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
  · by_cases hy0 : (applyM4 x).x0 = Goldilocks.zero <;>
      by_cases hy1 : (applyM4 x).x1 = Goldilocks.zero <;>
      by_cases hy2 : (applyM4 x).x2 = Goldilocks.zero <;>
      by_cases hy3 : (applyM4 x).x3 = Goldilocks.zero
    · exact False.elim (hx0 (m4_minor_0123_0123 x hy0 hy1 hy2 hy3))
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    · simp [laneWeight4, hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]

def vectorLane4 (x : Fin 4 → Goldilocks) : Lane4 := ⟨x 0, x 1, x 2, x 3⟩

def lane4Vector (x : Lane4) (i : Fin 4) : Goldilocks :=
  if i.val = 0 then x.x0 else if i.val = 1 then x.x1 else if i.val = 2 then x.x2 else x.x3

def hammingWeight4 (x : Fin 4 → Goldilocks) : Nat := laneWeight4 (vectorLane4 x)

/-- Function-vector interface to the deployed four-lane matrix. -/
def applyM4Vector (x : Fin 4 → Goldilocks) : Fin 4 → Goldilocks :=
  lane4Vector (applyM4 (vectorLane4 x))

private theorem vectorLane4_lane4Vector (x : Lane4) : vectorLane4 (lane4Vector x) = x := by
  cases x
  rfl

/-- Exact branch number: universal lower bound and an attaining nonzero input. -/
theorem m4_mds_branch_number_eq_five :
    (∀ x : Fin 4 → Goldilocks, x ≠ (fun _ => Goldilocks.zero) →
      5 ≤ hammingWeight4 x + hammingWeight4 (applyM4Vector x)) ∧
    (∃ x : Fin 4 → Goldilocks, x ≠ (fun _ => Goldilocks.zero) ∧
      hammingWeight4 x + hammingWeight4 (applyM4Vector x) = 5) := by
  constructor
  · intro x hx
    have hn : vectorLane4 x ≠ lane4Zero := by
      intro hz
      apply hx
      funext i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
        have := i.isLt
        omega
      rcases hi with rfl | rfl | rfl | rfl
      · exact congrArg Lane4.x0 hz
      · exact congrArg Lane4.x1 hz
      · exact congrArg Lane4.x2 hz
      · exact congrArg Lane4.x3 hz
    simpa only [hammingWeight4, applyM4Vector, vectorLane4_lane4Vector] using
      m4_mds_branch_lower (vectorLane4 x) hn
  · refine ⟨lane4Vector ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      contradiction
    · decide



/-! ## 6. Two-round differential activity for the deployed four-lane S-box/MDS component -/

private theorem gold_sub_zero_iff (a b : Goldilocks) :
    Goldilocks.sub a b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff

private theorem sbox7_add_diff_zero_iff (a b c : Goldilocks) :
    Goldilocks.sub (sbox7 (Goldilocks.add a c)) (sbox7 (Goldilocks.add b c)) =
      Goldilocks.zero ↔ Goldilocks.sub a b = Goldilocks.zero := by
  rw [gold_sub_zero_iff, (sbox7_bijective _ _).2.2.1, gold_sub_zero_iff]
  constructor
  · intro h
    apply LawfulCommRing.add_left_cancel (a := c)
    change Goldilocks.add c a = Goldilocks.add c b
    simpa only [show ∀ u v : Goldilocks, Goldilocks.add u v = Goldilocks.add v u from
      LawfulCommRing.add_comm] using h
  · intro h
    rw [h]

/-- Bijection of the actual seventh-power S-box preserves differential support, also after
    adding an arbitrary shared round constant. -/
theorem sbox7_preserves_differential_activity (a b rc : Lane4) :
    laneWeight4 (lane4Sub (sboxLane4 (lane4Add a rc)) (sboxLane4 (lane4Add b rc))) =
      laneWeight4 (lane4Sub a b) := by
  simp only [laneWeight4, lane4Sub, sboxLane4, lane4Add, sbox7_add_diff_zero_iff]
  rfl

private theorem applyM4_sub (a b : Lane4) :
    lane4Sub (applyM4 a) (applyM4 b) = applyM4 (lane4Sub a b) := by
  unfold applyM4 lane4Sub lane4Sum
  apply Lane4.ext <;>
    (dsimp only
     rw [← goldOfInt_nat a.x0, ← goldOfInt_nat a.x1,
       ← goldOfInt_nat a.x2, ← goldOfInt_nat a.x3,
       ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1,
       ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3]
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
     congr 1
     omega)

private theorem lane4Sub_eq_zero_iff (a b : Lane4) : lane4Sub a b = lane4Zero ↔ a = b := by
  constructor
  · intro h
    apply Lane4.ext
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x0 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x1 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x2 h)
    · exact (gold_sub_zero_iff _ _).mp (congrArg Lane4.x3 h)
  · intro h
    subst b
    apply Lane4.ext <;> exact (gold_sub_zero_iff _ _).mpr rfl

/-- One full round of the four-lane component: shared constant, actual S-box, actual M4. -/
def poseidon2Round4 (rc x : Lane4) : Lane4 := applyM4 (sboxLane4 (lane4Add x rc))

/-- At least five active S-boxes across two successive four-lane rounds. The first term counts
    the first S-box inputs and the second counts the next round's S-box inputs. Arbitrary shared
    round constants preserve these counts. This is a structural bound, not a probability claim
    for the full twelve-lane permutation or for partial rounds. -/
theorem poseidon2_two_round_active_sboxes_ge_five (a b rc : Lane4) (hne : a ≠ b) :
    5 ≤ laneWeight4 (lane4Sub a b) +
      laneWeight4 (lane4Sub (poseidon2Round4 rc a) (poseidon2Round4 rc b)) := by
  let d := lane4Sub (sboxLane4 (lane4Add a rc)) (sboxLane4 (lane4Add b rc))
  have hd : d ≠ lane4Zero := by
    intro h
    have hEq := (lane4Sub_eq_zero_iff _ _).mp h
    apply hne
    apply Lane4.ext
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x0 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x1 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x2 hEq)))
    · exact (gold_sub_zero_iff _ _).mp ((sbox7_add_diff_zero_iff _ _ _).mp
        ((gold_sub_zero_iff _ _).mpr (congrArg Lane4.x3 hEq)))
  have hm := m4_mds_branch_lower d hd
  rw [sbox7_preserves_differential_activity] at hm
  simpa only [poseidon2Round4, applyM4_sub] using hm

private theorem laneWeight4_le_four (x : Lane4) : laneWeight4 x ≤ 4 := by
  unfold laneWeight4
  split <;> split <;> split <;> split <;> decide +kernel

private theorem poseidon2Round4_injective (rc : Lane4) (a b : Lane4)
    (h : poseidon2Round4 rc a = poseidon2Round4 rc b) : a = b := by
  if he : a = b then exact he else
    have hm := poseidon2_two_round_active_sboxes_ge_five a b rc he
    have hu := laneWeight4_le_four (lane4Sub a b)
    have hz := (lane4Sub_eq_zero_iff _ _).mpr h
    rw [hz] at hm
    have hw : laneWeight4 lane4Zero = 0 := rfl
    rw [hw] at hm
    omega

/-- Eight full four-lane rounds contain four disjoint two-round windows. This counts actual
    differential supports in a supplied nonzero trajectory, rather than a nominal round floor. -/
theorem poseidon2_eight_round_active_sboxes_ge_twenty
    (a b : Nat → Lane4) (rc : Nat → Lane4)
    (ha : ∀ i, a (i + 1) = poseidon2Round4 (rc i) (a i))
    (hb : ∀ i, b (i + 1) = poseidon2Round4 (rc i) (b i))
    (hInitial : a 0 ≠ b 0) :
    20 ≤ (laneWeight4 (lane4Sub (a 0) (b 0)) + laneWeight4 (lane4Sub (a 1) (b 1))) +
      (laneWeight4 (lane4Sub (a 2) (b 2)) + laneWeight4 (lane4Sub (a 3) (b 3))) +
      (laneWeight4 (lane4Sub (a 4) (b 4)) + laneWeight4 (lane4Sub (a 5) (b 5))) +
      (laneWeight4 (lane4Sub (a 6) (b 6)) + laneWeight4 (lane4Sub (a 7) (b 7))) := by
  have hne : ∀ i, a i ≠ b i := by
    intro i
    induction i with
    | zero => exact hInitial
    | succ i ih =>
      intro h
      rw [ha i, hb i] at h
      exact ih (poseidon2Round4_injective (rc i) (a i) (b i) h)
  have h0 := poseidon2_two_round_active_sboxes_ge_five (a 0) (b 0) (rc 0) (hne 0)
  have h2 := poseidon2_two_round_active_sboxes_ge_five (a 2) (b 2) (rc 2) (hne 2)
  have h4 := poseidon2_two_round_active_sboxes_ge_five (a 4) (b 4) (rc 4) (hne 4)
  have h6 := poseidon2_two_round_active_sboxes_ge_five (a 6) (b 6) (rc 6) (hne 6)
  rw [← ha 0, ← hb 0] at h0
  rw [← ha 2, ← hb 2] at h2
  rw [← ha 4, ← hb 4] at h4
  rw [← ha 6, ← hb 6] at h6
  simp only [Nat.reduceAdd] at h0 h2 h4 h6
  omega


/-! ### Symbolic degree of actual four-lane rounds -/

/-- Scalar polynomial syntax. Degree here is a syntactic upper bound; cancellations and
    reduction modulo `X^p - X` may lower the degree of the induced field function. -/
inductive PoseidonExpr where
  | variable : Nat → PoseidonExpr
  | constant : Goldilocks → PoseidonExpr
  | add : PoseidonExpr → PoseidonExpr → PoseidonExpr
  | mul : PoseidonExpr → PoseidonExpr → PoseidonExpr

def PoseidonExpr.eval (v : Nat → Goldilocks) : PoseidonExpr → Goldilocks
  | .variable i => v i
  | .constant c => c
  | .add a b => Goldilocks.add (a.eval v) (b.eval v)
  | .mul a b => Goldilocks.mul (a.eval v) (b.eval v)

def PoseidonExpr.degree : PoseidonExpr → Nat
  | .variable _ => 1
  | .constant _ => 0
  | .add a b => max a.degree b.degree
  | .mul a b => a.degree + b.degree

/-- Exactly the multiplication circuit used by `sbox7`. -/
def PoseidonExpr.seventh (x : PoseidonExpr) : PoseidonExpr :=
  let x2 := .mul x x
  let x3 := .mul x2 x
  let x4 := .mul x2 x2
  .mul x3 x4

theorem symbolic_sbox7_eval (v : Nat → Goldilocks) (x : PoseidonExpr) :
    x.seventh.eval v = sbox7 (x.eval v) := by
  simp only [PoseidonExpr.seventh, PoseidonExpr.eval, sbox7]

theorem symbolic_sbox7_degree (x : PoseidonExpr) : x.seventh.degree = 7 * x.degree := by
  simp only [PoseidonExpr.seventh, PoseidonExpr.degree]
  omega

private def symbolicM4Lane (s a b : PoseidonExpr) : PoseidonExpr :=
  .add s (.add a (.mul (.constant (Goldilocks.ofNat 2)) b))

/-- The operational circuit of `applyM4`, lifted to polynomial expressions. -/
def symbolicM4 (x : Fin 4 → PoseidonExpr) (i : Fin 4) : PoseidonExpr :=
  let s := PoseidonExpr.add (.add (x 0) (x 1)) (.add (x 2) (x 3))
  if i.val = 0 then symbolicM4Lane s (x 0) (x 1)
  else if i.val = 1 then symbolicM4Lane s (x 1) (x 2)
  else if i.val = 2 then symbolicM4Lane s (x 2) (x 3)
  else symbolicM4Lane s (x 3) (x 0)

private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have := i.isLt
  omega

theorem symbolicM4_eval (v : Nat → Goldilocks) (x : Fin 4 → PoseidonExpr) :
    (fun i => (symbolicM4 x i).eval v) = applyM4Vector (fun i => (x i).eval v) := by
  funext i
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;> rfl

theorem symbolicM4_degree_le (x : Fin 4 → PoseidonExpr) (k : Nat)
    (hx : ∀ i, (x i).degree ≤ k) (i : Fin 4) : (symbolicM4 x i).degree ≤ k := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  rcases fin4_cases i with rfl | rfl | rfl | rfl <;>
    (simp [symbolicM4, symbolicM4Lane, PoseidonExpr.degree, show (3 : Fin 4).val = 3 from rfl]
     omega)

/-- Shared round constants are degree zero; each round multiplies the degree bound by seven. -/
def symbolicRound4 (rc : Lane4) (x : Fin 4 → PoseidonExpr) : Fin 4 → PoseidonExpr :=
  symbolicM4 (fun i => (PoseidonExpr.add (x i) (.constant (lane4Vector rc i))).seventh)

theorem symbolicRound4_eval (v : Nat → Goldilocks) (rc : Lane4)
    (x : Fin 4 → PoseidonExpr) :
    (fun i => (symbolicRound4 rc x i).eval v) =
      lane4Vector (poseidon2Round4 rc (vectorLane4 (fun i => (x i).eval v))) := by
  rw [symbolicRound4, symbolicM4_eval]
  rfl

theorem symbolicRound4_degree_le (rc : Lane4) (x : Fin 4 → PoseidonExpr) (k : Nat)
    (hx : ∀ i, (x i).degree ≤ k) (i : Fin 4) : (symbolicRound4 rc x i).degree ≤ 7 * k := by
  apply symbolicM4_degree_le
  intro j
  rw [symbolic_sbox7_degree]
  simp only [PoseidonExpr.degree, Nat.max_zero]
  exact Nat.mul_le_mul_left 7 (hx j)

/-- Round-by-round symbolic bound for any sequence of actual four-lane rounds, starting with
    coordinate variables. This gives `7^r` as an upper bound, never as a lower bound on security. -/
theorem poseidon2_symbolic_round_degree_bound (x : Nat → Fin 4 → PoseidonExpr)
    (rc : Nat → Lane4) (h0 : ∀ i, x 0 i = .variable i.val)
    (hstep : ∀ r, x (r + 1) = symbolicRound4 (rc r) (x r)) :
    ∀ r i, (x r i).degree ≤ 7 ^ r := by
  intro r
  induction r with
  | zero => intro i; rw [h0]; exact Nat.le_refl 1
  | succ r ih =>
    intro i
    rw [hstep]
    have h := symbolicRound4_degree_le (rc r) (x r) (7 ^ r) ih i
    simpa only [Nat.pow_succ, Nat.mul_comm] using h


/-! ## 8. Width-12 `M_E` & `M_I` Differential/Linear Branch Numbers & `2026/306` Subspace Analysis

The deployed external layer is `applyME = T₃₄ ∘ applyMEStd ∘ T₄₃` (`M_4 ⊗ P_3`), the lane-transposition
conjugate of the block-circulant factor `applyMEStd = P_3 ⊗ M_4 = circ(2 M_4, M_4, M_4)`. Block-structured
bounds are proved for `applyMEStd` (names `…me12std…`) and transferred to `applyME` through the weight-
preserving transpositions. The internal layer `applyMI` is `1·1ᵀ + diag(-64, 1, 2, 4, …, 1024)`. -/

/-- Exact 12-lane Hamming weight (count of nonzero `Goldilocks` elements) on `Poseidon2State12`. -/
def stateWeight12 (s : Poseidon2State12) : Nat :=
  laneWeight4 s.b0 + laneWeight4 s.b1 + laneWeight4 s.b2

/-- Count of nonzero 4-lane blocks in `Poseidon2State12` (`0..3`). -/
def activeBlocks12 (s : Poseidon2State12) : Nat :=
  (if s.b0 = lane4Zero then 0 else 1) +
  (if s.b1 = lane4Zero then 0 else 1) +
  (if s.b2 = lane4Zero then 0 else 1)

def lane4Neg (a : Lane4) : Lane4 := lane4Sub lane4Zero a

def lane4Rev (a : Lane4) : Lane4 := ⟨a.x0, a.x3, a.x2, a.x1⟩

def state12Rev4 (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨lane4Rev s.b0, lane4Rev s.b1, lane4Rev s.b2⟩

/-- Exact transpose of `applyMEStd` with respect to the standard 12-lane dot product. -/
def applyMEStdTranspose (s : Poseidon2State12) : Poseidon2State12 :=
  state12Rev4 (applyMEStd (state12Rev4 s))

def lane4Dot (a b : Lane4) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add (Goldilocks.mul a.x0 b.x0) (Goldilocks.mul a.x1 b.x1))
    (Goldilocks.add (Goldilocks.mul a.x2 b.x2) (Goldilocks.mul a.x3 b.x3))

def state12Dot (a b : Poseidon2State12) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (lane4Dot a.b0 b.b0) (lane4Dot a.b1 b.b1)) (lane4Dot a.b2 b.b2)

private theorem gold_add_eq_zero_of_both_zero {a b : Goldilocks}
    (ha : a = Goldilocks.zero) (hb : b = Goldilocks.zero) :
    Goldilocks.add a b = Goldilocks.zero := by
  subst ha; subst hb; rfl

private theorem gold_sub_eq_zero_of_both_zero {a b : Goldilocks}
    (ha : a = Goldilocks.zero) (hb : b = Goldilocks.zero) :
    Goldilocks.sub a b = Goldilocks.zero := by
  subst ha; subst hb; rfl

private theorem coord_wt_add_le (a b : Goldilocks) :
    (if Goldilocks.add a b = Goldilocks.zero then 0 else 1) ≤
      (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero <;> by_cases hb : b = Goldilocks.zero
  · rw [gold_add_eq_zero_of_both_zero ha hb]; simp [ha, hb]
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega

private theorem coord_wt_sub_le (a b : Goldilocks) :
    (if Goldilocks.sub a b = Goldilocks.zero then 0 else 1) ≤
      (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero <;> by_cases hb : b = Goldilocks.zero
  · rw [gold_sub_eq_zero_of_both_zero ha hb]; simp [ha, hb]
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega
  · simp [ha, hb]; split <;> omega

private theorem coord_wt_mul_nz {c : Goldilocks} (hc : c ≠ Goldilocks.zero) (a : Goldilocks) :
    (if Goldilocks.mul c a = Goldilocks.zero then 0 else 1) =
      (if a = Goldilocks.zero then 0 else 1) := by
  by_cases ha : a = Goldilocks.zero
  · subst ha
    have hz : Goldilocks.mul c Goldilocks.zero = Goldilocks.zero :=
      LawfulCommRing.mul_zero c
    simp [hz]
  · have hnz : Goldilocks.mul c a ≠ Goldilocks.zero := fun hm => by
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hm with h1 | h2
      · exact hc h1
      · exact ha h2
    simp [ha, hnz]

private theorem laneWeight4_pos_of_ne_zero {a : Lane4} (ha : a ≠ lane4Zero) :
    1 ≤ laneWeight4 a := by
  unfold laneWeight4
  by_cases h0 : a.x0 = Goldilocks.zero <;>
    by_cases h1 : a.x1 = Goldilocks.zero <;>
    by_cases h2 : a.x2 = Goldilocks.zero <;>
    by_cases h3 : a.x3 = Goldilocks.zero
  · exact False.elim (ha (Lane4.ext h0 h1 h2 h3))
  all_goals simp [h0, h1, h2, h3]

private theorem gold_add_cring (a b : Goldilocks) : Goldilocks.add a b = CommRingOps.add a b := rfl
private theorem gold_sub_cring (a b : Goldilocks) : Goldilocks.sub a b = CommRingOps.sub a b := rfl
private theorem gold_mul_cring (a b : Goldilocks) : Goldilocks.mul a b = CommRingOps.mul a b := rfl
private theorem gold_neg_cring (a : Goldilocks) : Goldilocks.neg a = CommRingOps.neg a := rfl
private theorem gold_zero_cring : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := rfl
private theorem gold_one_cring : Goldilocks.one = (CommRingOps.one : Goldilocks) := rfl
private theorem gold_2_cring : Goldilocks.ofNat 2 = CRing.natCast 2 := by decide +kernel
private theorem gold_3_cring : Goldilocks.ofNat 3 = CRing.natCast 3 := by decide +kernel
private theorem gold_4_cring : Goldilocks.ofNat 4 = CRing.natCast 4 := by decide +kernel

macro "gold_cring" : tactic => `(tactic| (
  try dsimp only
  try simp only [gold_add_cring, gold_sub_cring, gold_mul_cring, gold_neg_cring,
    gold_zero_cring, gold_one_cring, gold_2_cring, gold_3_cring, gold_4_cring]
  try (open scoped Qsag.CRing in constructive_ring)))

private theorem laneWeight4_add_le (a b : Lane4) :
    laneWeight4 (lane4Add a b) ≤ laneWeight4 a + laneWeight4 b := by
  unfold laneWeight4 lane4Add
  dsimp only
  have h0 := coord_wt_add_le a.x0 b.x0
  have h1 := coord_wt_add_le a.x1 b.x1
  have h2 := coord_wt_add_le a.x2 b.x2
  have h3 := coord_wt_add_le a.x3 b.x3
  omega

private theorem laneWeight4_sub_le (a b : Lane4) :
    laneWeight4 (lane4Sub a b) ≤ laneWeight4 a + laneWeight4 b := by
  unfold laneWeight4 lane4Sub
  dsimp only
  have h0 := coord_wt_sub_le a.x0 b.x0
  have h1 := coord_wt_sub_le a.x1 b.x1
  have h2 := coord_wt_sub_le a.x2 b.x2
  have h3 := coord_wt_sub_le a.x3 b.x3
  omega

private theorem laneWeight4_scale_ne_zero {c : Goldilocks} (hc : c ≠ Goldilocks.zero) (a : Lane4) :
    laneWeight4 (lane4Scale c a) = laneWeight4 a := by
  unfold laneWeight4 lane4Scale
  dsimp only
  rw [coord_wt_mul_nz hc, coord_wt_mul_nz hc, coord_wt_mul_nz hc, coord_wt_mul_nz hc]

private theorem applyM4_ne_zero_of_ne_zero {a : Lane4} (ha : a ≠ lane4Zero) :
    applyM4 a ≠ lane4Zero := fun hz => by
  apply ha
  have hInv := congrArg applyM4Inv hz
  rw [applyM4Inv_applyM4] at hInv
  exact hInv.trans (by decide +kernel)

private def rot12 (s : Poseidon2State12) : Poseidon2State12 := ⟨s.b1, s.b2, s.b0⟩
private def swap01 (s : Poseidon2State12) : Poseidon2State12 := ⟨s.b1, s.b0, s.b2⟩

private theorem stateWeight12_rot12 (s : Poseidon2State12) :
    stateWeight12 (rot12 s) = stateWeight12 s := by
  unfold stateWeight12 rot12; dsimp only; omega

private theorem activeBlocks12_rot12 (s : Poseidon2State12) :
    activeBlocks12 (rot12 s) = activeBlocks12 s := by
  unfold activeBlocks12 rot12; dsimp only; omega

private theorem stateWeight12_swap01 (s : Poseidon2State12) :
    stateWeight12 (swap01 s) = stateWeight12 s := by
  unfold stateWeight12 swap01; dsimp only; omega

private theorem activeBlocks12_swap01 (s : Poseidon2State12) :
    activeBlocks12 (swap01 s) = activeBlocks12 s := by
  unfold activeBlocks12 swap01; dsimp only; omega

private theorem lane4Add_sum3_rot (a b c : Lane4) :
    lane4Add (lane4Add b c) a = lane4Add (lane4Add a b) c := by
  unfold lane4Add
  apply Lane4.ext <;> gold_cring

private theorem lane4Add_sum3_swap01 (a b c : Lane4) :
    lane4Add (lane4Add b a) c = lane4Add (lane4Add a b) c := by
  unfold lane4Add
  apply Lane4.ext <;> gold_cring

private theorem applyME_rot12 (s : Poseidon2State12) :
    applyMEStd (rot12 s) = rot12 (applyMEStd s) := by
  unfold applyMEStd rot12
  dsimp only
  rw [lane4Add_sum3_rot]

private theorem applyME_swap01 (s : Poseidon2State12) :
    applyMEStd (swap01 s) = swap01 (applyMEStd s) := by
  unfold applyMEStd swap01
  dsimp only
  rw [lane4Add_sum3_swap01]

private theorem applyME_single_b0 (b : Lane4) (hb : b ≠ lane4Zero) :
    7 ≤ stateWeight12 ⟨b, lane4Zero, lane4Zero⟩ +
      stateWeight12 (applyMEStd ⟨b, lane4Zero, lane4Zero⟩) := by
  have hzM4 : applyM4 lane4Zero = lane4Zero := by decide +kernel
  have hOut : applyMEStd ⟨b, lane4Zero, lane4Zero⟩ =
      ⟨lane4Scale (Goldilocks.ofNat 2) (applyM4 b), applyM4 b, applyM4 b⟩ := by
    unfold applyMEStd
    dsimp only
    rw [hzM4]
    unfold lane4Add lane4Scale lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  rw [hOut]
  unfold stateWeight12
  dsimp only
  have h2nz : Goldilocks.ofNat 2 ≠ Goldilocks.zero := by decide +kernel
  rw [laneWeight4_scale_ne_zero h2nz, show laneWeight4 lane4Zero = 0 from rfl]
  have hm := m4_mds_branch_lower b hb
  have hy := laneWeight4_pos_of_ne_zero (applyM4_ne_zero_of_ne_zero hb)
  omega

/-- **Single-Active-Block Width-12 `M_E` Branch Bound (`poseidon2_me12std_single_block_branch_ge_seven`)**:
    Across any nonzero state supported in a single 4-lane block (`activeBlocks12 x = 1`),
    `stateWeight12 x + stateWeight12 (applyMEStd x) ≥ 7` (hence strictly above `5`). -/
theorem poseidon2_me12std_single_block_branch_ge_seven (x : Poseidon2State12)
    (h1 : activeBlocks12 x = 1) :
    7 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) ∧
    5 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) := by
  have h7 : 7 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) := by
    unfold activeBlocks12 at h1
    by_cases hb0 : x.b0 = lane4Zero <;>
      by_cases hb1 : x.b1 = lane4Zero <;>
      by_cases hb2 : x.b2 = lane4Zero
    · simp [hb0, hb1, hb2] at h1
    · have hRot : rot12 (rot12 x) = ⟨x.b2, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb0 hb1
      have hm := applyME_single_b0 x.b2 hb2
      rw [← hRot, stateWeight12_rot12, stateWeight12_rot12,
          applyME_rot12, applyME_rot12, stateWeight12_rot12, stateWeight12_rot12] at hm
      exact hm
    · have hRot : rot12 x = ⟨x.b1, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb2 hb0
      have hm := applyME_single_b0 x.b1 hb1
      rw [← hRot, stateWeight12_rot12, applyME_rot12, stateWeight12_rot12] at hm
      exact hm
    · simp [hb0, hb1, hb2] at h1
    · have hx : x = ⟨x.b0, lane4Zero, lane4Zero⟩ :=
        Poseidon2State12.ext rfl hb1 hb2
      rw [hx]
      exact applyME_single_b0 x.b0 hb0
    · simp [hb0, hb1, hb2] at h1
    · simp [hb0, hb1, hb2] at h1
    · simp [hb0, hb1, hb2] at h1
  exact ⟨h7, by omega⟩

private theorem applyMEInv_single_b0 (z : Lane4) (hz : z ≠ lane4Zero) :
    7 ≤ stateWeight12 (applyMEStdInv ⟨z, lane4Zero, lane4Zero⟩) +
      stateWeight12 ⟨z, lane4Zero, lane4Zero⟩ := by
  let cinv4 : Goldilocks := Goldilocks.ofNat 13835058052060938241
  let c3 : Goldilocks := Goldilocks.mul (Goldilocks.ofNat 3) cinv4
  let cn1 : Goldilocks := Goldilocks.sub Goldilocks.zero cinv4
  have hc3nz : c3 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide +kernel)
  have hcn1nz : cn1 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide +kernel)
  have h4inv : Goldilocks.mul (Goldilocks.ofNat 4) cinv4 = Goldilocks.one := by decide +kernel
  have hLinM4 : ∀ (c : Goldilocks) (v : Lane4), applyM4 (lane4Scale c v) = lane4Scale c (applyM4 v) :=
    fun c v => by
      unfold applyM4 lane4Scale lane4Sum
      apply Lane4.ext <;> gold_cring
  have hInvShape : applyMEStdInv ⟨z, lane4Zero, lane4Zero⟩ =
      ⟨lane4Scale c3 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z)⟩ := by
    suffices hFwd : applyMEStd ⟨lane4Scale c3 (applyM4Inv z),
        lane4Scale cn1 (applyM4Inv z), lane4Scale cn1 (applyM4Inv z)⟩ = ⟨z, lane4Zero, lane4Zero⟩ by
      have h := congrArg applyMEStdInv hFwd
      rw [applyMEStdInv_applyMEStd] at h
      exact h.symm
    unfold applyMEStd
    dsimp only
    rw [hLinM4, hLinM4, applyM4_applyM4Inv]
    unfold c3 cn1 lane4Add lane4Scale lane4Zero
    have hCoeff1 : ∀ a : Goldilocks,
        Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a))
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a)) = a := fun a => by
      have hRing : Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 3) cinv4) a)
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a))
            (Goldilocks.mul (Goldilocks.sub Goldilocks.zero cinv4) a)) =
          Goldilocks.mul (Goldilocks.mul (Goldilocks.ofNat 4) cinv4) a := by gold_cring
      rw [hRing, h4inv]
      exact LawfulCommRing.one_mul a
    apply Poseidon2State12.ext
    · exact Lane4.ext (hCoeff1 z.x0) (hCoeff1 z.x1) (hCoeff1 z.x2) (hCoeff1 z.x3)
    · apply Lane4.ext <;> gold_cring
    · apply Lane4.ext <;> gold_cring
  rw [hInvShape]
  unfold stateWeight12
  dsimp only
  rw [laneWeight4_scale_ne_zero hc3nz, laneWeight4_scale_ne_zero hcn1nz,
      show laneWeight4 lane4Zero = 0 from rfl]
  let v := applyM4Inv z
  have hv : v ≠ lane4Zero := fun hvz => by
    apply hz
    have := congrArg applyM4 hvz
    rw [applyM4_applyM4Inv] at this
    exact this.trans (by decide +kernel)
  have hm := m4_mds_branch_lower v hv
  have hM4v : applyM4 v = z := applyM4_applyM4Inv z
  rw [hM4v] at hm
  have hvp := laneWeight4_pos_of_ne_zero hv
  change 7 ≤ laneWeight4 v + laneWeight4 v + laneWeight4 v + (laneWeight4 z + 0 + 0)
  omega

private theorem applyME_single_out_branch_ge_seven (x : Poseidon2State12)
    (h1 : activeBlocks12 (applyMEStd x) = 1) :
    7 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) := by
  let y := applyMEStd x
  have hyEq : x = applyMEStdInv y := (applyMEStdInv_applyMEStd x).symm
  unfold activeBlocks12 at h1
  change (if y.b0 = lane4Zero then 0 else 1) +
      (if y.b1 = lane4Zero then 0 else 1) +
      (if y.b2 = lane4Zero then 0 else 1) = 1 at h1
  by_cases hy0 : y.b0 = lane4Zero <;>
    by_cases hy1 : y.b1 = lane4Zero <;>
    by_cases hy2 : y.b2 = lane4Zero
  · simp [hy0, hy1, hy2] at h1
  · have hRot : rot12 (rot12 y) = ⟨y.b2, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy0 hy1
    have hInvRot : applyMEStdInv ⟨y.b2, lane4Zero, lane4Zero⟩ = rot12 (rot12 x) := by
      suffices hFwd : applyMEStd (applyMEStdInv ⟨y.b2, lane4Zero, lane4Zero⟩) = applyMEStd (rot12 (rot12 x)) by
        have h := congrArg applyMEStdInv hFwd
        rwa [applyMEStdInv_applyMEStd, applyMEStdInv_applyMEStd] at h
      rw [applyMEStd_applyMEStdInv, applyME_rot12, applyME_rot12, ← hRot]
    have hm := applyMEInv_single_b0 y.b2 hy2
    rw [hInvRot, ← hRot, stateWeight12_rot12, stateWeight12_rot12,
        stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · have hRot : rot12 y = ⟨y.b1, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy2 hy0
    have hInvRot : applyMEStdInv ⟨y.b1, lane4Zero, lane4Zero⟩ = rot12 x := by
      suffices hFwd : applyMEStd (applyMEStdInv ⟨y.b1, lane4Zero, lane4Zero⟩) = applyMEStd (rot12 x) by
        have h := congrArg applyMEStdInv hFwd
        rwa [applyMEStdInv_applyMEStd, applyMEStdInv_applyMEStd] at h
      rw [applyMEStd_applyMEStdInv, applyME_rot12, ← hRot]
    have hm := applyMEInv_single_b0 y.b1 hy1
    rw [hInvRot, ← hRot, stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · simp [hy0, hy1, hy2] at h1
  · have hyShape : y = ⟨y.b0, lane4Zero, lane4Zero⟩ :=
      Poseidon2State12.ext rfl hy1 hy2
    have hm := applyMEInv_single_b0 y.b0 hy0
    rw [← hyShape, ← hyEq] at hm
    exact hm
  · simp [hy0, hy1, hy2] at h1
  · simp [hy0, hy1, hy2] at h1
  · simp [hy0, hy1, hy2] at h1

private theorem applyME_block_diffs (x : Poseidon2State12) :
    lane4Sub (applyMEStd x).b0 (applyMEStd x).b1 = applyM4 (lane4Sub x.b0 x.b1) ∧
    lane4Sub (applyMEStd x).b1 (applyMEStd x).b2 = applyM4 (lane4Sub x.b1 x.b2) ∧
    lane4Sub (applyMEStd x).b2 (applyMEStd x).b0 = applyM4 (lane4Sub x.b2 x.b0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold applyMEStd applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring
  · unfold applyMEStd applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring
  · unfold applyMEStd applyM4 lane4Add lane4Sub lane4Sum
    apply Lane4.ext <;> gold_cring

private theorem applyME_multiblock_b1_eq_b2 (x : Poseidon2State12)
    (hEq12 : x.b1 = x.b2)
    (hIn : 2 ≤ activeBlocks12 x)
    (hOut : 2 ≤ activeBlocks12 (applyMEStd x)) :
    8 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) := by
  have hb1nz : x.b1 ≠ lane4Zero := fun hz => by
    unfold activeBlocks12 at hIn
    rw [← hEq12, hz] at hIn
    by_cases hb0 : x.b0 = lane4Zero <;> simp [hb0] at hIn
  have houtEq12 : (applyMEStd x).b1 = (applyMEStd x).b2 := by
    unfold applyMEStd; rw [hEq12]
  have hout1nz : (applyMEStd x).b1 ≠ lane4Zero := fun hz => by
    unfold activeBlocks12 at hOut
    rw [← houtEq12, hz] at hOut
    by_cases hy0 : (applyMEStd x).b0 = lane4Zero <;> simp [hy0] at hOut
  have h2nz : Goldilocks.ofNat 2 ≠ Goldilocks.zero := by decide +kernel
  have h3nz : Goldilocks.ofNat 3 ≠ Goldilocks.zero := by decide +kernel
  have h4nz : Goldilocks.ofNat 4 ≠ Goldilocks.zero := by decide +kernel
  have hout0Eq : (applyMEStd x).b0 =
      lane4Scale (Goldilocks.ofNat 2) (applyM4 (lane4Add x.b0 x.b1)) := by
    unfold applyMEStd
    rw [hEq12]
    dsimp only
    unfold applyM4 lane4Add lane4Scale lane4Sum
    apply Lane4.ext <;> gold_cring
  have h4y1 : lane4Scale (Goldilocks.ofNat 4) (applyM4 x.b1) =
      lane4Sub (lane4Scale (Goldilocks.ofNat 2) (applyMEStd x).b1) (applyMEStd x).b0 := by
    unfold applyMEStd
    rw [hEq12]
    dsimp only
    unfold lane4Add lane4Sub lane4Scale
    apply Lane4.ext <;> gold_cring
  by_cases hb0 : x.b0 = lane4Zero
  · have hout1Scale : (applyMEStd x).b1 = lane4Scale (Goldilocks.ofNat 3) (applyM4 x.b1) := by
      unfold applyMEStd
      rw [hb0, ← hEq12, show applyM4 lane4Zero = lane4Zero from by decide +kernel]
      unfold lane4Add lane4Scale lane4Zero
      apply Lane4.ext <;> gold_cring
    have hAdd0 : lane4Add lane4Zero x.b1 = x.b1 := by
      unfold lane4Add lane4Zero
      apply Lane4.ext <;> exact LawfulCommRing.zero_add _
    unfold stateWeight12
    rw [hb0, ← hEq12, ← houtEq12, hout0Eq, hb0, hAdd0, hout1Scale,
        laneWeight4_scale_ne_zero h2nz, laneWeight4_scale_ne_zero h3nz,
        show laneWeight4 lane4Zero = 0 from rfl]
    have hm := m4_mds_branch_lower x.b1 hb1nz
    omega
  · by_cases hy0 : (applyMEStd x).b0 = lane4Zero
    · have hSumZero : lane4Add x.b0 x.b1 = lane4Zero := by
        by_cases hs : lane4Add x.b0 x.b1 = lane4Zero
        · exact hs
        · have hm4nz := applyM4_ne_zero_of_ne_zero hs
          have hwt := laneWeight4_pos_of_ne_zero hm4nz
          rw [← laneWeight4_scale_ne_zero h2nz, ← hout0Eq, hy0] at hwt
          cases hwt
      have hb0Neg : x.b0 = lane4Scale goldilocksNegOne x.b1 := by
        have hSub : x.b0 = lane4Sub (lane4Add x.b0 x.b1) x.b1 := by
          unfold lane4Add lane4Sub
          apply Lane4.ext <;> gold_cring
        rw [hSub, hSumZero]
        unfold lane4Sub lane4Scale lane4Zero
        have hn1 : goldilocksNegOne = CommRingOps.neg CommRingOps.one := by
          change goldilocksNegOne = Goldilocks.neg Goldilocks.one
          apply Goldilocks.ext
          rw [Goldilocks.neg_val]
          decide
        rw [hn1]
        apply Lane4.ext <;> gold_cring
      have hw0 : laneWeight4 x.b0 = laneWeight4 x.b1 := by
        rw [hb0Neg, laneWeight4_scale_ne_zero (by decide +kernel)]
      have hwOut1 : laneWeight4 (applyM4 x.b1) = laneWeight4 (applyMEStd x).b1 := by
        have h := congrArg laneWeight4 h4y1
        rw [hy0, laneWeight4_scale_ne_zero h4nz] at h
        have hSub0 : lane4Sub (lane4Scale (Goldilocks.ofNat 2) (applyMEStd x).b1) lane4Zero =
            lane4Scale (Goldilocks.ofNat 2) (applyMEStd x).b1 := by
          unfold lane4Sub lane4Zero
          apply Lane4.ext <;> exact LawfulCommRing.sub_zero _
        rw [hSub0, laneWeight4_scale_ne_zero h2nz] at h
        exact h
      unfold stateWeight12
      rw [← hEq12, ← houtEq12, hy0, hw0, ← hwOut1, show laneWeight4 lane4Zero = 0 from rfl]
      have hm := m4_mds_branch_lower x.b1 hb1nz
      omega
    · have hSumNz : lane4Add x.b0 x.b1 ≠ lane4Zero := fun hz => by
        rw [hz, show applyM4 lane4Zero = lane4Zero from by decide +kernel] at hout0Eq
        have : lane4Scale (Goldilocks.ofNat 2) lane4Zero = lane4Zero := by decide +kernel
        exact hy0 (hout0Eq.trans this)
      have hmSum : 5 ≤ laneWeight4 x.b0 + laneWeight4 x.b1 + laneWeight4 (applyMEStd x).b0 := by
        have hm := m4_mds_branch_lower (lane4Add x.b0 x.b1) hSumNz
        have hwOut0 : laneWeight4 (applyMEStd x).b0 = laneWeight4 (applyM4 (lane4Add x.b0 x.b1)) := by
          rw [hout0Eq, laneWeight4_scale_ne_zero h2nz]
        have hTri := laneWeight4_add_le x.b0 x.b1
        omega
      have hmB1 : 5 ≤ laneWeight4 x.b1 + laneWeight4 (applyMEStd x).b0 + laneWeight4 (applyMEStd x).b1 := by
        have hm := m4_mds_branch_lower x.b1 hb1nz
        have hwt4 : laneWeight4 (applyM4 x.b1) ≤
            laneWeight4 (applyMEStd x).b1 + laneWeight4 (applyMEStd x).b0 := by
          have h := congrArg laneWeight4 h4y1
          rw [laneWeight4_scale_ne_zero h4nz] at h
          have hTri := laneWeight4_sub_le (lane4Scale (Goldilocks.ofNat 2) (applyMEStd x).b1) (applyMEStd x).b0
          rw [laneWeight4_scale_ne_zero h2nz] at hTri
          omega
        omega
      have p0 := laneWeight4_pos_of_ne_zero hb0
      have p1 := laneWeight4_pos_of_ne_zero hb1nz
      have po1 := laneWeight4_pos_of_ne_zero hout1nz
      unfold stateWeight12
      rw [← hEq12, ← houtEq12]
      omega

/-- **Multi-Block Width-12 `M_E` Branch Bound (`poseidon2_me12std_multiblock_branch_ge_eight`)**:
    Whenever both input `x` and output `applyMEStd x` activate at least two 4-lane blocks,
    `8 ≤ stateWeight12 x + stateWeight12 (applyMEStd x)`. -/
theorem poseidon2_me12std_multiblock_branch_ge_eight (x : Poseidon2State12)
    (hIn : 2 ≤ activeBlocks12 x) (hOut : 2 ≤ activeBlocks12 (applyMEStd x)) :
    8 ≤ stateWeight12 x + stateWeight12 (applyMEStd x) := by
  by_cases h01 : x.b0 = x.b1
  · have hRotEq : (rot12 (rot12 x)).b1 = (rot12 (rot12 x)).b2 := h01
    have hIn' : 2 ≤ activeBlocks12 (rot12 (rot12 x)) := by
      rw [activeBlocks12_rot12, activeBlocks12_rot12]; exact hIn
    have hOut' : 2 ≤ activeBlocks12 (applyMEStd (rot12 (rot12 x))) := by
      rw [applyME_rot12, applyME_rot12, activeBlocks12_rot12, activeBlocks12_rot12]; exact hOut
    have hm := applyME_multiblock_b1_eq_b2 (rot12 (rot12 x)) hRotEq hIn' hOut'
    rw [stateWeight12_rot12, stateWeight12_rot12,
        applyME_rot12, applyME_rot12, stateWeight12_rot12, stateWeight12_rot12] at hm
    exact hm
  · by_cases h12 : x.b1 = x.b2
    · exact applyME_multiblock_b1_eq_b2 x h12 hIn hOut
    · by_cases h20 : x.b2 = x.b0
      · have hRotEq : (rot12 x).b1 = (rot12 x).b2 := h20
        have hIn' : 2 ≤ activeBlocks12 (rot12 x) := by
          rw [activeBlocks12_rot12]; exact hIn
        have hOut' : 2 ≤ activeBlocks12 (applyMEStd (rot12 x)) := by
          rw [applyME_rot12, activeBlocks12_rot12]; exact hOut
        have hm := applyME_multiblock_b1_eq_b2 (rot12 x) hRotEq hIn' hOut'
        rw [stateWeight12_rot12, applyME_rot12, stateWeight12_rot12] at hm
        exact hm
      · obtain ⟨hd01, hd12, hd20⟩ := applyME_block_diffs x
        have hn01 : lane4Sub x.b0 x.b1 ≠ lane4Zero := fun hz =>
          h01 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have hn12 : lane4Sub x.b1 x.b2 ≠ lane4Zero := fun hz =>
          h12 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have hn20 : lane4Sub x.b2 x.b0 ≠ lane4Zero := fun hz =>
          h20 ((lane4Sub_eq_zero_iff _ _).mp hz)
        have m01 := m4_mds_branch_lower (lane4Sub x.b0 x.b1) hn01
        have m12 := m4_mds_branch_lower (lane4Sub x.b1 x.b2) hn12
        have m20 := m4_mds_branch_lower (lane4Sub x.b2 x.b0) hn20
        rw [← hd01] at m01
        rw [← hd12] at m12
        rw [← hd20] at m20
        have t1 := laneWeight4_sub_le x.b0 x.b1
        have t2 := laneWeight4_sub_le x.b1 x.b2
        have t3 := laneWeight4_sub_le x.b2 x.b0
        have u1 := laneWeight4_sub_le (applyMEStd x).b0 (applyMEStd x).b1
        have u2 := laneWeight4_sub_le (applyMEStd x).b1 (applyMEStd x).b2
        have u3 := laneWeight4_sub_le (applyMEStd x).b2 (applyMEStd x).b0
        unfold stateWeight12
        omega

def me12BranchSevenWitness : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 3, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨goldilocksNegOne, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨goldilocksNegOne, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩

/-- **Exact Universal Width-12 `M_E` Branch Number = 7 (`poseidon2_me12std_branch_number_eq_seven`)**:
    Every nonzero 12-lane state satisfies `7 ≤ stateWeight12 x + stateWeight12 (applyMEStd x)`,
    and `me12BranchSevenWitness` attains `3 + 4 = 7`. -/
theorem poseidon2_me12std_branch_number_eq_seven :
    (∀ x : Poseidon2State12, x ≠ state12Zero →
      7 ≤ stateWeight12 x + stateWeight12 (applyMEStd x)) ∧
    me12BranchSevenWitness ≠ state12Zero ∧
    stateWeight12 me12BranchSevenWitness + stateWeight12 (applyMEStd me12BranchSevenWitness) = 7 := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  intro x hx
  have hInPos : 1 ≤ activeBlocks12 x := by
    unfold activeBlocks12
    by_cases h0 : x.b0 = lane4Zero <;>
      by_cases h1 : x.b1 = lane4Zero <;>
      by_cases h2 : x.b2 = lane4Zero
    · exact False.elim (hx (Poseidon2State12.ext h0 h1 h2))
    all_goals simp [h0, h1, h2]
  have hyNz : applyMEStd x ≠ state12Zero := fun hz => by
    apply hx
    have hInv := congrArg applyMEStdInv hz
    rw [applyMEStdInv_applyMEStd] at hInv
    exact hInv.trans (by decide +kernel)
  have hOutPos : 1 ≤ activeBlocks12 (applyMEStd x) := by
    unfold activeBlocks12
    by_cases h0 : (applyMEStd x).b0 = lane4Zero <;>
      by_cases h1 : (applyMEStd x).b1 = lane4Zero <;>
      by_cases h2 : (applyMEStd x).b2 = lane4Zero
    · exact False.elim (hyNz (Poseidon2State12.ext h0 h1 h2))
    all_goals simp [h0, h1, h2]
  by_cases hIn1 : activeBlocks12 x = 1
  · exact (poseidon2_me12std_single_block_branch_ge_seven x hIn1).1
  · by_cases hOut1 : activeBlocks12 (applyMEStd x) = 1
    · exact applyME_single_out_branch_ge_seven x hOut1
    · have h2In : 2 ≤ activeBlocks12 x := by omega
      have h2Out : 2 ≤ activeBlocks12 (applyMEStd x) := by omega
      have h8 := poseidon2_me12std_multiblock_branch_ge_eight x h2In h2Out
      omega

/-- Exact bilinear transpose laws for `applyMEStd` and symmetric `applyMI` (`M_I^T = M_I`),
    plus identical universal linear branch bound `≥ 7` for `applyMEStdTranspose`. -/
theorem poseidon2_me12std_and_mi12_linear_transpose_laws (x y : Poseidon2State12) :
    state12Dot (applyMEStd x) y = state12Dot x (applyMEStdTranspose y) ∧
    state12Dot (applyMI x) y = state12Dot x (applyMI y) ∧
    (y ≠ state12Zero → 7 ≤ stateWeight12 y + stateWeight12 (applyMEStdTranspose y)) := by
  have hwRev4 : ∀ b : Lane4, laneWeight4 (lane4Rev b) = laneWeight4 b := fun b => by
    unfold laneWeight4 lane4Rev; dsimp only; omega
  have hwRev12 : ∀ s : Poseidon2State12, stateWeight12 (state12Rev4 s) = stateWeight12 s := fun s => by
    unfold stateWeight12 state12Rev4; dsimp only; rw [hwRev4, hwRev4, hwRev4]
  refine ⟨?_, ?_, ?_⟩
  · unfold state12Dot applyMEStdTranspose state12Rev4 lane4Rev applyMEStd applyM4 lane4Add lane4Sum lane4Dot
    gold_cring
  · unfold state12Dot applyMI state12Sum lane4Sum lane4Dot
    gold_cring
  · intro hy
    have hRevNz : state12Rev4 y ≠ state12Zero := fun hz => by
      apply hy
      have hInv : state12Rev4 (state12Rev4 y) = y := by
        rcases y with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩; rfl
      rw [← hInv, hz]; rfl
    have hm := poseidon2_me12std_branch_number_eq_seven.1 (state12Rev4 y) hRevNz
    unfold applyMEStdTranspose
    rw [hwRev12]
    rw [hwRev12] at hm
    exact hm

private theorem stateWeight12_transpose4x3 (s : Poseidon2State12) :
    stateWeight12 (poseidon2Transpose4x3 s) = stateWeight12 s := by
  unfold stateWeight12 poseidon2Transpose4x3 laneWeight4; dsimp only; omega

private theorem stateWeight12_transpose3x4 (s : Poseidon2State12) :
    stateWeight12 (poseidon2Transpose3x4 s) = stateWeight12 s := by
  unfold stateWeight12 poseidon2Transpose3x4 laneWeight4; dsimp only; omega

/-- **Exact universal branch number `7` of the deployed `M_E = M_4 ⊗ P_3`
    (`poseidon2_me12_branch_number_eq_seven`)**: `applyME` is the lane transposition conjugate of
    `applyMEStd`, and lane transpositions preserve Hamming weight, so every nonzero 12-lane state
    satisfies `7 ≤ stateWeight12 x + stateWeight12 (applyME x)`; the transposed witness attains `7`. -/
theorem poseidon2_me12_branch_number_eq_seven :
    (∀ x : Poseidon2State12, x ≠ state12Zero →
      7 ≤ stateWeight12 x + stateWeight12 (applyME x)) ∧
    poseidon2Transpose3x4 me12BranchSevenWitness ≠ state12Zero ∧
    stateWeight12 (poseidon2Transpose3x4 me12BranchSevenWitness) +
      stateWeight12 (applyME (poseidon2Transpose3x4 me12BranchSevenWitness)) = 7 := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  intro x hx
  have hNz : poseidon2Transpose4x3 x ≠ state12Zero := fun hz => by
    apply hx; rw [← poseidon2Transpose34_43 x, hz]; rfl
  have hm := poseidon2_me12std_branch_number_eq_seven.1 (poseidon2Transpose4x3 x) hNz
  unfold applyME
  rw [stateWeight12_transpose3x4]
  rw [stateWeight12_transpose4x3] at hm
  exact hm

/-- Exact transpose of the deployed `applyME` with respect to the standard 12-lane dot product:
    the lane transpositions are permutation matrices, so `(T₃₄ · M · T₄₃)ᵀ = T₃₄ · Mᵀ · T₄₃`. -/
def applyMETranspose (s : Poseidon2State12) : Poseidon2State12 :=
  poseidon2Transpose3x4 (applyMEStdTranspose (poseidon2Transpose4x3 s))

/-- Bilinear transpose law for the deployed `applyME` and the universal linear branch bound `≥ 7`
    for `applyMETranspose`. -/
theorem poseidon2_me12_linear_transpose_laws (x y : Poseidon2State12) :
    state12Dot (applyME x) y = state12Dot x (applyMETranspose y) ∧
    (y ≠ state12Zero → 7 ≤ stateWeight12 y + stateWeight12 (applyMETranspose y)) := by
  refine ⟨?_, ?_⟩
  · unfold state12Dot applyMETranspose applyMEStdTranspose state12Rev4 lane4Rev applyME
      poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4 lane4Add lane4Sum lane4Dot
    gold_cring
  · intro hy
    have hNz : poseidon2Transpose4x3 y ≠ state12Zero := fun hz => by
      apply hy; rw [← poseidon2Transpose34_43 y, hz]; rfl
    have hm := (poseidon2_me12std_and_mi12_linear_transpose_laws state12Zero
      (poseidon2Transpose4x3 y)).2.2 hNz
    unfold applyMETranspose
    rw [stateWeight12_transpose3x4]
    rw [stateWeight12_transpose4x3] at hm
    exact hm

private theorem mi_lane_wt_ge_one (v : Int) (x s : Goldilocks) (hs : s ≠ Goldilocks.zero) :
    1 ≤ (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero then 0 else 1) := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    have hz : Goldilocks.add (Goldilocks.mul (goldOfInt v) Goldilocks.zero) s = s := by
      change CommRingOps.add (CommRingOps.mul (goldOfInt v) CommRingOps.zero) s = s
      rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    rw [hz]
    simp [hs]
  · simp [hx]

private theorem mi_lane1_wt_ge_one (x s : Goldilocks) (hs : s ≠ Goldilocks.zero) :
    1 ≤ (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add x s = Goldilocks.zero then 0 else 1) := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    have hz : Goldilocks.add Goldilocks.zero s = s := LawfulCommRing.zero_add s
    rw [hz]
    simp [hs]
  · simp [hx]

private theorem mi_lane_scaled_of_wt_le_one (v w : Int) (hvw : v * w = 1024)
    (x s : Goldilocks)
    (h1 : (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero then 0 else 1) ≤ 1) :
    Goldilocks.mul (goldOfInt 1024) x =
      Goldilocks.mul (goldOfInt (if x = Goldilocks.zero then 0 else -w)) s := by
  by_cases hx : x = Goldilocks.zero
  · subst hx
    simp only [↓reduceIte]
    change CommRingOps.mul (goldOfInt 1024) CommRingOps.zero = CommRingOps.mul CommRingOps.zero s
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul]
  · have hy : Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero := by
      by_cases hy0 : Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s = Goldilocks.zero
      · exact hy0
      · simp [hx, hy0] at h1
    simp only [hx, ↓reduceIte]
    have hMulW := congrArg (Goldilocks.mul (goldOfInt w)) hy
    rw [show Goldilocks.mul (goldOfInt w) Goldilocks.zero = Goldilocks.zero from
      LawfulCommRing.mul_zero _] at hMulW
    rw [← goldOfInt_nat x, ← goldOfInt_nat s] at hMulW ⊢
    simp only [goldOfInt_add, goldOfInt_mul] at hMulW ⊢
    have hSub : goldOfInt (w * (v * ↑x.val + ↑s.val)) = goldOfInt 0 := hMulW
    have hId : (1024 : Int) * ↑x.val = w * (v * ↑x.val + ↑s.val) + (-w) * ↑s.val := by
      have hvw' : w * v = 1024 := Int.mul_comm w v ▸ hvw
      have hCancel : w * ↑s.val + (-w) * ↑s.val = 0 := by
        rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]
      calc (1024 : Int) * ↑x.val = (w * v) * ↑x.val := by rw [hvw']
      _ = w * (v * ↑x.val) + 0 := by rw [Int.mul_assoc, Int.add_zero]
      _ = w * (v * ↑x.val) + (w * ↑s.val + (-w) * ↑s.val) := by rw [hCancel]
      _ = w * (v * ↑x.val + ↑s.val) + (-w) * ↑s.val := by rw [← Int.add_assoc, ← Int.mul_add]
    have hGoal : goldOfInt ((1024 : Int) * ↑x.val) =
        Goldilocks.add (goldOfInt (w * (v * ↑x.val + ↑s.val))) (goldOfInt ((-w) * ↑s.val)) := by
      rw [hId]
      exact (goldOfInt_add _ _).symm
    rw [hGoal, hSub]
    exact LawfulCommRing.zero_add _

private theorem zero_wt_congr {a b : Goldilocks} (h : a = b) :
    (if a = Goldilocks.zero then 0 else 1) = (if b = Goldilocks.zero then 0 else 1) := by
  subst h; rfl

private theorem mi_lane1_scaled_of_wt_le_one (x s : Goldilocks)
    (h1 : (if x = Goldilocks.zero then 0 else 1) +
      (if Goldilocks.add x s = Goldilocks.zero then 0 else 1) ≤ 1) :
    Goldilocks.mul (goldOfInt 1024) x =
      Goldilocks.mul (goldOfInt (if x = Goldilocks.zero then 0 else -1024)) s := by
  have hMul1 : Goldilocks.mul (goldOfInt 1) x = x := by
    change CommRingOps.mul CommRingOps.one x = x
    exact LawfulCommRing.one_mul x
  apply mi_lane_scaled_of_wt_le_one 1 1024 rfl x s
  rw [zero_wt_congr (show Goldilocks.add (Goldilocks.mul (goldOfInt 1) x) s =
      Goldilocks.add x s by rw [hMul1])]
  exact h1

private theorem mi_u0_bounds (x : Goldilocks) :
    0 ≤ (if x = Goldilocks.zero then (0 : Int) else -(-16)) ∧
    (if x = Goldilocks.zero then (0 : Int) else -(-16)) ≤ 16 := by
  if hx : x = Goldilocks.zero then
    simp only [hx, ↓reduceIte]; exact ⟨Int.le_refl 0, by decide +kernel⟩
  else
    simp only [hx, ↓reduceIte]; exact ⟨by decide +kernel, Int.le_refl 16⟩

private theorem sum12_pairs_le_one
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
     c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Nat)
    (h12 : ((a0 + a1 + a2 + a3) + (a4 + a5 + a6 + a7) + (a8 + a9 + a10 + a11)) +
           ((c0 + c1 + c2 + c3) + (c4 + c5 + c6 + c7) + (c8 + c9 + c10 + c11)) ≤ 12)
    (g0 : 1 ≤ a0 + c0) (g1 : 1 ≤ a1 + c1) (g2 : 1 ≤ a2 + c2) (g3 : 1 ≤ a3 + c3)
    (g4 : 1 ≤ a4 + c4) (g5 : 1 ≤ a5 + c5) (g6 : 1 ≤ a6 + c6) (g7 : 1 ≤ a7 + c7)
    (g8 : 1 ≤ a8 + c8) (g9 : 1 ≤ a9 + c9) (g10 : 1 ≤ a10 + c10) (g11 : 1 ≤ a11 + c11) :
    (a0 + c0 ≤ 1 ∧ a1 + c1 ≤ 1 ∧ a2 + c2 ≤ 1 ∧ a3 + c3 ≤ 1) ∧
    (a4 + c4 ≤ 1 ∧ a5 + c5 ≤ 1 ∧ a6 + c6 ≤ 1 ∧ a7 + c7 ≤ 1) ∧
    (a8 + c8 ≤ 1 ∧ a9 + c9 ≤ 1 ∧ a10 + c10 ≤ 1 ∧ a11 + c11 ≤ 1) := by
  exact ⟨⟨by omega, by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega, by omega⟩,
         ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem mi_u_bounds
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : Int)
    (b0 : 0 ≤ u0 ∧ u0 ≤ 16)
    (b1 : -1024 ≤ u1 ∧ u1 ≤ 0) (b2 : -512 ≤ u2 ∧ u2 ≤ 0) (b3 : -256 ≤ u3 ∧ u3 ≤ 0)
    (b4 : -128 ≤ u4 ∧ u4 ≤ 0) (b5 : -64 ≤ u5 ∧ u5 ≤ 0) (b6 : -32 ≤ u6 ∧ u6 ≤ 0)
    (b7 : -16 ≤ u7 ∧ u7 ≤ 0) (b8 : -8 ≤ u8 ∧ u8 ≤ 0) (b9 : -4 ≤ u9 ∧ u9 ≤ 0)
    (b10 : -2 ≤ u10 ∧ u10 ≤ 0) (b11 : -1 ≤ u11 ∧ u11 ≤ 0) :
    let U := u0 + u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10 + u11
    512 ≤ 1024 - U ∧ 1024 - U < (goldilocksPrime : Int) := by
  intro U
  dsimp only [U]
  simp only [goldilocksPrime]
  exact ⟨by omega, by omega⟩

private theorem ite_nonpos_bounds (p : Prop) [hDec : Decidable p] (k : Int) (hk : k ≤ 0) :
    k ≤ (if p then (0 : Int) else k) ∧ (if p then (0 : Int) else k) ≤ 0 := by
  cases hDec with
  | isFalse _ => exact ⟨Int.le_refl k, hk⟩
  | isTrue _ => exact ⟨hk, Int.le_refl 0⟩

/-- **Exact Nonzero-Sum `M_I` Branch Number = 13 (`poseidon2_mi12_nonzero_sum_branch_eq_thirteen`)**:
    1. Whenever `state12Sum x ≠ 0`, `13 ≤ stateWeight12 x + stateWeight12 (applyMI x)`
       (proven via `v_0 = -64, v_1..v_11 = 2^(i-1)` forcing `1008 ≤ 1024 - Σ_{i ∈ S} (-1024 / v_i) ≤ 3071 < p`).
    2. Every single-lane partial-round difference `⟨⟨Δ, 0, 0, 0⟩, 0, 0⟩` with `Δ ≠ 0` achieves
       full 12-lane diffusion `stateWeight12 (applyMI x) = 12` and attains `1 + 12 = 13`.
    3. Across ALL nonzero `x ≠ state12Zero` (including zero-sum states), `4 ≤ stateWeight12 x + stateWeight12 (applyMI x)`. -/
theorem poseidon2_mi12_nonzero_sum_branch_eq_thirteen :
    (∀ x : Poseidon2State12, state12Sum x ≠ Goldilocks.zero →
      13 ≤ stateWeight12 x + stateWeight12 (applyMI x)) ∧
    (∀ Δ : Goldilocks, Δ ≠ Goldilocks.zero →
      let x : Poseidon2State12 :=
        ⟨⟨Δ, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, lane4Zero, lane4Zero⟩
      stateWeight12 (applyMI x) = 12 ∧
      stateWeight12 x + stateWeight12 (applyMI x) = 13) ∧
    (∀ x : Poseidon2State12, x ≠ state12Zero →
      4 ≤ stateWeight12 x + stateWeight12 (applyMI x)) := by
  have hBranch13 : ∀ x : Poseidon2State12, state12Sum x ≠ Goldilocks.zero →
      13 ≤ stateWeight12 x + stateWeight12 (applyMI x) := by
    intro x hs
    by_cases h13 : 13 ≤ stateWeight12 x + stateWeight12 (applyMI x)
    · exact h13
    · exfalso
      let s := state12Sum x
      have hMIEq : ∀ (st : Poseidon2State12) (sm : Goldilocks), state12Sum st = sm →
          stateWeight12 (applyMI st) =
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt (-64)) st.b0.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add st.b0.x1 sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) sm = Goldilocks.zero then 0 else 1)) +
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) sm = Goldilocks.zero then 0 else 1)) +
            ((if Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) sm = Goldilocks.zero then 0 else 1) +
             (if Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) sm = Goldilocks.zero then 0 else 1)) := by
        intro st sm hsm; subst hsm; rfl
      have hLe12 : stateWeight12 x + stateWeight12 (applyMI x) ≤ 12 := by omega
      rw [hMIEq x s rfl] at hLe12
      unfold stateWeight12 laneWeight4 at hLe12
      have g0 := mi_lane_wt_ge_one (-64) x.b0.x0 s hs
      have g1 := mi_lane1_wt_ge_one x.b0.x1 s hs
      have g2 := mi_lane_wt_ge_one 2 x.b0.x2 s hs
      have g3 := mi_lane_wt_ge_one 4 x.b0.x3 s hs
      have g4 := mi_lane_wt_ge_one 8 x.b1.x0 s hs
      have g5 := mi_lane_wt_ge_one 16 x.b1.x1 s hs
      have g6 := mi_lane_wt_ge_one 32 x.b1.x2 s hs
      have g7 := mi_lane_wt_ge_one 64 x.b1.x3 s hs
      have g8 := mi_lane_wt_ge_one 128 x.b2.x0 s hs
      have g9 := mi_lane_wt_ge_one 256 x.b2.x1 s hs
      have g10 := mi_lane_wt_ge_one 512 x.b2.x2 s hs
      have g11 := mi_lane_wt_ge_one 1024 x.b2.x3 s hs
      have hPairs := sum12_pairs_le_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        hLe12 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
      have e0 := mi_lane_scaled_of_wt_le_one (-64) (-16) rfl x.b0.x0 s hPairs.1.1
      have e1 := mi_lane1_scaled_of_wt_le_one x.b0.x1 s hPairs.1.2.1
      have e2 := mi_lane_scaled_of_wt_le_one 2 512 rfl x.b0.x2 s hPairs.1.2.2.1
      have e3 := mi_lane_scaled_of_wt_le_one 4 256 rfl x.b0.x3 s hPairs.1.2.2.2
      have e4 := mi_lane_scaled_of_wt_le_one 8 128 rfl x.b1.x0 s hPairs.2.1.1
      have e5 := mi_lane_scaled_of_wt_le_one 16 64 rfl x.b1.x1 s hPairs.2.1.2.1
      have e6 := mi_lane_scaled_of_wt_le_one 32 32 rfl x.b1.x2 s hPairs.2.1.2.2.1
      have e7 := mi_lane_scaled_of_wt_le_one 64 16 rfl x.b1.x3 s hPairs.2.1.2.2.2
      have e8 := mi_lane_scaled_of_wt_le_one 128 8 rfl x.b2.x0 s hPairs.2.2.1
      have e9 := mi_lane_scaled_of_wt_le_one 256 4 rfl x.b2.x1 s hPairs.2.2.2.1
      have e10 := mi_lane_scaled_of_wt_le_one 512 2 rfl x.b2.x2 s hPairs.2.2.2.2.1
      have e11 := mi_lane_scaled_of_wt_le_one 1024 1 rfl x.b2.x3 s hPairs.2.2.2.2.2
      let u0 : Int := if x.b0.x0 = Goldilocks.zero then 0 else -(-16)
      let u1 : Int := if x.b0.x1 = Goldilocks.zero then 0 else -1024
      let u2 : Int := if x.b0.x2 = Goldilocks.zero then 0 else -512
      let u3 : Int := if x.b0.x3 = Goldilocks.zero then 0 else -256
      let u4 : Int := if x.b1.x0 = Goldilocks.zero then 0 else -128
      let u5 : Int := if x.b1.x1 = Goldilocks.zero then 0 else -64
      let u6 : Int := if x.b1.x2 = Goldilocks.zero then 0 else -32
      let u7 : Int := if x.b1.x3 = Goldilocks.zero then 0 else -16
      let u8 : Int := if x.b2.x0 = Goldilocks.zero then 0 else -8
      let u9 : Int := if x.b2.x1 = Goldilocks.zero then 0 else -4
      let u10 : Int := if x.b2.x2 = Goldilocks.zero then 0 else -2
      let u11 : Int := if x.b2.x3 = Goldilocks.zero then 0 else -1
      let U : Int := u0 + u1 + u2 + u3 + u4 + u5 + u6 + u7 + u8 + u9 + u10 + u11
      have hSum1024 : Goldilocks.mul (goldOfInt 1024) s = Goldilocks.mul (goldOfInt U) s := by
        have hDist : Goldilocks.mul (goldOfInt 1024) s =
            Goldilocks.add (Goldilocks.add
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b0.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b0.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b0.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b0.x3)))
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b1.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b1.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b1.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b1.x3))))
              (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b2.x0)
                                              (Goldilocks.mul (goldOfInt 1024) x.b2.x1))
                              (Goldilocks.add (Goldilocks.mul (goldOfInt 1024) x.b2.x2)
                                              (Goldilocks.mul (goldOfInt 1024) x.b2.x3))) := by
          unfold s state12Sum lane4Sum
          gold_cring
        rw [hDist, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
        change Goldilocks.add (Goldilocks.add
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt u0) s)
                                          (Goldilocks.mul (goldOfInt u1) s))
                          (Goldilocks.add (Goldilocks.mul (goldOfInt u2) s)
                                          (Goldilocks.mul (goldOfInt u3) s)))
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt u4) s)
                                          (Goldilocks.mul (goldOfInt u5) s))
                          (Goldilocks.add (Goldilocks.mul (goldOfInt u6) s)
                                          (Goldilocks.mul (goldOfInt u7) s))))
          (Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt u8) s)
                                          (Goldilocks.mul (goldOfInt u9) s))
                          (Goldilocks.add (Goldilocks.mul (goldOfInt u10) s)
                                          (Goldilocks.mul (goldOfInt u11) s))) =
          Goldilocks.mul (goldOfInt U) s
        rw [← goldOfInt_nat s]
        simp only [goldOfInt_add, goldOfInt_mul]
        congr 1
        dsimp only [U]
        simp only [Int.add_mul, Int.add_assoc]
      have hDiffZero : Goldilocks.mul (goldOfInt (1024 - U)) s = Goldilocks.zero := by
        have hSub := congrArg (fun z => Goldilocks.sub z (Goldilocks.mul (goldOfInt U) s)) hSum1024
        rw [show Goldilocks.sub (Goldilocks.mul (goldOfInt U) s) (Goldilocks.mul (goldOfInt U) s) =
            Goldilocks.zero from LawfulCommRing.sub_self _] at hSub
        have hFactor : Goldilocks.sub (Goldilocks.mul (goldOfInt 1024) s)
            (Goldilocks.mul (goldOfInt U) s) = Goldilocks.mul (goldOfInt (1024 - U)) s := by
          rw [← goldOfInt_nat s]
          simp only [goldOfInt_sub, goldOfInt_mul]
          congr 1
          exact (Int.sub_mul 1024 U _).symm
        rwa [hFactor] at hSub
      have b0 := mi_u0_bounds x.b0.x0
      have b1 := ite_nonpos_bounds (x.b0.x1 = Goldilocks.zero) (-1024) (by decide +kernel)
      have b2 := ite_nonpos_bounds (x.b0.x2 = Goldilocks.zero) (-512) (by decide +kernel)
      have b3 := ite_nonpos_bounds (x.b0.x3 = Goldilocks.zero) (-256) (by decide +kernel)
      have b4 := ite_nonpos_bounds (x.b1.x0 = Goldilocks.zero) (-128) (by decide +kernel)
      have b5 := ite_nonpos_bounds (x.b1.x1 = Goldilocks.zero) (-64) (by decide +kernel)
      have b6 := ite_nonpos_bounds (x.b1.x2 = Goldilocks.zero) (-32) (by decide +kernel)
      have b7 := ite_nonpos_bounds (x.b1.x3 = Goldilocks.zero) (-16) (by decide +kernel)
      have b8 := ite_nonpos_bounds (x.b2.x0 = Goldilocks.zero) (-8) (by decide +kernel)
      have b9 := ite_nonpos_bounds (x.b2.x1 = Goldilocks.zero) (-4) (by decide +kernel)
      have b10 := ite_nonpos_bounds (x.b2.x2 = Goldilocks.zero) (-2) (by decide +kernel)
      have b11 := ite_nonpos_bounds (x.b2.x3 = Goldilocks.zero) (-1) (by decide +kernel)
      have hBounds : 512 ≤ 1024 - U ∧ 1024 - U < (goldilocksPrime : Int) :=
        mi_u_bounds u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
      have hNonneg : 0 ≤ 1024 - U := Int.le_trans (by decide +kernel : (0 : Int) ≤ 512) hBounds.1
      have hPos : 1024 - U ≠ 0 := by
        intro hEq0
        have : (512 : Int) ≤ 0 := hEq0 ▸ hBounds.1
        exact absurd this (by decide +kernel)
      have hCoeffNz : goldOfInt (1024 - U) ≠ Goldilocks.zero := by
        intro hz
        have hv := congrArg (fun g => (g.val : Int)) hz
        rw [goldOfInt_val] at hv
        change (1024 - U) % (goldilocksPrime : Int) = 0 at hv
        rw [Int.emod_eq_of_lt hNonneg hBounds.2] at hv
        exact hPos hv
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hDiffZero with h1 | h2
      · exact hCoeffNz h1
      · exact hs h2
  refine ⟨hBranch13, ?_, ?_⟩
  · intro Δ hΔ
    let x : Poseidon2State12 :=
      ⟨⟨Δ, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, lane4Zero, lane4Zero⟩
    change stateWeight12 (applyMI x) = 12 ∧ stateWeight12 x + stateWeight12 (applyMI x) = 13
    have hSumEq : state12Sum x = Δ := by
      unfold x state12Sum lane4Sum lane4Zero
      gold_cring
    have hxWt : stateWeight12 x = 1 := by
      unfold x stateWeight12 laneWeight4 lane4Zero
      dsimp only
      simp only [hΔ, ↓reduceIte]
    have h13 := hBranch13 x (hSumEq.symm ▸ hΔ)
    have hMax : stateWeight12 (applyMI x) ≤ 12 := by
      have l0 := laneWeight4_le_four (applyMI x).b0
      have l1 := laneWeight4_le_four (applyMI x).b1
      have l2 := laneWeight4_le_four (applyMI x).b2
      unfold stateWeight12; omega
    exact ⟨by omega, by omega⟩
  · intro x hx
    by_cases hs : state12Sum x = Goldilocks.zero
    · have hAdd0 : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a :=
        LawfulCommRing.add_zero
      have hWtEq : stateWeight12 (applyMI x) = stateWeight12 x := by
        unfold applyMI stateWeight12 laneWeight4
        rw [hs]
        dsimp only
        rw [zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _),
            zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _),
            zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _),
            zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _), zero_wt_congr (hAdd0 _)]
        rw [coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel),
            coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel),
            coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel),
            coord_wt_mul_nz (by decide +kernel), coord_wt_mul_nz (by decide +kernel)]
      by_cases hw1 : 2 ≤ stateWeight12 x
      · omega
      · exfalso
        have hSingle : ∀ (a b c d : Goldilocks),
            (if a = Goldilocks.zero then 0 else 1) + (if b = Goldilocks.zero then 0 else 1) +
            (if c = Goldilocks.zero then 0 else 1) + (if d = Goldilocks.zero then 0 else 1) ≤ 1 →
            lane4Sum ⟨a, b, c, d⟩ = Goldilocks.zero →
            ⟨a, b, c, d⟩ = lane4Zero := by
          intro a b c d hw hsum
          by_cases ha : a = Goldilocks.zero <;>
            by_cases hb : b = Goldilocks.zero <;>
            by_cases hc : c = Goldilocks.zero <;>
            by_cases hd : d = Goldilocks.zero
          · exact Lane4.ext ha hb hc hd
          · subst ha hb hc; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero)
                (Goldilocks.add Goldilocks.zero d) = d := by gold_cring
            exact False.elim (hd (this ▸ hsum))
          · subst ha hb hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero)
                (Goldilocks.add c Goldilocks.zero) = c := by gold_cring
            exact False.elim (hc (this ▸ hsum))
          · simp [ha, hb, hc, hd] at hw
          · subst ha hc hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero b)
                (Goldilocks.add Goldilocks.zero Goldilocks.zero) = b := by gold_cring
            exact False.elim (hb (this ▸ hsum))
          · simp [ha, hb, hc, hd] at hw
          · simp [ha, hb, hc, hd] at hw
          · simp [ha, hb, hc, hd] at hw
          · subst hb hc hd; unfold lane4Sum at hsum; dsimp only at hsum
            have : Goldilocks.add (Goldilocks.add a Goldilocks.zero)
                (Goldilocks.add Goldilocks.zero Goldilocks.zero) = a := by gold_cring
            exact False.elim (ha (this ▸ hsum))
          all_goals simp [ha, hb, hc, hd] at hw
        unfold stateWeight12 at hw1
        unfold state12Sum at hs
        by_cases hb0 : x.b0 = lane4Zero <;>
          by_cases hb1 : x.b1 = lane4Zero <;>
          by_cases hb2 : x.b2 = lane4Zero
        · exact hx (Poseidon2State12.ext hb0 hb1 hb2)
        · rw [hb0, hb1] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b2 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero Goldilocks.zero) (lane4Sum x.b2) =
                lane4Sum x.b2 := by gold_cring
            exact this ▸ hs
          exact hb2 (hSingle x.b2.x0 x.b2.x1 x.b2.x2 x.b2.x3
            ((show ∀ n : Nat, ¬ 2 ≤ 0 + 0 + n → n ≤ 1 by omega) _ hw1) hs')
        · rw [hb0, hb2] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b1 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add Goldilocks.zero (lane4Sum x.b1)) Goldilocks.zero =
                lane4Sum x.b1 := by gold_cring
            exact this ▸ hs
          exact hb1 (hSingle x.b1.x0 x.b1.x1 x.b1.x2 x.b1.x3
            ((show ∀ n : Nat, ¬ 2 ≤ 0 + n + 0 → n ≤ 1 by omega) _ hw1) hs')
        · have p1 := laneWeight4_pos_of_ne_zero hb1
          have p2 := laneWeight4_pos_of_ne_zero hb2
          omega
        · rw [hb1, hb2] at hw1 hs
          rw [show laneWeight4 lane4Zero = 0 from rfl] at hw1
          rw [show lane4Sum lane4Zero = Goldilocks.zero from rfl] at hs
          have hs' : lane4Sum x.b0 = Goldilocks.zero := by
            have : Goldilocks.add (Goldilocks.add (lane4Sum x.b0) Goldilocks.zero) Goldilocks.zero =
                lane4Sum x.b0 := by gold_cring
            exact this ▸ hs
          exact hb0 (hSingle x.b0.x0 x.b0.x1 x.b0.x2 x.b0.x3
            ((show ∀ n : Nat, ¬ 2 ≤ n + 0 + 0 → n ≤ 1 by omega) _ hw1) hs')
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p2 := laneWeight4_pos_of_ne_zero hb2
          omega
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p1 := laneWeight4_pos_of_ne_zero hb1
          omega
        · have p0 := laneWeight4_pos_of_ne_zero hb0
          have p1 := laneWeight4_pos_of_ne_zero hb1
          omega
    · have h13 := hBranch13 x hs
      omega

/-! ### Merz–Rodríguez García (`2026/306`) `(X, -X, 0)` Subspace Round-Skipping & `M_4 ⊗ P_3` + Jive Mitigation -/

theorem sbox7_odd (u : Goldilocks) :
    sbox7 (Goldilocks.sub Goldilocks.zero u) = Goldilocks.sub Goldilocks.zero (sbox7 u) := by
  unfold sbox7
  gold_cring

/-- **Subspace round-skipping is blocked by the deployed `M_E = M_4 ⊗ P_3` and weighted compression
    (`poseidon2_kronecker_swap_kills_subspace_skip`, Merz–Rodríguez García `2026/306` §6)**:
    1. `applyME` maps `(X, -X, 0)` injectively into `b2` (`det = 128 = 2^7`) and `(0, X, -X)`
       injectively into `b0` (`|det| = 112 = 16 · 7`): only `X = 0` leaves the capacity/output block
       inactive. The block-circulant factor `applyMEStd = P_3 ⊗ M_4` alone does not have this property.
    2. `poseidon2WeightedFeedForward` (`in0 + 2 · in1 + 4 · tweak`) is injective in `X` on all three
       difference subspaces `(U0 + X, -X, U2)`, `(U0, U1 + X, -X)`, and `(U0 + X, U1, -X)`.
    Invertibility and the branch number of `applyME` are `applyMEInv_applyME`, `applyME_applyMEInv`
    and `poseidon2_me12_branch_number_eq_seven`. -/
theorem poseidon2_kronecker_swap_kills_subspace_skip :
    (∀ X : Lane4,
      (applyME ⟨X, lane4Neg X, lane4Zero⟩).b2 = lane4Zero ↔ X = lane4Zero) ∧
    (∀ X : Lane4,
      (applyME ⟨lane4Zero, X, lane4Neg X⟩).b0 = lane4Zero ↔ X = lane4Zero) ∧
    (∀ U0 U1 U2 X Y : Lane4,
      (poseidon2WeightedFeedForward ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
       poseidon2WeightedFeedForward ⟨lane4Add U0 Y, lane4Neg Y, U2⟩ → X = Y) ∧
      (poseidon2WeightedFeedForward ⟨U0, lane4Add U1 X, lane4Neg X⟩ =
       poseidon2WeightedFeedForward ⟨U0, lane4Add U1 Y, lane4Neg Y⟩ → X = Y) ∧
      (poseidon2WeightedFeedForward ⟨lane4Add U0 X, U1, lane4Neg X⟩ =
       poseidon2WeightedFeedForward ⟨lane4Add U0 Y, U1, lane4Neg Y⟩ → X = Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    constructor
    · intro hb2
      let y := (applyME ⟨X, lane4Neg X, lane4Zero⟩).b2
      have hy0 : y.x0 = Goldilocks.zero := congrArg Lane4.x0 hb2
      have hy1 : y.x1 = Goldilocks.zero := congrArg Lane4.x1 hb2
      have hy2 : y.x2 = Goldilocks.zero := congrArg Lane4.x2 hb2
      have hy3 : y.x3 = Goldilocks.zero := congrArg Lane4.x3 hb2
      have c0 : Goldilocks.mul (goldOfInt 128) X.x0 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.x0) (Goldilocks.mul (goldOfInt 28) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-4)) y.x2) (Goldilocks.mul (goldOfInt (-4)) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c1 : Goldilocks.mul (goldOfInt 128) X.x1 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-24)) y.x0) (Goldilocks.mul (goldOfInt (-1)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 23) y.x2) (Goldilocks.mul (goldOfInt (-9)) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c2 : Goldilocks.mul (goldOfInt 128) X.x2 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-8)) y.x0) (Goldilocks.mul (goldOfInt (-11)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-3)) y.x2) (Goldilocks.mul (goldOfInt 29) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c3 : Goldilocks.mul (goldOfInt 128) X.x3 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-104)) y.x0) (Goldilocks.mul (goldOfInt 1) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-23)) y.x2) (Goldilocks.mul (goldOfInt 9) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      rw [hy0, hy1, hy2, hy3] at c0 c1 c2 c3
      exact Lane4.ext
        (minor_scalar_cancel 128 (by decide +kernel) X.x0 (c0.trans (by decide +kernel)))
        (minor_scalar_cancel 128 (by decide +kernel) X.x1 (c1.trans (by decide +kernel)))
        (minor_scalar_cancel 128 (by decide +kernel) X.x2 (c2.trans (by decide +kernel)))
        (minor_scalar_cancel 128 (by decide +kernel) X.x3 (c3.trans (by decide +kernel)))
    · intro hX; subst hX; decide
  · intro X
    constructor
    · intro hb0
      let y := (applyME ⟨lane4Zero, X, lane4Neg X⟩).b0
      have hy0 : y.x0 = Goldilocks.zero := congrArg Lane4.x0 hb0
      have hy1 : y.x1 = Goldilocks.zero := congrArg Lane4.x1 hb0
      have hy2 : y.x2 = Goldilocks.zero := congrArg Lane4.x2 hb0
      have hy3 : y.x3 = Goldilocks.zero := congrArg Lane4.x3 hb0
      have c0 : Goldilocks.mul (goldOfInt 112) X.x0 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 45) y.x0) (Goldilocks.mul (goldOfInt 5) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-11)) y.x2) (Goldilocks.mul (goldOfInt (-8)) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c1 : Goldilocks.mul (goldOfInt 112) X.x1 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-31)) y.x0) (Goldilocks.mul (goldOfInt 9) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 25) y.x2) (Goldilocks.mul (goldOfInt 8) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c2 : Goldilocks.mul (goldOfInt 112) X.x2 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt 53) y.x0) (Goldilocks.mul (goldOfInt (-19)) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt (-3)) y.x2) (Goldilocks.mul (goldOfInt 8) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      have c3 : Goldilocks.mul (goldOfInt 112) X.x3 =
          Goldilocks.add (Goldilocks.add (Goldilocks.mul (goldOfInt (-110)) y.x0) (Goldilocks.mul (goldOfInt 50) y.x1))
            (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.x2) (Goldilocks.mul (goldOfInt 32) y.x3)) := by
        unfold y applyME poseidon2Transpose3x4 poseidon2Transpose4x3 applyMEStd applyM4
          lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
        dsimp only
        rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
        simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
          goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
        congr 1; omega
      rw [hy0, hy1, hy2, hy3] at c0 c1 c2 c3
      exact Lane4.ext
        (minor_scalar_cancel 112 (by decide +kernel) X.x0 (c0.trans (by decide +kernel)))
        (minor_scalar_cancel 112 (by decide +kernel) X.x1 (c1.trans (by decide +kernel)))
        (minor_scalar_cancel 112 (by decide +kernel) X.x2 (c2.trans (by decide +kernel)))
        (minor_scalar_cancel 112 (by decide +kernel) X.x3 (c3.trans (by decide +kernel)))
    · intro hX; subst hX; decide
  · intro U0 U1 U2 X Y
    have cancelScaleNz : ∀ (c : Goldilocks) (hc : c ≠ Goldilocks.zero) (d : Lane4),
        lane4Scale c d = lane4Zero → d = lane4Zero := by
      intro c hc d hSc
      have coordNz : ∀ a : Goldilocks, Goldilocks.mul c a = Goldilocks.zero → a = Goldilocks.zero := by
        intro a hm
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hm with h1 | h2
        · exact False.elim (hc h1)
        · exact h2
      exact Lane4.ext
        (coordNz d.x0 (congrArg Lane4.x0 hSc))
        (coordNz d.x1 (congrArg Lane4.x1 hSc))
        (coordNz d.x2 (congrArg Lane4.x2 hSc))
        (coordNz d.x3 (congrArg Lane4.x3 hSc))
    refine ⟨?_, ?_, ?_⟩
    · intro hEq
      have hDiff : lane4Sub Y X =
          lane4Sub (poseidon2WeightedFeedForward ⟨lane4Add U0 X, lane4Neg X, U2⟩)
                   (poseidon2WeightedFeedForward ⟨lane4Add U0 Y, lane4Neg Y, U2⟩) := by
        unfold poseidon2WeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp hDiff).symm
    · intro hEq
      have hDiff : lane4Scale (Goldilocks.ofNat 2) (lane4Sub Y X) =
          lane4Sub (poseidon2WeightedFeedForward ⟨U0, lane4Add U1 X, lane4Neg X⟩)
                   (poseidon2WeightedFeedForward ⟨U0, lane4Add U1 Y, lane4Neg Y⟩) := by
        unfold poseidon2WeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp (cancelScaleNz (Goldilocks.ofNat 2) (by decide +kernel) _ hDiff)).symm
    · intro hEq
      have hDiff : lane4Scale (Goldilocks.ofNat 3) (lane4Sub Y X) =
          lane4Sub (poseidon2WeightedFeedForward ⟨lane4Add U0 X, U1, lane4Neg X⟩)
                   (poseidon2WeightedFeedForward ⟨lane4Add U0 Y, U1, lane4Neg Y⟩) := by
        unfold poseidon2WeightedFeedForward lane4Add lane4Scale lane4Neg lane4Sub lane4Zero
        apply Lane4.ext <;> gold_cring
      rw [hEq, (lane4Sub_eq_zero_iff _ _).mpr rfl] at hDiff
      exact ((lane4Sub_eq_zero_iff Y X).mp (cancelScaleNz (Goldilocks.ofNat 3) (by decide +kernel) _ hDiff)).symm

/-! ## 9. `sbox7` Differential Uniformity `≤ 6` & Width-12 `(R_F = 8, R_P = 22)` Wide-Trail Bounds -/

/-- Degree-6 polynomial `(X + Δ)^7 - X^7 - δ` (`length = 7 = 6 + 1`) over `Goldilocks`. -/
def sbox7DiffPoly (Δ δ : Goldilocks) : List Goldilocks :=
  let Δ2 := Goldilocks.mul Δ Δ
  let Δ3 := Goldilocks.mul Δ2 Δ
  let Δ4 := Goldilocks.mul Δ2 Δ2
  let Δ5 := Goldilocks.mul Δ4 Δ
  let Δ6 := Goldilocks.mul Δ3 Δ3
  let Δ7 := Goldilocks.mul Δ3 Δ4
  [Goldilocks.sub Δ7 δ,
   Goldilocks.mul (CRing.natCast 7) Δ6,
   Goldilocks.mul (CRing.natCast 21) Δ5,
   Goldilocks.mul (CRing.natCast 35) Δ4,
   Goldilocks.mul (CRing.natCast 35) Δ3,
   Goldilocks.mul (CRing.natCast 21) Δ2,
   Goldilocks.mul (CRing.natCast 7) Δ]

theorem evalCoeffs_sbox7DiffPoly (Δ δ x : Goldilocks) :
    RoundPoly.evalCoeffs (sbox7DiffPoly Δ δ) x =
      Goldilocks.sub (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x)) δ := by
  simp only [sbox7DiffPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, sbox7]
  gold_cring

/-- **Exact `sbox7` Differential Uniformity Bound (`sbox7_differential_uniformity_le_six`)**:
    For every nonzero input difference `Δ ≠ 0`, output difference `δ`, and duplicate-free set
    `S : List Goldilocks`, the equation `sbox7 (x + Δ) - sbox7 x = δ` has at most `6` solutions in `S`. -/
theorem sbox7_differential_uniformity_le_six (Δ δ : Goldilocks) (hΔ : Δ ≠ Goldilocks.zero)
    (S : List Goldilocks) (hNodup : S.Nodup) :
    (S.filter (fun x =>
      decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ))).length ≤ 6 := by
  let p := sbox7DiffPoly Δ δ
  have hLen : p.length ≤ 6 + 1 := Nat.le_refl 7
  let c5040 : Goldilocks :=
    Goldilocks.mul (CRing.natCast 7)
      (Goldilocks.mul (CRing.natCast 8) (Goldilocks.mul (CRing.natCast 9) (CRing.natCast 10)))
  have h6Diff : ∀ (Δ' δ' : Goldilocks),
      let f := RoundPoly.evalCoeffs (sbox7DiffPoly Δ' δ')
      Goldilocks.add
        (Goldilocks.sub
          (Goldilocks.add
            (Goldilocks.sub
              (Goldilocks.add
                (Goldilocks.sub (f (CRing.natCast 6))
                  (Goldilocks.mul (CRing.natCast 6) (f (CRing.natCast 5))))
                (Goldilocks.mul (CRing.natCast 15) (f (CRing.natCast 4))))
              (Goldilocks.mul (CRing.natCast 20) (f (CRing.natCast 3))))
            (Goldilocks.mul (CRing.natCast 15) (f (CRing.natCast 2))))
          (Goldilocks.mul (CRing.natCast 6) (f (CRing.natCast 1))))
        (f (CRing.natCast 0)) =
      Goldilocks.mul c5040 Δ' := by
    intro Δ' δ'
    dsimp only [c5040]
    simp only [sbox7DiffPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
    gold_cring
  have h5040Nz : Goldilocks.mul c5040 Δ ≠ Goldilocks.zero := fun hz => by
    have hc : c5040 ≠ Goldilocks.zero := fun h => absurd (congrArg Goldilocks.val h) (by decide +kernel)
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with h1 | h2
    · exact hc h1
    · exact hΔ h2
  have hExistsNz : ∃ x₀ : Goldilocks, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero := by
    by_cases z0 : RoundPoly.evalCoeffs p (CRing.natCast 0) = Goldilocks.zero
    · by_cases z1 : RoundPoly.evalCoeffs p (CRing.natCast 1) = Goldilocks.zero
      · by_cases z2 : RoundPoly.evalCoeffs p (CRing.natCast 2) = Goldilocks.zero
        · by_cases z3 : RoundPoly.evalCoeffs p (CRing.natCast 3) = Goldilocks.zero
          · by_cases z4 : RoundPoly.evalCoeffs p (CRing.natCast 4) = Goldilocks.zero
            · by_cases z5 : RoundPoly.evalCoeffs p (CRing.natCast 5) = Goldilocks.zero
              · by_cases z6 : RoundPoly.evalCoeffs p (CRing.natCast 6) = Goldilocks.zero
                · exfalso
                  have hId := h6Diff Δ δ
                  dsimp only at hId
                  change _ = _ at hId
                  rw [z0, z1, z2, z3, z4, z5, z6] at hId
                  have hLHS : Goldilocks.add
                      (Goldilocks.sub
                        (Goldilocks.add
                          (Goldilocks.sub
                            (Goldilocks.add
                              (Goldilocks.sub Goldilocks.zero
                                (Goldilocks.mul (CRing.natCast 6) Goldilocks.zero))
                              (Goldilocks.mul (CRing.natCast 15) Goldilocks.zero))
                            (Goldilocks.mul (CRing.natCast 20) Goldilocks.zero))
                          (Goldilocks.mul (CRing.natCast 15) Goldilocks.zero))
                        (Goldilocks.mul (CRing.natCast 6) Goldilocks.zero))
                      Goldilocks.zero = Goldilocks.zero := by gold_cring
                  exact h5040Nz (hId.symm.trans hLHS)
                · exact ⟨CRing.natCast 6, z6⟩
              · exact ⟨CRing.natCast 5, z5⟩
            · exact ⟨CRing.natCast 4, z4⟩
          · exact ⟨CRing.natCast 3, z3⟩
        · exact ⟨CRing.natCast 2, z2⟩
      · exact ⟨CRing.natCast 1, z1⟩
    · exact ⟨CRing.natCast 0, z0⟩
  have hRoots := RoundPoly.roots_nodup_length_le 6 p S hNodup hLen hExistsNz
  have hFiltEq : S.filter (fun x =>
      decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ)) =
      S.filter (fun x => decide (RoundPoly.evalCoeffs p x = CommRingOps.zero)) := by
    congr 1
    funext x
    dsimp only [p]
    rw [evalCoeffs_sbox7DiffPoly]
    change decide (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x) = δ) =
      decide (Goldilocks.sub (Goldilocks.sub (sbox7 (Goldilocks.add x Δ)) (sbox7 x)) δ = Goldilocks.zero)
    simp only [gold_sub_zero_iff]
  rwa [hFiltEq]

private theorem state12Sub_eq_zero_iff (a b : Poseidon2State12) :
    state12Sub a b = state12Zero ↔ a = b := by
  constructor
  · intro h
    exact Poseidon2State12.ext
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b0 h))
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b1 h))
      ((lane4Sub_eq_zero_iff _ _).mp (congrArg Poseidon2State12.b2 h))
  · intro h; subst h
    exact Poseidon2State12.ext
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)
      ((lane4Sub_eq_zero_iff _ _).mpr rfl)

private theorem applyMEStd_sub (a b : Poseidon2State12) :
    state12Sub (applyMEStd a) (applyMEStd b) = applyMEStd (state12Sub a b) := by
  unfold applyMEStd applyM4 state12Sub lane4Add lane4Sub lane4Sum
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring

private theorem applyME_sub (a b : Poseidon2State12) :
    state12Sub (applyME a) (applyME b) = applyME (state12Sub a b) := by
  have ht : poseidon2Transpose4x3 (state12Sub a b) =
      state12Sub (poseidon2Transpose4x3 a) (poseidon2Transpose4x3 b) := rfl
  have hu (x y : Poseidon2State12) : state12Sub (poseidon2Transpose3x4 x) (poseidon2Transpose3x4 y) =
      poseidon2Transpose3x4 (state12Sub x y) := rfl
  unfold applyME
  rw [hu, applyMEStd_sub, ht]

theorem sboxState12_preserves_differential_activity (a b rc : Poseidon2State12) :
    stateWeight12 (state12Sub (sboxState12 (state12Add a rc)) (sboxState12 (state12Add b rc))) =
      stateWeight12 (state12Sub a b) := by
  unfold stateWeight12 state12Sub sboxState12 state12Add
  dsimp only
  rw [sbox7_preserves_differential_activity,
      sbox7_preserves_differential_activity,
      sbox7_preserves_differential_activity]

/-- Two successive width-12 external rounds activate at least `7` S-boxes on any `a ≠ b`. -/
theorem poseidon2_width12_two_ext_rounds_active_ge_seven
    (a b rc : Poseidon2State12) (hne : a ≠ b) :
    7 ≤ stateWeight12 (state12Sub a b) +
      stateWeight12 (state12Sub (externalRound rc a) (externalRound rc b)) := by
  let d := state12Sub (sboxState12 (state12Add a rc)) (sboxState12 (state12Add b rc))
  have hdNz : d ≠ state12Zero := fun hz => by
    have hw0 : stateWeight12 d = 0 := by rw [hz]; rfl
    rw [sboxState12_preserves_differential_activity] at hw0
    have hdab : state12Sub a b ≠ state12Zero := fun hz' =>
      hne ((state12Sub_eq_zero_iff _ _).mp hz')
    unfold stateWeight12 at hw0
    by_cases h0 : (state12Sub a b).b0 = lane4Zero <;>
      by_cases h1 : (state12Sub a b).b1 = lane4Zero <;>
      by_cases h2 : (state12Sub a b).b2 = lane4Zero
    · exact hdab (Poseidon2State12.ext h0 h1 h2)
    · have := laneWeight4_pos_of_ne_zero h2; omega
    · have := laneWeight4_pos_of_ne_zero h1; omega
    · have := laneWeight4_pos_of_ne_zero h1; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
    · have := laneWeight4_pos_of_ne_zero h0; omega
  have hm := poseidon2_me12_branch_number_eq_seven.1 d hdNz
  rw [sboxState12_preserves_differential_activity] at hm
  unfold externalRound
  rwa [applyME_sub]

def countExtRoundsActive : List Poseidon2State12 → Poseidon2State12 → Poseidon2State12 → Nat
  | [], _, _ => 0
  | rc :: rcs, a, b =>
    stateWeight12 (state12Sub a b) +
      countExtRoundsActive rcs (externalRound rc a) (externalRound rc b)

def countIntRoundsActive : List Goldilocks → Poseidon2State12 → Poseidon2State12 → Nat
  | [], _, _ => 0
  | rc :: rcs, a, b =>
    (if a.b0.x0 = b.b0.x0 then 0 else 1) +
      countIntRoundsActive rcs (internalRound rc a) (internalRound rc b)

/-- Exact count of active degree-7 S-boxes across all `8` external + `22` internal rounds (`118` total S-boxes)
    of the deployed width-12 `poseidon2Perm12` trajectory on `(a, b)`. -/
def poseidon2Perm12ActiveSboxes (a b : Poseidon2State12) : Nat :=
  let s0a := applyME a
  let s0b := applyME b
  let s1a := runRounds externalRound poseidon2InitialExtConsts s0a
  let s1b := runRounds externalRound poseidon2InitialExtConsts s0b
  let s2a := runRounds internalRound poseidon2InternalConsts s1a
  let s2b := runRounds internalRound poseidon2InternalConsts s1b
  countExtRoundsActive poseidon2InitialExtConsts s0a s0b +
    countIntRoundsActive poseidon2InternalConsts s1a s1b +
    countExtRoundsActive poseidon2TerminalExtConsts s2a s2b

private theorem externalRound_ne_of_ne (rc a b : Poseidon2State12) (hne : a ≠ b) :
    externalRound rc a ≠ externalRound rc b := fun hEq => by
  apply hne
  have hInv := congrArg (externalRoundInv rc) hEq
  rwa [(poseidon2_full_round_two_sided_inverse rc a).1,
       (poseidon2_full_round_two_sided_inverse rc b).1] at hInv

private theorem runRounds_int_ne_of_ne :
    ∀ (rcs : List Goldilocks) (a b : Poseidon2State12),
      a ≠ b → runRounds internalRound rcs a ≠ runRounds internalRound rcs b
  | [], a, b, hne => hne
  | rc :: rcs, a, b, hne => by
    apply runRounds_int_ne_of_ne rcs
    intro hEq
    apply hne
    have hInv := congrArg (internalRoundInv rc) hEq
    rwa [(poseidon2_partial_round_two_sided_inverse rc a).1,
         (poseidon2_partial_round_two_sided_inverse rc b).1] at hInv

private theorem countExtRoundsActive_four (c0 c1 c2 c3 a b : Poseidon2State12) (hne : a ≠ b) :
    14 ≤ countExtRoundsActive [c0, c1, c2, c3] a b := by
  let a1 := externalRound c0 a
  let b1 := externalRound c0 b
  let a2 := externalRound c1 a1
  let b2 := externalRound c1 b1
  have hne2 : a2 ≠ b2 := externalRound_ne_of_ne c1 a1 b1 (externalRound_ne_of_ne c0 a b hne)
  have w01 := poseidon2_width12_two_ext_rounds_active_ge_seven a b c0 hne
  have w23 := poseidon2_width12_two_ext_rounds_active_ge_seven a2 b2 c2 hne2
  dsimp only [a1, b1, a2, b2] at w23
  simp only [countExtRoundsActive]
  omega

private theorem pow_lt_pow_of_lt_base (u v k : Nat) (hu : 1 ≤ u) (huv : u < v) (hk : 1 ≤ k) :
    u ^ k < v ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  induction m with
  | zero => simpa using huv
  | succ m ih =>
    have ih' := ih (by omega)
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ih' (by omega))
      (Nat.mul_le_mul_left _ (Nat.le_of_lt huv))

/-- Actual activity lower bound plus separate arithmetic inequalities. Every distinct input
    pair activates at least 28 S-boxes. Interpreting `6^active / p^active` as a differential
    trajectory probability needs an appropriate conditional-distribution experiment: a
    realized trail of a fixed width-12 permutation under uniform inputs has mass at least
    `p^-12`, which rules out that product as a universal bound for those events. Linear trail
    contributions are signed Fourier quantities, not such events, and can multiply without
    stochastic independence. Here neither the component character-sum estimate underlying
    `36/p` nor the Fourier trail/hull connection is formalized. -/
theorem poseidon2_width12_active_sboxes_ge_28_and_exponent_arithmetic :
    (∀ a b : Poseidon2State12, a ≠ b → 28 ≤ poseidon2Perm12ActiveSboxes a b) ∧
    (∀ active : Nat, 28 ≤ active →
      6 ^ active * 2 ^ 256 < goldilocksPrime ^ active ∧
      36 ^ active * 2 ^ 256 < goldilocksPrime ^ active ∧
      6 ^ active * 2 ^ 1680 < goldilocksPrime ^ active) := by
  refine ⟨?_, ?_⟩
  · intro a b hne
    have hs0 : applyME a ≠ applyME b := fun hEq => by
      apply hne
      have hInv := congrArg applyMEInv hEq
      rwa [applyMEInv_applyME, applyMEInv_applyME] at hInv
    have hInitConsts : poseidon2InitialExtConsts =
        [poseidon2ExtRoundConst 0 0, poseidon2ExtRoundConst 0 1,
         poseidon2ExtRoundConst 0 2, poseidon2ExtRoundConst 0 3] := rfl
    have hTermConsts : poseidon2TerminalExtConsts =
        [poseidon2ExtRoundConst 2 0, poseidon2ExtRoundConst 2 1,
         poseidon2ExtRoundConst 2 2, poseidon2ExtRoundConst 2 3] := rfl
    have hInit14 : 14 ≤ countExtRoundsActive poseidon2InitialExtConsts (applyME a) (applyME b) := by
      rw [hInitConsts]
      exact countExtRoundsActive_four _ _ _ _ _ _ hs0
    have hs1 : runRounds externalRound poseidon2InitialExtConsts (applyME a) ≠
        runRounds externalRound poseidon2InitialExtConsts (applyME b) := by
      rw [hInitConsts]
      simp only [runRounds]
      exact externalRound_ne_of_ne _ _ _ (externalRound_ne_of_ne _ _ _
        (externalRound_ne_of_ne _ _ _ (externalRound_ne_of_ne _ _ _ hs0)))
    have hs2 : runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME a)) ≠
        runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME b)) :=
      runRounds_int_ne_of_ne poseidon2InternalConsts _ _ hs1
    have hTerm14 : 14 ≤ countExtRoundsActive poseidon2TerminalExtConsts
        (runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME a)))
        (runRounds internalRound poseidon2InternalConsts
          (runRounds externalRound poseidon2InitialExtConsts (applyME b))) := by
      rw [hTermConsts]
      exact countExtRoundsActive_four _ _ _ _ _ _ hs2
    unfold poseidon2Perm12ActiveSboxes
    dsimp only
    omega
  · intro active hAct
    have h36Base : 36 * 2 ^ 57 < goldilocksPrime := by decide +kernel
    have h6Base : 6 * 2 ^ 60 < goldilocksPrime := by decide +kernel
    have hMulPow : ∀ (a b k : Nat), (a * b) ^ k = a ^ k * b ^ k := fun a b k => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
        ac_rfl
    have hPow36 : 36 ^ active * 2 ^ (57 * active) < goldilocksPrime ^ active := by
      have hLt := pow_lt_pow_of_lt_base (36 * 2 ^ 57) goldilocksPrime active (by decide +kernel) h36Base (by omega)
      rwa [hMulPow, ← Nat.pow_mul] at hLt
    have hPow6 : 6 ^ active * 2 ^ (60 * active) < goldilocksPrime ^ active := by
      have hLt := pow_lt_pow_of_lt_base (6 * 2 ^ 60) goldilocksPrime active (by decide +kernel) h6Base (by omega)
      rwa [hMulPow, ← Nat.pow_mul] at hLt
    have h57 : 256 ≤ 57 * active := by omega
    have h60 : 1680 ≤ 60 * active := by omega
    have h256Le : 2 ^ 256 ≤ 2 ^ (57 * active) :=
      @Nat.pow_le_pow_right 2 (Nat.zero_lt_succ 1) 256 (57 * active) h57
    have h1680Le : 2 ^ 1680 ≤ 2 ^ (60 * active) :=
      @Nat.pow_le_pow_right 2 (Nat.zero_lt_succ 1) 1680 (60 * active) h60
    have h36_256 : 36 ^ active * 2 ^ 256 < goldilocksPrime ^ active :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h256Le) hPow36
    have h6_1680 : 6 ^ active * 2 ^ 1680 < goldilocksPrime ^ active :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h1680Le) hPow6
    have h6Le36All : ∀ n : Nat, 6 ^ n ≤ 36 ^ n := fun n => by
      induction n with
      | zero => decide
      | succ k ih =>
        rw [Nat.pow_succ, Nat.pow_succ]
        exact Nat.mul_le_mul ih (by decide +kernel)
    have h6Le36 : 6 ^ active ≤ 36 ^ active := h6Le36All active
    exact ⟨Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h6Le36) h36_256, h36_256, h6_1680⟩


/-! ## 10. Width-12 Symbolic Circuit, Univariate Saturation & CICO-1 Macaulay / Bézout Bounds -/

structure SymbolicLane4 where
  x0 : PoseidonExpr
  x1 : PoseidonExpr
  x2 : PoseidonExpr
  x3 : PoseidonExpr

structure SymbolicState12 where
  b0 : SymbolicLane4
  b1 : SymbolicLane4
  b2 : SymbolicLane4

def SymbolicLane4.eval (v : Nat → Goldilocks) (b : SymbolicLane4) : Lane4 :=
  ⟨b.x0.eval v, b.x1.eval v, b.x2.eval v, b.x3.eval v⟩

def SymbolicState12.eval (v : Nat → Goldilocks) (s : SymbolicState12) : Poseidon2State12 :=
  ⟨s.b0.eval v, s.b1.eval v, s.b2.eval v⟩

def SymbolicLane4.maxDeg (b : SymbolicLane4) : Nat :=
  max (max b.x0.degree b.x1.degree) (max b.x2.degree b.x3.degree)

def SymbolicState12.maxDeg (s : SymbolicState12) : Nat :=
  max (max s.b0.maxDeg s.b1.maxDeg) s.b2.maxDeg

def symbolicLane4Add (a b : SymbolicLane4) : SymbolicLane4 :=
  ⟨.add a.x0 b.x0, .add a.x1 b.x1, .add a.x2 b.x2, .add a.x3 b.x3⟩

def symbolicLane4Const (c : Lane4) : SymbolicLane4 :=
  ⟨.constant c.x0, .constant c.x1, .constant c.x2, .constant c.x3⟩

def symbolicApplyM4 (b : SymbolicLane4) : SymbolicLane4 :=
  let s : PoseidonExpr := .add (.add b.x0 b.x1) (.add b.x2 b.x3)
  let c2 : PoseidonExpr := .constant (Goldilocks.ofNat 2)
  ⟨.add s (.add b.x0 (.mul c2 b.x1)),
   .add s (.add b.x1 (.mul c2 b.x2)),
   .add s (.add b.x2 (.mul c2 b.x3)),
   .add s (.add b.x3 (.mul c2 b.x0))⟩

def symbolicTranspose4x3 (s : SymbolicState12) : SymbolicState12 :=
  ⟨⟨s.b0.x0, s.b0.x3, s.b1.x2, s.b2.x1⟩,
   ⟨s.b0.x1, s.b1.x0, s.b1.x3, s.b2.x2⟩,
   ⟨s.b0.x2, s.b1.x1, s.b2.x0, s.b2.x3⟩⟩

def symbolicTranspose3x4 (s : SymbolicState12) : SymbolicState12 :=
  ⟨⟨s.b0.x0, s.b1.x0, s.b2.x0, s.b0.x1⟩,
   ⟨s.b1.x1, s.b2.x1, s.b0.x2, s.b1.x2⟩,
   ⟨s.b2.x2, s.b0.x3, s.b1.x3, s.b2.x3⟩⟩

def symbolicME12Std (st : SymbolicState12) : SymbolicState12 :=
  let y0 := symbolicApplyM4 st.b0
  let y1 := symbolicApplyM4 st.b1
  let y2 := symbolicApplyM4 st.b2
  let s := symbolicLane4Add (symbolicLane4Add y0 y1) y2
  ⟨symbolicLane4Add y0 s, symbolicLane4Add y1 s, symbolicLane4Add y2 s⟩

def symbolicME12 (st : SymbolicState12) : SymbolicState12 :=
  symbolicTranspose3x4 (symbolicME12Std (symbolicTranspose4x3 st))

def symbolicMI12WithSum (st : SymbolicState12) (s : PoseidonExpr) : SymbolicState12 :=
  ⟨⟨.add (.mul (.constant (goldOfInt (-64))) st.b0.x0) s,
    .add st.b0.x1 s,
    .add (.mul (.constant (goldOfInt 2)) st.b0.x2) s,
    .add (.mul (.constant (goldOfInt 4)) st.b0.x3) s⟩,
   ⟨.add (.mul (.constant (goldOfInt 8)) st.b1.x0) s,
    .add (.mul (.constant (goldOfInt 16)) st.b1.x1) s,
    .add (.mul (.constant (goldOfInt 32)) st.b1.x2) s,
    .add (.mul (.constant (goldOfInt 64)) st.b1.x3) s⟩,
   ⟨.add (.mul (.constant (goldOfInt 128)) st.b2.x0) s,
    .add (.mul (.constant (goldOfInt 256)) st.b2.x1) s,
    .add (.mul (.constant (goldOfInt 512)) st.b2.x2) s,
    .add (.mul (.constant (goldOfInt 1024)) st.b2.x3) s⟩⟩

def symbolicMI12 (st : SymbolicState12) : SymbolicState12 :=
  let sum4 (b : SymbolicLane4) : PoseidonExpr := .add (.add b.x0 b.x1) (.add b.x2 b.x3)
  symbolicMI12WithSum st (.add (.add (sum4 st.b0) (sum4 st.b1)) (sum4 st.b2))

def symbolicExtRound12 (rc : Poseidon2State12) (st : SymbolicState12) : SymbolicState12 :=
  let sbox4 (b : SymbolicLane4) (c : Lane4) : SymbolicLane4 :=
    ⟨(PoseidonExpr.add b.x0 (.constant c.x0)).seventh,
     (PoseidonExpr.add b.x1 (.constant c.x1)).seventh,
     (PoseidonExpr.add b.x2 (.constant c.x2)).seventh,
     (PoseidonExpr.add b.x3 (.constant c.x3)).seventh⟩
  symbolicME12 ⟨sbox4 st.b0 rc.b0, sbox4 st.b1 rc.b1, sbox4 st.b2 rc.b2⟩

def symbolicIntRound12 (rc : Goldilocks) (st : SymbolicState12) : SymbolicState12 :=
  let x0' := (PoseidonExpr.add st.b0.x0 (.constant rc)).seventh
  symbolicMI12 ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2⟩

def symbolicPerm12 (st : SymbolicState12) : SymbolicState12 :=
  let s0 := symbolicME12 st
  let s1 := runRounds symbolicExtRound12 poseidon2InitialExtConsts s0
  let s2 := runRounds symbolicIntRound12 poseidon2InternalConsts s1
  runRounds symbolicExtRound12 poseidon2TerminalExtConsts s2

private theorem symbolicME12_eval (v : Nat → Goldilocks) (st : SymbolicState12) :
    (symbolicME12 st).eval v = applyME (st.eval v) := rfl

private theorem symbolicMI12_eval (v : Nat → Goldilocks) (st : SymbolicState12) :
    (symbolicMI12 st).eval v = applyMI (st.eval v) := rfl

private theorem symbolicExtRound12_eval (v : Nat → Goldilocks) (rc : Poseidon2State12)
    (st : SymbolicState12) :
    (symbolicExtRound12 rc st).eval v = externalRound rc (st.eval v) := rfl

private theorem symbolicIntRound12_eval (v : Nat → Goldilocks) (rc : Goldilocks)
    (st : SymbolicState12) :
    (symbolicIntRound12 rc st).eval v = internalRound rc (st.eval v) := rfl

private theorem runRounds_symbolic_eval {α : Type} (v : Nat → Goldilocks)
    (sStep : α → SymbolicState12 → SymbolicState12)
    (cStep : α → Poseidon2State12 → Poseidon2State12)
    (hStep : ∀ c st, (sStep c st).eval v = cStep c (st.eval v)) :
    ∀ (cs : List α) (st : SymbolicState12),
      (runRounds sStep cs st).eval v = runRounds cStep cs (st.eval v)
  | [], _ => rfl
  | c :: cs, st => by
    simp only [runRounds, runRounds_symbolic_eval v sStep cStep hStep cs (sStep c st), hStep]

private theorem max_le_of_le {a b k : Nat} (ha : a ≤ k) (hb : b ≤ k) : max a b ≤ k := by omega
private theorem le_of_max_le_left {a b k : Nat} (h : max a b ≤ k) : a ≤ k := by omega
private theorem le_of_max_le_right {a b k : Nat} (h : max a b ≤ k) : b ≤ k := by omega

private theorem symbolicLane4Add_maxDeg_le (a b : SymbolicLane4) (k : Nat)
    (ha : a.maxDeg ≤ k) (hb : b.maxDeg ≤ k) : (symbolicLane4Add a b).maxDeg ≤ k := by
  unfold SymbolicLane4.maxDeg at ha hb
  unfold symbolicLane4Add SymbolicLane4.maxDeg
  dsimp only [PoseidonExpr.degree]
  omega

private theorem symbolicApplyM4_maxDeg_le (b : SymbolicLane4) (k : Nat)
    (hb : b.maxDeg ≤ k) : (symbolicApplyM4 b).maxDeg ≤ k := by
  unfold SymbolicLane4.maxDeg at hb
  have h0 : b.x0.degree ≤ k := by omega
  have h1 : b.x1.degree ≤ k := by omega
  have h2 : b.x2.degree ≤ k := by omega
  have h3 : b.x3.degree ≤ k := by omega
  have hs : (PoseidonExpr.add (.add b.x0 b.x1) (.add b.x2 b.x3)).degree ≤ k := by
    dsimp only [PoseidonExpr.degree]; omega
  unfold symbolicApplyM4 SymbolicLane4.maxDeg
  dsimp only
  apply max_le_of_le <;> apply max_le_of_le <;> (dsimp only [PoseidonExpr.degree]; omega)

private theorem symbolicState12_coord_degrees {st : SymbolicState12} {k : Nat} (h : st.maxDeg ≤ k) :
    ((st.b0.x0.degree ≤ k ∧ st.b0.x1.degree ≤ k) ∧ (st.b0.x2.degree ≤ k ∧ st.b0.x3.degree ≤ k)) ∧
    ((st.b1.x0.degree ≤ k ∧ st.b1.x1.degree ≤ k) ∧ (st.b1.x2.degree ≤ k ∧ st.b1.x3.degree ≤ k)) ∧
    ((st.b2.x0.degree ≤ k ∧ st.b2.x1.degree ≤ k) ∧ (st.b2.x2.degree ≤ k ∧ st.b2.x3.degree ≤ k)) := by
  have lane : ∀ b : SymbolicLane4, b.maxDeg ≤ k →
      (b.x0.degree ≤ k ∧ b.x1.degree ≤ k) ∧ (b.x2.degree ≤ k ∧ b.x3.degree ≤ k) := fun b hb =>
    ⟨⟨le_of_max_le_left (le_of_max_le_left hb), le_of_max_le_right (le_of_max_le_left hb)⟩,
     ⟨le_of_max_le_left (le_of_max_le_right hb), le_of_max_le_right (le_of_max_le_right hb)⟩⟩
  exact ⟨lane _ (le_of_max_le_left (le_of_max_le_left h)),
    lane _ (le_of_max_le_right (le_of_max_le_left h)), lane _ (le_of_max_le_right h)⟩

private theorem symbolicState12_maxDeg_le_of_coords {a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : PoseidonExpr}
    {k : Nat} (ha : (a0.degree ≤ k ∧ a1.degree ≤ k) ∧ (a2.degree ≤ k ∧ a3.degree ≤ k))
    (hb : (b0.degree ≤ k ∧ b1.degree ≤ k) ∧ (b2.degree ≤ k ∧ b3.degree ≤ k))
    (hc : (c0.degree ≤ k ∧ c1.degree ≤ k) ∧ (c2.degree ≤ k ∧ c3.degree ≤ k)) :
    (SymbolicState12.mk ⟨a0, a1, a2, a3⟩ ⟨b0, b1, b2, b3⟩ ⟨c0, c1, c2, c3⟩).maxDeg ≤ k :=
  max_le_of_le
    (max_le_of_le (max_le_of_le (max_le_of_le ha.1.1 ha.1.2) (max_le_of_le ha.2.1 ha.2.2))
      (max_le_of_le (max_le_of_le hb.1.1 hb.1.2) (max_le_of_le hb.2.1 hb.2.2)))
    (max_le_of_le (max_le_of_le hc.1.1 hc.1.2) (max_le_of_le hc.2.1 hc.2.2))

private theorem symbolicTranspose4x3_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicTranspose4x3 st).maxDeg ≤ k := by
  obtain ⟨⟨⟨h00, h01⟩, h02, h03⟩, ⟨⟨h10, h11⟩, h12, h13⟩, ⟨h20, h21⟩, h22, h23⟩ :=
    symbolicState12_coord_degrees h
  exact symbolicState12_maxDeg_le_of_coords ⟨⟨h00, h03⟩, h12, h21⟩ ⟨⟨h01, h10⟩, h13, h22⟩
    ⟨⟨h02, h11⟩, h20, h23⟩

private theorem symbolicTranspose3x4_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicTranspose3x4 st).maxDeg ≤ k := by
  obtain ⟨⟨⟨h00, h01⟩, h02, h03⟩, ⟨⟨h10, h11⟩, h12, h13⟩, ⟨h20, h21⟩, h22, h23⟩ :=
    symbolicState12_coord_degrees h
  exact symbolicState12_maxDeg_le_of_coords ⟨⟨h00, h10⟩, h20, h01⟩ ⟨⟨h11, h21⟩, h02, h12⟩
    ⟨⟨h22, h03⟩, h13, h23⟩

private theorem symbolicME12Std_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicME12Std st).maxDeg ≤ k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ k := le_of_max_le_right (le_of_max_le_left h)
  have hb2 : st.b2.maxDeg ≤ k := le_of_max_le_right h
  have hy0 := symbolicApplyM4_maxDeg_le st.b0 k hb0
  have hy1 := symbolicApplyM4_maxDeg_le st.b1 k hb1
  have hy2 := symbolicApplyM4_maxDeg_le st.b2 k hb2
  have hs := symbolicLane4Add_maxDeg_le _ _ k (symbolicLane4Add_maxDeg_le _ _ k hy0 hy1) hy2
  unfold symbolicME12Std SymbolicState12.maxDeg
  exact max_le_of_le
    (max_le_of_le (symbolicLane4Add_maxDeg_le _ _ k hy0 hs) (symbolicLane4Add_maxDeg_le _ _ k hy1 hs))
    (symbolicLane4Add_maxDeg_le _ _ k hy2 hs)

private theorem symbolicME12_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicME12 st).maxDeg ≤ k :=
  symbolicTranspose3x4_maxDeg_le _ k
    (symbolicME12Std_maxDeg_le _ k (symbolicTranspose4x3_maxDeg_le st k h))

private theorem symbolicMI12WithSum_maxDeg_le (st : SymbolicState12) (s : PoseidonExpr) (k : Nat)
    (h : st.maxDeg ≤ k) (hs : s.degree ≤ k) :
    (symbolicMI12WithSum st s).maxDeg ≤ k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ k := le_of_max_le_right (le_of_max_le_left h)
  have hb2 : st.b2.maxDeg ≤ k := le_of_max_le_right h
  have hDegMul : ∀ (c : Goldilocks) (e : PoseidonExpr), e.degree ≤ k →
      (PoseidonExpr.add (.mul (.constant c) e) s).degree ≤ k := fun _ _ he => by
    dsimp only [PoseidonExpr.degree]; omega
  have hDegAdd : ∀ (e : PoseidonExpr), e.degree ≤ k →
      (PoseidonExpr.add e s).degree ≤ k := fun _ he => by
    dsimp only [PoseidonExpr.degree]; omega
  have h00 : st.b0.x0.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb0; omega
  have h01 : st.b0.x1.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb0; omega
  have h02 : st.b0.x2.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb0; omega
  have h03 : st.b0.x3.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb0; omega
  have h10 : st.b1.x0.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb1; omega
  have h11 : st.b1.x1.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb1; omega
  have h12 : st.b1.x2.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb1; omega
  have h13 : st.b1.x3.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb1; omega
  have h20 : st.b2.x0.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb2; omega
  have h21 : st.b2.x1.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb2; omega
  have h22 : st.b2.x2.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb2; omega
  have h23 : st.b2.x3.degree ≤ k := by unfold SymbolicLane4.maxDeg at hb2; omega
  unfold symbolicMI12WithSum SymbolicState12.maxDeg SymbolicLane4.maxDeg
  exact max_le_of_le
    (max_le_of_le
      (max_le_of_le (max_le_of_le (hDegMul _ _ h00) (hDegAdd _ h01)) (max_le_of_le (hDegMul _ _ h02) (hDegMul _ _ h03)))
      (max_le_of_le (max_le_of_le (hDegMul _ _ h10) (hDegMul _ _ h11)) (max_le_of_le (hDegMul _ _ h12) (hDegMul _ _ h13))))
    (max_le_of_le (max_le_of_le (hDegMul _ _ h20) (hDegMul _ _ h21)) (max_le_of_le (hDegMul _ _ h22) (hDegMul _ _ h23)))

private theorem symbolicMI12_maxDeg_le (st : SymbolicState12) (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicMI12 st).maxDeg ≤ k := by
  have hb0 : st.b0.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hb1 : st.b1.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hb2 : st.b2.maxDeg ≤ k := by unfold SymbolicState12.maxDeg at h; omega
  have hs0 : (PoseidonExpr.add (.add st.b0.x0 st.b0.x1) (.add st.b0.x2 st.b0.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb0; dsimp only [PoseidonExpr.degree]; omega
  have hs1 : (PoseidonExpr.add (.add st.b1.x0 st.b1.x1) (.add st.b1.x2 st.b1.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb1; dsimp only [PoseidonExpr.degree]; omega
  have hs2 : (PoseidonExpr.add (.add st.b2.x0 st.b2.x1) (.add st.b2.x2 st.b2.x3)).degree ≤ k := by
    unfold SymbolicLane4.maxDeg at hb2; dsimp only [PoseidonExpr.degree]; omega
  exact symbolicMI12WithSum_maxDeg_le st _ k h (max_le_of_le (max_le_of_le hs0 hs1) hs2)

private theorem sbox4_maxDeg_le (b : SymbolicLane4) (c : Lane4) (k : Nat) (hb : b.maxDeg ≤ k) :
    (SymbolicLane4.mk
      (PoseidonExpr.add b.x0 (.constant c.x0)).seventh
      (PoseidonExpr.add b.x1 (.constant c.x1)).seventh
      (PoseidonExpr.add b.x2 (.constant c.x2)).seventh
      (PoseidonExpr.add b.x3 (.constant c.x3)).seventh).maxDeg ≤ 7 * k := by
  unfold SymbolicLane4.maxDeg at hb ⊢
  dsimp only
  simp only [symbolic_sbox7_degree, PoseidonExpr.degree, Nat.max_zero]
  omega

private theorem symbolicExtRound12_maxDeg_le (rc : Poseidon2State12) (st : SymbolicState12)
    (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicExtRound12 rc st).maxDeg ≤ 7 * k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 := sbox4_maxDeg_le st.b0 rc.b0 k (le_of_max_le_left (le_of_max_le_left h))
  have hb1 := sbox4_maxDeg_le st.b1 rc.b1 k (le_of_max_le_right (le_of_max_le_left h))
  have hb2 := sbox4_maxDeg_le st.b2 rc.b2 k (le_of_max_le_right h)
  unfold symbolicExtRound12
  dsimp only
  exact symbolicME12_maxDeg_le _ (7 * k) (max_le_of_le (max_le_of_le hb0 hb1) hb2)

private theorem symbolicIntRound12_maxDeg_le (rc : Goldilocks) (st : SymbolicState12)
    (k : Nat) (h : st.maxDeg ≤ k) :
    (symbolicIntRound12 rc st).maxDeg ≤ 7 * k := by
  unfold SymbolicState12.maxDeg at h
  have hb0 : st.b0.maxDeg ≤ k := le_of_max_le_left (le_of_max_le_left h)
  have hb1 : st.b1.maxDeg ≤ 7 * k := by
    have := le_of_max_le_right (le_of_max_le_left h); omega
  have hb2 : st.b2.maxDeg ≤ 7 * k := by
    have := le_of_max_le_right h; omega
  have hb0' : (SymbolicLane4.mk (PoseidonExpr.add st.b0.x0 (.constant rc)).seventh
      st.b0.x1 st.b0.x2 st.b0.x3).maxDeg ≤ 7 * k := by
    unfold SymbolicLane4.maxDeg at hb0 ⊢
    dsimp only
    simp only [symbolic_sbox7_degree, PoseidonExpr.degree, Nat.max_zero]
    omega
  unfold symbolicIntRound12
  dsimp only
  exact symbolicMI12_maxDeg_le _ (7 * k) (max_le_of_le (max_le_of_le hb0' hb1) hb2)

private theorem runRounds_maxDeg_le {α : Type}
    (step : α → SymbolicState12 → SymbolicState12)
    (hStep : ∀ c st k, st.maxDeg ≤ k → (step c st).maxDeg ≤ 7 * k) :
    ∀ (cs : List α) (st : SymbolicState12) (k : Nat),
      st.maxDeg ≤ k → (runRounds step cs st).maxDeg ≤ 7 ^ cs.length * k
  | [], st, k, h => by simpa [runRounds] using h
  | c :: cs, st, k, h => by
    simp only [runRounds, List.length_cons]
    have h1 := hStep c st k h
    have ih := runRounds_maxDeg_le step hStep cs (step c st) (7 * k) h1
    have hEq : 7 ^ cs.length * (7 * k) = 7 ^ (cs.length + 1) * k := by
      rw [Nat.pow_succ]; ac_rfl
    omega

/-- Macaulay / CICO-1 semi-regularity degree `(7 * r + 1) / 2` and Pascal binomial coefficient. -/
def cicoMacaulayDegree (activeRounds : Nat) : Nat := (7 * activeRounds + 1) / 2

def binomCoeff : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomCoeff n k + binomCoeff n (k + 1)

private theorem binomCoeff_gt_zero : ∀ (n k : Nat), n < k → binomCoeff n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [binomCoeff, binomCoeff_gt_zero n k (by omega),
      binomCoeff_gt_zero n (k + 1) (by omega)]

private theorem binomCoeff_self : ∀ n : Nat, binomCoeff n n = 1
  | 0 => rfl
  | n + 1 => by simp only [binomCoeff, binomCoeff_self n, binomCoeff_gt_zero n (n + 1) (by omega)]

private theorem binomCoeff_symm : ∀ (n k : Nat), k ≤ n → binomCoeff n k = binomCoeff n (n - k)
  | _, 0, _ => by simp [binomCoeff, binomCoeff_self]
  | 0, _ + 1, h => by omega
  | n + 1, k + 1, h => by
    by_cases hEq : k = n
    · subst hEq; simp [binomCoeff_self, binomCoeff, binomCoeff_gt_zero k (k + 1) (by omega)]
    · have hkLt : k < n := by omega
      have hSub : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
      have hSub2 : n - k = (n - (k + 1)) + 1 := by omega
      rw [hSub]
      simp only [binomCoeff]
      rw [binomCoeff_symm n k (by omega), binomCoeff_symm n (k + 1) (by omega), hSub2]
      omega

private theorem two_pow_le_binomCoeff_central : ∀ k : Nat, 2 ^ k ≤ binomCoeff (2 * k) k
  | 0 => by decide +kernel
  | 1 => by decide +kernel
  | m + 2 => by
    have ih := two_pow_le_binomCoeff_central (m + 1)
    have hSubSymm : binomCoeff (2 * m + 3) (m + 1) = binomCoeff (2 * m + 3) (m + 2) := by
      have hs := binomCoeff_symm (2 * m + 3) (m + 1) (by omega)
      have hsub : 2 * m + 3 - (m + 1) = m + 2 := by omega
      rwa [hsub] at hs
    have h2m4 : 2 * (m + 2) = (2 * m + 3) + 1 := by omega
    have h2m2 : 2 * (m + 1) = 2 * m + 2 := by omega
    have hP : binomCoeff (2 * (m + 2)) (m + 2) =
        binomCoeff (2 * m + 3) (m + 1) + binomCoeff (2 * m + 3) (m + 2) := by
      rw [h2m4]; rfl
    have hGe : binomCoeff (2 * (m + 1)) (m + 1) ≤ binomCoeff (2 * m + 3) (m + 1) := by
      have hEq : binomCoeff (2 * m + 3) (m + 1) =
          binomCoeff (2 * m + 2) m + binomCoeff (2 * m + 2) (m + 1) := rfl
      rw [h2m2]
      omega
    rw [Nat.pow_succ]
    omega

private theorem binomCoeff_mono_add_left (a b c : Nat) :
    binomCoeff (a + b) b ≤ binomCoeff (a + c + b) b := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hEq : a + (c + 1) + b = (a + c + b) + 1 := by omega
    rw [hEq]
    cases b with
    | zero => simp [binomCoeff]
    | succ b' =>
      have hStep : binomCoeff ((a + c + (b' + 1)) + 1) (b' + 1) =
          binomCoeff (a + c + (b' + 1)) b' + binomCoeff (a + c + (b' + 1)) (b' + 1) := rfl
      rw [hStep]
      omega

private theorem binomCoeff_mono_both (a a' b b' : Nat) (ha : a ≤ a') (hb : b ≤ b') :
    binomCoeff (a + b) b ≤ binomCoeff (a' + b') b' := by
  have h1 : binomCoeff (a + b) b ≤ binomCoeff (a' + b) b := by
    obtain ⟨d, rfl⟩ : ∃ d, a' = a + d := ⟨a' - a, by omega⟩
    exact binomCoeff_mono_add_left a b d
  have hSym1 : binomCoeff (a' + b) b = binomCoeff (b + a') a' := by
    rw [Nat.add_comm a' b]
    have hs := binomCoeff_symm (b + a') b (by omega)
    have hsub : b + a' - b = a' := by omega
    rwa [hsub] at hs
  have h2 : binomCoeff (b + a') a' ≤ binomCoeff (b' + a') a' := by
    obtain ⟨e, rfl⟩ : ∃ e, b' = b + e := ⟨b' - b, by omega⟩
    exact binomCoeff_mono_add_left b a' e
  have hSym2 : binomCoeff (b' + a') a' = binomCoeff (a' + b') b' := by
    rw [Nat.add_comm b' a']
    have hs := binomCoeff_symm (a' + b') a' (by omega)
    have hsub : a' + b' - a' = b' := by omega
    rwa [hsub] at hs
  omega

/-- Symbolic evaluation correctness, a syntactic degree upper bound, and parameter arithmetic.
    `symbolicPerm12` evaluates to the actual permutation and has syntactic degree at most `7^30`
    on affine inputs. The remaining conjuncts compare nominal exponent products and a binomial
    matrix-size expression to `2^128`. They do not establish reduced polynomial degree,
    semi-regularity, Macaulay rank, a minimum number of monomials, or attack running-time lower
    bounds. In particular a large upper bound, or the size of one possible algorithm's matrix,
    is not a lower bound on every solving algorithm. No cited attack is formalized by these
    numerical expressions. -/
theorem poseidon2_width12_symbolic_eval_degree_le_7pow30_and_parameter_arithmetic :
    (∀ (v : Nat → Goldilocks) (st : SymbolicState12),
      (symbolicPerm12 st).eval v = poseidon2Perm12 (st.eval v)) ∧
    (∀ st : SymbolicState12, st.maxDeg ≤ 1 → (symbolicPerm12 st).maxDeg ≤ 7 ^ 30) ∧
    (∀ rFwd rBwd : Nat, rFwd + rBwd = 30 →
      (rBwd = 0 → goldilocksPrime < 7 ^ rFwd) ∧
      (1 ≤ rBwd → 2 ^ 63 < poseidon2DInv ∧ goldilocksPrime < 7 ^ rFwd * 7 ^ rBwd ∧
        2 ^ 128 < (7 ^ rFwd * 7 ^ rBwd) ^ 2)) ∧
    2 ^ 128 < 7 ^ (12 * (8 / 2) + 22) ∧
    2 ^ 128 < (7 ^ (22 + 4)) ^ 2 ∧
    2 ^ 128 < 7 ^ (3 * 11 + (22 + 4 - 12 + 2)) ∧
    2 ^ 128 < (binomCoeff (70 + cicoMacaulayDegree 26) 70) ^ 2 := by
  refine ⟨?_, ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  · intro v st
    unfold symbolicPerm12 poseidon2Perm12
    dsimp only
    rw [runRounds_symbolic_eval v symbolicExtRound12 externalRound (symbolicExtRound12_eval v),
        runRounds_symbolic_eval v symbolicIntRound12 internalRound (symbolicIntRound12_eval v),
        runRounds_symbolic_eval v symbolicExtRound12 externalRound (symbolicExtRound12_eval v),
        symbolicME12_eval]
  · intro st h1
    unfold symbolicPerm12
    have h0 := symbolicME12_maxDeg_le st 1 h1
    have h1' := runRounds_maxDeg_le symbolicExtRound12 symbolicExtRound12_maxDeg_le
      poseidon2InitialExtConsts (symbolicME12 st) 1 h0
    have h2' := runRounds_maxDeg_le symbolicIntRound12 symbolicIntRound12_maxDeg_le
      poseidon2InternalConsts _ _ h1'
    have h3' := runRounds_maxDeg_le symbolicExtRound12 symbolicExtRound12_maxDeg_le
      poseidon2TerminalExtConsts _ _ h2'
    have hLens : poseidon2InitialExtConsts.length = 4 ∧
        poseidon2InternalConsts.length = 22 ∧
        poseidon2TerminalExtConsts.length = 4 := ⟨rfl, rfl, rfl⟩
    rw [hLens.1, hLens.2.1, hLens.2.2] at h3'
    have hPow : 7 ^ 4 * (7 ^ 22 * (7 ^ 4 * 1)) = 7 ^ 30 := by decide +kernel
    omega
  · intro rFwd rBwd hSum
    refine ⟨?_, ?_⟩
    · intro h0; subst h0; simp at hSum; subst hSum; decide
    · intro _
      rw [← Nat.pow_add, hSum]
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  · have hMac : 70 ≤ cicoMacaulayDegree 26 := by decide +kernel
    have hMono := binomCoeff_mono_both 70 (cicoMacaulayDegree 26) 70 70 hMac (Nat.le_refl 70)
    have h140 : 70 + 70 = 2 * 70 := rfl
    have h70 : 2 ^ 70 ≤ binomCoeff (70 + 70) 70 := by
      rw [h140]; exact two_pow_le_binomCoeff_central 70
    have hGe : 2 ^ 70 ≤ binomCoeff (cicoMacaulayDegree 26 + 70) 70 := Nat.le_trans h70 hMono
    rw [Nat.add_comm 70 (cicoMacaulayDegree 26)]
    have hPow2 : ∀ n : Nat, n ^ 2 = n * n := fun n => by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    have hSq : (2 ^ 70) ^ 2 ≤ (binomCoeff (cicoMacaulayDegree 26 + 70) 70) ^ 2 := by
      rw [hPow2, hPow2]; exact Nat.mul_le_mul hGe hGe
    exact Nat.lt_of_lt_of_le (by decide +kernel : 2 ^ 128 < (2 ^ 70) ^ 2) hSq


end Qsag
end

public section
namespace Qsag.CrossProtocol
open CommRingOps LawfulCommRing
/-- Three blocks of four field elements represent width twelve and rate eight. -/
abbrev State (D : Type) := D × D × D
abbrev Block4 := Fin 4 → Goldilocks

/-- Componentwise field addition is the Rust four-limb feed-forward operation. -/
instance : LawfulCommRing Block4 where
  zero := fun _ => zero; one := fun _ => one
  add := fun a b i => add (a i) (b i); mul := fun a b i => mul (a i) (b i)
  neg := fun a i => neg (a i); sub := fun a b i => sub (a i) (b i)
  add_assoc := fun _ _ _ => funext (fun _ => add_assoc _ _ _)
  add_comm := fun _ _ => funext (fun _ => add_comm _ _)
  zero_add := fun _ => funext (fun _ => zero_add _)
  add_zero := fun _ => funext (fun _ => add_zero _)
  add_left_neg := fun _ => funext (fun _ => add_left_neg _)
  sub_eq_add_neg := fun _ _ => funext (fun _ => sub_eq_add_neg _ _)
  mul_assoc := fun _ _ _ => funext (fun _ => mul_assoc _ _ _)
  mul_comm := fun _ _ => funext (fun _ => mul_comm _ _)
  one_mul := fun _ => funext (fun _ => one_mul _)
  mul_one := fun _ => funext (fun _ => mul_one _)
  left_distrib := fun _ _ _ => funext (fun _ => left_distrib _ _ _)
  right_distrib := fun _ _ _ => funext (fun _ => right_distrib _ _ _)

def rawTrunc {D : Type} (p : SimpleEquiv (State D) (State D)) (x : State D) : D :=
  (p.toFun x).1

/-- Feed-forward relation `y.1 + x.1 + extra x`. The deployed weighted compression
    (`poseidon2CompressWeighted`, `poseidon2_compress12_ff` in `agg/sponge.rs`) is the instance
    `extra x = 2 · x.2.1 + 4 · x.2.2`; `extra = 0` is the superseded partial feed-forward. -/
def relation {D : Type} [LawfulCommRing D] (extra : State D → D)
    (x y : State D) : D := add y.1 (add x.1 (extra x))

def jiveCompress {D : Type} [LawfulCommRing D] (extra : State D → D)
    (p : SimpleEquiv (State D) (State D)) (x : State D) : D :=
  relation extra x (p.toFun x)

/-- One inverse call suffices only when the recovered capacity is admissible. -/
theorem raw_inverse {D : Type} (p : SimpleEquiv (State D) (State D))
    (target b c : D) : rawTrunc p (p.invFun (target, b, c)) = target := by
  unfold rawTrunc
  rw [p.right_inv]

theorem raw_inverse_fixed_capacity {D : Type} (p : SimpleEquiv (State D) (State D))
    (target b c cap : D) (h : (p.invFun (target, b, c)).2.2 = cap) :
    ∃ a r, rawTrunc p (a, r, cap) = target := by
  have e := raw_inverse p target b c
  exact ⟨(p.invFun (target, b, c)).1, (p.invFun (target, b, c)).2.1, h ▸ e⟩

theorem inverse_feedforward_relation {D : Type} [LawfulCommRing D]
    (extra : State D → D) (p : SimpleEquiv (State D) (State D)) (y : State D) :
    jiveCompress extra p (p.invFun y) =
      add y.1 (add (p.invFun y).1 (extra (p.invFun y))) := by
  unfold jiveCompress
  rw [p.right_inv]
  rfl

def Consistent {S : Type} (p : SimpleEquiv S S) (t : List (S × S)) : Prop :=
  ∀ x y, (x, y) ∈ t → p.toFun x = y

theorem forward_extension {S : Type} (p : SimpleEquiv S S) (t : List (S × S))
    (h : Consistent p t) (x : S) : Consistent p ((x, p.toFun x) :: t) := by
  intro a b hab
  rcases List.mem_cons.mp hab with he | he
  · cases he; rfl
  · exact h a b he

theorem inverse_extension {S : Type} (p : SimpleEquiv S S) (t : List (S × S))
    (h : Consistent p t) (y : S) : Consistent p ((p.invFun y, y) :: t) := by
  intro a b hab
  rcases List.mem_cons.mp hab with he | he
  · cases he; exact p.right_inv y
  · exact h a b he

theorem checked_preimage_is_transcript_hit {D : Type} [LawfulCommRing D]
    (extra : State D → D) (p : SimpleEquiv (State D) (State D))
    (t : List (State D × State D)) (target : D) (x y : State D)
    (hc : Consistent p t) (hm : (x, y) ∈ t) (hs : jiveCompress extra p x = target) :
    relation extra x y = target := by
  unfold jiveCompress at hs
  rwa [hc x y hm] at hs

def transcriptOutputs {S D : Type} (f : S → S → D) (t : List (S × S)) : List D :=
  t.map (fun xy => f xy.1 xy.2)

theorem preimage_target_count {S D : Type} (f : S → S → D)
    (t : List (S × S)) (q : Nat) (hq : t.length ≤ q) :
    (transcriptOutputs f t).length ≤ q := by
  simpa [transcriptOutputs] using hq

def unorderedPairs {D : Type} : List D → List (D × D)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

theorem unorderedPairs_count {D : Type} (xs : List D) :
    2 * (unorderedPairs xs).length = xs.length * (xs.length - 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons]
    cases hn : xs.length with
    | zero => simp_all
    | succ n =>
      rw [hn] at ih
      simp only [Nat.succ_sub_one] at *
      rw [Nat.mul_add, ih]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

/-- Candidate counts, not a probability claim for an arbitrary permutation. -/
theorem collision_candidate_count {D : Type} (xs : List D) :
    (unorderedPairs xs).length + xs.length =
      xs.length * (xs.length - 1) / 2 + xs.length := by
  rw [← unorderedPairs_count xs, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem sum_constant {A : Type} (xs : List A) (f : A → Nat) (k : Nat)
    (h : ∀ x ∈ xs, f x = k) : (xs.map f).sum = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha])), Nat.add_mul]
    omega

private theorem erase_length {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) : (ys.erase y).length = ys.length - 1 := by
  induction ys with
  | nil => cases hy
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; simp only [List.erase_cons_head, List.length_cons, Nat.add_sub_cancel]
    · have ht : y ∈ ys := (List.mem_cons.mp hy).resolve_left (Ne.symm he)
      have hp := List.length_pos_of_mem ht
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      simp only [List.length_cons, ih ht]
      omega

private theorem erase_survives {S : Type} [DecidableEq S] (ys : List S) (x y : S)
    (hne : x ≠ y) (hx : x ∈ ys) : x ∈ ys.erase y := by
  induction ys with
  | nil => cases hx
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; rw [List.erase_cons_head]
      exact (List.mem_cons.mp hx).resolve_left hne
    · rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      rcases List.mem_cons.mp hx with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (ih h))

private theorem nodup_length_bound {S : Type} [DecidableEq S] (xs ys : List S)
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have hay := hs (List.mem_cons_self ..)
    have hsub : xs ⊆ ys.erase a := fun x hx =>
      erase_survives ys x a (fun he => ha (he ▸ hx)) (hs (List.mem_cons_of_mem a hx))
    have hb := ih (ys.erase a) ht hsub
    rw [erase_length ys a hay] at hb
    have hp := List.length_pos_of_mem hay
    simp only [List.length_cons]
    omega

private theorem erase_perm {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) : ys.Perm (y :: ys.erase y) := by
  induction ys with
  | nil => cases hy
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; rw [List.erase_cons_head]
    · have ht : y ∈ ys := (List.mem_cons.mp hy).resolve_left (Ne.symm he)
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      exact (List.Perm.cons a (ih ht)).trans (List.Perm.swap y a _)

/-- All ways to complete the unused output table, in fixed unused-input order. -/
def extensions {S : Type} [DecidableEq S] : Nat → List S → List (List S)
  | 0, _ => [[]]
  | n + 1, ys => ys.flatMap (fun y => (extensions n (ys.erase y)).map (y :: ·))

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem extensions_count {S : Type} [DecidableEq S] (n : Nat) (ys : List S)
    (h : ys.length = n) : (extensions n ys).length = factorial n := by
  induction n generalizing ys with
  | zero => rfl
  | succ n ih =>
    rw [extensions, List.length_flatMap]
    have he : ∀ y ∈ ys, ((extensions n (ys.erase y)).map (y :: ·)).length = factorial n := by
      intro y hy
      rw [List.length_map, ih _ (by rw [erase_length ys y hy, h]; omega)]
    rw [sum_constant ys _ _ he, h]
    rfl

theorem extensions_are_permutations {S : Type} [DecidableEq S] (n : Nat)
    (ys zs : List S) (h : ys.length = n) (hm : zs ∈ extensions n ys) : zs.Perm ys := by
  induction n generalizing ys zs with
  | zero =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h
    have hz : zs = [] := List.mem_singleton.mp hm
    subst ys; subst zs; exact List.Perm.refl _
  | succ n ih =>
    obtain ⟨y, hy, hzs⟩ := List.mem_flatMap.mp hm
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hzs
    exact (List.Perm.cons y (ih _ _ (by rw [erase_length ys y hy, h]; omega) hr)).trans
      (erase_perm ys y hy).symm

theorem extensions_complete {S : Type} [DecidableEq S] (n : Nat) (ys zs : List S)
    (hl : ys.length = n) (hp : zs.Perm ys) : zs ∈ extensions n ys := by
  induction n generalizing ys zs with
  | zero =>
    have hz := hp.length_eq.trans hl
    have he := List.length_eq_zero_iff.mp hz
    subst zs; exact List.mem_singleton.mpr rfl
  | succ n ih =>
    cases zs with
    | nil => have h := hp.length_eq; simp only [List.length_nil] at h; omega
    | cons y zs =>
      have hy := hp.mem_iff.mp (by simp : y ∈ y :: zs)
      apply List.mem_flatMap.mpr
      refine ⟨y, hy, List.mem_map.mpr ⟨zs, ?_, rfl⟩⟩
      exact ih _ _ (by rw [erase_length ys y hy, hl]; omega)
        (List.Perm.cons_inv (hp.trans (erase_perm ys y hy)))

private theorem flatMap_nodup {A B : Type} (xs : List A) (f : A → List B)
    (hn : xs.Nodup) (hf : ∀ a ∈ xs, (f a).Nodup)
    (sep : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ u ∈ f a, ∀ v ∈ f b, u ≠ v) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    apply List.nodup_append.mpr
    refine ⟨hf a (by simp), ih ht (fun x hx => hf x (by simp [hx]))
      (fun x hx y hy => sep x (by simp [hx]) y (by simp [hy])), ?_⟩
    intro u hu v hv
    obtain ⟨b, hb, hv⟩ := List.mem_flatMap.mp hv
    exact sep a (by simp) b (by simp [hb]) (fun h => ha (h ▸ hb)) u hu v hv

theorem extensions_nodup {S : Type} [DecidableEq S] (n : Nat) (ys : List S)
    (hn : ys.Nodup) : (extensions n ys).Nodup := by
  induction n generalizing ys with
  | zero => exact .cons (by intro _ h; cases h) .nil
  | succ n ih =>
    apply flatMap_nodup ys _ hn
    · intro y _
      exact (ih _ (hn.erase y)).map (y :: ·) (fun _ _ h e => h (List.cons.inj e).2)
    · intro a _ b _ hab u hu v hv
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
      exact fun e => hab (List.cons.inj e).1

/-- Each possible fresh answer has exactly the same number of completions. -/
theorem fresh_answer_weight {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) :
    (extensions (ys.length - 1) (ys.erase y)).length = factorial (ys.length - 1) :=
  extensions_count _ _ (erase_length ys y hy)

def forwardFiber {D : Type} [LawfulCommRing D] (ds : List D)
    (extra : State D → D) (x : State D) (target : D) : List (State D) :=
  ds.flatMap (fun b => ds.map (fun c => (sub target (add x.1 (extra x)), b, c)))

/-- `extra` may depend on the second/third block, but not on the unknown first block. -/
def inverseFiber {D : Type} [LawfulCommRing D] (ds : List D)
    (extra : D → D → D) (y : State D) (target : D) : List (State D) :=
  ds.flatMap (fun b => ds.map (fun c => (sub (sub target y.1) (extra b c), b, c)))

private theorem solve_add {D : Type} [LawfulCommRing D] {a b t : D}
    (h : add a b = t) : a = sub t b := by
  rw [← h, sub_eq_add_neg, add_assoc, add_right_neg, add_zero]

theorem forward_fiber_complete {D : Type} [LawfulCommRing D] (ds : List D)
    (allD : ∀ d, d ∈ ds) (extra : State D → D) (x y : State D) (target : D)
    (h : relation extra x y = target) : y ∈ forwardFiber ds extra x target := by
  have e := solve_add h
  exact List.mem_flatMap.mpr ⟨y.2.1, allD _, List.mem_map.mpr ⟨y.2.2, allD _,
    by cases y; simp_all⟩⟩

theorem inverse_fiber_complete {D : Type} [LawfulCommRing D] (ds : List D)
    (allD : ∀ d, d ∈ ds) (extra : D → D → D) (x y : State D) (target : D)
    (h : relation (fun z => extra z.2.1 z.2.2) x y = target) :
    x ∈ inverseFiber ds extra y target := by
  have he : add (add x.1 (extra x.2.1 x.2.2)) y.1 = target :=
    (add_comm _ _).trans h
  have e := solve_add (solve_add he)
  exact List.mem_flatMap.mpr ⟨x.2.1, allD _, List.mem_map.mpr ⟨x.2.2, allD _,
    by cases x; simp_all⟩⟩

theorem fiber_counts {D : Type} [LawfulCommRing D] (ds : List D)
    (f : State D → D) (g : D → D → D) (x y : State D) (target : D) :
    (forwardFiber ds f x target).length = ds.length * ds.length ∧
    (inverseFiber ds g y target).length = ds.length * ds.length := by
  constructor <;> simp only [forwardFiber, inverseFiber, List.length_flatMap]
  all_goals exact sum_constant ds _ _ (fun _ _ => List.length_map _)

/-- Finite counting form: at most B favorable fresh responses, each of weight (N-t-1)!.
    With D = F^4, fibers have B = |D|^2 = p^8 and the full state space has N = p^12.
    The conditional ratio is at most B/(N-t), in either query direction. -/
theorem fresh_bad_extensions_bound {S : Type} [DecidableEq S]
    (available fiber : List S) (bad : S → Bool) (hn : available.Nodup)
    (cover : ∀ x ∈ available, bad x = true → x ∈ fiber) :
    ((available.filter bad).flatMap (fun y =>
      (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length ≤
      fiber.length * factorial (available.length - 1) := by
  rw [List.length_flatMap]
  have hw : ∀ y ∈ available.filter bad,
      ((extensions (available.length - 1) (available.erase y)).map (y :: ·)).length =
      factorial (available.length - 1) := by
    intro y hy
    rw [List.length_map, fresh_answer_weight available y (List.mem_filter.mp hy).1]
  rw [sum_constant _ _ _ hw]
  apply Nat.mul_le_mul_right
  exact nodup_length_bound _ _ (hn.filter bad) (fun x hx =>
    cover x (List.mem_filter.mp hx).1 (List.mem_filter.mp hx).2)

def queryValue {D : Type} [LawfulCommRing D] (inverse : Bool)
    (extra : D → D → D) (chosen answer : State D) : D :=
  if inverse then relation (fun z => extra z.2.1 z.2.2) answer chosen
  else relation (fun z => extra z.2.1 z.2.2) chosen answer

def queryFiber {D : Type} [LawfulCommRing D] (inverse : Bool) (ds : List D)
    (extra : D → D → D) (chosen : State D) (target : D) : List (State D) :=
  if inverse then inverseFiber ds extra chosen target
  else forwardFiber ds (fun z => extra z.2.1 z.2.2) chosen target

/-- One theorem covers forward/inverse preimages (one target) and collisions
    (all prior transcript outputs). Each target contributes at most |D|² completions
    per residual permutation, with the exact without-replacement denominator. -/
theorem bidirectional_bad_count {D : Type} [LawfulCommRing D] [DecidableEq D]
    (inverse : Bool) (ds : List D) (allD : ∀ d, d ∈ ds) (extra : D → D → D)
    (chosen : State D) (targets : List D) (available : List (State D))
    (hn : available.Nodup) :
    ((available.filter (fun x => decide (queryValue inverse extra chosen x ∈ targets))).flatMap
      (fun y => (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length ≤
      (targets.length * (ds.length * ds.length)) * factorial (available.length - 1) := by
  let fibers := targets.flatMap (queryFiber inverse ds extra chosen)
  have hc : ∀ x ∈ available,
      decide (queryValue inverse extra chosen x ∈ targets) = true → x ∈ fibers := by
    intro x _ hx
    apply List.mem_flatMap.mpr
    refine ⟨queryValue inverse extra chosen x, of_decide_eq_true hx, ?_⟩
    cases inverse
    · exact forward_fiber_complete ds allD (fun z => extra z.2.1 z.2.2) chosen x _ rfl
    · exact inverse_fiber_complete ds allD extra x chosen _ rfl
  have hl : fibers.length = targets.length * (ds.length * ds.length) := by
    rw [List.length_flatMap]
    apply sum_constant
    intro t _
    cases inverse
    · exact (fiber_counts ds (fun z => extra z.2.1 z.2.2) extra chosen chosen t).1
    · exact (fiber_counts ds (fun z => extra z.2.1 z.2.2) extra chosen chosen t).2
  have hb := fresh_bad_extensions_bound available fibers _ hn hc
  rwa [hl] at hb

/-- Uniform completions give an exact finite denominator: available.length factorial.
    Deleting prior responses affects the denominator even when the bad fiber is unchanged. -/
theorem conditional_extension_density {S : Type} [DecidableEq S]
    (available : List S) (bad : S → Bool) :
    ((available.filter bad).flatMap (fun y =>
      (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length =
      (available.filter bad).length * factorial (available.length - 1) := by
  rw [List.length_flatMap]
  exact sum_constant _ _ _ (fun y hy => by
    rw [List.length_map, fresh_answer_weight available y (List.mem_filter.mp hy).1])

theorem width12_fiber_cardinality (ds : List Block4)
    (hc : ds.length = goldilocksPrime ^ 4) (x y : State Block4) (target : Block4) :
    (forwardFiber ds (fun _ => zero) x target).length = goldilocksPrime ^ 8 ∧
    (inverseFiber ds (fun _ _ => zero) y target).length = goldilocksPrime ^ 8 := by
  obtain ⟨hf, hi⟩ := fiber_counts ds (fun _ => zero) (fun _ _ => zero) x y target
  have he : ds.length * ds.length = goldilocksPrime ^ 8 := by
    rw [hc, ← Nat.pow_add]
  exact ⟨hf.trans he, hi.trans he⟩


/-! ### Exports for lane threshold-a -/

theorem _root_.Qsag.chunk7Exact_cons7 (b0 b1 b2 b3 b4 b5 b6 : UInt8) (rest : List UInt8) :
    chunk7Exact (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      pack7BytesLimb [b0, b1, b2, b3, b4, b5, b6] :: chunk7Exact rest := by rfl

theorem _root_.Qsag.chunk7Exact_of_length_lt :
    ∀ (bs : List UInt8), bs.length < 7 → chunk7Exact bs = []
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by
    simp only [List.length_cons] at h
    omega

theorem _root_.Qsag.pack7BytesLimb_val (bs : List UInt8) :
    (pack7BytesLimb bs).val = ofBE ((bs ++ List.replicate (7 - bs.length) (0 : UInt8)).take 7) := by
  rfl

theorem _root_.Qsag.bytesToLimbs56_def (msg : List UInt8) :
    bytesToLimbs56 msg =
      chunk7Exact ((msg ++ [(0x01 : UInt8)]) ++
        List.replicate ((7 - (msg ++ [(0x01 : UInt8)]).length % 7) % 7) (0x00 : UInt8)) := by rfl

theorem _root_.Qsag.poseidon2PadBytes_def (msg : List UInt8) :
    poseidon2PadBytes msg = poseidon2Pad (bytesToLimbs56 msg) := by rfl

theorem _root_.Qsag.absorbRate8Block_def (st : Poseidon2State12) (r0 r1 : Lane4) :
    absorbRate8Block st r0 r1 = poseidon2Perm12 ⟨lane4Add st.b0 r0, lane4Add st.b1 r1, st.b2⟩ := by
  rfl

theorem _root_.Qsag.absorbLimbStream_cons8 (st : Poseidon2State12)
    (m0 m1 m2 m3 m4 m5 m6 m7 : Goldilocks) (rest : List Goldilocks) :
    absorbLimbStream st (m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: m7 :: rest) =
      absorbLimbStream (absorbRate8Block st ⟨m0, m1, m2, m3⟩ ⟨m4, m5, m6, m7⟩) rest := by
  simp only [absorbLimbStream]

theorem _root_.Qsag.absorbLimbStream_of_length_lt (st : Poseidon2State12) :
    ∀ (ms : List Goldilocks), ms.length < 8 → absorbLimbStream st ms = st
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _], _ => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => by
    simp only [List.length_cons] at h
    omega

theorem _root_.Qsag.squeeze32Bytes_def (st : Poseidon2State12) :
    squeeze32Bytes st =
      be 8 st.b0.x0.val ++ be 8 st.b0.x1.val ++ be 8 st.b0.x2.val ++ be 8 st.b0.x3.val := by rfl

theorem _root_.Qsag.poseidon2InitState_def :
    poseidon2InitState =
      ⟨lane4Zero, lane4Zero,
        ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 4, Goldilocks.ofNat 32,
          Goldilocks.ofNat 0x504F53325F474C31⟩⟩ := by rfl


/-! ### Exports for lane agg-core -/

theorem rawTrunc_eq {D : Type} (p : SimpleEquiv (State D) (State D)) (x : State D) :
    rawTrunc p x = (p.toFun x).1 := by rfl

theorem jiveCompress_eq {D : Type} [LawfulCommRing D] (extra : State D → D)
    (p : SimpleEquiv (State D) (State D)) (x : State D) :
    jiveCompress extra p x =
      CommRingOps.add (p.toFun x).1 (CommRingOps.add x.1 (extra x)) := by rfl

theorem consistent_iff {S : Type} (p : SimpleEquiv S S) (t : List (S × S)) :
    Consistent p t ↔ ∀ x y, (x, y) ∈ t → p.toFun x = y := Iff.rfl
theorem _root_.Qsag.poseidon2InternalConsts_length : poseidon2InternalConsts.length = 22 := by
  unfold poseidon2InternalConsts
  rw [List.length_map, List.length_range]

theorem _root_.Qsag.poseidon2InitialExtConsts_length : poseidon2InitialExtConsts.length = 4 := by
  unfold poseidon2InitialExtConsts
  rw [List.length_map, List.length_range]

theorem _root_.Qsag.lane4Sum_def (a : Lane4) :
    lane4Sum a = Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3) := by rfl

theorem _root_.Qsag.applyM4_def (b : Lane4) :
    applyM4 b =
      ⟨Goldilocks.add (lane4Sum b) (Goldilocks.add b.x0 (Goldilocks.mul (Goldilocks.ofNat 2) b.x1)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x1 (Goldilocks.mul (Goldilocks.ofNat 2) b.x2)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x2 (Goldilocks.mul (Goldilocks.ofNat 2) b.x3)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x3 (Goldilocks.mul (Goldilocks.ofNat 2) b.x0))⟩ := by
  rfl

theorem _root_.Qsag.sboxLane4_def (b : Lane4) :
    sboxLane4 b = ⟨sbox7 b.x0, sbox7 b.x1, sbox7 b.x2, sbox7 b.x3⟩ := by rfl

theorem _root_.Qsag.poseidon2Transpose4x3_def (s : Poseidon2State12) :
    poseidon2Transpose4x3 s =
      ⟨⟨s.b0.x0, s.b0.x3, s.b1.x2, s.b2.x1⟩,
       ⟨s.b0.x1, s.b1.x0, s.b1.x3, s.b2.x2⟩,
       ⟨s.b0.x2, s.b1.x1, s.b2.x0, s.b2.x3⟩⟩ := by rfl

theorem _root_.Qsag.poseidon2Transpose3x4_def (s : Poseidon2State12) :
    poseidon2Transpose3x4 s =
      ⟨⟨s.b0.x0, s.b1.x0, s.b2.x0, s.b0.x1⟩,
       ⟨s.b1.x1, s.b2.x1, s.b0.x2, s.b1.x2⟩,
       ⟨s.b2.x2, s.b0.x3, s.b1.x3, s.b2.x3⟩⟩ := by rfl

theorem _root_.Qsag.state12Sum_def (st : Poseidon2State12) :
    state12Sum st =
      Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1)) (lane4Sum st.b2) := by rfl


#verify_constructive checked_preimage_is_transcript_hit inverse_feedforward_relation
-- Equations for the symbolic instances of `Tests/CompositionInstances`; no body is exposed.
#export_eqns rawTrunc relation jiveCompress Consistent extensions queryValue

end Qsag.CrossProtocol
end

public section
namespace Qsag

theorem lane4Sub_eq (a b : Lane4) : lane4Sub a b =
    ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
     Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩ := by unfold lane4Sub; rfl

theorem state12Sub_eq (a b : Poseidon2State12) : state12Sub a b =
    ⟨lane4Sub a.b0 b.b0, lane4Sub a.b1 b.b1, lane4Sub a.b2 b.b2⟩ := by unfold state12Sub; rfl

theorem Poseidon2State12.toList_eq (s : Poseidon2State12) : s.toList =
    [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3, s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
     s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3] := by unfold Poseidon2State12.toList; rfl

theorem Poseidon2State12.toList_length (s : Poseidon2State12) : s.toList.length = 12 := by
  rw [Poseidon2State12.toList_eq]
  rfl

theorem poseidon2TerminalExtConsts_length : poseidon2TerminalExtConsts.length = 4 := by
  unfold poseidon2TerminalExtConsts
  rw [List.length_map, List.length_range]

theorem poseidon2InitialExtConsts_eq : poseidon2InitialExtConsts =
    [poseidon2ExtRoundConst 0 0, poseidon2ExtRoundConst 0 1,
     poseidon2ExtRoundConst 0 2, poseidon2ExtRoundConst 0 3] := by
  unfold poseidon2InitialExtConsts
  rfl

theorem poseidon2_initial_sbox_zero_nonzero :
    (sboxState12 (state12Add (applyME state12Zero) (poseidon2ExtRoundConst 0 0))).b0.x0 ≠
      Goldilocks.zero := by decide +kernel

end Qsag
end

public section
namespace Qsag

/-- The four limbs of a `Lane4` / `Digest4` as a residual list. -/
@[expose] def Lane4.toList (l : Lane4) : List Goldilocks :=
  [l.x0, l.x1, l.x2, l.x3]

theorem Lane4.toList_eq (s : Lane4) : s.toList = [s.x0, s.x1, s.x2, s.x3] := by
  unfold Lane4.toList
  rfl

end Qsag
end

/-! ### Exports for lane mir -/

public section
namespace Qsag

/-- Defining equation of `poseidon2Transpose4x3`. -/
theorem poseidon2Transpose4x3_eq (s : Poseidon2State12) :
    poseidon2Transpose4x3 s =
      ⟨⟨s.b0.x0, s.b0.x3, s.b1.x2, s.b2.x1⟩,
       ⟨s.b0.x1, s.b1.x0, s.b1.x3, s.b2.x2⟩,
       ⟨s.b0.x2, s.b1.x1, s.b2.x0, s.b2.x3⟩⟩ := by
  unfold poseidon2Transpose4x3
  rfl

/-- Defining equation of `poseidon2Transpose3x4`. -/
theorem poseidon2Transpose3x4_eq (s : Poseidon2State12) :
    poseidon2Transpose3x4 s =
      ⟨⟨s.b0.x0, s.b1.x0, s.b2.x0, s.b0.x1⟩,
       ⟨s.b1.x1, s.b2.x1, s.b0.x2, s.b1.x2⟩,
       ⟨s.b2.x2, s.b0.x3, s.b1.x3, s.b2.x3⟩⟩ := by
  unfold poseidon2Transpose3x4
  rfl

/-- Defining equation of `lane4Sum`. -/
theorem lane4Sum_eq (a : Lane4) :
    lane4Sum a = Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3) := by
  unfold lane4Sum
  rfl

/-- Defining equation of `applyM4`. -/
theorem applyM4_eq (b : Lane4) :
    applyM4 b =
      ⟨Goldilocks.add (lane4Sum b) (Goldilocks.add b.x0 (Goldilocks.mul (Goldilocks.ofNat 2) b.x1)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x1 (Goldilocks.mul (Goldilocks.ofNat 2) b.x2)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x2 (Goldilocks.mul (Goldilocks.ofNat 2) b.x3)),
       Goldilocks.add (lane4Sum b) (Goldilocks.add b.x3 (Goldilocks.mul (Goldilocks.ofNat 2) b.x0))⟩ := by
  unfold applyM4
  rfl

end Qsag

/-! ### Exports for lane oracle -/

public section
namespace Qsag

/-- Defining equation of `sboxLane4`. -/
theorem sboxLane4_eq (b : Lane4) :
    sboxLane4 b = ⟨sbox7 b.x0, sbox7 b.x1, sbox7 b.x2, sbox7 b.x3⟩ := by
  unfold sboxLane4
  rfl

/-- Defining equation of `sboxLane4Inv`. -/
theorem sboxLane4Inv_eq (b : Lane4) :
    sboxLane4Inv b = ⟨sbox7Inv b.x0, sbox7Inv b.x1, sbox7Inv b.x2, sbox7Inv b.x3⟩ := by
  unfold sboxLane4Inv
  rfl

theorem runRoundsInv_nil {α σ : Type} (stepInv : α → σ → σ) (s : σ) :
    runRoundsInv stepInv [] s = s := by
  unfold runRoundsInv
  rfl

theorem runRoundsInv_cons {α σ : Type} (stepInv : α → σ → σ) (c : α) (cs : List α) (s : σ) :
    runRoundsInv stepInv (c :: cs) s = stepInv c (runRoundsInv stepInv cs s) := by
  rw [runRoundsInv]

/-- Defining equation of `state16Zero`. -/
theorem state16Zero_eq : state16Zero = ⟨lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩ := by
  unfold state16Zero
  rfl

/-- Defining equation of `applyME16`, with the block sum written out. -/
theorem applyME16_eq (st : Poseidon2State16) :
    applyME16 st =
      ⟨lane4Add (applyM4 st.b0)
          (lane4Add (lane4Add (lane4Add (applyM4 st.b0) (applyM4 st.b1)) (applyM4 st.b2))
            (applyM4 st.b3)),
       lane4Add (applyM4 st.b1)
          (lane4Add (lane4Add (lane4Add (applyM4 st.b0) (applyM4 st.b1)) (applyM4 st.b2))
            (applyM4 st.b3)),
       lane4Add (applyM4 st.b2)
          (lane4Add (lane4Add (lane4Add (applyM4 st.b0) (applyM4 st.b1)) (applyM4 st.b2))
            (applyM4 st.b3)),
       lane4Add (applyM4 st.b3)
          (lane4Add (lane4Add (lane4Add (applyM4 st.b0) (applyM4 st.b1)) (applyM4 st.b2))
            (applyM4 st.b3))⟩ := by
  unfold applyME16
  rfl

/-- Defining equation of the SplitMix64 finalizer used by the round-constant generator. -/
theorem splitMix64Mix_eq (x : UInt64) :
    splitMix64Mix x =
      (let z0 := x + 0x9E3779B97F4A7C15
       let z1 := (z0 ^^^ (z0 >>> 30)) * 0xBF58476D1CE4E5B9
       let z2 := (z1 ^^^ (z1 >>> 27)) * 0x94D049BB133111EB
       z2 ^^^ (z2 >>> 31)) := by
  unfold splitMix64Mix
  rfl

/-- Defining equation of `poseidon2ConstAt`, down to the SplitMix64 finalizer. -/
theorem poseidon2ConstAt_eq (tag round lane : Nat) :
    poseidon2ConstAt tag round lane =
      Goldilocks.ofNat
        (splitMix64Mix
          (splitMix64Mix (splitMix64Mix ((0x504F53325F474C31 : UInt64) ^^^ UInt64.ofNat tag) ^^^
            UInt64.ofNat round) ^^^ UInt64.ofNat lane)).toNat := by
  unfold poseidon2ConstAt poseidon2ConstWord poseidon2ConstIV
  rfl

/-! ## 5. Build-Time Conformance Vectors Matching `poseidon2.rs` -/

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩).toList.map (·.val) =
    [17528629447354354351, 5014055130248055117, 10679077121839038553, 431078547345611051, 7807009921345120310, 2413869689279715014, 11875300792986830377, 1872634884137602556, 15069512080271275672, 14253608580209913153, 14550618143248480092, 107036164978639472] := by decide +kernel

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩).toList.map (·.val) =
    [13782584570844608145, 13136387643152332171, 7171133015474200819, 7643370872200861694, 14144755201299840503, 16470027036684692562, 1748465969625202405, 1718729118078964347, 6141020819996733037, 16322330185628708898, 11650380702735067362, 2734959974607798415] := by decide +kernel

example : poseidon2Hash32 [] =
    [182, 168, 65, 106, 0, 54, 23, 124, 22, 116, 119, 199, 75, 253, 202, 145, 123, 13, 115, 200, 186, 143, 207, 66, 162, 161, 198, 9, 220, 37, 176, 162] := by decide +kernel

example : poseidon2Hash32 [0] =
    [116, 79, 15, 95, 17, 248, 202, 240, 45, 126, 192, 181, 89, 193, 185, 161, 98, 167, 199, 38, 214, 141, 4, 22, 97, 34, 223, 133, 16, 3, 170, 104] := by decide +kernel

example : poseidon2Hash32 [1, 2, 3] =
    [149, 79, 171, 160, 0, 49, 166, 60, 204, 121, 241, 71, 102, 130, 24, 17, 35, 162, 114, 249, 194, 254, 120, 46, 18, 111, 254, 27, 106, 81, 178, 227] := by decide +kernel

example : poseidon2Hash32 [113, 115, 97, 103, 45, 112, 111, 115, 101, 105, 100, 111, 110, 50, 45, 107, 97, 116] =
    [228, 156, 140, 147, 124, 10, 100, 197, 103, 106, 168, 7, 254, 196, 250, 183, 212, 130, 17, 26, 2, 139, 235, 15, 219, 46, 193, 238, 148, 50, 236, 229] := by decide +kernel

example : (let out := poseidon2CompressWeighted ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩;
    [out.x0.val, out.x1.val, out.x2.val, out.x3.val]) =
    [13782584570844608185, 13136387643152332218, 7171133015474200873, 7643370872200861755] := by decide +kernel

/-! ## Teeth that unfold or execute this module's definitions (audited and paired in `Tests/OracleAndQrom`) -/
section ExecutedTeeth
open RoundPoly

/-- `x ↦ x ^ 3` identifies `ω₃ ≠ 1` with `1`, because `3 ∣ p - 1`. -/
theorem tooth_d3_not_permutation_on_goldilocks :
    goldilocksOmega3 ≠ Goldilocks.one ∧ goldilocksOmega3 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega3 3 = goldilocksPow Goldilocks.one 3 ∧
    3 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨6148914689804861440, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide

/-- `x ↦ x ^ 5` identifies `ω₅ ≠ 1` with `1`, because `5 ∣ p - 1`. -/
theorem tooth_d5_not_permutation_on_goldilocks :
    goldilocksOmega5 ≠ Goldilocks.one ∧ goldilocksOmega5 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega5 5 = goldilocksPow Goldilocks.one 5 ∧
    5 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨3689348813882916864, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide

/-- `#tooth` **Merz–Rodríguez García (`2026/306`) `(X, -X, 0)` Subspace & Partial Feed-Forward Vulnerability**:
    1. On the block-circulant factor `applyMEStd = P_3 ⊗ M_4 = circ(2 M_4, M_4, M_4)` (the external layer before the `M_4 ⊗ P_3` lane transposition was deployed), the entire 4-dimensional subspace
       `⟨X, -X, 0⟩` maps to `⟨M_4 X, -M_4 X, 0⟩`, leaving the sponge capacity block `b2 = 0` untouched!
    2. Across a full round `sboxState12 (state12Add (applyMEStd ⟨U0 + X, -X, U2⟩) C)` under the two linear
       antisymmetry conditions `(applyMEStd ⟨U0, 0, U2⟩).b0 + C.b0 = -((applyMEStd ⟨U0, 0, U2⟩).b1 + C.b1)`,
       oddness of `sbox7` preserves `(X^(1), -X^(1))` in blocks `0, 1` while keeping block `b2` independent of `X`!
    3. Partial feed-forward `(perm st).b0 + st.b0` (`poseidon2_compress12_ff` in `sponge.rs`) and naive
       uniform sum `st.b0 + st.b1 + st.b2` leave `(0, X, -X)` canceled in the feed-forward term. -/
theorem tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip (X U0 U2 : Lane4)
    (C : Poseidon2State12)
    (hAnti : lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b0 C.b0 =
             lane4Neg (lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b1 C.b1)) :
    applyMEStd ⟨X, lane4Neg X, lane4Zero⟩ = ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ ∧
    let afterSbox := sboxState12 (state12Add (applyMEStd ⟨lane4Add U0 X, lane4Neg X, U2⟩) C)
    afterSbox.b1 = lane4Neg afterSbox.b0 ∧
    afterSbox.b2 = sboxLane4 (lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b2 C.b2) ∧
    (⟨U0, X, lane4Neg X⟩ : Poseidon2State12).b0 = U0 ∧
    lane4Add (lane4Add U0 X) (lane4Neg X) = U0 := by
  have hLinSub : applyMEStd ⟨X, lane4Neg X, lane4Zero⟩ =
      ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ := by
    unfold applyMEStd lane4Neg applyM4 lane4Add lane4Sub lane4Sum lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  have hDecomp : ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
      state12Add ⟨U0, lane4Zero, U2⟩ ⟨X, lane4Neg X, lane4Zero⟩ := by
    unfold state12Add lane4Add lane4Neg lane4Sub lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  refine ⟨hLinSub, ?_, ?_, rfl, ?_⟩
  · rw [hDecomp, applyMEStd_add, hLinSub]
    unfold state12Add sboxState12 sboxLane4
    dsimp only
    have hHelper : ∀ (M0 M1 A C0 C1 : Lane4),
        lane4Add M0 C0 = lane4Neg (lane4Add M1 C1) →
        lane4Add (lane4Add M1 (lane4Neg A)) C1 = lane4Neg (lane4Add (lane4Add M0 A) C0) := by
      intro M0 M1 A C0 C1 hEq
      have h0 := congrArg Lane4.x0 hEq
      have h1 := congrArg Lane4.x1 hEq
      have h2 := congrArg Lane4.x2 hEq
      have h3 := congrArg Lane4.x3 hEq
      unfold lane4Add lane4Neg lane4Sub lane4Zero at h0 h1 h2 h3 ⊢
      dsimp only at h0 h1 h2 h3 ⊢
      have hInv : ∀ a : Goldilocks, Goldilocks.sub Goldilocks.zero (Goldilocks.sub Goldilocks.zero a) = a :=
        fun _ => by gold_cring
      apply Lane4.ext
      · have hL : Goldilocks.add (Goldilocks.add M1.x0 (Goldilocks.sub Goldilocks.zero A.x0)) C1.x0 =
            Goldilocks.sub (Goldilocks.add M1.x0 C1.x0) A.x0 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x0 A.x0) C0.x0) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0)) A.x0 := by gold_cring
        have hFlip : Goldilocks.add M1.x0 C1.x0 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h0
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x1 (Goldilocks.sub Goldilocks.zero A.x1)) C1.x1 =
            Goldilocks.sub (Goldilocks.add M1.x1 C1.x1) A.x1 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x1 A.x1) C0.x1) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1)) A.x1 := by gold_cring
        have hFlip : Goldilocks.add M1.x1 C1.x1 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h1
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x2 (Goldilocks.sub Goldilocks.zero A.x2)) C1.x2 =
            Goldilocks.sub (Goldilocks.add M1.x2 C1.x2) A.x2 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x2 A.x2) C0.x2) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2)) A.x2 := by gold_cring
        have hFlip : Goldilocks.add M1.x2 C1.x2 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h2
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x3 (Goldilocks.sub Goldilocks.zero A.x3)) C1.x3 =
            Goldilocks.sub (Goldilocks.add M1.x3 C1.x3) A.x3 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x3 A.x3) C0.x3) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3)) A.x3 := by gold_cring
        have hFlip : Goldilocks.add M1.x3 C1.x3 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h3
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
    have hSumAnti := hHelper (applyMEStd ⟨U0, lane4Zero, U2⟩).b0 (applyMEStd ⟨U0, lane4Zero, U2⟩).b1
      (applyM4 X) C.b0 C.b1 hAnti
    rw [hSumAnti]
    unfold lane4Neg lane4Sub lane4Zero
    dsimp only
    exact Lane4.ext (sbox7_odd _) (sbox7_odd _) (sbox7_odd _) (sbox7_odd _)
  · rw [hDecomp, applyMEStd_add, hLinSub]
    unfold state12Add sboxState12
    dsimp only
    have hAddZ : ∀ a : Lane4, lane4Add a lane4Zero = a := fun a => by
      unfold lane4Add lane4Zero; apply Lane4.ext <;> exact LawfulCommRing.add_zero _
    rw [hAddZ]
  · unfold lane4Add lane4Neg lane4Sub lane4Zero
    apply Lane4.ext <;> gold_cring

/-- Superseded internal diffusion matrix `diag(-2, 1, 2, 4, ..., 1024) + 1·1ᵀ` (first diagonal entry
    `-2`; the deployed `applyMI` uses `-64`). Kept only as the object of the tooth below. -/
def applyMIFirstEntryNegTwo (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) st.b0.x0) s,
    Goldilocks.add st.b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) s⟩⟩

/-- Explicit 12-lane Goldilocks eigenvector of `applyMIFirstEntryNegTwo` for eigenvalue
    `λ₀ = 8914261387277420341`. -/
def miRationalEigvec0 : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 8415733694666260766, Goldilocks.ofNat 10081604446170657914,
    Goldilocks.ofNat 13429757962329074280, Goldilocks.ofNat 7212905167159261059⟩,
   ⟨Goldilocks.ofNat 7177536167446655380, Goldilocks.ofNat 16173559831921257667,
    Goldilocks.ofNat 11410676009809774369, Goldilocks.ofNat 263994636750658321⟩,
   ⟨Goldilocks.ofNat 11338638786567724180, Goldilocks.ofNat 17416777037312523837,
    Goldilocks.ofNat 8867871345638664998, Goldilocks.ofNat 17338153400129577477⟩⟩

/-- `#tooth` **The superseded `V[0] = -2` internal matrix has a rational eigenvector over Goldilocks**:
    `applyMIFirstEntryNegTwo miRationalEigvec0 = λ₀ · miRationalEigvec0` with `miRationalEigvec0 ≠ 0`, so
    `diag(-2, 1, 2, ..., 1024) + 1·1ᵀ` has a reducible characteristic polynomial over `𝔽_p`. The same
    vector is not an eigenvector of the deployed `applyMI` for `λ₀`. -/
theorem tooth_current_mi_has_rational_eigenvector :
    miRationalEigvec0 ≠ state12Zero ∧
    applyMIFirstEntryNegTwo miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0 ∧
    ¬ (applyMI miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0) := by decide

#verify_constructive
  Qsag.poseidon2_interpolation_margin_needs_26
  Qsag.tooth_d3_not_permutation_on_goldilocks
  Qsag.tooth_d5_not_permutation_on_goldilocks
  Qsag.tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip
  Qsag.tooth_current_mi_has_rational_eigenvector
end ExecutedTeeth

end Qsag

/-! ### Feed-forward teeth (evaluate `rawTrunc` / `jiveCompress`; audited and paired in `Tests/OracleAndQrom`) -/
namespace Qsag.CrossProtocol
open CommRingOps LawfulCommRing

/-- Explicit permutation: raw inversion succeeds, adding the recovered input fails. -/
theorem raw_vs_feedforward_tooth :
    ∃ p : SimpleEquiv (State Goldilocks) (State Goldilocks),
      rawTrunc p (p.invFun (one, zero, zero)) = one ∧
      jiveCompress (fun _ => zero) p (p.invFun (one, zero, zero)) ≠ one := by
  refine ⟨SimpleEquiv.refl _, rfl, ?_⟩
  decide


/-- Feed-forward does not guarantee security for every fixed permutation. -/
theorem identity_collision_tooth :
    ∃ x y : State Goldilocks, x ≠ y ∧
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x =
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) y := by
  exact ⟨(zero, zero, zero), (zero, one, zero), by decide, rfl⟩


/-- A zero-query guess can succeed; verification must extend the charged transcript. -/
theorem unchecked_preimage_tooth : ∃ x : State Goldilocks,
    jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x = zero ∧
    ¬ ∃ y, (x, y) ∈ ([] : List (State Goldilocks × State Goldilocks)) := by
  exact ⟨(zero, zero, zero), by decide, by intro ⟨_, h⟩; cases h⟩

#verify_constructive
  Qsag.CrossProtocol.inverse_feedforward_relation
  Qsag.CrossProtocol.raw_vs_feedforward_tooth
  Qsag.CrossProtocol.identity_collision_tooth
  Qsag.CrossProtocol.unchecked_preimage_tooth
end Qsag.CrossProtocol
end

/-! ### Registry-digest KAT for the Sbox7 two-key fixture

`poseidon2Hash32` is evaluated here because its sponge internals are sealed downstream.
`Protocol/Aggregation/Poseidon2AlgebraicAndRecursiveHem` proves that these bytes are its
`encodeRegistry` of the one-shard, two-key fixture policy with threshold `thr`. -/
public section
namespace Qsag

/-- The 188 canonical registry bytes of the one-shard, two-key Sbox7 fixture policy; only the
    threshold byte (index 7) varies. -/
def sbox7TwoKeyRegistryBytes (thr : UInt8) : List UInt8 :=
  [1, 185, 1, 5, 1, 0, 1] ++ [thr] ++
  [22, 81, 83, 65, 71, 46, 80, 81, 46, 83, 85, 73, 84, 69, 46, 83, 66, 79, 88, 55, 47, 118, 49,
   17, 8, 1, 2, 1, 2, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 137, 1, 2, 67, 2, 32] ++
  List.replicate 32 0 ++ [32] ++ List.replicate 32 0 ++ [67, 2, 32] ++
  List.replicate 31 0 ++ [1, 32] ++ List.replicate 31 0 ++ [1]

set_option maxRecDepth 16384 in
/-- Lowering the threshold byte from `2` to `1` changes the `poseidon2Hash32` registry digest. -/
theorem poseidon2Hash32_sbox7TwoKeyRegistry_threshold_kat :
    ¬ (poseidon2Hash32 (sbox7TwoKeyRegistryBytes 1) =
      poseidon2Hash32 (sbox7TwoKeyRegistryBytes 2)) := by
  decide +kernel

#export_eqns sbox7TwoKeyRegistryBytes
#verify_constructive poseidon2Hash32_sbox7TwoKeyRegistry_threshold_kat

/-! ### Duplex-chain KATs for the recursive verifier transcript

The permutation is evaluated here because `lane4Add`, `state12Add` and the round helpers are sealed
downstream. `Protocol/Aggregation/RecursivePoseidon2WhirSoundness` proves that its transcript
sponge is this chain on the block addends of its frames, and cites the two KATs below. -/

/-- Rate-8 duplex from the zero state: add each block to the state, then permute. -/
def poseidon2DuplexChain (blocks : List Poseidon2State12) : Poseidon2State12 :=
  blocks.foldl (fun st b => poseidon2Perm12 (state12Add st b)) ⟨lane4Zero, lane4Zero, lane4Zero⟩

/-- A duplex block addend: six rate limbs `r0..r5` and the two capacity limbs `c10`, `c11`. -/
def poseidon2DuplexBlock (r0 r1 r2 r3 r4 r5 c10 c11 : Nat) : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat r0, Goldilocks.ofNat r1, Goldilocks.ofNat r2, Goldilocks.ofNat r3⟩,
   ⟨Goldilocks.ofNat r4, Goldilocks.ofNat r5, Goldilocks.zero, Goldilocks.zero⟩,
   ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.ofNat c10, Goldilocks.ofNat c11⟩⟩

/-- Blocks of two absorbed one-limb messages `a`, `b` (tag `10`), each followed by an empty
    squeeze frame (tag `11`). -/
def poseidon2SwapRoundKatBlocks (a b : Nat) : List Poseidon2State12 :=
  [poseidon2DuplexBlock a 1 0 0 0 0 10 1, poseidon2DuplexBlock 1 0 0 0 0 0 11 0,
   poseidon2DuplexBlock b 1 0 0 0 0 10 1, poseidon2DuplexBlock 1 0 0 0 0 0 11 0]

set_option maxRecDepth 100000 in
/-- Swapping the two absorbed messages changes the squeezed lane. -/
theorem poseidon2DuplexChain_swap_round_kat :
    ¬ ((poseidon2DuplexChain (poseidon2SwapRoundKatBlocks 1 2)).b0 =
      (poseidon2DuplexChain (poseidon2SwapRoundKatBlocks 2 1)).b0) := by
  decide +kernel

/-- Blocks of the child-verifier transcript prefix up to the first fold challenge, at bottom
    depth `1`, canopy depth `0`, zero digests and claim, and two four-limb sumcheck messages
    `[a, 0, 0, 0]`, `[b, 0, 0, 0]`. -/
def poseidon2SwapSumcheckKatBlocks (a b : Nat) : List Poseidon2State12 :=
  [poseidon2DuplexBlock 0x4657484952000001 1 0 1 0 0 1 3,
   poseidon2DuplexBlock 0 0 0 0 0 0 2 12, poseidon2DuplexBlock 0 0 0 0 0 0 0 0,
   poseidon2DuplexBlock 1 0 0 0 0 0 0 0,
   poseidon2DuplexBlock 0 0 0 0 1 0 3 4,
   poseidon2DuplexBlock a 0 0 0 1 0 10 4, poseidon2DuplexBlock 1 0 0 0 0 0 11 0,
   poseidon2DuplexBlock b 0 0 0 1 0 10 4, poseidon2DuplexBlock 1 0 0 0 0 0 11 0,
   poseidon2DuplexBlock 1 0 0 0 0 0 12 0, poseidon2DuplexBlock 1 0 0 0 0 0 13 0]

set_option maxRecDepth 100000 in
/-- Swapping the two sumcheck messages changes the lane squeezed for the fold challenge. -/
theorem poseidon2DuplexChain_swap_sumcheck_kat :
    ¬ ((poseidon2DuplexChain (poseidon2SwapSumcheckKatBlocks 1 0)).b0 =
      (poseidon2DuplexChain (poseidon2SwapSumcheckKatBlocks 0 1)).b0) := by
  decide +kernel

#export_eqns poseidon2DuplexChain poseidon2DuplexBlock poseidon2SwapRoundKatBlocks
  poseidon2SwapSumcheckKatBlocks
#verify_constructive poseidon2DuplexChain_swap_round_kat poseidon2DuplexChain_swap_sumcheck_kat

/-! ### `Poseidon2` permutation, compression, and compact Jorts KATs for `Tests/CompositionInstances` -/

section CompositionInstancesPoseidon2Kats
set_option exponentiation.threshold 2048
set_option maxRecDepth 1000000

theorem poseidon2Perm12_realX_kat :
    ((poseidon2Perm12
      ⟨⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4⟩,
       ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7, Goldilocks.ofNat 8⟩,
       ⟨Goldilocks.ofNat 0x515341474D524B4C, Goldilocks.ofNat 9, Goldilocks.ofNat 10,
        Goldilocks.ofNat 0x504F53325F474C31⟩⟩).b0.x0).val ≠ 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem poseidon2CompressWeighted_realX_kat :
    ((poseidon2CompressWeighted
      ⟨⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4⟩,
       ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7, Goldilocks.ofNat 8⟩,
       ⟨Goldilocks.ofNat 0x515341474D524B4C, Goldilocks.ofNat 9, Goldilocks.ofNat 10,
        Goldilocks.ofNat 0x504F53325F474C31⟩⟩).x0).val ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem poseidon2Inv_realY_feedforward_kat :
    let invY := poseidon2Perm12Inv
      ⟨⟨Goldilocks.ofNat 7, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
       lane4Zero, lane4Zero⟩
    ((lane4Add ⟨Goldilocks.ofNat 7, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
        (lane4Add invY.b0
          (lane4Add (lane4Scale (Goldilocks.ofNat 2) invY.b1)
            (lane4Scale (Goldilocks.ofNat 4) invY.b2)))).x0).val ≠ 7 := by
  decide +kernel

def compactPackWotsAddr (layer kpIdx chainIdx stepIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat
    ((layer % 64) * (2 ^ 44) +
     (kpIdx % (2 ^ 28)) * (2 ^ 16) +
     (chainIdx % 4096) * 16 +
     (stepIdx % 16))

def compactWotsSecret (skSeed pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat) : Lane4 :=
  poseidon2CompressWeighted
    ⟨skSeed, pkSeed,
     ⟨Goldilocks.ofNat 0x5153414757505246,
      compactPackWotsAddr layer kpIdx chainIdx 0,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩

def compactWotsStep (pkSeed cur : Lane4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) : Lane4 :=
  poseidon2CompressWeighted
    ⟨cur, pkSeed,
     ⟨Goldilocks.ofNat 0x5153414757535450,
      compactPackWotsAddr layer kpIdx chainIdx stepIdx,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩

def compactIterAt {σ : Type} (step : Nat → σ → σ) : Nat → Nat → σ → σ
  | 0, _, s => s
  | n + 1, idx, s => compactIterAt step n (idx + 1) (step idx s)

def compactWotsWalk (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx steps idx : Nat)
    (s : Lane4) : Lane4 :=
  compactIterAt (fun stp v => compactWotsStep pkSeed v layer treeIdx kpIdx chainIdx stp) steps idx s

def compactWotsPk2 (pkSeed : Lane4) (layer treeIdx kpIdx : Nat) (e0 e1 : Lane4) : Lane4 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pkSeed,
     ⟨layerKp, Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32)), Goldilocks.ofNat 2⟩,
     ⟨Goldilocks.ofNat 0x5153414757504B31, Goldilocks.zero, Goldilocks.zero,
      Goldilocks.ofNat 0x504F53325F474C31⟩⟩
  let stAbs := poseidon2Perm12 ⟨lane4Add st0.b0 e0, lane4Add st0.b1 e1, st0.b2⟩
  let stPad : Poseidon2State12 :=
    ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
     stAbs.b1, stAbs.b2⟩
  (poseidon2Perm12 stPad).b0

def compactHonestWotsPk (skSeed pkSeed : Lane4) (layer treeIdx kpIdx : Nat) : Lane4 :=
  compactWotsPk2 pkSeed layer treeIdx kpIdx
    (compactWotsWalk pkSeed layer treeIdx kpIdx 0 3 0
      (compactWotsSecret skSeed pkSeed layer treeIdx kpIdx 0))
    (compactWotsWalk pkSeed layer treeIdx kpIdx 1 3 0
      (compactWotsSecret skSeed pkSeed layer treeIdx kpIdx 1))

def compactMerkleNode (pkSeed : Lane4) (layer treeIdx level nodeIdx : Nat)
    (left right : Lane4) : Lane4 :=
  let meta0 := Goldilocks.ofNat
    ((layer % 65536) * (2 ^ 48) + (level % 65536) * (2 ^ 32) + (nodeIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pkSeed, left,
     ⟨Goldilocks.ofNat 0x515341474D524B4C, meta0,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
  let b0' := lane4Add st0.b0 right
  let b1' : Lane4 :=
    ⟨Goldilocks.add st0.b1.x0 Goldilocks.one,
     Goldilocks.add st0.b1.x1 (Goldilocks.ofNat 0x504F53325F474C31),
     st0.b1.x2, st0.b1.x3⟩
  (poseidon2Perm12 ⟨b0', b1', st0.b2⟩).b0

def compactJortsPkRoot (skSeed pkSeed : Lane4) : Lane4 :=
  compactMerkleNode pkSeed 0 0 1 0
    (compactHonestWotsPk skSeed pkSeed 0 0 0)
    (compactHonestWotsPk skSeed pkSeed 0 0 1)

def compactJortsHmsgStateful (pkSeed pkRoot rRand : Lane4) (msg : List UInt8)
    (kpIdx tswCtr : Nat) :
    Goldilocks × Goldilocks × Goldilocks × Goldilocks × Goldilocks :=
  let pkBytes : List UInt8 :=
    (1 : UInt8) ::
      be 8 pkSeed.x0.val ++ be 8 pkSeed.x1.val ++ be 8 pkSeed.x2.val ++ be 8 pkSeed.x3.val ++
      be 8 pkRoot.x0.val ++ be 8 pkRoot.x1.val ++ be 8 pkRoot.x2.val ++ be 8 pkRoot.x3.val
  let framed := encodeMultiFrame
    [[0x51, 0x53, 0x41, 0x47, 0x2e, 0x4d, 0x55, 0x2f, 0x76, 0x32], pkBytes, msg]
  let h32 := poseidon2Hash32 framed
  let b := (h32 ++ List.replicate (32 - h32.length) (0 : UInt8)).take 32
  let m0 := Goldilocks.ofNat (ofBE (b.take 7))
  let m1 := Goldilocks.ofNat (ofBE ((b.drop 7).take 7))
  let m2 := Goldilocks.ofNat (ofBE ((b.drop 14).take 7))
  let m3 := Goldilocks.ofNat (ofBE ((b.drop 21).take 7))
  let m4 := Goldilocks.ofNat (ofBE ((b.drop 28).take 4))
  let kpCtr := Goldilocks.ofNat ((kpIdx % (2 ^ 32)) * (2 ^ 32) + (tswCtr % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pkSeed, pkRoot,
     ⟨Goldilocks.ofNat 0x51534147484D5331, kpCtr, m4, Goldilocks.ofNat 0x504F53325F474C31⟩⟩
  let st1 := poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 ⟨m0, m1, m2, m3⟩, st0.b2⟩
  let st2 := poseidon2Perm12
    ⟨⟨Goldilocks.add st1.b0.x0 Goldilocks.one, st1.b0.x1, st1.b0.x2, st1.b0.x3⟩,
     st1.b1, st1.b2⟩
  (st2.b0.x0, st2.b0.x1, st2.b0.x2, st2.b0.x3, st2.b1.x0)

def compactCheck5Limbs63
    (h : Goldilocks × Goldilocks × Goldilocks × Goldilocks × Goldilocks) : Bool :=
  (h.1.val < 2 ^ 63) &&
  (h.2.1.val < 2 ^ 63) &&
  (h.2.2.1.val < 2 ^ 63) &&
  (h.2.2.2.1.val < 2 ^ 63) &&
  (h.2.2.2.2.val < 2 ^ 63)

def compactJortsSign1 (skSeed pkSeed pkRoot : Lane4) (msg : List UInt8)
    (rRand : Lane4) (leafIdx ctr : Nat) : List Lane4 × List Lane4 :=
  let kp0 := leafIdx % 2
  let tr0 := leafIdx / 2
  let hmsg := compactJortsHmsgStateful pkSeed pkRoot rRand msg kp0 ctr
  let chains :=
    if compactCheck5Limbs63 hmsg then
      let d0 := hmsg.1.val % 4
      let d1 := (hmsg.1.val / 4) % 4
      [compactWotsWalk pkSeed 0 tr0 kp0 0 d0 0 (compactWotsSecret skSeed pkSeed 0 tr0 kp0 0),
       compactWotsWalk pkSeed 0 tr0 kp0 1 d1 0 (compactWotsSecret skSeed pkSeed 0 tr0 kp0 1)]
    else []
  let sibIdx := if kp0 % 2 == 0 then kp0 + 1 else kp0 - 1
  let sib := compactHonestWotsPk skSeed pkSeed 0 tr0 sibIdx
  (chains, [sib])

def compactJortsVerify1 (pkSeed pkRoot : Lane4) (msg : List UInt8)
    (rRand : Lane4) (leafIdx ctr : Nat) (c0 c1 s0 : Lane4) : Bool :=
  if !(leafIdx < 2) then false
  else
    let kp0 := leafIdx % 2
    let tr0 := leafIdx / 2
    let hmsg := compactJortsHmsgStateful pkSeed pkRoot rRand msg kp0 ctr
    if compactCheck5Limbs63 hmsg then
      let d0 := hmsg.1.val % 4
      let d1 := (hmsg.1.val / 4) % 4
      if (d0 + (d1 + 0)) == 3 then
        let ep0 := compactWotsWalk pkSeed 0 tr0 kp0 0 (3 - d0) d0 c0
        let ep1 := compactWotsWalk pkSeed 0 tr0 kp0 1 (3 - d1) d1 c1
        let wotsPk := compactWotsPk2 pkSeed 0 tr0 kp0 ep0 ep1
        let root0 :=
          if kp0 % 2 == 0 then compactMerkleNode pkSeed 0 tr0 1 (kp0 / 2) wotsPk s0
          else compactMerkleNode pkSeed 0 tr0 1 (kp0 / 2) s0 wotsPk
        root0 == pkRoot
      else false
    else false

theorem compactPackWotsAddr_eq (layer kpIdx chainIdx stepIdx : Nat) :
    compactPackWotsAddr layer kpIdx chainIdx stepIdx =
      Goldilocks.ofNat
        ((layer % 64) * (2 ^ 44) +
         (kpIdx % (2 ^ 28)) * (2 ^ 16) +
         (chainIdx % 4096) * 16 +
         (stepIdx % 16)) := by rfl

theorem compactWotsSecret_eq_def (skSeed pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat) :
    compactWotsSecret skSeed pkSeed layer treeIdx kpIdx chainIdx =
      poseidon2CompressWeighted
        ⟨skSeed, pkSeed,
         ⟨Goldilocks.ofNat 0x5153414757505246,
          compactPackWotsAddr layer kpIdx chainIdx 0,
          Goldilocks.ofNat (treeIdx % (2 ^ 32)),
          Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩ := by rfl

theorem compactWotsStep_eq_def (pkSeed cur : Lane4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) :
    compactWotsStep pkSeed cur layer treeIdx kpIdx chainIdx stepIdx =
      poseidon2CompressWeighted
        ⟨cur, pkSeed,
         ⟨Goldilocks.ofNat 0x5153414757535450,
          compactPackWotsAddr layer kpIdx chainIdx stepIdx,
          Goldilocks.ofNat (treeIdx % (2 ^ 32)),
          Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩ := by rfl

theorem compactWotsWalk_zero (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx idx : Nat) (s : Lane4) :
    compactWotsWalk pkSeed layer treeIdx kpIdx chainIdx 0 idx s = s := by
  unfold compactWotsWalk compactIterAt
  rfl

theorem compactWotsWalk_succ (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx n idx : Nat) (s : Lane4) :
    compactWotsWalk pkSeed layer treeIdx kpIdx chainIdx (n + 1) idx s =
      compactWotsWalk pkSeed layer treeIdx kpIdx chainIdx n (idx + 1)
        (compactWotsStep pkSeed s layer treeIdx kpIdx chainIdx idx) := by
  unfold compactWotsWalk
  rw [compactIterAt]

theorem compactWotsPk2_eq_def (pkSeed : Lane4) (layer treeIdx kpIdx : Nat) (e0 e1 : Lane4) :
    compactWotsPk2 pkSeed layer treeIdx kpIdx e0 e1 =
      let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
      let st0 := poseidon2Perm12
        ⟨pkSeed,
         ⟨layerKp, Goldilocks.ofNat (treeIdx % (2 ^ 32)),
          Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32)), Goldilocks.ofNat 2⟩,
         ⟨Goldilocks.ofNat 0x5153414757504B31, Goldilocks.zero, Goldilocks.zero,
          Goldilocks.ofNat 0x504F53325F474C31⟩⟩
      let stAbs := poseidon2Perm12 ⟨lane4Add st0.b0 e0, lane4Add st0.b1 e1, st0.b2⟩
      let stPad : Poseidon2State12 :=
        ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
         stAbs.b1, stAbs.b2⟩
      (poseidon2Perm12 stPad).b0 := by rfl

theorem compactHonestWotsPk_eq_def (skSeed pkSeed : Lane4) (layer treeIdx kpIdx : Nat) :
    compactHonestWotsPk skSeed pkSeed layer treeIdx kpIdx =
      compactWotsPk2 pkSeed layer treeIdx kpIdx
        (compactWotsWalk pkSeed layer treeIdx kpIdx 0 3 0
          (compactWotsSecret skSeed pkSeed layer treeIdx kpIdx 0))
        (compactWotsWalk pkSeed layer treeIdx kpIdx 1 3 0
          (compactWotsSecret skSeed pkSeed layer treeIdx kpIdx 1)) := by rfl

theorem compactMerkleNode_eq_def (pkSeed : Lane4) (layer treeIdx level nodeIdx : Nat)
    (left right : Lane4) :
    compactMerkleNode pkSeed layer treeIdx level nodeIdx left right =
      let meta0 := Goldilocks.ofNat
        ((layer % 65536) * (2 ^ 48) + (level % 65536) * (2 ^ 32) + (nodeIdx % (2 ^ 32)))
      let st0 := poseidon2Perm12
        ⟨pkSeed, left,
         ⟨Goldilocks.ofNat 0x515341474D524B4C, meta0,
          Goldilocks.ofNat (treeIdx % (2 ^ 32)),
          Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
      let b0' := lane4Add st0.b0 right
      let b1' : Lane4 :=
        ⟨Goldilocks.add st0.b1.x0 Goldilocks.one,
         Goldilocks.add st0.b1.x1 (Goldilocks.ofNat 0x504F53325F474C31),
         st0.b1.x2, st0.b1.x3⟩
      (poseidon2Perm12 ⟨b0', b1', st0.b2⟩).b0 := by rfl

theorem compactJortsPkRoot_eq_def (skSeed pkSeed : Lane4) :
    compactJortsPkRoot skSeed pkSeed =
      compactMerkleNode pkSeed 0 0 1 0
        (compactHonestWotsPk skSeed pkSeed 0 0 0)
        (compactHonestWotsPk skSeed pkSeed 0 0 1) := by rfl

theorem compactJortsHmsgStateful_eq_def (pkSeed pkRoot rRand : Lane4) (msg : List UInt8)
    (kpIdx tswCtr : Nat) :
    compactJortsHmsgStateful pkSeed pkRoot rRand msg kpIdx tswCtr =
      let pkBytes : List UInt8 :=
        (1 : UInt8) ::
          be 8 pkSeed.x0.val ++ be 8 pkSeed.x1.val ++ be 8 pkSeed.x2.val ++ be 8 pkSeed.x3.val ++
          be 8 pkRoot.x0.val ++ be 8 pkRoot.x1.val ++ be 8 pkRoot.x2.val ++ be 8 pkRoot.x3.val
      let framed := encodeMultiFrame
        [[0x51, 0x53, 0x41, 0x47, 0x2e, 0x4d, 0x55, 0x2f, 0x76, 0x32], pkBytes, msg]
      let h32 := poseidon2Hash32 framed
      let b := (h32 ++ List.replicate (32 - h32.length) (0 : UInt8)).take 32
      let m0 := Goldilocks.ofNat (ofBE (b.take 7))
      let m1 := Goldilocks.ofNat (ofBE ((b.drop 7).take 7))
      let m2 := Goldilocks.ofNat (ofBE ((b.drop 14).take 7))
      let m3 := Goldilocks.ofNat (ofBE ((b.drop 21).take 7))
      let m4 := Goldilocks.ofNat (ofBE ((b.drop 28).take 4))
      let kpCtr := Goldilocks.ofNat ((kpIdx % (2 ^ 32)) * (2 ^ 32) + (tswCtr % (2 ^ 32)))
      let st0 := poseidon2Perm12
        ⟨pkSeed, pkRoot,
         ⟨Goldilocks.ofNat 0x51534147484D5331, kpCtr, m4, Goldilocks.ofNat 0x504F53325F474C31⟩⟩
      let st1 := poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 ⟨m0, m1, m2, m3⟩, st0.b2⟩
      let st2 := poseidon2Perm12
        ⟨⟨Goldilocks.add st1.b0.x0 Goldilocks.one, st1.b0.x1, st1.b0.x2, st1.b0.x3⟩,
         st1.b1, st1.b2⟩
      (st2.b0.x0, st2.b0.x1, st2.b0.x2, st2.b0.x3, st2.b1.x0) := by rfl

theorem compactCheck5Limbs63_eq_def
    (h : Goldilocks × Goldilocks × Goldilocks × Goldilocks × Goldilocks) :
    compactCheck5Limbs63 h =
      ((h.1.val < 2 ^ 63) &&
       (h.2.1.val < 2 ^ 63) &&
       (h.2.2.1.val < 2 ^ 63) &&
       (h.2.2.2.1.val < 2 ^ 63) &&
       (h.2.2.2.2.val < 2 ^ 63)) := by rfl

theorem compactJortsSign1_eq_def (skSeed pkSeed pkRoot : Lane4) (msg : List UInt8)
    (rRand : Lane4) (leafIdx ctr : Nat) :
    compactJortsSign1 skSeed pkSeed pkRoot msg rRand leafIdx ctr =
      let kp0 := leafIdx % 2
      let tr0 := leafIdx / 2
      let hmsg := compactJortsHmsgStateful pkSeed pkRoot rRand msg kp0 ctr
      let chains :=
        if compactCheck5Limbs63 hmsg then
          let d0 := hmsg.1.val % 4
          let d1 := (hmsg.1.val / 4) % 4
          [compactWotsWalk pkSeed 0 tr0 kp0 0 d0 0 (compactWotsSecret skSeed pkSeed 0 tr0 kp0 0),
           compactWotsWalk pkSeed 0 tr0 kp0 1 d1 0 (compactWotsSecret skSeed pkSeed 0 tr0 kp0 1)]
        else []
      let sibIdx := if kp0 % 2 == 0 then kp0 + 1 else kp0 - 1
      let sib := compactHonestWotsPk skSeed pkSeed 0 tr0 sibIdx
      (chains, [sib]) := by rfl

theorem compactJortsVerify1_eq_def (pkSeed pkRoot : Lane4) (msg : List UInt8)
    (rRand : Lane4) (leafIdx ctr : Nat) (c0 c1 s0 : Lane4) :
    compactJortsVerify1 pkSeed pkRoot msg rRand leafIdx ctr c0 c1 s0 =
      if !(leafIdx < 2) then false
      else
        let kp0 := leafIdx % 2
        let tr0 := leafIdx / 2
        let hmsg := compactJortsHmsgStateful pkSeed pkRoot rRand msg kp0 ctr
        if compactCheck5Limbs63 hmsg then
          let d0 := hmsg.1.val % 4
          let d1 := (hmsg.1.val / 4) % 4
          if (d0 + (d1 + 0)) == 3 then
            let ep0 := compactWotsWalk pkSeed 0 tr0 kp0 0 (3 - d0) d0 c0
            let ep1 := compactWotsWalk pkSeed 0 tr0 kp0 1 (3 - d1) d1 c1
            let wotsPk := compactWotsPk2 pkSeed 0 tr0 kp0 ep0 ep1
            let root0 :=
              if kp0 % 2 == 0 then compactMerkleNode pkSeed 0 tr0 1 (kp0 / 2) wotsPk s0
              else compactMerkleNode pkSeed 0 tr0 1 (kp0 / 2) s0 wotsPk
            root0 == pkRoot
          else false
        else false := by rfl

section CompactJortsKats
set_option exponentiation.threshold 2048
set_option maxRecDepth 1000000

private def cjLane (a b c d : Nat) : Lane4 :=
  ⟨Goldilocks.ofNat a, Goldilocks.ofNat b, Goldilocks.ofNat c, Goldilocks.ofNat d⟩

private def cjSk0 : Lane4 := cjLane 11 22 33 44
private def cjSk1 : Lane4 := cjLane 12 23 34 45
private def cjPkSeed : Lane4 := cjLane 55 66 77 88
private def cjRRand : Lane4 := cjLane 99 101 102 103
private def cjPkRoot0 : Lane4 :=
  cjLane 4411130677596272051 12386187803866016865 4846206855630815541 13194810747827022671
private def cjPkRoot1 : Lane4 :=
  cjLane 17576564533966561130 16051823357764822570 14727583026633534692 1732328166828656438

private def cjAuditC00 : Lane4 :=
  cjLane 8311586201798180139 8396487982263648832 16278201376156863497 5873789825944876137
private def cjAuditC01 : Lane4 :=
  cjLane 11009790873695555519 14395406594536956999 11951049901538821830 10044662254597907680
private def cjSib0 : Lane4 :=
  cjLane 5524291857455771020 16376422686410664307 15963494650740044646 18098363549869475062
private def cjAuditC10 : Lane4 :=
  cjLane 7345396832099288313 5628321512706338704 2904634915904338214 11778081422095187519
private def cjAuditC11 : Lane4 :=
  cjLane 6519691662884691569 6995657412139860735 8574290930621241436 12609139020484668794
private def cjSib1 : Lane4 :=
  cjLane 13388180661509288011 5130805258596798721 8406673262598715289 15360960474733464499

private def cjHybC00 : Lane4 :=
  cjLane 4152917893602010253 5344412802567744713 18406927796743773750 1962659585794765281
private def cjHybC01 : Lane4 :=
  cjLane 12873018474816122043 2869910227242953051 3097284758269903553 18326636155894048790
private def cjHybC10 : Lane4 :=
  cjLane 10036846859147774993 15499800327978969217 15476824389852128619 15451031862181482938
private def cjHybC11 : Lane4 :=
  cjLane 14010823692816899133 11663312065820974772 3799621797402719272 6812636063505864400

private def cjTrPaid0 : List UInt8 :=
  [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
   216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
   92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
   173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
   149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
   0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]

private def cjTrPaid1 : List UInt8 :=
  [2, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
   216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
   92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
   173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
   149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
   0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]

private def cjTrUnpaid0 : List UInt8 :=
  [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
   216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
   92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
   173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
   149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
   0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 122]

private def cjTrRogue1 : List UInt8 :=
  [2, 5, 1, 0, 1, 1, 1, 120, 130, 148, 209, 221, 48, 122, 11, 201, 31, 97, 23, 207, 212, 76, 157,
   190, 150, 250, 193, 174, 105, 54, 248, 197, 104, 124, 130, 106, 159, 53, 46, 94, 59, 166, 234,
   77, 144, 26, 197, 209, 246, 48, 107, 133, 48, 181, 232, 37, 98, 85, 103, 78, 54, 227, 77, 248,
   234, 245, 170, 196, 166, 208, 0, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67,
   25, 7, 149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
   0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]

theorem compactJortsPkRoot_kat0 :
    compactJortsPkRoot ⟨Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩ =
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩ := by
  decide +kernel

theorem compactJortsPkRoot_kat1 :
    compactJortsPkRoot ⟨Goldilocks.ofNat 12, Goldilocks.ofNat 23, Goldilocks.ofNat 34, Goldilocks.ofNat 45⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩ =
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩ := by
  decide +kernel

theorem compactJortsSign1_audit0 :
    compactJortsSign1
      ⟨Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 37 =
      ([⟨Goldilocks.ofNat 8311586201798180139, Goldilocks.ofNat 8396487982263648832,
         Goldilocks.ofNat 16278201376156863497, Goldilocks.ofNat 5873789825944876137⟩,
        ⟨Goldilocks.ofNat 11009790873695555519, Goldilocks.ofNat 14395406594536956999,
         Goldilocks.ofNat 11951049901538821830, Goldilocks.ofNat 10044662254597907680⟩],
       [⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
         Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩]) := by
  decide +kernel

theorem compactJortsSign1_audit1 :
    compactJortsSign1
      ⟨Goldilocks.ofNat 12, Goldilocks.ofNat 23, Goldilocks.ofNat 34, Goldilocks.ofNat 45⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 45 =
      ([⟨Goldilocks.ofNat 7345396832099288313, Goldilocks.ofNat 5628321512706338704,
         Goldilocks.ofNat 2904634915904338214, Goldilocks.ofNat 11778081422095187519⟩,
        ⟨Goldilocks.ofNat 6519691662884691569, Goldilocks.ofNat 6995657412139860735,
         Goldilocks.ofNat 8574290930621241436, Goldilocks.ofNat 12609139020484668794⟩],
       [⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
         Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩]) := by
  decide +kernel

theorem compactJortsVerify1_audit_accepts0 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 37
      ⟨Goldilocks.ofNat 8311586201798180139, Goldilocks.ofNat 8396487982263648832,
       Goldilocks.ofNat 16278201376156863497, Goldilocks.ofNat 5873789825944876137⟩
      ⟨Goldilocks.ofNat 11009790873695555519, Goldilocks.ofNat 14395406594536956999,
       Goldilocks.ofNat 11951049901538821830, Goldilocks.ofNat 10044662254597907680⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = true := by
  decide +kernel

theorem compactJortsVerify1_audit_accepts1 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 45
      ⟨Goldilocks.ofNat 7345396832099288313, Goldilocks.ofNat 5628321512706338704,
       Goldilocks.ofNat 2904634915904338214, Goldilocks.ofNat 11778081422095187519⟩
      ⟨Goldilocks.ofNat 6519691662884691569, Goldilocks.ofNat 6995657412139860735,
       Goldilocks.ofNat 8574290930621241436, Goldilocks.ofNat 12609139020484668794⟩
      ⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
       Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩ = true := by
  decide +kernel

theorem compactJortsVerify1_audit_rejects_otherMsg0 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [0x51, 0x53, 0x41, 0x48]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 37
      ⟨Goldilocks.ofNat 8311586201798180139, Goldilocks.ofNat 8396487982263648832,
       Goldilocks.ofNat 16278201376156863497, Goldilocks.ofNat 5873789825944876137⟩
      ⟨Goldilocks.ofNat 11009790873695555519, Goldilocks.ofNat 14395406594536956999,
       Goldilocks.ofNat 11951049901538821830, Goldilocks.ofNat 10044662254597907680⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = false := by
  decide +kernel

theorem compactJortsVerify1_audit_rejects_otherMsg1 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [0x51, 0x53, 0x41, 0x48]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 45
      ⟨Goldilocks.ofNat 7345396832099288313, Goldilocks.ofNat 5628321512706338704,
       Goldilocks.ofNat 2904634915904338214, Goldilocks.ofNat 11778081422095187519⟩
      ⟨Goldilocks.ofNat 6519691662884691569, Goldilocks.ofNat 6995657412139860735,
       Goldilocks.ofNat 8574290930621241436, Goldilocks.ofNat 12609139020484668794⟩
      ⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
       Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩ = false := by
  decide +kernel

theorem compactJortsVerify1_audit_rejects_otherKey :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 37
      ⟨Goldilocks.ofNat 8311586201798180139, Goldilocks.ofNat 8396487982263648832,
       Goldilocks.ofNat 16278201376156863497, Goldilocks.ofNat 5873789825944876137⟩
      ⟨Goldilocks.ofNat 11009790873695555519, Goldilocks.ofNat 14395406594536956999,
       Goldilocks.ofNat 11951049901538821830, Goldilocks.ofNat 10044662254597907680⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = false := by
  decide +kernel

theorem compactJortsVerify1_audit_rejects_tamperedRand :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [0x51, 0x53, 0x41, 0x47]
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      0 37
      ⟨Goldilocks.ofNat 8311586201798180139, Goldilocks.ofNat 8396487982263648832,
       Goldilocks.ofNat 16278201376156863497, Goldilocks.ofNat 5873789825944876137⟩
      ⟨Goldilocks.ofNat 11009790873695555519, Goldilocks.ofNat 14395406594536956999,
       Goldilocks.ofNat 11951049901538821830, Goldilocks.ofNat 10044662254597907680⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = false := by
  decide +kernel

theorem compactJortsSign1_hybrid0 :
    compactJortsSign1
      ⟨Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 21 =
      ([⟨Goldilocks.ofNat 4152917893602010253, Goldilocks.ofNat 5344412802567744713,
         Goldilocks.ofNat 18406927796743773750, Goldilocks.ofNat 1962659585794765281⟩,
        ⟨Goldilocks.ofNat 12873018474816122043, Goldilocks.ofNat 2869910227242953051,
         Goldilocks.ofNat 3097284758269903553, Goldilocks.ofNat 18326636155894048790⟩],
       [⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
         Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩]) := by
  decide +kernel

theorem compactJortsSign1_hybrid1 :
    compactJortsSign1
      ⟨Goldilocks.ofNat 12, Goldilocks.ofNat 23, Goldilocks.ofNat 34, Goldilocks.ofNat 45⟩
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [2, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 122 =
      ([⟨Goldilocks.ofNat 10036846859147774993, Goldilocks.ofNat 15499800327978969217,
         Goldilocks.ofNat 15476824389852128619, Goldilocks.ofNat 15451031862181482938⟩,
        ⟨Goldilocks.ofNat 14010823692816899133, Goldilocks.ofNat 11663312065820974772,
         Goldilocks.ofNat 3799621797402719272, Goldilocks.ofNat 6812636063505864400⟩],
       [⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
         Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩]) := by
  decide +kernel

theorem compactJortsVerify1_hybrid_paid0 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 21
      ⟨Goldilocks.ofNat 4152917893602010253, Goldilocks.ofNat 5344412802567744713,
       Goldilocks.ofNat 18406927796743773750, Goldilocks.ofNat 1962659585794765281⟩
      ⟨Goldilocks.ofNat 12873018474816122043, Goldilocks.ofNat 2869910227242953051,
       Goldilocks.ofNat 3097284758269903553, Goldilocks.ofNat 18326636155894048790⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = true := by
  decide +kernel

theorem compactJortsVerify1_hybrid_paid1 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [2, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 122
      ⟨Goldilocks.ofNat 10036846859147774993, Goldilocks.ofNat 15499800327978969217,
       Goldilocks.ofNat 15476824389852128619, Goldilocks.ofNat 15451031862181482938⟩
      ⟨Goldilocks.ofNat 14010823692816899133, Goldilocks.ofNat 11663312065820974772,
       Goldilocks.ofNat 3799621797402719272, Goldilocks.ofNat 6812636063505864400⟩
      ⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
       Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩ = true := by
  decide +kernel

theorem compactJortsVerify1_hybrid_unpaid0 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 4411130677596272051, Goldilocks.ofNat 12386187803866016865,
       Goldilocks.ofNat 4846206855630815541, Goldilocks.ofNat 13194810747827022671⟩
      [1, 5, 1, 0, 1, 1, 1, 206, 73, 15, 23, 239, 92, 48, 234, 75, 102, 152, 130, 28, 89, 229, 182,
       216, 35, 70, 212, 124, 3, 104, 43, 36, 3, 143, 228, 38, 18, 223, 21, 43, 75, 67, 27, 105, 156,
       92, 201, 184, 206, 75, 28, 48, 223, 0, 28, 57, 117, 15, 89, 215, 207, 202, 102, 90, 173, 39,
       173, 45, 208, 180, 136, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67, 25, 7,
       149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 122]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      0 21
      ⟨Goldilocks.ofNat 4152917893602010253, Goldilocks.ofNat 5344412802567744713,
       Goldilocks.ofNat 18406927796743773750, Goldilocks.ofNat 1962659585794765281⟩
      ⟨Goldilocks.ofNat 12873018474816122043, Goldilocks.ofNat 2869910227242953051,
       Goldilocks.ofNat 3097284758269903553, Goldilocks.ofNat 18326636155894048790⟩
      ⟨Goldilocks.ofNat 5524291857455771020, Goldilocks.ofNat 16376422686410664307,
       Goldilocks.ofNat 15963494650740044646, Goldilocks.ofNat 18098363549869475062⟩ = false := by
  decide +kernel

theorem compactJortsVerify1_hybrid_rogue1 :
    compactJortsVerify1
      ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
      ⟨Goldilocks.ofNat 17576564533966561130, Goldilocks.ofNat 16051823357764822570,
       Goldilocks.ofNat 14727583026633534692, Goldilocks.ofNat 1732328166828656438⟩
      [2, 5, 1, 0, 1, 1, 1, 120, 130, 148, 209, 221, 48, 122, 11, 201, 31, 97, 23, 207, 212, 76, 157,
       190, 150, 250, 193, 174, 105, 54, 248, 197, 104, 124, 130, 106, 159, 53, 46, 94, 59, 166, 234,
       77, 144, 26, 197, 209, 246, 48, 107, 133, 48, 181, 232, 37, 98, 85, 103, 78, 54, 227, 77, 248,
       234, 245, 170, 196, 166, 208, 0, 201, 197, 141, 148, 57, 199, 227, 247, 109, 141, 53, 178, 67,
       25, 7, 149, 86, 29, 49, 79, 239, 0, 64, 168, 235, 189, 88, 222, 80, 188, 241, 127,
       0, 0, 0, 0, 0, 0, 0, 3, 112, 97, 121]
      ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
      1 122
      ⟨Goldilocks.ofNat 10036846859147774993, Goldilocks.ofNat 15499800327978969217,
       Goldilocks.ofNat 15476824389852128619, Goldilocks.ofNat 15451031862181482938⟩
      ⟨Goldilocks.ofNat 14010823692816899133, Goldilocks.ofNat 11663312065820974772,
       Goldilocks.ofNat 3799621797402719272, Goldilocks.ofNat 6812636063505864400⟩
      ⟨Goldilocks.ofNat 13388180661509288011, Goldilocks.ofNat 5130805258596798721,
       Goldilocks.ofNat 8406673262598715289, Goldilocks.ofNat 15360960474733464499⟩ = false := by
  decide +kernel

#verify_constructive
  Qsag.poseidon2Perm12_realX_kat
  Qsag.poseidon2CompressWeighted_realX_kat
  Qsag.poseidon2Inv_realY_feedforward_kat
  Qsag.compactJortsPkRoot_kat0
  Qsag.compactJortsPkRoot_kat1
  Qsag.compactJortsSign1_audit0
  Qsag.compactJortsSign1_audit1
  Qsag.compactJortsVerify1_audit_accepts0
  Qsag.compactJortsVerify1_audit_accepts1
  Qsag.compactJortsVerify1_audit_rejects_otherMsg0
  Qsag.compactJortsVerify1_audit_rejects_otherMsg1
  Qsag.compactJortsVerify1_audit_rejects_otherKey
  Qsag.compactJortsVerify1_audit_rejects_tamperedRand
  Qsag.compactJortsSign1_hybrid0
  Qsag.compactJortsSign1_hybrid1
  Qsag.compactJortsVerify1_hybrid_paid0
  Qsag.compactJortsVerify1_hybrid_paid1
  Qsag.compactJortsVerify1_hybrid_unpaid0
  Qsag.compactJortsVerify1_hybrid_rogue1
end CompactJortsKats
end CompositionInstancesPoseidon2Kats

end Qsag
end
