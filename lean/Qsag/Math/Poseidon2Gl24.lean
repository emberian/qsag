module
/-
# Qsag.Math.Poseidon2Gl24 — Algebraic Width-24 Goldilocks `Poseidon2-GL-w24` (`SECURITY.md §V2.10`)

Constructive Lean 4.35 specification and soundness proofs for `Poseidon2-GL-w24` over Goldilocks
$p = 2^{64} - 2^{32} + 1$, matching `crates/qsag-accel/src/poseidon2.rs`,
`crates/qsag-core/src/sponge/poseidon2.rs`, and `crates/qsag-agg/src/zk_hem/relation.rs` bit-for-bit:

1. **State Geometry (`w = 24 = 6 × 4`, `rate = 16`, `capacity = 8`, 7-limb = 56-byte digest):**
   - Two 7-limb (448-bit) child digests + 2 tweak limbs (`7 + 7 + 2 = 16`) compress in **1 single
     permutation call** (`236` $x^7$ S-boxes = **708 degree-3 R1CS rows** in `CubicR1csSystem`),
     giving `171.3` QROM collision bits and `235.3` QROM sponge bits at $t = 2^{88} + 2200$.
2. **Kronecker-Swapped External Matrix $M_E = M_4 \otimes P_6$ (`0` field muls):**
   - Constructive two-sided inverse `applyME24Inv` (`applyME24Inv_applyME24`, `applyME24_applyME24Inv`).
   - Kills Bariant / Merz–Rodríguez García (`ePrint 2026/306`) subspace trail skipping
     (`poseidon2_gl24_kronecker_swap_kills_subspace_skip`), paired against the block-circulant
     vulnerability witness `tooth_poseidon2_gl24_me_std_admits_subspace_skip`.
3. **Shift-Only Internal Matrix $M_I = J_{24} + \mathrm{diag}(-2^{23}, 1, 2, 4, \dots, 2^{22})$ (`0` field muls):**
   - Constructive Sherman–Morrison inverse `applyMI24Inv` (`applyMI24Inv_applyMI24`, `applyMI24_applyMI24Inv`,
     $\sigma = 25{,}165{,}821 / 2^{23} \not\equiv 0 \pmod p$).
   - Constructive proof of **maximal nonzero-sum differential/linear branch number `25`**
     (`poseidon2_gl24_mi_nonzero_sum_branch_25`).
4. **GSR-Hardened (`ePrint 2026/1692`) `(R_F, R_P) = (8, 44)` Permutation & 1-Call Jive Merkle Compression:**
   - 236 Grain-LFSR round constants, full constructive permutation `SimpleEquiv` (`poseidon2Gl24PermEquiv`),
     and kernel-verified KATs (`poseidon2Gl24Perm_seq_kat`, `poseidon2Gl24CompressMerkle_kat`).
-/

public import Qsag.Math.Goldilocks
public import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Poseidon2Gl24

set_option autoImplicit false

/-! ## 1. Width-24 State (`6 × 4` lanes) & Degree-7 S-Box Bijection -/

structure Lane4 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane4.ext {a b : Lane4}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2) (h3 : a.x3 = b.x3) : a = b := by
  cases a; cases b; simp only at *; subst h0 h1 h2 h3; rfl

structure Poseidon2State24 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  b3 : Lane4
  b4 : Lane4
  b5 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State24.ext {s t : Poseidon2State24}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2)
    (h3 : s.b3 = t.b3) (h4 : s.b4 = t.b4) (h5 : s.b5 = t.b5) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2 h3 h4 h5; rfl

def Poseidon2State24.toList (s : Poseidon2State24) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3,
   s.b3.x0, s.b3.x1, s.b3.x2, s.b3.x3,
   s.b4.x0, s.b4.x1, s.b4.x2, s.b4.x3,
   s.b5.x0, s.b5.x1, s.b5.x2, s.b5.x3]

structure Digest7 where
  d0 : Goldilocks
  d1 : Goldilocks
  d2 : Goldilocks
  d3 : Goldilocks
  d4 : Goldilocks
  d5 : Goldilocks
  d6 : Goldilocks
  deriving DecidableEq, Repr

def Digest7.toList (d : Digest7) : List Goldilocks :=
  [d.d0, d.d1, d.d2, d.d3, d.d4, d.d5, d.d6]

def lane4Zero : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane4Add (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1,
   Goldilocks.add a.x2 b.x2, Goldilocks.add a.x3 b.x3⟩

def lane4Sub (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
   Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩

def lane4Neg (a : Lane4) : Lane4 := lane4Sub lane4Zero a

def lane4Scale (c : Goldilocks) (a : Lane4) : Lane4 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1,
   Goldilocks.mul c a.x2, Goldilocks.mul c a.x3⟩

def lane4Sum (a : Lane4) : Goldilocks :=
  Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3)

def state24Zero : Poseidon2State24 :=
  ⟨lane4Zero, lane4Zero, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩

def state24Add (a b : Poseidon2State24) : Poseidon2State24 :=
  ⟨lane4Add a.b0 b.b0, lane4Add a.b1 b.b1, lane4Add a.b2 b.b2,
   lane4Add a.b3 b.b3, lane4Add a.b4 b.b4, lane4Add a.b5 b.b5⟩

def state24Sub (a b : Poseidon2State24) : Poseidon2State24 :=
  ⟨lane4Sub a.b0 b.b0, lane4Sub a.b1 b.b1, lane4Sub a.b2 b.b2,
   lane4Sub a.b3 b.b3, lane4Sub a.b4 b.b4, lane4Sub a.b5 b.b5⟩

def poseidon2DInv : Nat := 10540996611094048183

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
  unfold sbox7; dsimp only
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

def sbox7Inv (x : Goldilocks) : Goldilocks :=
  goldilocksPow x poseidon2DInv

private theorem pow_two_mul_nat (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

private theorem goldilocksPowAux_val (fuel : Nat) (base : Goldilocks) :
    ∀ (exp : Nat), exp < 2 ^ fuel →
      (goldilocksPowAux fuel base exp).val = (base.val ^ exp) % goldilocksPrime := by
  induction fuel with
  | zero =>
    intro exp hlt
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; rfl
  | succ fuel ih =>
    intro exp hlt
    simp only [goldilocksPowAux]
    if h0 : exp = 0 then
      subst h0; rfl
    else
      simp only [h0, ↓reduceIte]
      have hexpHalf : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hlt; omega
      have ihHalf := ih (exp / 2) hexpHalf
      let half := goldilocksPowAux fuel base (exp / 2)
      have hsq : (Goldilocks.mul half half).val = (base.val ^ (2 * (exp / 2))) % goldilocksPrime := by
        rw [Goldilocks.mul_val, ihHalf, ← Nat.mul_mod, ← pow_two_mul_nat]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide +kernel, ↓reduceIte]
        rw [hsq, show 2 * (exp / 2) = exp by omega]
      · simp only [hr1, ↓reduceIte]
        change (Goldilocks.mul (Goldilocks.mul half half) base).val = _
        rw [Goldilocks.mul_val, hsq, Nat.mod_mul_mod]
        conv => rhs; rw [show exp = 2 * (exp / 2) + 1 by omega, Nat.pow_add, Nat.pow_one]

private theorem goldilocksPow_val (x : Goldilocks) (exp : Nat) :
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
    rw [eq_of_beq hx0]
    cases he0 : (exp == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have heNe : exp ≠ 0 := by intro h; subst h; simp at he0
      rw [Nat.zero_pow (Nat.pos_of_ne_zero heNe), Nat.zero_mod]; rfl
    · simp only [↓reduceIte]
      rw [eq_of_beq he0, Nat.pow_zero]; rfl

private theorem pow_mod_congr_nat {x y m : Nat} (h : x % m = y % m) (k : Nat) :
    (x ^ k) % m = (y ^ k) % m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

private theorem pow4_mod_one {u p : Nat} (hp : 1 < p) (hu : u % p = 1) :
    (u ^ 4) % p = 1 := by
  have hu2 : (u * u) % p = 1 := by rw [Nat.mul_mod, hu, Nat.one_mul, Nat.mod_eq_of_lt hp]
  have h4 : u ^ 4 = (u * u) * (u * u) := by
    rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, show (2 : Nat) = 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  rw [h4, Nat.mul_mod, hu2, Nat.one_mul, Nat.mod_eq_of_lt hp]

private theorem pow_seven_dInv_mod (a : Goldilocks) :
    (a.val ^ (7 * poseidon2DInv)) % goldilocksPrime = a.val := by
  if ha0 : a.val = 0 then
    have hexp0 : 7 * poseidon2DInv = (4 * (goldilocksPrime - 1)) + 1 := rfl
    rw [ha0, hexp0, Nat.zero_pow (by omega), Nat.zero_mod]
  else
    have hndvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hlt := a.isLt; omega
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod hndvd
    have hexp : 7 * poseidon2DInv = (goldilocksPrime - 1) * 4 + 1 := rfl
    have hu4 : ((a.val ^ (goldilocksPrime - 1)) ^ 4) % goldilocksPrime = 1 :=
      pow4_mod_one (by decide +kernel) hflt
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.pow_one, Nat.mul_mod, hu4,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

theorem sbox7Inv_sbox7 (x : Goldilocks) : sbox7Inv (sbox7 x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7 x).val % goldilocksPrime = (x.val ^ 7) % goldilocksPrime := by
    rw [sbox7_val, Nat.mod_mod]
  unfold sbox7Inv
  rw [goldilocksPow_val, pow_mod_congr_nat hCongr poseidon2DInv, ← Nat.pow_mul, pow_seven_dInv_mod]

theorem sbox7_sbox7Inv (x : Goldilocks) : sbox7 (sbox7Inv x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7Inv x).val % goldilocksPrime = (x.val ^ poseidon2DInv) % goldilocksPrime := by
    unfold sbox7Inv
    rw [goldilocksPow_val, Nat.mod_mod]
  rw [sbox7_val, pow_mod_congr_nat hCongr 7, ← Nat.pow_mul, Nat.mul_comm poseidon2DInv 7, pow_seven_dInv_mod]

/-! ## 2. Kronecker-Swapped External Layer $M_E = M_4 \otimes P_6$ & Inverse `applyME24Inv` -/

private def inv3G : Goldilocks := ⟨12297829379609722881, by decide +kernel⟩
private def inv7G : Goldilocks := ⟨2635249152773512046, by decide +kernel⟩
private def inv15G : Goldilocks := ⟨17216961131453612033, by decide +kernel⟩
private def invPow2_23G : Goldilocks := ⟨18446741870391329281, by decide +kernel⟩
private def inv25165821G : Goldilocks := ⟨10127602075383216580, by decide +kernel⟩

private theorem ofNat_eq_goldOfInt (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

private theorem mul_cancel_of_prod_one {u k : Goldilocks} (h : Goldilocks.mul u k = Goldilocks.one)
    (x : Goldilocks) : Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]; exact LawfulCommRing.one_mul x

private theorem inv3G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv3G (Goldilocks.mul (Goldilocks.ofNat 3) x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem inv7G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv7G (Goldilocks.mul (Goldilocks.ofNat 7) x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem mul_inv7G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem inv15G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv15G (Goldilocks.mul (Goldilocks.ofNat 15) x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem invPow2_23G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat 8388608) x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem inv25165821G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv25165821G (Goldilocks.mul (Goldilocks.ofNat 25165821) x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

private theorem mul_inv25165821G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 25165821) (Goldilocks.mul inv25165821G x) = x :=
  mul_cancel_of_prod_one (by decide +kernel) x

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
  unfold applyM4 lane4Sum; dsimp only
  rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3,
      ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_add, goldOfInt_mul]; congr 1; omega

private theorem makeM4InvRaw_applyM4 (b : Lane4) :
    makeM4InvRaw (applyM4 b) (lane4Sum b) = lane4Scale (Goldilocks.ofNat 15) b := by
  unfold makeM4InvRaw applyM4 lane4Sum lane4Scale; dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4Inv_applyM4 (b : Lane4) : applyM4Inv (applyM4 b) = b := by
  unfold applyM4Inv
  rw [lane4Sum_applyM4, inv7G_mul_cancel, makeM4InvRaw_applyM4]
  unfold lane4Scale
  exact Lane4.ext (inv15G_mul_cancel _) (inv15G_mul_cancel _) (inv15G_mul_cancel _) (inv15G_mul_cancel _)

private theorem applyM4_scale (c : Goldilocks) (b : Lane4) :
    applyM4 (lane4Scale c b) = lane4Scale c (applyM4 b) := by
  have h2 : ∀ x : Int, (c.val : Int) * (((2 : Nat) : Int) * x) =
      ((2 : Nat) : Int) * ((c.val : Int) * x) := fun x => by
    rw [← Int.mul_assoc, Int.mul_comm (c.val : Int) ((2 : Nat) : Int), Int.mul_assoc]
  unfold applyM4 lane4Scale lane4Sum; dsimp only
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
  unfold applyM4 makeM4InvRaw lane4Sum; dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat y.x0, ← goldOfInt_nat y.x1, ← goldOfInt_nat y.x2,
         ← goldOfInt_nat y.x3, ← goldOfInt_nat s];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

private theorem zero_rem_add_eq (a u v : Goldilocks) (h : v = u) :
    Goldilocks.add a (Goldilocks.mul (Goldilocks.ofNat 5) (Goldilocks.sub u v)) = a := by
  rw [h, ← goldOfInt_nat a, ← goldOfInt_nat u]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

theorem applyM4_applyM4Inv (y : Lane4) : applyM4 (applyM4Inv y) = y := by
  unfold applyM4Inv
  generalize hsDef : Goldilocks.mul inv7G (lane4Sum y) = s
  have hs7 : Goldilocks.mul (Goldilocks.ofNat 7) s = lane4Sum y := by
    rw [← hsDef]; exact mul_inv7G_cancel (lane4Sum y)
  rw [applyM4_scale, applyM4_makeM4InvRaw]
  unfold lane4Scale; dsimp only
  rw [zero_rem_add_eq _ _ _ hs7, zero_rem_add_eq _ _ _ hs7,
      zero_rem_add_eq _ _ _ hs7, zero_rem_add_eq _ _ _ hs7]
  exact Lane4.ext (inv15G_mul_cancel _) (inv15G_mul_cancel _) (inv15G_mul_cancel _) (inv15G_mul_cancel _)

def sum6Lane4 (a0 a1 a2 a3 a4 a5 : Lane4) : Lane4 :=
  lane4Add (lane4Add (lane4Add a0 a1) (lane4Add a2 a3)) (lane4Add a4 a5)

/-- Unswapped block-circulant $P_6 \otimes M_4$ (`det(P_6) = 1 + 6 = 7`). -/
def applyME24Std (st : Poseidon2State24) : Poseidon2State24 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let y3 := applyM4 st.b3
  let y4 := applyM4 st.b4
  let y5 := applyM4 st.b5
  let s := sum6Lane4 y0 y1 y2 y3 y4 y5
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s,
   lane4Add y3 s, lane4Add y4 s, lane4Add y5 s⟩

def applyME24StdInv (st : Poseidon2State24) : Poseidon2State24 :=
  let sumAll := sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5
  let s := lane4Scale inv7G sumAll
  ⟨applyM4Inv (lane4Sub st.b0 s), applyM4Inv (lane4Sub st.b1 s), applyM4Inv (lane4Sub st.b2 s),
   applyM4Inv (lane4Sub st.b3 s), applyM4Inv (lane4Sub st.b4 s), applyM4Inv (lane4Sub st.b5 s)⟩

private theorem scalar_sum_seven_cancel (a0 a1 a2 a3 a4 a5 : Goldilocks) :
    let s := Goldilocks.add (Goldilocks.add (Goldilocks.add a0 a1) (Goldilocks.add a2 a3)) (Goldilocks.add a4 a5)
    Goldilocks.mul inv7G
      (Goldilocks.add
        (Goldilocks.add (Goldilocks.add (Goldilocks.add a0 s) (Goldilocks.add a1 s))
                        (Goldilocks.add (Goldilocks.add a2 s) (Goldilocks.add a3 s)))
        (Goldilocks.add (Goldilocks.add a4 s) (Goldilocks.add a5 s))) = s := by
  dsimp only
  have h :
      let s := Goldilocks.add (Goldilocks.add (Goldilocks.add a0 a1) (Goldilocks.add a2 a3)) (Goldilocks.add a4 a5)
      Goldilocks.add
        (Goldilocks.add (Goldilocks.add (Goldilocks.add a0 s) (Goldilocks.add a1 s))
                        (Goldilocks.add (Goldilocks.add a2 s) (Goldilocks.add a3 s)))
        (Goldilocks.add (Goldilocks.add a4 s) (Goldilocks.add a5 s)) =
      Goldilocks.mul (Goldilocks.ofNat 7) s := by
    dsimp only
    rw [← goldOfInt_nat a0, ← goldOfInt_nat a1, ← goldOfInt_nat a2,
        ← goldOfInt_nat a3, ← goldOfInt_nat a4, ← goldOfInt_nat a5]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  rw [h, inv7G_mul_cancel]

private theorem lane4Sub_add_right (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _;
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyME24StdInv_applyME24Std (st : Poseidon2State24) :
    applyME24StdInv (applyME24Std st) = st := by
  unfold applyME24StdInv applyME24Std sum6Lane4
  dsimp only
  have hS :
      let y0 := applyM4 st.b0; let y1 := applyM4 st.b1; let y2 := applyM4 st.b2
      let y3 := applyM4 st.b3; let y4 := applyM4 st.b4; let y5 := applyM4 st.b5
      let s := lane4Add (lane4Add (lane4Add y0 y1) (lane4Add y2 y3)) (lane4Add y4 y5)
      lane4Scale inv7G
        (lane4Add (lane4Add (lane4Add (lane4Add y0 s) (lane4Add y1 s))
                            (lane4Add (lane4Add y2 s) (lane4Add y3 s)))
                  (lane4Add (lane4Add y4 s) (lane4Add y5 s))) = s := by
    dsimp only; unfold lane4Scale lane4Add
    exact Lane4.ext
      (scalar_sum_seven_cancel _ _ _ _ _ _)
      (scalar_sum_seven_cancel _ _ _ _ _ _)
      (scalar_sum_seven_cancel _ _ _ _ _ _)
      (scalar_sum_seven_cancel _ _ _ _ _ _)
  rw [hS]
  simp only [lane4Sub_add_right, applyM4Inv_applyM4]

private theorem scalar_sub6_sum_id (a0 a1 a2 a3 a4 a5 s : Goldilocks) :
    Goldilocks.add
      (Goldilocks.add (Goldilocks.add (Goldilocks.sub a0 s) (Goldilocks.sub a1 s))
                      (Goldilocks.add (Goldilocks.sub a2 s) (Goldilocks.sub a3 s)))
      (Goldilocks.add (Goldilocks.sub a4 s) (Goldilocks.sub a5 s)) =
    Goldilocks.add s
      (Goldilocks.sub
        (Goldilocks.add (Goldilocks.add (Goldilocks.add a0 a1) (Goldilocks.add a2 a3)) (Goldilocks.add a4 a5))
        (Goldilocks.mul (Goldilocks.ofNat 7) s)) := by
  rw [← goldOfInt_nat a0, ← goldOfInt_nat a1, ← goldOfInt_nat a2,
      ← goldOfInt_nat a3, ← goldOfInt_nat a4, ← goldOfInt_nat a5, ← goldOfInt_nat s]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

private theorem add_sub_self_zero_eq (s u v : Goldilocks) (h : v = u) :
    Goldilocks.add s (Goldilocks.sub u v) = s := by
  rw [h, ← goldOfInt_nat s, ← goldOfInt_nat u]
  simp only [goldOfInt_add, goldOfInt_sub]
  congr 1; omega

private theorem lane4Add_sub_cancel (a b : Lane4) : lane4Add (lane4Sub a b) b = a := by
  unfold lane4Add lane4Sub
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat a.x0, ← goldOfInt_nat a.x1, ← goldOfInt_nat a.x2, ← goldOfInt_nat a.x3,
         ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega)

private theorem applyME24Std_sub_sum (st : Poseidon2State24) (s : Lane4)
    (hs0 : Goldilocks.mul (Goldilocks.ofNat 7) s.x0 = (sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5).x0)
    (hs1 : Goldilocks.mul (Goldilocks.ofNat 7) s.x1 = (sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5).x1)
    (hs2 : Goldilocks.mul (Goldilocks.ofNat 7) s.x2 = (sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5).x2)
    (hs3 : Goldilocks.mul (Goldilocks.ofNat 7) s.x3 = (sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5).x3) :
    applyME24Std ⟨applyM4Inv (lane4Sub st.b0 s), applyM4Inv (lane4Sub st.b1 s), applyM4Inv (lane4Sub st.b2 s),
                  applyM4Inv (lane4Sub st.b3 s), applyM4Inv (lane4Sub st.b4 s), applyM4Inv (lane4Sub st.b5 s)⟩ = st := by
  unfold applyME24Std
  dsimp only
  simp only [applyM4_applyM4Inv]
  have hSubSum : sum6Lane4 (lane4Sub st.b0 s) (lane4Sub st.b1 s) (lane4Sub st.b2 s)
      (lane4Sub st.b3 s) (lane4Sub st.b4 s) (lane4Sub st.b5 s) = s := by
    unfold sum6Lane4 lane4Add at hs0 hs1 hs2 hs3
    unfold sum6Lane4 lane4Add lane4Sub
    dsimp only at hs0 hs1 hs2 hs3 ⊢
    exact Lane4.ext
      ((scalar_sub6_sum_id _ _ _ _ _ _ _).trans (add_sub_self_zero_eq _ _ _ hs0))
      ((scalar_sub6_sum_id _ _ _ _ _ _ _).trans (add_sub_self_zero_eq _ _ _ hs1))
      ((scalar_sub6_sum_id _ _ _ _ _ _ _).trans (add_sub_self_zero_eq _ _ _ hs2))
      ((scalar_sub6_sum_id _ _ _ _ _ _ _).trans (add_sub_self_zero_eq _ _ _ hs3))
  rw [hSubSum]
  simp only [lane4Add_sub_cancel]

theorem applyME24Std_applyME24StdInv (st : Poseidon2State24) :
    applyME24Std (applyME24StdInv st) = st := by
  unfold applyME24StdInv
  dsimp only
  exact applyME24Std_sub_sum st (lane4Scale inv7G (sum6Lane4 st.b0 st.b1 st.b2 st.b3 st.b4 st.b5))
    (mul_inv7G_cancel _) (mul_inv7G_cancel _) (mul_inv7G_cancel _) (mul_inv7G_cancel _)

/-- $4 \times 6 \to 6 \times 4$ lane transposition matching `poseidon2_gl24_apply_me` (`u_c = [st[c], st[6+c], st[12+c], st[18+c]]`). -/
def poseidon2Transpose4x6 (s : Poseidon2State24) : Poseidon2State24 :=
  ⟨⟨s.b0.x0, s.b1.x2, s.b3.x0, s.b4.x2⟩,
   ⟨s.b0.x1, s.b1.x3, s.b3.x1, s.b4.x3⟩,
   ⟨s.b0.x2, s.b2.x0, s.b3.x2, s.b5.x0⟩,
   ⟨s.b0.x3, s.b2.x1, s.b3.x3, s.b5.x1⟩,
   ⟨s.b1.x0, s.b2.x2, s.b4.x0, s.b5.x2⟩,
   ⟨s.b1.x1, s.b2.x3, s.b4.x1, s.b5.x3⟩⟩

def poseidon2Transpose6x4 (t : Poseidon2State24) : Poseidon2State24 :=
  ⟨⟨t.b0.x0, t.b1.x0, t.b2.x0, t.b3.x0⟩,
   ⟨t.b4.x0, t.b5.x0, t.b0.x1, t.b1.x1⟩,
   ⟨t.b2.x1, t.b3.x1, t.b4.x1, t.b5.x1⟩,
   ⟨t.b0.x2, t.b1.x2, t.b2.x2, t.b3.x2⟩,
   ⟨t.b4.x2, t.b5.x2, t.b0.x3, t.b1.x3⟩,
   ⟨t.b2.x3, t.b3.x3, t.b4.x3, t.b5.x3⟩⟩

@[simp] theorem poseidon2Transpose64_46 (s : Poseidon2State24) :
    poseidon2Transpose6x4 (poseidon2Transpose4x6 s) = s := by
  cases s with | mk b0 b1 b2 b3 b4 b5 =>
    cases b0; cases b1; cases b2; cases b3; cases b4; cases b5; rfl

@[simp] theorem poseidon2Transpose46_64 (s : Poseidon2State24) :
    poseidon2Transpose4x6 (poseidon2Transpose6x4 s) = s := by
  cases s with | mk b0 b1 b2 b3 b4 b5 =>
    cases b0; cases b1; cases b2; cases b3; cases b4; cases b5; rfl

/-- Kronecker-swapped external layer $M_E = M_4 \otimes P_6$ (`0` field multiplications). -/
@[expose] def applyME24 (s : Poseidon2State24) : Poseidon2State24 :=
  poseidon2Transpose6x4 (applyME24Std (poseidon2Transpose4x6 s))

def applyME24Inv (s : Poseidon2State24) : Poseidon2State24 :=
  poseidon2Transpose6x4 (applyME24StdInv (poseidon2Transpose4x6 s))

theorem applyME24Inv_applyME24 (s : Poseidon2State24) : applyME24Inv (applyME24 s) = s := by
  simp only [applyME24Inv, applyME24, poseidon2Transpose46_64, applyME24StdInv_applyME24Std,
    poseidon2Transpose64_46]

theorem applyME24_applyME24Inv (s : Poseidon2State24) : applyME24 (applyME24Inv s) = s := by
  simp only [applyME24Inv, applyME24, poseidon2Transpose46_64, applyME24Std_applyME24StdInv,
    poseidon2Transpose64_46]

/-- **Merz–Rodríguez García (`ePrint 2026/306`) Subspace-Skip Kill (`poseidon2_gl24_kronecker_swap_kills_subspace_skip`)**:
    Under $M_E = M_4 \otimes P_6$, any opposite-sign rate difference `(X, -X, 0, 0, 0, 0)` maps
    injectively (`det = -3 ≢ 0 mod p`) into capacity block `b4` alone. -/
theorem poseidon2_gl24_kronecker_swap_kills_subspace_skip (X : Lane4) :
    (applyME24 ⟨X, lane4Neg X, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩).b4 = lane4Zero ↔
      X = lane4Zero := by
  constructor
  · intro hb4
    let y := (applyME24 ⟨X, lane4Neg X, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩).b4
    have hy0 : y.x0 = Goldilocks.zero := congrArg Lane4.x0 hb4
    have hy1 : y.x1 = Goldilocks.zero := congrArg Lane4.x1 hb4
    have hy2 : y.x2 = Goldilocks.zero := congrArg Lane4.x2 hb4
    have hy3 : y.x3 = Goldilocks.zero := congrArg Lane4.x3 hb4
    have hx0 : X.x0 = Goldilocks.sub Goldilocks.zero y.x0 := by
      unfold y applyME24 poseidon2Transpose6x4 poseidon2Transpose4x6 applyME24Std sum6Lane4
        applyM4 lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
      dsimp only
      rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
        goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
      congr 1; omega
    have hx1 : X.x1 = Goldilocks.sub Goldilocks.zero y.x1 := by
      unfold y applyME24 poseidon2Transpose6x4 poseidon2Transpose4x6 applyME24Std sum6Lane4
        applyM4 lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
      dsimp only
      rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
        goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
      congr 1; omega
    have hx2 : Goldilocks.mul (Goldilocks.ofNat 3) X.x2 =
        Goldilocks.add
          (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 6) y.x1) (Goldilocks.mul (Goldilocks.ofNat 3) y.x0))
          (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 2) y.x3) y.x2) := by
      unfold y applyME24 poseidon2Transpose6x4 poseidon2Transpose4x6 applyME24Std sum6Lane4
        applyM4 lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
      dsimp only
      rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
        goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
      congr 1; omega
    have hx3 : Goldilocks.mul (Goldilocks.ofNat 3) X.x3 =
        Goldilocks.add
          (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 6) y.x0) (Goldilocks.mul (Goldilocks.ofNat 3) y.x1))
          (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 2) y.x2) y.x3) := by
      unfold y applyME24 poseidon2Transpose6x4 poseidon2Transpose4x6 applyME24Std sum6Lane4
        applyM4 lane4Neg lane4Add lane4Sub lane4Sum lane4Zero
      dsimp only
      rw [← goldOfInt_nat X.x0, ← goldOfInt_nat X.x1, ← goldOfInt_nat X.x2, ← goldOfInt_nat X.x3]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
        goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
      congr 1; omega
    rw [hy0] at hx0
    rw [hy1] at hx1
    rw [hy0, hy1, hy2, hy3] at hx2 hx3
    have h2z := congrArg (Goldilocks.mul inv3G) hx2
    rw [inv3G_mul_cancel] at h2z
    have h3z := congrArg (Goldilocks.mul inv3G) hx3
    rw [inv3G_mul_cancel] at h3z
    exact Lane4.ext
      (hx0.trans (by decide +kernel))
      (hx1.trans (by decide +kernel))
      (h2z.trans (by decide +kernel))
      (h3z.trans (by decide +kernel))
  · intro hX; subst hX; decide +kernel

/-- `#tooth` **Block-circulant $P_6 \otimes M_4$ (`applyME24Std`) admits `(X, -X, 0, 0, 0, 0)` subspace skipping**:
    nonzero `X` leaves *both* capacity blocks `b4, b5` identically zero! -/
theorem tooth_poseidon2_gl24_me_std_admits_subspace_skip :
    ∃ X : Lane4, X ≠ lane4Zero ∧
      (applyME24Std ⟨X, lane4Neg X, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩).b4 = lane4Zero ∧
      (applyME24Std ⟨X, lane4Neg X, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩).b5 = lane4Zero :=
  ⟨⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 3. Shift-Only Internal Layer $M_I = J_{24} + \mathrm{diag}(-2^{23}, 1, 2, \dots, 2^{22})$, Inverse & Branch Number `25` -/

def state24Sum (st : Poseidon2State24) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1))
                    (Goldilocks.add (lane4Sum st.b2) (lane4Sum st.b3)))
    (Goldilocks.add (lane4Sum st.b4) (lane4Sum st.b5))

def applyMI24WithSum (st : Poseidon2State24) (s : Goldilocks) : Poseidon2State24 :=
  ⟨⟨Goldilocks.sub s (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b0.x0),
    Goldilocks.add s st.b0.x1,
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 2) st.b0.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 4) st.b0.x3)⟩,
   ⟨Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 8) st.b1.x0),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 16) st.b1.x1),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 32) st.b1.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 64) st.b1.x3)⟩,
   ⟨Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 128) st.b2.x0),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 256) st.b2.x1),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 512) st.b2.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 1024) st.b2.x3)⟩,
   ⟨Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 2048) st.b3.x0),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 4096) st.b3.x1),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 8192) st.b3.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 16384) st.b3.x3)⟩,
   ⟨Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 32768) st.b4.x0),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 65536) st.b4.x1),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 131072) st.b4.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 262144) st.b4.x3)⟩,
   ⟨Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 524288) st.b5.x0),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 1048576) st.b5.x1),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 2097152) st.b5.x2),
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat 4194304) st.b5.x3)⟩⟩

@[expose] def applyMI24 (st : Poseidon2State24) : Poseidon2State24 :=
  applyMI24WithSum st (state24Sum st)

private def weightedSumMI24 (y : Poseidon2State24) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 8388608) y.b0.x1) y.b0.x0)
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 4194304) y.b0.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 2097152) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 1048576) y.b1.x0)
                    (Goldilocks.mul (Goldilocks.ofNat 524288) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 262144) y.b1.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 131072) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 65536) y.b2.x0)
                    (Goldilocks.mul (Goldilocks.ofNat 32768) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 16384) y.b2.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 8192) y.b2.x3))
  let t3 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 4096) y.b3.x0)
                    (Goldilocks.mul (Goldilocks.ofNat 2048) y.b3.x1))
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 1024) y.b3.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 512) y.b3.x3))
  let t4 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 256) y.b4.x0)
                    (Goldilocks.mul (Goldilocks.ofNat 128) y.b4.x1))
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 64) y.b4.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 32) y.b4.x3))
  let t5 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 16) y.b5.x0)
                    (Goldilocks.mul (Goldilocks.ofNat 8) y.b5.x1))
    (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 4) y.b5.x2)
                    (Goldilocks.mul (Goldilocks.ofNat 2) y.b5.x3))
  Goldilocks.add (Goldilocks.add (Goldilocks.add t0 t1) (Goldilocks.add t2 t3)) (Goldilocks.add t4 t5)

private def makeMI24InvRaw (y : Poseidon2State24) (invP23 s : Goldilocks) : Poseidon2State24 :=
  let sc (w : Nat) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul invP23 (Goldilocks.mul (Goldilocks.ofNat w) (Goldilocks.sub yi s))
  ⟨⟨Goldilocks.mul invP23 (Goldilocks.sub s y.b0.x0),
    sc 8388608 y.b0.x1, sc 4194304 y.b0.x2, sc 2097152 y.b0.x3⟩,
   ⟨sc 1048576 y.b1.x0, sc 524288 y.b1.x1, sc 262144 y.b1.x2, sc 131072 y.b1.x3⟩,
   ⟨sc 65536 y.b2.x0, sc 32768 y.b2.x1, sc 16384 y.b2.x2, sc 8192 y.b2.x3⟩,
   ⟨sc 4096 y.b3.x0, sc 2048 y.b3.x1, sc 1024 y.b3.x2, sc 512 y.b3.x3⟩,
   ⟨sc 256 y.b4.x0, sc 128 y.b4.x1, sc 64 y.b4.x2, sc 32 y.b4.x3⟩,
   ⟨sc 16 y.b5.x0, sc 8 y.b5.x1, sc 4 y.b5.x2, sc 2 y.b5.x3⟩⟩

def applyMI24Inv (y : Poseidon2State24) : Poseidon2State24 :=
  makeMI24InvRaw y invPow2_23G (Goldilocks.mul inv25165821G (weightedSumMI24 y))

private def state24ValSumInt (st : Poseidon2State24) : Int :=
  ((st.b0.x0.val : Int) + st.b0.x1.val + st.b0.x2.val + st.b0.x3.val) +
  ((st.b1.x0.val : Int) + st.b1.x1.val + st.b1.x2.val + st.b1.x3.val) +
  ((st.b2.x0.val : Int) + st.b2.x1.val + st.b2.x2.val + st.b2.x3.val) +
  ((st.b3.x0.val : Int) + st.b3.x1.val + st.b3.x2.val + st.b3.x3.val) +
  ((st.b4.x0.val : Int) + st.b4.x1.val + st.b4.x2.val + st.b4.x3.val) +
  ((st.b5.x0.val : Int) + st.b5.x1.val + st.b5.x2.val + st.b5.x3.val)

private theorem state24Sum_eq_goldOfInt (st : Poseidon2State24) :
    state24Sum st = goldOfInt (state24ValSumInt st) := by
  unfold state24Sum lane4Sum
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3,
      ← goldOfInt_nat st.b3.x0, ← goldOfInt_nat st.b3.x1, ← goldOfInt_nat st.b3.x2, ← goldOfInt_nat st.b3.x3,
      ← goldOfInt_nat st.b4.x0, ← goldOfInt_nat st.b4.x1, ← goldOfInt_nat st.b4.x2, ← goldOfInt_nat st.b4.x3,
      ← goldOfInt_nat st.b5.x0, ← goldOfInt_nat st.b5.x1, ← goldOfInt_nat st.b5.x2, ← goldOfInt_nat st.b5.x3]
  simp only [goldOfInt_add]
  congr 1
  unfold state24ValSumInt
  omega

private theorem weightedSumMI24_applyMI24 (st : Poseidon2State24) :
    weightedSumMI24 (applyMI24 st) = Goldilocks.mul (Goldilocks.ofNat 25165821) (state24Sum st) := by
  unfold weightedSumMI24 applyMI24 applyMI24WithSum
  rw [state24Sum_eq_goldOfInt st]
  dsimp only
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3,
      ← goldOfInt_nat st.b3.x0, ← goldOfInt_nat st.b3.x1, ← goldOfInt_nat st.b3.x2, ← goldOfInt_nat st.b3.x3,
      ← goldOfInt_nat st.b4.x0, ← goldOfInt_nat st.b4.x1, ← goldOfInt_nat st.b4.x2, ← goldOfInt_nat st.b4.x3,
      ← goldOfInt_nat st.b5.x0, ← goldOfInt_nat st.b5.x1, ← goldOfInt_nat st.b5.x2, ← goldOfInt_nat st.b5.x3]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
  congr 1; unfold state24ValSumInt; omega

private theorem mi24_lane0_recover (x s : Goldilocks) :
    Goldilocks.mul invPow2_23G
      (Goldilocks.sub s (Goldilocks.sub s (Goldilocks.mul (Goldilocks.ofNat 8388608) x))) = x := by
  have hSub : Goldilocks.sub s (Goldilocks.sub s (Goldilocks.mul (Goldilocks.ofNat 8388608) x)) =
      Goldilocks.mul (Goldilocks.ofNat 8388608) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, goldOfInt_sub, goldOfInt_mul]
    congr 1; omega
  rw [hSub, invPow2_23G_mul_cancel]

private theorem mi24_lane1_recover (x s : Goldilocks) :
    Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat 8388608)
      (Goldilocks.sub (Goldilocks.add s x) s)) = x := by
  have hSub : Goldilocks.sub (Goldilocks.add s x) s = x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s]
    simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega
  rw [hSub, invPow2_23G_mul_cancel]

private theorem mi24_lane_pos_recover (v w : Nat) (hv : v * w = 8388608) (x s : Goldilocks) :
    Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat w)
      (Goldilocks.sub (Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v) x)) s)) = x := by
  have hProd : Goldilocks.mul (Goldilocks.ofNat w)
      (Goldilocks.sub (Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v) x)) s) =
      Goldilocks.mul (Goldilocks.ofNat 8388608) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hsCancel : (s.val : Int) + (v : Int) * (x.val : Int) - (s.val : Int) =
        (v : Int) * (x.val : Int) := by omega
    have hvw : ((v * w : Nat) : Int) = (w : Int) * (v : Int) := by
      rw [Int.natCast_mul, Int.mul_comm]
    rw [hsCancel, ← Int.mul_assoc, ← hvw, hv]
  rw [hProd, invPow2_23G_mul_cancel]

theorem applyMI24Inv_applyMI24 (st : Poseidon2State24) : applyMI24Inv (applyMI24 st) = st := by
  unfold applyMI24Inv
  rw [weightedSumMI24_applyMI24, inv25165821G_mul_cancel]
  unfold makeMI24InvRaw applyMI24 applyMI24WithSum
  dsimp only
  apply Poseidon2State24.ext
  · apply Lane4.ext
    · exact mi24_lane0_recover _ _
    · exact mi24_lane1_recover _ _
    · exact mi24_lane_pos_recover 2 4194304 rfl _ _
    · exact mi24_lane_pos_recover 4 2097152 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_recover 8 1048576 rfl _ _
    · exact mi24_lane_pos_recover 16 524288 rfl _ _
    · exact mi24_lane_pos_recover 32 262144 rfl _ _
    · exact mi24_lane_pos_recover 64 131072 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_recover 128 65536 rfl _ _
    · exact mi24_lane_pos_recover 256 32768 rfl _ _
    · exact mi24_lane_pos_recover 512 16384 rfl _ _
    · exact mi24_lane_pos_recover 1024 8192 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_recover 2048 4096 rfl _ _
    · exact mi24_lane_pos_recover 4096 2048 rfl _ _
    · exact mi24_lane_pos_recover 8192 1024 rfl _ _
    · exact mi24_lane_pos_recover 16384 512 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_recover 32768 256 rfl _ _
    · exact mi24_lane_pos_recover 65536 128 rfl _ _
    · exact mi24_lane_pos_recover 131072 64 rfl _ _
    · exact mi24_lane_pos_recover 262144 32 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_recover 524288 16 rfl _ _
    · exact mi24_lane_pos_recover 1048576 8 rfl _ _
    · exact mi24_lane_pos_recover 2097152 4 rfl _ _
    · exact mi24_lane_pos_recover 4194304 2 rfl _ _

private theorem state24Sum_makeMI24InvRaw (y : Poseidon2State24) (invP23 s : Goldilocks) :
    state24Sum (makeMI24InvRaw y invP23 s) =
      Goldilocks.mul invP23
        (Goldilocks.sub (weightedSumMI24 y) (Goldilocks.mul (Goldilocks.ofNat 16777213) s)) := by
  unfold state24Sum makeMI24InvRaw lane4Sum weightedSumMI24
  dsimp only
  rw [← goldOfInt_nat invP23, ← goldOfInt_nat s,
      ← goldOfInt_nat y.b0.x0, ← goldOfInt_nat y.b0.x1, ← goldOfInt_nat y.b0.x2, ← goldOfInt_nat y.b0.x3,
      ← goldOfInt_nat y.b1.x0, ← goldOfInt_nat y.b1.x1, ← goldOfInt_nat y.b1.x2, ← goldOfInt_nat y.b1.x3,
      ← goldOfInt_nat y.b2.x0, ← goldOfInt_nat y.b2.x1, ← goldOfInt_nat y.b2.x2, ← goldOfInt_nat y.b2.x3,
      ← goldOfInt_nat y.b3.x0, ← goldOfInt_nat y.b3.x1, ← goldOfInt_nat y.b3.x2, ← goldOfInt_nat y.b3.x3,
      ← goldOfInt_nat y.b4.x0, ← goldOfInt_nat y.b4.x1, ← goldOfInt_nat y.b4.x2, ← goldOfInt_nat y.b4.x3,
      ← goldOfInt_nat y.b5.x0, ← goldOfInt_nat y.b5.x1, ← goldOfInt_nat y.b5.x2, ← goldOfInt_nat y.b5.x3]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
  congr 1; congr 1; omega

private theorem mi24_lane0_forward (yi s : Goldilocks) :
    Goldilocks.sub s (Goldilocks.mul (Goldilocks.ofNat 8388608)
      (Goldilocks.mul invPow2_23G (Goldilocks.sub s yi))) = yi := by
  have hAssoc : Goldilocks.mul (Goldilocks.ofNat 8388608)
      (Goldilocks.mul invPow2_23G (Goldilocks.sub s yi)) =
      Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat 8388608) (Goldilocks.sub s yi)) := by
    change CommRingOps.mul _ (CommRingOps.mul _ _) = CommRingOps.mul _ (CommRingOps.mul _ _)
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (Goldilocks.ofNat 8388608) invPow2_23G,
        LawfulCommRing.mul_assoc]
  rw [hAssoc, invPow2_23G_mul_cancel]
  rw [← goldOfInt_nat s, ← goldOfInt_nat yi]
  simp only [goldOfInt_sub]; congr 1; omega

private theorem mi24_lane1_forward (yi s : Goldilocks) :
    Goldilocks.add s (Goldilocks.mul invPow2_23G
      (Goldilocks.mul (Goldilocks.ofNat 8388608) (Goldilocks.sub yi s))) = yi := by
  rw [invPow2_23G_mul_cancel, ← goldOfInt_nat s, ← goldOfInt_nat yi]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

private theorem mi24_lane_pos_forward (v w : Nat) (hv : v * w = 8388608) (yi s : Goldilocks) :
    Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v)
      (Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat w) (Goldilocks.sub yi s)))) = yi := by
  have hAssoc : Goldilocks.mul (Goldilocks.ofNat v)
      (Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat w) (Goldilocks.sub yi s))) =
      Goldilocks.mul invPow2_23G (Goldilocks.mul (Goldilocks.ofNat 8388608) (Goldilocks.sub yi s)) := by
    rw [← goldOfInt_nat invPow2_23G, ← goldOfInt_nat yi, ← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hvw : ((v * w : Nat) : Int) = (v : Int) * (w : Int) := Int.natCast_mul v w
    rw [← hv, hvw]; ac_rfl
  rw [hAssoc, invPow2_23G_mul_cancel]
  rw [← goldOfInt_nat s, ← goldOfInt_nat yi]
  simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega

theorem applyMI24_applyMI24Inv (y : Poseidon2State24) : applyMI24 (applyMI24Inv y) = y := by
  let s := Goldilocks.mul inv25165821G (weightedSumMI24 y)
  have hSum : state24Sum (makeMI24InvRaw y invPow2_23G s) = s := by
    rw [state24Sum_makeMI24InvRaw]
    have hs : weightedSumMI24 y = Goldilocks.mul (Goldilocks.ofNat 25165821) s :=
      (mul_inv25165821G_cancel (weightedSumMI24 y)).symm
    have hDiff : Goldilocks.sub (weightedSumMI24 y) (Goldilocks.mul (Goldilocks.ofNat 16777213) s) =
        Goldilocks.mul (Goldilocks.ofNat 8388608) s := by
      rw [hs, ← goldOfInt_nat s]
      simp only [ofNat_eq_goldOfInt, goldOfInt_sub, goldOfInt_mul]; congr 1; omega
    rw [hDiff, invPow2_23G_mul_cancel]
  change applyMI24 (makeMI24InvRaw y invPow2_23G s) = y
  unfold applyMI24
  rw [hSum]
  unfold applyMI24WithSum makeMI24InvRaw; dsimp only
  apply Poseidon2State24.ext
  · apply Lane4.ext
    · exact mi24_lane0_forward _ _
    · exact mi24_lane1_forward _ _
    · exact mi24_lane_pos_forward 2 4194304 rfl _ _
    · exact mi24_lane_pos_forward 4 2097152 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_forward 8 1048576 rfl _ _
    · exact mi24_lane_pos_forward 16 524288 rfl _ _
    · exact mi24_lane_pos_forward 32 262144 rfl _ _
    · exact mi24_lane_pos_forward 64 131072 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_forward 128 65536 rfl _ _
    · exact mi24_lane_pos_forward 256 32768 rfl _ _
    · exact mi24_lane_pos_forward 512 16384 rfl _ _
    · exact mi24_lane_pos_forward 1024 8192 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_forward 2048 4096 rfl _ _
    · exact mi24_lane_pos_forward 4096 2048 rfl _ _
    · exact mi24_lane_pos_forward 8192 1024 rfl _ _
    · exact mi24_lane_pos_forward 16384 512 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_forward 32768 256 rfl _ _
    · exact mi24_lane_pos_forward 65536 128 rfl _ _
    · exact mi24_lane_pos_forward 131072 64 rfl _ _
    · exact mi24_lane_pos_forward 262144 32 rfl _ _
  · apply Lane4.ext
    · exact mi24_lane_pos_forward 524288 16 rfl _ _
    · exact mi24_lane_pos_forward 1048576 8 rfl _ _
    · exact mi24_lane_pos_forward 2097152 4 rfl _ _
    · exact mi24_lane_pos_forward 4194304 2 rfl _ _

/-- Hamming weight (`0..24`) of a `Poseidon2State24`. -/
def nzBit (x : Goldilocks) : Nat :=
  match decEq x Goldilocks.zero with
  | isTrue _ => 0
  | isFalse _ => 1

def laneWeight4 (b : Lane4) : Nat := nzBit b.x0 + nzBit b.x1 + nzBit b.x2 + nzBit b.x3

def stateWeight24 (s : Poseidon2State24) : Nat :=
  laneWeight4 s.b0 + laneWeight4 s.b1 + laneWeight4 s.b2 +
  laneWeight4 s.b3 + laneWeight4 s.b4 + laneWeight4 s.b5

private theorem sub_zero_symm {a b : Goldilocks} (h : Goldilocks.sub a b = Goldilocks.zero) :
    Goldilocks.sub b a = Goldilocks.zero := by
  have hNeg : Goldilocks.sub b a = Goldilocks.sub Goldilocks.zero (Goldilocks.sub a b) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b]
    simp only [show Goldilocks.zero = goldOfInt 0 from rfl, goldOfInt_sub]
    congr 1; omega
  rw [hNeg, h]; decide +kernel

private theorem nzBit_zero : nzBit Goldilocks.zero = 0 := rfl

private theorem nzBit_of_ne {z : Goldilocks} (hz : z ≠ Goldilocks.zero) : nzBit z = 1 := by
  unfold nzBit
  cases decEq z Goldilocks.zero with
  | isFalse _ => rfl
  | isTrue h => exact False.elim (hz h)

private theorem nz_pair_lane0 (x s y : Goldilocks)
    (hy : y = Goldilocks.sub s (Goldilocks.mul (Goldilocks.ofNat 8388608) x))
    (hs : s ≠ Goldilocks.zero) :
    1 ≤ nzBit x + nzBit y ∧
    (nzBit x + nzBit y = 1 →
      Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 8388608) x)
        (Goldilocks.mul (Goldilocks.ofNat (nzBit x)) s) = Goldilocks.zero) := by
  cases decEq x Goldilocks.zero with
  | isTrue hx =>
    have hyS : y = s := by
      rw [hy, hx, ← goldOfInt_nat s]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
                 goldOfInt_sub, goldOfInt_mul]
      congr 1
    rw [hx, hyS, nzBit_zero, nzBit_of_ne hs]
    refine ⟨by omega, fun _ => ?_⟩
    rw [← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
               goldOfInt_sub, goldOfInt_mul]
    congr 1; omega
  | isFalse hx =>
    rw [nzBit_of_ne hx]
    cases decEq y Goldilocks.zero with
    | isTrue hy0 =>
      rw [hy0, nzBit_zero]
      refine ⟨by omega, fun _ => ?_⟩
      have h1 : Goldilocks.mul (Goldilocks.ofNat 1) s = s := LawfulCommRing.one_mul s
      rw [h1]
      exact sub_zero_symm (hy.symm.trans hy0)
    | isFalse hy0 =>
      rw [nzBit_of_ne hy0]; refine ⟨by omega, fun hEq => by omega⟩

private theorem nz_pair_lane1 (x s y : Goldilocks)
    (hy : y = Goldilocks.add s x)
    (hs : s ≠ Goldilocks.zero) :
    1 ≤ nzBit x + nzBit y ∧
    (nzBit x + nzBit y = 1 →
      Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) x)
        (Goldilocks.mul (Goldilocks.ofNat (nzBit x * 8388608)) s) = Goldilocks.zero) := by
  cases decEq x Goldilocks.zero with
  | isTrue hx =>
    have hyS : y = s := by
      rw [hy, hx, ← goldOfInt_nat s]
      simp only [show Goldilocks.zero = goldOfInt 0 from rfl, goldOfInt_add]
      congr 1
    rw [hx, hyS, nzBit_zero, nzBit_of_ne hs, Nat.zero_mul]
    refine ⟨by omega, fun _ => ?_⟩
    rw [← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
               goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  | isFalse hx =>
    rw [nzBit_of_ne hx, Nat.one_mul]
    cases decEq y Goldilocks.zero with
    | isTrue hy0 =>
      rw [hy0, nzBit_zero]
      refine ⟨by omega, fun _ => ?_⟩
      have hMul : Goldilocks.mul (Goldilocks.ofNat 8388608) (Goldilocks.add s x) = Goldilocks.zero :=
        (congrArg (Goldilocks.mul (Goldilocks.ofNat 8388608)) (hy.symm.trans hy0)).trans
          (by decide +kernel)
      have hExpand : Goldilocks.mul (Goldilocks.ofNat 8388608) (Goldilocks.add s x) =
          Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) x)
            (Goldilocks.mul (Goldilocks.ofNat 8388608) s) :=
        (LawfulCommRing.left_distrib (Goldilocks.ofNat 8388608) s x).trans
          (LawfulCommRing.add_comm _ _)
      exact hExpand.symm.trans hMul
    | isFalse hy0 =>
      rw [nzBit_of_ne hy0]; refine ⟨by omega, fun hEq => by omega⟩

private theorem nz_pair_lane_pos (v w : Nat) (hv : v * w = 8388608) (x s y : Goldilocks)
    (hy : y = Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v) x))
    (hs : s ≠ Goldilocks.zero) :
    1 ≤ nzBit x + nzBit y ∧
    (nzBit x + nzBit y = 1 →
      Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) x)
        (Goldilocks.mul (Goldilocks.ofNat (nzBit x * w)) s) = Goldilocks.zero) := by
  cases decEq x Goldilocks.zero with
  | isTrue hx =>
    have hyS : y = s := by
      rw [hy, hx, ← goldOfInt_nat s]
      simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
                 goldOfInt_add, goldOfInt_mul]
      congr 1
    rw [hx, hyS, nzBit_zero, nzBit_of_ne hs, Nat.zero_mul]
    refine ⟨by omega, fun _ => ?_⟩
    rw [← goldOfInt_nat s]
    simp only [ofNat_eq_goldOfInt, show Goldilocks.zero = goldOfInt 0 from rfl,
               goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  | isFalse hx =>
    rw [nzBit_of_ne hx, Nat.one_mul]
    cases decEq y Goldilocks.zero with
    | isTrue hy0 =>
      rw [hy0, nzBit_zero]
      refine ⟨by omega, fun _ => ?_⟩
      have hMul : Goldilocks.mul (Goldilocks.ofNat w)
          (Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v) x)) = Goldilocks.zero :=
        (congrArg (Goldilocks.mul (Goldilocks.ofNat w)) (hy.symm.trans hy0)).trans
          (LawfulCommRing.mul_zero _)
      have hExpand : Goldilocks.mul (Goldilocks.ofNat w)
          (Goldilocks.add s (Goldilocks.mul (Goldilocks.ofNat v) x)) =
          Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) x)
            (Goldilocks.mul (Goldilocks.ofNat w) s) := by
        rw [← goldOfInt_nat x, ← goldOfInt_nat s]
        simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
        congr 1
        have hvw : ((v * w : Nat) : Int) = (w : Int) * (v : Int) := by
          rw [Int.natCast_mul, Int.mul_comm]
        rw [Int.mul_add, ← Int.mul_assoc, ← hvw, hv, Int.add_comm]
      exact hExpand.symm.trans hMul
    | isFalse hy0 =>
      rw [nzBit_of_ne hy0]; refine ⟨by omega, fun hEq => by omega⟩

private theorem nzBit_le_one (x : Goldilocks) : nzBit x ≤ 1 := by
  cases decEq x Goldilocks.zero with
  | isTrue h => rw [h, nzBit_zero]; omega
  | isFalse h => rw [nzBit_of_ne h]; omega

private theorem gold_add_eq_zero {a b : Goldilocks}
    (ha : a = Goldilocks.zero) (hb : b = Goldilocks.zero) :
    Goldilocks.add a b = Goldilocks.zero :=
  (congrArg (fun x => Goldilocks.add x b) ha).trans
    ((congrArg (Goldilocks.add Goldilocks.zero) hb).trans (by decide +kernel))

private theorem ofNat_add_mul_s (a b : Nat) (s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat a) s)
      (Goldilocks.mul (Goldilocks.ofNat b) s) =
    Goldilocks.mul (Goldilocks.ofNat (a + b)) s := by
  rw [← goldOfInt_nat s]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul, Int.natCast_add, Int.add_mul]

private theorem ofNat_sub_mul_s {a b : Nat} (hle : b ≤ a) (s : Goldilocks) :
    Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat a) s)
      (Goldilocks.mul (Goldilocks.ofNat b) s) =
    Goldilocks.mul (Goldilocks.ofNat (a - b)) s := by
  rw [← goldOfInt_nat s]
  simp only [ofNat_eq_goldOfInt, goldOfInt_sub, goldOfInt_mul, Int.natCast_sub hle, Int.sub_mul]

private theorem combine_pos_eq {a1 a2 s : Goldilocks} {c1 c2 : Nat}
    (h1 : Goldilocks.add a1 (Goldilocks.mul (Goldilocks.ofNat c1) s) = Goldilocks.zero)
    (h2 : Goldilocks.add a2 (Goldilocks.mul (Goldilocks.ofNat c2) s) = Goldilocks.zero) :
    Goldilocks.add (Goldilocks.add a1 a2) (Goldilocks.mul (Goldilocks.ofNat (c1 + c2)) s) =
      Goldilocks.zero := by
  have hSum : Goldilocks.add (Goldilocks.add a1 a2) (Goldilocks.mul (Goldilocks.ofNat (c1 + c2)) s) =
      Goldilocks.add (Goldilocks.add a1 (Goldilocks.mul (Goldilocks.ofNat c1) s))
        (Goldilocks.add a2 (Goldilocks.mul (Goldilocks.ofNat c2) s)) := by
    rw [← ofNat_add_mul_s c1 c2 s]
    have u1Eq := goldOfInt_nat (Goldilocks.mul (Goldilocks.ofNat c1) s)
    have u2Eq := goldOfInt_nat (Goldilocks.mul (Goldilocks.ofNat c2) s)
    rw [← goldOfInt_nat a1, ← goldOfInt_nat a2, ← u1Eq, ← u2Eq]
    simp only [goldOfInt_add]; congr 1; omega
  exact hSum.trans (gold_add_eq_zero h1 h2)

private theorem combine_lane0_with_pos {a0 aPos s : Goldilocks} {b0 cPos : Nat}
    (hb0 : b0 ≤ 8388608 + cPos)
    (hAll : Goldilocks.add a0 aPos = Goldilocks.mul (Goldilocks.ofNat 8388608) s)
    (h0 : Goldilocks.sub a0 (Goldilocks.mul (Goldilocks.ofNat b0) s) = Goldilocks.zero)
    (hPos : Goldilocks.add aPos (Goldilocks.mul (Goldilocks.ofNat cPos) s) = Goldilocks.zero) :
    Goldilocks.mul (Goldilocks.ofNat (8388608 + cPos - b0)) s = Goldilocks.zero := by
  have hStep1 : Goldilocks.mul (Goldilocks.ofNat (8388608 + cPos - b0)) s =
      Goldilocks.sub
        (Goldilocks.add (Goldilocks.add a0 aPos) (Goldilocks.mul (Goldilocks.ofNat cPos) s))
        (Goldilocks.mul (Goldilocks.ofNat b0) s) := by
    rw [← ofNat_sub_mul_s hb0 s, ← ofNat_add_mul_s 8388608 cPos s, ← hAll]
  have hStep2 :
      Goldilocks.sub
        (Goldilocks.add (Goldilocks.add a0 aPos) (Goldilocks.mul (Goldilocks.ofNat cPos) s))
        (Goldilocks.mul (Goldilocks.ofNat b0) s) =
      Goldilocks.add (Goldilocks.sub a0 (Goldilocks.mul (Goldilocks.ofNat b0) s))
        (Goldilocks.add aPos (Goldilocks.mul (Goldilocks.ofNat cPos) s)) := by
    have u0Eq := goldOfInt_nat (Goldilocks.mul (Goldilocks.ofNat b0) s)
    have uPosEq := goldOfInt_nat (Goldilocks.mul (Goldilocks.ofNat cPos) s)
    rw [← goldOfInt_nat a0, ← goldOfInt_nat aPos, ← u0Eq, ← uPosEq]
    simp only [goldOfInt_add, goldOfInt_sub]; congr 1; omega
  exact hStep1.trans (hStep2.trans (gold_add_eq_zero h0 hPos))

private theorem scale_state24_tail_sum (st : Poseidon2State24) :
    Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b0.x0)
      (Goldilocks.add
        (Goldilocks.add
          (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b0.x1)
            (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b0.x2)
                            (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b0.x3)))
          (Goldilocks.add
            (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b1.x0)
                            (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b1.x1))
            (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b1.x2)
                            (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b1.x3))))
        (Goldilocks.add
          (Goldilocks.add
            (Goldilocks.add
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b2.x0)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b2.x1))
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b2.x2)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b2.x3)))
            (Goldilocks.add
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b3.x0)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b3.x1))
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b3.x2)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b3.x3))))
          (Goldilocks.add
            (Goldilocks.add
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b4.x0)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b4.x1))
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b4.x2)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b4.x3)))
            (Goldilocks.add
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b5.x0)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b5.x1))
              (Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b5.x2)
                              (Goldilocks.mul (Goldilocks.ofNat 8388608) st.b5.x3)))))) =
      Goldilocks.mul (Goldilocks.ofNat 8388608) (state24Sum st) := by
  have hAdd : ∀ a b : Goldilocks, Goldilocks.add a b = CommRingOps.add a b := fun _ _ => rfl
  have hMul : ∀ a b : Goldilocks, Goldilocks.mul a b = CommRingOps.mul a b := fun _ _ => rfl
  simp only [state24Sum, lane4Sum, hAdd, hMul, LawfulCommRing.left_distrib, LawfulCommRing.add_assoc]

private def lanePairSum4 (x y : Lane4) : Nat :=
  (nzBit x.x0 + nzBit y.x0) + (nzBit x.x1 + nzBit y.x1) +
  (nzBit x.x2 + nzBit y.x2) + (nzBit x.x3 + nzBit y.x3)

private theorem stateWeight24_pair_eq (x y : Poseidon2State24) :
    stateWeight24 x + stateWeight24 y =
      lanePairSum4 x.b0 y.b0 + lanePairSum4 x.b1 y.b1 + lanePairSum4 x.b2 y.b2 +
      lanePairSum4 x.b3 y.b3 + lanePairSum4 x.b4 y.b4 + lanePairSum4 x.b5 y.b5 := by
  have h4 : ∀ a b : Lane4, laneWeight4 a + laneWeight4 b = lanePairSum4 a b := fun a b => by
    unfold laneWeight4 lanePairSum4; omega
  have h6 : ∀ a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Nat,
      (a0 + a1 + a2 + a3 + a4 + a5) + (b0 + b1 + b2 + b3 + b4 + b5) =
      (a0 + b0) + (a1 + b1) + (a2 + b2) + (a3 + b3) + (a4 + b4) + (a5 + b5) := by omega
  unfold stateWeight24
  rw [h6, h4, h4, h4, h4, h4, h4]

private theorem four_ge_one_info {u0 u1 u2 u3 : Nat}
    (h0 : 1 ≤ u0) (h1 : 1 ≤ u1) (h2 : 1 ≤ u2) (h3 : 1 ≤ u3) :
    4 ≤ u0 + u1 + u2 + u3 ∧
    (u0 + u1 + u2 + u3 ≤ 4 → u0 = 1 ∧ u1 = 1 ∧ u2 = 1 ∧ u3 = 1) :=
  ⟨by omega, fun _ => ⟨by omega, by omega, by omega, by omega⟩⟩

private theorem six_ge_four_le_four {s0 s1 s2 s3 s4 s5 : Nat}
    (h0 : 4 ≤ s0) (h1 : 4 ≤ s1) (h2 : 4 ≤ s2) (h3 : 4 ≤ s3) (h4 : 4 ≤ s4) (h5 : 4 ≤ s5)
    (hSum : s0 + s1 + s2 + s3 + s4 + s5 ≤ 24) :
    s0 ≤ 4 ∧ s1 ≤ 4 ∧ s2 ≤ 4 ∧ s3 ≤ 4 ∧ s4 ≤ 4 ∧ s5 ≤ 4 :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem ofNat_ne_zero_of_bounds {W : Nat} (h1 : 1 ≤ W) (h2 : W < goldilocksPrime) :
    Goldilocks.ofNat W ≠ Goldilocks.zero := fun hZ => by
  have hv : W % goldilocksPrime = 0 := congrArg Goldilocks.val hZ
  rw [Nat.mod_eq_of_lt h2] at hv
  rw [hv] at h1
  cases h1

private theorem branch25_w_bounds
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 : Nat)
    (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1)
    (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1) (h7 : b7 ≤ 1)
    (h8 : b8 ≤ 1) (h9 : b9 ≤ 1) (h10 : b10 ≤ 1) (h11 : b11 ≤ 1)
    (h12 : b12 ≤ 1) (h13 : b13 ≤ 1) (h14 : b14 ≤ 1) (h15 : b15 ≤ 1)
    (h16 : b16 ≤ 1) (h17 : b17 ≤ 1) (h18 : b18 ≤ 1) (h19 : b19 ≤ 1)
    (h20 : b20 ≤ 1) (h21 : b21 ≤ 1) (h22 : b22 ≤ 1) (h23 : b23 ≤ 1) :
    let cPos :=
      (b1 * 8388608 + (b2 * 4194304 + b3 * 2097152)) +
      ((b4 * 1048576 + b5 * 524288) + (b6 * 262144 + b7 * 131072)) +
      (((b8 * 65536 + b9 * 32768) + (b10 * 16384 + b11 * 8192)) +
       ((b12 * 4096 + b13 * 2048) + (b14 * 1024 + b15 * 512)) +
       (((b16 * 256 + b17 * 128) + (b18 * 64 + b19 * 32)) +
        ((b20 * 16 + b21 * 8) + (b22 * 4 + b23 * 2))))
    b0 ≤ 8388608 + cPos ∧ 1 ≤ 8388608 + cPos - b0 ∧ 8388608 + cPos - b0 < goldilocksPrime := by
  dsimp only
  simp only [goldilocksPrime]
  exact ⟨by omega, by omega, by omega⟩

private theorem branch25_aux (st ySt : Poseidon2State24) (s : Goldilocks)
    (hsEq : s = state24Sum st) (hyEq : ySt = applyMI24WithSum st s)
    (hs : s ≠ Goldilocks.zero) :
    25 ≤ stateWeight24 st + stateWeight24 ySt := by
  match Nat.lt_or_ge (stateWeight24 st + stateWeight24 ySt) 25 with
  | .inr hGe => exact hGe
  | .inl hLt =>
  exfalso
  have hLe24 : stateWeight24 st + stateWeight24 ySt ≤ 24 := Nat.le_of_lt_succ hLt
  rw [stateWeight24_pair_eq] at hLe24
  have p0 := nz_pair_lane0 st.b0.x0 s ySt.b0.x0 (congrArg (fun u => u.b0.x0) hyEq) hs
  have p1 := nz_pair_lane1 st.b0.x1 s ySt.b0.x1 (congrArg (fun u => u.b0.x1) hyEq) hs
  have p2 := nz_pair_lane_pos 2 4194304 rfl st.b0.x2 s ySt.b0.x2 (congrArg (fun u => u.b0.x2) hyEq) hs
  have p3 := nz_pair_lane_pos 4 2097152 rfl st.b0.x3 s ySt.b0.x3 (congrArg (fun u => u.b0.x3) hyEq) hs
  have p4 := nz_pair_lane_pos 8 1048576 rfl st.b1.x0 s ySt.b1.x0 (congrArg (fun u => u.b1.x0) hyEq) hs
  have p5 := nz_pair_lane_pos 16 524288 rfl st.b1.x1 s ySt.b1.x1 (congrArg (fun u => u.b1.x1) hyEq) hs
  have p6 := nz_pair_lane_pos 32 262144 rfl st.b1.x2 s ySt.b1.x2 (congrArg (fun u => u.b1.x2) hyEq) hs
  have p7 := nz_pair_lane_pos 64 131072 rfl st.b1.x3 s ySt.b1.x3 (congrArg (fun u => u.b1.x3) hyEq) hs
  have p8 := nz_pair_lane_pos 128 65536 rfl st.b2.x0 s ySt.b2.x0 (congrArg (fun u => u.b2.x0) hyEq) hs
  have p9 := nz_pair_lane_pos 256 32768 rfl st.b2.x1 s ySt.b2.x1 (congrArg (fun u => u.b2.x1) hyEq) hs
  have p10 := nz_pair_lane_pos 512 16384 rfl st.b2.x2 s ySt.b2.x2 (congrArg (fun u => u.b2.x2) hyEq) hs
  have p11 := nz_pair_lane_pos 1024 8192 rfl st.b2.x3 s ySt.b2.x3 (congrArg (fun u => u.b2.x3) hyEq) hs
  have p12 := nz_pair_lane_pos 2048 4096 rfl st.b3.x0 s ySt.b3.x0 (congrArg (fun u => u.b3.x0) hyEq) hs
  have p13 := nz_pair_lane_pos 4096 2048 rfl st.b3.x1 s ySt.b3.x1 (congrArg (fun u => u.b3.x1) hyEq) hs
  have p14 := nz_pair_lane_pos 8192 1024 rfl st.b3.x2 s ySt.b3.x2 (congrArg (fun u => u.b3.x2) hyEq) hs
  have p15 := nz_pair_lane_pos 16384 512 rfl st.b3.x3 s ySt.b3.x3 (congrArg (fun u => u.b3.x3) hyEq) hs
  have p16 := nz_pair_lane_pos 32768 256 rfl st.b4.x0 s ySt.b4.x0 (congrArg (fun u => u.b4.x0) hyEq) hs
  have p17 := nz_pair_lane_pos 65536 128 rfl st.b4.x1 s ySt.b4.x1 (congrArg (fun u => u.b4.x1) hyEq) hs
  have p18 := nz_pair_lane_pos 131072 64 rfl st.b4.x2 s ySt.b4.x2 (congrArg (fun u => u.b4.x2) hyEq) hs
  have p19 := nz_pair_lane_pos 262144 32 rfl st.b4.x3 s ySt.b4.x3 (congrArg (fun u => u.b4.x3) hyEq) hs
  have p20 := nz_pair_lane_pos 524288 16 rfl st.b5.x0 s ySt.b5.x0 (congrArg (fun u => u.b5.x0) hyEq) hs
  have p21 := nz_pair_lane_pos 1048576 8 rfl st.b5.x1 s ySt.b5.x1 (congrArg (fun u => u.b5.x1) hyEq) hs
  have p22 := nz_pair_lane_pos 2097152 4 rfl st.b5.x2 s ySt.b5.x2 (congrArg (fun u => u.b5.x2) hyEq) hs
  have p23 := nz_pair_lane_pos 4194304 2 rfl st.b5.x3 s ySt.b5.x3 (congrArg (fun u => u.b5.x3) hyEq) hs
  have g0 := four_ge_one_info p0.1 p1.1 p2.1 p3.1
  have g1 := four_ge_one_info p4.1 p5.1 p6.1 p7.1
  have g2 := four_ge_one_info p8.1 p9.1 p10.1 p11.1
  have g3 := four_ge_one_info p12.1 p13.1 p14.1 p15.1
  have g4 := four_ge_one_info p16.1 p17.1 p18.1 p19.1
  have g5 := four_ge_one_info p20.1 p21.1 p22.1 p23.1
  have ⟨ub0, ub1, ub2, ub3, ub4, ub5⟩ :=
    six_ge_four_le_four g0.1 g1.1 g2.1 g3.1 g4.1 g5.1 hLe24
  have ⟨u0, u1, u2, u3⟩ := g0.2 ub0
  have ⟨u4, u5, u6, u7⟩ := g1.2 ub1
  have ⟨u8, u9, u10, u11⟩ := g2.2 ub2
  have ⟨u12, u13, u14, u15⟩ := g3.2 ub3
  have ⟨u16, u17, u18, u19⟩ := g4.2 ub4
  have ⟨u20, u21, u22, u23⟩ := g5.2 ub5
  have e0 := p0.2 u0; have e1 := p1.2 u1; have e2 := p2.2 u2; have e3 := p3.2 u3
  have e4 := p4.2 u4; have e5 := p5.2 u5; have e6 := p6.2 u6; have e7 := p7.2 u7
  have e8 := p8.2 u8; have e9 := p9.2 u9; have e10 := p10.2 u10; have e11 := p11.2 u11
  have e12 := p12.2 u12; have e13 := p13.2 u13; have e14 := p14.2 u14; have e15 := p15.2 u15
  have e16 := p16.2 u16; have e17 := p17.2 u17; have e18 := p18.2 u18; have e19 := p19.2 u19
  have e20 := p20.2 u20; have e21 := p21.2 u21; have e22 := p22.2 u22; have e23 := p23.2 u23
  have hPos01 := combine_pos_eq (combine_pos_eq e1 (combine_pos_eq e2 e3))
    (combine_pos_eq (combine_pos_eq e4 e5) (combine_pos_eq e6 e7))
  have hPos23 := combine_pos_eq
    (combine_pos_eq (combine_pos_eq e8 e9) (combine_pos_eq e10 e11))
    (combine_pos_eq (combine_pos_eq e12 e13) (combine_pos_eq e14 e15))
  have hPos45 := combine_pos_eq
    (combine_pos_eq (combine_pos_eq e16 e17) (combine_pos_eq e18 e19))
    (combine_pos_eq (combine_pos_eq e20 e21) (combine_pos_eq e22 e23))
  have hPos := combine_pos_eq hPos01 (combine_pos_eq hPos23 hPos45)
  have hAll :=
    (scale_state24_tail_sum st).trans (congrArg (Goldilocks.mul (Goldilocks.ofNat 8388608)) hsEq.symm)
  have ⟨hb0LeSum, hWGe1, hWLtP⟩ := branch25_w_bounds
    (nzBit st.b0.x0) (nzBit st.b0.x1) (nzBit st.b0.x2) (nzBit st.b0.x3)
    (nzBit st.b1.x0) (nzBit st.b1.x1) (nzBit st.b1.x2) (nzBit st.b1.x3)
    (nzBit st.b2.x0) (nzBit st.b2.x1) (nzBit st.b2.x2) (nzBit st.b2.x3)
    (nzBit st.b3.x0) (nzBit st.b3.x1) (nzBit st.b3.x2) (nzBit st.b3.x3)
    (nzBit st.b4.x0) (nzBit st.b4.x1) (nzBit st.b4.x2) (nzBit st.b4.x3)
    (nzBit st.b5.x0) (nzBit st.b5.x1) (nzBit st.b5.x2) (nzBit st.b5.x3)
    (nzBit_le_one st.b0.x0) (nzBit_le_one st.b0.x1) (nzBit_le_one st.b0.x2) (nzBit_le_one st.b0.x3)
    (nzBit_le_one st.b1.x0) (nzBit_le_one st.b1.x1) (nzBit_le_one st.b1.x2) (nzBit_le_one st.b1.x3)
    (nzBit_le_one st.b2.x0) (nzBit_le_one st.b2.x1) (nzBit_le_one st.b2.x2) (nzBit_le_one st.b2.x3)
    (nzBit_le_one st.b3.x0) (nzBit_le_one st.b3.x1) (nzBit_le_one st.b3.x2) (nzBit_le_one st.b3.x3)
    (nzBit_le_one st.b4.x0) (nzBit_le_one st.b4.x1) (nzBit_le_one st.b4.x2) (nzBit_le_one st.b4.x3)
    (nzBit_le_one st.b5.x0) (nzBit_le_one st.b5.x1) (nzBit_le_one st.b5.x2) (nzBit_le_one st.b5.x3)
  let cPos : Nat :=
    (nzBit st.b0.x1 * 8388608 + (nzBit st.b0.x2 * 4194304 + nzBit st.b0.x3 * 2097152)) +
    ((nzBit st.b1.x0 * 1048576 + nzBit st.b1.x1 * 524288) + (nzBit st.b1.x2 * 262144 + nzBit st.b1.x3 * 131072)) +
    (((nzBit st.b2.x0 * 65536 + nzBit st.b2.x1 * 32768) + (nzBit st.b2.x2 * 16384 + nzBit st.b2.x3 * 8192)) +
     ((nzBit st.b3.x0 * 4096 + nzBit st.b3.x1 * 2048) + (nzBit st.b3.x2 * 1024 + nzBit st.b3.x3 * 512)) +
     (((nzBit st.b4.x0 * 256 + nzBit st.b4.x1 * 128) + (nzBit st.b4.x2 * 64 + nzBit st.b4.x3 * 32)) +
      ((nzBit st.b5.x0 * 16 + nzBit st.b5.x1 * 8) + (nzBit st.b5.x2 * 4 + nzBit st.b5.x3 * 2))))
  let W : Nat := 8388608 + cPos - nzBit st.b0.x0
  have hWSZero : Goldilocks.mul (Goldilocks.ofNat W) s = Goldilocks.zero :=
    combine_lane0_with_pos hb0LeSum hAll e0 hPos
  have hWNz : Goldilocks.ofNat W ≠ Goldilocks.zero := ofNat_ne_zero_of_bounds hWGe1 hWLtP
  have hCancel : s = Goldilocks.zero := by
    calc s = CommRingOps.mul CommRingOps.one s := (LawfulCommRing.one_mul s).symm
      _ = CommRingOps.mul (CommRingOps.mul (LawfulField.inv (Goldilocks.ofNat W)) (Goldilocks.ofNat W)) s := by
          rw [LawfulCommRing.mul_comm (LawfulField.inv _), LawfulField.mul_inv_cancel hWNz]
      _ = CommRingOps.mul (LawfulField.inv (Goldilocks.ofNat W)) (Goldilocks.mul (Goldilocks.ofNat W) s) :=
          LawfulCommRing.mul_assoc _ _ _
      _ = CommRingOps.mul (LawfulField.inv (Goldilocks.ofNat W)) CommRingOps.zero :=
          congrArg (CommRingOps.mul (LawfulField.inv (Goldilocks.ofNat W))) hWSZero
      _ = Goldilocks.zero := LawfulCommRing.mul_zero _
  exact hs hCancel

/-- **Maximal Nonzero-Sum Differential/Linear Branch Number `25` (`poseidon2_gl24_mi_nonzero_sum_branch_25`)**:
    For every state `st` with `state24Sum st ≠ 0`, `stateWeight24 st + stateWeight24 (applyMI24 st) ≥ 25`. -/
theorem poseidon2_gl24_mi_nonzero_sum_branch_25 (st : Poseidon2State24)
    (hs : state24Sum st ≠ Goldilocks.zero) :
    25 ≤ stateWeight24 st + stateWeight24 (applyMI24 st) :=
  branch25_aux st (applyMI24 st) (state24Sum st) rfl rfl hs

/-- `#tooth` **Zero-sum exception**: when `state24Sum st = 0` (`b0.x1 = 1, b0.x2 = -1`, weight `2`),
    `applyMI24 st` leaves all 22 zero lanes zero (`weight(st) + weight(M_I st) = 4 < 25`), proving the
    `state24Sum st ≠ 0` hypothesis in `poseidon2_gl24_mi_nonzero_sum_branch_25` is necessary. -/
theorem tooth_poseidon2_gl24_mi_zero_sum_weight_four :
    ∃ st : Poseidon2State24, st ≠ state24Zero ∧ state24Sum st = Goldilocks.zero ∧
      ¬ (25 ≤ stateWeight24 st + stateWeight24 (applyMI24 st)) :=
  ⟨⟨⟨Goldilocks.zero, Goldilocks.one, Goldilocks.sub Goldilocks.zero Goldilocks.one, Goldilocks.zero⟩,
    lane4Zero, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 4. Grain-LFSR Round Constants, `(8, 44)` Permutation Bijection & 1-Call Jive Merkle Compression -/

def sboxLane4 (b : Lane4) : Lane4 :=
  ⟨sbox7 b.x0, sbox7 b.x1, sbox7 b.x2, sbox7 b.x3⟩

def sboxLane4Inv (b : Lane4) : Lane4 :=
  ⟨sbox7Inv b.x0, sbox7Inv b.x1, sbox7Inv b.x2, sbox7Inv b.x3⟩

def sboxState24 (st : Poseidon2State24) : Poseidon2State24 :=
  ⟨sboxLane4 st.b0, sboxLane4 st.b1, sboxLane4 st.b2,
   sboxLane4 st.b3, sboxLane4 st.b4, sboxLane4 st.b5⟩

def sboxState24Inv (st : Poseidon2State24) : Poseidon2State24 :=
  ⟨sboxLane4Inv st.b0, sboxLane4Inv st.b1, sboxLane4Inv st.b2,
   sboxLane4Inv st.b3, sboxLane4Inv st.b4, sboxLane4Inv st.b5⟩

private theorem sboxState24Inv_sboxState24 (st : Poseidon2State24) :
    sboxState24Inv (sboxState24 st) = st := by
  unfold sboxState24Inv sboxState24 sboxLane4Inv sboxLane4
  apply Poseidon2State24.ext <;> apply Lane4.ext <;> exact sbox7Inv_sbox7 _

private theorem sboxState24_sboxState24Inv (st : Poseidon2State24) :
    sboxState24 (sboxState24Inv st) = st := by
  unfold sboxState24 sboxState24Inv sboxLane4 sboxLane4Inv
  apply Poseidon2State24.ext <;> apply Lane4.ext <;> exact sbox7_sbox7Inv _

private theorem state24Sub_add_right (a c : Poseidon2State24) :
    state24Sub (state24Add a c) c = a := by
  unfold state24Sub state24Add
  exact Poseidon2State24.ext (lane4Sub_add_right _ _) (lane4Sub_add_right _ _)
    (lane4Sub_add_right _ _) (lane4Sub_add_right _ _) (lane4Sub_add_right _ _) (lane4Sub_add_right _ _)

private theorem state24Add_sub_right (a c : Poseidon2State24) :
    state24Add (state24Sub a c) c = a := by
  unfold state24Add state24Sub
  exact Poseidon2State24.ext (lane4Add_sub_cancel _ _) (lane4Add_sub_cancel _ _)
    (lane4Add_sub_cancel _ _) (lane4Add_sub_cancel _ _)
    (lane4Add_sub_cancel _ _) (lane4Add_sub_cancel _ _)

def externalRound24 (rc : Poseidon2State24) (st : Poseidon2State24) : Poseidon2State24 :=
  applyME24 (sboxState24 (state24Add st rc))

def externalRound24Inv (rc : Poseidon2State24) (st : Poseidon2State24) : Poseidon2State24 :=
  state24Sub (sboxState24Inv (applyME24Inv st)) rc

private theorem externalRound24Inv_externalRound24 (rc st : Poseidon2State24) :
    externalRound24Inv rc (externalRound24 rc st) = st := by
  unfold externalRound24Inv externalRound24
  rw [applyME24Inv_applyME24, sboxState24Inv_sboxState24, state24Sub_add_right]

private theorem externalRound24_externalRound24Inv (rc st : Poseidon2State24) :
    externalRound24 rc (externalRound24Inv rc st) = st := by
  unfold externalRound24 externalRound24Inv
  rw [state24Add_sub_right, sboxState24_sboxState24Inv, applyME24_applyME24Inv]

def internalRound24 (rc : Goldilocks) (st : Poseidon2State24) : Poseidon2State24 :=
  let x0' := sbox7 (Goldilocks.add st.b0.x0 rc)
  applyMI24 ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2, st.b3, st.b4, st.b5⟩

def internalRound24Inv (rc : Goldilocks) (st : Poseidon2State24) : Poseidon2State24 :=
  let u := applyMI24Inv st
  ⟨⟨Goldilocks.sub (sbox7Inv u.b0.x0) rc, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2, u.b3, u.b4, u.b5⟩

private theorem internalRound24Inv_internalRound24 (rc : Goldilocks) (st : Poseidon2State24) :
    internalRound24Inv rc (internalRound24 rc st) = st := by
  unfold internalRound24Inv internalRound24
  rw [applyMI24Inv_applyMI24]
  dsimp only
  rw [sbox7Inv_sbox7]
  have hSub : Goldilocks.sub (Goldilocks.add st.b0.x0 rc) rc = st.b0.x0 := by
    change CommRingOps.sub (CommRingOps.add st.b0.x0 rc) rc = st.b0.x0
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  rw [hSub]

private theorem internalRound24_internalRound24Inv (rc : Goldilocks) (st : Poseidon2State24) :
    internalRound24 rc (internalRound24Inv rc st) = st := by
  have hCancel : ∀ u : Poseidon2State24,
      internalRound24 rc ⟨⟨Goldilocks.sub (sbox7Inv u.b0.x0) rc, u.b0.x1, u.b0.x2, u.b0.x3⟩,
        u.b1, u.b2, u.b3, u.b4, u.b5⟩ = applyMI24 u := fun u => by
    cases u with | mk b0 b1 b2 b3 b4 b5 =>
      cases b0 with | mk x0 x1 x2 x3 =>
        unfold internalRound24; dsimp only
        have hAdd : Goldilocks.add (Goldilocks.sub (sbox7Inv x0) rc) rc = sbox7Inv x0 := by
          change CommRingOps.add (CommRingOps.sub (sbox7Inv x0) rc) rc = sbox7Inv x0
          rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]
        rw [hAdd, sbox7_sbox7Inv]
  unfold internalRound24Inv
  rw [hCancel (applyMI24Inv st), applyMI24_applyMI24Inv]

def runRounds {α σ : Type} (step : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => runRounds step cs (step c s)

def runRoundsInv {α σ : Type} (stepInv : α → σ → σ) : List α → σ → σ
  | [], s => s
  | c :: cs, s => stepInv c (runRoundsInv stepInv cs s)

private theorem runRoundsInv_runRounds {α σ : Type} (step stepInv : α → σ → σ)
    (hL : ∀ c s, stepInv c (step c s) = s) :
    ∀ (cs : List α) (s : σ), runRoundsInv stepInv cs (runRounds step cs s) = s
  | [], _ => rfl
  | c :: cs, s => by
    unfold runRounds runRoundsInv
    rw [runRoundsInv_runRounds step stepInv hL cs (step c s), hL]

private theorem runRounds_runRoundsInv {α σ : Type} (step stepInv : α → σ → σ)
    (hR : ∀ c s, step c (stepInv c s) = s) :
    ∀ (cs : List α) (s : σ), runRounds step cs (runRoundsInv stepInv cs s) = s
  | [], _ => rfl
  | c :: cs, s => by
    unfold runRounds runRoundsInv
    rw [hR, runRounds_runRoundsInv step stepInv hR cs s]

/-- The 236 Grain-LFSR round constants (`field=1, sbox=0, n=64, t=24, R_F=8, R_P=44`) matching `POSEIDON2_GL24_RC`. -/
def poseidon2Gl24RcWords : List Nat := [
  0xD5BF8AE11C92B989, 0x260F9DF9310DFA25, 0x592432578A606550, 0xBBA16923E2A2D02F,
  0x8186E689E4D19FE2, 0x6710500744D40C61, 0x94AB290278034115, 0x09E5E099E84C8CED,
  0x837D929C50E40826, 0xA70DC82E9B01D522, 0x31935D3C3E0F8A5A, 0x43E7EF85F89C6EF6,
  0x2D825D978F0DB37D, 0x10DF4F507965E5D1, 0x2BEFD14E9F68FD6C, 0xCCC326E2586546FC,
  0xDF9019005948354A, 0x9DB550A181AD3921, 0x96F3555B2A083851, 0xB5E8DDBEB0793433,
  0x64C3C22CA9101B42, 0x2CCEBEC54F899583, 0x042880BB620E90E8, 0xDAEAFCA5DC5056CB,
  0xD1D6E1A20F99C0BE, 0x6226660B08A6F1BF, 0xB52C699A069D9692, 0x3A52D12F49152AA8,
  0x191FDA0ACEBAFD70, 0xEC74521FBFBEF34E, 0xCA8858549BB6C38B, 0xD2E0823E1F895C8B,
  0xCE6AF0F65EBA2097, 0x1F7DC7B5D45A7CD2, 0x6C4C19343F84D09E, 0xC6904F7CA68627EC,
  0x61CF36273D3AFD34, 0x5C44CCB71106CE37, 0xA52532EBA89ED18F, 0x60C0AA5F964A4045,
  0x4FE93A8B09BEDE3C, 0xF527DADC07C2C43C, 0x3CC1A0CFE0223264, 0x735865252CB5EF9D,
  0x82D7D081FF9ABF8E, 0x2750D74D59176D65, 0x4F7C1C75FF71C541, 0x7F3400DF32068090,
  0x5B913EF8AF694F26, 0xCBE1569D0A51FD68, 0x2C75D647DDC081FD, 0x96C13E58F3B38A62,
  0x496FD72241D8F3A3, 0xF00B449AFC0B1ADF, 0xFFDF86D47806CC01, 0xE5C5829F9A87DAF1,
  0x23E37341879D515E, 0x40E752E90576C96B, 0xF38C008E636E7766, 0x011BE5EEEF591F11,
  0x35BB0D9AA2395D9C, 0x20F9929BE109EF16, 0x2F47ED98704FF1B3, 0xBD3FEFFCE9168BAC,
  0x9E93E8584169F154, 0xC101CAAA756D6273, 0x5A7304DE0B923DE4, 0x4D733CE9743DDA95,
  0x030AFC51F4773B1A, 0xBE9BEB2814D5F26D, 0x041457EA23A9560E, 0x0D6426EFAB24E9EB,
  0x4C990D19967E6195, 0x609041AC55071D96, 0xC1DEC65DE8603B08, 0xA786C9D7BBECBE0F,
  0x5F917B3FBC155F42, 0x5E2750EE5E630CB1, 0xFA9441D8B670DD72, 0x199581935DE3BBE1,
  0x773E66E3F25FF275, 0x81C6FC6D036C2F79, 0x7A89BEC509557B68, 0xD0CE5771ACE9C477,
  0x82B00C5CF2D9E7CF, 0xCEAB40115DBAFE74, 0x1B6E699BC6CBB141, 0x34DA4D64DFEAE0C4,
  0x5052731A0D6EB36D, 0xBAC21ACB2D51D029, 0xF8BE263FDA6A23E9, 0x8A180FE76B3D6598,
  0xAAAECCE7B5C242F8, 0x9CC2044963F82975, 0xFAAEFD24975B8281, 0x10AC86FC5BCA467F,
  0xAE56D1A26332ADB1, 0x041CDF5D414C8E00, 0x5D1433A3E546B7E3, 0xA7D44D7291E80DF4,
  0x666E2424EDED37DB, 0x30F77A8CE061BB38, 0xE34B90D6822F097B, 0xBBB62D4B35C9690B,
  0xD705F328CD84C560, 0x50D9FE62B0DDB847, 0x207C9F06E6F738AF, 0x3EB0014EDBCE5FF6,
  0x8F670712BD4A7C06, 0x743C54A67F4CB1B0, 0x6AC5F9961E689829, 0x017323ADC7642AD3,
  0x11E26CE992890AC8, 0x7C2C7BEA88F55D71, 0x9031876CD7240FC0, 0x7E8103C164B8BCF0,
  0x241469CC623303EA, 0xFDBFF43E97F5D12D, 0xADCFA466A0FE777E, 0x5B0D89C22C13CB55,
  0x39149BDBC24B61F7, 0x4B3227B21D8AD305, 0xE9CC64CB74054EFE, 0xE331CDDF0C8BBC86,
  0xFEEAD8DF8A753555, 0xEA647E77EA830D4C, 0x09FEE5990DA0DDEA, 0x2D03A2DA7FAE6365,
  0x5701E887DDAE112B, 0x07B8FCB458AB3738, 0x89ACFCE4460CFABA, 0x887BCB83C1E7CA78,
  0x9FFB5BDA660B1D57, 0x255AD1A68673D75A, 0x4185FB0593177EFD, 0x135CC5E6DBEB9CCB,
  0x7C0380AF942806A0, 0x2FA13E5EAB16D370, 0xC319501C58979653, 0xA0286BF5D5C5D17C,
  0x14A12A392E083337, 0xC6E93F876C58E64D, 0x6AF72F6425763436, 0x99D1B5E1DDA2A84E,
  0x731D7B66DBF1908A, 0x5C79E43127E5359C, 0x6C35271BEA1699DA, 0xB28ED7593E646253,
  0x64963DCD50DF6A37, 0xADBA13F2B4CDFDDF, 0xB92C782D580820D7, 0x0C49406D0BF61AF0,
  0x7B64E36C1CE9DF84, 0xDCF480C3320CCF23, 0x4C3D9A4A5826CB07, 0x30C385C667A6D9E1,
  0x9886A00E36B72D1D, 0xB34E65714720198E, 0xB025E90315B2B014, 0xA7C1444587E54DC2,
  0xD73A18E7CDBECA00, 0x4DDF042CA95B8E38, 0x3D01D171320415C8, 0x815E1561637009B5,
  0x5C19D306C0F40819, 0x941240C1EC94BFDA, 0xDA98CF3370DB7009, 0x5419A91CBFC3E19C,
  0x4B16F27EB28FE9C1, 0x0F29D651515358BE, 0x7B3A882F5B6868FE, 0x8CB08C6E7FC80207,
  0x96781F1035EB6496, 0x4D54331E5ABAB73B, 0xC5F7DA04667D0FA1, 0xAB88CDFC63133CA8,
  0x816006C9C1FFECC7, 0xE7223FBD2834D6FB, 0x255FAF450A99E279, 0x7C8D180FFA074DF3,
  0x18759C88B5A4A77B, 0x79FD00FE7F777BAC, 0x435652355C66EA7F, 0x3B6FFC9372478E5B,
  0x30CB2B8695AA63BC, 0xFC41D8C7E2A8C3CF, 0xB997CCD3DA7FEC2B, 0xDC74E2C341716150,
  0xE3BCE7A490863D53, 0x53B06A4A507CAF4C, 0xE1BD9FB50B9CA99B, 0x6F3F00BFED4E8F96,
  0x545F04C63B604F10, 0xBB7F48E5A268E0C9, 0xE81C580FD20BF995, 0xD58C0B9BD1C4D0C1,
  0x40A4B56AB10CDAB8, 0xC8D60A42BAD3C402, 0x64C117840FDC1D45, 0xFA3F3045A92898CD,
  0x5976828B0DADE5AA, 0xD5799E65EEB4B83B, 0x8468B013305DBA4B, 0xF778AD262258648C,
  0xC4C4DEA693460642, 0x260A16EC33184BAC, 0x165C37F648EAE04C, 0xC770334EB4D86222,
  0x34E1409BCF3D2D49, 0x21CED38891C7C5B2, 0x85AE9FAECFC0F77F, 0xDDA99AA0028E5AD7,
  0x92942B704E466454, 0x152E8D42FC9CECE1, 0x20A5C832A26F8E04, 0xC68513EAB138AB5E,
  0x12F64E5C04268504, 0x834D365BCD434547, 0xF83A067EAC681FE3, 0x58A7B388B42B4A86,
  0xFC14EF180DC44036, 0xCCBDC423FA397007, 0x93C151DAE8AE215F, 0xEF1E1257F8F3CA18,
  0x732664212B7022B8, 0x361A2F369AF43085, 0xB33A51623CD46175, 0x5426FDFF93B406BF,
  0xBB5C0ADF3633BF48, 0x1C88E1C43458B977, 0x0D446D3D0E3FFDC6, 0xB9091B410833FB23,
  0x081A8B34A6133C46, 0x9C232A0BBDB6BCAB, 0xAEFACA1D3E76DEB8, 0x4107C3371F3C1A72]

def rcAt (idx : Nat) : Goldilocks := Goldilocks.ofNat (poseidon2Gl24RcWords.getD idx 0)

def extRoundConst24 (base : Nat) : Poseidon2State24 :=
  ⟨⟨rcAt (base + 0), rcAt (base + 1), rcAt (base + 2), rcAt (base + 3)⟩,
   ⟨rcAt (base + 4), rcAt (base + 5), rcAt (base + 6), rcAt (base + 7)⟩,
   ⟨rcAt (base + 8), rcAt (base + 9), rcAt (base + 10), rcAt (base + 11)⟩,
   ⟨rcAt (base + 12), rcAt (base + 13), rcAt (base + 14), rcAt (base + 15)⟩,
   ⟨rcAt (base + 16), rcAt (base + 17), rcAt (base + 18), rcAt (base + 19)⟩,
   ⟨rcAt (base + 20), rcAt (base + 21), rcAt (base + 22), rcAt (base + 23)⟩⟩

def initialExtConsts24 : List Poseidon2State24 :=
  (List.range 4).map (fun r => extRoundConst24 (24 * r))

def internalConsts24 : List Goldilocks :=
  (List.range 44).map (fun r => rcAt (96 + r))

def terminalExtConsts24 : List Poseidon2State24 :=
  (List.range 4).map (fun r => extRoundConst24 (140 + 24 * r))

/-- Full GSR-hardened `(R_F, R_P) = (8, 44)` `Poseidon2-GL-w24` permutation (`236` $x^7$ S-boxes). -/
@[expose] def poseidon2Gl24Perm (st : Poseidon2State24) : Poseidon2State24 :=
  let s0 := applyME24 st
  let s1 := runRounds externalRound24 initialExtConsts24 s0
  let s2 := runRounds internalRound24 internalConsts24 s1
  runRounds externalRound24 terminalExtConsts24 s2

def poseidon2Gl24PermInv (st : Poseidon2State24) : Poseidon2State24 :=
  let s2 := runRoundsInv externalRound24Inv terminalExtConsts24 st
  let s1 := runRoundsInv internalRound24Inv internalConsts24 s2
  let s0 := runRoundsInv externalRound24Inv initialExtConsts24 s1
  applyME24Inv s0

theorem poseidon2Gl24PermInv_left_inv (st : Poseidon2State24) :
    poseidon2Gl24PermInv (poseidon2Gl24Perm st) = st := by
  unfold poseidon2Gl24PermInv poseidon2Gl24Perm
  dsimp only
  rw [runRoundsInv_runRounds externalRound24 externalRound24Inv externalRound24Inv_externalRound24,
      runRoundsInv_runRounds internalRound24 internalRound24Inv internalRound24Inv_internalRound24,
      runRoundsInv_runRounds externalRound24 externalRound24Inv externalRound24Inv_externalRound24,
      applyME24Inv_applyME24]

theorem poseidon2Gl24PermInv_right_inv (st : Poseidon2State24) :
    poseidon2Gl24Perm (poseidon2Gl24PermInv st) = st := by
  unfold poseidon2Gl24Perm poseidon2Gl24PermInv
  dsimp only
  rw [applyME24_applyME24Inv,
      runRounds_runRoundsInv externalRound24 externalRound24Inv externalRound24_externalRound24Inv,
      runRounds_runRoundsInv internalRound24 internalRound24Inv internalRound24_internalRound24Inv,
      runRounds_runRoundsInv externalRound24 externalRound24Inv externalRound24_externalRound24Inv]

/-- Constructive `SimpleEquiv` certifying `poseidon2Gl24Perm` is a bijection on `𝔽_p^24`. -/
def poseidon2Gl24PermEquiv : SimpleEquiv Poseidon2State24 Poseidon2State24 where
  toFun := poseidon2Gl24Perm
  invFun := poseidon2Gl24PermInv
  left_inv := poseidon2Gl24PermInv_left_inv
  right_inv := poseidon2Gl24PermInv_right_inv

def poseidon2Gl24Iv : Goldilocks := Goldilocks.ofNat 0x504F5332474C3234
def poseidon2Gl24MerkleTag : Goldilocks := Goldilocks.ofNat 0x4D524B4C474C3234

/-- 1-call 2-to-1 Merkle compression of two 7-limb digests + 2 tweak limbs (`7 + 7 + 2 = 16` rate limbs)
    with Jive-weighted feed-forward (`left + 2 * right + 4 * tweak`), matching `poseidon2_gl24_compress_merkle`. -/
@[expose] def poseidon2Gl24CompressMerkle (left right : Digest7) (tweak0 tweak1 : Goldilocks) : Digest7 :=
  let st : Poseidon2State24 :=
    ⟨⟨left.d0, left.d1, left.d2, left.d3⟩,
     ⟨left.d4, left.d5, left.d6, right.d0⟩,
     ⟨right.d1, right.d2, right.d3, right.d4⟩,
     ⟨right.d5, right.d6, tweak0, tweak1⟩,
     ⟨Goldilocks.ofNat 16, Goldilocks.ofNat 8, Goldilocks.ofNat 7, poseidon2Gl24MerkleTag⟩,
     ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, poseidon2Gl24Iv⟩⟩
  let y := poseidon2Gl24Perm st
  let c2 := Goldilocks.ofNat 2
  let c4 := Goldilocks.ofNat 4
  ⟨Goldilocks.add y.b0.x0 (Goldilocks.add left.d0 (Goldilocks.add (Goldilocks.mul c2 right.d0) (Goldilocks.mul c4 tweak0))),
   Goldilocks.add y.b0.x1 (Goldilocks.add left.d1 (Goldilocks.add (Goldilocks.mul c2 right.d1) (Goldilocks.mul c4 tweak1))),
   Goldilocks.add y.b0.x2 (Goldilocks.add left.d2 (Goldilocks.mul c2 right.d2)),
   Goldilocks.add y.b0.x3 (Goldilocks.add left.d3 (Goldilocks.mul c2 right.d3)),
   Goldilocks.add y.b1.x0 (Goldilocks.add left.d4 (Goldilocks.mul c2 right.d4)),
   Goldilocks.add y.b1.x1 (Goldilocks.add left.d5 (Goldilocks.mul c2 right.d5)),
   Goldilocks.add y.b1.x2 (Goldilocks.add left.d6 (Goldilocks.mul c2 right.d6))⟩

/-! ## 5. Fast Pure-`Nat` Evaluation Bridge, Kernel-Verified KATs & Assurance Gates -/

private structure Lane4Nat where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  deriving DecidableEq

private structure State24Nat where
  b0 : Lane4Nat
  b1 : Lane4Nat
  b2 : Lane4Nat
  b3 : Lane4Nat
  b4 : Lane4Nat
  b5 : Lane4Nat
  deriving DecidableEq

private def toLane4Nat (b : Lane4) : Lane4Nat := ⟨b.x0.val, b.x1.val, b.x2.val, b.x3.val⟩

private def toState24Nat (s : Poseidon2State24) : State24Nat :=
  ⟨toLane4Nat s.b0, toLane4Nat s.b1, toLane4Nat s.b2,
   toLane4Nat s.b3, toLane4Nat s.b4, toLane4Nat s.b5⟩

private def state24NatToList (s : State24Nat) : List Nat :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3,
   s.b3.x0, s.b3.x1, s.b3.x2, s.b3.x3,
   s.b4.x0, s.b4.x1, s.b4.x2, s.b4.x3,
   s.b5.x0, s.b5.x1, s.b5.x2, s.b5.x3]

private theorem state24ToList_val (s : Poseidon2State24) :
    s.toList.map Goldilocks.val = state24NatToList (toState24Nat s) := rfl

private def addModP (a b : Nat) : Nat := (a + b) % goldilocksPrime
private def subModP (a b : Nat) : Nat := (a + goldilocksPrime - b) % goldilocksPrime
private def mulModP (a b : Nat) : Nat := (a * b) % goldilocksPrime
private def sbox7Nat (x : Nat) : Nat := (x ^ 7) % goldilocksPrime

private def lane4AddNat (a b : Lane4Nat) : Lane4Nat :=
  ⟨addModP a.x0 b.x0, addModP a.x1 b.x1, addModP a.x2 b.x2, addModP a.x3 b.x3⟩

private def state24AddNat (a b : State24Nat) : State24Nat :=
  ⟨lane4AddNat a.b0 b.b0, lane4AddNat a.b1 b.b1, lane4AddNat a.b2 b.b2,
   lane4AddNat a.b3 b.b3, lane4AddNat a.b4 b.b4, lane4AddNat a.b5 b.b5⟩

private def sboxLane4Nat (b : Lane4Nat) : Lane4Nat :=
  ⟨sbox7Nat b.x0, sbox7Nat b.x1, sbox7Nat b.x2, sbox7Nat b.x3⟩

private def sboxState24Nat (s : State24Nat) : State24Nat :=
  ⟨sboxLane4Nat s.b0, sboxLane4Nat s.b1, sboxLane4Nat s.b2,
   sboxLane4Nat s.b3, sboxLane4Nat s.b4, sboxLane4Nat s.b5⟩

private def lane4SumNat (b : Lane4Nat) : Nat :=
  addModP (addModP b.x0 b.x1) (addModP b.x2 b.x3)

private def applyM4NatWithSum (b : Lane4Nat) (s : Nat) : Lane4Nat :=
  let c2 := 2 % goldilocksPrime
  ⟨addModP s (addModP b.x0 (mulModP c2 b.x1)),
   addModP s (addModP b.x1 (mulModP c2 b.x2)),
   addModP s (addModP b.x2 (mulModP c2 b.x3)),
   addModP s (addModP b.x3 (mulModP c2 b.x0))⟩

private def applyM4Nat (b : Lane4Nat) : Lane4Nat := applyM4NatWithSum b (lane4SumNat b)

private def sum6Lane4Nat (a0 a1 a2 a3 a4 a5 : Lane4Nat) : Lane4Nat :=
  lane4AddNat (lane4AddNat (lane4AddNat a0 a1) (lane4AddNat a2 a3)) (lane4AddNat a4 a5)

private def applyME24StdNatWithYs (y0 y1 y2 y3 y4 y5 s : Lane4Nat) : State24Nat :=
  ⟨lane4AddNat y0 s, lane4AddNat y1 s, lane4AddNat y2 s,
   lane4AddNat y3 s, lane4AddNat y4 s, lane4AddNat y5 s⟩

private def applyME24StdNatStep (y0 y1 y2 y3 y4 y5 : Lane4Nat) : State24Nat :=
  applyME24StdNatWithYs y0 y1 y2 y3 y4 y5 (sum6Lane4Nat y0 y1 y2 y3 y4 y5)

private def applyME24StdNat (st : State24Nat) : State24Nat :=
  applyME24StdNatStep (applyM4Nat st.b0) (applyM4Nat st.b1) (applyM4Nat st.b2)
    (applyM4Nat st.b3) (applyM4Nat st.b4) (applyM4Nat st.b5)

private def transpose4x6Nat (s : State24Nat) : State24Nat :=
  ⟨⟨s.b0.x0, s.b1.x2, s.b3.x0, s.b4.x2⟩,
   ⟨s.b0.x1, s.b1.x3, s.b3.x1, s.b4.x3⟩,
   ⟨s.b0.x2, s.b2.x0, s.b3.x2, s.b5.x0⟩,
   ⟨s.b0.x3, s.b2.x1, s.b3.x3, s.b5.x1⟩,
   ⟨s.b1.x0, s.b2.x2, s.b4.x0, s.b5.x2⟩,
   ⟨s.b1.x1, s.b2.x3, s.b4.x1, s.b5.x3⟩⟩

private def transpose6x4Nat (t : State24Nat) : State24Nat :=
  ⟨⟨t.b0.x0, t.b1.x0, t.b2.x0, t.b3.x0⟩,
   ⟨t.b4.x0, t.b5.x0, t.b0.x1, t.b1.x1⟩,
   ⟨t.b2.x1, t.b3.x1, t.b4.x1, t.b5.x1⟩,
   ⟨t.b0.x2, t.b1.x2, t.b2.x2, t.b3.x2⟩,
   ⟨t.b4.x2, t.b5.x2, t.b0.x3, t.b1.x3⟩,
   ⟨t.b2.x3, t.b3.x3, t.b4.x3, t.b5.x3⟩⟩

private def applyME24Nat (s : State24Nat) : State24Nat :=
  transpose6x4Nat (applyME24StdNat (transpose4x6Nat s))

private def state24SumNat (st : State24Nat) : Nat :=
  addModP
    (addModP (addModP (lane4SumNat st.b0) (lane4SumNat st.b1))
             (addModP (lane4SumNat st.b2) (lane4SumNat st.b3)))
    (addModP (lane4SumNat st.b4) (lane4SumNat st.b5))

private def applyMI24NatWithSum (st : State24Nat) (s : Nat) : State24Nat :=
  ⟨⟨subModP s (mulModP (8388608 % goldilocksPrime) st.b0.x0),
    addModP s st.b0.x1,
    addModP s (mulModP (2 % goldilocksPrime) st.b0.x2),
    addModP s (mulModP (4 % goldilocksPrime) st.b0.x3)⟩,
   ⟨addModP s (mulModP (8 % goldilocksPrime) st.b1.x0),
    addModP s (mulModP (16 % goldilocksPrime) st.b1.x1),
    addModP s (mulModP (32 % goldilocksPrime) st.b1.x2),
    addModP s (mulModP (64 % goldilocksPrime) st.b1.x3)⟩,
   ⟨addModP s (mulModP (128 % goldilocksPrime) st.b2.x0),
    addModP s (mulModP (256 % goldilocksPrime) st.b2.x1),
    addModP s (mulModP (512 % goldilocksPrime) st.b2.x2),
    addModP s (mulModP (1024 % goldilocksPrime) st.b2.x3)⟩,
   ⟨addModP s (mulModP (2048 % goldilocksPrime) st.b3.x0),
    addModP s (mulModP (4096 % goldilocksPrime) st.b3.x1),
    addModP s (mulModP (8192 % goldilocksPrime) st.b3.x2),
    addModP s (mulModP (16384 % goldilocksPrime) st.b3.x3)⟩,
   ⟨addModP s (mulModP (32768 % goldilocksPrime) st.b4.x0),
    addModP s (mulModP (65536 % goldilocksPrime) st.b4.x1),
    addModP s (mulModP (131072 % goldilocksPrime) st.b4.x2),
    addModP s (mulModP (262144 % goldilocksPrime) st.b4.x3)⟩,
   ⟨addModP s (mulModP (524288 % goldilocksPrime) st.b5.x0),
    addModP s (mulModP (1048576 % goldilocksPrime) st.b5.x1),
    addModP s (mulModP (2097152 % goldilocksPrime) st.b5.x2),
    addModP s (mulModP (4194304 % goldilocksPrime) st.b5.x3)⟩⟩

private def applyMI24Nat (st : State24Nat) : State24Nat :=
  applyMI24NatWithSum st (state24SumNat st)

private def extRound24Nat (rc st : State24Nat) : State24Nat :=
  applyME24Nat (sboxState24Nat (state24AddNat st rc))

private def intRound24Nat (rc : Nat) (st : State24Nat) : State24Nat :=
  applyMI24Nat ⟨⟨sbox7Nat (addModP st.b0.x0 rc), st.b0.x1, st.b0.x2, st.b0.x3⟩,
                st.b1, st.b2, st.b3, st.b4, st.b5⟩

private def perm24Nat (st : State24Nat) : State24Nat :=
  runRounds extRound24Nat (initialExtConsts24.map toState24Nat)
    |> (fun f => runRounds intRound24Nat (internalConsts24.map Goldilocks.val) (f (applyME24Nat st)))
    |> runRounds extRound24Nat (terminalExtConsts24.map toState24Nat)

private theorem toLane4Nat_add (a b : Lane4) :
    toLane4Nat (lane4Add a b) = lane4AddNat (toLane4Nat a) (toLane4Nat b) := by
  unfold toLane4Nat lane4Add lane4AddNat addModP
  simp only [Goldilocks.add_val]

private theorem toState24Nat_add (a b : Poseidon2State24) :
    toState24Nat (state24Add a b) = state24AddNat (toState24Nat a) (toState24Nat b) := by
  unfold toState24Nat state24Add state24AddNat
  simp only [toLane4Nat_add]

private theorem toLane4Nat_sbox (b : Lane4) :
    toLane4Nat (sboxLane4 b) = sboxLane4Nat (toLane4Nat b) := by
  unfold toLane4Nat sboxLane4 sboxLane4Nat sbox7Nat
  simp only [sbox7_val]

private theorem toState24Nat_sbox (s : Poseidon2State24) :
    toState24Nat (sboxState24 s) = sboxState24Nat (toState24Nat s) := by
  unfold toState24Nat sboxState24 sboxState24Nat
  simp only [toLane4Nat_sbox]

private theorem val_lane4Sum (b : Lane4) :
    (lane4Sum b).val = lane4SumNat (toLane4Nat b) := by
  unfold lane4Sum lane4SumNat toLane4Nat addModP
  simp only [Goldilocks.add_val]

private theorem toLane4Nat_applyM4 (b : Lane4) :
    toLane4Nat (applyM4 b) = applyM4Nat (toLane4Nat b) := by
  unfold applyM4 applyM4Nat applyM4NatWithSum toLane4Nat addModP mulModP
  dsimp only
  simp only [Goldilocks.add_val, Goldilocks.mul_val, val_lane4Sum]; rfl

private theorem toState24Nat_transpose4x6 (s : Poseidon2State24) :
    toState24Nat (poseidon2Transpose4x6 s) = transpose4x6Nat (toState24Nat s) := rfl

private theorem toState24Nat_transpose6x4 (s : Poseidon2State24) :
    toState24Nat (poseidon2Transpose6x4 s) = transpose6x4Nat (toState24Nat s) := rfl

private theorem toState24Nat_applyME24Std (st : Poseidon2State24) :
    toState24Nat (applyME24Std st) = applyME24StdNat (toState24Nat st) := by
  unfold applyME24Std applyME24StdNat applyME24StdNatStep applyME24StdNatWithYs
    sum6Lane4 sum6Lane4Nat toState24Nat
  dsimp only
  simp only [toLane4Nat_add, toLane4Nat_applyM4]

private theorem toState24Nat_applyME24 (s : Poseidon2State24) :
    toState24Nat (applyME24 s) = applyME24Nat (toState24Nat s) := by
  unfold applyME24 applyME24Nat
  rw [toState24Nat_transpose6x4, toState24Nat_applyME24Std, toState24Nat_transpose4x6]

private theorem val_state24Sum (s : Poseidon2State24) :
    (state24Sum s).val = state24SumNat (toState24Nat s) := by
  unfold state24Sum state24SumNat toState24Nat addModP
  simp only [Goldilocks.add_val, val_lane4Sum]

private theorem toState24Nat_applyMI24 (s : Poseidon2State24) :
    toState24Nat (applyMI24 s) = applyMI24Nat (toState24Nat s) := by
  unfold applyMI24 applyMI24WithSum applyMI24Nat applyMI24NatWithSum toState24Nat toLane4Nat addModP subModP mulModP
  dsimp only
  simp only [Goldilocks.add_val, Goldilocks.sub_val, Goldilocks.mul_val, val_state24Sum]; rfl

private theorem toState24Nat_extRound (rc st : Poseidon2State24) :
    toState24Nat (externalRound24 rc st) = extRound24Nat (toState24Nat rc) (toState24Nat st) := by
  unfold externalRound24 extRound24Nat
  rw [toState24Nat_applyME24, toState24Nat_sbox, toState24Nat_add]

private theorem toState24Nat_intRound (rc : Goldilocks) (st : Poseidon2State24) :
    toState24Nat (internalRound24 rc st) = intRound24Nat rc.val (toState24Nat st) := by
  unfold internalRound24 intRound24Nat
  rw [toState24Nat_applyMI24]
  unfold toState24Nat toLane4Nat addModP sbox7Nat
  simp only [sbox7_val, Goldilocks.add_val]

private theorem toState24Nat_runRounds {α β : Type} (step : α → Poseidon2State24 → Poseidon2State24)
    (stepN : β → State24Nat → State24Nat) (proj : α → β)
    (hStep : ∀ c s, toState24Nat (step c s) = stepN (proj c) (toState24Nat s)) :
    ∀ (cs : List α) (s : Poseidon2State24),
      toState24Nat (runRounds step cs s) = runRounds stepN (cs.map proj) (toState24Nat s)
  | [], _ => rfl
  | c :: cs, s => by
    unfold runRounds List.map
    rw [toState24Nat_runRounds step stepN proj hStep cs (step c s), hStep]

private theorem toState24Nat_poseidon2Gl24Perm (st : Poseidon2State24) :
    toState24Nat (poseidon2Gl24Perm st) = perm24Nat (toState24Nat st) := by
  unfold poseidon2Gl24Perm perm24Nat
  dsimp only
  rw [toState24Nat_runRounds externalRound24 extRound24Nat toState24Nat toState24Nat_extRound,
      toState24Nat_runRounds internalRound24 intRound24Nat Goldilocks.val toState24Nat_intRound,
      toState24Nat_runRounds externalRound24 extRound24Nat toState24Nat toState24Nat_extRound,
      toState24Nat_applyME24]

private def compressMerkleNatWithY (left right : List Nat) (tw0 tw1 : Nat) (y : State24Nat) : List Nat :=
  let c2 := 2 % goldilocksPrime
  let c4 := 4 % goldilocksPrime
  [addModP y.b0.x0 (addModP (left.getD 0 0) (addModP (mulModP c2 (right.getD 0 0)) (mulModP c4 tw0))),
   addModP y.b0.x1 (addModP (left.getD 1 0) (addModP (mulModP c2 (right.getD 1 0)) (mulModP c4 tw1))),
   addModP y.b0.x2 (addModP (left.getD 2 0) (mulModP c2 (right.getD 2 0))),
   addModP y.b0.x3 (addModP (left.getD 3 0) (mulModP c2 (right.getD 3 0))),
   addModP y.b1.x0 (addModP (left.getD 4 0) (mulModP c2 (right.getD 4 0))),
   addModP y.b1.x1 (addModP (left.getD 5 0) (mulModP c2 (right.getD 5 0))),
   addModP y.b1.x2 (addModP (left.getD 6 0) (mulModP c2 (right.getD 6 0)))]

private theorem compressMerkle_val_eq (left right : Digest7) (tw0 tw1 : Goldilocks) :
    (poseidon2Gl24CompressMerkle left right tw0 tw1).toList.map Goldilocks.val =
      compressMerkleNatWithY (left.toList.map Goldilocks.val) (right.toList.map Goldilocks.val) tw0.val tw1.val
        (perm24Nat (toState24Nat
          ⟨⟨left.d0, left.d1, left.d2, left.d3⟩,
           ⟨left.d4, left.d5, left.d6, right.d0⟩,
           ⟨right.d1, right.d2, right.d3, right.d4⟩,
           ⟨right.d5, right.d6, tw0, tw1⟩,
           ⟨Goldilocks.ofNat 16, Goldilocks.ofNat 8, Goldilocks.ofNat 7, poseidon2Gl24MerkleTag⟩,
           ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, poseidon2Gl24Iv⟩⟩)) := by
  unfold poseidon2Gl24CompressMerkle
  dsimp only
  rw [← toState24Nat_poseidon2Gl24Perm]
  unfold Digest7.toList compressMerkleNatWithY toState24Nat toLane4Nat addModP mulModP
  dsimp only
  simp only [List.map, List.getD, Goldilocks.add_val, Goldilocks.mul_val]; rfl

private def initExtNatConsts : List State24Nat := [⟨⟨15402181950082038153, 2742584391687338533, 6423314320102286672, 13520203159190032431⟩, ⟨9333400757695782882, 7426523777683688545, 10712701229211009301, 713223067640040685⟩, ⟨9474890391127066662, 12037497481525843234, 3572301442755562074, 4893142878842023670⟩, ⟨3279286384200627069, 1215777631466022353, 3165979198676860268, 14754679557783373564⟩, ⟨16109403356392863050, 11364077889334884641, 10877131375065446481, 13107970526536086579⟩, ⟨7260860521322126146, 3228727737523475843, 299630917512499432, 15774698434114639563⟩⟩, ⟨⟨15120520885105705150, 7072452462407774655, 13054925530097096338, 4202651403309886120⟩, ⟨1810405315179117936, 17038333586563855182, 14594011712907035531, 15195288346076732555⟩, ⟨14873965660286361751, 2269189371030306002, 7803639966520889502, 14308023412944414700⟩, ⟨7047911484017016116, 6648664036542434871, 11899973578124087695, 6971759550689591365⟩, ⟨5758197967408258620, 17665328701941924924, 4377957127459844708, 8311504322650566557⟩, ⟨9428233601681112974, 2833000892823203173, 5727484119230825793, 9165952100222795920⟩⟩, ⟨⟨6598124166890213158, 14691118691942268264, 3203702314095378941, 10863032327961021026⟩, ⟨5291684629317219235, 17296994226290760415, 18437603646583000065, 16556783227101502193⟩, ⟨2586037336326099294, 4676797898820077931, 17549402459509520230, 79910232789688081⟩, ⟨3871703262452866460, 2376091476607758102, 3406952882104168883, 13636882066222517164⟩, ⟨11426732145321308500, 13907619957760156275, 6517558437458623972, 5580871336617433749⟩, ⟨219264960804895514, 13734830045977244269, 293956538818188814, 964939030974491115⟩⟩, ⟨⟨5519457221869461909, 6958133632704126358, 13969821200782736136, 12071557779621199375⟩, ⟨6886420818894872386, 6784480348372929713, 18056129205064752498, 1843522092413467617⟩, ⟨8592418268279468661, 9351439221420470137, 8829798297910999912, 15046059550835328119⟩, ⟨9417040414182598607, 14892067036161834612, 1976633404238311745, 3808441530543956164⟩, ⟨5787815026856211309, 13457348096477483049, 17923805622670337001, 9950720863286158744⟩, ⟨12298992927954322168, 11295595528654956917, 18063653489029644929, 1201483619030943359⟩⟩]
private def intNatConsts : List Nat := [12562458705975750065, 296357267120098816, 6707042524080814051, 12093376053866139124, 7380876580335990747, 3528423578546584376, 16378343720844462459, 13526048331902052619, 15494057449610331488, 5825967292808017991, 2340920758319397039, 4517111864459419638, 10333235647091473414, 8375662481079316912, 7693829961582942249, 104466445641198291, 1288712193823017672, 8947662806928678257, 10390234716856127424, 9115571249927994608, 2599819211441374186, 18284601561822122285, 12524409849435289470, 6561051699204836181, 4113083727855968759, 5418436947633427205, 16846951131073826558, 16371092478340349062, 18368732484796233045, 16889763556046867788, 720265435947261418, 3243615215965594469, 6269547826513842475, 556472405492184888, 9920582136548358842, 9834677978047957624, 11527908664757919063, 2691694240457807706, 4721455785729031933, 1395207579900812491, 8936127577226479264, 3432092967351276400, 14058355794489349715, 11540592748734566780]
private def termExtNatConsts : List State24Nat := [⟨⟨1486515777082766135, 14333057139954214477, 7707681394439631926, 11083840139626195022⟩, ⟨8294921770393243786, 6663608023445222812, 7797181330706831834, 12866457963742913107⟩, ⟨7248048602333801015, 12518340047366127071, 13343171932137726167, 885309638851304176⟩, ⟨8891481617817264004, 15921492158508224291, 5493716764559067911, 3513799221468125665⟩, ⟨10990647923552234781, 12920375918171527566, 12692807324271816724, 12088017940262505922⟩, ⟨15508735650672069120, 5611208250593349176, 4396024995390952904, 9321911786727803317⟩⟩, ⟨⟨6636567551867619353, 10669661668836163546, 15751567516572020745, 6060060714545176988⟩, ⟨5410778628307806657, 1092640029359167678, 8879559352292763902, 10137757167429091847⟩, ⟨10842450257379026070, 5572134844428367675, 14265110057153531809, 12360355661195984040⟩, ⟨9322458692269894855, 16654944453625435899, 2693063813256307321, 8974856089317625331⟩, ⟨1762486940162369403, 8790183140757306284, 4852156037675281023, 4282919480860315227⟩, ⟨3515951791129387964, 18177047924056835023, 13373382828775959595, 15885571113887031632⟩⟩, ⟨⟨16410245836216614227, 6030436768459566924, 16266333029064812955, 8016126686062874518⟩, ⟨6079583271419662096, 13510597558244270281, 16725339941118933397, 15387686790685315265⟩, ⟨4658047384449505976, 14471765734320227330, 7260109930267155781, 18032184508763642061⟩, ⟨6446483450369009066, 15382500162894346299, 9541069407046711883, 17832193103870059660⟩, ⟨14178702333885941314, 2741028526933691308, 1611224297616629836, 14371042824073798178⟩, ⟨3810397797673151817, 2436117031968818610, 9632812226150725503, 15972467565474503383⟩⟩, ⟨⟨10562114787440223316, 1526312642570677473, 2352506500170092036, 14304861690128804702⟩, ⟨1366365694067115268, 9461278160088941895, 17886616011183497187, 6388271996167998086⟩, ⟨18164406083681271862, 14753163613136580615, 10646880994729009503, 17230229393414277656⟩, ⟨8297429457102185144, 3898480339017019525, 12914724363807514997, 6063813222437488319⟩, ⟨13500677736753250120, 2056141462702700919, 956009129908895174, 13333218137931512611⟩, ⟨583932159938739270, 11250882524017507499, 12608612333727964856, 4685928578816940658⟩⟩]

private theorem initExtConsts24_val : initialExtConsts24.map toState24Nat = initExtNatConsts := by
  decide +kernel

private theorem intConsts24_val : internalConsts24.map Goldilocks.val = intNatConsts := by
  decide +kernel

private theorem termExtConsts24_val : terminalExtConsts24.map toState24Nat = termExtNatConsts := by
  decide +kernel

private theorem runRounds_cons {α σ : Type} {step : α → σ → σ} {c : α} {cs : List α}
    {s s' out : σ} (h1 : step c s = s') (hRest : runRounds step cs s' = out) :
    runRounds step (c :: cs) s = out := by
  unfold runRounds; rw [h1]; exact hRest

def seqState24 : Poseidon2State24 :=
  ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩,
   ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩,
   ⟨Goldilocks.ofNat 12, Goldilocks.ofNat 13, Goldilocks.ofNat 14, Goldilocks.ofNat 15⟩,
   ⟨Goldilocks.ofNat 16, Goldilocks.ofNat 17, Goldilocks.ofNat 18, Goldilocks.ofNat 19⟩,
   ⟨Goldilocks.ofNat 20, Goldilocks.ofNat 21, Goldilocks.ofNat 22, Goldilocks.ofNat 23⟩⟩

private theorem perm24Nat_seq_eval : perm24Nat (toState24Nat seqState24) =
    ⟨⟨9262813872168818283, 14473920968081642809, 3132432025506878070, 739327372316014541⟩, ⟨13930273445042610257, 9887230855574303117, 10411529172945029295, 2610146355123527807⟩, ⟨15800955794096892263, 126337761019280528, 15741922631823646152, 12261346758669164007⟩, ⟨2093389069744887410, 3165987204040455923, 14526830091420603371, 2537012170462392522⟩, ⟨17818886402825694850, 14929111493621950133, 16221575831479706027, 10965213893411960579⟩, ⟨16472025002487739980, 12534132784495569014, 13110610053613593246, 5468252370409873572⟩⟩ := by
  unfold perm24Nat
  dsimp only
  rw [initExtConsts24_val, intConsts24_val, termExtConsts24_val]
  have hme : applyME24Nat (toState24Nat seqState24) = ⟨⟨441, 448, 455, 462⟩, ⟨469, 476, 567, 574⟩, ⟨581, 588, 595, 602⟩, ⟨693, 700, 707, 714⟩, ⟨721, 728, 483, 490⟩, ⟨497, 504, 511, 518⟩⟩ := by decide +kernel
  have hInit : runRounds extRound24Nat initExtNatConsts ⟨⟨441, 448, 455, 462⟩, ⟨469, 476, 567, 574⟩, ⟨581, 588, 595, 602⟩, ⟨693, 700, 707, 714⟩, ⟨721, 728, 483, 490⟩, ⟨497, 504, 511, 518⟩⟩ = ⟨⟨2546719658721551180, 9473147093471122618, 17975447038958080122, 16030253945802485373⟩, ⟨15279790520409453733, 3577425229520601954, 11050428317250274616, 17531750328992864371⟩, ⟨8921291293129306432, 14632037877695414561, 15506914541704270984, 16958738981620479987⟩, ⟨15505101423503350177, 1383599973007400377, 7143427344918302263, 9681493987809603978⟩, ⟨6785992636013614418, 15399183738189717187, 1913888962814653837, 11579386589376291617⟩, ⟨5273739284793497694, 1701863533109482427, 10709288485400581244, 5248417428446371138⟩⟩ := by
    unfold initExtNatConsts
    refine runRounds_cons (s' := ⟨⟨13811986182918985342, 5250050294993119867, 14529619014602357888, 6221450900675683784⟩, ⟨446295031360335921, 5946931734423732544, 4178543319100835118, 1010672986115492311⟩, ⟨15171281458571129030, 6224316725709823749, 1824246587269228806, 14291510116585209491⟩, ⟨6985090331160976245, 17030084625452973091, 5854253425800508205, 5603842549930017304⟩, ⟨9559266053823207392, 5934454292388150817, 684488719916269044, 7108027462336116626⟩, ⟨12409476965175695703, 2098351620154701457, 11122973215547660769, 855204209975131632⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5585742202481710939, 5461892515573896095, 9963639518258640574, 3976013325278741357⟩, ⟨12218642601863978204, 2210580033502916277, 7861970650460372788, 14507689366167755000⟩, ⟨12456083880337359378, 17894901533032762596, 1372512010575188580, 14287936328196360906⟩, ⟨12433125635575931053, 2082090220003626210, 13863016438289147071, 5140533514725436884⟩, ⟨13034853429595141451, 13066607973440359313, 4794815728891553822, 18035050209848318620⟩, ⟨3954056792262998787, 1506209631947466212, 9663499690967266948, 3283147643706514954⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨8704229552244833871, 9150528290243156457, 17786654491784994725, 14815618955800456894⟩, ⟨13447042325021395760, 7997611947323848418, 7406226205950606872, 16830800781930637239⟩, ⟨4732452794405788209, 8783714563025454528, 6761637774197025279, 7130346019063726546⟩, ⟨2657624591636650549, 1657569411390869856, 179057505132508391, 3999554014140081173⟩, ⟨11348531987833960162, 1336250567452976058, 14722920058864153186, 10146215030619086829⟩, ⟨6094949890953316350, 9250144101581395670, 18378647625837538648, 11374241467682199284⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2546719658721551180, 9473147093471122618, 17975447038958080122, 16030253945802485373⟩, ⟨15279790520409453733, 3577425229520601954, 11050428317250274616, 17531750328992864371⟩, ⟨8921291293129306432, 14632037877695414561, 15506914541704270984, 16958738981620479987⟩, ⟨15505101423503350177, 1383599973007400377, 7143427344918302263, 9681493987809603978⟩, ⟨6785992636013614418, 15399183738189717187, 1913888962814653837, 11579386589376291617⟩, ⟨5273739284793497694, 1701863533109482427, 10709288485400581244, 5248417428446371138⟩⟩) (by decide +kernel) ?_
    rfl
  have hInt : runRounds intRound24Nat intNatConsts ⟨⟨2546719658721551180, 9473147093471122618, 17975447038958080122, 16030253945802485373⟩, ⟨15279790520409453733, 3577425229520601954, 11050428317250274616, 17531750328992864371⟩, ⟨8921291293129306432, 14632037877695414561, 15506914541704270984, 16958738981620479987⟩, ⟨15505101423503350177, 1383599973007400377, 7143427344918302263, 9681493987809603978⟩, ⟨6785992636013614418, 15399183738189717187, 1913888962814653837, 11579386589376291617⟩, ⟨5273739284793497694, 1701863533109482427, 10709288485400581244, 5248417428446371138⟩⟩ = ⟨⟨14969635859164057230, 9448787690476171214, 9292548227376260786, 4180790751300341999⟩, ⟨13996151291085529245, 6663586995284079128, 12321063357610184517, 8750499573013414204⟩, ⟨15734287036257765739, 2745823942826254056, 7013266715057232467, 13008281178537255385⟩, ⟨14504284238385545039, 4205116158511176071, 16682203033342081038, 13192856921588998913⟩, ⟨17615769561727854216, 8104127387961042006, 14530916899771451480, 4772813454990489017⟩, ⟨9012825326803713426, 18086538563555436904, 1186133744305242005, 2983074779849861425⟩⟩ := by
    unfold intNatConsts
    refine runRounds_cons (s' := ⟨⟨14125204200368256153, 13557357554409728532, 3141616400025597516, 12864994035904794443⟩, ⟨15642070207726729852, 5982781925024484215, 7209779294070291527, 864843282192282077⟩, ⟨2311363677785601308, 5196861059804116367, 11524505965254091692, 11446758321186266541⟩, ⟨11685382333300151969, 8159270588973163559, 9968831848609278198, 2129453837479605187⟩, ⟨10437894631656449604, 2068382859750555557, 4065744534314147899, 3725441541434479249⟩, ⟨16731279861042891738, 17765773172111350647, 6711712657211883897, 3369288756159569874⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6547847792114403737, 4856986523249531452, 16029605838305582273, 5866116973629812050⟩, ⟨5755726214166135810, 13237163491573213076, 651637546114119932, 9756110890316687206⟩, ⟨10453018684178005529, 11977231350258106081, 7335325035682350825, 17544409854730281390⟩, ⟨15982333606249755416, 4618451693105535253, 10680881547096596190, 15925011041126820038⟩, ⟨17595872140987115452, 16610047592297780085, 7024553344321355600, 4369287891459514715⟩, ⟨1901342637766586013, 15022945371845920606, 16901352636474542992, 1782838466741878689⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨10823406193933347980, 1332876564117861727, 10088357648064910500, 1493613865972994154⟩, ⟨5628211615368248113, 5356321142479311960, 17328291516520168099, 12124432730455028866⟩, ⟨6296708617802966875, 487600184122489725, 7473262219071335512, 13269601744285929302⟩, ⟨3771136498894836789, 5741353851191797538, 1350402622810884252, 1108670062807196643⟩, ⟨6581572284419924235, 10187362713563198625, 4841844308856903723, 2294894782938704024⟩, ⟨4001992313993791500, 7110321817559847776, 2653816485049076078, 6344880779574913961⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5032916173730792575, 12179579371730070482, 12576674034327445434, 16821158271504185371⟩, ⟨532163522314440696, 4314120740208278510, 11949709253820058293, 12047146641321514697⟩, ⟨5168666832150258631, 6545141457067488108, 234192533902452131, 3668509797855169426⟩, ⟨4948487459527122128, 7833388785619915128, 5298547225625408539, 5254103467356451482⟩, ⟨14922403153784244424, 6841394563346966802, 17727733229752594448, 80345673401415438⟩, ⟨935590492091152931, 10872616802935835556, 10923237789859355627, 8327559412736537360⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨16278903585394117283, 15122925631306845860, 9649950258817081925, 14887747137349763899⟩, ⟨7200654438092300946, 16629045894665478575, 16399160993526954334, 17644224458155758825⟩, ⟨449914275884844590, 18292593021541142136, 12169459201144760524, 14808333172109650439⟩, ⟨10183169262516101293, 9615875446787005447, 3453423250406619553, 13666727539227414680⟩, ⟨12404841489311464263, 12462842644921189345, 5170020722351437511, 17344571198184644189⟩, ⟨4439713942752983795, 16062416794245330078, 9626592412530470894, 17545542544441441911⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨4804466243833000104, 12274450259425414514, 16451425145752732504, 1362280969273871287⟩, ⟨17863271994027807580, 4961841970962045360, 5415842477372746354, 1130501715797489873⟩, ⟨17847063802549507532, 13029088580761122257, 11361884221521040765, 16107811879026890649⟩, ⟨7461375822613733988, 18425510536969938552, 8736133546588182737, 6236012775856197476⟩, ⟨4991876835814025403, 13966684783048085978, 964254730980978511, 498728167326825469⟩, ⟨1941487694578520550, 9805340788452823100, 12825175298500611006, 6317787419488952124⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨550147434357174303, 15412340444651042703, 17593996407316508876, 8587014062321113337⟩, ⟨16916857651545998582, 8740385442960016665, 10424152836422252628, 1703023718606642777⟩, ⟨165792304154136481, 18170634365447748201, 9698229738404438754, 6148056252123269791⟩, ⟨10131485422877017825, 8399061639029479970, 14623658576446028534, 15902553395197105275⟩, ⟨9678382640090859386, 14797851742328858698, 11290369764723838810, 9659365967402290798⟩, ⟨10500555071844913809, 4865257355212122340, 14634849195685096088, 13220376463527182027⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨13999425712979568179, 1809514198768255026, 3138422499335645754, 2298485933987081350⟩, ⟨11051570549997695053, 15562876424989973037, 6375415339581362962, 3156971397869428446⟩, ⟨7618588685846681891, 7946809885680087208, 8163389214081256343, 10113792327386809167⟩, ⟨1538985784256941119, 4222701830081995099, 8698989291086966598, 10465508321315672440⟩, ⟨9662226945278510460, 14626485824088505160, 3040239060334317381, 2011156128490172528⟩, ⟨18221116952914377433, 2294067571315937366, 18235839992330085751, 15689777926257896087⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨833342101809483931, 5390185855036437824, 9857516654939474306, 12774615392216508198⟩, ⟨18206259778591405938, 12779021553718155217, 4679777759311370051, 2712656356351175811⟩, ⟨1082587765670495833, 8822154754766232736, 14271789578175373868, 11480591958778965725⟩, ⟨1030321944589675619, 15168174630654599525, 5928604092159321591, 7982882883684176063⟩, ⟨13964751179988234755, 16793560130497276435, 7229400302065442988, 8147314715235468650⟩, ⟨8960733151528537627, 15458192035983046572, 3256158099411374775, 12339406351338194364⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7812540836693879219, 656534825677821923, 14981382280520332711, 9471322400678248249⟩, ⟨11789218713470541356, 15263253135986024361, 15892028782703135484, 2855659152385377114⟩, ⟨4710374490562760476, 3235189722217677353, 15958705577671997720, 816542543212074022⟩, ⟨2436867577034439217, 13922354412975629692, 10560681240617924699, 17850807172193748722⟩, ⟨2299628926939169213, 8378391827220068757, 13320127673431890428, 906702836762484319⟩, ⟨1796043127656480716, 4211853612099140155, 1123741704420408477, 16951318789041951500⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6634807552629432276, 7644213866489127186, 56955463022802043, 7979480504695129617⟩, ⟨9067708401502714506, 11392056314198098866, 17470510213117864084, 5282424099329597349⟩, ⟨1173059542163363598, 5092764804880413186, 5937312058213283700, 13023760166318809346⟩, ⟨17071578065405055009, 14065436028510387484, 4858716628449973981, 1485167694955957056⟩, ⟨6278833424931125562, 7490497540720465129, 10669641362220423034, 7398784898581649114⟩, ⟨18349224464901685705, 9922716546678678007, 361999649069733412, 670993332440480099⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3412731606018064626, 203531315277942165, 11119972444249003386, 6030495398154749126⟩, ⟨9760752452566778064, 8811521851227137946, 16660066255537520358, 17039810625835111858⟩, ⟨13583730359797265276, 5035022639153688125, 7197063869998240735, 10340509641919705521⟩, ⟨17017927927118769437, 13850305515003699281, 5538979983717286934, 12738148118767085405⟩, ⟨836379411052298482, 3499714913688142992, 17677300015024768096, 12062824848389476813⟩, ⟨17022211076841551704, 13460054988118266171, 3541930650550111169, 15068595648173037710⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨13453409079367217154, 6729124949686539974, 10318794453492020260, 12200831157613009992⟩, ⟨10824636977284485037, 18382734768140714698, 4692135798586303956, 8715573592395281782⟩, ⟨11249137163487626963, 4219304398731855339, 2073481190590989929, 6776371116215651059⟩, ⟨13342441249498622416, 13638969639714065710, 2859209486545731477, 1881970157728865535⟩, ⟨1144447846052954979, 15473162069020858528, 2304324141948837516, 7474038589130206098⟩, ⟨12745865961973884761, 16556144593794358390, 4592080861063767106, 6102992011538022807⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15867871713837621065, 16864893479510693758, 12326613367393609983, 3598860952032440789⟩, ⟨4499144001027112475, 9111619709442239816, 12710161529269205808, 14530156360684658202⟩, ⟨11179288041902828010, 1919794509718645629, 1846982086365106814, 13164021434767133504⟩, ⟨15827480700003482351, 167626541861393635, 5414914155934325698, 1378748698372094512⟩, ⟨9172094873202981063, 4870140022279350780, 13969053522865963203, 479832747327021523⟩, ⟨15649397836016187813, 7591672422346138756, 12935575622661998957, 5066366662956766252⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨8375345387634263468, 11588539240926381716, 930128426788323603, 9119089569545451114⟩, ⟨12270053700218003437, 11382352626589434767, 14067189240324003073, 2316449374504596836⟩, ⟨5273221780054680521, 6575694444609776636, 18041270509621160676, 8558424290313841724⟩, ⟨16921533476537475130, 17239174726758981362, 7727668302751098290, 5327578926360963662⟩, ⟨11574071974291402610, 17101000919225068417, 14924385104377850719, 10098295787509912692⟩, ⟨6495612658848327080, 6076840894148352358, 7396405252491558538, 2278837292208266048⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨14972184567343688213, 3538378532826113114, 12256840214890962925, 9979453500666951533⟩, ⟨16323292615985421610, 8046784692599428781, 17824781385732390351, 11075390774291838655⟩, ⟨2839440639973802530, 15120650864689961324, 5708305510641837010, 12019623670760688620⟩, ⟨4265036880059442800, 7919966447073193683, 6229673267458117727, 7456776389529946955⟩, ⟨4528969778141400439, 9656888412327669876, 12872887374784020363, 18039823019944062262⟩, ⟨18063146590123429023, 18003596123003623539, 8992031619109062941, 3220562632395748803⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨825651732326575628, 4312864687953610418, 6841422515494838833, 3798812018966134794⟩, ⟨2233618597108779937, 395832750816267553, 17765168416126458906, 8623221072050967026⟩, ⟨13734750752897119045, 16291597008109473159, 8841344636243723706, 4890830714544902077⟩, ⟨10260071683767967871, 11580979336089586554, 10563797171287685002, 18259624550401034362⟩, ⟨2000137852206220011, 3717942985741605972, 7528676702460427533, 6383847179133991151⟩, ⟨10069852381111471343, 18403282958308181183, 12575003170505591061, 3779339886839592425⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6314426359322622503, 9781853666665324427, 705089940286807354, 2217492985161668864⟩, ⟨4891193686167369184, 11802312991771994857, 2105312142906285050, 3952815507536074043⟩, ⟨11076398755157441274, 7153663367040786167, 12785145728925092836, 14611997861339089866⟩, ⟨7254302272298372198, 14581347136761949902, 10418986543612200582, 1862304983530183039⟩, ⟨4704451442110941944, 1538089643356398912, 14054484608095651811, 4081938588598400633⟩, ⟨13188022556937353951, 15095544994372739712, 11835457197296158829, 12866502349150370847⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12426079043463422954, 17503224723583213359, 9131550937491503640, 16591342997564564388⟩, ⟨9957432407427673762, 12090938231123963434, 1304383352260673248, 2447146567422447190⟩, ⟨5101118372147379287, 12831530147315299905, 5121839624387987009, 10097740772918027385⟩, ⟨14903448845243772031, 2361946469440656126, 6974327146783403409, 8811530403714332974⟩, ⟨3746038050582339327, 14954642780588255820, 9924919421558012301, 4700761994846133516⟩, ⟨10399140237363447674, 14864819041490806722, 2225411268869502884, 6428373209873521636⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨14320344819417146479, 3954327591104870570, 4714204742504664491, 15922986718950746121⟩, ⟨10770329918699294344, 13885417940773813266, 9744626070448616826, 13941274696656187124⟩, ⟨12204956142290339033, 6249120293857008074, 7842076766714616558, 14807719532829064012⟩, ⟨16246391184458894086, 13336693392621549424, 9019450409609325923, 8792894154030791402⟩, ⟨10437650534387236734, 15301451641419270643, 1097750202823656963, 2052898848698848394⟩, ⟨11210713500233848563, 7392996168015606997, 4341617262815214900, 2023660946957503473⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15079490449538831597, 11543958222106690997, 17018040116011149409, 15941345298561051948⟩, ⟨1518549633523253574, 8395388850407820831, 5823015705309625402, 14387495885097748955⟩, ⟨1850770943925549366, 2497691819327051444, 1342728056506116145, 7470807189175056853⟩, ⟨2272475178906793471, 13876577272284086650, 15717388145189576038, 1296268143584603785⟩, ⟨7440550416167224478, 1623301168689821873, 7300473699609570963, 15840686910246820630⟩, ⟨979891804824186983, 10871540770965496696, 2744076086957704442, 11785670751208769452⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5008262010611160265, 3244516577517092363, 7289894518018115863, 125707341410856195⟩, ⟨3848955423596429958, 15346315545448028736, 12016364300587155341, 8609835600351702757⟩, ⟨7238310344905708362, 3920365743039704116, 15094536787616832050, 4855075333030709944⟩, ⟨15596963333462765403, 14189331834109611086, 8717383304033328403, 16002143018786845656⟩, ⟨11486973939875710134, 12439645367083475408, 9880944907777764790, 4619236250295716097⟩, ⟨13839536891996588941, 1769717794328136287, 16287603027813234106, 15255022569623803024⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨725896386368350138, 9691347504755693235, 2579875893860248277, 6949660292882025652⟩, ⟨344986177180871894, 12180206752017464475, 3588863088321301043, 4073987267310047690⟩, ⟨10613351604440055158, 13936281397015301234, 5663901102345779973, 15869817278162401179⟩, ⟨17713753702336686565, 259460714850413657, 11904564864408971657, 1984592141430874403⟩, ⟨5796156369915201779, 15638204401743457286, 12650157715289146984, 11893479865880549437⟩, ⟨11912366294020724777, 2939585448134938547, 7972897492787451778, 16618963589727398778⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5635149835137271332, 7779200149486988505, 3247604432451791824, 7439749746844813557⟩, ⟨847742062178270422, 8503719982864883660, 2251007054525422720, 568620780770166936⟩, ⟨9984540945793700061, 5554284883633637221, 1866398147680903049, 15645964398195900086⟩, ⟨9556594561192605304, 9374528715394328045, 10794070957534388608, 10482447539679940420⟩, ⟨17309587402917604847, 17691260837886868769, 12415975763307673354, 7578177860099310062⟩, ⟨13094574556084202397, 18138437356086036847, 7378456553184280953, 13478586770757512588⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨11816309076765621098, 17776508392305574902, 16492517107722170045, 2862819091368671983⟩, ⟨16779244740244749773, 16929619482754634710, 8242557709973776153, 9495550073280101659⟩, ⟨15193208514805876056, 11494945108106722256, 6362468245882562793, 1244255674146499512⟩, ⟨9907511916400284408, 1945773976821702395, 1335523591012828259, 15230512109182399167⟩, ⟨10070680687255510785, 9709329151196488089, 6564008682137058944, 17091942720940782193⟩, ⟨13561854491278158163, 6166889538412714898, 17246752519977994860, 6576566350277940153⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6658302542012199030, 11566671179745325942, 8328452933469506809, 5241439152914438972⟩, ⟨17343656292910243298, 6409657539709725906, 17744336604210991763, 11209557256099558944⟩, ⟨1612725394060532503, 3463803425841741537, 4746948462345060560, 13529376393263517500⟩, ⟨11402835288594049845, 13133677931446918609, 13926931271094930736, 1393532660785593001⟩, ⟨14497009087932819872, 2395485213811583170, 13839494429231511889, 14355780979461225142⟩, ⟨13856130178900184534, 13808236433501247022, 7725204560229844072, 13402872756660428375⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7443893273828365115, 16472973725909232035, 3116464343688335390, 7425315088407077660⟩, ⟨14528344403543762230, 15227102834446598984, 876007729063528558, 2894948229366889990⟩, ⟨8420968222351638946, 6196264229749692157, 373698104109782441, 5482933117653001022⟩, ⟨4334981707914238267, 9745403339814648521, 1215206026632470020, 17923002991478829400⟩, ⟨2346820364430037397, 13633244183965963503, 14542064895741015566, 3391269299049371973⟩, ⟨3169841261588493270, 11685505556625603618, 6334258047780933503, 13039276238404007433⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨9263598567594069743, 14181919211243051767, 3941874172710490512, 8963461769547546051⟩, ⟨3255236297196411646, 1534917934089807303, 7294448745952149267, 16964935540083520203⟩, ⟨5681721920297714202, 15979342401015344639, 4574934095396586314, 4422260859973232676⟩, ⟨2867585905278732147, 14573603222388275425, 9881662244067274553, 12917860933121487654⟩, ⟨12289365808811794700, 16397527852740949026, 8514499650971950517, 13117882256252712212⟩, ⟨3377599494562713960, 17762589582540033697, 11856354465715680347, 736716840706192416⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨754853377031584941, 7527640529351064617, 1229469663528993874, 10752824326883612733⟩, ⟨940867626264721697, 17904408263544929698, 5407152355601777542, 9190439857407415224⟩, ⟨1183108409046642187, 7326936637413105493, 11422225414922581172, 2288544924125114429⟩, ⟨97041255113635828, 11607455664303875215, 18056592195439734799, 84541187035821153⟩, ⟨17308253212035599341, 6655314802333760931, 14721262070083925216, 17676204509361916163⟩, ⟨14585839091848194614, 17694095951911729437, 1580857206812381163, 12085239096178184925⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12041149849242018651, 16247176789925919750, 11178475587632842881, 14837345429280137423⟩, ⟨16246477270692628709, 42163366660381165, 15727715015100477588, 6611876913382731197⟩, ⟨12583460063228380501, 2847420358042260599, 9281078696513185440, 9453041749039821662⟩, ⟨4545841969740603346, 15598470367863940556, 3882108667330658442, 10336539449374801810⟩, ⟨1967630022284527555, 16613644767499543425, 6105181465886205764, 8244665903631559331⟩, ⟨17584371073244032131, 7018599351173015292, 2388129862017679826, 13009290899573297668⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2167045717723427779, 14046000407483208718, 1709030723408390409, 1807973126434085697⟩, ⟨17090177366610812714, 16920181553537971929, 3023614226578795117, 15130576546931230514⟩, ⟨3614977671721157169, 7315416569207213793, 8897890392760063751, 11619682261092486652⟩, ⟨10524166661362443792, 8058738005552302721, 16292994788982460749, 10550604948426077228⟩, ⟨1728871232984009313, 7447097410624811385, 14832933119065927317, 11622060388103753309⟩, ⟨14129292771966990279, 1171401501264822679, 14993855798025761662, 3101061240275383670⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12223635110174487765, 3464027443509751700, 11282832552257908121, 15096663611177470091⟩, ⟨15458981552425538768, 1886514920829913352, 12386706008889649442, 16990978499481495507⟩, ⟨9413311350384636910, 17490261811614841890, 7238867053191440528, 8269481691740571906⟩, ⟨15561020499491526391, 15230501664981722250, 17884740235242020676, 4537571634220758764⟩, ⟨9566296353269845896, 15332829311422673966, 13930101433966493653, 15459389732416689760⟩, ⟨1476948695483480796, 16464755328634984301, 8811612049470200043, 2185758884865005883⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5798061195078824543, 7272675356435466692, 7927568948026946913, 8855070149391842393⟩, ⟨16800035915842519210, 15546142576789744303, 12801614739688226395, 2873371784280952501⟩, ⟨9674136250211258607, 17203606887995833150, 2313021194611816807, 4702372393977143397⟩, ⟨15251622992584641393, 1055024917935877370, 11559255724930415402, 7003703245062490738⟩, ⟨6685580297204668367, 6620708088635032935, 9782554183040292749, 6419308794202095621⟩, ⟨11310503740099245623, 3509888658368500295, 9515465410238550284, 4387878808786617560⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5885373258419189262, 4346566909877363446, 12929029449495790580, 14047428081594682005⟩, ⟨2346970394279960187, 6004499879688209429, 897193696344286332, 14948989122691597929⟩, ⟨17878222999120433264, 10872166359704114756, 749122752158705394, 16149764938244811822⟩, ⟨2060070847896214165, 1917843175782873160, 3359481878343550245, 6999746898575671526⟩, ⟨15083246057826134735, 5931931638522510673, 1282250072351525293, 13024194660970853595⟩, ⟨12769994486211506555, 16834207850045591001, 250260632376563579, 17962718470232809467⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨4113434015706614888, 9173382093888656186, 12238130013588289579, 5676295302146267797⟩, ⟨5155834268836389915, 8665092911949721999, 15090269397613871043, 2331427426715175504⟩, ⟨5843094464018294728, 2643048786662437805, 996038831562183727, 13903425751231046852⟩, ⟨17994263848932677472, 1999489620046835354, 3160211007815092848, 5272121897342851067⟩, ⟨9019786205836576667, 13214158552320777714, 3623082006856748205, 3685933129117048135⟩, ⟨6169728366053615235, 3502944802099811922, 11097006044735602977, 10738624091091508779⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨1605455003558105495, 10432032756630883725, 7288166620504222376, 5517087801912714406⟩, ⟨5611836674604178217, 10772928768035689276, 4531925581606908569, 2896053417196785227⟩, ⟨11304979280500579883, 13796353549401270063, 13168442548386519096, 15926942404689692496⟩, ⟨15363106655940801158, 813767554504398999, 8925297295321035992, 12048083728930318345⟩, ⟨7879563355216460733, 3506452820154958577, 11330874450798777796, 6058493986281794999⟩, ⟨5444684055547530585, 7875099512512737412, 10956055762465208900, 9179003940135123075⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2944984973458710003, 8444028341720553590, 12588328826098114617, 1633602723325943168⟩, ⟨6013200843093926959, 4358159248929439392, 13906405710608653826, 17338717660952665504⟩, ⟨6203306074826317851, 6550386973629200682, 7192995022664169852, 279260624842246005⟩, ⟨9955788599984174144, 10789966340482791989, 9600691765018852206, 13654267643373199645⟩, ⟨14914023791552812093, 5813144562978085440, 11022982114309263467, 4982135121906186905⟩, ⟨2221600790125096558, 8715986910806652490, 4170005062632442226, 13936375481746895442⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨654869940166494215, 14011711505866137197, 12297596746927228520, 12102094057449356279⟩, ⟨16779801770067830637, 1511254869358276595, 7850808237672482335, 8440969300241116603⟩, ⟨6380865757087142732, 3813038096493784988, 17479064954698267952, 14829401961386727912⟩, ⟨11370539228618555814, 2871023464317537435, 15964654284209894736, 13423422399984506520⟩, ⟨17155397835524415099, 13651240945957582155, 5543621149438956548, 12916965587035681127⟩, ⟨18335449364501172050, 14696453982443435681, 18276829265977330205, 4025157589399612410⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨1245186017664560378, 12343167991935342908, 4479905910509078430, 9846344577037462185⟩, ⟨3442662160709760560, 4064790326387046910, 9749647189199044258, 3597913688477722994⟩, ⟨3425534338981765283, 15238517578919777947, 941839625509001450, 1968695817875691416⟩, ⟨5404781095666099681, 7467594113612326994, 11810644653538631454, 5601262271549754429⟩, ⟨328959610060571589, 15864212293662915933, 13040605577920045298, 570178557150014918⟩, ⟨13351442470721259307, 11053938427998419851, 15363531392665241157, 14482560438624158657⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12599290036521059212, 16473147249901703451, 13089791078984517403, 6621869427287040641⟩, ⟨13224532474229860702, 13826392271915358140, 2524040132287843342, 13035526487565620307⟩, ⟨18323261051096877384, 12927480814952223244, 6736521713795910597, 9379393196484679538⟩, ⟨5075221533387914631, 6693801524676923749, 3758336966940468066, 2659290991585928304⟩, ⟨10579945184658945431, 4204360475438029750, 5525560508175060460, 17497214394514855993⟩, ⟨781303943839034768, 16162247960904032616, 9676464288962072856, 4084331357434460358⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5814351255515506475, 9134319120021006343, 394009958673753377, 701905509852881135⟩, ⟨6223711316885266903, 10969263457204605601, 18090223895086536873, 15278128020077292416⟩, ⟨13748833664281983598, 129072072677859897, 10665892422512844850, 4852888974847302884⟩, ⟨1197961168157494457, 17057273866141262111, 11788497262907052136, 9722030126135053747⟩, ⟨6643686266160041347, 9059869400605580436, 1309190105648889231, 17965291705551899555⟩, ⟨10991217999134900271, 607804418360021551, 4201351246726057398, 642785484329904975⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨18369851043668899184, 2453171396201366695, 12553616262942451427, 14573218385006469213⟩, ⟨6215054672433326934, 2806370966722791079, 356950767097426337, 11888353951568690284⟩, ⟨728874709888750401, 7914558812297909663, 12466272125454548857, 503007847295331219⟩, ⟨11773107500003877916, 2092817117759143381, 14429970694817122350, 9872143547379923686⟩, ⟨3603658646905646727, 14015272185688858342, 18317790262340876363, 14540046860545570651⟩, ⟨15534826431606773852, 5883784349664515499, 17991543347093361371, 2507686053608939960⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7559331028376265134, 9875870485776770217, 14083187546045722055, 10375340421357527411⟩, ⟨1802904260798266031, 15431146418310892144, 398379567278461985, 11960845143973624537⟩, ⟨8484941608262533245, 4407907402236001940, 7580579304858243240, 5993900776386210790⟩, ⟨8852360372655667943, 1865621153244982833, 11006634222785365754, 11570578735169748418⟩, ⟨14500452571053115137, 12019956103613193602, 2406865908285170582, 16526823089748228320⟩, ⟨13380880998067807052, 15139940923194787212, 1323073896961976872, 3641108334368074940⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨14969635859164057230, 9448787690476171214, 9292548227376260786, 4180790751300341999⟩, ⟨13996151291085529245, 6663586995284079128, 12321063357610184517, 8750499573013414204⟩, ⟨15734287036257765739, 2745823942826254056, 7013266715057232467, 13008281178537255385⟩, ⟨14504284238385545039, 4205116158511176071, 16682203033342081038, 13192856921588998913⟩, ⟨17615769561727854216, 8104127387961042006, 14530916899771451480, 4772813454990489017⟩, ⟨9012825326803713426, 18086538563555436904, 1186133744305242005, 2983074779849861425⟩⟩) (by decide +kernel) ?_
    rfl
  have hTerm : runRounds extRound24Nat termExtNatConsts ⟨⟨14969635859164057230, 9448787690476171214, 9292548227376260786, 4180790751300341999⟩, ⟨13996151291085529245, 6663586995284079128, 12321063357610184517, 8750499573013414204⟩, ⟨15734287036257765739, 2745823942826254056, 7013266715057232467, 13008281178537255385⟩, ⟨14504284238385545039, 4205116158511176071, 16682203033342081038, 13192856921588998913⟩, ⟨17615769561727854216, 8104127387961042006, 14530916899771451480, 4772813454990489017⟩, ⟨9012825326803713426, 18086538563555436904, 1186133744305242005, 2983074779849861425⟩⟩ = ⟨⟨9262813872168818283, 14473920968081642809, 3132432025506878070, 739327372316014541⟩, ⟨13930273445042610257, 9887230855574303117, 10411529172945029295, 2610146355123527807⟩, ⟨15800955794096892263, 126337761019280528, 15741922631823646152, 12261346758669164007⟩, ⟨2093389069744887410, 3165987204040455923, 14526830091420603371, 2537012170462392522⟩, ⟨17818886402825694850, 14929111493621950133, 16221575831479706027, 10965213893411960579⟩, ⟨16472025002487739980, 12534132784495569014, 13110610053613593246, 5468252370409873572⟩⟩ := by
    unfold termExtNatConsts
    refine runRounds_cons (s' := ⟨⟨10677480738950177807, 5094608623586897777, 15602795207739113612, 4142904337638840928⟩, ⟨14607266893007205348, 303381387031006268, 16373661140368720688, 5016095276378360650⟩, ⟨12105915333803737324, 5759867108052860598, 13983271432886216943, 12565249293965296763⟩, ⟨402137128818883119, 9742136088811316249, 2877005153895550585, 8303117693673384032⟩, ⟨637168969902690783, 11714993270508206624, 9187511133609498262, 9780971090191237788⟩, ⟨12778080782956397918, 4856941846615319933, 4810533011873849839, 405687179333803369⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨9642775099087552633, 10495153699502931707, 4255938424866592398, 13580543213819642757⟩, ⟨3595811151496165885, 17958632767934159377, 4490489557447490761, 15000271738208999171⟩, ⟨439410915809538393, 13568055501969438262, 10373021444921903975, 184290104216388162⟩, ⟨706265140090435938, 2778589607837762185, 3862658083467100923, 5839003587604410060⟩, ⟨9249573231285131402, 8760288302144991588, 15126163909191728654, 11217288586145561810⟩, ⟨1053054779485057709, 9362801398769240483, 13489816396611668584, 10025995857467381752⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15657625492227184270, 5153849860416701841, 16040370151358744939, 3439228386252868968⟩, ⟨4211567624079547928, 7967725857007118098, 15230762935559721998, 12359830973487839852⟩, ⟨12025053558145267018, 12370199943734054529, 13258519728113409655, 7764840443978332887⟩, ⟨16238395109683058798, 10095329104668609372, 14878222926308103397, 10084617932137887965⟩, ⟨1335980394882499283, 9998744888514792277, 1432702208688842403, 16882264456161933180⟩, ⟨9956481365483639368, 2499180182782097741, 7964747926492421285, 6227744783597193682⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨9262813872168818283, 14473920968081642809, 3132432025506878070, 739327372316014541⟩, ⟨13930273445042610257, 9887230855574303117, 10411529172945029295, 2610146355123527807⟩, ⟨15800955794096892263, 126337761019280528, 15741922631823646152, 12261346758669164007⟩, ⟨2093389069744887410, 3165987204040455923, 14526830091420603371, 2537012170462392522⟩, ⟨17818886402825694850, 14929111493621950133, 16221575831479706027, 10965213893411960579⟩, ⟨16472025002487739980, 12534132784495569014, 13110610053613593246, 5468252370409873572⟩⟩) (by decide +kernel) ?_
    rfl
  rw [hme, hInit, hInt, hTerm]

private theorem perm24Nat_merkle_eval : perm24Nat (toState24Nat
          ⟨⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4⟩,
           ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7, Goldilocks.ofNat 8⟩,
           ⟨Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11, Goldilocks.ofNat 12⟩,
           ⟨Goldilocks.ofNat 13, Goldilocks.ofNat 14, Goldilocks.ofNat 100, Goldilocks.ofNat 200⟩,
           ⟨Goldilocks.ofNat 16, Goldilocks.ofNat 8, Goldilocks.ofNat 7, poseidon2Gl24MerkleTag⟩,
           ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, poseidon2Gl24Iv⟩⟩) =
    ⟨⟨1170443848852734242, 833485916214918700, 373819593114229842, 2500389336842599919⟩, ⟨2668122737528357646, 15131165148025152804, 573418327208874834, 11542618087740092325⟩, ⟨11689289631835769111, 12304969562289533240, 15835240181100103881, 11172752928363632645⟩, ⟨5443232731664037725, 8930854513653823679, 6656347969346280873, 5643972817548579632⟩, ⟨13107671858976799679, 4364933070422677448, 8993198673880906353, 2148388791134660717⟩, ⟨650075810295284558, 18350876254755807787, 14195893604467810598, 10050238888845265849⟩⟩ := by
  unfold perm24Nat
  dsimp only
  rw [initExtConsts24_val, intConsts24_val, termExtConsts24_val]
  have hme : applyME24Nat (toState24Nat
          ⟨⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4⟩,
           ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7, Goldilocks.ofNat 8⟩,
           ⟨Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11, Goldilocks.ofNat 12⟩,
           ⟨Goldilocks.ofNat 13, Goldilocks.ofNat 14, Goldilocks.ofNat 100, Goldilocks.ofNat 200⟩,
           ⟨Goldilocks.ofNat 16, Goldilocks.ofNat 8, Goldilocks.ofNat 7, poseidon2Gl24MerkleTag⟩,
           ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, poseidon2Gl24Iv⟩⟩) = ⟨⟨11358534001600521934, 16930132481597020417, 11358534001600522024, 11358534001600522129⟩, ⟨11358534001600521950, 17145469523204544783, 11358534001600522576, 16930132481597021059⟩, ⟨11358534001600522836, 11358534001600523139, 11358534001600522590, 17145469523204545405⟩, ⟨15628857935386980495, 13896909305961891609, 15628857935386980652, 15628857935386980854⟩, ⟨15628857935386980488, 14542920430784464661, 4270323933786458841, 15413520893779455800⟩, ⟨4270323933786458922, 4270323933786459026, 4270323933786458846, 15844194976994504514⟩⟩ := by decide +kernel
  have hInit : runRounds extRound24Nat initExtNatConsts ⟨⟨11358534001600521934, 16930132481597020417, 11358534001600522024, 11358534001600522129⟩, ⟨11358534001600521950, 17145469523204544783, 11358534001600522576, 16930132481597021059⟩, ⟨11358534001600522836, 11358534001600523139, 11358534001600522590, 17145469523204545405⟩, ⟨15628857935386980495, 13896909305961891609, 15628857935386980652, 15628857935386980854⟩, ⟨15628857935386980488, 14542920430784464661, 4270323933786458841, 15413520893779455800⟩, ⟨4270323933786458922, 4270323933786459026, 4270323933786458846, 15844194976994504514⟩⟩ = ⟨⟨6919711587574855007, 14421617632508761982, 4435454496602481509, 14231086996715217048⟩, ⟨17594995837193025458, 3627297981614136775, 6698821074054433523, 13156959501117977386⟩, ⟨10398902800119282776, 18040062189166692107, 17706991350302626549, 12651816096724672175⟩, ⟨9777889023170906499, 12688285356138252329, 10837500452456675326, 9179965429718500453⟩, ⟨3784674144688776898, 1226191381624434267, 11239934977828782897, 10810975123582636833⟩, ⟨14313213113500858463, 18125038689835218302, 11438764855145313787, 11203115575649408262⟩⟩ := by
    unfold initExtNatConsts
    refine runRounds_cons (s' := ⟨⟨11834540941623996427, 8704742143033883004, 3714371965886298157, 979652790539020933⟩, ⟨13561965825192275624, 11638217489915287252, 11691163034695632741, 7800820717993705120⟩, ⟨15084818380875896675, 2549197214955019698, 8818837188540132878, 12588341611735517543⟩, ⟨4397975821822378968, 11285816437091121760, 6530408737119085516, 12272083211871581488⟩, ⟨17680804694255765006, 13998778286548738989, 15475723499557301968, 12022538679914597137⟩, ⟨9052281140918362085, 14085549821477693132, 8000589326889640326, 13216145281859799086⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨8012371300723081999, 18170530028114620203, 847690357335849485, 5982005454961294083⟩, ⟨2238611325004175547, 6227664638819107600, 408992029406397318, 18101874943602569433⟩, ⟨6711958155483017443, 14067428393963698155, 12394518849649500143, 17028619922384827639⟩, ⟨13187291016463701839, 9670565005242443647, 10450906879970522656, 1730888796991903660⟩, ⟨18273325853638574991, 2699702727889422050, 16046545085803668064, 8530381353773079724⟩, ⟨12209327862863209426, 14481644801007005449, 9725485443968832987, 8702397967686790785⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨10707566787375351180, 5626676814324516239, 16909468984201666953, 10184625227371426790⟩, ⟨9187207535638303367, 2381397545162118449, 2623912036079293932, 10757246718068870518⟩, ⟨850244102414601686, 16641547423822229843, 8620228530007346202, 13483091068435433262⟩, ⟨15824110314715770192, 3991548208320195140, 10172293666254639456, 6618147891806448502⟩, ⟨226606813167177226, 5105303459008389893, 12492605622465807435, 745929194895828788⟩, ⟨5542481962257940506, 14962918582741084636, 18248724999782409718, 12486943263124318122⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6919711587574855007, 14421617632508761982, 4435454496602481509, 14231086996715217048⟩, ⟨17594995837193025458, 3627297981614136775, 6698821074054433523, 13156959501117977386⟩, ⟨10398902800119282776, 18040062189166692107, 17706991350302626549, 12651816096724672175⟩, ⟨9777889023170906499, 12688285356138252329, 10837500452456675326, 9179965429718500453⟩, ⟨3784674144688776898, 1226191381624434267, 11239934977828782897, 10810975123582636833⟩, ⟨14313213113500858463, 18125038689835218302, 11438764855145313787, 11203115575649408262⟩⟩) (by decide +kernel) ?_
    rfl
  have hInt : runRounds intRound24Nat intNatConsts ⟨⟨6919711587574855007, 14421617632508761982, 4435454496602481509, 14231086996715217048⟩, ⟨17594995837193025458, 3627297981614136775, 6698821074054433523, 13156959501117977386⟩, ⟨10398902800119282776, 18040062189166692107, 17706991350302626549, 12651816096724672175⟩, ⟨9777889023170906499, 12688285356138252329, 10837500452456675326, 9179965429718500453⟩, ⟨3784674144688776898, 1226191381624434267, 11239934977828782897, 10810975123582636833⟩, ⟨14313213113500858463, 18125038689835218302, 11438764855145313787, 11203115575649408262⟩⟩ = ⟨⟨11122095525565186915, 6050811279017883739, 9134166129583447155, 14662938264636479001⟩, ⟨1698636573548665178, 7557579007503755239, 6650847812082994433, 535118101817843469⟩, ⟨5705235467509404137, 14515361923076953952, 17646800853568931355, 12434778970437555469⟩, ⟨5772501093288927013, 3544769088889231214, 3204674542777705848, 8114757753475041414⟩, ⟨12865669891144658970, 13100250176221103666, 3477093962145555358, 17704486428671844357⟩, ⟨6316931895663693504, 3792601546171249908, 9338235642575563544, 8570338207213203762⟩⟩ := by
    unfold intNatConsts
    refine runRounds_cons (s' := ⟨⟨6711568200043101362, 12957516564480385003, 7406807925176586039, 120014710588738250⟩, ⟨10168657143613736438, 1232434429554058458, 9983988538153068226, 10477823879865881280⟩, ⟨1429884349389747237, 5105802004998722163, 7164132204355514498, 4381245248997736879⟩, ⟨8935303071164144688, 5274674133369130348, 13607143434076140961, 6785101502777075860⟩, ⟨15724637488977210923, 4197118700966442857, 8524953179841286261, 2167079007888584780⟩, ⟨16691591870078767960, 1604598503172362204, 17058743412694593689, 8966496262903769616⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨13835054534767162695, 827863868263957291, 2683963154136744366, 6797150215553109609⟩, ⟨13879372244449710829, 7589298176648507616, 12210075414048406384, 12815033185689522973⟩, ⟨4874847400939959735, 3683575724435543546, 3450710189719299706, 10153417479136730702⟩, ⟨6647664258098831201, 10245036368677822126, 2361691852611857318, 13340350580523928503⟩, ⟨16782983290276427301, 9287458869130422530, 14351762880654882468, 7146173626827975413⟩, ⟨16908708743248733726, 3823838462418075382, 17284515213980961703, 10220775069002106728⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨10719253666217891559, 11460267235764778909, 16000329675774310350, 927516090884091412⟩, ⟨10986916906611002324, 2933965707974853227, 13973191159343555165, 691044127973997445⟩, ⟨7423572327719800784, 12843841282856169023, 6508589839982176274, 3768246853687503422⟩, ⟨11351680725943892368, 7958611553680919439, 6977531147937017945, 3465836178135795241⟩, ⟨2647917688468258813, 4769536295247491982, 18170218012019533339, 14971153301005936577⟩, ⟨18137568915163078452, 11581043909264565090, 8357664783986571412, 14208464197744475795⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨8253985212870953950, 7816719205219828331, 9910367251589085801, 66516332991415070⟩, ⟨10464810944684730730, 6406415158223532412, 776711402498790998, 3689788020961717260⟩, ⟨5789762377445749403, 859376024838310172, 8340517545704123930, 18118463707225014782⟩, ⟨1701051240170374626, 17879349260345160680, 8278488823123828404, 1538148888233737928⟩, ⟨8285909240569772143, 11055585148372846750, 17831897554405511804, 12673134778049629118⟩, ⟨9520061771313016098, 17200037002127425357, 5215500291884763970, 9781935576714968872⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7421051296560082492, 14677192762530557726, 8234463991074316676, 7126538889276389675⟩, ⟨16791984837130237951, 17129395741814326382, 13268494367857457010, 3199233996471037862⟩, ⟨10080295093783280139, 5499807082943121575, 16007576923053203404, 2742775924654039237⟩, ⟨4178784306881526774, 7101088355189120305, 14009713419701050967, 9639459558550759261⟩, ⟨1908510834337690420, 12921942923566961478, 11522897560476679620, 8283805310308363571⟩, ⟨14783105795327478723, 5162653060659970438, 1980546006700155021, 321922663319960728⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3485635113298084403, 1964443706132384157, 3756178925750459783, 15793406500707385131⟩, ⟨10942665224156224113, 3103165840826868049, 6050701187919595689, 7570786023602406389⟩, ⟨4739682158255366074, 11732058970947125556, 11259012796181115076, 10431443307735772648⟩, ⟨4595007298016118960, 1276500400853705815, 16111473375896871475, 16063424050399770895⟩, ⟨9354619275015245122, 5058695212666824492, 7792358493276281517, 4881409003810098856⟩, ⟨8270266365018239295, 2974886990019813417, 5964880729884125942, 922799638249159827⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨17719621691286269287, 6196458785930015090, 11744372931298550499, 12065408874383418494⟩, ⟨17986360595389086553, 16989180394198351075, 13387012399078849771, 9146974785572447483⟩, ⟨2168777045803205812, 819828327684528946, 13462417067178241693, 5365146010184500626⟩, ⟨6967486015371257303, 12349085332249286330, 2968093765617937378, 7674018491769466906⟩, ⟨6850217317202126572, 5997056893898121633, 4918810441863942029, 4124558654052374748⟩, ⟨6216761517323555238, 18016835950633325383, 12122149061048717029, 10605277515774424121⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨1442101636421368998, 15477673051688046163, 14323216058940547750, 2202617555047952086⟩, ⟨5598146473554048929, 4406939531712883458, 13390497439745784362, 4391790321127971713⟩, ⟨10183515087349610194, 16243081389437013718, 2956470699963241835, 6060996009140544439⟩, ⟨912664019204723163, 10162496824044630571, 11096658719478896571, 7392606286897087041⟩, ⟨17220427708379524441, 6072669825923828135, 13898224216645637211, 128137505038579691⟩, ⟨9087239865568389806, 1030479372582911062, 5471252453097117072, 7960769374483566976⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5233799801840521335, 15947690118081180033, 10669705114859645049, 9280487286584942214⟩, ⟨8361700715996356660, 15640817365555516235, 4690821541722794071, 4843436577364558687⟩, ⟨12687863388122336232, 8181437143987173453, 1550001755577039068, 8823923103010307550⟩, ⟨6484777386793155273, 10202387753897724510, 17190217031856893935, 18056605881521146249⟩, ⟨11990825923930221489, 8903175260151647976, 15644198414322786670, 17873931565284187154⟩, ⟨16906872203996820044, 18374736605666279007, 7662662095475991925, 7709509802067510425⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2622635251716656249, 3401562889453866001, 8793283001091976066, 6129077848297870503⟩, ⟨17453990360514370606, 16346021787285933876, 8432953620600005993, 2285908612071092800⟩, ⟨6633652411962887737, 15866445857655645984, 6291520711404147302, 2693280310195884199⟩, ⟨5068975014668558273, 13005539581833376184, 5714315901525679295, 14896738481558658028⟩, ⟨5635813655638984541, 13879550555886952195, 651166901303142490, 3036259116668697181⟩, ⟨9760982690687403399, 3125785611687963278, 2623862409561034665, 16599172276007820070⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3028881996643886877, 12809171567878533591, 8547430611194035401, 15477176002201565281⟩, ⟨1465579007222957870, 12689540303195429112, 2560963496406094551, 8131807295657932222⟩, ⟨9964890216603419160, 12934052967061488874, 2486000769795830039, 315035906822439216⟩, ⟨5151527639221037971, 5900863398613998206, 3247025802574445532, 8700108111112647191⟩, ⟨13394597747266469547, 10682776452570850600, 6070887102635463603, 6404381576894201146⟩, ⟨5973830524137253398, 15694916412864704438, 2398382120306071691, 5913611816812465855⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3163983601669929831, 11241047694517986860, 15526737349027524071, 5000347927201961430⟩, ⟨10156508184423116229, 16997080283620475851, 6595731733976141617, 2358709105138754489⟩, ⟨1112483062270787600, 7582247269170011554, 16885673541912699409, 7433995532769276996⟩, ⟨15669617615597570586, 3133625916470644535, 16309046790081244852, 3011744229757982246⟩, ⟨9229214973108819812, 14038549387600224277, 2994014494615555029, 12011467989371031762⟩, ⟨7201145374335458587, 11489395786729084765, 7267297387279076157, 10500589138761510910⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15918748036061725694, 16692439205154209842, 18058122139276686803, 7006039150029484381⟩, ⟨12916480708362815530, 703515007345071783, 13600622234312327195, 8834821684199835710⟩, ⟨275270925980361214, 9598565129627827101, 17840020483912858162, 17804260467567126634⟩, ⟨17940331542498648891, 1849273061845550926, 17842145155774397884, 4828466181404282771⟩, ⟨12445356357748464124, 4463595226541430579, 885897034798139116, 9630556606744936257⟩, ⟨2895468085989489289, 15363098360061059806, 6538544547849354930, 15548316194194385825⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7020090544996768690, 3266266181032701339, 4243327185017280782, 14597983575996429021⟩, ⟨16118696365122678453, 16276811162814224346, 15965368946752106675, 17046836751645031628⟩, ⟨3361761431950142568, 8836282997877098981, 7972744448457215867, 11200149252421439886⟩, ⟨905383808674037154, 16477963904690097104, 14320425177408966263, 14971917523324427434⟩, ⟨12286559198749906703, 2729884888009338744, 17509543211589571796, 13151837648682227408⟩, ⟨7835989898851314676, 5671447299383941663, 13379159362086557112, 1346913481707240380⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨17632524518736410094, 14638229984543008978, 1411874104130284882, 14423665899252270760⟩, ⟨11194326238589645016, 13546525436733716681, 5754936155969360251, 14011615813331856892⟩, ⟨17402313496593116960, 4510890722053775292, 16686682072981696602, 6449987107193303241⟩, ⟨2476852957065382610, 8475567426184015084, 3002735661005652575, 6466030875787085637⟩, ⟨17154473467150345718, 2137255131480905044, 7449885195185624378, 8680710440936939812⟩, ⟨15578865300675859775, 1308544398757203942, 17267604408082744749, 5264451983973043946⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7749420849415353091, 6161176415168468253, 12793438708300613360, 12324121888805373673⟩, ⟨7290580061684282119, 5353168654804498640, 9660206796913728418, 2822643151964252955⟩, ⟨5409785664794311635, 2612838972687706125, 12708407727716163197, 10822111415561375462⟩, ⟨9709927480932940601, 9121529511518135538, 423636859290453782, 9768368747693364701⟩, ⟨124234811940517187, 10994268167694257827, 2924679409177484677, 15779116490068281964⟩, ⟨9654883994393275058, 12503790538309765566, 16253386343289927665, 6226275455551858822⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨17972159749517178631, 4017906732686397870, 4996863664704572016, 10259729733910255667⟩, ⟨841138602748433606, 9720452516731570573, 11835442708123889857, 12485195418498859848⟩, ⟨7779764842850199020, 2660720826645662061, 11307574474259805489, 11652378203615810105⟩, ⟨16644848508672966748, 4984868931267843240, 301996574973459413, 17305490354086206126⟩, ⟨10499352713176562613, 6838761064149885950, 18094487593727322981, 11360241667324465319⟩, ⟨3529782861657181353, 1602940047133238315, 18075589554065017502, 346679698890498694⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨11189909605336753692, 7038324751215064411, 13014145347937810573, 7165848815340520567⟩, ⟨9749526840516135389, 10973705730917121141, 12819703290201455545, 8862929817628571010⟩, ⟨2706138154966587767, 1635419071478534280, 220911043369600115, 12285609882158374⟩, ⟨2087123502612741237, 497875649669734234, 5112654899553878823, 9718032464768821155⟩, ⟨14033228806134782675, 5971607648713622725, 4260042482514865524, 16742978971501636879⟩, ⟨11558858728897616843, 13950652021763063745, 14398996661575075969, 20177558739218371⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨13226117377573632478, 377613980749051767, 920835855995024181, 3555940421481485303⟩, ⟨15995271745419317505, 2897884299476666723, 16188169058274294055, 7164475475325002366⟩, ⟨7683579815794703754, 6178202000917907974, 14212023087696324631, 5919753748864162332⟩, ⟨6570342545659062581, 3496102641161134510, 2099188803802896702, 18181872954037100646⟩, ⟨12191390356749312189, 942722695106522941, 1131320307935136735, 12555614673169916081⟩, ⟨3009373285203066578, 7293127551667742834, 666330714669074348, 8939572963406065713⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨5407176885451670238, 3971362932838765100, 5435420664079761695, 17817510638015654545⟩, ⟨2428714429542163126, 13066409604887212259, 5106324873258762105, 951577637525256732⟩, ⟨9414529694838824832, 17240215286834487392, 12132406503261701931, 14889533021008284013⟩, ⟨11978855858617909212, 8956769282379233197, 7782957011026908945, 17376994989239081889⟩, ⟨8383391671313466909, 7722406983734283680, 13080320671903071055, 3889303039948792251⟩, ⟨13427700398648200346, 9207485580635998031, 4181188267690701516, 13961849186507708102⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12841760621666550686, 12132023191436095754, 584757517342269723, 5643726533001611550⟩, ⟨9143631625520051341, 14309029173232299267, 5542359578146459125, 13721396851970008539⟩, ⟨14182096686018928285, 12883941098140450287, 3400038535873803149, 18031872434633510820⟩, ⟨6687846386678249900, 4513686818328291097, 14196990694231994718, 5798596607020589716⟩, ⟨6226264136291296434, 17401201879491736499, 13111212477045273553, 14072048050717755128⟩, ⟨11834103483129236504, 7416090678653837925, 9492204403664363020, 7538257730162060865⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7153414278850624820, 7020418305546732785, 14504654218209760798, 17463301246117083231⟩, ⟨12697215910027294796, 2471933052852413451, 6223204990066070142, 6060822377705720440⟩, ⟨2415852121904194053, 9656871882269901365, 1714182956526923145, 12781698764241395711⟩, ⟨4113695525544866049, 17758789502792065022, 8361548673071807303, 16809991123757875146⟩, ⟨14568949451424180404, 3889654205536526954, 9052679729530431487, 10207321287811319488⟩, ⟨3201330726895399438, 12391673175773242676, 7836368724651760773, 1657324099704171670⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7503043328687441838, 15434484111197079825, 529886103240699994, 4480294512460342680⟩, ⟨17758072738795783803, 11071506512459793614, 4642440724204164053, 8925072521110184459⟩, ⟨4048488229339252367, 8709562365190797466, 632024215534949872, 18132055173899271515⟩, ⟨3100462399070980695, 12904003540242699449, 13460065873544189343, 13419681094932826574⟩, ⟨2013173623751597832, 5235784607340072485, 11332797864058931421, 3984748883657526657⟩, ⟨13795564516047282357, 9684690817385628831, 8040217797204061204, 6053585775063663648⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6500176889699705383, 9136853970580833986, 13208886135279738470, 11623547909225124881⟩, ⟨6639743283847934338, 4825777434009193096, 13133264548014913610, 11504689127998029907⟩, ⟨13846773340614280470, 9741047018477786937, 3704119033230155168, 3502334101165958595⟩, ⟨16216147347549795418, 17025855890111201921, 2372703042412365400, 13461609955798404899⟩, ⟨14265624794602565562, 16642705387105760521, 564562251655103269, 6384052707799965823⟩, ⟨3408950284345967124, 10983247389706295107, 10971658439313885983, 13027318514853182728⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨7020265538324662599, 17155765379881136219, 15989939610445194852, 17619614907371633115⟩, ⟨5796625471840023974, 11444374075789054485, 4008263349242098370, 6449252824590843441⟩, ⟨9518468344128107577, 11416498768644874770, 4513217273437563186, 15740681536812545239⟩, ⟨14549354245029540497, 17232054917654637269, 2333985688425784699, 13764333289596025573⟩, ⟨5070717911187359388, 3722568496294658722, 16431897925098265070, 5169735424207652662⟩, ⟨11606193147466116897, 14142682817042211540, 10837900302212456756, 13416087384663963396⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨14936754899625277349, 10058137316044145778, 6435507087638814942, 8040599357405789056⟩, ⟨2381887572054032709, 9991660524056622430, 10486334695422651473, 18272927252270719042⟩, ⟨12227955472612798550, 940493741746627961, 16273351328786904987, 7352693033277222062⟩, ⟨16934937721522853321, 16603249138772235558, 2086275606681907211, 14739484153567257687⟩, ⟨363052506394456296, 15407771164453953647, 5023385916169866244, 17972355884625294622⟩, ⟨8569325070972488588, 1081139156372606921, 4213685880152672025, 13183254845944530999⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨963537591933071375, 15071429829131487441, 17884306688364971547, 282201803881329245⟩, ⟨5621649020105019014, 17305908342676625975, 8534609517149671021, 12335760285294548128⟩, ⟨2218347107285888778, 5972017497834503506, 17487597546005166236, 7899378267812330183⟩, ⟨7886895692472419591, 17223125062006380025, 14098054173366132929, 10395051852713939260⟩, ⟨3367897274224361946, 12380710482462404236, 10616027115037505778, 14945495102655979189⟩, ⟨2564276268099865852, 16928539202482689104, 16505214087056782623, 7029985091367765834⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15569964008072765139, 2619819551711198760, 4870259029895070092, 7123941007519612620⟩, ⟨14074837814005279110, 6188506233601546425, 2401477299565003497, 2273797066018250029⟩, ⟨13242402483369294409, 3751855476216694533, 12974203680566012787, 15284577628232470434⟩, ⟨17456451237748337133, 11566066328756434536, 2190303402642816227, 18183439821732680008⟩, ⟨16829992337843133946, 8199419247626946951, 13549255976441712305, 10783909616268048308⟩, ⟨8116660330142210215, 6821776291662136948, 16987781836401152911, 16120691415442936183⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨15995733287728342970, 15849776508739139916, 4523730947403497019, 4832232848277222994⟩, ⟨15148195052582668110, 1565592278165178030, 16290254265449715776, 11179016626879268444⟩, ⟨11157020442155867976, 14474267258943356912, 15194376417576132540, 3351733334095577043⟩, ⟨14252085340157975442, 16598869286731264284, 7513451866587928407, 15791275179720408078⟩, ⟨14558184182428223068, 16715027389782051162, 17917506374866846483, 5350510212650984579⟩, ⟨1451753305680131586, 14838733772334420071, 16870141823347999501, 10622857250955578647⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6843526631318338610, 12499013469765322579, 5696698855833176701, 15978168354135074639⟩, ⟨7154332965200021617, 3251969342254446822, 1428539511808726507, 11130026443545158881⟩, ⟨4348560212054290874, 12712841367608687935, 10090709536466044002, 16176518233198975310⟩, ⟨2170895790687492057, 9365939619541467042, 8508712482282397951, 5316207960647030590⟩, ⟨6426891707889133827, 9681179671270401552, 6610582268183911608, 2613104202808812804⟩, ⟨2379317270691474650, 3278650206645137195, 16502695800631446063, 16893079946225791754⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3848067620369572933, 8358404529498327004, 7252788771399357827, 4431832268029550018⟩, ⟨16200566642504008719, 10997412396974984935, 4679167298783084007, 7204808808868968611⟩, ⟨17519520189659290988, 3719824950590275289, 15661078363678507890, 13884631590601585928⟩, ⟨14635393728216500121, 7967152388661205098, 7432951668837454279, 9531866594429611544⟩, ⟨4216578733975639025, 4334803991555979823, 14529506058369730831, 4053258531982520187⟩, ⟨731657259744180321, 8533001464447068296, 1391429489293500382, 8363037418615055480⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨3827398420183543680, 278871455192022368, 6426044468492411018, 9647795997811895436⟩, ⟨10844535649238259190, 1858368652562195435, 12526612000850293341, 10306373027357662764⟩, ⟨2363018802918238987, 3411706736660368977, 4505663003160139730, 5790282252487758466⟩, ⟨7694453583801005868, 11533136157004697244, 8405108973990889632, 10334202465992954995⟩, ⟨13106085993611286595, 16222932623203416413, 16821055409611629119, 15313420740823291013⟩, ⟨9445684275639460938, 9933645847141846736, 14399433353171405722, 2180223535171432870⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨12979319416233112579, 9933804028169238158, 4060277440547453505, 11352628425395628892⟩, ⟨4177497419810367705, 2495342875143174108, 4678147073065747640, 5180019824942597130⟩, ⟨16973434235878456990, 16054885895546210815, 10711381514145717425, 17499112838360317933⟩, ⟨14376436917382223320, 7269069893466681133, 2612036381701810841, 2564322245082371411⟩, ⟨11232091186678783549, 17672886122507917323, 5731660687896471117, 5917461160180344605⟩, ⟨319331787122909311, 16883021404048399224, 10453425213517250188, 17745585709737060545⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨16429453021092840228, 2149569008631041486, 336319861556710338, 732790543215150254⟩, ⟨7189000269530160647, 13694506913338004735, 12789262832663637561, 10142384596740086191⟩, ⟨6546291051397932491, 7089370830254052706, 16206855676352165912, 17965564129280575350⟩, ⟨12601781062993170693, 11727864654263214323, 10241427430192984761, 2835182353026502235⟩, ⟨14388841180469348689, 5207547395240305150, 8793222037777578027, 13998598154907799237⟩, ⟨9837342138985935821, 4345048091128656504, 8009145706087642368, 11523146593297991170⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6890638299304747422, 16368031494669221938, 14891102209151601128, 17149624658898781468⟩, ⟨16390232434035712665, 11969644266471244360, 17646503604153727342, 17695034247893245441⟩, ⟨3593489871902660534, 2869732159031825409, 11093737541784182946, 1105549593592186494⟩, ⟨15671126385048294637, 16230529592586475576, 16199942929439850656, 16944567686327478414⟩, ⟨8987849868880776844, 12832528715451968031, 6847941045516959316, 15041965854073219408⟩, ⟨15692483243069255226, 2941449238808243608, 4043031188870794653, 17800808247798396872⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨10084263385059736136, 12881816712081578859, 7849245566300974856, 9772051644763729830⟩, ⟨16955180273210552315, 3560652786806423471, 7799578467894102235, 3744588848290421564⟩, ⟨13758631155002881569, 11742199222390873106, 13356977300636638726, 3345180821521683196⟩, ⟨12092685084357639278, 13144114350869007654, 569427820149325599, 11259257386739245168⟩, ⟨8109220498869296348, 2053556466690042147, 6616317710874516776, 45101395310975034⟩, ⟨186160120587029762, 15535667622348803608, 4460266332037765058, 168168006514907374⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2846989294079253099, 9924378332012336618, 12741052752532707471, 17684024129571092758⟩, ⟨3556795319713086032, 17119518070004364653, 6821399690152433106, 15335319077542726003⟩, ⟨5706662865914088096, 14673023306831612893, 10519633862493586701, 9860070016436251078⟩, ⟨7331073230003840321, 7735748227629059865, 13215758790730815875, 1274891809880380271⟩, ⟨13078292721360929339, 9921176239140281856, 11152114115570107100, 14186529594836105215⟩, ⟨15283736749439559125, 5567633619608944867, 7645817021482270142, 15078720985943057699⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨16639883943679029468, 5227658261161591690, 2338641364800085693, 10699144239189873141⟩, ⟨5310898417439359007, 10961152077414909026, 10673885250466686933, 17533009282325334572⟩, ⟨6333108058983742841, 6908200386881538517, 13353293326221608573, 1645970790092735357⟩, ⟨12138326542957179507, 7868453112937182955, 13305094271212107444, 1416406431990163764⟩, ⟨8487696913873474273, 15567817640221991922, 5204575522565470232, 8419506526086453790⟩, ⟨12366601164855168203, 1390274462232451421, 9307546414641916468, 17667284729240100105⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨9609814856451122838, 18358117129123001287, 17807741597561580983, 586803616477149198⟩, ⟨277413999232528690, 4041451412454110803, 4206649564018289354, 9991664702493178624⟩, ⟨12111551363638783121, 10742327245835175133, 6274592140614215882, 1504093536780657633⟩, ⟨6212213273405375225, 15852520191383984490, 6652022466766838056, 13529401271257443155⟩, ⟨16422598110278579544, 13106337274594383921, 8210921548532883400, 1768071889704312028⟩, ⟨12116460616291078981, 12274651027172916105, 4258943227625179867, 3260061876066346121⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨14739368881923259287, 10820407730896667273, 9631029727482243631, 13256249137096847099⟩, ⟨13128346665048479827, 1785280992795685871, 16394612233871419388, 4739533201241231008⟩, ⟨11661107386127406831, 12379943262220020526, 13766742587529110037, 1574314503756583535⟩, ⟨5268410709333529617, 10292614240651911427, 12595101374443520825, 2095980798077116370⟩, ⟨18185919317428935887, 12084558337443158240, 12875746187602799325, 7455001207514868893⟩, ⟨2110700318587833744, 13304718692703922494, 6992741702472641385, 15541125551531835199⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨13526527537382719602, 7116985988777270447, 15558637712845090436, 12428086667438822928⟩, ⟨9089631231195520185, 6414330073196992789, 4415335798157662602, 4478798026686038550⟩, ⟨13178798129021931862, 11168817516311938939, 16659292625828315817, 3527896065553307087⟩, ⟨13103174434832015326, 4034309355784634681, 2727457463433094221, 7455260772813787873⟩, ⟨8880353400519842806, 14295392825764950642, 8826201199917954247, 13619663185194138705⟩, ⟨9415229924559744977, 9165961757210464233, 9049610817633761472, 11754936149813882588⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨9295275806800265291, 14242518431001280370, 1349319729085022153, 1497646903735548672⟩, ⟨6055606014129834119, 17521093266302972942, 842325427952538619, 17067445108911712308⟩, ⟨15357982640304115048, 7097485858819808552, 14287596796783751925, 4129265963551940095⟩, ⟨2414153979971210516, 3373967540620111683, 11450004825070255624, 18225550629361731814⟩, ⟨1158065661365413156, 15198708415535373408, 5861638822081965513, 8137148989969116856⟩, ⟨5819476887277964662, 18259038497586327427, 423971468892237805, 7819240676584839752⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨2449764744287542481, 7724368726813451223, 14627233823396799480, 17919181980168949862⟩, ⟨5033210270021675163, 15564925584855557431, 1989519920878822340, 15887181240115867947⟩, ⟨3948756896792958971, 2657311351053896707, 3820758760917765337, 15992549146473602945⟩, ⟨12388534743157293914, 15088332753680552313, 8674528367599554697, 3457110144549807402⟩, ⟨14471635201285102685, 5643798712148840825, 1761791175173505460, 9016210004523311282⟩, ⟨2357790382516772430, 15130129632540577300, 11478378876559714334, 2561785369619465092⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨11122095525565186915, 6050811279017883739, 9134166129583447155, 14662938264636479001⟩, ⟨1698636573548665178, 7557579007503755239, 6650847812082994433, 535118101817843469⟩, ⟨5705235467509404137, 14515361923076953952, 17646800853568931355, 12434778970437555469⟩, ⟨5772501093288927013, 3544769088889231214, 3204674542777705848, 8114757753475041414⟩, ⟨12865669891144658970, 13100250176221103666, 3477093962145555358, 17704486428671844357⟩, ⟨6316931895663693504, 3792601546171249908, 9338235642575563544, 8570338207213203762⟩⟩) (by decide +kernel) ?_
    rfl
  have hTerm : runRounds extRound24Nat termExtNatConsts ⟨⟨11122095525565186915, 6050811279017883739, 9134166129583447155, 14662938264636479001⟩, ⟨1698636573548665178, 7557579007503755239, 6650847812082994433, 535118101817843469⟩, ⟨5705235467509404137, 14515361923076953952, 17646800853568931355, 12434778970437555469⟩, ⟨5772501093288927013, 3544769088889231214, 3204674542777705848, 8114757753475041414⟩, ⟨12865669891144658970, 13100250176221103666, 3477093962145555358, 17704486428671844357⟩, ⟨6316931895663693504, 3792601546171249908, 9338235642575563544, 8570338207213203762⟩⟩ = ⟨⟨1170443848852734242, 833485916214918700, 373819593114229842, 2500389336842599919⟩, ⟨2668122737528357646, 15131165148025152804, 573418327208874834, 11542618087740092325⟩, ⟨11689289631835769111, 12304969562289533240, 15835240181100103881, 11172752928363632645⟩, ⟨5443232731664037725, 8930854513653823679, 6656347969346280873, 5643972817548579632⟩, ⟨13107671858976799679, 4364933070422677448, 8993198673880906353, 2148388791134660717⟩, ⟨650075810295284558, 18350876254755807787, 14195893604467810598, 10050238888845265849⟩⟩ := by
    unfold termExtNatConsts
    refine runRounds_cons (s' := ⟨⟨2220342271196391166, 5303164949044623310, 12723506108558409478, 2078358632819419304⟩, ⟨3434242796434796514, 2296355746594218753, 14117298681208346956, 15591347440006528200⟩, ⟨8168630793286636449, 5745290370293596278, 323862484880539771, 4299639151271233093⟩, ⟨5278459798027787773, 8309553290954959297, 6251935979541983001, 14215036992196885191⟩, ⟨14130288791268731517, 4333826769184862785, 16511665294313087298, 13354878827107962621⟩, ⟨11510236335829462164, 13287205911828376982, 7180609772670235457, 15260128075407714471⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨11863804281629628985, 17722747781430112523, 12855411229160809476, 3771626956104609592⟩, ⟨5009926523210266543, 2954388200674546330, 17405920365527518061, 10684264794707340718⟩, ⟨15031601700719834075, 5311207657981096273, 3298627968035943307, 10350479555349874684⟩, ⟨9231227307109012430, 9256772058984573167, 15616696023164089044, 13531495017773304941⟩, ⟨3730445996317828127, 11728751609397056081, 3230717786258336020, 14137993040698878830⟩, ⟨5336299745459711111, 5434105814212786485, 5172327309517890615, 2301199275209099774⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨6633273470836574167, 11644624251906138415, 16475193922328351846, 4366699298228243340⟩, ⟨11846964531274906310, 10201919561937085611, 17357411642314568114, 10442807506358900739⟩, ⟨11934396652558489331, 15140373060754492280, 7540636927943417570, 12278981177753079192⟩, ⟨16795932043686196565, 15795749320313741769, 16462952128744693809, 3408237316120272660⟩, ⟨1485805856098688494, 14679475984614890190, 2666933682899163400, 14476389627233427397⟩, ⟨12057270779716972280, 5545649611900351638, 1005223641610924442, 9364417092340260238⟩⟩) (by decide +kernel) ?_
    refine runRounds_cons (s' := ⟨⟨1170443848852734242, 833485916214918700, 373819593114229842, 2500389336842599919⟩, ⟨2668122737528357646, 15131165148025152804, 573418327208874834, 11542618087740092325⟩, ⟨11689289631835769111, 12304969562289533240, 15835240181100103881, 11172752928363632645⟩, ⟨5443232731664037725, 8930854513653823679, 6656347969346280873, 5643972817548579632⟩, ⟨13107671858976799679, 4364933070422677448, 8993198673880906353, 2148388791134660717⟩, ⟨650075810295284558, 18350876254755807787, 14195893604467810598, 10050238888845265849⟩⟩) (by decide +kernel) ?_
    rfl
  rw [hme, hInit, hInt, hTerm]

theorem poseidon2Gl24Perm_seq_kat :
    (poseidon2Gl24Perm seqState24).toList.map Goldilocks.val =
      [9262813872168818283, 14473920968081642809, 3132432025506878070, 739327372316014541,
       13930273445042610257, 9887230855574303117, 10411529172945029295, 2610146355123527807,
       15800955794096892263, 126337761019280528, 15741922631823646152, 12261346758669164007,
       2093389069744887410, 3165987204040455923, 14526830091420603371, 2537012170462392522,
       17818886402825694850, 14929111493621950133, 16221575831479706027, 10965213893411960579,
       16472025002487739980, 12534132784495569014, 13110610053613593246, 5468252370409873572] := by
  rw [state24ToList_val, toState24Nat_poseidon2Gl24Perm, perm24Nat_seq_eval]
  decide +kernel

theorem poseidon2Gl24CompressMerkle_kat :
    (poseidon2Gl24CompressMerkle
      ⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4,
       Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩
      ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11,
       Goldilocks.ofNat 12, Goldilocks.ofNat 13, Goldilocks.ofNat 14⟩
      (Goldilocks.ofNat 100) (Goldilocks.ofNat 200)).toList.map Goldilocks.val =
      [1170443848852734659, 833485916214919520, 373819593114229865, 2500389336842599945,
       2668122737528357675, 15131165148025152836, 573418327208874869] := by
  rw [compressMerkle_val_eq, perm24Nat_merkle_eval]
  decide +kernel

theorem witness_mi_nonzero_sum_branch_25 :
    ∃ st : Poseidon2State24, state24Sum st ≠ Goldilocks.zero ∧
      25 ≤ stateWeight24 st + stateWeight24 (applyMI24 st) :=
  ⟨⟨⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩,
    lane4Zero, lane4Zero, lane4Zero, lane4Zero, lane4Zero⟩,
   by decide +kernel,
   poseidon2_gl24_mi_nonzero_sum_branch_25 _ (by decide +kernel)⟩

#verify_constructive
  applyME24Inv_applyME24
  applyME24_applyME24Inv
  poseidon2_gl24_kronecker_swap_kills_subspace_skip
  tooth_poseidon2_gl24_me_std_admits_subspace_skip
  applyMI24Inv_applyMI24
  applyMI24_applyMI24Inv
  poseidon2_gl24_mi_nonzero_sum_branch_25
  tooth_poseidon2_gl24_mi_zero_sum_weight_four
  poseidon2Gl24PermInv_left_inv
  poseidon2Gl24PermInv_right_inv
  poseidon2Gl24Perm_seq_kat
  poseidon2Gl24CompressMerkle_kat

#verify_inhabited poseidon2_gl24_mi_nonzero_sum_branch_25 witness_mi_nonzero_sum_branch_25

#tooth_pair poseidon2_gl24_kronecker_swap_kills_subspace_skip vs tooth_poseidon2_gl24_me_std_admits_subspace_skip
#tooth_pair poseidon2_gl24_mi_nonzero_sum_branch_25 vs tooth_poseidon2_gl24_mi_zero_sum_weight_four

end Qsag.Poseidon2Gl24
end
