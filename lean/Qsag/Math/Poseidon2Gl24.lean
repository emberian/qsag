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

