module
/-
# Qsag.Protocol.Migration.HdToprfAndMigrationSecurity — HD batch isolation, 2-of-5 Shamir decoding, 3-party co-ZK

Information-theoretic cores of three custody/credential/migration arguments, each stated over the
specified parameters and proved constructively.

1. **`qsag-hd` (`q = 8380417`).** A child secret is `master + known + hidden`, where `known` is the
   part of the per-child PRF offset a coalition below threshold can compute and `hidden` is the
   component keyed by the subset seed it does not hold (`seeds.rs`: every coalition of at most
   `t - 1` custodians misses one seed). `hidden` is modeled as uniform: that is the PRF-to-random
   hop for the additive model. Inventory uses XOR instead; the production sections below
   distinguish its PRF hop from the MLWE public-image hop for short hardened tweaks.
   - `hd_watch_only_subspace_isolation`: for every enrolled batch, every candidate master and
     every candidate assignment of the un-enrolled children there is exactly one custody state
     consistent with the watch-only view.
   - `hd_unenrolled_fiber_card_exact`: the fiber over a view and a master candidate, with every
     other child revealed, is in bijection with `Fin (8380417 ^ k)`.
   - `hd_child_mac_unforgeable_below_threshold`: a forged opening passes the lane MACs for exactly
     one key vector, and the Shamir sharing of a key is shift-invariant on any corrupt set of
     fewer than `t` points. `hd_child_mac_six_limb_bound` is `2^137 < q^6`.
   - `master_secret_recoverable` and `tooth_unkeyed_public_tweak_pins_master`: with a public
     tweak, one leaked child determines the parent.

2. **Error correction for Shamir shares.** A degree-one polynomial is uniquely determined
   by three correct responses among five distinct points when at most one response is wrong.
   The decoder recovers the shared value at zero. The credential service uses a separate
   Shamir-SPDZ arithmetic model in `ToprfSpdzArithmeticRefinement`.

3. **`qsag-migrate` co-ZK (`zk_engine.rs`).** One ZKBoo repetition over any commutative ring, with
   the production multiplication gate `a_p b_p + a_p b_{p+1} + a_{p+1} b_p + (r_p - r_{p+1})`.
   - `cozk_opened_pair_uniform`: for every opened pair and every witness, the prover randomness
     and the opened view are in bijection. The view is the information-theoretic part of an
     opening; the commitment to the unopened party is assumed hiding.
   - `cozk_false_statement_caught_at_least_one_pair`: if no witness satisfies the circuit, at most
     two of the three pair openings of any committed repetition verify.
   - `cozk_corrupted_mul_wire_fails_owner_pair`, `cozk_preopen_sacrifice_sound`: a faulted product
     fails the pair that owns it, and passes the pre-open sacrifice for one challenge only.
   - `cozk_3party_active_soundness_and_2privacy`: over 438 repetitions the accepting challenge
     vectors number fewer than `3^438 / 2^256`. `cozk_438_grover_query_floor` is the arithmetic
     `Q^2 (2/3)^438 < 1` for `Q <= 2^128`; neither is a Fiat-Shamir or QROM extraction theorem.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Math.Lattices
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Tactic.MaskBijection
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf

public section
namespace Qsag

set_option autoImplicit false

-- `Fin.instLinearOrderPackage` supplies a `BEq (Fin n)` whose package proofs use `Classical.choice`;
-- without it `==` on `Fin` resolves to `instBEqOfDecidableEq`.
attribute [-instance] Fin.instLinearOrderPackage

open CommRingOps

/-! ## §0. Ring identities used below -/

namespace CustodyAlgebra
variable {R : Type} [LawfulCommRing R]

theorem add_left_comm (a b c : R) : add a (add b c) = add b (add a c) := by
  rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_comm a b, LawfulCommRing.add_assoc]

theorem mul_left_comm (a b c : R) : mul a (mul b c) = mul b (mul a c) := by
  rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm a b, LawfulCommRing.mul_assoc]

theorem add_sub_cancel (a b : R) : sub (add a b) a = b := by
  apply LawfulCommRing.add_left_cancel (a := a)
  rw [LawfulCommRing.add_sub_cancel_left]

theorem sub_sub_self (a b : R) : sub a (sub a b) = b := by
  apply LawfulCommRing.add_left_cancel (a := sub a b)
  rw [LawfulCommRing.add_sub_cancel_left, ring_sub_add_cancel_right]

theorem add_sub_add_left (a u v : R) : sub (add a u) (add a v) = sub u v := by
  apply LawfulCommRing.add_left_cancel (a := add a v)
  rw [LawfulCommRing.add_sub_cancel_left, LawfulCommRing.add_assoc,
    LawfulCommRing.add_sub_cancel_left]

theorem add_right_cancel {a b c : R} (h : add b a = add c a) : b = c := by
  rw [LawfulCommRing.add_comm b a, LawfulCommRing.add_comm c a] at h
  exact LawfulCommRing.add_left_cancel h

theorem eq_sub_of_add_eq {a b x : R} (h : add a b = x) : a = sub x b := by
  rw [← h, ring_add_sub_cancel_right]

theorem sub_add_sub_cancel (a b c : R) : add (sub a b) (sub b c) = sub a c := by
  apply add_right_cancel (a := c)
  rw [LawfulCommRing.add_assoc, ring_sub_add_cancel_right, ring_sub_add_cancel_right,
    ring_sub_add_cancel_right]

theorem telescope3 (r0 r1 r2 : R) : add (add (sub r0 r1) (sub r1 r2)) (sub r2 r0) = zero := by
  rw [sub_add_sub_cancel, sub_add_sub_cancel, LawfulCommRing.sub_self]

end CustodyAlgebra

open CustodyAlgebra

/-! ## §1. `qsag-hd`: watch-only batch isolation and child-MAC unforgeability -/

/-- Secret state of the HD family as seen against a coalition below threshold. `known` is the
part of each child's PRF offset the coalition can compute; `hidden` is the component keyed by the
subset seed it misses. -/
structure HdCustodyState (R : Type) (Idx : Type) (k : Nat) where
  master : Fin k → R
  known : Idx → Fin k → R
  hidden : Idx → Fin k → R

section HdGeneric
variable {R : Type} [LawfulCommRing R] {Idx : Type} {k : Nat}

/-- Child secret, limb by limb. -/
def hdChildSecret (s : HdCustodyState R Idx k) : Idx → Fin k → R :=
  fun i l => add (add (s.master l) (s.known i l)) (s.hidden i l)

/-- The state with a given master, coalition-known offsets and child secrets. -/
def hdStateOfChildren (m : Fin k → R) (kn c : Idx → Fin k → R) : HdCustodyState R Idx k :=
  { master := m, known := kn, hidden := fun i l => sub (c i l) (add (m l) (kn i l)) }

theorem hdChildSecret_stateOfChildren (m : Fin k → R) (kn c : Idx → Fin k → R) :
    hdChildSecret (hdStateOfChildren m kn c) = c := by
  funext i l
  exact LawfulCommRing.add_sub_cancel_left _ _

theorem hdStateOfChildren_childSecret (s : HdCustodyState R Idx k) :
    hdStateOfChildren s.master s.known (hdChildSecret s) = s := by
  cases s with
  | mk m kn h =>
    have e : (fun (i : Idx) (l : Fin k) =>
        sub (add (add (m l) (kn i l)) (h i l)) (add (m l) (kn i l))) = h :=
      funext fun i => funext fun l => add_sub_cancel _ _
    exact congrArg (HdCustodyState.mk m kn) e

/-- The map from custody states to (master, coalition view, all child secrets) is a bijection. -/
theorem hd_state_unique_of_children (m : Fin k → R) (kn c : Idx → Fin k → R) :
    ∃ s : HdCustodyState R Idx k,
      (s.master = m ∧ s.known = kn ∧ hdChildSecret s = c) ∧
      ∀ s' : HdCustodyState R Idx k,
        s'.master = m → s'.known = kn → hdChildSecret s' = c → s' = s :=
  ⟨hdStateOfChildren m kn c, ⟨rfl, rfl, hdChildSecret_stateOfChildren m kn c⟩,
    fun s' hm hk hc =>
      calc s' = hdStateOfChildren s'.master s'.known (hdChildSecret s') :=
            (hdStateOfChildren_childSecret s').symm
        _ = hdStateOfChildren m kn c := by rw [hm, hk, hc]⟩

end HdGeneric

/-- **Watch-only batch isolation.** Fix the coalition's own view and the child secrets of an
enrolled batch. Every candidate master and every candidate assignment of the un-enrolled children
is consistent with that view through exactly one custody state, so both are uniform given the
view. -/
theorem hd_watch_only_subspace_isolation {Idx : Type} {k : Nat} (enrolled : Idx → Bool)
    (corruptKnown watchView : Idx → Fin k → Fq204)
    (masterCandidate : Fin k → Fq204) (unenrolledCandidate : Idx → Fin k → Fq204) :
    ∃ s : HdCustodyState Fq204 Idx k,
      (s.master = masterCandidate ∧ s.known = corruptKnown ∧
        (∀ i, enrolled i = true → hdChildSecret s i = watchView i) ∧
        (∀ i, enrolled i = false → hdChildSecret s i = unenrolledCandidate i)) ∧
      ∀ s' : HdCustodyState Fq204 Idx k,
        s'.master = masterCandidate → s'.known = corruptKnown →
        (∀ i, enrolled i = true → hdChildSecret s' i = watchView i) →
        (∀ i, enrolled i = false → hdChildSecret s' i = unenrolledCandidate i) → s' = s := by
  obtain ⟨s, ⟨hm, hk, hc⟩, huniq⟩ := hd_state_unique_of_children masterCandidate corruptKnown
    (fun i => if enrolled i = true then watchView i else unenrolledCandidate i)
  refine ⟨s, ⟨hm, hk, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [congrFun hc i, ite_eq_left hi]
  · intro i hi
    rw [congrFun hc i, ite_eq_right (by rw [hi]; exact Bool.false_ne_true)]
  · intro s' hm' hk' hen hun
    refine huniq s' hm' hk' (funext fun i => ?_)
    cases hi : enrolled i with
    | true => rw [hen i hi, ite_eq_left rfl]
    | false => rw [hun i hi, ite_eq_right Bool.false_ne_true]

/-! ### Exact fiber cardinality -/

/-- `Fin a × Fin b` and `Fin (a * b)`. -/
def finProdEquiv (a b : Nat) : SimpleEquiv (Fin a × Fin b) (Fin (a * b)) where
  toFun x := ⟨x.1.val * b + x.2.val, by
    have h1 := x.1.isLt
    have h2 := x.2.isLt
    calc x.1.val * b + x.2.val < x.1.val * b + b := by omega
      _ = (x.1.val + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ a * b := Nat.mul_le_mul_right b h1⟩
  invFun n :=
    (⟨n.val / b, Nat.lt_of_not_le fun hle =>
        Nat.not_le_of_gt n.isLt
          (Nat.le_trans (Nat.mul_le_mul_right b hle) (Nat.div_mul_le_self n.val b))⟩,
      ⟨n.val % b, Nat.mod_lt _ (by
        rcases Nat.eq_zero_or_pos b with h | h
        · have h0 : a * b = 0 := by rw [h, Nat.mul_zero]
          exact absurd (Nat.lt_of_lt_of_eq n.isLt h0) (Nat.not_lt_zero _)
        · exact h)⟩)
  left_inv x := by
    have h2 := x.2.isLt
    have hb : 0 < b := by omega
    apply Prod.ext
    · apply Fin.ext
      show (x.1.val * b + x.2.val) / b = x.1.val
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt h2, Nat.zero_add]
    · apply Fin.ext
      show (x.1.val * b + x.2.val) % b = x.2.val
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  right_inv n := by
    apply Fin.ext
    show n.val / b * b + n.val % b = n.val
    exact Nat.div_add_mod' n.val b

/-- Vectors of `k` residues modulo `q` and `Fin (q ^ k)`. -/
def finVecEquiv (q : Nat) : (k : Nat) → SimpleEquiv (Fin k → Fin q) (Fin (q ^ k))
  | 0 =>
    { toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      invFun := fun _ i => i.elim0
      left_inv := fun _ => funext fun i => i.elim0
      right_inv := fun b => Fin.ext (by
        have h : b.val < 1 := b.isLt
        show 0 = b.val
        omega) }
  | k + 1 =>
    { toFun := fun f =>
        (finProdEquiv (q ^ k) q).toFun ((finVecEquiv q k).toFun (fun i => f i.succ), f 0)
      invFun := fun n =>
        Fin.cases ((finProdEquiv (q ^ k) q).invFun n).2
          (fun j => (finVecEquiv q k).invFun ((finProdEquiv (q ^ k) q).invFun n).1 j)
      left_inv := fun f => by
        funext i
        simp only [SimpleEquiv.left_inv]
        cases i using Fin.cases with
        | zero => rfl
        | succ j => rfl
      right_inv := fun n => by
        have e : (fun i : Fin k =>
            (Fin.cases ((finProdEquiv (q ^ k) q).invFun n).2
              (fun j => (finVecEquiv q k).invFun ((finProdEquiv (q ^ k) q).invFun n).1 j)
              : Fin (k + 1) → Fin q) i.succ) =
            (finVecEquiv q k).invFun ((finProdEquiv (q ^ k) q).invFun n).1 :=
          funext fun _ => rfl
        show (finProdEquiv (q ^ k) q).toFun ((finVecEquiv q k).toFun _, _) = n
        rw [e, SimpleEquiv.right_inv]
        exact (finProdEquiv (q ^ k) q).right_inv n }

/-- The HD field has exactly `8380417` elements. -/
def hdFieldFinEquiv : SimpleEquiv Fq204 (Fin 8380417) where
  toFun a := ⟨a.val, a.isLt⟩
  invFun n := ⟨n.val, n.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A `k`-limb secret ranges over exactly `8380417 ^ k` values. -/
def hdLimbVecCardEquiv (k : Nat) : SimpleEquiv (Fin k → Fq204) (Fin (8380417 ^ k)) where
  toFun v := (finVecEquiv 8380417 k).toFun (fun l => hdFieldFinEquiv.toFun (v l))
  invFun n := fun l => hdFieldFinEquiv.invFun ((finVecEquiv 8380417 k).invFun n l)
  left_inv v := by
    funext l
    rw [SimpleEquiv.left_inv]
    exact hdFieldFinEquiv.left_inv (v l)
  right_inv n := by
    have e : (fun l => hdFieldFinEquiv.toFun
        (hdFieldFinEquiv.invFun ((finVecEquiv 8380417 k).invFun n l))) =
        (finVecEquiv 8380417 k).invFun n :=
      funext fun _ => hdFieldFinEquiv.right_inv _
    show (finVecEquiv 8380417 k).toFun _ = n
    rw [e]
    exact (finVecEquiv 8380417 k).right_inv n

/-- With every child but `j` revealed, the states consistent with the view and with a fixed
master candidate are indexed by the secret of child `j`. -/
def hdUnenrolledFiberEquiv {Idx : Type} [DecidableEq Idx] {k : Nat} (j : Idx)
    (m : Fin k → Fq204) (kn view : Idx → Fin k → Fq204) :
    SimpleEquiv
      { s : HdCustodyState Fq204 Idx k //
        s.master = m ∧ s.known = kn ∧ ∀ i, i ≠ j → hdChildSecret s i = view i }
      (Fin (8380417 ^ k)) where
  toFun s := (hdLimbVecCardEquiv k).toFun (hdChildSecret s.1 j)
  invFun n :=
    ⟨hdStateOfChildren m kn (fun i => if i = j then (hdLimbVecCardEquiv k).invFun n else view i),
      rfl, rfl, fun i hi => by rw [hdChildSecret_stateOfChildren, ite_eq_right hi]⟩
  left_inv s := by
    obtain ⟨s, hm, hk, hv⟩ := s
    apply Subtype.ext
    have hc : (fun i => if i = j then
        (hdLimbVecCardEquiv k).invFun ((hdLimbVecCardEquiv k).toFun (hdChildSecret s j))
        else view i) = hdChildSecret s := by
      funext i
      refine if h : i = j then ?_ else ?_
      · rw [ite_eq_left h, SimpleEquiv.left_inv, h]
      · rw [ite_eq_right h, hv i h]
    subst hm
    subst hk
    show hdStateOfChildren s.master s.known _ = s
    rw [hc]
    exact hdStateOfChildren_childSecret s
  right_inv n := by
    show (hdLimbVecCardEquiv k).toFun (hdChildSecret (hdStateOfChildren m kn _) j) = n
    rw [hdChildSecret_stateOfChildren, ite_eq_left rfl, SimpleEquiv.right_inv]

/-- **Exact fiber cardinality.** For every master candidate, the fiber over a view that reveals
every child but `j` has exactly `8380417 ^ k` elements, read off by the secret of child `j`. -/
theorem hd_unenrolled_fiber_card_exact {Idx : Type} [DecidableEq Idx] {k : Nat} (j : Idx)
    (m : Fin k → Fq204) (kn view : Idx → Fin k → Fq204) :
    ∃ e : SimpleEquiv
        { s : HdCustodyState Fq204 Idx k //
          s.master = m ∧ s.known = kn ∧ ∀ i, i ≠ j → hdChildSecret s i = view i }
        (Fin (8380417 ^ k)),
      ∀ s, e.toFun s = (hdLimbVecCardEquiv k).toFun (hdChildSecret s.1 j) :=
  ⟨hdUnenrolledFiberEquiv j m kn view, fun _ => rfl⟩

/-! ### Why the tweak must be secret-keyed -/

/-- Unkeyed derivation: the child is the parent plus a tweak any watch-only holder computes. -/
def naiveBip32Child (parent publicTweak : Fq204) : Fq204 := add parent publicTweak

/-- Whether subtracting the public tweak from a leaked child returns the parent. -/
def masterSecretRecoverable (parent publicTweak : Fq204) : Bool :=
  decide (sub (naiveBip32Child parent publicTweak) publicTweak = parent)

theorem master_secret_recoverable (parent publicTweak : Fq204) :
    masterSecretRecoverable parent publicTweak = true :=
  decide_eq_true (ring_add_sub_cancel_right parent publicTweak)

/-- With a public tweak a leaked child is consistent with one master only, in contrast to
`hd_watch_only_subspace_isolation`, where every candidate is consistent. -/
theorem tooth_unkeyed_public_tweak_pins_master :
    ¬ (∀ publicTweak leakedChild masterCandidate : Fq204,
        naiveBip32Child masterCandidate publicTweak = leakedChild) := by
  intro h
  have h1 : add (one : Fq204) zero = zero := h zero zero one
  rw [LawfulCommRing.add_zero] at h1
  exact LawfulField.one_ne_zero h1

/-! ### Child-MAC unforgeability -/

section HdMac
variable {R : Type} [LawfulCommRing R]

/-- SPDZ-style MAC relation `m = α · s`. -/
def hdMacVerify (α s m : R) : Prop := mul α s = m

/-- Opening `s + e` with MAC `α s + d`, `e ≠ 0`, verifies for exactly one key. -/
theorem hd_child_mac_forgery_pins_key (inv : R → R)
    (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one) (α s e d : R) (he : e ≠ zero) :
    hdMacVerify α (add s e) (add (mul α s) d) ↔ α = mul d (inv e) := by
  unfold hdMacVerify
  rw [LawfulCommRing.left_distrib]
  constructor
  · intro h
    have hd : mul α e = d := LawfulCommRing.add_left_cancel h
    rw [← hd, LawfulCommRing.mul_assoc, hInv e he, LawfulCommRing.mul_one]
  · intro h
    subst h
    have hm : mul (mul d (inv e)) e = d := by
      rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (inv e) e, hInv e he,
        LawfulCommRing.mul_one]
    rw [hm]

/-- Across independent lanes the forgery verifies for exactly one key vector. -/
theorem hd_child_mac_lanes_unique_forging_key (inv : R → R)
    (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one) (lanes : Nat) (s e : R) (he : e ≠ zero)
    (d α : Fin lanes → R) :
    (∀ l, hdMacVerify (α l) (add s e) (add (mul (α l) s) (d l))) ↔
      α = fun l => mul (d l) (inv e) :=
  ⟨fun h => funext fun l => (hd_child_mac_forgery_pins_key inv hInv (α l) s e (d l) he).mp (h l),
    fun h l => (hd_child_mac_forgery_pins_key inv hInv (α l) s e (d l) he).mpr (congrFun h l)⟩

end HdMac

/-- **Child-MAC unforgeability below threshold.** For a corrupt set of fewer than `t` nonzero
evaluation points, shifting a degree-`t - 1` sharing by any `δ` at zero leaves every corrupt share
unchanged, so the key is uniform given the corrupt view; and a forged opening verifies on all
lanes for exactly one key vector. The forgery succeeds with probability `q^-lanes`. -/
theorem hd_child_mac_unforgeable_below_threshold
    (t : Nat) (corruptPts : List Fq204) (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero)
    (lanes : Nat) (s e : Fq204) (he : e ≠ zero) (d : Fin lanes → Fq204) :
    (∀ (δ : Fq204) (P : ShamirPadPoly Fq204 t),
      RoundPoly.evalCoeffs ((shamir_rebalanceEquiv Fq204.inv t corruptPts δ hCard).toFun P).1 zero =
          add δ (RoundPoly.evalCoeffs P.1 zero) ∧
        ∀ xc ∈ corruptPts,
          RoundPoly.evalCoeffs ((shamir_rebalanceEquiv Fq204.inv t corruptPts δ hCard).toFun P).1 xc =
            RoundPoly.evalCoeffs P.1 xc) ∧
    (∀ α : Fin lanes → Fq204,
      (∀ l, hdMacVerify (α l) (add s e) (add (mul (α l) s) (d l))) ↔
        α = fun l => mul (d l) (Fq204.inv e)) := by
  have hInv : ∀ x : Fq204, x ≠ zero → mul x (Fq204.inv x) = one :=
    fun _ hx => Fq204.mul_inv_cancel hx
  refine ⟨fun δ P => ?_, fun α => hd_child_mac_lanes_unique_forging_key Fq204.inv hInv lanes s e he d α⟩
  have h := pad_bijection_masked_openings_uniform Fq204.inv hInv t corruptPts δ hCard hNonZero P
  simp only [LawfulCommRing.zero_add] at h
  exact h

theorem hd_child_mac_six_limb_bound : 2 ^ 137 < 8380417 ^ 6 := by decide +kernel


/-! ## §2. Unique decoding of two-of-five Shamir shares -/

section ShamirLines
variable {F : Type} [LawfulCommRing F]

/-- A sharing polynomial of degree at most one, as `(f 0, slope)`, evaluated at `x`. -/
def lineAt (l : F × F) (x : F) : F := add l.1 (mul l.2 x)

theorem lineAt_zero (l : F × F) : lineAt l zero = l.1 := by
  unfold lineAt
  rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem lineAt_diff (l : F × F) (x y : F) :
    sub (lineAt l x) (lineAt l y) = mul l.2 (sub x y) := by
  unfold lineAt
  rw [add_sub_add_left, LawfulCommRing.mul_sub]

/-- Two polynomials of degree at most one that agree at two distinct points are equal. -/
theorem line_unique_of_two_points [NoZeroDivisors F] {l l' : F × F} {x y : F} (hxy : x ≠ y)
    (hx : lineAt l x = lineAt l' x) (hy : lineAt l y = lineAt l' y) : l = l' := by
  have hb : mul l.2 (sub x y) = mul l'.2 (sub x y) := by
    rw [← lineAt_diff l x y, ← lineAt_diff l' x y, hx, hy]
  have h0 : mul (sub l.2 l'.2) (sub x y) = zero := by
    rw [LawfulCommRing.sub_mul, hb, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h | h
  · have hb2 : l.2 = l'.2 := LawfulCommRing.sub_eq_zero_iff.mp h
    have ha : l.1 = l'.1 := by
      unfold lineAt at hx
      rw [hb2] at hx
      exact add_right_cancel hx
    exact Prod.ext ha hb2
  · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp h) hxy

/-- The line through `(x, vx)` and `(y, vy)`. -/
def lineThrough (inv : F → F) (x y vx vy : F) : F × F :=
  (sub vx (mul (mul (sub vy vx) (inv (sub y x))) x), mul (sub vy vx) (inv (sub y x)))

theorem lineThrough_of_on_line (inv : F → F) (hInv : ∀ x : F, x ≠ zero → mul x (inv x) = one)
    (l : F × F) {x y : F} (hxy : x ≠ y) :
    lineThrough inv x y (lineAt l x) (lineAt l y) = l := by
  have hne : sub y x ≠ zero := fun h => hxy (LawfulCommRing.sub_eq_zero_iff.mp h).symm
  have hb : mul (sub (lineAt l y) (lineAt l x)) (inv (sub y x)) = l.2 := by
    rw [lineAt_diff, LawfulCommRing.mul_assoc, hInv _ hne, LawfulCommRing.mul_one]
  unfold lineThrough
  rw [hb]
  apply Prod.ext
  · show sub (lineAt l x) (mul l.2 x) = l.1
    unfold lineAt
    exact ring_add_sub_cancel_right _ _
  · rfl

/-- Number of the five servers satisfying `p`. -/
def count5 (p : Fin 5 → Bool) : Nat :=
  (p 0).toNat + (p 1).toNat + (p 2).toNat + (p 3).toNat + (p 4).toNat

theorem count5_good (p w : Fin 5 → Bool) (h3 : 3 ≤ count5 p) (h1 : count5 w ≤ 1) :
    2 ≤ count5 (fun i => p i && !w i) := by
  have pt : ∀ a b : Bool, a.toNat ≤ (a && !b).toNat + b.toNat := by decide
  have e0 := pt (p 0) (w 0)
  have e1 := pt (p 1) (w 1)
  have e2 := pt (p 2) (w 2)
  have e3 := pt (p 3) (w 3)
  have e4 := pt (p 4) (w 4)
  simp only [count5] at h3 h1 ⊢
  omega

theorem count5_two (g : Fin 5 → Bool) (h : 2 ≤ count5 g) :
    ∃ i j : Fin 5, i ≠ j ∧ g i = true ∧ g j = true := by
  simp only [count5] at h
  cases h0 : g 0 <;> cases h1 : g 1 <;> cases h2 : g 2 <;> cases h3 : g 3 <;> cases h4 : g 4 <;>
    rw [h0, h1, h2, h3, h4] at h <;>
    first
      | exact absurd h (by decide)
      | exact ⟨0, 1, by decide, h0, h1⟩
      | exact ⟨0, 2, by decide, h0, h2⟩
      | exact ⟨0, 3, by decide, h0, h3⟩
      | exact ⟨0, 4, by decide, h0, h4⟩
      | exact ⟨1, 2, by decide, h1, h2⟩
      | exact ⟨1, 3, by decide, h1, h3⟩
      | exact ⟨1, 4, by decide, h1, h4⟩
      | exact ⟨2, 3, by decide, h2, h3⟩
      | exact ⟨2, 4, by decide, h2, h4⟩
      | exact ⟨3, 4, by decide, h3, h4⟩

theorem count5_ge_four_of_all_but : ∀ (liar : Fin 5) (p : Fin 5 → Bool),
    (∀ i, i ≠ liar → p i = true) → 4 ≤ count5 p
  | 0, p, h => by
    simp only [count5, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
      Bool.toNat_true]
    omega
  | 1, p, h => by
    simp only [count5, h 0 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
      Bool.toNat_true]
    omega
  | 2, p, h => by
    simp only [count5, h 0 (by decide), h 1 (by decide), h 3 (by decide), h 4 (by decide),
      Bool.toNat_true]
    omega
  | 3, p, h => by
    simp only [count5, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 4 (by decide),
      Bool.toNat_true]
    omega
  | 4, p, h => by
    simp only [count5, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      Bool.toNat_true]
    omega

theorem count5_le_one_of_all_but (liar : Fin 5) (w : Fin 5 → Bool)
    (h : ∀ i, i ≠ liar → w i = false) : count5 w ≤ 1 := by
  have h4 := count5_ge_four_of_all_but liar (fun i => !w i) (fun i hi => by rw [h i hi]; rfl)
  have pt : ∀ a : Bool, a.toNat + (!a).toNat = 1 := by decide
  have e0 := pt (w 0)
  have e1 := pt (w 1)
  have e2 := pt (w 2)
  have e3 := pt (w 3)
  have e4 := pt (w 4)
  simp only [count5] at h4 ⊢
  omega

variable [DecidableEq F]

/-- Server `i` answered with the value of `l` at its point. -/
def lineResponseAgrees (pts : Fin 5 → F) (ys : Fin 5 → Option F) (l : F × F) (i : Fin 5) : Bool :=
  decide (ys i = some (lineAt l (pts i)))

/-- Server `i` answered, with a value off `l`. -/
def lineResponseWrong (pts : Fin 5 → F) (ys : Fin 5 → Option F) (l : F × F) (i : Fin 5) : Bool :=
  (ys i).isSome && !decide (ys i = some (lineAt l (pts i)))

/-- At least three correct responses and at most one wrong one. A silent server is neither. -/
def OneFaultyLineResponse (pts : Fin 5 → F) (ys : Fin 5 → Option F) (honest : F × F) : Prop :=
  3 ≤ count5 (lineResponseAgrees pts ys honest) ∧ count5 (lineResponseWrong pts ys honest) ≤ 1

theorem shamir_agree_not_wrong (pts : Fin 5 → F) (ys : Fin 5 → Option F) (l honest : F × F)
    (i : Fin 5) (h : (lineResponseAgrees pts ys l i && !lineResponseWrong pts ys honest i) = true) :
    lineAt l (pts i) = lineAt honest (pts i) := by
  simp only [lineResponseAgrees, lineResponseWrong, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  simp only [Option.isSome_some, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq] at h2
  exact Option.some.inj h2

/-- The honest line is the only line agreeing with three responses. -/
theorem line_unique_of_three_agree [NoZeroDivisors F] (pts : Fin 5 → F)
    (hpts : ∀ i j : Fin 5, i ≠ j → pts i ≠ pts j) (ys : Fin 5 → Option F) (honest l : F × F)
    (hWrong : count5 (lineResponseWrong pts ys honest) ≤ 1)
    (hAgree : 3 ≤ count5 (lineResponseAgrees pts ys l)) : l = honest := by
  obtain ⟨i, j, hij, hi, hj⟩ := count5_two _ (count5_good _ _ hAgree hWrong)
  exact line_unique_of_two_points (hpts i j hij)
    (shamir_agree_not_wrong pts ys l honest i hi) (shamir_agree_not_wrong pts ys l honest j hj)

def all5 : List (Fin 5) := [0, 1, 2, 3, 4]

theorem all5_mem : ∀ i : Fin 5, i ∈ all5
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide

/-- Lines through every pair of received responses. -/
def responseLineCandidates (inv : F → F) (pts : Fin 5 → F) (ys : Fin 5 → Option F) : List (F × F) :=
  all5.flatMap fun i => all5.filterMap fun j =>
    match ys i, ys j with
    | some vi, some vj => some (lineThrough inv (pts i) (pts j) vi vj)
    | _, _ => none

/-- Pair-consistency voter: the value at zero of the first pair line that a third response
confirms. -/
def decodeSharedConstant (inv : F → F) (pts : Fin 5 → F) (ys : Fin 5 → Option F) : Option F :=
  ((responseLineCandidates inv pts ys).find? fun l => decide (3 ≤ count5 (lineResponseAgrees pts ys l))).map
    Prod.fst

theorem decodeSharedConstant_sound [NoZeroDivisors F] (inv : F → F)
    (hInv : ∀ x : F, x ≠ zero → mul x (inv x) = one) (pts : Fin 5 → F)
    (hpts : ∀ i j : Fin 5, i ≠ j → pts i ≠ pts j) (ys : Fin 5 → Option F) (honest : F × F)
    (h : OneFaultyLineResponse pts ys honest) :
    decodeSharedConstant inv pts ys = some honest.1 := by
  unfold decodeSharedConstant
  cases hf : (responseLineCandidates inv pts ys).find?
      (fun l => decide (3 ≤ count5 (lineResponseAgrees pts ys l))) with
  | some l =>
    have hp := List.find?_some hf
    have hl : 3 ≤ count5 (lineResponseAgrees pts ys l) := of_decide_eq_true hp
    rw [line_unique_of_three_agree pts hpts ys honest l h.2 hl]
    rfl
  | none =>
    exfalso
    obtain ⟨i, j, hij, hi, hj⟩ :=
      count5_two _ (show 2 ≤ count5 (lineResponseAgrees pts ys honest) from Nat.le_trans (by decide) h.1)
    have hi' : ys i = some (lineAt honest (pts i)) := of_decide_eq_true hi
    have hj' : ys j = some (lineAt honest (pts j)) := of_decide_eq_true hj
    have hmem : honest ∈ responseLineCandidates inv pts ys := by
      unfold responseLineCandidates
      refine List.mem_flatMap.mpr ⟨i, all5_mem i, List.mem_filterMap.mpr ⟨j, all5_mem j, ?_⟩⟩
      simp only [hi', hj', lineThrough_of_on_line inv hInv honest (hpts i j hij)]
    exact List.find?_eq_none.mp hf honest hmem (decide_eq_true h.1)

/-- Whichever server deviates and whatever it sends, or if it sends nothing, the voter returns
the honest value. -/
theorem shamir_any_single_forgery_corrected [NoZeroDivisors F] (inv : F → F)
    (hInv : ∀ x : F, x ≠ zero → mul x (inv x) = one) (pts : Fin 5 → F)
    (hpts : ∀ i j : Fin 5, i ≠ j → pts i ≠ pts j) (honest : F × F) (liar : Fin 5)
    (forged : Option F) :
    decodeSharedConstant inv pts
      (fun i => if i = liar then forged else some (lineAt honest (pts i))) = some honest.1 := by
  refine decodeSharedConstant_sound inv hInv pts hpts _ honest ⟨?_, ?_⟩
  · refine Nat.le_trans (by decide) (count5_ge_four_of_all_but liar _ fun i hi => ?_)
    simp only [lineResponseAgrees, ite_eq_right hi, decide_true]
  · refine count5_le_one_of_all_but liar _ fun i hi => ?_
    simp only [lineResponseWrong, ite_eq_right hi, decide_true, Option.isSome_some, Bool.not_true,
      Bool.and_false]

end ShamirLines

/-! ### Goldilocks, evaluation points `1..5` -/

/-- Shamir evaluation point of server `i`. -/
def shamirEvaluationPoint (i : Fin 5) : Goldilocks :=
  ⟨i.val + 1, by have := i.isLt; unfold goldilocksPrime; omega⟩

theorem shamirEvaluationPoint_distinct (i j : Fin 5) (h : i ≠ j) : shamirEvaluationPoint i ≠ shamirEvaluationPoint j :=
  fun he => h (Fin.ext (by
    have hv : i.val + 1 = j.val + 1 := congrArg Goldilocks.val he
    omega))

theorem goldilocks_mul_inv (x : Goldilocks) (hx : x ≠ zero) : mul x (Goldilocks.inv x) = one :=
  Goldilocks.mul_inv_cancel hx

/-- **Unique decoding against one Byzantine server.** Given at least three correct responses and
at most one wrong one among the five (so any four responses with one forgery qualify), the
sharing polynomial is the only polynomial of degree at most one agreeing with three responses,
and the voter outputs its value at zero. -/
theorem shamir_2of5_byzantine_unique_decoding (key slope : Goldilocks)
    (ys : Fin 5 → Option Goldilocks) (h : OneFaultyLineResponse shamirEvaluationPoint ys (key, slope)) :
    (∀ l : Goldilocks × Goldilocks,
      3 ≤ count5 (lineResponseAgrees shamirEvaluationPoint ys l) → l = (key, slope)) ∧
    decodeSharedConstant Goldilocks.inv shamirEvaluationPoint ys = some key ∧
    lineAt (key, slope) zero = key :=
  ⟨fun l hl => line_unique_of_three_agree shamirEvaluationPoint shamirEvaluationPoint_distinct ys (key, slope) l
      h.2 hl,
    decodeSharedConstant_sound Goldilocks.inv goldilocks_mul_inv shamirEvaluationPoint shamirEvaluationPoint_distinct
      ys (key, slope) h,
    lineAt_zero (key, slope)⟩

theorem shamir_2of5_any_single_forgery_corrected (key slope : Goldilocks) (liar : Fin 5)
    (forged : Option Goldilocks) :
    decodeSharedConstant Goldilocks.inv shamirEvaluationPoint
      (fun i => if i = liar then forged else some (lineAt (key, slope) (shamirEvaluationPoint i))) =
      some key :=
  shamir_any_single_forgery_corrected Goldilocks.inv goldilocks_mul_inv shamirEvaluationPoint
    shamirEvaluationPoint_distinct (key, slope) liar forged

/-- The premise of `shamir_2of5_byzantine_unique_decoding` holds with server `0` forging. -/
theorem shamir_one_byzantine_inhabited (key slope forged : Goldilocks) :
    ∃ ys : Fin 5 → Option Goldilocks,
      OneFaultyLineResponse shamirEvaluationPoint ys (key, slope) ∧ ys 0 = some forged := by
  refine ⟨fun i => if i = 0 then some forged else some (lineAt (key, slope) (shamirEvaluationPoint i)),
    ⟨?_, ?_⟩, rfl⟩
  · refine Nat.le_trans (by decide) (count5_ge_four_of_all_but 0 _ fun i hi => ?_)
    simp only [lineResponseAgrees, ite_eq_right hi, decide_true]
  · refine count5_le_one_of_all_but 0 _ fun i hi => ?_
    simp only [lineResponseWrong, ite_eq_right hi, decide_true, Option.isSome_some, Bool.not_true,
      Bool.and_false]

/-- **2-of-3 is ambiguous.** Responses `(2, 3, 6)` at points `(1, 2, 3)`: `1 + x` explains them
with server 2 forging, `2x` explains them with server 1 forging, and the two keys differ. Each
explanation agrees with all but one response, which is all one liar permits. -/
theorem ambiguous_2of3_witness :
    ∃ (ys : Fin 3 → Goldilocks) (lA lB : Goldilocks × Goldilocks),
      lA.1 ≠ lB.1 ∧
      (ys 0 = lineAt lA (shamirEvaluationPoint 0) ∧ ys 1 = lineAt lA (shamirEvaluationPoint 1)) ∧
      (ys 0 = lineAt lB (shamirEvaluationPoint 0) ∧ ys 2 = lineAt lB (shamirEvaluationPoint 2)) := by
  refine ⟨fun i => if i = 0 then ⟨2, by decide⟩ else if i = 1 then ⟨3, by decide⟩
      else ⟨6, by decide⟩,
    (⟨1, by decide⟩, ⟨1, by decide⟩), (⟨0, by decide⟩, ⟨2, by decide⟩), ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    exact absurd (congrArg Goldilocks.val h) (by decide)
  all_goals
    apply Goldilocks.ext
    show _ = (Goldilocks.add _ (Goldilocks.mul _ _)).val
    rw [Goldilocks.add_val, Goldilocks.mul_val]
    decide

/-! ## §3. 3-party co-ZK: one ZKBoo repetition -/

/-- Circuit gates. Wire operands are indices of earlier gates. -/
inductive CzkGate (R : Type) where
  | input : CzkGate R
  | const (v : R) : CzkGate R
  | add (a b : Nat) : CzkGate R
  | scale (a : Nat) (v : R) : CzkGate R
  | mul (a b : Nat) : CzkGate R

/-- Prover randomness consumed by a gate: two input shares, or one mask per party. -/
@[expose] def CzkGateRand (R : Type) : CzkGate R → Type
  | .input => R × R
  | .mul _ _ => Fin 3 → R
  | .const _ => Unit
  | .add _ _ => Unit
  | .scale _ _ => Unit

/-- What an opened pair `(e, e + 1)` shows of a gate beyond what it determines: both input
shares, or both masks and the second party's product share. -/
@[expose] def CzkGateView (R : Type) : CzkGate R → Type
  | .input => R × R
  | .mul _ _ => R × R × R
  | .const _ => Unit
  | .add _ _ => Unit
  | .scale _ _ => Unit

@[expose] def CzkRand (R : Type) : List (CzkGate R) → Type
  | [] => Unit
  | g :: gs => CzkGateRand R g × CzkRand R gs

@[expose] def CzkView (R : Type) : List (CzkGate R) → Type
  | [] => Unit
  | g :: gs => CzkGateView R g × CzkView R gs

/-- A party's commitment at one gate: its wire share and its tape mask. -/
structure CzkGateCommit (R : Type) where
  share : Fin 3 → R
  mask : Fin 3 → R

section CoZk
variable {R : Type} [LawfulCommRing R]

def czkMulProd (a0 a1 b0 b1 : R) : R := add (add (mul a0 b0) (mul a0 b1)) (mul a1 b0)

/-- The multiplication gate of `zk_engine.rs::gate`. -/
def czkMulShare (a0 a1 b0 b1 r0 r1 : R) : R := add (czkMulProd a0 a1 b0 b1) (sub r0 r1)

def czkEmptyWires : Fin 3 → Nat → R := fun _ _ => zero

def czkPush (W : Fin 3 → Nat → R) (n : Nat) (x : Fin 3 → R) : Fin 3 → Nat → R :=
  fun p a => if a = n then x p else W p a

def czkSum3 (x : Fin 3 → R) : R := add (add (x 0) (x 1)) (x 2)

/-- Share of a gate each party computes from its own wires. -/
def czkLocalShare (g : CzkGate R) (W : Fin 3 → Nat → R) (p : Fin 3) : R :=
  match g with
  | .const v => if p = 0 then v else zero
  | .add a b => add (W p a) (W p b)
  | .scale a v => mul (W p a) v
  | .input => zero
  | .mul _ _ => zero

def czkInputShares (w : R) (ρ : R × R) : Fin 3 → R :=
  fun p => if p = 0 then ρ.1 else if p = 1 then ρ.2 else sub w (add ρ.1 ρ.2)

def czkMulShares (a b : Nat) (W : Fin 3 → Nat → R) (r : Fin 3 → R) : Fin 3 → R :=
  fun p => czkMulShare (W p a) (W (p + 1) a) (W p b) (W (p + 1) b) (r p) (r (p + 1))

/-- The three parties' shares of a gate in an honest execution. -/
def czkGateShares : (g : CzkGate R) → (Fin 3 → Nat → R) → R → CzkGateRand R g → Fin 3 → R
  | .input, _, w, ρ => czkInputShares w ρ
  | .mul a b, W, _, r => czkMulShares a b W r
  | .const v, W, _, _ => czkLocalShare (.const v) W
  | .add a b, W, _, _ => czkLocalShare (.add a b) W
  | .scale a v, W, _, _ => czkLocalShare (.scale a v) W

def czkGateView (e : Fin 3) :
    (g : CzkGate R) → (Fin 3 → Nat → R) → R → CzkGateRand R g → CzkGateView R g
  | .input, _, w, ρ => (czkInputShares w ρ e, czkInputShares w ρ (e + 1))
  | .mul a b, W, _, r => (r e, r (e + 1), czkMulShares a b W r (e + 1))
  | .const _, _, _, _ => ()
  | .add _ _, _, _, _ => ()
  | .scale _ _, _, _, _ => ()

def czkInputSim (e : Fin 3) (w : R) (v : R × R) : R × R :=
  if e = 0 then v else if e = 1 then (sub (sub w v.2) v.1, v.1) else (v.2, sub (sub w v.1) v.2)

def czkMulSim (e : Fin 3) (a b : Nat) (W : Fin 3 → Nat → R) (v : R × R × R) : Fin 3 → R :=
  fun p => if p = e then v.1 else if p = e + 1 then v.2.1
    else sub v.2.1 (sub v.2.2
      (czkMulProd (W (e + 1) a) (W (e + 2) a) (W (e + 1) b) (W (e + 2) b)))

/-- The randomness that produces a given gate view, for the given wires. -/
def czkGateSim (e : Fin 3) :
    (g : CzkGate R) → (Fin 3 → Nat → R) → R → CzkGateView R g → CzkGateRand R g
  | .input, _, w, v => czkInputSim e w v
  | .mul a b, W, _, v => czkMulSim e a b W v
  | .const _, _, _, _ => ()
  | .add _ _, _, _, _ => ()
  | .scale _ _, _, _, _ => ()

def czkNextWit (g : CzkGate R) (ws : List R) : List R :=
  match g with
  | .input => ws.tail
  | .const _ => ws
  | .add _ _ => ws
  | .scale _ _ => ws
  | .mul _ _ => ws

/-- Opened view of the pair `(e, e + 1)` in an honest execution on witness `ws`. -/
def czkRunView (e : Fin 3) :
    (gs : List (CzkGate R)) → (Fin 3 → Nat → R) → Nat → List R → CzkRand R gs → CzkView R gs
  | [], _, _, _, _ => ()
  | g :: gs, W, n, ws, ρ =>
    (czkGateView e g W (ws.headD zero) ρ.1,
      czkRunView e gs (czkPush W n (czkGateShares g W (ws.headD zero) ρ.1)) (n + 1)
        (czkNextWit g ws) ρ.2)

def czkSimRand (e : Fin 3) :
    (gs : List (CzkGate R)) → (Fin 3 → Nat → R) → Nat → List R → CzkView R gs → CzkRand R gs
  | [], _, _, _, _ => ()
  | g :: gs, W, n, ws, v =>
    (czkGateSim e g W (ws.headD zero) v.1,
      czkSimRand e gs
        (czkPush W n (czkGateShares g W (ws.headD zero) (czkGateSim e g W (ws.headD zero) v.1)))
        (n + 1) (czkNextWit g ws) v.2)

theorem fin3_cycle : ∀ e : Fin 3,
    e + 1 ≠ e ∧ e + 2 ≠ e ∧ e + 2 ≠ e + 1 ∧ e + 1 + 1 = e + 2 ∧
      ∀ p : Fin 3, p ≠ e → p ≠ e + 1 → p = e + 2 := by
  decide

theorem czkInputSim_view : ∀ (e : Fin 3) (w : R) (ρ : R × R),
    czkInputSim e w (czkInputShares w ρ e, czkInputShares w ρ (e + 1)) = ρ
  | 0, _, _ => rfl
  | 1, w, ρ => by
    show (sub (sub w (sub w (add ρ.1 ρ.2))) ρ.2, ρ.2) = ρ
    rw [sub_sub_self, ring_add_sub_cancel_right]
  | 2, w, ρ => by
    show (ρ.1, sub (sub w (sub w (add ρ.1 ρ.2))) ρ.1) = ρ
    rw [sub_sub_self, add_sub_cancel]

theorem czkInputView_sim : ∀ (e : Fin 3) (w : R) (v : R × R),
    (czkInputShares w (czkInputSim e w v) e, czkInputShares w (czkInputSim e w v) (e + 1)) = v
  | 0, _, _ => rfl
  | 1, w, v => by
    show (v.1, sub w (add (sub (sub w v.2) v.1) v.1)) = v
    rw [ring_sub_add_cancel_right, sub_sub_self]
  | 2, w, v => by
    show (sub w (add v.2 (sub (sub w v.1) v.2)), v.2) = v
    rw [LawfulCommRing.add_sub_cancel_left, sub_sub_self]

theorem czkMulSim_view (e : Fin 3) (a b : Nat) (W : Fin 3 → Nat → R) (r : Fin 3 → R) :
    czkMulSim e a b W (r e, r (e + 1), czkMulShares a b W r (e + 1)) = r := by
  obtain ⟨_, _, _, h4, h5⟩ := fin3_cycle e
  funext p
  show (if p = e then r e else if p = e + 1 then r (e + 1)
    else sub (r (e + 1)) (sub (czkMulShares a b W r (e + 1))
      (czkMulProd (W (e + 1) a) (W (e + 2) a) (W (e + 1) b) (W (e + 2) b)))) = r p
  refine if h1 : p = e then ?_ else if h2 : p = e + 1 then ?_ else ?_
  · rw [ite_eq_left h1, h1]
  · rw [ite_eq_right h1, ite_eq_left h2, h2]
  · rw [ite_eq_right h1, ite_eq_right h2, h5 p h1 h2]
    show sub (r (e + 1)) (sub (czkMulShare (W (e + 1) a) (W (e + 1 + 1) a) (W (e + 1) b)
      (W (e + 1 + 1) b) (r (e + 1)) (r (e + 1 + 1))) _) = r (e + 2)
    rw [h4]
    unfold czkMulShare
    rw [add_sub_cancel, sub_sub_self]

theorem czkMulView_sim (e : Fin 3) (a b : Nat) (W : Fin 3 → Nat → R) (v : R × R × R) :
    (czkMulSim e a b W v e, czkMulSim e a b W v (e + 1),
      czkMulShares a b W (czkMulSim e a b W v) (e + 1)) = v := by
  obtain ⟨h1, h2, h3, h4, _⟩ := fin3_cycle e
  obtain ⟨v0, v1, vz⟩ := v
  have e0 : czkMulSim e a b W (v0, v1, vz) e = v0 := ite_eq_left rfl
  have e1 : czkMulSim e a b W (v0, v1, vz) (e + 1) = v1 := by
    show (if e + 1 = e then v0 else if e + 1 = e + 1 then v1 else _) = v1
    rw [ite_eq_right h1, ite_eq_left rfl]
  have e2 : czkMulSim e a b W (v0, v1, vz) (e + 2) = sub v1 (sub vz
      (czkMulProd (W (e + 1) a) (W (e + 2) a) (W (e + 1) b) (W (e + 2) b))) := by
    show (if e + 2 = e then v0 else if e + 2 = e + 1 then v1 else _) = _
    rw [ite_eq_right h2, ite_eq_right h3]
  have ez : czkMulShares a b W (czkMulSim e a b W (v0, v1, vz)) (e + 1) = vz := by
    show czkMulShare (W (e + 1) a) (W (e + 1 + 1) a) (W (e + 1) b) (W (e + 1 + 1) b)
      (czkMulSim e a b W (v0, v1, vz) (e + 1)) (czkMulSim e a b W (v0, v1, vz) (e + 1 + 1)) = vz
    rw [h4, e1, e2]
    unfold czkMulShare
    rw [sub_sub_self, LawfulCommRing.add_sub_cancel_left]
  rw [e0, e1, ez]

theorem czkGateSim_view (e : Fin 3) (g : CzkGate R) (W : Fin 3 → Nat → R) (w : R)
    (ρ : CzkGateRand R g) : czkGateSim e g W w (czkGateView e g W w ρ) = ρ := by
  cases g with
  | input => exact czkInputSim_view e w ρ
  | mul a b => exact czkMulSim_view e a b W ρ
  | const v => rfl
  | add a b => rfl
  | scale a v => rfl

theorem czkGateView_sim (e : Fin 3) (g : CzkGate R) (W : Fin 3 → Nat → R) (w : R)
    (v : CzkGateView R g) : czkGateView e g W w (czkGateSim e g W w v) = v := by
  cases g with
  | input => exact czkInputView_sim e w v
  | mul a b => exact czkMulView_sim e a b W v
  | const v => rfl
  | add a b => rfl
  | scale a v => rfl

theorem czkSimRand_runView (e : Fin 3) : ∀ (gs : List (CzkGate R)) (W : Fin 3 → Nat → R)
    (n : Nat) (ws : List R) (ρ : CzkRand R gs),
    czkSimRand e gs W n ws (czkRunView e gs W n ws ρ) = ρ := by
  intro gs
  induction gs with
  | nil => intro _ _ _ _; rfl
  | cons g gs ih =>
    intro W n ws ρ
    obtain ⟨ρg, ρs⟩ := ρ
    show (czkGateSim e g W (ws.headD zero) (czkGateView e g W (ws.headD zero) ρg),
      czkSimRand e gs (czkPush W n (czkGateShares g W (ws.headD zero)
        (czkGateSim e g W (ws.headD zero) (czkGateView e g W (ws.headD zero) ρg)))) (n + 1)
        (czkNextWit g ws)
        (czkRunView e gs (czkPush W n (czkGateShares g W (ws.headD zero) ρg)) (n + 1)
          (czkNextWit g ws) ρs)) = (ρg, ρs)
    rw [czkGateSim_view, ih]

theorem czkRunView_simRand (e : Fin 3) : ∀ (gs : List (CzkGate R)) (W : Fin 3 → Nat → R)
    (n : Nat) (ws : List R) (v : CzkView R gs),
    czkRunView e gs W n ws (czkSimRand e gs W n ws v) = v := by
  intro gs
  induction gs with
  | nil => intro _ _ _ _; rfl
  | cons g gs ih =>
    intro W n ws v
    obtain ⟨vg, vrest⟩ := v
    show (czkGateView e g W (ws.headD zero) (czkGateSim e g W (ws.headD zero) vg),
      czkRunView e gs (czkPush W n (czkGateShares g W (ws.headD zero)
        (czkGateSim e g W (ws.headD zero) vg))) (n + 1) (czkNextWit g ws)
        (czkSimRand e gs (czkPush W n (czkGateShares g W (ws.headD zero)
          (czkGateSim e g W (ws.headD zero) vg))) (n + 1) (czkNextWit g ws) vrest)) = (vg, vrest)
    rw [czkGateView_sim, ih]

theorem czk_view_fiber_unique (e : Fin 3) (gs : List (CzkGate R)) (ws : List R)
    (v : CzkView R gs) :
    ∃ ρ : CzkRand R gs, czkRunView e gs czkEmptyWires 0 ws ρ = v ∧
      ∀ ρ' : CzkRand R gs, czkRunView e gs czkEmptyWires 0 ws ρ' = v → ρ' = ρ :=
  ⟨czkSimRand e gs czkEmptyWires 0 ws v, czkRunView_simRand e gs czkEmptyWires 0 ws v,
    fun ρ' h => by rw [← h, czkSimRand_runView]⟩

/-- **Exact 2-privacy.** For every opened pair, every circuit and any two witnesses, each opened
view arises from exactly one choice of prover randomness under either witness. -/
theorem cozk_opened_pair_uniform (e : Fin 3) (gs : List (CzkGate R)) (w₁ w₂ : List R)
    (v : CzkView R gs) :
    (∃ ρ : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₁ ρ = v ∧
      ∀ ρ' : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₁ ρ' = v → ρ' = ρ) ∧
    (∃ ρ : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₂ ρ = v ∧
      ∀ ρ' : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₂ ρ' = v → ρ' = ρ) :=
  ⟨czk_view_fiber_unique e gs w₁ v, czk_view_fiber_unique e gs w₂ v⟩

/-! ### Verification of an opened pair and extraction -/

def czkPlainGate (g : CzkGate R) (vals : Nat → R) (w : R) : R :=
  match g with
  | .input => w
  | .const v => v
  | .add a b => add (vals a) (vals b)
  | .scale a v => mul (vals a) v
  | .mul a b => mul (vals a) (vals b)

/-- Wire values of the circuit on a witness. -/
def czkPlainEval : List (CzkGate R) → (Nat → R) → Nat → List R → Nat → R
  | [], vals, _, _ => vals
  | g :: gs, vals, n, ws =>
    czkPlainEval gs (fun a => if a = n then czkPlainGate g vals (ws.headD zero) else vals a)
      (n + 1) (czkNextWit g ws)

/-- The witness makes every output wire zero. -/
def czkAccepts (gs : List (CzkGate R)) (outs : List Nat) (ws : List R) : Prop :=
  ∀ o ∈ outs, czkPlainEval gs (fun _ => zero) 0 ws o = zero

def czkGateWitness (g : CzkGate R) (c : CzkGateCommit R) : List R :=
  match g with
  | .input => [czkSum3 c.share]
  | .const _ => []
  | .add _ _ => []
  | .scale _ _ => []
  | .mul _ _ => []

/-- The witness reconstructed from the three committed input shares. -/
def czkExtractWitness : List (CzkGate R) → List (CzkGateCommit R) → List R
  | g :: gs, c :: T => czkGateWitness g c ++ czkExtractWitness gs T
  | [], _ => []
  | _ :: _, [] => []

theorem czk_mul_sum (a0 a1 a2 b0 b1 b2 r0 r1 r2 : R) :
    add (add (czkMulShare a0 a1 b0 b1 r0 r1) (czkMulShare a1 a2 b1 b2 r1 r2))
      (czkMulShare a2 a0 b2 b0 r2 r0) =
    mul (add (add a0 a1) a2) (add (add b0 b1) b2) := by
  have hsplit : add (add (czkMulShare a0 a1 b0 b1 r0 r1) (czkMulShare a1 a2 b1 b2 r1 r2))
      (czkMulShare a2 a0 b2 b0 r2 r0) =
      add (add (add (czkMulProd a0 a1 b0 b1) (czkMulProd a1 a2 b1 b2)) (czkMulProd a2 a0 b2 b0))
        (add (add (sub r0 r1) (sub r1 r2)) (sub r2 r0)) := by
    simp only [czkMulShare, LawfulCommRing.add_assoc, LawfulCommRing.add_comm, add_left_comm]
  rw [hsplit, telescope3, LawfulCommRing.add_zero]
  simp only [czkMulProd, LawfulCommRing.left_distrib, LawfulCommRing.right_distrib,
    LawfulCommRing.add_assoc, LawfulCommRing.add_comm, add_left_comm]

variable [DecidableEq R]

/-- Replay check of pair `(e, e + 1)` at one gate: party `e`'s product is recomputed from both
parties' wires and masks; local gates are recomputed for both parties. Only indices `e` and
`e + 1` are read. -/
def czkPairGateOk (e : Fin 3) (g : CzkGate R) (W : Fin 3 → Nat → R) (c : CzkGateCommit R) : Bool :=
  match g with
  | .input => true
  | .mul a b => decide (c.share e =
      czkMulShare (W e a) (W (e + 1) a) (W e b) (W (e + 1) b) (c.mask e) (c.mask (e + 1)))
  | .const v => decide (c.share e = czkLocalShare (.const v) W e) &&
      decide (c.share (e + 1) = czkLocalShare (.const v) W (e + 1))
  | .add a b => decide (c.share e = czkLocalShare (.add a b) W e) &&
      decide (c.share (e + 1) = czkLocalShare (.add a b) W (e + 1))
  | .scale a v => decide (c.share e = czkLocalShare (.scale a v) W e) &&
      decide (c.share (e + 1) = czkLocalShare (.scale a v) W (e + 1))

/-- Output check: the two opened output shares match the replayed wires and the three committed
output shares sum to zero. -/
def czkOutputsOk (e : Fin 3) (W : Fin 3 → Nat → R) : List Nat → List (Fin 3 → R) → Bool
  | [], [] => true
  | o :: os, y :: ys =>
    decide (y e = W e o) && decide (y (e + 1) = W (e + 1) o) && decide (czkSum3 y = zero) &&
      czkOutputsOk e W os ys
  | [], _ :: _ => false
  | _ :: _, [] => false

def czkVerifyPair (e : Fin 3) (outs : List Nat) (O : List (Fin 3 → R)) :
    List (CzkGate R) → List (CzkGateCommit R) → (Fin 3 → Nat → R) → Nat → Bool
  | [], [], W, _ => czkOutputsOk e W outs O
  | g :: gs, c :: T, W, n =>
    czkPairGateOk e g W c && czkVerifyPair e outs O gs T (czkPush W n c.share) (n + 1)
  | [], _ :: _, _, _ => false
  | _ :: _, [], _, _ => false

theorem fin3_all {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ e, P e
  | 0 => h0
  | 1 => h1
  | 2 => h2

theorem czk_gate_sum (g : CzkGate R) (W : Fin 3 → Nat → R) (vals : Nat → R)
    (c : CzkGateCommit R) (hW : ∀ a, czkSum3 (fun p => W p a) = vals a)
    (hok : ∀ e : Fin 3, czkPairGateOk e g W c = true) :
    czkSum3 c.share = czkPlainGate g vals ((czkGateWitness g c).headD zero) := by
  cases g with
  | input => rfl
  | const v =>
    have h0 : c.share 0 = v := (of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 0)).1)
    have h1 : c.share 1 = zero := (of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 1)).1)
    have h2 : c.share 2 = zero := (of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 2)).1)
    show add (add (c.share 0) (c.share 1)) (c.share 2) = v
    rw [h0, h1, h2, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  | add a b =>
    have h0 : c.share 0 = add (W 0 a) (W 0 b) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 0)).1
    have h1 : c.share 1 = add (W 1 a) (W 1 b) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 1)).1
    have h2 : c.share 2 = add (W 2 a) (W 2 b) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 2)).1
    show add (add (c.share 0) (c.share 1)) (c.share 2) = add (vals a) (vals b)
    rw [h0, h1, h2, ← hW a, ← hW b]
    simp only [czkSum3, LawfulCommRing.add_comm, add_left_comm]
  | scale a v =>
    have h0 : c.share 0 = mul (W 0 a) v := of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 0)).1
    have h1 : c.share 1 = mul (W 1 a) v := of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 1)).1
    have h2 : c.share 2 = mul (W 2 a) v := of_decide_eq_true (Bool.and_eq_true_iff.mp (hok 2)).1
    show add (add (c.share 0) (c.share 1)) (c.share 2) = mul (vals a) v
    rw [h0, h1, h2, ← hW a]
    simp only [czkSum3, LawfulCommRing.right_distrib]
  | mul a b =>
    have h0 : c.share 0 = czkMulShare (W 0 a) (W 1 a) (W 0 b) (W 1 b) (c.mask 0) (c.mask 1) :=
      of_decide_eq_true (hok 0)
    have h1 : c.share 1 = czkMulShare (W 1 a) (W 2 a) (W 1 b) (W 2 b) (c.mask 1) (c.mask 2) :=
      of_decide_eq_true (hok 1)
    have h2 : c.share 2 = czkMulShare (W 2 a) (W 0 a) (W 2 b) (W 0 b) (c.mask 2) (c.mask 0) :=
      of_decide_eq_true (hok 2)
    show add (add (c.share 0) (c.share 1)) (c.share 2) = mul (vals a) (vals b)
    rw [h0, h1, h2, ← hW a, ← hW b]
    exact czk_mul_sum _ _ _ _ _ _ _ _ _

theorem czk_circuit_sum (outs : List Nat) (O : List (Fin 3 → R)) :
    ∀ (gs : List (CzkGate R)) (T : List (CzkGateCommit R)) (W : Fin 3 → Nat → R)
      (vals : Nat → R) (n : Nat),
      (∀ a, czkSum3 (fun p => W p a) = vals a) →
      (∀ e : Fin 3, czkVerifyPair e outs O gs T W n = true) →
      ∃ W' : Fin 3 → Nat → R,
        (∀ a, czkSum3 (fun p => W' p a) = czkPlainEval gs vals n (czkExtractWitness gs T) a) ∧
        ∀ e : Fin 3, czkOutputsOk e W' outs O = true := by
  intro gs
  induction gs with
  | nil =>
    intro T W vals n hW hv
    cases T with
    | nil => exact ⟨W, hW, hv⟩
    | cons c T => exact absurd (hv 0) Bool.false_ne_true
  | cons g gs ih =>
    intro T W vals n hW hv
    cases T with
    | nil => exact absurd (hv 0) Bool.false_ne_true
    | cons c T =>
      have hg : ∀ e : Fin 3, czkPairGateOk e g W c = true :=
        fun e => (Bool.and_eq_true_iff.mp (hv e)).1
      have hrest : ∀ e : Fin 3,
          czkVerifyPair e outs O gs T (czkPush W n c.share) (n + 1) = true :=
        fun e => (Bool.and_eq_true_iff.mp (hv e)).2
      have hsum := czk_gate_sum g W vals c hW hg
      have hpush : ∀ a, czkSum3 (fun p => czkPush W n c.share p a) =
          (if a = n then czkPlainGate g vals ((czkGateWitness g c).headD zero) else vals a) := by
        intro a
        refine if ha : a = n then ?_ else ?_
        · rw [ite_eq_left ha]
          show add (add (if a = n then c.share 0 else W 0 a) (if a = n then c.share 1 else W 1 a))
            (if a = n then c.share 2 else W 2 a) = _
          rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left ha]
          exact hsum
        · rw [ite_eq_right ha]
          show add (add (if a = n then c.share 0 else W 0 a) (if a = n then c.share 1 else W 1 a))
            (if a = n then c.share 2 else W 2 a) = _
          rw [ite_eq_right ha, ite_eq_right ha, ite_eq_right ha]
          exact hW a
      obtain ⟨W', hW', hout⟩ := ih T (czkPush W n c.share) _ (n + 1) hpush hrest
      refine ⟨W', fun a => ?_, hout⟩
      rw [hW' a]
      have hhead : czkPlainGate g vals ((czkExtractWitness (g :: gs) (c :: T)).headD zero) =
          czkPlainGate g vals ((czkGateWitness g c).headD zero) := by
        cases g <;> rfl
      have htail : czkNextWit g (czkExtractWitness (g :: gs) (c :: T)) = czkExtractWitness gs T := by
        cases g <;> rfl
      show _ = czkPlainEval gs
        (fun a => if a = n then
          czkPlainGate g vals ((czkExtractWitness (g :: gs) (c :: T)).headD zero) else vals a)
        (n + 1) (czkNextWit g (czkExtractWitness (g :: gs) (c :: T))) a
      rw [hhead, htail]

theorem czk_outputs_zero (W : Fin 3 → Nat → R) :
    ∀ (outs : List Nat) (O : List (Fin 3 → R)),
      (∀ e : Fin 3, czkOutputsOk e W outs O = true) →
      ∀ o ∈ outs, czkSum3 (fun p => W p o) = zero := by
  intro outs
  induction outs with
  | nil => intro _ _ o ho; exact absurd ho List.not_mem_nil
  | cons o os ih =>
    intro O h o' ho'
    cases O with
    | nil => exact absurd (h 0) Bool.false_ne_true
    | cons y ys =>
      have hsplit : ∀ e : Fin 3, (y e = W e o ∧ czkSum3 y = zero) ∧
          czkOutputsOk e W os ys = true := by
        intro e
        have he := h e
        simp only [czkOutputsOk, Bool.and_eq_true, decide_eq_true_eq] at he
        exact ⟨⟨he.1.1.1, he.1.2⟩, he.2⟩
      rcases List.mem_cons.mp ho' with rfl | hmem
      · show add (add (W 0 o') (W 1 o')) (W 2 o') = zero
        rw [← (hsplit 0).1.1, ← (hsplit 1).1.1, ← (hsplit 2).1.1]
        exact (hsplit 0).1.2
      · exact ih ys (fun e => (hsplit e).2) o' hmem

/-- **Three consistent openings yield a witness.** If all three pair openings of one committed
repetition verify, the sum of the committed input shares satisfies the circuit. -/
theorem cozk_three_valid_pairs_extract_witness (gs : List (CzkGate R)) (outs : List Nat)
    (T : List (CzkGateCommit R)) (O : List (Fin 3 → R))
    (h : ∀ e : Fin 3, czkVerifyPair e outs O gs T czkEmptyWires 0 = true) :
    czkAccepts gs outs (czkExtractWitness gs T) := by
  have h0 : ∀ a, czkSum3 (fun p => (czkEmptyWires : Fin 3 → Nat → R) p a) = zero := by
    intro a
    show add (add zero zero) zero = (zero : R)
    rw [LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  obtain ⟨W', hW', hout⟩ := czk_circuit_sum outs O gs T czkEmptyWires (fun _ => zero) 0 h0 h
  intro o ho
  rw [← hW' o]
  exact czk_outputs_zero W' outs O hout o ho

/-- Number of the three pair openings of a committed repetition that verify. -/
def czkValidPairCount (gs : List (CzkGate R)) (outs : List Nat)
    (rep : List (CzkGateCommit R) × List (Fin 3 → R)) : Nat :=
  (czkVerifyPair 0 outs rep.2 gs rep.1 czkEmptyWires 0).toNat +
    (czkVerifyPair 1 outs rep.2 gs rep.1 czkEmptyWires 0).toNat +
    (czkVerifyPair 2 outs rep.2 gs rep.1 czkEmptyWires 0).toNat

theorem three_bools_le_two : ∀ a b c : Bool, ¬ (a = true ∧ b = true ∧ c = true) →
    a.toNat + b.toNat + c.toNat ≤ 2 := by
  decide

/-- **Cheating is caught on at least one pair.** If no witness satisfies the circuit, then for
every committed repetition at most two of the three pair openings verify. -/
theorem cozk_false_statement_caught_at_least_one_pair (gs : List (CzkGate R)) (outs : List Nat)
    (hFalse : ∀ ws : List R, ¬ czkAccepts gs outs ws)
    (rep : List (CzkGateCommit R) × List (Fin 3 → R)) :
    czkValidPairCount gs outs rep ≤ 2 :=
  three_bools_le_two _ _ _ fun ⟨h0, h1, h2⟩ =>
    hFalse _ (cozk_three_valid_pairs_extract_witness gs outs rep.1 rep.2 (fin3_all h0 h1 h2))

/-- Wires after replaying a prefix of the committed transcript. -/
def czkReplayWires : List (CzkGateCommit R) → (Fin 3 → Nat → R) → Nat → Fin 3 → Nat → R
  | [], W, _ => W
  | c :: T, W, n => czkReplayWires T (czkPush W n c.share) (n + 1)

theorem czkVerifyPair_gate_ok (e : Fin 3) (outs : List Nat) (O : List (Fin 3 → R))
    (g : CzkGate R) (c : CzkGateCommit R) (post : List (CzkGate R))
    (Tpost : List (CzkGateCommit R)) :
    ∀ (pre : List (CzkGate R)) (Tpre : List (CzkGateCommit R)) (W : Fin 3 → Nat → R) (n : Nat),
      pre.length = Tpre.length →
      czkVerifyPair e outs O (pre ++ g :: post) (Tpre ++ c :: Tpost) W n = true →
      czkPairGateOk e g (czkReplayWires Tpre W n) c = true := by
  intro pre
  induction pre with
  | nil =>
    intro Tpre W n hlen hv
    cases Tpre with
    | nil => exact (Bool.and_eq_true_iff.mp hv).1
    | cons _ _ => exact Nat.noConfusion hlen
  | cons g' pre ih =>
    intro Tpre W n hlen hv
    cases Tpre with
    | nil => exact Nat.noConfusion hlen
    | cons c' Tpre =>
      exact ih Tpre (czkPush W n c'.share) (n + 1) (Nat.succ.inj hlen)
        (Bool.and_eq_true_iff.mp hv).2

/-- A product share that differs from the gate formula fails the pair opening of its owner. -/
theorem cozk_corrupted_mul_wire_fails_owner_pair (p : Fin 3) (outs : List Nat)
    (O : List (Fin 3 → R)) (a b : Nat) (c : CzkGateCommit R) (pre post : List (CzkGate R))
    (Tpre Tpost : List (CzkGateCommit R)) (hlen : pre.length = Tpre.length)
    (hCorrupt : c.share p ≠
      czkMulShare (czkReplayWires Tpre czkEmptyWires 0 p a)
        (czkReplayWires Tpre czkEmptyWires 0 (p + 1) a)
        (czkReplayWires Tpre czkEmptyWires 0 p b)
        (czkReplayWires Tpre czkEmptyWires 0 (p + 1) b) (c.mask p) (c.mask (p + 1))) :
    czkVerifyPair p outs O (pre ++ .mul a b :: post) (Tpre ++ c :: Tpost) czkEmptyWires 0 =
      false := by
  cases hv : czkVerifyPair p outs O (pre ++ .mul a b :: post) (Tpre ++ c :: Tpost)
      czkEmptyWires 0 with
  | false => rfl
  | true =>
    exact absurd
      (of_decide_eq_true (czkVerifyPair_gate_ok p outs O (.mul a b) c post Tpost pre Tpre
        czkEmptyWires 0 hlen hv))
      hCorrupt

end CoZk

/-! ### Pre-open sacrifice of a multiplication triple -/

section CoZkSacrifice
variable {R : Type} [LawfulCommRing R]

/-- Residual of sacrificing the triple `(a, b, c)` against `(x, y, z)` under challenge `t`, with
`t x - a` and `y - b` opened. -/
def czkSacrificeResidual (t x y z a b c : R) : R :=
  sub (mul t z)
    (add (add (add c (mul (sub y b) a)) (mul (sub (mul t x) a) b))
      (mul (sub (mul t x) a) (sub y b)))

theorem czkSacrificeResidual_eq (t x y a b ez ec : R) :
    czkSacrificeResidual t x y (add (mul x y) ez) a b (add (mul a b) ec) =
      sub (mul t ez) ec := by
  have hP : mul t (mul x y) =
      add (add (add (mul a b) (mul (sub y b) a)) (mul (sub (mul t x) a) b))
        (mul (sub (mul t x) a) (sub y b)) := by
    have h1 : mul t (mul x y) = mul (add (sub (mul t x) a) a) (add (sub y b) b) := by
      rw [ring_sub_add_cancel_right, ring_sub_add_cancel_right, LawfulCommRing.mul_assoc]
    rw [h1]
    simp only [LawfulCommRing.left_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.add_assoc, LawfulCommRing.add_comm, LawfulCommRing.mul_comm]
  have hD : add (add (add (add (mul a b) ec) (mul (sub y b) a)) (mul (sub (mul t x) a) b))
      (mul (sub (mul t x) a) (sub y b)) =
      add (add (add (add (mul a b) (mul (sub y b) a)) (mul (sub (mul t x) a) b))
        (mul (sub (mul t x) a) (sub y b))) ec := by
    simp only [LawfulCommRing.add_assoc, LawfulCommRing.add_comm]
  unfold czkSacrificeResidual
  rw [LawfulCommRing.left_distrib, hD, hP, add_sub_add_left]

/-- **Pre-open sacrifice.** A product with nonzero error `ez` passes the sacrifice for exactly one
challenge, whatever error `ec` the auxiliary triple carries. Both errors are fixed before the
challenge is drawn. -/
theorem cozk_preopen_sacrifice_sound (inv : R → R)
    (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one) (t x y a b ez ec : R) (hez : ez ≠ zero) :
    czkSacrificeResidual t x y (add (mul x y) ez) a b (add (mul a b) ec) = zero ↔
      t = mul ec (inv ez) := by
  rw [czkSacrificeResidual_eq, LawfulCommRing.sub_eq_zero_iff]
  constructor
  · intro h
    rw [← h, LawfulCommRing.mul_assoc, hInv ez hez, LawfulCommRing.mul_one]
  · intro h
    subst h
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (inv ez) ez, hInv ez hez,
      LawfulCommRing.mul_one]

/-- A correct product with a correct auxiliary triple passes for every challenge. -/
theorem cozk_preopen_sacrifice_complete (t x y a b : R) :
    czkSacrificeResidual t x y (add (mul x y) zero) a b (add (mul a b) zero) = zero := by
  rw [czkSacrificeResidual_eq, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]

end CoZkSacrifice

/-! ### Repetitions -/

section CoZkReps
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- A challenge vector opens pair `es[i]` of repetition `i`; it is accepted when every opening
verifies. -/
def czkVerifyAll (gs : List (CzkGate R)) (outs : List Nat) :
    List (Fin 3) → List (List (CzkGateCommit R) × List (Fin 3 → R)) → Bool
  | [], [] => true
  | e :: es, r :: rs =>
    czkVerifyPair e outs r.2 gs r.1 czkEmptyWires 0 && czkVerifyAll gs outs es rs
  | [], _ :: _ => false
  | _ :: _, [] => false

def czkAcceptCount (gs : List (CzkGate R)) (outs : List Nat) :
    List (List (CzkGateCommit R) × List (Fin 3 → R)) → Nat
  | [] => 1
  | r :: rs => czkValidPairCount gs outs r * czkAcceptCount gs outs rs

end CoZkReps

/-- All challenge vectors of length `n`. -/
def czkChallenges : Nat → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (czkChallenges n).flatMap fun es => [0 :: es, 1 :: es, 2 :: es]

theorem czkChallenges_length : ∀ n, (czkChallenges n).length = 3 ^ n
  | 0 => rfl
  | n + 1 => by
    have aux : ∀ l : List (List (Fin 3)),
        (l.flatMap fun es => [0 :: es, 1 :: es, 2 :: es]).length = l.length * 3 := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih =>
        rw [List.flatMap_cons, List.length_append, ih]
        show 3 + l.length * 3 = (l.length + 1) * 3
        omega
    show ((czkChallenges n).flatMap fun es => [0 :: es, 1 :: es, 2 :: es]).length = 3 ^ (n + 1)
    rw [aux, czkChallenges_length n, Nat.pow_succ]

section CoZkCount
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem filter3_length {α : Type} (p : α → Bool) (x y z : α) :
    ([x, y, z].filter p).length = (p x).toNat + (p y).toNat + (p z).toNat := by
  cases hx : p x <;> cases hy : p y <;> cases hz : p z <;>
    simp [List.filter, hx, hy, hz]

/-- The accepting challenge vectors number exactly the product of the per-repetition counts. -/
theorem czk_accepting_challenge_count (gs : List (CzkGate R)) (outs : List Nat) :
    ∀ reps : List (List (CzkGateCommit R) × List (Fin 3 → R)),
      ((czkChallenges reps.length).filter fun es => czkVerifyAll gs outs es reps).length =
        czkAcceptCount gs outs reps := by
  intro reps
  induction reps with
  | nil => rfl
  | cons r rs ih =>
    have pt : ∀ v0 v1 v2 q : Bool,
        (v0 && q).toNat + (v1 && q).toNat + (v2 && q).toNat =
          (v0.toNat + v1.toNat + v2.toNat) * q.toNat := by decide
    have aux : ∀ l : List (List (Fin 3)),
        ((l.flatMap fun es => [0 :: es, 1 :: es, 2 :: es]).filter
          fun es => czkVerifyAll gs outs es (r :: rs)).length =
        czkValidPairCount gs outs r * (l.filter fun es => czkVerifyAll gs outs es rs).length := by
      intro l
      induction l with
      | nil => rfl
      | cons es l ihl =>
        rw [List.flatMap_cons, List.filter_append, List.length_append, ihl, filter3_length]
        show (czkVerifyPair 0 outs r.2 gs r.1 czkEmptyWires 0 && czkVerifyAll gs outs es rs).toNat +
            (czkVerifyPair 1 outs r.2 gs r.1 czkEmptyWires 0 && czkVerifyAll gs outs es rs).toNat +
            (czkVerifyPair 2 outs r.2 gs r.1 czkEmptyWires 0 && czkVerifyAll gs outs es rs).toNat +
            _ = _
        rw [pt]
        have hcons : ((es :: l).filter fun es => czkVerifyAll gs outs es rs).length =
            (czkVerifyAll gs outs es rs).toNat +
              (l.filter fun es => czkVerifyAll gs outs es rs).length := by
          cases hq : czkVerifyAll gs outs es rs <;> simp [List.filter, hq]
          omega
        rw [hcons, Nat.mul_add]
        rfl
    show (((czkChallenges rs.length).flatMap fun es => [0 :: es, 1 :: es, 2 :: es]).filter
      fun es => czkVerifyAll gs outs es (r :: rs)).length = _
    rw [aux, ih]
    rfl

theorem czkAcceptCount_le (gs : List (CzkGate R)) (outs : List Nat)
    (hFalse : ∀ ws : List R, ¬ czkAccepts gs outs ws) :
    ∀ reps : List (List (CzkGateCommit R) × List (Fin 3 → R)),
      czkAcceptCount gs outs reps ≤ 2 ^ reps.length := by
  intro reps
  induction reps with
  | nil => exact Nat.le_refl 1
  | cons r rs ih =>
    calc czkValidPairCount gs outs r * czkAcceptCount gs outs rs
        ≤ 2 * 2 ^ rs.length :=
          Nat.mul_le_mul (cozk_false_statement_caught_at_least_one_pair gs outs hFalse r) ih
      _ = 2 ^ (rs.length + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

end CoZkCount

theorem cozk_438_classical_bound : 2 ^ 438 * 2 ^ 256 < 3 ^ 438 := by decide +kernel

theorem cozk_219_qrom_amplitude_bound : 2 ^ 219 * 2 ^ 128 < 3 ^ 219 := by decide +kernel

/-- `Q^2 (2/3)^438 < 1` for every `Q ≤ 2^128`: the Grover search arithmetic for challenge
grinding. -/
theorem cozk_438_grover_query_floor (Q : Nat) (hQ : Q ≤ 2 ^ 128) :
    Q * Q * 2 ^ 438 < 3 ^ 438 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul hQ hQ)) (by decide +kernel)

/-- **438 repetitions.** For a circuit no witness satisfies and any 438 committed repetitions,
the accepting challenge vectors are fewer than a `2^-256` fraction of all `3^438`; and for every
opened pair and any two witnesses each opened view has exactly one preimage under either. -/
theorem cozk_3party_active_soundness_and_2privacy {R : Type} [LawfulCommRing R] [DecidableEq R]
    (gs : List (CzkGate R)) (outs : List Nat)
    (hFalse : ∀ ws : List R, ¬ czkAccepts gs outs ws)
    (reps : List (List (CzkGateCommit R) × List (Fin 3 → R))) (hReps : reps.length = 438) :
    ((czkChallenges reps.length).filter fun es => czkVerifyAll gs outs es reps).length * 2 ^ 256 <
        (czkChallenges reps.length).length ∧
    ∀ (e : Fin 3) (w₁ w₂ : List R) (v : CzkView R gs),
      (∃ ρ : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₁ ρ = v ∧
        ∀ ρ' : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₁ ρ' = v → ρ' = ρ) ∧
      (∃ ρ : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₂ ρ = v ∧
        ∀ ρ' : CzkRand R gs, czkRunView e gs czkEmptyWires 0 w₂ ρ' = v → ρ' = ρ) := by
  refine ⟨?_, fun e w₁ w₂ v => cozk_opened_pair_uniform e gs w₁ w₂ v⟩
  have hle := czkAcceptCount_le gs outs hFalse reps
  rw [czk_accepting_challenge_count, czkChallenges_length, hReps]
  rw [hReps] at hle
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hle) cozk_438_classical_bound

/-! ## A tight false-statement execution

The circuit asserts `1 * 1 = 0`. Party zero changes its multiplication output
from one to zero; both other multiplication shares and all masks are zero.
-/

def czkTightCircuit : List (CzkGate Goldilocks) := [.const one, .mul 0 0]
def czkTightRep : List (CzkGateCommit Goldilocks) × List (Fin 3 → Goldilocks) :=
  ([⟨(fun p => if p = 0 then one else zero), fun _ => zero⟩,
    ⟨(fun _ => zero), fun _ => zero⟩], [fun _ => zero])

theorem tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs :
    (∀ ws, ¬ czkAccepts czkTightCircuit [1] ws) ∧
    czkValidPairCount czkTightCircuit [1] czkTightRep = 2 := by
  constructor
  · intro ws h
    have hf := h 1 (by simp)
    have hone : czkPlainEval czkTightCircuit (fun _ => zero) 0 ws 1 =
        (one : Goldilocks) := by
      simp [czkPlainEval, czkTightCircuit, czkPlainGate, LawfulCommRing.mul_one]
    rw [hone] at hf
    exact (by decide : (one : Goldilocks) ≠ zero) hf
  · decide +kernel

theorem cozk_tight_repetitions (n : Nat) :
    czkAcceptCount czkTightCircuit [1] (List.replicate n czkTightRep) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, czkAcceptCount,
      tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs.2, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

theorem cozk_438_exact_accepting_fraction :
    ((czkChallenges 438).filter fun es =>
      czkVerifyAll czkTightCircuit [1] es (List.replicate 438 czkTightRep)).length = 2 ^ 438 ∧
    (czkChallenges 438).length = 3 ^ 438 := by
  constructor
  · have h := czk_accepting_challenge_count czkTightCircuit [1] (List.replicate 438 czkTightRep)
    simpa only [List.length_replicate, cozk_tight_repetitions] using h
  · exact czkChallenges_length 438

/-! ## Inventory XOR and the short-tweak boundary

The missing subset supplies an entire domain-separated table of 256-bit PRF outputs.
The ideal table has independent entries. An enrolled batch reveals a function only of
its entries; changing any other entry leaves that batch unchanged. Real leakage is
bounded by a PRF distinguishing advantage, not asserted to be identically zero.
-/

def inventoryXorChild (known hidden : BitVec 256) : BitVec 256 := hidden ^^^ known

def inventoryTableMask {I : Type} (known : I → BitVec 256) :
    SimpleEquiv (I → BitVec 256) (I → BitVec 256) where
  toFun h := fun i => inventoryXorChild (known i) (h i)
  invFun h := fun i => inventoryXorChild (known i) (h i)
  left_inv h := by funext i; dsimp [inventoryXorChild]; bv_xor_cancel
  right_inv h := by funext i; dsimp [inventoryXorChild]; bv_xor_cancel

theorem inventory_ideal_table_uniform {I : Type} {C : Nat}
    (enum : SimpleEquiv (Fin C) (I → BitVec 256)) (known : I → BitVec 256)
    (test : (I → BitVec 256) → Nat) :
    qsum C (fun r => test ((inventoryTableMask known).toFun (enum.toFun r))) =
      qsum C (fun r => test (enum.toFun r)) :=
  qsum_bijection_invariant enum (inventoryTableMask known) test

/-- Every prescribed child table has exactly one hidden table, including an arbitrary
assignment outside the enrolled batch. There is no additive master in this path. -/
theorem inventory_batch_fiber_unique {I : Type} (known desired : I → BitVec 256) :
    ∃ hidden : I → BitVec 256, (∀ i, inventoryXorChild (known i) (hidden i) = desired i) ∧
      ∀ other : I → BitVec 256, (∀ i, inventoryXorChild (known i) (other i) = desired i) → other = hidden := by
  refine ⟨(inventoryTableMask known).invFun desired, ?_, ?_⟩
  · intro i; exact congrFun ((inventoryTableMask known).right_inv desired) i
  · intro other h
    have he : (inventoryTableMask known).toFun other = desired := funext h
    rw [← he, (inventoryTableMask known).left_inv]

def hdGameHits {X : Type} {N : Nat} (sample : Fin N → X) (test : X → Bool) : Nat :=
  qsum N (fun r => (test (sample r)).toNat)

def hdGameGap (a b : Nat) : Nat := (a - b) + (b - a)

/-- Generic postprocessing identity: the distinguisher for reconstructed child tables is the PRF
adversary that XORs the known components before invoking its caller. Same coins,
same advantage numerator; divide by `N > 0` for probabilities. No adaptive custody query
history, child leakage policy, or production subset-seed experiment is instantiated here. -/
theorem inventory_prf_game_hop {I : Type} {N : Nat}
    (real ideal : Fin N → I → BitVec 256) (known : I → BitVec 256)
    (test : (I → BitVec 256) → Bool) (epsilon : Nat)
    (hPRF : hdGameGap
      (hdGameHits real (fun table => test ((inventoryTableMask known).toFun table)))
      (hdGameHits ideal (fun table => test ((inventoryTableMask known).toFun table))) ≤ epsilon) :
    hdGameGap
      (hdGameHits (fun r => (inventoryTableMask known).toFun (real r)) test)
      (hdGameHits (fun r => (inventoryTableMask known).toFun (ideal r)) test) ≤ epsilon := hPRF




/-! ## Commitment binding and the Fiat–Shamir boundary

The production root hashes the ordered repetition roots, each of which hashes three
view commitments and all three output byte strings. Framing must be injective.
Binding compares two openings of the same root; it does not supply an opening of
an arbitrary digest and does not make an adversarially selected FS challenge uniform.
-/

/-- Constructive collision extractor for any injectively framed commitment layer. -/
theorem cozk_commitment_binding_extract {V : Type} [DecidableEq V]
    (H : Hash) (encode : V → List UInt8)
    (injective : ∀ a b, encode a = encode b → a = b)
    (before after : V) (same : H (encode before) = H (encode after)) :
    before = after ∨ Collision H := by
  by_cases he : before = after
  · exact Or.inl he
  · exact Or.inr (HashCollisionWitness.toCollision ⟨encode before, encode after, fun h => he (injective _ _ h), same⟩)

/-- If an unopened party is later opened differently under its committed digest,
these two framed view strings are a hash collision, independently of the challenge. -/
theorem cozk_unopened_view_equivocation_collision
    (H : Hash) (before after : List UInt8)
    (changed : before ≠ after) (bound : H before = H after) : Collision H :=
  HashCollisionWitness.toCollision ⟨before, after, changed, bound⟩

/-- Lift acceptance to the committed transcript or extract a collision. `encode`
is the canonical full transcript encoding at the layer being compared. For the
production hash tree this lemma is applied from root to repetition to party view. -/
theorem cozk_committed_challenge_soundness {R : Type} [LawfulCommRing R] [DecidableEq R]
    (gs : List (CzkGate R)) (outs : List Nat) (H : Hash)
    (encode : List (List (CzkGateCommit R) × List (Fin 3 → R)) → List UInt8)
    (injective : ∀ a b, encode a = encode b → a = b)
    (before after : List (List (CzkGateCommit R) × List (Fin 3 → R)))
    (es : List (Fin 3)) (same : H (encode before) = H (encode after))
    (accepted : czkVerifyAll gs outs es after = true) :
    czkVerifyAll gs outs es before = true ∨ Collision H := by
  by_cases he : encode before = encode after
  · exact Or.inl (by rw [injective _ _ he]; exact accepted)
  · exact Or.inr (HashCollisionWitness.toCollision ⟨encode before, encode after, he, same⟩)

/-- With binding fixed, the 438-repetition counting theorem applies. This is the
single uniform-challenge experiment. FS grinding needs a separate oracle-query
bound; collision resistance alone cannot remove its query factor. -/
theorem cozk_binding_fixed_438_bound {R : Type} [LawfulCommRing R] [DecidableEq R]
    (gs : List (CzkGate R)) (outs : List Nat)
    (hFalse : ∀ ws : List R, ¬ czkAccepts gs outs ws)
    (reps : List (List (CzkGateCommit R) × List (Fin 3 → R))) (hlen : reps.length = 438) :
    ((czkChallenges 438).filter (fun es => czkVerifyAll gs outs es reps)).length ≤ 2 ^ 438 := by
  have h := czkAcceptCount_le gs outs hFalse reps
  rw [← czk_accepting_challenge_count, hlen] at h
  exact h


/-- An explicit change of ideal coins at an un-enrolled child. Every enrolled
child remains identical, while the target seed is translated by an arbitrary delta. -/
theorem inventory_unenrolled_coin_transport {I : Type} [DecidableEq I]
    (enrolled : I → Bool) (j : I) (hj : enrolled j = false)
    (known hidden : I → BitVec 256) (delta : BitVec 256) :
    let shifted := (inventoryTableMask (fun i => if i = j then delta else 0)).toFun hidden
    (∀ i, enrolled i = true → inventoryXorChild (known i) (shifted i) =
      inventoryXorChild (known i) (hidden i)) ∧
    inventoryXorChild (known j) (shifted j) =
      inventoryXorChild (known j) (hidden j) ^^^ delta := by
  dsimp [inventoryTableMask, inventoryXorChild]
  constructor
  · intro i hi
    have hij : i ≠ j := by intro he; subst i; rw [hj] at hi; contradiction
    simp [hij]
  · simp only [↓reduceIte]
    bv_xor_cancel

/-- Exact uniform-coin transport, valid for arbitrary batch-view distinguishers. -/
theorem inventory_unenrolled_joint_distribution {I : Type} [DecidableEq I] {C : Nat}
    (enum : SimpleEquiv (Fin C) (I → BitVec 256)) (j : I) (delta : BitVec 256)
    (test : (I → BitVec 256) → Nat) :
    qsum C (fun r => test ((inventoryTableMask
      (fun i => if i = j then delta else 0)).toFun (enum.toFun r))) =
      qsum C (fun r => test (enum.toFun r)) :=
  inventory_ideal_table_uniform enum _ test

theorem hd_game_gap_triangle (a b c : Nat) :
    hdGameGap a c ≤ hdGameGap a b + hdGameGap b c := by
  unfold hdGameGap
  omega

/-- Compose PRF expansion and the public-image MLWE hop without silently replacing
short secrets by uniform field secrets. All games use the same finite denominator. -/
theorem hd_prf_mlwe_composed_bound (real cbd ideal prfBudget mlweBudget : Nat)
    (hPRF : hdGameGap real cbd ≤ prfBudget)
    (hMLWE : hdGameGap cbd ideal ≤ mlweBudget) :
    hdGameGap real ideal ≤ prfBudget + mlweBudget :=
  Nat.le_trans (hd_game_gap_triangle real cbd ideal) (Nat.add_le_add hPRF hMLWE)


/-- A batch adversary's real target-translation advantage is at most the sum of
two PRF advantages. The middle ideal games are equal by the explicit coin bijection;
`inventory_unenrolled_coin_transport` shows why the enrolled batch is unchanged. -/
theorem inventory_batch_privacy_prf_bound {I : Type} [DecidableEq I] {C : Nat}
    (enum : SimpleEquiv (Fin C) (I → BitVec 256))
    (real : Fin C → I → BitVec 256) (j : I) (delta : BitVec 256)
    (test : (I → BitVec 256) → Bool) (eps₀ eps₁ : Nat)
    (h₀ : hdGameGap (hdGameHits real test) (hdGameHits enum.toFun test) ≤ eps₀)
    (h₁ : hdGameGap
      (hdGameHits enum.toFun (fun t => test ((inventoryTableMask
        (fun i => if i = j then delta else 0)).toFun t)))
      (hdGameHits real (fun t => test ((inventoryTableMask
        (fun i => if i = j then delta else 0)).toFun t))) ≤ eps₁) :
    hdGameGap (hdGameHits real test)
      (hdGameHits real (fun t => test ((inventoryTableMask
        (fun i => if i = j then delta else 0)).toFun t))) ≤ eps₀ + eps₁ := by
  have hid := inventory_unenrolled_joint_distribution enum j delta (fun t => (test t).toNat)
  change hdGameHits enum.toFun (fun t => test ((inventoryTableMask
    (fun i => if i = j then delta else 0)).toFun t)) = hdGameHits enum.toFun test at hid
  rw [hid] at h₁
  exact hd_prf_mlwe_composed_bound _ _ _ _ _ h₀ h₁

/-- A repetition root includes the unopened third digest and all output strings.
The caller supplies the injective framing used for this tagged hash layer. -/
def czkRepetitionRoot (H : Hash) (frame : List (List UInt8) → List UInt8)
    (views : Fin 3 → List UInt8) (outputs : Fin 3 → List UInt8) : List UInt8 :=
  H (frame [H (views 0), H (views 1), H (views 2), outputs 0, outputs 1, outputs 2])

/-- Collision extraction descends through the repetition layer, including the
unopened view. No assumption that the unopened view is checked by replay is used. -/
theorem cozk_repetition_root_binds_hidden_view
    (H : Hash) (frame : List (List UInt8) → List UInt8)
    (inj : ∀ a b, frame a = frame b → a = b)
    (before after : Fin 3 → List UInt8) (oldOut newOut : Fin 3 → List UInt8)
    (p : Fin 3) (changed : before p ≠ after p)
    (same : czkRepetitionRoot H frame before oldOut =
      czkRepetitionRoot H frame after newOut) : Collision H := by
  let a := [H (before 0), H (before 1), H (before 2), oldOut 0, oldOut 1, oldOut 2]
  let b := [H (after 0), H (after 1), H (after 2), newOut 0, newOut 1, newOut 2]
  by_cases he : frame a = frame b
  · have hs := inj a b he
    have hv : ∀ p : Fin 3, H (before p) = H (after p) := by
      have hh : H (before 0) = H (after 0) ∧ H (before 1) = H (after 1) ∧
          H (before 2) = H (after 2) := by
        simp only [a, b, List.cons.injEq] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
      exact fin3_all hh.1 hh.2.1 hh.2.2
    exact HashCollisionWitness.toCollision ⟨before p, after p, changed, hv p⟩
  · exact HashCollisionWitness.toCollision ⟨frame a, frame b, he, same⟩

/-- Descend from the outer transcript root through a repetition root to a
changed party view. This covers the unopened third digest in the production
three-layer commitment layout, with injective domain/length framing explicit. -/
theorem cozk_transcript_root_binds_hidden_view
    (H : Hash) (outerFrame repFrame : List (List UInt8) → List UInt8)
    (outerInj : ∀ a b, outerFrame a = outerFrame b → a = b)
    (repInj : ∀ a b, repFrame a = repFrame b → a = b)
    (oldRoots newRoots : List (List UInt8)) (rep : Nat)
    (before after : Fin 3 → List UInt8) (oldOut newOut : Fin 3 → List UInt8)
    (oldAt : oldRoots[rep]? = some (czkRepetitionRoot H repFrame before oldOut))
    (newAt : newRoots[rep]? = some (czkRepetitionRoot H repFrame after newOut))
    (p : Fin 3) (changed : before p ≠ after p)
    (same : H (outerFrame oldRoots) = H (outerFrame newRoots)) : Collision H := by
  by_cases he : outerFrame oldRoots = outerFrame newRoots
  · have hl := outerInj oldRoots newRoots he
    rw [hl, newAt] at oldAt
    exact cozk_repetition_root_binds_hidden_view H repFrame repInj before after oldOut newOut
      p changed (Option.some.inj oldAt).symm
  · exact HashCollisionWitness.toCollision ⟨outerFrame oldRoots, outerFrame newRoots, he, same⟩

/-- Binding is not a guarantee of rejection after the challenge is known: pair
one accepts the fixed false transcript without any change to a commitment. -/
theorem tooth_cozk_binding_does_not_prevent_lucky_challenge :
    czkVerifyAll czkTightCircuit [1] [1] [czkTightRep] = true ∧
    (∀ H : Hash, ∀ encode :
      (List (CzkGateCommit Goldilocks) × List (Fin 3 → Goldilocks)) → List UInt8,
      H (encode czkTightRep) = H (encode czkTightRep)) := by
  constructor
  · decide +kernel
  · intros; rfl

theorem tooth_cozk_two_pairs_witness :
    ∃ rep, czkValidPairCount czkTightCircuit [1] rep = 2 ∧
      ∀ ws, ¬ czkAccepts czkTightCircuit [1] ws :=
  ⟨czkTightRep, tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs.2,
    tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs.1⟩

/-! ## Audits -/

#tooth_pair
  Qsag.cozk_false_statement_caught_at_least_one_pair
  vs
  Qsag.tooth_cozk_two_pairs_witness

#verify_constructive Qsag.inventory_batch_privacy_prf_bound




#verify_constructive Qsag.tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs
#verify_constructive Qsag.cozk_tight_repetitions
#verify_constructive Qsag.cozk_438_exact_accepting_fraction
#verify_constructive Qsag.inventory_ideal_table_uniform
#verify_constructive Qsag.inventory_batch_fiber_unique
#verify_constructive Qsag.inventory_prf_game_hop


#verify_constructive Qsag.cozk_commitment_binding_extract
#verify_constructive Qsag.cozk_unopened_view_equivocation_collision
#verify_constructive Qsag.cozk_committed_challenge_soundness
#verify_constructive Qsag.cozk_binding_fixed_438_bound

#verify_constructive Qsag.inventory_unenrolled_coin_transport
#verify_constructive Qsag.inventory_unenrolled_joint_distribution
#verify_constructive Qsag.hd_game_gap_triangle
#verify_constructive Qsag.hd_prf_mlwe_composed_bound

#verify_constructive Qsag.cozk_repetition_root_binds_hidden_view
#verify_constructive Qsag.cozk_transcript_root_binds_hidden_view
#verify_constructive Qsag.tooth_cozk_binding_does_not_prevent_lucky_challenge

#tooth_pair
  Qsag.hd_watch_only_subspace_isolation
  vs
  Qsag.tooth_unkeyed_public_tweak_pins_master

#tooth_pair
  Qsag.shamir_2of5_byzantine_unique_decoding
  vs
  Qsag.ambiguous_2of3_witness

#verify_inhabited
  Qsag.shamir_2of5_byzantine_unique_decoding
  Qsag.shamir_one_byzantine_inhabited

#verify_constructive
  Qsag.hd_state_unique_of_children
  Qsag.hd_watch_only_subspace_isolation
  Qsag.hd_unenrolled_fiber_card_exact
  Qsag.master_secret_recoverable
  Qsag.tooth_unkeyed_public_tweak_pins_master
  Qsag.hd_child_mac_forgery_pins_key
  Qsag.hd_child_mac_lanes_unique_forging_key
  Qsag.hd_child_mac_unforgeable_below_threshold
  Qsag.hd_child_mac_six_limb_bound
  Qsag.line_unique_of_two_points
  Qsag.line_unique_of_three_agree
  Qsag.decodeSharedConstant_sound
  Qsag.shamir_any_single_forgery_corrected
  Qsag.shamir_2of5_byzantine_unique_decoding
  Qsag.shamir_2of5_any_single_forgery_corrected
  Qsag.shamir_one_byzantine_inhabited
  Qsag.ambiguous_2of3_witness
  Qsag.cozk_opened_pair_uniform
  Qsag.cozk_three_valid_pairs_extract_witness
  Qsag.cozk_false_statement_caught_at_least_one_pair
  Qsag.cozk_corrupted_mul_wire_fails_owner_pair
  Qsag.cozk_preopen_sacrifice_sound
  Qsag.cozk_preopen_sacrifice_complete
  Qsag.czk_accepting_challenge_count
  Qsag.cozk_438_classical_bound
  Qsag.cozk_219_qrom_amplitude_bound
  Qsag.cozk_438_grover_query_floor
  Qsag.cozk_3party_active_soundness_and_2privacy

open Lean Elab Command in
run_cmd do
  let names : List Name := [
    ``Qsag.CustodyAlgebra.add_left_comm,
    ``Qsag.CustodyAlgebra.mul_left_comm,
    ``Qsag.CustodyAlgebra.add_sub_cancel,
    ``Qsag.CustodyAlgebra.sub_sub_self,
    ``Qsag.CustodyAlgebra.add_sub_add_left,
    ``Qsag.CustodyAlgebra.add_right_cancel,
    ``Qsag.CustodyAlgebra.eq_sub_of_add_eq,
    ``Qsag.CustodyAlgebra.sub_add_sub_cancel,
    ``Qsag.CustodyAlgebra.telescope3,
    ``Qsag.HdCustodyState,
    ``Qsag.hdChildSecret,
    ``Qsag.hdStateOfChildren,
    ``Qsag.hdChildSecret_stateOfChildren,
    ``Qsag.hdStateOfChildren_childSecret,
    ``Qsag.hd_state_unique_of_children,
    ``Qsag.hd_watch_only_subspace_isolation,
    ``Qsag.finProdEquiv,
    ``Qsag.finVecEquiv,
    ``Qsag.hdFieldFinEquiv,
    ``Qsag.hdLimbVecCardEquiv,
    ``Qsag.hdUnenrolledFiberEquiv,
    ``Qsag.hd_unenrolled_fiber_card_exact,
    ``Qsag.naiveBip32Child,
    ``Qsag.masterSecretRecoverable,
    ``Qsag.master_secret_recoverable,
    ``Qsag.tooth_unkeyed_public_tweak_pins_master,
    ``Qsag.hdMacVerify,
    ``Qsag.hd_child_mac_forgery_pins_key,
    ``Qsag.hd_child_mac_lanes_unique_forging_key,
    ``Qsag.hd_child_mac_unforgeable_below_threshold,
    ``Qsag.hd_child_mac_six_limb_bound,
    ``Qsag.lineAt,
    ``Qsag.lineAt_zero,
    ``Qsag.lineAt_diff,
    ``Qsag.line_unique_of_two_points,
    ``Qsag.lineThrough,
    ``Qsag.lineThrough_of_on_line,
    ``Qsag.count5,
    ``Qsag.count5_good,
    ``Qsag.count5_two,
    ``Qsag.count5_ge_four_of_all_but,
    ``Qsag.count5_le_one_of_all_but,
    ``Qsag.lineResponseAgrees,
    ``Qsag.lineResponseWrong,
    ``Qsag.OneFaultyLineResponse,
    ``Qsag.shamir_agree_not_wrong,
    ``Qsag.line_unique_of_three_agree,
    ``Qsag.all5,
    ``Qsag.all5_mem,
    ``Qsag.responseLineCandidates,
    ``Qsag.decodeSharedConstant,
    ``Qsag.decodeSharedConstant_sound,
    ``Qsag.shamir_any_single_forgery_corrected,
    ``Qsag.shamirEvaluationPoint,
    ``Qsag.shamirEvaluationPoint_distinct,
    ``Qsag.goldilocks_mul_inv,
    ``Qsag.shamir_2of5_byzantine_unique_decoding,
    ``Qsag.shamir_2of5_any_single_forgery_corrected,
    ``Qsag.shamir_one_byzantine_inhabited,
    ``Qsag.ambiguous_2of3_witness,
    ``Qsag.CzkGate,
    ``Qsag.CzkGateRand,
    ``Qsag.CzkGateView,
    ``Qsag.CzkRand,
    ``Qsag.CzkView,
    ``Qsag.CzkGateCommit,
    ``Qsag.czkMulProd,
    ``Qsag.czkMulShare,
    ``Qsag.czkEmptyWires,
    ``Qsag.czkPush,
    ``Qsag.czkSum3,
    ``Qsag.czkLocalShare,
    ``Qsag.czkInputShares,
    ``Qsag.czkMulShares,
    ``Qsag.czkGateShares,
    ``Qsag.czkGateView,
    ``Qsag.czkInputSim,
    ``Qsag.czkMulSim,
    ``Qsag.czkGateSim,
    ``Qsag.czkNextWit,
    ``Qsag.czkRunView,
    ``Qsag.czkSimRand,
    ``Qsag.fin3_cycle,
    ``Qsag.czkInputSim_view,
    ``Qsag.czkInputView_sim,
    ``Qsag.czkMulSim_view,
    ``Qsag.czkMulView_sim,
    ``Qsag.czkGateSim_view,
    ``Qsag.czkGateView_sim,
    ``Qsag.czkSimRand_runView,
    ``Qsag.czkRunView_simRand,
    ``Qsag.czk_view_fiber_unique,
    ``Qsag.cozk_opened_pair_uniform,
    ``Qsag.czkPlainGate,
    ``Qsag.czkPlainEval,
    ``Qsag.czkAccepts,
    ``Qsag.czkGateWitness,
    ``Qsag.czkExtractWitness,
    ``Qsag.czk_mul_sum,
    ``Qsag.czkPairGateOk,
    ``Qsag.czkOutputsOk,
    ``Qsag.czkVerifyPair,
    ``Qsag.fin3_all,
    ``Qsag.czk_gate_sum,
    ``Qsag.czk_circuit_sum,
    ``Qsag.czk_outputs_zero,
    ``Qsag.cozk_three_valid_pairs_extract_witness,
    ``Qsag.czkValidPairCount,
    ``Qsag.three_bools_le_two,
    ``Qsag.cozk_false_statement_caught_at_least_one_pair,
    ``Qsag.czkReplayWires,
    ``Qsag.czkVerifyPair_gate_ok,
    ``Qsag.cozk_corrupted_mul_wire_fails_owner_pair,
    ``Qsag.czkSacrificeResidual,
    ``Qsag.czkSacrificeResidual_eq,
    ``Qsag.cozk_preopen_sacrifice_sound,
    ``Qsag.cozk_preopen_sacrifice_complete,
    ``Qsag.czkVerifyAll,
    ``Qsag.czkAcceptCount,
    ``Qsag.czkChallenges,
    ``Qsag.czkChallenges_length,
    ``Qsag.filter3_length,
    ``Qsag.czk_accepting_challenge_count,
    ``Qsag.czkAcceptCount_le,
    ``Qsag.cozk_438_classical_bound,
    ``Qsag.cozk_219_qrom_amplitude_bound,
    ``Qsag.cozk_438_grover_query_floor,
    ``Qsag.cozk_3party_active_soundness_and_2privacy,
    ``Qsag.czkTightCircuit,
    ``Qsag.czkTightRep,
    ``Qsag.tooth_cozk_single_corrupt_mul_passes_exactly_two_pairs,
    ``Qsag.cozk_tight_repetitions,
    ``Qsag.cozk_438_exact_accepting_fraction,
    ``Qsag.inventoryXorChild,
    ``Qsag.inventoryTableMask,
    ``Qsag.inventory_ideal_table_uniform,
    ``Qsag.inventory_batch_fiber_unique,
    ``Qsag.hdGameHits,
    ``Qsag.hdGameGap,
    ``Qsag.inventory_prf_game_hop,
    ``Qsag.cozk_commitment_binding_extract,
    ``Qsag.cozk_unopened_view_equivocation_collision,
    ``Qsag.cozk_committed_challenge_soundness,
    ``Qsag.cozk_binding_fixed_438_bound,
    ``Qsag.inventory_unenrolled_coin_transport,
    ``Qsag.inventory_unenrolled_joint_distribution,
    ``Qsag.hd_game_gap_triangle,
    ``Qsag.hd_prf_mlwe_composed_bound,
    ``Qsag.inventory_batch_privacy_prf_bound,
    ``Qsag.czkRepetitionRoot,
    ``Qsag.cozk_repetition_root_binds_hidden_view,
    ``Qsag.cozk_transcript_root_binds_hidden_view,
    ``Qsag.tooth_cozk_binding_does_not_prevent_lucky_challenge,
    ``Qsag.tooth_cozk_two_pairs_witness]
  let mut rejected : Nat := 0
  for n in names do
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Quot.sound do
        logInfo m!"Rejected dependency: {n}: {ax}"
        rejected := rejected + 1
  if rejected != 0 then
    throwError m!"Module axiom audit rejected {rejected} dependencies"
  logInfo m!"Module axiom audit: {names.length} declarations, 0 rejected axioms"


end Qsag
end
