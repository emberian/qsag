module
/-
# Qsag.Math.QuinticToom3 — 9-Triple Toom-3 `𝔽_{p^5} mod (u^5 - 3)` Interpolation Identity

Constructive (`0 sorry`, `0 axiom`, `0 Classical.choice`, `0 native_decide`) formalization of the
production 9-triple Toom-3 `QuinticGoldilocks` (`𝔽_{p^5} = 𝔽_p[u] / (u^5 - 3)`) multiplication
identity used by collaborative MPC `zk-Hem v2` (`crates/qsag-migrate/src/hem/collab/engine.rs:674-770`):
* Evaluates 5-limb inputs at `{0, 1, -1, 2, -2, 3, -3, 4, ∞}` (`toom3Eval9`),
* Performs **9** base-field Beaver-triple products (`toom3PointwiseMul`),
* Interpolates degree-8 even/odd parts via exact Newton divided differences and reduces modulo
  `u^5 - 3` (`toom3InterpGeneric`, `toom3MulFp5`),
* Proves exact ring equality `toom3MulFp5 x y = QuinticGoldilocks.mul x y` with 25-product
  schoolbook multiplication, share-linearity (`toom3Eval9_add`), and `#tooth_pair` mutation kill.
-/

public import Qsag.Math.QuinticExt5
import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

/-- Nine base-field evaluation slots `{0, 1, -1, 2, -2, 3, -3, 4, ∞}` (`EXT_MUL_TRIPLES = 9`). -/
structure Toom9Eval (R : Type) where
  v0 : R
  v1 : R
  vm1 : R
  v2 : R
  vm2 : R
  v3 : R
  vm3 : R
  v4 : R
  vinf : R
  deriving DecidableEq, Repr

/-- Evaluate `a0 + a1 u + a2 u² + a3 u³ + a4 u⁴` at `{0, ±1, ±2, ±3, 4, ∞}` (`collab/engine.rs:680-700`). -/
@[expose] def toom3Eval9Generic {R : Type} [LawfulCommRing R]
    (a0 a1 a2 a3 a4 : R) : Toom9Eval R :=
  let c := fun n : Nat => (CRing.natCast n : R)
  let e1 := a0 +ᵍ a2 +ᵍ a4
  let o1 := a1 +ᵍ a3
  let e2 := a0 +ᵍ c 4 *ᵍ a2 +ᵍ c 16 *ᵍ a4
  let o2 := c 2 *ᵍ a1 +ᵍ c 8 *ᵍ a3
  let e3 := a0 +ᵍ c 9 *ᵍ a2 +ᵍ c 81 *ᵍ a4
  let o3 := c 3 *ᵍ a1 +ᵍ c 27 *ᵍ a3
  let v4 := a0 +ᵍ c 4 *ᵍ a1 +ᵍ c 16 *ᵍ a2 +ᵍ c 64 *ᵍ a3 +ᵍ c 256 *ᵍ a4
  ⟨a0, e1 +ᵍ o1, e1 -ᵍ o1, e2 +ᵍ o2, e2 -ᵍ o2, e3 +ᵍ o3, e3 -ᵍ o3, v4, a4⟩

@[expose] def toom3Eval9 (x : QuinticGoldilocks) : Toom9Eval Goldilocks :=
  toom3Eval9Generic x.c0 x.c1 x.c2 x.c3 x.c4

@[expose] def toom3PointwiseMul {R : Type} [CommRingOps R]
    (x y : Toom9Eval R) : Toom9Eval R :=
  ⟨x.v0 *ᵍ y.v0, x.v1 *ᵍ y.v1, x.vm1 *ᵍ y.vm1, x.v2 *ᵍ y.v2, x.vm2 *ᵍ y.vm2,
   x.v3 *ᵍ y.v3, x.vm3 *ᵍ y.vm3, x.v4 *ᵍ y.v4, x.vinf *ᵍ y.vinf⟩

/-- Exact even/odd Newton divided-difference interpolation and reduction mod `u^5 - red`
    (`collab/engine.rs:724-767`), returning the 5 reduced limbs `(r0, r1, r2, r3, r4)`. -/
@[expose] def toom3InterpGeneric {R : Type} [LawfulCommRing R]
    (inv2 inv3 inv4 inv5 inv6 inv7 inv8 inv9 inv12 inv15 red : R)
    (v : Toom9Eval R) : R × R × R × R × R :=
  let c := fun n : Nat => (CRing.natCast n : R)
  let p0 := v.v0
  let p8 := v.vinf
  let s1 := (v.v1 +ᵍ v.vm1) *ᵍ inv2 -ᵍ p0 -ᵍ p8
  let s2 := ((v.v2 +ᵍ v.vm2) *ᵍ inv2 -ᵍ p0 -ᵍ p8 *ᵍ c 256) *ᵍ inv4
  let s3 := ((v.v3 +ᵍ v.vm3) *ᵍ inv2 -ᵍ p0 -ᵍ p8 *ᵍ c 6561) *ᵍ inv9
  let d01 := (s2 -ᵍ s1) *ᵍ inv3
  let d12 := (s3 -ᵍ s2) *ᵍ inv5
  let p6 := (d12 -ᵍ d01) *ᵍ inv8
  let p4 := d01 -ᵍ p6 *ᵍ c 5
  let p2 := s1 -ᵍ p4 -ᵍ p6
  let q1 := (v.v1 -ᵍ v.vm1) *ᵍ inv2
  let q2 := (v.v2 -ᵍ v.vm2) *ᵍ inv4
  let q3 := (v.v3 -ᵍ v.vm3) *ᵍ inv6
  let evenAt4 := p0 +ᵍ p2 *ᵍ c 16 +ᵍ p4 *ᵍ c 256 +ᵍ p6 *ᵍ c 4096 +ᵍ p8 *ᵍ c 65536
  let q4 := (v.v4 -ᵍ evenAt4) *ᵍ inv4
  let del0 := (q2 -ᵍ q1) *ᵍ inv3
  let del1 := (q3 -ᵍ q2) *ᵍ inv5
  let del2 := (q4 -ᵍ q3) *ᵍ inv7
  let del01 := (del1 -ᵍ del0) *ᵍ inv8
  let del12 := (del2 -ᵍ del1) *ᵍ inv12
  let p7 := (del12 -ᵍ del01) *ᵍ inv15
  let p5 := del01 -ᵍ p7 *ᵍ c 14
  let p3 := del0 -ᵍ del01 *ᵍ c 5 +ᵍ p7 *ᵍ c 49
  let p1 := q1 -ᵍ del0 +ᵍ del01 *ᵍ c 4 -ᵍ p7 *ᵍ c 36
  (p0 +ᵍ p5 *ᵍ red, p1 +ᵍ p6 *ᵍ red, p2 +ᵍ p7 *ᵍ red, p3 +ᵍ p8 *ᵍ red, p4)

@[expose] def toom3InterpMod (red : Goldilocks) (v : Toom9Eval Goldilocks) : QuinticGoldilocks :=
  let gInv := fun n : Nat => LawfulField.inv (CRing.natCast n : Goldilocks)
  let r := toom3InterpGeneric
    (gInv 2) (gInv 3) (gInv 4) (gInv 5) (gInv 6)
    (gInv 7) (gInv 8) (gInv 9) (gInv 12) (gInv 15) red v
  ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2⟩

/-- Production 9-triple Toom-3 `𝔽_{p^5}` multiplication modulo `u^5 - 3` (`collab/engine.rs:674-770`). -/
@[expose] def toom3MulFp5 (x y : QuinticGoldilocks) : QuinticGoldilocks :=
  toom3InterpMod QuinticGoldilocks.nonResidue (toom3PointwiseMul (toom3Eval9 x) (toom3Eval9 y))

private theorem cancelScale {R : Type} [LawfulCommRing R] {k ik target num : R}
    (hk : k *ᵍ ik = CommRingOps.one) (h : num = k *ᵍ target) : num *ᵍ ik = target := by
  calc num *ᵍ ik = (k *ᵍ target) *ᵍ ik := by rw [h]
    _ = target *ᵍ (k *ᵍ ik) := by constructive_ring
    _ = target *ᵍ CommRingOps.one := by rw [hk]
    _ = target := LawfulCommRing.mul_one target

/-- Polymorphic ring-level 9-point Toom-3 interpolation identity over any `[LawfulCommRing R]`. -/
theorem toom3InterpGeneric_eq_schoolbook {R : Type} [LawfulCommRing R]
    (i2 i3 i4 i5 i6 i7 i8 i9 i12 i15 red : R)
    (h2 : (CRing.natCast 2 : R) *ᵍ i2 = CommRingOps.one)
    (h3 : (CRing.natCast 3 : R) *ᵍ i3 = CommRingOps.one)
    (h4 : (CRing.natCast 4 : R) *ᵍ i4 = CommRingOps.one)
    (h5 : (CRing.natCast 5 : R) *ᵍ i5 = CommRingOps.one)
    (h6 : (CRing.natCast 6 : R) *ᵍ i6 = CommRingOps.one)
    (h7 : (CRing.natCast 7 : R) *ᵍ i7 = CommRingOps.one)
    (h8 : (CRing.natCast 8 : R) *ᵍ i8 = CommRingOps.one)
    (h9 : (CRing.natCast 9 : R) *ᵍ i9 = CommRingOps.one)
    (h12 : (CRing.natCast 12 : R) *ᵍ i12 = CommRingOps.one)
    (h15 : (CRing.natCast 15 : R) *ᵍ i15 = CommRingOps.one)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : R) :
    let v := toom3PointwiseMul (toom3Eval9Generic a0 a1 a2 a3 a4)
                               (toom3Eval9Generic b0 b1 b2 b3 b4)
    toom3InterpGeneric i2 i3 i4 i5 i6 i7 i8 i9 i12 i15 red v =
      (a0 *ᵍ b0 +ᵍ red *ᵍ (a1 *ᵍ b4 +ᵍ a2 *ᵍ b3 +ᵍ a3 *ᵍ b2 +ᵍ a4 *ᵍ b1),
       a0 *ᵍ b1 +ᵍ a1 *ᵍ b0 +ᵍ red *ᵍ (a2 *ᵍ b4 +ᵍ a3 *ᵍ b3 +ᵍ a4 *ᵍ b2),
       a0 *ᵍ b2 +ᵍ a1 *ᵍ b1 +ᵍ a2 *ᵍ b0 +ᵍ red *ᵍ (a3 *ᵍ b4 +ᵍ a4 *ᵍ b3),
       a0 *ᵍ b3 +ᵍ a1 *ᵍ b2 +ᵍ a2 *ᵍ b1 +ᵍ a3 *ᵍ b0 +ᵍ red *ᵍ (a4 *ᵍ b4),
       a0 *ᵍ b4 +ᵍ a1 *ᵍ b3 +ᵍ a2 *ᵍ b2 +ᵍ a3 *ᵍ b1 +ᵍ a4 *ᵍ b0) := by
  dsimp only [toom3InterpGeneric]
  let c := fun n : Nat => (CRing.natCast n : R)
  let v := toom3PointwiseMul (toom3Eval9Generic a0 a1 a2 a3 a4) (toom3Eval9Generic b0 b1 b2 b3 b4)
  let c0 := a0 *ᵍ b0
  let c1 := a0 *ᵍ b1 +ᵍ a1 *ᵍ b0
  let c2 := a0 *ᵍ b2 +ᵍ a1 *ᵍ b1 +ᵍ a2 *ᵍ b0
  let c3 := a0 *ᵍ b3 +ᵍ a1 *ᵍ b2 +ᵍ a2 *ᵍ b1 +ᵍ a3 *ᵍ b0
  let c4 := a0 *ᵍ b4 +ᵍ a1 *ᵍ b3 +ᵍ a2 *ᵍ b2 +ᵍ a3 *ᵍ b1 +ᵍ a4 *ᵍ b0
  let c5 := a1 *ᵍ b4 +ᵍ a2 *ᵍ b3 +ᵍ a3 *ᵍ b2 +ᵍ a4 *ᵍ b1
  let c6 := a2 *ᵍ b4 +ᵍ a3 *ᵍ b3 +ᵍ a4 *ᵍ b2
  let c7 := a3 *ᵍ b4 +ᵍ a4 *ᵍ b3
  let c8 := a4 *ᵍ b4
  have hp0 : v.v0 = c0 := rfl
  have hp8 : v.vinf = c8 := rfl
  have hv1p : (v.v1 +ᵍ v.vm1) *ᵍ i2 = c0 +ᵍ c2 +ᵍ c4 +ᵍ c6 +ᵍ c8 :=
    cancelScale h2 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c0, c2, c4, c6, c8]; constructive_ring)
  have hv2p : (v.v2 +ᵍ v.vm2) *ᵍ i2 = c0 +ᵍ c 4 *ᵍ c2 +ᵍ c 16 *ᵍ c4 +ᵍ c 64 *ᵍ c6 +ᵍ c 256 *ᵍ c8 :=
    cancelScale h2 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c, c0, c2, c4, c6, c8]; constructive_ring)
  have hv3p : (v.v3 +ᵍ v.vm3) *ᵍ i2 = c0 +ᵍ c 9 *ᵍ c2 +ᵍ c 81 *ᵍ c4 +ᵍ c 729 *ᵍ c6 +ᵍ c 6561 *ᵍ c8 :=
    cancelScale h2 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c, c0, c2, c4, c6, c8]; constructive_ring)
  have hs1 : (v.v1 +ᵍ v.vm1) *ᵍ i2 -ᵍ v.v0 -ᵍ v.vinf = c2 +ᵍ c4 +ᵍ c6 := by
    rw [hv1p, hp0, hp8]; constructive_ring
  have hs2 : ((v.v2 +ᵍ v.vm2) *ᵍ i2 -ᵍ v.v0 -ᵍ v.vinf *ᵍ c 256) *ᵍ i4 = c2 +ᵍ c 4 *ᵍ c4 +ᵍ c 16 *ᵍ c6 :=
    cancelScale h4 (by rw [hv2p, hp0, hp8]; dsimp only [c]; constructive_ring)
  have hs3 : ((v.v3 +ᵍ v.vm3) *ᵍ i2 -ᵍ v.v0 -ᵍ v.vinf *ᵍ c 6561) *ᵍ i9 = c2 +ᵍ c 9 *ᵍ c4 +ᵍ c 81 *ᵍ c6 :=
    cancelScale h9 (by rw [hv3p, hp0, hp8]; dsimp only [c]; constructive_ring)
  rw [hs1, hs2, hs3]
  have hd01 : ((c2 +ᵍ c 4 *ᵍ c4 +ᵍ c 16 *ᵍ c6) -ᵍ (c2 +ᵍ c4 +ᵍ c6)) *ᵍ i3 = c4 +ᵍ c 5 *ᵍ c6 :=
    cancelScale h3 (by dsimp only [c]; constructive_ring)
  have hd12 : ((c2 +ᵍ c 9 *ᵍ c4 +ᵍ c 81 *ᵍ c6) -ᵍ (c2 +ᵍ c 4 *ᵍ c4 +ᵍ c 16 *ᵍ c6)) *ᵍ i5 = c4 +ᵍ c 13 *ᵍ c6 :=
    cancelScale h5 (by dsimp only [c]; constructive_ring)
  rw [hd01, hd12]
  have hp6 : ((c4 +ᵍ c 13 *ᵍ c6) -ᵍ (c4 +ᵍ c 5 *ᵍ c6)) *ᵍ i8 = c6 :=
    cancelScale h8 (by dsimp only [c]; constructive_ring)
  rw [hp6]
  have hp4 : (c4 +ᵍ c 5 *ᵍ c6) -ᵍ c6 *ᵍ c 5 = c4 := by dsimp only [c]; constructive_ring
  have hp2 : (c2 +ᵍ c4 +ᵍ c6) -ᵍ c4 -ᵍ c6 = c2 := by constructive_ring
  rw [hp4, hp2, hp0, hp8]
  have hq1 : (v.v1 -ᵍ v.vm1) *ᵍ i2 = c1 +ᵍ c3 +ᵍ c5 +ᵍ c7 :=
    cancelScale h2 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c1, c3, c5, c7]; constructive_ring)
  have hq2 : (v.v2 -ᵍ v.vm2) *ᵍ i4 = c1 +ᵍ c 4 *ᵍ c3 +ᵍ c 16 *ᵍ c5 +ᵍ c 64 *ᵍ c7 :=
    cancelScale h4 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c, c1, c3, c5, c7]; constructive_ring)
  have hq3 : (v.v3 -ᵍ v.vm3) *ᵍ i6 = c1 +ᵍ c 9 *ᵍ c3 +ᵍ c 81 *ᵍ c5 +ᵍ c 729 *ᵍ c7 :=
    cancelScale h6 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c, c1, c3, c5, c7]; constructive_ring)
  have hq4 : (v.v4 -ᵍ (c0 +ᵍ c2 *ᵍ c 16 +ᵍ c4 *ᵍ c 256 +ᵍ c6 *ᵍ c 4096 +ᵍ c8 *ᵍ c 65536)) *ᵍ i4 =
      c1 +ᵍ c 16 *ᵍ c3 +ᵍ c 256 *ᵍ c5 +ᵍ c 4096 *ᵍ c7 :=
    cancelScale h4 (by dsimp only [v, toom3PointwiseMul, toom3Eval9Generic, c, c0, c1, c2, c3, c4, c5, c6, c7, c8]; constructive_ring)
  rw [hq1, hq2, hq3, hq4]
  have hdel0 : ((c1 +ᵍ c 4 *ᵍ c3 +ᵍ c 16 *ᵍ c5 +ᵍ c 64 *ᵍ c7) -ᵍ (c1 +ᵍ c3 +ᵍ c5 +ᵍ c7)) *ᵍ i3 =
      c3 +ᵍ c 5 *ᵍ c5 +ᵍ c 21 *ᵍ c7 := cancelScale h3 (by dsimp only [c]; constructive_ring)
  have hdel1 : ((c1 +ᵍ c 9 *ᵍ c3 +ᵍ c 81 *ᵍ c5 +ᵍ c 729 *ᵍ c7) -ᵍ
      (c1 +ᵍ c 4 *ᵍ c3 +ᵍ c 16 *ᵍ c5 +ᵍ c 64 *ᵍ c7)) *ᵍ i5 =
      c3 +ᵍ c 13 *ᵍ c5 +ᵍ c 133 *ᵍ c7 := cancelScale h5 (by dsimp only [c]; constructive_ring)
  have hdel2 : ((c1 +ᵍ c 16 *ᵍ c3 +ᵍ c 256 *ᵍ c5 +ᵍ c 4096 *ᵍ c7) -ᵍ
      (c1 +ᵍ c 9 *ᵍ c3 +ᵍ c 81 *ᵍ c5 +ᵍ c 729 *ᵍ c7)) *ᵍ i7 =
      c3 +ᵍ c 25 *ᵍ c5 +ᵍ c 481 *ᵍ c7 := cancelScale h7 (by dsimp only [c]; constructive_ring)
  rw [hdel0, hdel1, hdel2]
  have hdel01 : ((c3 +ᵍ c 13 *ᵍ c5 +ᵍ c 133 *ᵍ c7) -ᵍ (c3 +ᵍ c 5 *ᵍ c5 +ᵍ c 21 *ᵍ c7)) *ᵍ i8 =
      c5 +ᵍ c 14 *ᵍ c7 := cancelScale h8 (by dsimp only [c]; constructive_ring)
  have hdel12 : ((c3 +ᵍ c 25 *ᵍ c5 +ᵍ c 481 *ᵍ c7) -ᵍ (c3 +ᵍ c 13 *ᵍ c5 +ᵍ c 133 *ᵍ c7)) *ᵍ i12 =
      c5 +ᵍ c 29 *ᵍ c7 := cancelScale h12 (by dsimp only [c]; constructive_ring)
  rw [hdel01, hdel12]
  have hp7 : ((c5 +ᵍ c 29 *ᵍ c7) -ᵍ (c5 +ᵍ c 14 *ᵍ c7)) *ᵍ i15 = c7 :=
    cancelScale h15 (by dsimp only [c]; constructive_ring)
  rw [hp7]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))) <;>
    (dsimp only [c, c0, c1, c2, c3, c4, c5, c6, c7, c8]; constructive_ring)

private theorem goldilocks_natCast_inv_cancel (k : Nat)
    (h : decide ((CRing.natCast k : Goldilocks) ≠ CommRingOps.zero) = true) :
    (CRing.natCast k : Goldilocks) *ᵍ LawfulField.inv (CRing.natCast k : Goldilocks) =
      CommRingOps.one :=
  LawfulField.mul_inv_cancel (of_decide_eq_true h)

theorem toom3InterpMod_eq_mulWith (red : Goldilocks) (x y : QuinticGoldilocks) :
    toom3InterpMod red (toom3PointwiseMul (toom3Eval9 x) (toom3Eval9 y)) =
      QuinticGoldilocks.mulWith red x y := by
  dsimp only [toom3InterpMod, toom3Eval9, QuinticGoldilocks.mulWith]
  have hMain := toom3InterpGeneric_eq_schoolbook
    (LawfulField.inv (CRing.natCast 2 : Goldilocks))
    (LawfulField.inv (CRing.natCast 3 : Goldilocks))
    (LawfulField.inv (CRing.natCast 4 : Goldilocks))
    (LawfulField.inv (CRing.natCast 5 : Goldilocks))
    (LawfulField.inv (CRing.natCast 6 : Goldilocks))
    (LawfulField.inv (CRing.natCast 7 : Goldilocks))
    (LawfulField.inv (CRing.natCast 8 : Goldilocks))
    (LawfulField.inv (CRing.natCast 9 : Goldilocks))
    (LawfulField.inv (CRing.natCast 12 : Goldilocks))
    (LawfulField.inv (CRing.natCast 15 : Goldilocks))
    red
    (goldilocks_natCast_inv_cancel 2 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 3 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 4 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 5 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 6 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 7 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 8 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 9 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 12 (by decide +kernel))
    (goldilocks_natCast_inv_cancel 15 (by decide +kernel))
    x.c0 x.c1 x.c2 x.c3 x.c4 y.c0 y.c1 y.c2 y.c3 y.c4
  dsimp only at hMain
  rw [hMain]

/-- **Exact 9-Triple Toom-3 `𝔽_{p^5}` Multiplication Equivalence (`toom3MulFp5_eq_quinticMul`)**:
    `toom3MulFp5` (`9` base-field Beaver products over `{0, ±1, ±2, ±3, 4, ∞}` reduced mod
    `u^5 - 3`) agrees identically with 25-product schoolbook `QuinticGoldilocks.mul`! -/
theorem toom3MulFp5_eq_quinticMul (x y : QuinticGoldilocks) :
    toom3MulFp5 x y = QuinticGoldilocks.mul x y :=
  toom3InterpMod_eq_mulWith QuinticGoldilocks.nonResidue x y

/-- Linear share-additivity of `toom3Eval9` for MPC secret-shared inputs (`collab/engine.rs:680`). -/
theorem toom3Eval9_add (x y : QuinticGoldilocks) :
    let ex := toom3Eval9 x
    let ey := toom3Eval9 y
    toom3Eval9 (x +ᵍ y) =
      ⟨ex.v0 +ᵍ ey.v0, ex.v1 +ᵍ ey.v1, ex.vm1 +ᵍ ey.vm1, ex.v2 +ᵍ ey.v2,
       ex.vm2 +ᵍ ey.vm2, ex.v3 +ᵍ ey.v3, ex.vm3 +ᵍ ey.vm3, ex.v4 +ᵍ ey.v4,
       ex.vinf +ᵍ ey.vinf⟩ := by
  dsimp only [toom3Eval9, toom3Eval9Generic]
  simp only [QuinticGoldilocks.add_c0, QuinticGoldilocks.add_c1, QuinticGoldilocks.add_c2,
    QuinticGoldilocks.add_c3, QuinticGoldilocks.add_c4]
  congr 1 <;> constructive_ring

/-- `#tooth` Reducing the 9-triple Toom-3 interpolant modulo `u^5 - 1` (`Goldilocks.one`) instead
    of `u^5 - 3` (`QuinticGoldilocks.nonResidue`) disagrees with `QuinticGoldilocks.mul` at
    `x = X`, `y = X^4` (`1 ≠ 3`). -/
theorem tooth_toom3_wrong_reduction_ne_quinticMul :
    ¬ (∀ x y : QuinticGoldilocks,
      toom3InterpMod Goldilocks.one (toom3PointwiseMul (toom3Eval9 x) (toom3Eval9 y)) =
        QuinticGoldilocks.mul x y) := by
  intro hAll
  let u1 : QuinticGoldilocks := ⟨Goldilocks.zero, Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩
  let u4 : QuinticGoldilocks := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.one⟩
  have hSpec := hAll u1 u4
  rw [toom3InterpMod_eq_mulWith Goldilocks.one u1 u4] at hSpec
  have hC0 := congrArg QuinticGoldilocks.c0 hSpec
  revert hC0
  decide +kernel

#verify_constructive
  Qsag.toom3InterpGeneric_eq_schoolbook
  Qsag.toom3InterpMod_eq_mulWith
  Qsag.toom3MulFp5_eq_quinticMul
  Qsag.toom3Eval9_add
  Qsag.tooth_toom3_wrong_reduction_ne_quinticMul

#tooth_pair Qsag.toom3MulFp5_eq_quinticMul vs
  Qsag.tooth_toom3_wrong_reduction_ne_quinticMul

end Qsag
end
