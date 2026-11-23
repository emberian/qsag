module
public import QsagWhirVerified.Proofs
public import Qsag.Math.QuinticExt5
public import Qsag.Math.Poseidon2Gl24
public import Qsag.Exec.Tactic.SimulationKit
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.PublicHemQuintic128
public import Qsag.Protocol.Aggregation.QuinticMultiStageWhir
import Qsag.Tactic.AssuranceKit
/-!
# Canonical `Qsag` Soundness and Refinement Welds for Quintic `Fp5` (`qsag-whir-verified`)

Transports the power-basis quintic MIR functions and refinement theorems in
`QsagWhirVerified.{Arithmetic,Proofs}` directly to the canonical `Qsag` mathematical
and protocol specifications in `Qsag.Math.QuinticExt5`, `Qsag.Math.Poseidon2Gl24`,
`Qsag.Protocol.Aggregation.Aggregation`, `Qsag.Protocol.Aggregation.HemRbrSoundness`,
`Qsag.Protocol.Aggregation.PublicHemQuintic128`, and `Qsag.Protocol.Aggregation.QuinticMultiStageWhir`:

1. **Field, Quintic `Fp5` & `Gl24Digest` Bijections (`fieldAbs`, `fp5Abs`, `gl24Abs`, `fp5Inv`):**
   Exact coordinatewise homomorphisms onto `Qsag.Goldilocks`, `Qsag.QuinticGoldilocks`
   (`F_p[X]/(X^5 - 3)`), and `Qsag.Poseidon2Gl24.Digest7`, including Frobenius (`frob`) and
   multiplicative inversion (`fp5_mul_fp5Inv_ok_one`).
2. **Canonical Wire Decoding (`load_le_u64_40`, `load_le_u64_56`, `decode_canonical_u64`,
   `decode_canonical_fp5_limbs`, `decode_canonical_fp5`, `decode_canonical_gl24_limbs`,
   `decode_canonical_gl24_digest`):**
   Exact refinement to `Qsag.Goldilocks`, `Qsag.QuinticGoldilocks`, and `Qsag.Poseidon2Gl24.Digest7`.
3. **Production Quintic WHIR Fold, Bridge, Sumcheck & Horner Gates:**
   Direct soundness welds into `Qsag.hemVirtualFoldOracle`, `Qsag.hemBridgeFoldClaim`,
   `Qsag.RoundPoly.evalCoeffs`, `Qsag.SuccinctWhirAgg.fiberPoint`, and Schwartz–Zippel root bounds
   over `Qsag.QuinticGoldilocks`.
4. **Canopy Merkle (`400`-bit & `Poseidon2-GL-w24`), OOD-Pin, & Quorum Sum Welds:**
   Direct welds into `Qsag.Aggregation.merkleNodeFrame`, `Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle`,
   `Fp5Refines`, `Gl24Refines`, and `U64NatRefines`.
-/

public section
namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std

/-! ## 0. Private Ring Dictionary Bridges -/

private theorem goldilocks_ring_add (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.add a b = Qsag.Goldilocks.add a b := rfl

private theorem goldilocks_ring_sub (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.sub a b = Qsag.Goldilocks.sub a b := rfl

private theorem goldilocks_ring_mul (a b : Qsag.Goldilocks) :
    Qsag.CommRingOps.mul a b = Qsag.Goldilocks.mul a b := rfl

/-! ## 1. Field, Quintic `Fp5` & `Gl24Digest` Homomorphisms (`fieldAbs`, `fp5Abs`, `gl24Abs`, `fp5Inv`) -/

/-- Representation map into canonical `Qsag.Goldilocks`. -/
@[expose] def fieldAbs (x : U64) : Qsag.Goldilocks := Qsag.Goldilocks.ofNat x.val

theorem fieldAbs_add (x y : U64) :
    fieldAbs (fieldAdd x y) = Qsag.Goldilocks.add (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldAdd_val,
    Qsag.Goldilocks.add_val, Qsag.goldilocksPrime, Nat.mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]

theorem fieldAbs_mul (x y : U64) :
    fieldAbs (fieldMul x y) = Qsag.Goldilocks.mul (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldMul_val,
    Qsag.Goldilocks.mul_val, Qsag.goldilocksPrime, Nat.mod_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]

theorem fieldAbs_sub (x y : U64) :
    fieldAbs (fieldSub x y) = Qsag.Goldilocks.sub (fieldAbs x) (fieldAbs y) := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, fieldSub_val,
    Qsag.Goldilocks.sub_val, Qsag.goldilocksPrime, Nat.mod_mod]
  rw [Nat.add_sub_assoc (Nat.le_of_lt (Nat.mod_lt y.val (by decide)))]
  exact (Nat.mod_add_mod _ _ _).symm

theorem fieldAbs_zero : fieldAbs 0#u64 = Qsag.Goldilocks.zero := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.zero_val]; rfl

theorem fieldAbs_one : fieldAbs 1#u64 = Qsag.Goldilocks.one := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.one_val]; rfl

theorem fieldAbs_three : fieldAbs 3#u64 = Qsag.QuinticGoldilocks.nonResidue := by
  apply Qsag.Goldilocks.ext
  simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.QuinticGoldilocks.nonResidue]; decide

/-- Direct power-basis `[1, X, X^2, X^3, X^4]` abstraction map into `Qsag.QuinticGoldilocks`. -/
@[expose] def fp5Abs (x : Fp5) : Qsag.QuinticGoldilocks :=
  ⟨fieldAbs x.c0, fieldAbs x.c1, fieldAbs x.c2, fieldAbs x.c3, fieldAbs x.c4⟩

/-- Direct 7-limb digest abstraction map into `Qsag.Poseidon2Gl24.Digest7`. -/
@[expose] def gl24Abs (d : Gl24Digest) : Qsag.Poseidon2Gl24.Digest7 :=
  ⟨fieldAbs d.l0, fieldAbs d.l1, fieldAbs d.l2, fieldAbs d.l3,
   fieldAbs d.l4, fieldAbs d.l5, fieldAbs d.l6⟩

theorem fp5Abs_zero : fp5Abs fp5Zero = Qsag.QuinticGoldilocks.zero := by
  apply Qsag.QuinticGoldilocks.ext <;> exact fieldAbs_zero

theorem fp5Abs_one : fp5Abs fp5One = Qsag.QuinticGoldilocks.one := by
  refine Qsag.QuinticGoldilocks.ext fieldAbs_one fieldAbs_zero fieldAbs_zero fieldAbs_zero fieldAbs_zero

theorem fp5Abs_fromBase (x : U64) :
    fp5Abs (fp5FromBase x) = Qsag.QuinticGoldilocks.ofBase (fieldAbs x) := by
  refine Qsag.QuinticGoldilocks.ext ?_ fieldAbs_zero fieldAbs_zero fieldAbs_zero fieldAbs_zero
  apply Qsag.Goldilocks.ext
  have hlt : x.val % 18446744069414584321 < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  change (BitVec.ofNat 64 (x.val % 18446744069414584321)).toNat % 18446744069414584321 =
    x.val % 18446744069414584321
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_mod]

theorem fp5Abs_add (x y : Fp5) :
    fp5Abs (fp5Add x y) = Qsag.QuinticGoldilocks.add (fp5Abs x) (fp5Abs y) := by
  apply Qsag.QuinticGoldilocks.ext <;>
    simp only [fp5Abs, fp5Add, fieldAbs_add, Qsag.QuinticGoldilocks.add, goldilocks_ring_add]

theorem fp5Abs_sub (x y : Fp5) :
    fp5Abs (fp5Sub x y) = Qsag.QuinticGoldilocks.sub (fp5Abs x) (fp5Abs y) := by
  apply Qsag.QuinticGoldilocks.ext <;>
    simp only [fp5Abs, fp5Sub, fieldAbs_sub, Qsag.QuinticGoldilocks.sub, goldilocks_ring_sub]

theorem fp5Abs_neg (x : Fp5) :
    fp5Abs (fp5Neg x) = Qsag.QuinticGoldilocks.neg (fp5Abs x) := by
  rw [fp5Neg, fp5Abs_sub, fp5Abs_zero, ← Qsag.QuinticGoldilocks.ring_sub,
    ← Qsag.QuinticGoldilocks.ring_zero, ← Qsag.QuinticGoldilocks.ring_neg,
    Qsag.LawfulCommRing.sub_eq_add_neg, Qsag.LawfulCommRing.zero_add]

theorem fp5Abs_scale (x : Fp5) (s : U64) :
    fp5Abs (fp5Scale x s) =
      Qsag.QuinticGoldilocks.mul (fp5Abs x) (Qsag.QuinticGoldilocks.ofBase (fieldAbs s)) := by
  apply Qsag.QuinticGoldilocks.ext <;>
    simp only [fp5Abs, fp5Scale, fieldAbs_mul, Qsag.QuinticGoldilocks.mul,
      Qsag.QuinticGoldilocks.mulWith, Qsag.QuinticGoldilocks.ofBase, ← goldilocks_ring_mul] <;>
    constructive_ring

theorem fp5Abs_mul (x y : Fp5) :
    fp5Abs (fp5Mul x y) = Qsag.QuinticGoldilocks.mul (fp5Abs x) (fp5Abs y) := by
  unfold fp5Abs fp5Mul Qsag.QuinticGoldilocks.mul Qsag.QuinticGoldilocks.mulWith
  dsimp only
  simp only [fieldAbs_add, fieldAbs_mul]
  have h3 : fieldAbs 3#u64 = Qsag.QuinticGoldilocks.nonResidue := fieldAbs_three
  change _ = _
  rw [show fieldAbs { bv := 3#64 } = Qsag.QuinticGoldilocks.nonResidue from h3]
  apply Qsag.QuinticGoldilocks.ext <;>
    simp only [← goldilocks_ring_add, ← goldilocks_ring_mul] <;>
    constructive_ring

theorem fp5Abs_frob (x : Fp5) :
    fp5Abs (fp5Frob x) = Qsag.QuinticGoldilocks.frob (fp5Abs x) := by
  have hz1 : fieldAbs 1041288259238279555#u64 = Qsag.QuinticGoldilocks.zeta := by
    apply Qsag.Goldilocks.ext
    rw [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.QuinticGoldilocks.zeta_val]; decide
  have hz2 : fieldAbs 15820824984080659046#u64 =
      Qsag.CommRingOps.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta := by
    apply Qsag.Goldilocks.ext
    rw [goldilocks_ring_mul, Qsag.Goldilocks.mul_val, Qsag.QuinticGoldilocks.zeta_val,
        fieldAbs, Qsag.Goldilocks.ofNat_val]; decide
  have hz3 : fieldAbs 211587555138949697#u64 =
      Qsag.CommRingOps.mul
        (Qsag.CommRingOps.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta)
        Qsag.QuinticGoldilocks.zeta := by
    apply Qsag.Goldilocks.ext
    rw [goldilocks_ring_mul, goldilocks_ring_mul, Qsag.Goldilocks.mul_val, Qsag.Goldilocks.mul_val,
        Qsag.QuinticGoldilocks.zeta_val, fieldAbs, Qsag.Goldilocks.ofNat_val]; decide
  have hz4 : fieldAbs 1373043270956696022#u64 =
      Qsag.CommRingOps.mul
        (Qsag.CommRingOps.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta)
        (Qsag.CommRingOps.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta) := by
    apply Qsag.Goldilocks.ext
    rw [goldilocks_ring_mul, goldilocks_ring_mul, Qsag.Goldilocks.mul_val, Qsag.Goldilocks.mul_val,
        Qsag.QuinticGoldilocks.zeta_val, fieldAbs, Qsag.Goldilocks.ofNat_val]; decide
  apply Qsag.QuinticGoldilocks.ext
  · rw [Qsag.QuinticGoldilocks.frob_c0]
    apply Qsag.Goldilocks.ext
    have hlt : x.c0.val % 18446744069414584321 < 2 ^ 64 :=
      Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
    change (BitVec.ofNat 64 (x.c0.val % 18446744069414584321)).toNat % 18446744069414584321 =
      x.c0.val % 18446744069414584321
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_mod]
  · rw [Qsag.QuinticGoldilocks.frob_c1]; simp only [fp5Abs, fp5Frob, fieldAbs_mul, hz1, ← goldilocks_ring_mul]
    exact Qsag.LawfulCommRing.mul_comm _ _
  · rw [Qsag.QuinticGoldilocks.frob_c2]; simp only [fp5Abs, fp5Frob, fieldAbs_mul, hz2, ← goldilocks_ring_mul]
    exact Qsag.LawfulCommRing.mul_comm _ _
  · rw [Qsag.QuinticGoldilocks.frob_c3]; simp only [fp5Abs, fp5Frob, fieldAbs_mul, hz3, ← goldilocks_ring_mul]
    exact Qsag.LawfulCommRing.mul_comm _ _
  · rw [Qsag.QuinticGoldilocks.frob_c4]; simp only [fp5Abs, fp5Frob, fieldAbs_mul, hz4, ← goldilocks_ring_mul]
    exact Qsag.LawfulCommRing.mul_comm _ _

/-- Canonical scalar encoding used at the verifier/twiddle boundary. -/
@[expose] def canonicalFieldWord (x : Qsag.Goldilocks) : U64 := ⟨BitVec.ofNat 64 x.val⟩

theorem canonicalFieldWord_val (x : Qsag.Goldilocks) :
    (canonicalFieldWord x).val = x.val := by
  simp only [canonicalFieldWord, UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Qsag.Goldilocks.val_lt_two_pow_64 x)

theorem isCanonical_canonicalFieldWord (x : Qsag.Goldilocks) :
    IsCanonical (canonicalFieldWord x) := by
  rw [IsCanonical, canonicalFieldWord_val]; exact x.isLt

theorem fieldAbs_canonicalFieldWord (x : Qsag.Goldilocks) :
    fieldAbs (canonicalFieldWord x) = x := by
  apply Qsag.Goldilocks.ext
  rw [fieldAbs, Qsag.Goldilocks.ofNat_val, canonicalFieldWord_val, Nat.mod_eq_of_lt x.isLt]

theorem canonicalFieldWord_fieldAbs {x : U64} (hx : IsCanonical x) :
    canonicalFieldWord (fieldAbs x) = x := by
  apply UScalar.eq_of_val_eq
  rw [canonicalFieldWord_val, fieldAbs, Qsag.Goldilocks.ofNat_val]
  exact Nat.mod_eq_of_lt hx

theorem fieldAbs_inj {x y : U64} (hx : IsCanonical x) (hy : IsCanonical y) :
    fieldAbs x = fieldAbs y ↔ x = y :=
  ⟨fun h => by rw [← canonicalFieldWord_fieldAbs hx, h, canonicalFieldWord_fieldAbs hy],
   congrArg fieldAbs⟩

/-- Canonical `Fp5` encoding of `Qsag.QuinticGoldilocks` (inverse of `fp5Abs`). -/
@[expose] def canonicalFp5 (z : Qsag.QuinticGoldilocks) : Fp5 :=
  ⟨canonicalFieldWord z.c0, canonicalFieldWord z.c1, canonicalFieldWord z.c2,
   canonicalFieldWord z.c3, canonicalFieldWord z.c4⟩

theorem isCanonicalFp5_canonicalFp5 (z : Qsag.QuinticGoldilocks) :
    IsCanonicalFp5 (canonicalFp5 z) :=
  ⟨isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _⟩

theorem fp5Abs_canonicalFp5 (z : Qsag.QuinticGoldilocks) :
    fp5Abs (canonicalFp5 z) = z := by
  cases z
  simp only [fp5Abs, canonicalFp5, fieldAbs_canonicalFieldWord]

theorem canonicalFp5_fp5Abs {x : Fp5} (hx : IsCanonicalFp5 x) :
    canonicalFp5 (fp5Abs x) = x := by
  rcases hx with ⟨h0, h1, h2, h3, h4⟩
  cases x
  simp only [fp5Abs, canonicalFp5, canonicalFieldWord_fieldAbs h0, canonicalFieldWord_fieldAbs h1,
    canonicalFieldWord_fieldAbs h2, canonicalFieldWord_fieldAbs h3, canonicalFieldWord_fieldAbs h4]

theorem fp5Abs_inj {x y : Fp5} (hx : IsCanonicalFp5 x) (hy : IsCanonicalFp5 y) :
    fp5Abs x = fp5Abs y ↔ x = y :=
  ⟨fun h => by rw [← canonicalFp5_fp5Abs hx, h, canonicalFp5_fp5Abs hy], congrArg fp5Abs⟩

/-- Canonical `Gl24Digest` encoding of `Qsag.Poseidon2Gl24.Digest7` (inverse of `gl24Abs`). -/
@[expose] def canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) : Gl24Digest :=
  ⟨canonicalFieldWord d.d0, canonicalFieldWord d.d1, canonicalFieldWord d.d2,
   canonicalFieldWord d.d3, canonicalFieldWord d.d4, canonicalFieldWord d.d5,
   canonicalFieldWord d.d6⟩

theorem isCanonicalGl24_canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) :
    IsCanonicalGl24 (canonicalGl24 d) :=
  ⟨isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
   isCanonical_canonicalFieldWord _⟩

theorem gl24Abs_canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) :
    gl24Abs (canonicalGl24 d) = d := by
  cases d
  simp only [gl24Abs, canonicalGl24, fieldAbs_canonicalFieldWord]

theorem canonicalGl24_gl24Abs {d : Gl24Digest} (hd : IsCanonicalGl24 d) :
    canonicalGl24 (gl24Abs d) = d := by
  rcases hd with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  cases d
  simp only [gl24Abs, canonicalGl24, canonicalFieldWord_fieldAbs h0, canonicalFieldWord_fieldAbs h1,
    canonicalFieldWord_fieldAbs h2, canonicalFieldWord_fieldAbs h3, canonicalFieldWord_fieldAbs h4,
    canonicalFieldWord_fieldAbs h5, canonicalFieldWord_fieldAbs h6]

theorem gl24Abs_inj {a b : Gl24Digest} (ha : IsCanonicalGl24 a) (hb : IsCanonicalGl24 b) :
    gl24Abs a = gl24Abs b ↔ a = b :=
  ⟨fun h => by rw [← canonicalGl24_gl24Abs ha, h, canonicalGl24_gl24Abs hb], congrArg gl24Abs⟩

/-- Canonical multiplicative inverse on MIR `Fp5`, transported from `LawfulField.inv` on `QuinticGoldilocks`. -/
@[expose] def fp5Inv (x : Fp5) : Fp5 :=
  canonicalFp5 (Qsag.LawfulField.inv (fp5Abs x))

theorem isCanonicalFp5_fp5Inv (x : Fp5) : IsCanonicalFp5 (fp5Inv x) :=
  isCanonicalFp5_canonicalFp5 _

theorem fp5Abs_inv (x : Fp5) :
    fp5Abs (fp5Inv x) = Qsag.LawfulField.inv (fp5Abs x) :=
  fp5Abs_canonicalFp5 _

private theorem isCanonicalFp5_fp5One : IsCanonicalFp5 fp5One :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Extracted `fp5_mul` cancels `fp5Inv` to `fp5One` for every nonzero quintic field element. -/
theorem fp5_mul_fp5Inv_ok_one {x : Fp5}
    (hz : fp5Abs x ≠ Qsag.QuinticGoldilocks.zero) :
    fp5_mul x (fp5Inv x) = .ok fp5One := by
  rw [fp5_mul_refines]
  congr 1
  apply (fp5Abs_inj (fp5Mul_canonical x (fp5Inv x)) isCanonicalFp5_fp5One).mp
  rw [fp5Abs_mul, fp5Abs_inv, fp5Abs_one, ← Qsag.QuinticGoldilocks.ring_mul,
      ← Qsag.QuinticGoldilocks.ring_one]
  exact Qsag.LawfulField.mul_inv_cancel (by rwa [Qsag.QuinticGoldilocks.ring_zero])

/-- Canonical discharge of `hit : fieldMul 2#u64 it = 1#u64`. -/
theorem canonicalFieldWord_two_inv :
    fieldMul 2#u64 (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))) = 1#u64 := by
  apply (fieldAbs_inj (fieldMul_canonical _ _) (by decide : IsCanonical 1#u64)).mp
  rw [fieldAbs_mul, fieldAbs_canonicalFieldWord, fieldAbs_one]
  have h2 : fieldAbs 2#u64 = Qsag.Goldilocks.ofNat 2 := rfl
  rw [h2, ← goldilocks_ring_mul, ← Qsag.Goldilocks.ring_one]
  exact Qsag.Goldilocks.mul_inv_cancel (by decide)

/-- Canonical discharge of `hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64` for `x ≠ 0`. -/
theorem canonicalFieldWord_two_x_inv {x : Qsag.Goldilocks} (hx : x ≠ Qsag.Goldilocks.zero) :
    fieldMul (fieldMul 2#u64 (canonicalFieldWord x))
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))) = 1#u64 := by
  apply (fieldAbs_inj (fieldMul_canonical _ _) (by decide : IsCanonical 1#u64)).mp
  rw [fieldAbs_mul, fieldAbs_mul, fieldAbs_canonicalFieldWord, fieldAbs_canonicalFieldWord,
    fieldAbs_one]
  have h2 : fieldAbs 2#u64 = Qsag.Goldilocks.ofNat 2 := rfl
  rw [h2, ← goldilocks_ring_mul, ← goldilocks_ring_mul, ← goldilocks_ring_mul,
    ← Qsag.Goldilocks.ring_one]
  have hc1 := Qsag.Goldilocks.mul_inv_cancel (show Qsag.Goldilocks.ofNat 2 ≠ Qsag.Goldilocks.zero by decide)
  have hc2 := Qsag.Goldilocks.mul_inv_cancel hx
  calc
    Qsag.CommRingOps.mul (Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2) x)
        (Qsag.CommRingOps.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
      = Qsag.CommRingOps.mul
          (Qsag.CommRingOps.mul (Qsag.Goldilocks.ofNat 2)
            (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
          (Qsag.CommRingOps.mul x (Qsag.Goldilocks.inv x)) := by constructive_ring
    _ = Qsag.CommRingOps.mul Qsag.CommRingOps.one Qsag.CommRingOps.one := by rw [hc1, hc2]
    _ = Qsag.CommRingOps.one := Qsag.LawfulCommRing.one_mul _

/-! ## 2. Canonical Wire Decoding Welds (`load_le_u64_*`, `decode_canonical_*`) -/

theorem load_le_u64_40_refines_qsag (bytes : Array U8 40#usize) (off : Usize) :
    (fieldAbs <$> load_le_u64_40 bytes off) =
      .ok (if 32 < off.val then Qsag.Goldilocks.zero
           else Qsag.Goldilocks.ofNat (lePackU64At bytes.val off.val).val) := by
  rw [load_le_u64_40_spec]
  change Result.ok (fieldAbs (if 32 < off.val then 0#u64 else lePackU64At bytes.val off.val)) = _
  by_cases h : 32 < off.val
  · rw [ite_eq_left h, ite_eq_left h, fieldAbs_zero]
  · rw [ite_eq_right h, ite_eq_right h]; rfl

theorem load_le_u64_56_refines_qsag (bytes : Array U8 56#usize) (off : Usize) :
    (fieldAbs <$> load_le_u64_56 bytes off) =
      .ok (if 48 < off.val then Qsag.Goldilocks.zero
           else Qsag.Goldilocks.ofNat (lePackU64At bytes.val off.val).val) := by
  rw [load_le_u64_56_spec]
  change Result.ok (fieldAbs (if 48 < off.val then 0#u64 else lePackU64At bytes.val off.val)) = _
  by_cases h : 48 < off.val
  · rw [ite_eq_left h, ite_eq_left h, fieldAbs_zero]
  · rw [ite_eq_right h, ite_eq_right h]; rfl

theorem decode_canonical_u64_refines_qsag (x : U64) :
    (Option.map fieldAbs <$> decode_canonical_u64 x) =
      .ok (if x.val < Qsag.goldilocksPrime then some (Qsag.Goldilocks.ofNat x.val) else none) := by
  rw [decode_canonical_u64_spec]
  change Result.ok (Option.map fieldAbs (if x.val < goldilocksMod then some x else none)) = _
  have hp : goldilocksMod = Qsag.goldilocksPrime := rfl
  rw [hp]
  by_cases h : x.val < Qsag.goldilocksPrime <;> simp [h, fieldAbs]

theorem decode_canonical_fp5_limbs_refines_qsag (c0 c1 c2 c3 c4 : U64) :
    (Option.map fp5Abs <$> decode_canonical_fp5_limbs c0 c1 c2 c3 c4) =
      .ok (if c0.val < Qsag.goldilocksPrime ∧ c1.val < Qsag.goldilocksPrime ∧
              c2.val < Qsag.goldilocksPrime ∧ c3.val < Qsag.goldilocksPrime ∧
              c4.val < Qsag.goldilocksPrime
           then some ⟨fieldAbs c0, fieldAbs c1, fieldAbs c2, fieldAbs c3, fieldAbs c4⟩
           else none) := by
  rw [decode_canonical_fp5_limbs_spec]
  change Result.ok (Option.map fp5Abs _) = _
  have hp : (IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4) ↔
      (c0.val < Qsag.goldilocksPrime ∧ c1.val < Qsag.goldilocksPrime ∧
       c2.val < Qsag.goldilocksPrime ∧ c3.val < Qsag.goldilocksPrime ∧
       c4.val < Qsag.goldilocksPrime) := Iff.rfl
  by_cases h : IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4
  · have h' := hp.mp h; simp [h, h', fp5Abs]
  · have h' : ¬ (c0.val < Qsag.goldilocksPrime ∧ c1.val < Qsag.goldilocksPrime ∧
        c2.val < Qsag.goldilocksPrime ∧ c3.val < Qsag.goldilocksPrime ∧
        c4.val < Qsag.goldilocksPrime) := fun hc => h (hp.mpr hc)
    simp [h, h']

theorem decode_canonical_fp5_limbs_canonicalFp5 (z : Qsag.QuinticGoldilocks) :
    decode_canonical_fp5_limbs
      (canonicalFieldWord z.c0) (canonicalFieldWord z.c1) (canonicalFieldWord z.c2)
      (canonicalFieldWord z.c3) (canonicalFieldWord z.c4) =
      .ok (some (canonicalFp5 z)) := by
  rw [decode_canonical_fp5_limbs_some_iff]
  exact ⟨isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
    isCanonical_canonicalFieldWord _, isCanonical_canonicalFieldWord _,
    isCanonical_canonicalFieldWord _, rfl⟩

theorem decode_canonical_fp5_refines_qsag (bytes : Array U8 40#usize) :
    (Option.map fp5Abs <$> decode_canonical_fp5 bytes) =
      (Option.map fp5Abs <$> decode_canonical_fp5_limbs
        (lePackU64At bytes.val 0) (lePackU64At bytes.val 8) (lePackU64At bytes.val 16)
        (lePackU64At bytes.val 24) (lePackU64At bytes.val 32)) ∧
      (∀ out, decode_canonical_fp5 bytes = .ok (some out) →
        fp5Abs out = (⟨fieldAbs (lePackU64At bytes.val 0), fieldAbs (lePackU64At bytes.val 8),
                       fieldAbs (lePackU64At bytes.val 16), fieldAbs (lePackU64At bytes.val 24),
                       fieldAbs (lePackU64At bytes.val 32)⟩ : Qsag.QuinticGoldilocks)) := by
  refine ⟨congrArg (Option.map fp5Abs <$> ·) (decode_canonical_fp5_spec bytes), fun out h => ?_⟩
  obtain ⟨_, rfl⟩ := (decode_canonical_fp5_some_iff bytes out).mp h
  rfl

theorem decode_canonical_gl24_limbs_refines_qsag (l0 l1 l2 l3 l4 l5 l6 : U64) :
    (Option.map gl24Abs <$> decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6) =
      .ok (if l0.val < Qsag.goldilocksPrime ∧ l1.val < Qsag.goldilocksPrime ∧
              l2.val < Qsag.goldilocksPrime ∧ l3.val < Qsag.goldilocksPrime ∧
              l4.val < Qsag.goldilocksPrime ∧ l5.val < Qsag.goldilocksPrime ∧
              l6.val < Qsag.goldilocksPrime
           then some (⟨fieldAbs l0, fieldAbs l1, fieldAbs l2, fieldAbs l3,
                       fieldAbs l4, fieldAbs l5, fieldAbs l6⟩ : Qsag.Poseidon2Gl24.Digest7)
           else none) := by
  rw [decode_canonical_gl24_limbs_spec]
  change Result.ok (Option.map gl24Abs _) = _
  have hp : IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ ↔
      (l0.val < Qsag.goldilocksPrime ∧ l1.val < Qsag.goldilocksPrime ∧
       l2.val < Qsag.goldilocksPrime ∧ l3.val < Qsag.goldilocksPrime ∧
       l4.val < Qsag.goldilocksPrime ∧ l5.val < Qsag.goldilocksPrime ∧
       l6.val < Qsag.goldilocksPrime) := Iff.rfl
  by_cases h : IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩
  · rw [ite_eq_left h, ite_eq_left (hp.mp h)]; rfl
  · rw [ite_eq_right h, ite_eq_right (mt hp.mpr h)]; rfl

theorem decode_canonical_gl24_digest_refines_qsag (bytes : Array U8 56#usize) :
    (Option.map gl24Abs <$> decode_canonical_gl24_digest bytes) =
      (Option.map gl24Abs <$> decode_canonical_gl24_limbs
        (lePackU64At bytes.val 0) (lePackU64At bytes.val 8) (lePackU64At bytes.val 16)
        (lePackU64At bytes.val 24) (lePackU64At bytes.val 32) (lePackU64At bytes.val 40)
        (lePackU64At bytes.val 48)) ∧
      (∀ out, decode_canonical_gl24_digest bytes = .ok (some out) →
        gl24Abs out = (⟨fieldAbs (lePackU64At bytes.val 0), fieldAbs (lePackU64At bytes.val 8),
                        fieldAbs (lePackU64At bytes.val 16), fieldAbs (lePackU64At bytes.val 24),
                        fieldAbs (lePackU64At bytes.val 32), fieldAbs (lePackU64At bytes.val 40),
                        fieldAbs (lePackU64At bytes.val 48)⟩ : Qsag.Poseidon2Gl24.Digest7)) := by
  refine ⟨congrArg (Option.map gl24Abs <$> ·) (decode_canonical_gl24_digest_spec bytes), fun out h => ?_⟩
  obtain ⟨_, rfl⟩ := (decode_canonical_gl24_digest_some_iff bytes out).mp h
  rfl

/-! ## 3. Canonical Quintic WHIR Fold Welds (`hemVirtualFoldOracle`, `duet_fold_fp5`, `cwyz_duet_fold_fp5`) -/

/-- Base-field inversion commutes with canonical embedding `Goldilocks ↪ QuinticGoldilocks`. -/
theorem ofBase_inv (a : Qsag.Goldilocks) :
    Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a) =
      Qsag.LawfulField.inv (Qsag.QuinticGoldilocks.ofBase a) := by
  by_cases ha : a = Qsag.Goldilocks.zero
  · subst ha
    have hz1 : Qsag.Goldilocks.inv Qsag.Goldilocks.zero = Qsag.Goldilocks.zero := rfl
    rw [hz1, ← Qsag.Goldilocks.ring_zero, Qsag.QuinticGoldilocks.ofBase_zero,
        Qsag.LawfulField.inv_zero]
  · let ea := Qsag.QuinticGoldilocks.ofBase a
    have hea : ea ≠ Qsag.CommRingOps.zero := fun h0 =>
      ha (Qsag.QuinticGoldilocks.ofBase_injective (h0.trans Qsag.QuinticGoldilocks.ofBase_zero.symm))
    have hmul : Qsag.CommRingOps.mul ea (Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a)) =
        Qsag.CommRingOps.one := by
      dsimp only [ea]
      rw [← Qsag.QuinticGoldilocks.ofBase_mul, Qsag.Goldilocks.mul_inv_cancel ha,
          Qsag.QuinticGoldilocks.ofBase_one]
    calc
      Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a)
        = Qsag.CommRingOps.mul Qsag.CommRingOps.one
            (Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a)) :=
          (Qsag.LawfulCommRing.one_mul _).symm
      _ = Qsag.CommRingOps.mul (Qsag.CommRingOps.mul (Qsag.LawfulField.inv ea) ea)
            (Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a)) := by
          rw [Qsag.LawfulCommRing.mul_comm (Qsag.LawfulField.inv ea) ea,
              Qsag.LawfulField.mul_inv_cancel hea]
      _ = Qsag.CommRingOps.mul (Qsag.LawfulField.inv ea)
            (Qsag.CommRingOps.mul ea (Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv a))) :=
          Qsag.LawfulCommRing.mul_assoc _ _ _
      _ = Qsag.LawfulField.inv ea := by rw [hmul, Qsag.LawfulCommRing.mul_one]

private theorem field_inv_mul {F : Type} [Qsag.LawfulField F] [Qsag.NoZeroDivisors F]
    [DecidableEq F] (a b : F) :
    Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b) =
      Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b) := by
  by_cases ha : a = Qsag.CommRingOps.zero
  · subst ha; rw [Qsag.LawfulCommRing.zero_mul, Qsag.LawfulField.inv_zero, Qsag.LawfulCommRing.zero_mul]
  · by_cases hb : b = Qsag.CommRingOps.zero
    · subst hb; rw [Qsag.LawfulCommRing.mul_zero, Qsag.LawfulField.inv_zero, Qsag.LawfulCommRing.mul_zero]
    · have hab : Qsag.CommRingOps.mul a b ≠ Qsag.CommRingOps.zero := fun h0 =>
        (Qsag.NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0).elim ha hb
      have hprod : Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a b)
          (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b)) =
          Qsag.CommRingOps.one := by
        calc
          _ = Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a (Qsag.LawfulField.inv a))
                (Qsag.CommRingOps.mul b (Qsag.LawfulField.inv b)) := by constructive_ring
          _ = Qsag.CommRingOps.mul Qsag.CommRingOps.one Qsag.CommRingOps.one := by
              rw [Qsag.LawfulField.mul_inv_cancel ha, Qsag.LawfulField.mul_inv_cancel hb]
          _ = Qsag.CommRingOps.one := Qsag.LawfulCommRing.one_mul _
      calc
        Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b)
          = Qsag.CommRingOps.mul (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b))
              (Qsag.CommRingOps.mul (Qsag.CommRingOps.mul a b)
                (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b))) := by
            rw [hprod, Qsag.LawfulCommRing.mul_one]
        _ = Qsag.CommRingOps.mul
              (Qsag.CommRingOps.mul (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b))
                (Qsag.CommRingOps.mul a b))
              (Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b)) := by
            constructive_ring
        _ = Qsag.CommRingOps.mul (Qsag.LawfulField.inv a) (Qsag.LawfulField.inv b) := by
            rw [Qsag.LawfulCommRing.mul_comm (Qsag.LawfulField.inv (Qsag.CommRingOps.mul a b)) _,
                Qsag.LawfulField.mul_inv_cancel hab, Qsag.LawfulCommRing.one_mul]

/-- Pure quintic duet fold specification over `Qsag.QuinticGoldilocks`. -/
@[expose] def hemDuetFoldFp5 (v0 v1 : Qsag.QuinticGoldilocks) (iy it : Qsag.Goldilocks)
    (alpha : Qsag.QuinticGoldilocks) : Qsag.QuinticGoldilocks :=
  let even := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.add v0 v1)
    (Qsag.QuinticGoldilocks.ofBase it)
  let odd := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.sub v0 v1)
    (Qsag.QuinticGoldilocks.ofBase iy)
  Qsag.QuinticGoldilocks.add odd (Qsag.QuinticGoldilocks.mul alpha even)

theorem duet_fold_fp5_refines_qsag (v0 v1 : Fp5) (iy it : U64) (alpha : Fp5) :
    (fp5Abs <$> duet_fold_fp5 v0 v1 iy it alpha) =
      .ok (hemDuetFoldFp5 (fp5Abs v0) (fp5Abs v1) (fieldAbs iy) (fieldAbs it) (fp5Abs alpha)) := by
  rw [duet_fold_fp5_refines]
  change Result.ok (fp5Abs (duetFp5Value v0 v1 iy it alpha)) = _
  simp only [duetFp5Value.public_eqs, fp5Abs_add, fp5Abs_sub, fp5Abs_mul, fp5Abs_scale,
    hemDuetFoldFp5]

/-- Extracted `cwyz_duet_fold_fp5` with canonical twiddles refines `Qsag.hemVirtualFoldOracle`
    over `Qsag.QuinticGoldilocks` directly. -/
theorem cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle
    (v0 v1 : Fp5) (x : Qsag.Goldilocks) (theta alpha beta : Fp5)
    (curDom foldDom : List Qsag.QuinticGoldilocks)
    (curOracle : Nat → Qsag.QuinticGoldilocks) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one = Qsag.QuinticGoldilocks.ofBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = fp5Abs v0)
    (hb : curOracle (2 * idx + 1) = fp5Abs v1) :
    (fp5Abs <$> cwyz_duet_fold_fp5 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.hemVirtualFoldOracle
        (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta) curDom foldDom curOracle idx) := by
  rw [cwyz_duet_fold_fp5_refines]
  change Result.ok (fp5Abs (cwyzFp5Value _ _ _ _ _ _ _ _)) = _
  simp only [cwyzFp5Value.public_eqs, fp5Abs_add, fp5Abs_sub, fp5Abs_mul, fp5Abs_scale,
    fieldAbs_canonicalFieldWord, Qsag.hemVirtualFoldOracle_def, hx, hy, ha, hb]
  apply congrArg Result.ok
  have htwo_g : Qsag.Goldilocks.ofNat 2 =
      Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.Goldilocks) Qsag.CommRingOps.one := by
    rw [goldilocks_ring_add, Qsag.Goldilocks.ring_one]; decide
  have htwo : Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.ofNat 2) =
      Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.QuinticGoldilocks) Qsag.CommRingOps.one := by
    rw [htwo_g, Qsag.QuinticGoldilocks.ofBase_add, Qsag.QuinticGoldilocks.ofBase_one]
  have hhalf : Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) =
      Qsag.LawfulField.inv (Qsag.CommRingOps.add
        (Qsag.CommRingOps.one : Qsag.QuinticGoldilocks) Qsag.CommRingOps.one) := by
    rw [ofBase_inv, htwo]
  have hinv2x : Qsag.QuinticGoldilocks.ofBase
      (Qsag.Goldilocks.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)) =
      Qsag.LawfulField.inv (Qsag.CommRingOps.mul
        (Qsag.CommRingOps.add (Qsag.CommRingOps.one : Qsag.QuinticGoldilocks) Qsag.CommRingOps.one)
        (Qsag.QuinticGoldilocks.ofBase x)) := by
    rw [← goldilocks_ring_mul, Qsag.QuinticGoldilocks.ofBase_mul, hhalf, ofBase_inv, ← field_inv_mul]
  rw [hhalf, hinv2x]
  simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_sub,
    ← Qsag.QuinticGoldilocks.ring_mul]
  constructive_ring

private theorem isCanonicalFp5_cwyzFp5Value
    (v0 v1 : Fp5) (iy it yy : U64) (theta alpha beta : Fp5) :
    IsCanonicalFp5 (cwyzFp5Value v0 v1 iy it yy theta alpha beta) := by
  rw [cwyzFp5Value.public_eqs]; exact fp5Add_canonical _ _

private theorem isCanonicalFp5_duetFp5Value
    (v0 v1 : Fp5) (iy it : U64) (alpha : Fp5) :
    IsCanonicalFp5 (duetFp5Value v0 v1 iy it alpha) := by
  rw [duetFp5Value.public_eqs]; exact fp5Add_canonical _ _

private theorem isCanonicalFp5_cwyzBridgeFp5Value
    (w0 w1 w2 w3 w4 claim phi theta alpha beta : Fp5) :
    IsCanonicalFp5 (cwyzBridgeFp5Value w0 w1 w2 w3 w4 claim phi theta alpha beta) := by
  rw [cwyzBridgeFp5Value.public_eqs]; exact fp5Add_canonical _ _

theorem verify_cwyz_duet_fold_step_fp5_sound_qsag
    (v0 v1 : Fp5) (x : Qsag.Goldilocks) (theta alpha beta claimed : Fp5)
    (curDom foldDom : List Qsag.QuinticGoldilocks)
    (curOracle : Nat → Qsag.QuinticGoldilocks) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one = Qsag.QuinticGoldilocks.ofBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = fp5Abs v0)
    (hb : curOracle (2 * idx + 1) = fp5Abs v1) :
    verify_cwyz_duet_fold_step_fp5 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x))
      theta alpha beta claimed = .ok true ↔
      (IsCanonicalFp5 claimed ∧
       fp5Abs claimed = Qsag.hemVirtualFoldOracle
         (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta) curDom foldDom curOracle idx) := by
  rw [verify_cwyz_duet_fold_step_fp5_sound]
  have href := cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle
    v0 v1 x theta alpha beta curDom foldDom curOracle idx hx hy ha hb
  rw [cwyz_duet_fold_fp5_refines] at href
  have hval := Result.ok.inj href
  exact ⟨fun heq => by subst heq; exact ⟨isCanonicalFp5_cwyzFp5Value _ _ _ _ _ _ _ _, hval⟩,
         fun ⟨hcan, habs⟩ => (fp5Abs_inj hcan (isCanonicalFp5_cwyzFp5Value _ _ _ _ _ _ _ _)).mp
           (habs.trans hval.symm)⟩

theorem verify_affine_duet_fold_step_fp5_sound_qsag
    (v0 v1 : Fp5) (iy it : U64) (alpha claimed : Fp5) :
    verify_affine_duet_fold_step_fp5 v0 v1 iy it alpha claimed = .ok true ↔
      (IsCanonicalFp5 claimed ∧
       fp5Abs claimed = hemDuetFoldFp5 (fp5Abs v0) (fp5Abs v1) (fieldAbs iy) (fieldAbs it) (fp5Abs alpha)) := by
  rw [verify_affine_duet_fold_step_fp5_sound]
  have href := duet_fold_fp5_refines_qsag v0 v1 iy it alpha
  rw [duet_fold_fp5_refines] at href
  have hval := Result.ok.inj href
  exact ⟨fun heq => by subst heq; exact ⟨isCanonicalFp5_duetFp5Value _ _ _ _ _, hval⟩,
         fun ⟨hcan, habs⟩ => (fp5Abs_inj hcan (isCanonicalFp5_duetFp5Value _ _ _ _ _)).mp
           (habs.trans hval.symm)⟩

/-! ## 4. Constructive Schwartz–Zippel Root Bounds over `Qsag.QuinticGoldilocks` -/

private theorem evalCoeffs_const (c r : Qsag.QuinticGoldilocks) :
    Qsag.RoundPoly.evalCoeffs [c] r = c := by
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_nil,
    Qsag.LawfulCommRing.mul_zero, Qsag.LawfulCommRing.add_zero]

private theorem evalCoeffs_linear (a b r : Qsag.QuinticGoldilocks) :
    Qsag.RoundPoly.evalCoeffs [a, b] r =
      Qsag.QuinticGoldilocks.add a (Qsag.QuinticGoldilocks.mul r b) := by
  rw [Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const, Qsag.QuinticGoldilocks.ring_add,
    Qsag.QuinticGoldilocks.ring_mul]

private theorem filter_imp_length_le {α : Type} (p q : α → Bool)
    (himp : ∀ x, p x = true → q x = true) :
    ∀ xs : List α, (xs.filter p).length ≤ (xs.filter q).length
  | [] => Nat.le_refl 0
  | x :: xs => by
    simp only [List.filter_cons]
    cases hp : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases q x
      · exact filter_imp_length_le p q himp xs
      · exact Nat.le_succ_of_le (filter_imp_length_le p q himp xs)
    · rw [himp x hp]
      simp only [↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ (filter_imp_length_le p q himp xs)

theorem fp5_poly_roots_le_degree (maxDegree : Nat)
    (candA candB S : List Qsag.QuinticGoldilocks)
    (hS : S.Nodup) (hLenA : candA.length ≤ maxDegree + 1) (hLenB : candB.length ≤ maxDegree + 1)
    (hDiff : ∃ z₀ : Qsag.QuinticGoldilocks,
      Qsag.RoundPoly.evalCoeffs candA z₀ ≠ Qsag.RoundPoly.evalCoeffs candB z₀) :
    (S.filter (fun z => decide
      (Qsag.RoundPoly.evalCoeffs candA z = Qsag.RoundPoly.evalCoeffs candB z))).length ≤ maxDegree := by
  let diff := Qsag.polySubVar candA candB
  obtain ⟨z₀, hz₀⟩ := hDiff
  have hNz : ∃ z : Qsag.QuinticGoldilocks, Qsag.RoundPoly.evalCoeffs diff z ≠ Qsag.CommRingOps.zero :=
    ⟨z₀, fun h0 => hz₀ (Qsag.LawfulCommRing.sub_eq_zero_iff.mp (by rwa [Qsag.evalCoeffs_polySubVar] at h0))⟩
  have hBound := @Qsag.RoundPoly.roots_nodup_length_le Qsag.QuinticGoldilocks _ _
    (Qsag.LawfulField.toNoZeroDivisors Qsag.QuinticGoldilocks)
    maxDegree diff S hS (Qsag.polySubVar_length_le candA candB (maxDegree + 1) hLenA hLenB) hNz
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hBound
  intro z hz
  have hEq := of_decide_eq_true hz
  dsimp only [diff]
  rw [Qsag.evalCoeffs_polySubVar, hEq, Qsag.LawfulCommRing.sub_self]
  exact decide_eq_true rfl

theorem verify_affine_duet_fold_step_fp5_roots_le_one
    (v0 v1 claimed : Fp5) (iy it : U64)
    (S : List Qsag.QuinticGoldilocks) (hS : S.Nodup)
    (hne : ∃ r : Qsag.QuinticGoldilocks,
      hemDuetFoldFp5 (fp5Abs v0) (fp5Abs v1) (fieldAbs iy) (fieldAbs it) r ≠ fp5Abs claimed) :
    (S.filter (fun r => decide
      (verify_affine_duet_fold_step_fp5 v0 v1 iy it (canonicalFp5 r) claimed = .ok true))).length ≤ 1 := by
  let even := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.add (fp5Abs v0) (fp5Abs v1))
    (Qsag.QuinticGoldilocks.ofBase (fieldAbs it))
  let odd := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.sub (fp5Abs v0) (fp5Abs v1))
    (Qsag.QuinticGoldilocks.ofBase (fieldAbs iy))
  have heval : ∀ r : Qsag.QuinticGoldilocks,
      Qsag.RoundPoly.evalCoeffs [odd, even] r =
        hemDuetFoldFp5 (fp5Abs v0) (fp5Abs v1) (fieldAbs iy) (fieldAbs it) r :=
    fun r => evalCoeffs_linear odd even r
  obtain ⟨r₀, hr₀⟩ := hne
  have hbound := fp5_poly_roots_le_degree 1 [odd, even] [fp5Abs claimed] S hS (by simp) (by simp)
    ⟨r₀, by rw [heval, evalCoeffs_const]; exact hr₀⟩
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hbound
  intro r hr
  have hacc := of_decide_eq_true hr
  have hval := ((verify_affine_duet_fold_step_fp5_sound_qsag v0 v1 iy it (canonicalFp5 r) claimed).mp hacc).2
  rw [fp5Abs_canonicalFp5] at hval
  rw [heval, evalCoeffs_const]
  exact decide_eq_true hval.symm

/-! ## 5. Canonical CWYZ Bridge, Quadratic Sumcheck Wire & Horner Welds -/

theorem cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim
    (w0 w1 w2 w3 w4 claim phi theta alpha beta : Fp5) :
    (fp5Abs <$> cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta) =
      .ok (Qsag.hemBridgeFoldClaim
        (fp5Abs claim) (fp5Abs w0) (fp5Abs w1) (fp5Abs w2) (fp5Abs w3) (fp5Abs w4)
        (fp5Abs phi) (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta)) := by
  rw [cwyz_bridge_claim_step_fp5_refines]
  change Result.ok (fp5Abs (cwyzBridgeFp5Value _ _ _ _ _ _ _ _ _ _)) = _
  rw [cwyzBridgeFp5Value.public_eqs, Qsag.hemBridgeFoldClaim_def]
  simp only [fp5Abs_add, fp5Abs_sub, fp5Abs_mul,
    ← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_sub,
    ← Qsag.QuinticGoldilocks.ring_mul]
  exact congrArg Result.ok (by constructive_ring)

theorem verify_cwyz_bridge_claim_step_fp5_sound_qsag
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      (IsCanonicalFp5 claimed_next ∧
       fp5Abs claimed_next = Qsag.hemBridgeFoldClaim
         (fp5Abs claim) (fp5Abs w0) (fp5Abs w1) (fp5Abs w2) (fp5Abs w3) (fp5Abs w4)
         (fp5Abs phi) (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta)) := by
  rw [verify_cwyz_bridge_claim_step_fp5_sound]
  have href := cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim
    w0 w1 w2 w3 w4 claim phi theta alpha beta
  rw [cwyz_bridge_claim_step_fp5_refines] at href
  have hval := Result.ok.inj href
  exact ⟨fun heq => by subst heq; exact ⟨isCanonicalFp5_cwyzBridgeFp5Value _ _ _ _ _ _ _ _ _ _, hval⟩,
         fun ⟨hcan, habs⟩ => (fp5Abs_inj hcan (isCanonicalFp5_cwyzBridgeFp5Value _ _ _ _ _ _ _ _ _ _)).mp
           (habs.trans hval.symm)⟩

/-- Canonical quadratic coefficient list reconstructed by `eval_quadratic_sumcheck_wire_fp5`. -/
@[expose] def canonicalQuadraticWireFp5Poly (c0 c2 claim : Qsag.QuinticGoldilocks) :
    List Qsag.QuinticGoldilocks :=
  [c0, Qsag.QuinticGoldilocks.sub
         (Qsag.QuinticGoldilocks.sub claim (Qsag.QuinticGoldilocks.add c0 c0))
         c2, c2]

private theorem canonicalQuadraticWireFp5Poly_sum (a c s : Qsag.QuinticGoldilocks) :
    Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWireFp5Poly a c s) Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWireFp5Poly a c s) Qsag.CommRingOps.one) = s := by
  unfold canonicalQuadraticWireFp5Poly
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const,
    Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const]
  simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_sub]
  constructive_ring

theorem eval_quadratic_sumcheck_wire_fp5_refines_qsag
    (c0 c2 sum_claim r : Fp5) :
    (fp5Abs <$> eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim r) =
      .ok (Qsag.RoundPoly.evalCoeffs
        (canonicalQuadraticWireFp5Poly (fp5Abs c0) (fp5Abs c2) (fp5Abs sum_claim))
        (fp5Abs r)) := by
  rw [eval_quadratic_sumcheck_wire_fp5_refines]
  change Result.ok (fp5Abs (quadraticWireFp5Value c0 c2 sum_claim r)) = _
  rw [quadraticWireFp5Value.public_eqs, fp5Abs_add, fp5Abs_mul, fp5Abs_add,
    fp5Abs_mul, fp5Abs_sub, fp5Abs_sub, fp5Abs_add]
  unfold canonicalQuadraticWireFp5Poly
  rw [Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, evalCoeffs_const]
  simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_sub,
    ← Qsag.QuinticGoldilocks.ring_mul]
  exact congrArg Result.ok (by constructive_ring)

theorem eval_quadratic_sumcheck_wire_fp5_bad_challenges_le_two
    (G S : List Qsag.QuinticGoldilocks) (c0 c2 sum_claim : Fp5)
    (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : fp5Abs sum_claim ≠ Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.one)) :
    (S.filter (fun r => decide
      ((fp5Abs <$> eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim (canonicalFp5 r)) =
        .ok (Qsag.RoundPoly.evalCoeffs G r)))).length ≤ 2 := by
  let H := canonicalQuadraticWireFp5Poly (fp5Abs c0) (fp5Abs c2) (fp5Abs sum_claim)
  have hbound := Qsag.hemSumcheck_polynomial_collision_count 2 G H S (fp5Abs sum_claim)
    hS hG (Nat.le_refl 3) (canonicalQuadraticWireFp5Poly_sum _ _ _) hFalse
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hbound
  intro r hr
  have hacc := of_decide_eq_true hr
  rw [eval_quadratic_sumcheck_wire_fp5_refines_qsag, fp5Abs_canonicalFp5] at hacc
  exact decide_eq_true (Result.ok.inj hacc)

theorem hornerSpec_fp5_eq_evalCoeffs (coeffs : List Fp5) (z : U64) :
    fp5Abs (hornerSpec coeffs z fp5Zero) =
      Qsag.RoundPoly.evalCoeffs (coeffs.map fp5Abs) (Qsag.QuinticGoldilocks.ofBase (fieldAbs z)) := by
  induction coeffs with
  | nil =>
    rw [hornerSpec_nil, List.map_nil, Qsag.RoundPoly.evalCoeffs_nil, fp5Abs_zero]
    rfl
  | cons c rest ih =>
    rw [hornerSpec_cons, List.map_cons, Qsag.RoundPoly.evalCoeffs_cons,
        fp5Abs_add, fp5Abs_scale, ih]
    simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_mul]
    constructive_ring

theorem eval_fp5_univariate_at_base_refines_evalCoeffs (coeffs : Slice Fp5) (z : U64) :
    (fp5Abs <$> eval_fp5_univariate_at_base coeffs z) =
      .ok (Qsag.RoundPoly.evalCoeffs (coeffs.val.map fp5Abs)
        (Qsag.QuinticGoldilocks.ofBase (fieldAbs z))) := by
  rw [eval_fp5_univariate_at_base_spec]
  exact congrArg Result.ok (hornerSpec_fp5_eq_evalCoeffs coeffs.val z)

theorem verify_fp5_univariate_at_base_pin_sound_qsag
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5) :
    verify_fp5_univariate_at_base_pin coeffs z expected = .ok true ↔
      (IsCanonicalFp5 expected ∧
       fp5Abs expected = Qsag.RoundPoly.evalCoeffs (coeffs.val.map fp5Abs)
         (Qsag.QuinticGoldilocks.ofBase (fieldAbs z))) := by
  rw [verify_fp5_univariate_at_base_pin_sound]
  have hval := hornerSpec_fp5_eq_evalCoeffs coeffs.val z
  exact ⟨fun heq => by subst heq; exact ⟨hornerSpec_canonical coeffs.val z, hval⟩,
         fun ⟨hcan, habs⟩ => (fp5Abs_inj hcan (hornerSpec_canonical coeffs.val z)).mp
           (habs.trans hval.symm)⟩

private theorem nodup_map_of_inj {α β : Type} {f : α → β}
    (hinj : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj hinj h.2⟩
    intro hm
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
    exact h.1 (hinj y x heq ▸ hy)

theorem verify_fp5_univariate_at_base_pin_roots_le_degree
    (d : Nat) (candA candB : Slice Fp5) (S : List Qsag.Goldilocks)
    (hNodup : S.Nodup)
    (hLenA : candA.val.length ≤ d + 1) (hLenB : candB.val.length ≤ d + 1)
    (hDiff : ∃ z₀ : Qsag.QuinticGoldilocks,
      Qsag.RoundPoly.evalCoeffs (candA.val.map fp5Abs) z₀ ≠
        Qsag.RoundPoly.evalCoeffs (candB.val.map fp5Abs) z₀) :
    (S.filter (fun z =>
      let pinA := canonicalFp5 (Qsag.RoundPoly.evalCoeffs (candA.val.map fp5Abs)
        (Qsag.QuinticGoldilocks.ofBase z))
      decide (verify_fp5_univariate_at_base_pin candB (canonicalFieldWord z) pinA = .ok true))).length ≤ d := by
  let SE : List Qsag.QuinticGoldilocks := S.map Qsag.QuinticGoldilocks.ofBase
  have hSENodup : SE.Nodup :=
    nodup_map_of_inj (fun _ _ h => Qsag.QuinticGoldilocks.ofBase_injective h) hNodup
  have hBound := fp5_poly_roots_le_degree d (candA.val.map fp5Abs) (candB.val.map fp5Abs) SE hSENodup
    (by simpa [List.length_map] using hLenA) (by simpa [List.length_map] using hLenB) hDiff
  rw [List.filter_map, List.length_map] at hBound
  refine Nat.le_trans (filter_imp_length_le _ _ ?_ S) hBound
  intro z hz
  have hacc := of_decide_eq_true hz
  have eB := ((verify_fp5_univariate_at_base_pin_sound_qsag candB (canonicalFieldWord z) _).mp hacc).2
  rw [fp5Abs_canonicalFp5, fieldAbs_canonicalFieldWord] at eB
  exact decide_eq_true eB

/-! ## 6. Canonical OOD-Pin, Canopy Merkle (`400`-bit & `Gl24`), & Quorum Sum Welds -/

theorem verify_ood_pin_eq_fp5_canonical_iff_qsag
    {expected supplied : Fp5} (he : IsCanonicalFp5 expected) (hs : IsCanonicalFp5 supplied) :
    verify_ood_pin_eq_fp5 expected supplied = .ok true ↔ fp5Abs expected = fp5Abs supplied := by
  rw [verify_ood_pin_eq_fp5_sound]
  exact (fp5Abs_inj he hs).symm

theorem step_merkle_pair_order_400_canonical_parity
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) (pair : MerklePair400)
    (h : step_merkle_pair_order_400 idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧
    0 < Qsag.Aggregation.publicHemDigestCard .turboShake400 ∧
    8 * node.val.length = 400 ∧
    Qsag.encodeMultiFrame [pair.left.val.map (fun b => UInt8.ofNat b.val),
                           pair.right.val.map (fun b => UInt8.ofNat b.val)] =
      Qsag.Aggregation.merkleNodeFrame (idx.val / 2 ^ level.val)
        (node.val.map (fun b => UInt8.ofNat b.val))
        (sibling.val.map (fun b => UInt8.ofNat b.val)) := by
  obtain ⟨hlt, hord⟩ := (step_merkle_pair_order_400_some_iff idx level node sibling pair).mp h
  refine ⟨hlt, Qsag.Aggregation.publicHemDigestCard_pos .turboShake400,
    by rw [node.property]; rfl, ?_⟩
  rw [Nat.shiftRight_eq_div_pow] at hord
  rw [Qsag.Aggregation.merkleNodeFrame.public_eq_1]
  by_cases hpar : (idx.val / 2 ^ level.val) % 2 = 0
  · simp only [hpar, ↓reduceIte] at hord ⊢; rw [hord.1, hord.2]
  · simp only [hpar, ↓reduceIte] at hord ⊢; rw [hord.1, hord.2]

theorem step_merkle_pair_order_gl24_refines_poseidon2Gl24
    (idx : U64) (level : U32) (node sibling : Gl24Digest) (pair : MerklePairGl24)
    (tweak0 tweak1 : Qsag.Goldilocks)
    (h : step_merkle_pair_order_gl24 idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧ IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling ∧
    Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs pair.left) (gl24Abs pair.right)
      tweak0 tweak1 =
      (if (idx.val / 2 ^ level.val) % 2 = 0
       then Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs node) (gl24Abs sibling) tweak0 tweak1
       else Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs sibling) (gl24Abs node) tweak0 tweak1) := by
  obtain ⟨hlt, hn, hs, hord⟩ := (step_merkle_pair_order_gl24_some_iff idx level node sibling pair).mp h
  refine ⟨hlt, hn, hs, ?_⟩
  rw [Nat.shiftRight_eq_div_pow] at hord
  by_cases hpar : (idx.val / 2 ^ level.val) % 2 = 0
  · simp only [hpar, ↓reduceIte] at hord ⊢; rw [hord.1, hord.2]
  · simp only [hpar, ↓reduceIte] at hord ⊢; rw [hord.1, hord.2]

private theorem foldl_add_u64_eq_sum :
    ∀ (xs : List U64) (acc : Nat),
      xs.foldl (fun a x => a + x.val) acc = acc + (xs.map UScalar.val).sum
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_u64_eq_sum xs]
    omega

theorem checked_quorum_sum_sound_qsag
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      (counts.val ≠ [] ∧
       counts.val.length = minimums.val.length ∧
       0 < minimum_global.val ∧
       (∀ i (hi : i < counts.val.length) (hmi : i < minimums.val.length),
         0 < (minimums.val[i]'hmi).val ∧ (minimums.val[i]'hmi).val ≤ (counts.val[i]'hi).val) ∧
       total.val = (counts.val.map UScalar.val).sum ∧
       minimum_global.val ≤ total.val ∧
       (counts.val.map UScalar.val).sum < 2 ^ 64) := by
  rw [checked_quorum_sum_sound]
  unfold QuorumSumSpec
  have hsum : ∀ xs : List U64, natSumU64 xs = (xs.map UScalar.val).sum := by
    intro xs; unfold natSumU64; rw [foldl_add_u64_eq_sum, Nat.zero_add]
  rw [hsum]
  exact ⟨fun ⟨hne, hlen, hg, hall, htot, hle, hmin⟩ => ⟨hne, hlen, hg, hall, htot, hmin, by omega⟩,
         fun ⟨hne, hlen, hg, hall, htot, hmin, hlt⟩ => ⟨hne, hlen, hg, hall, htot, by omega, hmin⟩⟩

/-! ## 7. `#tooth` Mutation-Sensitivity & Premise-Inhabitedness Witness for Canonical `Fp5` Welds -/

theorem tooth_canonical_cwyz_fp5_fold_rejects_wrong_twiddle_and_forged_claim :
    let x := Qsag.Goldilocks.ofNat 3
    let v0 := canonicalFp5 Qsag.QuinticGoldilocks.one
    let v1 := canonicalFp5 Qsag.QuinticGoldilocks.zero
    let curDom := [Qsag.QuinticGoldilocks.ofBase x]
    let foldDom := [Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x)]
    let curO : Nat → Qsag.QuinticGoldilocks :=
      fun i => if i = 0 then Qsag.QuinticGoldilocks.one else Qsag.QuinticGoldilocks.zero
    let honest := Qsag.hemVirtualFoldOracle
      Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.zero
      curDom foldDom curO 0
    let forged := Qsag.QuinticGoldilocks.add honest Qsag.QuinticGoldilocks.one
    let iyGood := canonicalFieldWord (Qsag.Goldilocks.mul
      (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
    let iyBad := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let it := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let yy := canonicalFieldWord (Qsag.Goldilocks.mul x x)
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok true ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 forged) = .ok false ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyBad it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok false := by
  intro x v0 v1 curDom foldDom curO honest forged iyGood iyBad it yy
  have ha : curO (2 * 0) = fp5Abs v0 := by simp [curO, v0, fp5Abs_canonicalFp5]
  have hb : curO (2 * 0 + 1) = fp5Abs v1 := by simp [curO, v1, fp5Abs_canonicalFp5]
  have hAccept : verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok true := by
    apply (verify_cwyz_duet_fold_step_fp5_sound_qsag v0 v1 x fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) curDom foldDom curO 0 rfl rfl ha hb).mpr
    refine ⟨isCanonicalFp5_canonicalFp5 _, ?_⟩
    rw [fp5Abs_canonicalFp5, fp5Abs_zero]
  have hRejectForged : verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 forged) = .ok false := by
    rw [verify_cwyz_duet_fold_step_fp5_spec]
    congr 1; apply decide_eq_false; intro hEq
    have h1 : verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
        (canonicalFp5 forged) = .ok true := by
      rw [verify_cwyz_duet_fold_step_fp5_spec]; exact congrArg Result.ok (decide_eq_true hEq)
    have h2 := ((verify_cwyz_duet_fold_step_fp5_sound_qsag v0 v1 x fp5Zero fp5Zero fp5Zero
      (canonicalFp5 forged) curDom foldDom curO 0 rfl rfl ha hb).mp h1).2
    rw [fp5Abs_canonicalFp5, fp5Abs_zero] at h2
    have hsub := congrArg (fun w => Qsag.CommRingOps.sub w honest) h2
    have hlhs : Qsag.CommRingOps.sub forged honest = Qsag.QuinticGoldilocks.one := by
      dsimp only [forged]
      rw [← Qsag.QuinticGoldilocks.ring_add]; constructive_ring
    have hrhs : Qsag.CommRingOps.sub honest honest = Qsag.QuinticGoldilocks.zero :=
      Qsag.LawfulCommRing.sub_self honest
    exact Qsag.LawfulField.zero_ne_one (F := Qsag.QuinticGoldilocks) (hlhs.symm.trans (hsub.trans hrhs)).symm
  have hRejectTwiddle : verify_cwyz_duet_fold_step_fp5 v0 v1 iyBad it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok false := by
    rw [verify_cwyz_duet_fold_step_fp5_spec]
    congr 1; apply decide_eq_false; intro hEq
    have hGoodEq : cwyzFp5Value v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero = canonicalFp5 honest :=
      ((verify_cwyz_duet_fold_step_fp5_sound v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
        (canonicalFp5 honest)).mp hAccept).symm
    have hSame := congrArg fp5Abs (hEq.trans hGoodEq.symm)
    have hEval : ∀ iyW : U64,
        fp5Abs (cwyzFp5Value v0 v1 iyW it yy fp5Zero fp5Zero fp5Zero) =
          Qsag.QuinticGoldilocks.ofBase (fieldAbs iyW) := by
      intro iyW
      rw [cwyzFp5Value.public_eqs, fp5Abs_add, fp5Abs_mul, fp5Abs_add, fp5Abs_scale,
          fp5Abs_add, fp5Abs_mul, fp5Abs_scale, fp5Abs_scale, fp5Abs_sub,
          fp5Abs_zero]
      dsimp only [v0, v1]
      rw [fp5Abs_canonicalFp5, fp5Abs_canonicalFp5]
      simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_sub,
        ← Qsag.QuinticGoldilocks.ring_mul, ← Qsag.QuinticGoldilocks.ring_zero,
        ← Qsag.QuinticGoldilocks.ring_one]
      constructive_ring
    rw [hEval iyBad, hEval iyGood] at hSame
    have hBase := Qsag.QuinticGoldilocks.ofBase_injective hSame
    simp only [iyBad, iyGood, fieldAbs_canonicalFieldWord] at hBase
    exact absurd (congrArg Qsag.Goldilocks.val hBase) (by decide)
  exact ⟨hAccept, hRejectForged, hRejectTwiddle⟩

/-! ## 8. Composable `DataRefinement` (`FieldRefines`, `Fp5Refines`, `Gl24Refines`) & `WhirWp` Bridge -/

abbrev FieldRefines : Qsag.DataRefinement Qsag.Goldilocks U64 where
  Rel x w := IsCanonical w ∧ fieldAbs w = x

abbrev Fp5Refines : Qsag.DataRefinement Qsag.QuinticGoldilocks Fp5 where
  Rel z w := IsCanonicalFp5 w ∧ fp5Abs w = z

abbrev Gl24Refines : Qsag.DataRefinement Qsag.Poseidon2Gl24.Digest7 Gl24Digest where
  Rel d w := IsCanonicalGl24 w ∧ gl24Abs w = d

abbrev U64NatRefines : Qsag.DataRefinement Nat U64 where
  Rel n w := n = w.val

abbrev WhirWp {α : Type} (m : Result α) (post : α → Prop) : Prop :=
  ∃ v : α, m = .ok v ∧ post v

theorem whirWp_ok {α : Type} (v : α) (post : α → Prop) :
    WhirWp (.ok v) post ↔ post v :=
  ⟨fun ⟨_, hEq, hPost⟩ => by cases hEq; exact hPost, fun hPost => ⟨v, rfl, hPost⟩⟩

theorem whirWp_mono {α : Type} {m : Result α} {P Q : α → Prop}
    (h : WhirWp m P) (hImp : ∀ v, P v → Q v) : WhirWp m Q :=
  let ⟨v, hEq, hP⟩ := h; ⟨v, hEq, hImp v hP⟩

theorem FieldRefines_canonicalFieldWord (x : Qsag.Goldilocks) :
    FieldRefines.Rel x (canonicalFieldWord x) :=
  ⟨isCanonical_canonicalFieldWord x, fieldAbs_canonicalFieldWord x⟩

theorem FieldRefines_iff_eq_canonicalFieldWord (x : Qsag.Goldilocks) (w : U64) :
    FieldRefines.Rel x w ↔ w = canonicalFieldWord x :=
  ⟨fun ⟨hw, rfl⟩ => (canonicalFieldWord_fieldAbs hw).symm, fun h => h ▸ FieldRefines_canonicalFieldWord x⟩

theorem Fp5Refines_canonicalFp5 (z : Qsag.QuinticGoldilocks) :
    Fp5Refines.Rel z (canonicalFp5 z) :=
  ⟨isCanonicalFp5_canonicalFp5 z, fp5Abs_canonicalFp5 z⟩

theorem Fp5Refines_iff_eq_canonicalFp5 (z : Qsag.QuinticGoldilocks) (w : Fp5) :
    Fp5Refines.Rel z w ↔ w = canonicalFp5 z :=
  ⟨fun ⟨hw, rfl⟩ => (canonicalFp5_fp5Abs hw).symm, fun h => h ▸ Fp5Refines_canonicalFp5 z⟩

theorem Gl24Refines_canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) :
    Gl24Refines.Rel d (canonicalGl24 d) :=
  ⟨isCanonicalGl24_canonicalGl24 d, gl24Abs_canonicalGl24 d⟩

theorem fp5Add_rel2 :
    Qsag.Rel2 Fp5Refines Fp5Refines Fp5Refines Qsag.QuinticGoldilocks.add fp5Add := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩; exact ⟨fp5Add_canonical x y, fp5Abs_add x y⟩

theorem fp5Sub_rel2 :
    Qsag.Rel2 Fp5Refines Fp5Refines Fp5Refines Qsag.QuinticGoldilocks.sub fp5Sub := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩; exact ⟨fp5Sub_canonical x y, fp5Abs_sub x y⟩

theorem fp5Mul_rel2 :
    Qsag.Rel2 Fp5Refines Fp5Refines Fp5Refines Qsag.QuinticGoldilocks.mul fp5Mul := by
  rintro _ x _ y ⟨_, rfl⟩ ⟨_, rfl⟩; exact ⟨fp5Mul_canonical x y, fp5Abs_mul x y⟩

theorem fp5Frob_rel1 :
    Qsag.Rel1 Fp5Refines Fp5Refines Qsag.QuinticGoldilocks.frob fp5Frob := by
  rintro _ x ⟨_, rfl⟩; exact ⟨fp5Frob_canonical x, fp5Abs_frob x⟩

theorem fp5Inv_rel1 :
    Qsag.Rel1 Fp5Refines Fp5Refines Qsag.LawfulField.inv fp5Inv := by
  rintro _ x ⟨_, rfl⟩; exact ⟨isCanonicalFp5_fp5Inv x, fp5Abs_inv x⟩

theorem cwyz_bridge_claim_step_fp5_wp_fp5Refines
    {w0s w1s w2s w3s w4s claims phis thetas alphas betas : Qsag.QuinticGoldilocks}
    {w0 w1 w2 w3 w4 claim phi theta alpha beta : Fp5}
    (hw0 : Fp5Refines.Rel w0s w0) (hw1 : Fp5Refines.Rel w1s w1)
    (hw2 : Fp5Refines.Rel w2s w2) (hw3 : Fp5Refines.Rel w3s w3)
    (hw4 : Fp5Refines.Rel w4s w4) (hc : Fp5Refines.Rel claims claim)
    (hp : Fp5Refines.Rel phis phi) (ht : Fp5Refines.Rel thetas theta)
    (ha : Fp5Refines.Rel alphas alpha) (hb : Fp5Refines.Rel betas beta) :
    WhirWp (cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta)
      (Fp5Refines.Rel
        (Qsag.hemBridgeFoldClaim claims w0s w1s w2s w3s w4s phis thetas alphas betas)) := by
  have hRef := cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim
    w0 w1 w2 w3 w4 claim phi theta alpha beta
  rw [cwyz_bridge_claim_step_fp5_refines] at hRef ⊢
  rw [whirWp_ok]
  have hVal := Result.ok.inj hRef
  rw [hw0.2, hw1.2, hw2.2, hw3.2, hw4.2, hc.2, hp.2, ht.2, ha.2, hb.2] at hVal
  exact ⟨isCanonicalFp5_cwyzBridgeFp5Value w0 w1 w2 w3 w4 claim phi theta alpha beta, hVal⟩

theorem checked_quorum_sum_wp_u64NatRefines
    (counts minimums : Slice U64) (minimum_global : U64) :
    WhirWp (checked_quorum_sum counts minimums minimum_global)
      (fun out => ∀ total : U64, out = some total ↔
        (counts.val ≠ [] ∧
         counts.val.length = minimums.val.length ∧
         0 < minimum_global.val ∧
         (∀ i (hi : i < counts.val.length) (hmi : i < minimums.val.length),
           0 < (minimums.val[i]'hmi).val ∧ (minimums.val[i]'hmi).val ≤ (counts.val[i]'hi).val) ∧
         U64NatRefines.Rel (counts.val.map UScalar.val).sum total ∧
         minimum_global.val ≤ total.val ∧
         (counts.val.map UScalar.val).sum < 2 ^ 64)) := by
  obtain ⟨out, hOut⟩ := checked_quorum_sum_total counts minimums minimum_global
  refine ⟨out, hOut, fun total => ?_⟩
  have hIff := checked_quorum_sum_sound_qsag counts minimums minimum_global total
  rw [hOut, Result.ok.injEq] at hIff
  exact hIff.trans (by simp only [eq_comm (a := total.val)])

#verify_constructive
  fieldAbs_canonicalFieldWord
  fp5Abs_canonicalFp5
  gl24Abs_canonicalGl24
  fp5Abs_frob
  fp5Abs_inv
  fp5_mul_fp5Inv_ok_one
  canonicalFieldWord_two_inv
  canonicalFieldWord_two_x_inv
  load_le_u64_40_refines_qsag
  load_le_u64_56_refines_qsag
  decode_canonical_u64_refines_qsag
  decode_canonical_fp5_limbs_refines_qsag
  decode_canonical_fp5_refines_qsag
  decode_canonical_gl24_limbs_refines_qsag
  decode_canonical_gl24_digest_refines_qsag
  ofBase_inv
  duet_fold_fp5_refines_qsag
  cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle
  verify_cwyz_duet_fold_step_fp5_sound_qsag
  verify_affine_duet_fold_step_fp5_sound_qsag
  verify_affine_duet_fold_step_fp5_roots_le_one
  cwyz_bridge_claim_step_fp5_refines_hemBridgeFoldClaim
  verify_cwyz_bridge_claim_step_fp5_sound_qsag
  eval_quadratic_sumcheck_wire_fp5_refines_qsag
  eval_quadratic_sumcheck_wire_fp5_bad_challenges_le_two
  eval_fp5_univariate_at_base_refines_evalCoeffs
  verify_fp5_univariate_at_base_pin_sound_qsag
  verify_fp5_univariate_at_base_pin_roots_le_degree
  verify_ood_pin_eq_fp5_canonical_iff_qsag
  step_merkle_pair_order_400_canonical_parity
  step_merkle_pair_order_gl24_refines_poseidon2Gl24
  checked_quorum_sum_sound_qsag
  tooth_canonical_cwyz_fp5_fold_rejects_wrong_twiddle_and_forged_claim
  whirWp_ok
  whirWp_mono
  FieldRefines_canonicalFieldWord
  Fp5Refines_canonicalFp5
  Gl24Refines_canonicalGl24
  fp5Add_rel2
  fp5Sub_rel2
  fp5Mul_rel2
  fp5Frob_rel1
  fp5Inv_rel1
  cwyz_bridge_claim_step_fp5_wp_fp5Refines
  checked_quorum_sum_wp_u64NatRefines

end qsag_whir_verified.proofs
end
