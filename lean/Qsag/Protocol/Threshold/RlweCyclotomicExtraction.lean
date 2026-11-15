module
/-
# Qsag.Protocol.Threshold.RlweCyclotomicExtraction — Cyclotomic Signed-Monomial Cofactor & 13-Parallel RLWE OR-Sigma Extraction

Constructive, choice-free, kernel-checked formalization of signed-monomial challenge-difference
invertibility over power-of-two cyclotomic rings and 2-special-soundness relaxed RLWE/SIS witness
extraction for a 13-parallel Ring-LWE OR-Sigma protocol over the single signed-monomial challenge set,
together with the challenge-agnostic fork lemma and cofactor step that `Qsag.LatticePreprocessingFull`
applies to the production verifier of `crates/qsag-core/src/preprocessing.rs`:

1. **Parametric Negacyclic Ring Algebra (`NegacyclicPolyInt`, `CycPolyInt`, `ModZq`, `CycPolyZq`)**:
   - Arbitrary-modulus residue ring `ModZq q` ($\mathbb{Z}_q$) with surjective homomorphism `ModZq.ofInt`,
     centered representative `ModZq.centered`, and odd-modulus inverse `(q + 1) / 2` of `2`.
   - Degree-$< 2^\nu$ integer negacyclic ring $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ (`CycPolyInt nu`) and
     quotient ring $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ (`CycPolyZq nu q`) with proved commutativity,
     associativity, distributivity, $X^{2^\nu} = -1$, $\ell_1$-$\ell_\infty$ convolution bounds, and
     signed monomials `signedMonomial nu sign k` ($\pm X^k$).
2. **Exact Cyclotomic Signed-Monomial Cofactor Theorem (`signedMonomial_diff_mul_cofactor_eq_two`)**:
   - For any distinct signed monomials $c_1 \ne c_2$ in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$:
     * When $k_1 = k_2$ and $s_1 \ne s_2$, multiplying $c_1 - c_2 = \pm 2 X^{k_1}$ by $(\pm X^{k_1})^{-1}$
       ($\pm 1$ at $k_1 = 0$, $\mp X^{2^\nu - k_1}$ at $k_1 > 0$) yields $2$ identically with support weight $1$.
     * When $k_1 \ne k_2$, writing $d = |k_2 - k_1| = 2^a \cdot u$ ($u$ odd, $0 \le a < \nu$) and
       $m = 2^{\nu - a}$ (always even since $\nu - a \ge 1$), the explicit $\{-1, 0, +1\}$-coefficient
       geometric-sum cofactor $g(X)$ has support weight $m \le 2^\nu$, $\ell_\infty$ norm $1$, and satisfies
       $(c_1 - c_2) \circledast g(X) = 2$ in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$ prior to any mod-$q$ reduction.
   - **Pairwise Invertibility (`signedMonomial_challenge_set_pairwise_invertible`)**:
     For every odd modulus $q \ge 3$, $((q + 1) / 2) \cdot g(X) \bmod q$ is the exact two-sided inverse
     of $c_1 - c_2$ in $R_q$, covering all $2 \cdot 2^{10} = 2048$ challenges at $\nu = 10, N = 1024$.
3. **13-Parallel RLWE OR-Sigma Witness Extractors: Short Isometric Witness vs. Cofactor Fork Relation**:
   - Models the 13-parallel RLWE OR-Sigma relation (`c0 ⊕ c1 = c`, `A * zs_b + ze_b = t_b + c_b * u_b`
     in $R_q$, `‖zs_b‖_∞ ≤ B_z`, `‖ze_b‖_∞ ≤ B_z`), welded via `SignedMonomialChal.ofBitVec` to the
     production 11-bit signed-monomial challenge words (`poly_from_chal11` in `preprocessing.rs`).
   - **Signed-Monomial $\ell_\infty$ Isometry & Short Witness Extractor (`ShortMonomialRelaxedRlweWitness`,
     `extract_rlwe_or_sigma_13_short_witness`)**: multiplying by $(\pm X^k)^{-1}$ in $\mathbb{Z}[X]/(X^N+1)$
     is an exact $\ell_\infty$ isometry (`cycIntInfNorm_mul_negacyclicSignedMonomial_eq`), yielding
     $(s_{\mathrm{iso}}, e_{\mathrm{iso}}) = (c^{-1} \circledast \Delta z_s, c^{-1} \circledast \Delta z_e)$
     and sparse unit $r_{\mathrm{rel}} = 1 - c^{-1} \circledast c' \in R_q^\times$ (`‖r_rel‖_1 ≤ 2`) with
     **strictly sub-half-modulus norm** $\|s_{\mathrm{iso}}\|_\infty, \|e_{\mathrm{iso}}\|_\infty \le 2 B_z = 6140 < 6144 = \lfloor 12289 / 2 \rfloor$,
     satisfying $A \cdot s_{\mathrm{iso}} + e_{\mathrm{iso}} = r_{\mathrm{rel}} \cdot u_{i,b}$ and constructively
     either recovering the exact short integer secret $(s^*, e^*)$ or producing a non-zero Short Ring-SIS
     solution $A \cdot s_{\mathrm{sis}} + e_{\mathrm{sis}} \equiv 0 \pmod{12289}$ of $\ell_\infty \le 6142 < 6144$
     (`short_monomial_witness_recovers_secret_or_breaks_short_sis`).
   - **Cofactor Fork Relation (`ExtractedRlweOrSigmaWitness`, `extract_rlwe_or_sigma_13_witness`)**:
     multiplying $(\Delta z_s, \Delta z_e)$ by the dense geometric cofactor $g$ gives $A \cdot s_2 + e_2 \equiv 2 \cdot u_{i,b} \pmod q$
     with $\|s_2\|_\infty \le 2 N B_z$ (`6287360` at $N = 1024, B_z = 3070$). That cofactor norm bound is
     wraparound-free only for $q \ge 12574722$ and is vacuous at $q = 12289$
     (`tooth_cofactor_relation_admits_zero_secret_at_12289`), whereas the isometric bound $\le 6140$
     refutes zero-secret forgeries (`tooth_short_monomial_witness_refutes_zero_secret_at_12289`).
   - Legacy two-term 20-bit challenges (`poly_from_chal20`) admit zero-divisor differences in $R_{12289}$
     (`tooth_two_term_challenge_difference_zero_divisor_12289`), motivating the v3 11-bit signed-monomial challenge space.
4. **Inhabitedness & `#tooth` Counterexamples**:
   - Concrete $N = 1024, q = 12289$ inhabited transcripts and distinct signed-monomial pairs.
   - `#tooth` (a): Over non-power-of-two $\mathbb{Z}_q[X]/(X^3 + 1)$, $(1 + X)(1 - X + X^2) = 0$ makes
     the signed-monomial difference $(+1) - (-X) = 1 + X$ a non-invertible zero divisor for all $q \ge 2$
     (and $1 - X$ at $q = 2$).
   - `#tooth` (b): Over $\mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ for every even $q \ge 2$, $c_1 - c_2 = 2$ is
     a zero divisor / non-unit with no multiplicative inverse.
   - `#tooth` (c): Unforked challenges and norm-violating transcripts are deterministically refused by
     the computational `PSum` extractor.
   - `#tooth` (d): Legacy two-term challenges $X^{108} + X^{512}$ and $X^{2} + X^{513}$ agree at the root
     $\psi = 1945$ of $X^{1024} + 1$ modulo $12289$, so their difference is a zero divisor with no inverse.
   - `#tooth` (e): At $q = 12289$, the $2 N B_z = 6287360$ cofactor bound admits $s_2 = 0, e_2 = \mathrm{centered}(2Y)$
     for every target $Y$, while `ShortMonomialRelaxedRlweWitness` ($\le 6140$) refutes $s_{\mathrm{iso}} = 0$.
-/

public import Qsag.Math.Lattices
import all Qsag.Math.Lattices
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 3. 13-Parallel RLWE OR-Sigma Relation, Choice-Free Witness Extractor & $\ell_\infty$ Norm-Slack -/

/-- Bitwise XOR group operation on `(nu + 1)`-bit signed-monomial challenge codes (`c0 ⊕ c1 = c`),
    matching `self.chal0[rep] ^ self.chal1[rep] == *expected` on 11-bit signed monomials (`nu = 10`)
    in `crates/qsag-core/src/preprocessing.rs`. -/
def SignedMonomialChal.xor {nu : Nat} (c0 c1 : SignedMonomialChal nu) : SignedMonomialChal nu where
  sign := bne c0.sign c1.sign
  deg := ⟨((BitVec.ofNat nu c0.deg.val) ^^^ (BitVec.ofNat nu c1.deg.val)).toNat,
          ((BitVec.ofNat nu c0.deg.val) ^^^ (BitVec.ofNat nu c1.deg.val)).isLt⟩

private theorem bitvec_xor_cancel_right {w : Nat} (a b : BitVec w) : (a ^^^ b) ^^^ b = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bitvec_xor_cancel_left {w : Nat} (a b : BitVec w) : a ^^^ (a ^^^ b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem SignedMonomialChal.xor_cancel_right {nu : Nat} (c f : SignedMonomialChal nu) :
    (c.xor f).xor f = c := by
  apply SignedMonomialChal.ext
  · unfold SignedMonomialChal.xor; dsimp only
    cases c.sign <;> cases f.sign <;> rfl
  · unfold SignedMonomialChal.xor; dsimp only
    have hOfNat : ∀ x : BitVec nu, BitVec.ofNat nu x.toNat = x :=
      fun x => (BitVec.ofNat_toNat nu x).trans (BitVec.setWidth_eq x)
    rw [hOfNat, bitvec_xor_cancel_right, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt c.deg.isLt

theorem SignedMonomialChal.xor_cancel_left {nu : Nat} (f c : SignedMonomialChal nu) :
    f.xor (f.xor c) = c := by
  apply SignedMonomialChal.ext
  · unfold SignedMonomialChal.xor; dsimp only
    cases f.sign <;> cases c.sign <;> rfl
  · unfold SignedMonomialChal.xor; dsimp only
    have hOfNat : ∀ x : BitVec nu, BitVec.ofNat nu x.toNat = x :=
      fun x => (BitVec.ofNat_toNat nu x).trans (BitVec.setWidth_eq x)
    rw [hOfNat, bitvec_xor_cancel_left, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt c.deg.isLt

/-- Decode a `(nu + 1)`-bit challenge word `u : BitVec (nu + 1)` into `SignedMonomialChal nu`:
    low `nu` bits select degree `u & ((1 << nu) - 1)` and bit `nu` selects sign `(u >> nu) & 1`,
    matching `poly_from_chal11` at `nu = 10` (`preprocessing.rs:861-869`). -/
def SignedMonomialChal.ofBitVec {nu : Nat} (u : BitVec (nu + 1)) : SignedMonomialChal nu :=
  SignedMonomialChal.ofFinIndex ⟨u.toNat, by
    have hPow : 2 ^ (nu + 1) = 2 * 2 ^ nu := by rw [Nat.pow_succ]; omega
    have hu := u.isLt
    omega⟩

/-- Canonical `(nu + 1)`-bit encoding of `SignedMonomialChal nu`. -/
def SignedMonomialChal.toBitVec {nu : Nat} (c : SignedMonomialChal nu) : BitVec (nu + 1) :=
  BitVec.ofNat (nu + 1) c.toFinIndex.val

theorem SignedMonomialChal.ofBitVec_toBitVec {nu : Nat} (c : SignedMonomialChal nu) :
    SignedMonomialChal.ofBitVec c.toBitVec = c := by
  have hPow : 2 ^ (nu + 1) = 2 * 2 ^ nu := by rw [Nat.pow_succ]; omega
  have hLt : c.toFinIndex.val < 2 ^ (nu + 1) := by
    have hc := c.toFinIndex.isLt
    omega
  have hIdxLt : c.toBitVec.toNat < 2 * 2 ^ nu := by
    have hb := c.toBitVec.isLt
    omega
  have hFin : (⟨c.toBitVec.toNat, hIdxLt⟩ : Fin (2 * 2 ^ nu)) = c.toFinIndex := by
    apply Fin.ext
    dsimp only [SignedMonomialChal.toBitVec]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]
  exact (congrArg SignedMonomialChal.ofFinIndex hFin).trans (SignedMonomialChal.ofFinIndex_toFinIndex c)

theorem SignedMonomialChal.toBitVec_ofBitVec {nu : Nat} (u : BitVec (nu + 1)) :
    (SignedMonomialChal.ofBitVec u).toBitVec = u := by
  apply BitVec.eq_of_toNat_eq
  unfold SignedMonomialChal.toBitVec SignedMonomialChal.ofBitVec
  have hIdx := SignedMonomialChal.toFinIndex_ofFinIndex (nu := nu) ⟨u.toNat, by
    have hPow : 2 ^ (nu + 1) = 2 * 2 ^ nu := by rw [Nat.pow_succ]; omega
    have hu := u.isLt
    omega⟩
  have hVal : (SignedMonomialChal.ofFinIndex (nu := nu) ⟨u.toNat, _⟩).toFinIndex.val = u.toNat :=
    congrArg Fin.val hIdx
  rw [hVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt u.isLt]

theorem SignedMonomialChal.ofBitVec_injective {nu : Nat} {u u' : BitVec (nu + 1)}
    (h : SignedMonomialChal.ofBitVec u = SignedMonomialChal.ofBitVec u') : u = u' := by
  have h2 := congrArg SignedMonomialChal.toBitVec h
  rw [SignedMonomialChal.toBitVec_ofBitVec, SignedMonomialChal.toBitVec_ofBitVec] at h2
  exact h2

private theorem bitvec_msb_eq_decide_ge {nu : Nat} (u : BitVec (nu + 1)) :
    u.getLsbD nu = decide (2 ^ nu ≤ u.toNat) := by
  change u.toNat.testBit nu = decide (2 ^ nu ≤ u.toNat)
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1, Nat.and_one_is_mod]
  have hu : u.toNat < 2 * 2 ^ nu := by
    have hPow : 2 ^ (nu + 1) = 2 * 2 ^ nu := by rw [Nat.pow_succ]; omega
    have h := u.isLt
    omega
  by_cases hGe : 2 ^ nu ≤ u.toNat
  · have hSub : u.toNat - 2 ^ nu < 2 ^ nu := by omega
    have hEq : u.toNat = (u.toNat - 2 ^ nu) + 2 ^ nu * 1 := by omega
    have hDiv : u.toNat / 2 ^ nu = 1 := (div_mod_of_eq_add_mul hSub hEq).1
    simp [hGe, hDiv]
  · have hLt : u.toNat < 2 ^ nu := by omega
    have hDiv : u.toNat / 2 ^ nu = 0 := Nat.div_eq_of_lt hLt
    simp [hGe, hDiv]

/-- `SignedMonomialChal.ofBitVec` is an exact XOR group isomorphism `(BitVec (nu + 1), ^^^) ≅ (SignedMonomialChal nu, xor)`. -/
theorem SignedMonomialChal.ofBitVec_xor {nu : Nat} (u0 u1 : BitVec (nu + 1)) :
    SignedMonomialChal.ofBitVec (u0 ^^^ u1) =
      (SignedMonomialChal.ofBitVec u0).xor (SignedMonomialChal.ofBitVec u1) := by
  apply SignedMonomialChal.ext
  · show decide (2 ^ nu ≤ (u0 ^^^ u1).toNat) =
      bne (decide (2 ^ nu ≤ u0.toNat)) (decide (2 ^ nu ≤ u1.toNat))
    rw [← bitvec_msb_eq_decide_ge (u0 ^^^ u1), ← bitvec_msb_eq_decide_ge u0,
        ← bitvec_msb_eq_decide_ge u1, BitVec.getLsbD_xor]
  · show (u0 ^^^ u1).toNat % 2 ^ nu =
      ((BitVec.ofNat nu (u0.toNat % 2 ^ nu)) ^^^ (BitVec.ofNat nu (u1.toNat % 2 ^ nu))).toNat
    have hEqBv : BitVec.ofNat nu ((u0 ^^^ u1).toNat) =
        (BitVec.ofNat nu (u0.toNat % 2 ^ nu)) ^^^ (BitVec.ofNat nu (u1.toNat % 2 ^ nu)) := by
      have hModId : ∀ x : Nat, BitVec.ofNat nu (x % 2 ^ nu) = BitVec.ofNat nu x := fun x => by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_mod]
      rw [hModId, hModId]
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat]
      simp only [hi, decide_true, Bool.true_and]
      exact BitVec.getLsbD_xor
    have hToNat := congrArg BitVec.toNat hEqBv
    rw [BitVec.toNat_ofNat] at hToNat
    exact hToNat

/-- Production `nu = 10` (`BitVec 11`) bit-field decomposition matching `poly_from_chal11` in `preprocessing.rs`. -/
theorem SignedMonomialChal.ofBitVec_11_spec (u : BitVec 11) :
    (SignedMonomialChal.ofBitVec u).deg.val = u.toNat % 1024 ∧
    (SignedMonomialChal.ofBitVec u).sign = decide (1024 ≤ u.toNat) :=
  ⟨rfl, rfl⟩

/-- Public statement for the parallel Ring-LWE OR-Sigma proof of short witness knowledge:
    public CRS polynomial $A \in R_q$, branch targets $(u_0, u_1) \in R_q^2$ (`pk0` and `pk0 + t_crs`
    in `preprocessing.rs:1158-1159`), and verifier $\ell_\infty$ response bound $B_z$. -/
structure RlweOrSigmaStatement (nu q : Nat) where
  A : CycPolyZq nu q
  u0 : CycPolyZq nu q
  u1 : CycPolyZq nu q
  Bz : Nat

def RlweOrSigmaStatement.branchU {nu q : Nat} (stmt : RlweOrSigmaStatement nu q) (b : Bool) :
    CycPolyZq nu q :=
  if b then stmt.u1 else stmt.u0

/-- Construct an OR-Sigma statement from Ring-LWE Base-OT parameters `(A, pk0, t_crs, B_z)`. -/
def RlweOrSigmaStatement.fromBaseOt {nu q : Nat} [NeZero q]
    (A pk0 tCrs : CycPolyZq nu q) (Bz : Nat) : RlweOrSigmaStatement nu q where
  A := A
  u0 := pk0
  u1 := cycZqAdd pk0 tCrs
  Bz := Bz

/-- `R`-parallel OR-Sigma transcript over single signed-monomial challenges, carrying commitments
    `(t0, t1)`, branch challenges `(c0, c1)`, and integer responses `(zs0, ze0, zs1, ze1)`. It has the
    shape of `RlweReceiverZkPok` (`R = 13`) with the challenge set narrowed to the pairwise-invertible one. -/
structure RlweOrSigmaTranscript (R nu q : Nat) where
  t0 : Fin R → CycPolyZq nu q
  t1 : Fin R → CycPolyZq nu q
  c0 : Fin R → SignedMonomialChal nu
  c1 : Fin R → SignedMonomialChal nu
  zs0 : Fin R → CycPolyInt nu
  ze0 : Fin R → CycPolyInt nu
  zs1 : Fin R → CycPolyInt nu
  ze1 : Fin R → CycPolyInt nu

def RlweOrSigmaTranscript.branchT {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyZq nu q :=
  if b then tr.t1 i else tr.t0 i

def RlweOrSigmaTranscript.branchChal {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : SignedMonomialChal nu :=
  if b then tr.c1 i else tr.c0 i

def RlweOrSigmaTranscript.branchZs {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyInt nu :=
  if b then tr.zs1 i else tr.zs0 i

def RlweOrSigmaTranscript.branchZe {R nu q : Nat} (tr : RlweOrSigmaTranscript R nu q)
    (b : Bool) (i : Fin R) : CycPolyInt nu :=
  if b then tr.ze1 i else tr.ze0 i

/-- Single-repetition OR-Sigma verifier checking:
    1. `c0_i ⊕ c1_i = c_i`,
    2. `‖zs_b‖_∞ ≤ B_z` and `‖ze_b‖_∞ ≤ B_z` for `b ∈ {0, 1}`,
    3. `A * zs_b + ze_b = t_b + c_b * u_b` in $R_q$ for `b ∈ {0, 1}`. -/
def verifyRlweOrSigmaRep {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (i : Fin R) (expectedChal : SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) : Bool :=
  let chalOk := decide ((tr.c0 i).xor (tr.c1 i) = expectedChal)
  let normOk :=
    decide (cycIntInfNorm (tr.zs0 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.ze0 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.zs1 i) ≤ stmt.Bz) &&
    decide (cycIntInfNorm (tr.ze1 i) ≤ stmt.Bz)
  let eq0Ok := cycZqEq
    (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs0 i))) (cycIntToZq q (tr.ze0 i)))
    (cycZqAdd (tr.t0 i) (cycZqMul ((tr.c0 i).toZqPoly q) stmt.u0))
  let eq1Ok := cycZqEq
    (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs1 i))) (cycIntToZq q (tr.ze1 i)))
    (cycZqAdd (tr.t1 i) (cycZqMul ((tr.c1 i).toZqPoly q) stmt.u1))
  chalOk && normOk && eq0Ok && eq1Ok

/-- Full `R`-parallel RLWE OR-Sigma verifier (`R = 13` in `verifyRlweOrSigma13`). -/
def verifyRlweOrSigma (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (jointChal : Fin R → SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) : Bool :=
  cycAllFin R (fun i => verifyRlweOrSigmaRep stmt i (jointChal i) tr)

theorem verifyRlweOrSigma_iff (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (jointChal : Fin R → SignedMonomialChal nu)
    (tr : RlweOrSigmaTranscript R nu q) :
    verifyRlweOrSigma R nu q stmt jointChal tr = true ↔
      ∀ i : Fin R, verifyRlweOrSigmaRep stmt i (jointChal i) tr = true := by
  unfold verifyRlweOrSigma
  exact cycAllFin_eq_true_iff _

abbrev verifyRlweOrSigma13 (nu q : Nat) [NeZero q] :=
  verifyRlweOrSigma rlweOrSigmaParallelReps nu q

/-- Honest masked OR-Sigma prover on active branch `branch : Bool` with short secret `(s, e)`
    satisfying `A * s + e = u_{branch}`: commits `(t0, t1)` independent of `jointChal` so rewinding
    with `jointChal' ≠ jointChal` yields two accepting transcripts on the exact same commitment! -/
def buildHonestRlweOrSigmaTranscript (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (jointChal : Fin R → SignedMonomialChal nu) : RlweOrSigmaTranscript R nu q :=
  let uFake := if branch then stmt.u0 else stmt.u1
  let tReal : Fin R → CycPolyZq nu q := fun i =>
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q (ysMask i))) (cycIntToZq q (yeMask i))
  let tFake : Fin R → CycPolyZq nu q := fun i =>
    cycZqSub
      (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)))
      (cycZqMul ((cFake i).toZqPoly q) uFake)
  let cReal : Fin R → SignedMonomialChal nu := fun i =>
    if branch then (cFake i).xor (jointChal i) else (jointChal i).xor (cFake i)
  let zsReal : Fin R → CycPolyInt nu := fun i =>
    cycIntAdd (ysMask i) (cycIntMul (cReal i).toIntPoly sSecret)
  let zeReal : Fin R → CycPolyInt nu := fun i =>
    cycIntAdd (yeMask i) (cycIntMul (cReal i).toIntPoly eSecret)
  if branch then
    { t0 := tFake, t1 := tReal, c0 := cFake, c1 := cReal,
      zs0 := zsFake, ze0 := zeFake, zs1 := zsReal, ze1 := zeReal }
  else
    { t0 := tReal, t1 := tFake, c0 := cReal, c1 := cFake,
      zs0 := zsReal, ze0 := zeReal, zs1 := zsFake, ze1 := zeFake }

/-- Commitments of `buildHonestRlweOrSigmaTranscript` are strictly independent of `jointChal`. -/
theorem buildHonestRlweOrSigmaTranscript_same_commitments (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (ch ch' : Fin R → SignedMonomialChal nu) :
    let tr := buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
      ysMask yeMask cFake zsFake zeFake ch
    let tr' := buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
      ysMask yeMask cFake zsFake zeFake ch'
    tr.t0 = tr'.t0 ∧ tr.t1 = tr'.t1 := by
  cases branch <;> exact ⟨rfl, rfl⟩

private theorem signedMonomial_l1Norm_eq_one (nu : Nat) (c : SignedMonomialChal nu) :
    cycIntL1Norm c.toIntPoly = 1 := by
  unfold cycIntL1Norm SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial
  rw [cycNatFinSum_eq_single c.deg]
  · simp [signBitToInt_natAbs]
  · intro i hiNe; simp [hiNe]

/-- Completeness of `buildHonestRlweOrSigmaTranscript` for all `R, nu, q`. -/
theorem buildHonestRlweOrSigmaTranscript_accepts {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) (branch : Bool)
    (sSecret eSecret : CycPolyInt nu)
    (ysMask yeMask : Fin R → CycPolyInt nu)
    (cFake : Fin R → SignedMonomialChal nu)
    (zsFake zeFake : Fin R → CycPolyInt nu)
    (jointChal : Fin R → SignedMonomialChal nu)
    (hRel : cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSecret)) (cycIntToZq q eSecret) =
      stmt.branchU branch)
    (hSafeS : ∀ i : Fin R, cycIntInfNorm (ysMask i) + cycIntInfNorm sSecret ≤ stmt.Bz)
    (hSafeE : ∀ i : Fin R, cycIntInfNorm (yeMask i) + cycIntInfNorm eSecret ≤ stmt.Bz)
    (hFakeS : ∀ i : Fin R, cycIntInfNorm (zsFake i) ≤ stmt.Bz)
    (hFakeE : ∀ i : Fin R, cycIntInfNorm (zeFake i) ≤ stmt.Bz) :
    verifyRlweOrSigma R nu q stmt jointChal
      (buildHonestRlweOrSigmaTranscript R nu q stmt branch sSecret eSecret
        ysMask yeMask cFake zsFake zeFake jointChal) = true := by
  unfold verifyRlweOrSigma
  rw [cycAllFin_eq_true_iff]
  intro i
  unfold verifyRlweOrSigmaRep buildHonestRlweOrSigmaTranscript
  have hRealSBound : ∀ c : SignedMonomialChal nu,
      cycIntInfNorm (cycIntAdd (ysMask i) (cycIntMul c.toIntPoly sSecret)) ≤ stmt.Bz := by
    intro c
    have hMulLe := cycIntInfNorm_mul_le c.toIntPoly sSecret
    rw [signedMonomial_l1Norm_eq_one, Nat.one_mul] at hMulLe
    rw [cycIntInfNorm_le_iff]; intro k
    unfold cycIntAdd
    have hy := cycCoeff_natAbs_le_infNorm (ysMask i) k
    have hcs := Nat.le_trans (cycCoeff_natAbs_le_infNorm (cycIntMul c.toIntPoly sSecret) k) hMulLe
    have hSafe := hSafeS i
    omega
  have hRealEBound : ∀ c : SignedMonomialChal nu,
      cycIntInfNorm (cycIntAdd (yeMask i) (cycIntMul c.toIntPoly eSecret)) ≤ stmt.Bz := by
    intro c
    have hMulLe := cycIntInfNorm_mul_le c.toIntPoly eSecret
    rw [signedMonomial_l1Norm_eq_one, Nat.one_mul] at hMulLe
    rw [cycIntInfNorm_le_iff]; intro k
    unfold cycIntAdd
    have hy := cycCoeff_natAbs_le_infNorm (yeMask i) k
    have hce := Nat.le_trans (cycCoeff_natAbs_le_infNorm (cycIntMul c.toIntPoly eSecret) k) hMulLe
    have hSafe := hSafeE i
    omega
  have hFakeEq : ∀ (uTgt : CycPolyZq nu q) (cf : SignedMonomialChal nu),
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)) =
      cycZqAdd (cycZqSub (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i)))
        (cycZqMul (cf.toZqPoly q) uTgt)) (cycZqMul (cf.toZqPoly q) uTgt) := by
    intro uTgt cf
    let X := cycZqAdd (cycZqMul stmt.A (cycIntToZq q (zsFake i))) (cycIntToZq q (zeFake i))
    let Y := cycZqMul (cf.toZqPoly q) uTgt
    show X = cycZqAdd (cycZqSub X Y) Y
    funext k; unfold cycZqAdd cycZqSub
    rw [← ModZq.ofInt_natVal (X k), ← ModZq.ofInt_natVal (Y k),
        ← ModZq.ofInt_sub, ← ModZq.ofInt_add]
    congr 1; omega
  have hRealEq : ∀ (uTgt : CycPolyZq nu q) (cr : SignedMonomialChal nu),
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSecret)) (cycIntToZq q eSecret) = uTgt →
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q (cycIntAdd (ysMask i) (cycIntMul cr.toIntPoly sSecret))))
        (cycIntToZq q (cycIntAdd (yeMask i) (cycIntMul cr.toIntPoly eSecret))) =
      cycZqAdd (cycZqAdd (cycZqMul stmt.A (cycIntToZq q (ysMask i))) (cycIntToZq q (yeMask i)))
        (cycZqMul (cr.toZqPoly q) uTgt) := by
    intro uTgt cr huTgt
    rw [cycIntToZq_add, cycIntToZq_add, cycIntToZq_mul, cycIntToZq_mul, cycZqMul_left_distrib]
    have hShift : cycZqAdd (cycZqMul stmt.A (cycZqMul (cr.toZqPoly q) (cycIntToZq q sSecret)))
        (cycZqMul (cr.toZqPoly q) (cycIntToZq q eSecret)) = cycZqMul (cr.toZqPoly q) uTgt := by
      rw [← huTgt, cycZqMul_left_distrib, ← cycZqMul_assoc stmt.A (cr.toZqPoly q),
          cycZqMul_comm stmt.A (cr.toZqPoly q), cycZqMul_assoc]
    funext k
    have hk := congrFun hShift k
    let AY := cycZqMul stmt.A (cycIntToZq q (ysMask i)) k
    let ACS := cycZqMul stmt.A (cycZqMul (cr.toZqPoly q) (cycIntToZq q sSecret)) k
    let YE := cycIntToZq q (yeMask i) k
    let CE := cycZqMul (cr.toZqPoly q) (cycIntToZq q eSecret) k
    let CU := cycZqMul (cr.toZqPoly q) uTgt k
    change ModZq.add ACS CE = CU at hk
    show ModZq.add (ModZq.add AY ACS) (ModZq.add YE CE) = ModZq.add (ModZq.add AY YE) CU
    rw [← hk]
    rw [← ModZq.ofInt_natVal AY, ← ModZq.ofInt_natVal ACS,
        ← ModZq.ofInt_natVal YE, ← ModZq.ofInt_natVal CE]
    simp only [← ModZq.ofInt_add]
    congr 1; omega
  cases branch
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold RlweOrSigmaStatement.branchU at hRel
    simp only [Bool.false_eq_true, ↓reduceIte] at hRel
    simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff]
    exact ⟨⟨⟨SignedMonomialChal.xor_cancel_right _ _,
      ⟨⟨⟨hRealSBound _, hRealEBound _⟩, hFakeS i⟩, hFakeE i⟩⟩,
      hRealEq stmt.u0 _ hRel⟩, hFakeEq stmt.u1 _⟩
  · simp only [↓reduceIte]
    unfold RlweOrSigmaStatement.branchU at hRel
    simp only [↓reduceIte] at hRel
    simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff]
    exact ⟨⟨⟨SignedMonomialChal.xor_cancel_left _ _,
      ⟨⟨⟨hFakeS i, hFakeE i⟩, hRealSBound _⟩, hRealEBound _⟩⟩,
      hFakeEq stmt.u0 _⟩, hRealEq stmt.u1 _ hRel⟩

/-- Relaxed short RLWE / Ring-SIS witness produced by 2-special-soundness extraction on the
    `R`-parallel signed-monomial OR-Sigma protocol (`R = 13` in production). -/
structure ExtractedRlweOrSigmaWitness (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) where
  repIdx : Fin R
  branch : Bool
  chal : SignedMonomialChal nu
  chal' : SignedMonomialChal nu
  cofactorG : CycPolyInt nu
  s2 : CycPolyInt nu
  e2 : CycPolyInt nu
  chal_ne : chal ≠ chal'
  cofactor_eq_two :
    cycIntMul (cycIntSub chal.toIntPoly chal'.toIntPoly) cofactorG = cycIntScale 2 cycIntOne
  cofactor_l1_le : cycIntL1Norm cofactorG ≤ 2 ^ nu
  s2_infNorm_le : cycIntInfNorm s2 ≤ 2 * (2 ^ nu) * stmt.Bz
  e2_infNorm_le : cycIntInfNorm e2 ≤ 2 * (2 ^ nu) * stmt.Bz
  relaxed_rlwe_mod_q :
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q s2)) (cycIntToZq q e2) =
      cycZqScale 2 (stmt.branchU branch)
  relaxed_rlwe_int_congr :
    ∀ k : Fin (2 ^ nu),
      (cycIntMul (cycZqToNatInt stmt.A) s2 k + e2 k -
        2 * cycZqToNatInt (stmt.branchU branch) k) % (q : Int) = 0

/-- Constructive first-difference locator over `Fin R` (choice-free). -/
def findDiffChalFin : (R : Nat) → {α : Type} → [DecidableEq α] →
    (ch ch' : Fin R → α) → ch ≠ ch' → { i : Fin R // ch i ≠ ch' i }
  | 0, _, _, _, _, hNe =>
    False.elim <| hNe <| funext fun i => Fin.elim0 i
  | r + 1, _, _, ch, ch', hNe =>
    if h0 : ch ⟨0, Nat.zero_lt_succ r⟩ = ch' ⟨0, Nat.zero_lt_succ r⟩ then
      have hTailNe : (fun i : Fin r => ch ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) ≠
          (fun i : Fin r => ch' ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
        intro hTailEq; apply hNe
        funext ⟨k, hk⟩
        cases k with
        | zero => exact h0
        | succ k' => exact congrFun hTailEq ⟨k', Nat.lt_of_succ_lt_succ hk⟩
      let ⟨iTail, hiTail⟩ := findDiffChalFin r
        (fun i => ch ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i => ch' ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        hTailNe
      ⟨⟨iTail.1 + 1, Nat.succ_lt_succ iTail.2⟩, hiTail⟩
    else
      ⟨⟨0, Nat.zero_lt_succ r⟩, h0⟩

/-- **Fork-difference relation for arbitrary challenge polynomials
    (`rlwe_sigma_fork_difference_relation`)**:
    Two accepting responses `(zs, ze)`, `(zs', ze')` to challenge polynomials `cP`, `cP'` on one shared
    commitment `tShared` satisfy `A * (zs - zs') + (ze - ze') = (cP - cP') * u` in
    $\mathbb{Z}_q[X]/(X^N + 1)$. No assumption is made on the challenge set: this is the part of
    2-special soundness that holds for every challenge space, including the two-term 20-bit challenges
    of `poly_from_chal20`, whose differences are not always invertible. -/
theorem rlwe_sigma_fork_difference_relation {N q : Nat} [NeZero q]
    (A u tShared : NegacyclicPolyZq N q)
    (cP cP' : NegacyclicPolyInt N)
    (zs ze zs' ze' : NegacyclicPolyInt N)
    (hEq1 : cycZqAdd (cycZqMul A (cycIntToZq q zs)) (cycIntToZq q ze) =
      cycZqAdd tShared (cycZqMul (cycIntToZq q cP) u))
    (hEq2 : cycZqAdd (cycZqMul A (cycIntToZq q zs')) (cycIntToZq q ze') =
      cycZqAdd tShared (cycZqMul (cycIntToZq q cP') u)) :
    cycZqAdd (cycZqMul A (cycIntToZq q (cycIntSub zs zs'))) (cycIntToZq q (cycIntSub ze ze')) =
      cycZqMul (cycIntToZq q (cycIntSub cP cP')) u := by
  rw [cycIntToZq_sub, cycIntToZq_sub, cycZqMul_sub_right, cycIntToZq_sub, cycZqMul_sub_left]
  funext k
  have hk1 := congrFun hEq1 k
  have hk2 := congrFun hEq2 k
  let AZ := cycZqMul A (cycIntToZq q zs) k
  let AZ' := cycZqMul A (cycIntToZq q zs') k
  let ZE := cycIntToZq q ze k
  let ZE' := cycIntToZq q ze' k
  let TS := tShared k
  let CU := cycZqMul (cycIntToZq q cP) u k
  let CU' := cycZqMul (cycIntToZq q cP') u k
  change ModZq.add AZ ZE = ModZq.add TS CU at hk1
  change ModZq.add AZ' ZE' = ModZq.add TS CU' at hk2
  show ModZq.add (ModZq.sub AZ AZ') (ModZq.sub ZE ZE') = ModZq.sub CU CU'
  have hCancelT : ModZq.sub (ModZq.add AZ ZE) (ModZq.add AZ' ZE') =
      ModZq.sub (ModZq.add TS CU) (ModZq.add TS CU') := by rw [hk1, hk2]
  rw [← ModZq.ofInt_natVal AZ, ← ModZq.ofInt_natVal AZ',
      ← ModZq.ofInt_natVal ZE, ← ModZq.ofInt_natVal ZE',
      ← ModZq.ofInt_natVal CU, ← ModZq.ofInt_natVal CU'] at hCancelT ⊢
  rw [← ModZq.ofInt_natVal TS] at hCancelT
  simp only [← ModZq.ofInt_add, ← ModZq.ofInt_sub] at hCancelT ⊢
  have hRearrL : ((AZ.val : Int) - (AZ'.val : Int)) + ((ZE.val : Int) - (ZE'.val : Int)) =
      ((AZ.val : Int) + (ZE.val : Int)) - ((AZ'.val : Int) + (ZE'.val : Int)) := by omega
  have hRearrR : ((TS.val : Int) + (CU.val : Int)) - ((TS.val : Int) + (CU'.val : Int)) =
      (CU.val : Int) - (CU'.val : Int) := by omega
  rw [hRearrL, hCancelT, hRearrR]

/-- **Cofactor lift of a fork difference (`ExtractedRlweOrSigmaWitness.ofForkDifference`)**:
    From distinct signed-monomial challenges `chal ≠ chal'` and a response difference `(dzs, dze)`
    with `‖dzs‖_∞, ‖dze‖_∞ ≤ 2 * B_z` and `A * dzs + dze = (chal - chal') * u_b` in $R_q$, multiply by
    the cyclotomic cofactor `g` (`(chal - chal') ⊛ g = 2` over $\mathbb{Z}$) to obtain
    `(s2, e2) = (g ⊛ dzs, g ⊛ dze)` with `A * s2 + e2 = 2 * u_b` and `‖s2‖_∞, ‖e2‖_∞ ≤ 2 * 2^nu * B_z`.
    This is the single place where invertibility of the challenge difference is used; callers supply
    the fork difference from whichever verifier produced it. -/
def ExtractedRlweOrSigmaWitness.ofForkDifference {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (i : Fin R) (b : Bool)
    (chal chal' : SignedMonomialChal nu)
    (hChalNe : chal ≠ chal')
    (dzs dze : CycPolyInt nu)
    (hDzs : cycIntInfNorm dzs ≤ 2 * stmt.Bz) (hDze : cycIntInfNorm dze ≤ 2 * stmt.Bz)
    (hDiffModQ :
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q dzs)) (cycIntToZq q dze) =
      cycZqMul (cycIntToZq q (cycIntSub chal.toIntPoly chal'.toIntPoly)) (stmt.branchU b)) :
    ExtractedRlweOrSigmaWitness R nu q stmt :=
  let g := signedMonomialCofactor nu chal chal'
  let s2 := cycIntMul g dzs
  let e2 := cycIntMul g dze
  have hCof := signedMonomial_diff_mul_cofactor_eq_two nu chal chal' hChalNe
  have hgL1 : cycIntL1Norm g ≤ 2 ^ nu := by
    dsimp only [g]
    dsimp only at hCof
    rw [hCof.2.2.2.2.2.1]
    exact hCof.2.2.2.2.2.2.2.1
  have hs2Norm : cycIntInfNorm s2 ≤ 2 * (2 ^ nu) * stmt.Bz := by
    calc cycIntInfNorm s2
      _ ≤ cycIntL1Norm g * cycIntInfNorm dzs := cycIntInfNorm_mul_le g dzs
      _ ≤ (2 ^ nu) * (2 * stmt.Bz) := Nat.mul_le_mul hgL1 hDzs
      _ = 2 * (2 ^ nu) * stmt.Bz := by rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ nu) 2]
  have he2Norm : cycIntInfNorm e2 ≤ 2 * (2 ^ nu) * stmt.Bz := by
    calc cycIntInfNorm e2
      _ ≤ cycIntL1Norm g * cycIntInfNorm dze := cycIntInfNorm_mul_le g dze
      _ ≤ (2 ^ nu) * (2 * stmt.Bz) := Nat.mul_le_mul hgL1 hDze
      _ = 2 * (2 ^ nu) * stmt.Bz := by rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ nu) 2]
  have hRelaxedModQ :
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q s2)) (cycIntToZq q e2) =
      cycZqScale 2 (stmt.branchU b) := by
    dsimp only [s2, e2]
    rw [cycIntToZq_mul, cycIntToZq_mul]
    have hAMul : cycZqMul stmt.A (cycZqMul (cycIntToZq q g) (cycIntToZq q dzs)) =
        cycZqMul (cycIntToZq q g) (cycZqMul stmt.A (cycIntToZq q dzs)) := by
      rw [← cycZqMul_assoc, cycZqMul_comm stmt.A (cycIntToZq q g), cycZqMul_assoc]
    rw [hAMul, ← cycZqMul_left_distrib, hDiffModQ, ← cycZqMul_assoc,
        ← cycIntToZq_mul, hCof.2.1, cycIntToZq_scale, cycIntToZq_one]
    have hScaleOne : cycZqMul (cycZqScale 2 (@cycZqOne (2 ^ nu) q _)) (stmt.branchU b) =
        cycZqScale 2 (stmt.branchU b) := by
      rw [← cycIntToZq_one q, ← cycIntToZq_scale, ← cycIntToZq_toNatInt (stmt.branchU b),
          ← cycIntToZq_mul, cycIntMul_scale_left, cycIntMul_one_left (Nat.two_pow_pos nu),
          cycIntToZq_scale, cycIntToZq_toNatInt]
    exact hScaleOne
  have hIntCongr : ∀ k : Fin (2 ^ nu),
      (cycIntMul (cycZqToNatInt stmt.A) s2 k + e2 k -
        2 * cycZqToNatInt (stmt.branchU b) k) % (q : Int) = 0 := by
    intro k
    let diffInt : CycPolyInt nu := cycIntSub
      (cycIntAdd (cycIntMul (cycZqToNatInt stmt.A) s2) e2)
      (cycIntScale 2 (cycZqToNatInt (stmt.branchU b)))
    have hProjZero : cycIntToZq q diffInt k = ModZq.zero q := by
      dsimp only [diffInt]
      have hHom : cycIntToZq q
          (cycIntSub (cycIntAdd (cycIntMul (cycZqToNatInt stmt.A) s2) e2)
            (cycIntScale 2 (cycZqToNatInt (stmt.branchU b)))) =
          cycZqSub (cycZqAdd (cycZqMul stmt.A (cycIntToZq q s2)) (cycIntToZq q e2))
            (cycZqScale 2 (stmt.branchU b)) := by
        rw [cycIntToZq_sub, cycIntToZq_add, cycIntToZq_mul, cycIntToZq_scale]
        simp only [cycIntToZq_toNatInt]
      rw [hHom, hRelaxedModQ, cycZqSub_self]
      rfl
    have hv := ModZq.ofInt_val_int q (diffInt k)
    change ModZq.ofInt q (diffInt k) = ModZq.zero q at hProjZero
    rw [hProjZero] at hv
    dsimp only [ModZq.zero, diffInt, cycIntSub, cycIntAdd, cycIntScale] at hv
    omega
  { repIdx := i
    branch := b
    chal := chal
    chal' := chal'
    cofactorG := g
    s2 := s2
    e2 := e2
    chal_ne := hChalNe
    cofactor_eq_two := hCof.1
    cofactor_l1_le := hgL1
    s2_infNorm_le := hs2Norm
    e2_infNorm_le := he2Norm
    relaxed_rlwe_mod_q := hRelaxedModQ
    relaxed_rlwe_int_congr := hIntCongr }

/-- Single-branch cyclotomic cofactor witness extraction core (choice-free). -/
private def extractSingleBranchCofactorWitness {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (i : Fin R) (b : Bool)
    (tShared : CycPolyZq nu q)
    (chal chal' : SignedMonomialChal nu)
    (zs ze zs' ze' : CycPolyInt nu)
    (hChalNe : chal ≠ chal')
    (hzs : cycIntInfNorm zs ≤ stmt.Bz) (hze : cycIntInfNorm ze ≤ stmt.Bz)
    (hzs' : cycIntInfNorm zs' ≤ stmt.Bz) (hze' : cycIntInfNorm ze' ≤ stmt.Bz)
    (hEq1 : cycZqAdd (cycZqMul stmt.A (cycIntToZq q zs)) (cycIntToZq q ze) =
      cycZqAdd tShared (cycZqMul (chal.toZqPoly q) (stmt.branchU b)))
    (hEq2 : cycZqAdd (cycZqMul stmt.A (cycIntToZq q zs')) (cycIntToZq q ze') =
      cycZqAdd tShared (cycZqMul (chal'.toZqPoly q) (stmt.branchU b))) :
    ExtractedRlweOrSigmaWitness R nu q stmt :=
  ExtractedRlweOrSigmaWitness.ofForkDifference stmt i b chal chal' hChalNe
    (cycIntSub zs zs') (cycIntSub ze ze')
    (by have hSub := cycIntInfNorm_sub_le zs zs'; omega)
    (by have hSub := cycIntInfNorm_sub_le ze ze'; omega)
    (rlwe_sigma_fork_difference_relation stmt.A (stmt.branchU b) tShared
      chal.toIntPoly chal'.toIntPoly zs ze zs' ze' hEq1 hEq2)

/-- Constructive `R`-parallel witness extractor (choice-free). -/
def extractRlweOrSigmaWitnessGen (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin R → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript R nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma R nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma R nu q stmt c' tr' = true) :
    ExtractedRlweOrSigmaWitness R nu q stmt :=
  let ⟨i, hiNe⟩ := findDiffChalFin R c c' hcNe
  have hRep : verifyRlweOrSigmaRep stmt i (c i) tr = true :=
    (verifyRlweOrSigma_iff R nu q stmt c tr).mp hAcc i
  have hRep' : verifyRlweOrSigmaRep stmt i (c' i) tr' = true :=
    (verifyRlweOrSigma_iff R nu q stmt c' tr').mp hAcc' i
  if hc0Eq : tr.c0 i = tr'.c0 i then
    have hc1Ne : tr.c1 i ≠ tr'.c1 i := by
      intro hc1Eq
      unfold verifyRlweOrSigmaRep at hRep hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hRep hRep'
      have hXor := hRep.1.1.1
      have hXor' := hRep'.1.1.1
      rw [hc0Eq, hc1Eq] at hXor
      exact hiNe (hXor.symm.trans hXor')
    have hU : cycIntInfNorm (tr.zs1 i) ≤ stmt.Bz ∧
              cycIntInfNorm (tr.ze1 i) ≤ stmt.Bz ∧
              cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs1 i))) (cycIntToZq q (tr.ze1 i)) =
                cycZqAdd (tr.t1 i) (cycZqMul ((tr.c1 i).toZqPoly q) stmt.u1) := by
      unfold verifyRlweOrSigmaRep at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep
      exact ⟨hRep.1.1.2.1.2, hRep.1.1.2.2, hRep.2⟩
    have hU' : cycIntInfNorm (tr'.zs1 i) ≤ stmt.Bz ∧
               cycIntInfNorm (tr'.ze1 i) ≤ stmt.Bz ∧
               cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr'.zs1 i))) (cycIntToZq q (tr'.ze1 i)) =
                 cycZqAdd (tr.t1 i) (cycZqMul ((tr'.c1 i).toZqPoly q) stmt.u1) := by
      unfold verifyRlweOrSigmaRep at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep'
      rw [← ht1] at hRep'
      exact ⟨hRep'.1.1.2.1.2, hRep'.1.1.2.2, hRep'.2⟩
    extractSingleBranchCofactorWitness stmt i true (tr.t1 i)
      (tr.c1 i) (tr'.c1 i) (tr.zs1 i) (tr.ze1 i) (tr'.zs1 i) (tr'.ze1 i)
      hc1Ne hU.1 hU.2.1 hU'.1 hU'.2.1 hU.2.2 hU'.2.2
  else
    have hU : cycIntInfNorm (tr.zs0 i) ≤ stmt.Bz ∧
              cycIntInfNorm (tr.ze0 i) ≤ stmt.Bz ∧
              cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs0 i))) (cycIntToZq q (tr.ze0 i)) =
                cycZqAdd (tr.t0 i) (cycZqMul ((tr.c0 i).toZqPoly q) stmt.u0) := by
      unfold verifyRlweOrSigmaRep at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep
      exact ⟨hRep.1.1.2.1.1.1, hRep.1.1.2.1.1.2, hRep.1.2⟩
    have hU' : cycIntInfNorm (tr'.zs0 i) ≤ stmt.Bz ∧
               cycIntInfNorm (tr'.ze0 i) ≤ stmt.Bz ∧
               cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr'.zs0 i))) (cycIntToZq q (tr'.ze0 i)) =
                 cycZqAdd (tr.t0 i) (cycZqMul ((tr'.c0 i).toZqPoly q) stmt.u0) := by
      unfold verifyRlweOrSigmaRep at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep'
      rw [← ht0] at hRep'
      exact ⟨hRep'.1.1.2.1.1.1, hRep'.1.1.2.1.1.2, hRep'.1.2⟩
    extractSingleBranchCofactorWitness stmt i false (tr.t0 i)
      (tr.c0 i) (tr'.c0 i) (tr.zs0 i) (tr.ze0 i) (tr'.zs0 i) (tr'.ze0 i)
      hc0Eq hU.1 hU.2.1 hU'.1 hU'.2.1 hU.2.2 hU'.2.2

/-- **13-Parallel Relaxed-RLWE / SIS Witness Extractor (`extract_rlwe_or_sigma_13_witness`)**:
    Given two accepting 13-parallel OR-Sigma transcripts `tr, tr'` on the same commitment `(t0, t1)`
    with distinct joint challenge vectors `c ≠ c'`, constructively (choice-free) locates
    `(repIdx : Fin 13, branch : Bool)` where `c_{i,b} ≠ c'_{i,b}`, applies the cyclotomic cofactor `g`,
    and outputs `(s2, e2)` satisfying `A * s2 + e2 ≡ 2 * u_{i,b} (mod q, X^{2^nu} + 1)` over $\mathbb{Z}$
    with exact $\ell_\infty$ bounds `‖s2‖_∞ ≤ 2 * (2^nu) * B_z` and `‖e2‖_∞ ≤ 2 * (2^nu) * B_z`! -/
@[expose] def extract_rlwe_or_sigma_13_witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 13 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 13 nu q stmt c' tr' = true) :
    ExtractedRlweOrSigmaWitness 13 nu q stmt :=
  extractRlweOrSigmaWitnessGen 13 nu q stmt c c' tr tr' ht0 ht1 hcNe hAcc hAcc'

/-- Production $N = 1024$ ($\nu = 10$) specialization of `extract_rlwe_or_sigma_13_witness`
    proving `‖s2‖_∞ ≤ 2 * 1024 * B_z` and `‖e2‖_∞ ≤ 2 * 1024 * B_z`. -/
theorem extract_rlwe_or_sigma_13_witness_1024_bounds {q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement 10 q)
    (c c' : Fin 13 → SignedMonomialChal 10)
    (tr tr' : RlweOrSigmaTranscript 13 10 q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 13 10 q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 13 10 q stmt c' tr' = true) :
    let w := extract_rlwe_or_sigma_13_witness stmt c c' tr tr' ht0 ht1 hcNe hAcc hAcc'
    cycIntInfNorm w.s2 ≤ 2 * 1024 * stmt.Bz ∧
    cycIntInfNorm w.e2 ≤ 2 * 1024 * stmt.Bz ∧
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.s2)) (cycIntToZq q w.e2) =
      cycZqScale 2 (stmt.branchU w.branch) := by
  intro w
  exact ⟨w.s2_infNorm_le, w.e2_infNorm_le, w.relaxed_rlwe_mod_q⟩

/-- **Odd-Modulus Exact Unrelaxed RLWE Recovery (`extracted_witness_unrelaxed_odd_q`)**:
    For every odd modulus $q$, scaling `(s2, e2)` by `(q + 1) / 2 mod q` clears the factor of `2`
    to yield an exact modular solution `A * s_inv + e_inv = u_{i,b}` in $R_q$. -/
theorem extracted_witness_unrelaxed_odd_q {R nu q : Nat} [NeZero q] (hOdd : q % 2 = 1)
    {stmt : RlweOrSigmaStatement nu q}
    (w : ExtractedRlweOrSigmaWitness R nu q stmt) :
    let h := (((q + 1) / 2 : Nat) : Int)
    let sInv := cycZqScale h (cycIntToZq q w.s2)
    let eInv := cycZqScale h (cycIntToZq q w.e2)
    cycZqAdd (cycZqMul stmt.A sInv) eInv = stmt.branchU w.branch := by
  intro h sInv eInv
  have hLin : cycZqAdd (cycZqMul stmt.A sInv) eInv =
      cycZqScale h (cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.s2)) (cycIntToZq q w.e2)) := by
    dsimp only [sInv, eInv]
    rw [cycZqScale_add, ← cycIntToZq_scale, ← cycIntToZq_toNatInt stmt.A, ← cycIntToZq_mul,
        cycIntMul_scale_right, cycIntToZq_scale, cycIntToZq_mul, cycIntToZq_toNatInt]
  rw [hLin, w.relaxed_rlwe_mod_q, cycZqScale_scale]
  funext k; dsimp only [cycZqScale]
  have hMul : h * 2 = 1 + 1 * (q : Int) := by dsimp only [h]; omega
  have hInv : ModZq.ofInt q (h * 2) = ModZq.one q := by
    rw [← ModZq.ofInt_one]
    apply ModZq.ext_int
    rw [ModZq.ofInt_val_int, ModZq.ofInt_val_int, hMul, Int.add_mul_emod_self_right]
  rw [hInv, ← ModZq.ofInt_natVal (stmt.branchU w.branch k), ← ModZq.ofInt_one,
      ← ModZq.ofInt_mul, Int.one_mul, ModZq.ofInt_natVal]

/-- **Zero Modular Wraparound of the Cofactor Witness (`extracted_witness_zero_modular_wraparound`)**:
    Whenever $2 \cdot 2^\nu \cdot B_z < q / 2$, reducing the extracted integer witness `(s2, e2)`
    modulo $q$ and applying `cycZqCentered` recovers `(s2, e2)` over $\mathbb{Z}$.
    The premise is a large-modulus condition. At `(nu, B_z) = (10, 3070)` it reads
    `6287360 < q / 2`, i.e. `q ≥ 12574722` (`cofactor_witness_no_wraparound_modulus_threshold`), so it
    is **false** at the production modulus `q = 12289`
    (`tooth_cofactor_no_wraparound_premise_dead_at_production`): there the cofactor witness is a
    statement modulo `q` only (`relaxed_rlwe_mod_q`), and the wraparound-free object is the fork
    difference (`rlwe_fork_difference_zero_modular_wraparound`, `2 * 3070 = 6140 < 6144`). -/
theorem extracted_witness_zero_modular_wraparound {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q}
    (w : ExtractedRlweOrSigmaWitness R nu q stmt)
    (hNoWrap : 2 * (2 ^ nu) * stmt.Bz < q / 2) :
    cycZqCentered (cycIntToZq q w.s2) = w.s2 ∧
    cycZqCentered (cycIntToZq q w.e2) = w.e2 := by
  refine ⟨?_, ?_⟩
  · funext k
    unfold cycZqCentered cycIntToZq
    apply ModZq.centered_ofInt_exact
    left
    exact Nat.lt_of_le_of_lt ( Nat.le_trans (cycCoeff_natAbs_le_infNorm w.s2 k) w.s2_infNorm_le ) hNoWrap
  · funext k
    unfold cycZqCentered cycIntToZq
    apply ModZq.centered_ofInt_exact
    left
    exact Nat.lt_of_le_of_lt ( Nat.le_trans (cycCoeff_natAbs_le_infNorm w.e2 k) w.e2_infNorm_le ) hNoWrap

/-- **Integer identity from a small residual (`extracted_witness_integer_identity_of_small_residual`)**:
    For every modulus, if a lift `uLift` of the branch target leaves an integer residual
    `A_Z ⊛ s2 + e2 - 2 * uLift` of $\ell_\infty$ norm below `q`, the relaxed relation holds identically
    in $\mathbb{Z}[X]/(X^{2^\nu} + 1)$. No modulus-size premise is needed. -/
theorem extracted_witness_integer_identity_of_small_residual {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q}
    (w : ExtractedRlweOrSigmaWitness R nu q stmt)
    (uLift : CycPolyInt nu)
    (huLift : cycIntToZq q uLift = stmt.branchU w.branch)
    (hResLtQ : cycIntInfNorm (cycIntSub (cycIntAdd (cycIntMul (cycZqToNatInt stmt.A) w.s2) w.e2)
        (cycIntScale 2 uLift)) < q) :
    cycIntAdd (cycIntMul (cycZqToNatInt stmt.A) w.s2) w.e2 = cycIntScale 2 uLift := by
  funext k
  let res := cycIntSub (cycIntAdd (cycIntMul (cycZqToNatInt stmt.A) w.s2) w.e2) (cycIntScale 2 uLift)
  have hProjZero : cycIntToZq q res k = ModZq.zero q := by
    have hHom : cycIntToZq q res =
        cycZqSub (cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.s2)) (cycIntToZq q w.e2))
          (cycZqScale 2 (stmt.branchU w.branch)) := by
      dsimp only [res]
      rw [cycIntToZq_sub, cycIntToZq_add, cycIntToZq_mul, cycIntToZq_scale,
          cycIntToZq_toNatInt, huLift]
    rw [hHom, w.relaxed_rlwe_mod_q, cycZqSub_self]
    rfl
  have hv := ModZq.ofInt_val_int q (res k)
  change ModZq.ofInt q (res k) = ModZq.zero q at hProjZero
  rw [hProjZero] at hv
  dsimp only [ModZq.zero] at hv
  have hkAbs : (res k).natAbs < q :=
    Nat.lt_of_le_of_lt (cycCoeff_natAbs_le_infNorm res k) hResLtQ
  have hResZero : res k = 0 := by
    have hModZ : (res k) % (q : Int) = 0 := hv.symm
    have hDef := Int.emod_def (res k) (q : Int)
    rw [hModZ] at hDef
    have hDiv : (q : Int) * ((res k) / (q : Int)) = res k := by omega
    by_cases hq0 : (res k) / (q : Int) = 0
    · rw [hq0, Int.mul_zero] at hDiv; exact hDiv.symm
    · exfalso
      have hAbsMul : (res k).natAbs = q * ((res k) / (q : Int)).natAbs := by
        conv => lhs; rw [← hDiv]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hQuotPos : 1 ≤ ((res k) / (q : Int)).natAbs := by omega
      have hGeQ : q ≤ q * ((res k) / (q : Int)).natAbs := by
        simpa using Nat.mul_le_mul_left q hQuotPos
      omega
  dsimp only [res, cycIntSub] at hResZero
  omega

/-- The cofactor no-wraparound premise at `(nu, B_z) = (10, 3070)` is exactly `q ≥ 12574722`. -/
theorem cofactor_witness_no_wraparound_modulus_threshold (q : Nat) :
    2 * (2 ^ rlweCyclotomicNu) * rlweProductionBz < q / 2 ↔ 12574722 ≤ q := by
  have hN : 2 ^ rlweCyclotomicNu = 1024 := rlweCyclotomicN_eq_1024
  rw [hN]
  unfold rlweProductionBz
  constructor <;> intro h <;> omega

/-- **`#tooth`: the cofactor no-wraparound premise is dead at production parameters
    (`tooth_cofactor_no_wraparound_premise_dead_at_production`)**:
    `2 * 1024 * 3070 = 6287360 ≥ 6144 = 12289 / 2`, so `extracted_witness_zero_modular_wraparound`
    cannot be instantiated at `q = 12289`; the fork-difference premise `2 * 3070 < 6144` does hold. -/
theorem tooth_cofactor_no_wraparound_premise_dead_at_production :
    ¬ (2 * (2 ^ rlweCyclotomicNu) * rlweProductionBz < rlweProductionQ / 2) ∧
    2 * rlweProductionBz < rlweProductionQ / 2 := by
  constructor <;> decide

/-- **Zero Modular Wraparound of the Fork Difference (`rlwe_fork_difference_zero_modular_wraparound`)**:
    A response difference `d = z - z'` with `‖d‖_∞ ≤ 2 * B_z` lifts back identically from
    $\mathbb{Z}_q$ whenever `2 * B_z < q / 2`. This premise holds at production parameters
    (`2 * 3070 = 6140 < 6144 = 12289 / 2`, see `rlwe_fork_difference_zero_modular_wraparound_production`),
    which is what the response box `[-3070, 3070)` is sized for. -/
theorem rlwe_fork_difference_zero_modular_wraparound {N q : Nat} [NeZero q]
    (d : NegacyclicPolyInt N) (Bz : Nat)
    (hNorm : cycIntInfNorm d ≤ 2 * Bz) (hNoWrap : 2 * Bz < q / 2) :
    cycZqCentered (cycIntToZq q d) = d := by
  funext k
  unfold cycZqCentered cycIntToZq
  apply ModZq.centered_ofInt_exact
  left
  exact Nat.lt_of_le_of_lt (Nat.le_trans (cycCoeff_natAbs_le_infNorm d k) hNorm) hNoWrap

/-- Production instance: every difference of two in-box responses is recovered exactly from its
    reduction modulo `12289`. -/
theorem rlwe_fork_difference_zero_modular_wraparound_production {N : Nat}
    (d : NegacyclicPolyInt N) (hNorm : cycIntInfNorm d ≤ 2 * rlweProductionBz) :
    cycZqCentered (cycIntToZq rlweProductionQ d) = d :=
  rlwe_fork_difference_zero_modular_wraparound d rlweProductionBz hNorm (by decide)

/-- Explicit refusal clauses for the total computational `PSum` OR-Sigma witness extractor. -/
inductive RlweOrSigmaExtractRefusal where
  | commitmentMismatchT0
  | commitmentMismatchT1
  | firstTranscriptInvalid
  | secondTranscriptInvalid
  | identicalJointChallenges
  deriving DecidableEq, Repr

/-- Total choice-free `PSum`-valued computational extractor for the 13-parallel OR-Sigma protocol. -/
def tryExtractRlweOrSigma13Witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q) :
    PSum (ExtractedRlweOrSigmaWitness 13 nu q stmt) RlweOrSigmaExtractRefusal :=
  if ht0 : cycAllFin 13 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true then
    if ht1 : cycAllFin 13 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true then
      if hAcc : verifyRlweOrSigma 13 nu q stmt c tr = true then
        if hAcc' : verifyRlweOrSigma 13 nu q stmt c' tr' = true then
          if hcEq : cycAllFin 13 (fun i => decide (c i = c' i)) = true then
            PSum.inr .identicalJointChallenges
          else
            have ht0Eq : tr.t0 = tr'.t0 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht0 i)
            have ht1Eq : tr.t1 = tr'.t1 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht1 i)
            have hcNe : c ≠ c' := by
              intro hEq; apply hcEq
              rw [cycAllFin_eq_true_iff]; intro i; subst hEq; exact decide_eq_true rfl
            PSum.inl (extract_rlwe_or_sigma_13_witness stmt c c' tr tr' ht0Eq ht1Eq hcNe hAcc hAcc')
        else
          PSum.inr .secondTranscriptInvalid
      else
        PSum.inr .firstTranscriptInvalid
    else
      PSum.inr .commitmentMismatchT1
  else
    PSum.inr .commitmentMismatchT0

theorem tryExtractRlweOrSigma13Witness_complete {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 13 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 13 nu q stmt c' tr' = true) :
    ∃ w, tryExtractRlweOrSigma13Witness stmt c c' tr tr' = PSum.inl w := by
  have ht0Bool : cycAllFin 13 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht0]; exact (cycZqEq_iff _ _).mpr rfl
  have ht1Bool : cycAllFin 13 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht1]; exact (cycZqEq_iff _ _).mpr rfl
  have hcEqFalse : ¬(cycAllFin 13 (fun i => decide (c i = c' i)) = true) := by
    intro hAll
    apply hcNe
    funext i
    exact of_decide_eq_true ((cycAllFin_eq_true_iff _).mp hAll i)
  unfold tryExtractRlweOrSigma13Witness
  simp only [ht0Bool, ht1Bool, hAcc, hAcc', hcEqFalse, ↓reduceDIte]
  exact ⟨_, rfl⟩


/-! ### 3.1 Evaluation at a Root of $X^N + 1$: Zero-Divisor Challenge Differences -/

/-- A signed monomial acts on any polynomial of $\mathbb{Z}[X]/(X^N + 1)$ by a signed negacyclic shift. -/
theorem negacyclicSignedMonomial_mul_apply {N : Nat} (s : Bool) (k : Fin N)
    (p : NegacyclicPolyInt N) (j : Fin N) :
    cycIntMul (negacyclicSignedMonomial s k) p j =
      if h : k.val ≤ j.val then signBitToInt s * p ⟨j.val - k.val, by omega⟩
      else -(signBitToInt s * p ⟨N + j.val - k.val, by omega⟩) := by
  rw [cycIntMul_eq_single]
  unfold cycIntMulSingle
  rw [cycIntFinSum_eq_single k]
  · have hk : negacyclicSignedMonomial s k k = signBitToInt s := by
      unfold negacyclicSignedMonomial; simp only [↓reduceIte]
    simp only [hk]
  · intro i hi
    have hz : negacyclicSignedMonomial s k i = 0 := by
      unfold negacyclicSignedMonomial; simp only [hi, ↓reduceIte]
    by_cases hij : i.val ≤ j.val
    · simp only [hij, ↓reduceDIte, hz, Int.zero_mul]
    · simp only [hij, ↓reduceDIte, hz, Int.zero_mul, Int.neg_zero]

/-! ### 3.0a Signed-Monomial $\ell_\infty$ Isometry & Short Relaxed RLWE / Ring-SIS Extraction (`H2`) -/

private theorem cycIntInfNorm_mul_negacyclicSignedMonomial_le {N : Nat} (s : Bool) (k : Fin N)
    (p : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntMul (negacyclicSignedMonomial s k) p) ≤ cycIntInfNorm p := by
  rw [cycIntInfNorm_le_iff]
  intro j
  rw [negacyclicSignedMonomial_mul_apply]
  by_cases hkj : k.val ≤ j.val
  · simp only [hkj, ↓reduceDIte, Int.natAbs_mul, signBitToInt_natAbs, Nat.one_mul]
    exact cycCoeff_natAbs_le_infNorm p _
  · simp only [hkj, ↓reduceDIte, Int.natAbs_neg, Int.natAbs_mul, signBitToInt_natAbs, Nat.one_mul]
    exact cycCoeff_natAbs_le_infNorm p _

/-- **Signed-Monomial $\ell_\infty$ Isometry (`cycIntInfNorm_mul_negacyclicSignedMonomial_eq`)**:
    Multiplying any integer polynomial $p \in \mathbb{Z}[X]/(X^N + 1)$ by a signed monomial $\pm X^k$
    permutes and flips signs of coefficients without ever adding terms: $\|(\pm X^k) \circledast p\|_\infty = \|p\|_\infty$. -/
theorem cycIntInfNorm_mul_negacyclicSignedMonomial_eq {N : Nat} (s : Bool) (k : Fin N)
    (p : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntMul (negacyclicSignedMonomial s k) p) = cycIntInfNorm p := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have hLe := cycIntInfNorm_mul_negacyclicSignedMonomial_le s k p
  have hInvEq : p = cycIntMul (negacyclicSignedMonomialInv hN s k)
      (cycIntMul (negacyclicSignedMonomial s k) p) := by
    rw [← cycIntMul_assoc, cycIntMul_comm (negacyclicSignedMonomialInv hN s k),
        negacyclicSignedMonomial_mul_inv hN s k, cycIntMul_one_left hN]
  have hGe : cycIntInfNorm p ≤ cycIntInfNorm (cycIntMul (negacyclicSignedMonomial s k) p) := by
    conv => lhs; rw [hInvEq]
    exact cycIntInfNorm_mul_negacyclicSignedMonomial_le _ _ _
  omega

theorem cycIntInfNorm_mul_negacyclicSignedMonomialInv_eq {N : Nat} (hN : 0 < N) (s : Bool) (k : Fin N)
    (p : NegacyclicPolyInt N) :
    cycIntInfNorm (cycIntMul (negacyclicSignedMonomialInv hN s k) p) = cycIntInfNorm p :=
  cycIntInfNorm_mul_negacyclicSignedMonomial_eq _ _ p

theorem cycIntInfNorm_mul_signedMonomial_eq {nu : Nat} (c : SignedMonomialChal nu)
    (p : CycPolyInt nu) :
    cycIntInfNorm (cycIntMul c.toIntPoly p) = cycIntInfNorm p :=
  cycIntInfNorm_mul_negacyclicSignedMonomial_eq c.sign c.deg p

/-- Exact integer inverse $c^{-1} = (\pm X^k)^{-1} \in \mathbb{Z}[X]/(X^{2^\nu} + 1)$ of a signed monomial. -/
def SignedMonomialChal.invIntPoly {nu : Nat} (c : SignedMonomialChal nu) : CycPolyInt nu :=
  negacyclicSignedMonomialInv (Nat.two_pow_pos nu) c.sign c.deg

theorem SignedMonomialChal.mul_invIntPoly {nu : Nat} (c : SignedMonomialChal nu) :
    cycIntMul c.toIntPoly c.invIntPoly = cycIntOne :=
  negacyclicSignedMonomial_mul_inv (Nat.two_pow_pos nu) c.sign c.deg

theorem SignedMonomialChal.invIntPoly_mul {nu : Nat} (c : SignedMonomialChal nu) :
    cycIntMul c.invIntPoly c.toIntPoly = cycIntOne := by
  rw [cycIntMul_comm, c.mul_invIntPoly]

theorem cycIntInfNorm_mul_chalInv_eq {nu : Nat} (c : SignedMonomialChal nu) (p : CycPolyInt nu) :
    cycIntInfNorm (cycIntMul c.invIntPoly p) = cycIntInfNorm p :=
  cycIntInfNorm_mul_negacyclicSignedMonomialInv_eq (Nat.two_pow_pos nu) c.sign c.deg p

private theorem negacyclicSignedMonomial_l1Norm_eq_one {N : Nat} (s : Bool) (k : Fin N) :
    cycIntL1Norm (negacyclicSignedMonomial s k) = 1 := by
  unfold cycIntL1Norm negacyclicSignedMonomial
  rw [cycNatFinSum_eq_single k]
  · simp [signBitToInt_natAbs]
  · intro i hiNe; simp [hiNe]

private theorem negacyclicSignedMonomial_infNorm_eq_one {N : Nat} (s : Bool) (k : Fin N) :
    cycIntInfNorm (negacyclicSignedMonomial s k) = 1 := by
  have hLe : cycIntInfNorm (negacyclicSignedMonomial s k) ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro i; unfold negacyclicSignedMonomial
    split
    · rw [signBitToInt_natAbs]; exact Nat.le_refl 1
    · decide
  have hGe : 1 ≤ cycIntInfNorm (negacyclicSignedMonomial s k) := by
    have hk := cycCoeff_natAbs_le_infNorm (negacyclicSignedMonomial s k) k
    unfold negacyclicSignedMonomial at hk
    simp only [↓reduceIte, signBitToInt_natAbs] at hk
    exact hk
  omega

private theorem cycIntL1Norm_sub_le {N : Nat} (a b : NegacyclicPolyInt N) :
    cycIntL1Norm (cycIntSub a b) ≤ cycIntL1Norm a + cycIntL1Norm b := by
  unfold cycIntL1Norm
  rw [← cycNatFinSum_add]
  apply cycNatFinSum_le
  intro i; unfold cycIntSub; omega

private theorem cycIntOne_l1_and_inf {N : Nat} (hN : 0 < N) :
    cycIntL1Norm (@cycIntOne N) = 1 ∧ cycIntInfNorm (@cycIntOne N) = 1 := by
  have hEq : (@cycIntOne N) = negacyclicSignedMonomial false ⟨0, hN⟩ := by
    funext i; unfold cycIntOne negacyclicSignedMonomial signBitToInt
    by_cases hi : i.val = 0
    · have hiEq : i = ⟨0, hN⟩ := Fin.ext hi
      simp [hiEq]
    · have hiNe : i ≠ ⟨0, hN⟩ := fun h => hi (congrArg Fin.val h)
      simp [hiNe, hi]
  rw [hEq]
  exact ⟨negacyclicSignedMonomial_l1Norm_eq_one false ⟨0, hN⟩,
         negacyclicSignedMonomial_infNorm_eq_one false ⟨0, hN⟩⟩

/-- Explicit alias documenting that `ExtractedRlweOrSigmaWitness.relaxed_rlwe_mod_q` is the
    cyclotomic cofactor fork relation $A \cdot s_2 + e_2 \equiv 2 \cdot u_b \pmod q$ (`‖s2‖_∞ ≤ 2 N B_z`). -/
theorem ExtractedRlweOrSigmaWitness.cofactor_fork_relation {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q} (w : ExtractedRlweOrSigmaWitness R nu q stmt) :
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.s2)) (cycIntToZq q w.e2) =
      cycZqScale 2 (stmt.branchU w.branch) :=
  w.relaxed_rlwe_mod_q

/-- **Short Isometric Signed-Monomial Relaxed RLWE Witness (`ShortMonomialRelaxedRlweWitness`, `H2`)**:
    Applying the $\ell_\infty$ isometry $c^{-1} = (\pm X^k)^{-1}$ to the fork difference $(\Delta z_s, \Delta z_e)$
    produces $(s_{\mathrm{iso}}, e_{\mathrm{iso}}) = (c^{-1} \circledast \Delta z_s, c^{-1} \circledast \Delta z_e)$
    and relaxation polynomial $r_{\mathrm{rel}} = 1 - c^{-1} \circledast c'$ (`‖r_rel‖_1 ≤ 2`, invertible in
    $R_q$ for every odd $q \ge 3$ and **every** distinct challenge pair $c \ne c'$) such that:
    - $\|s_{\mathrm{iso}}\|_\infty \le 2 B_z$ and $\|e_{\mathrm{iso}}\|_\infty \le 2 B_z$
      (`6140 < 6144 = ⌊12289 / 2⌋` at production $q = 12289, B_z = 3070$ — **strictly wraparound-free**!),
    - $A \cdot s_{\mathrm{iso}} + e_{\mathrm{iso}} = r_{\mathrm{rel}} \cdot u_b$ in $R_q$. -/
structure ShortMonomialRelaxedRlweWitness (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q) where
  repIdx : Fin R
  branch : Bool
  chal : SignedMonomialChal nu
  chal' : SignedMonomialChal nu
  sIso : CycPolyInt nu
  eIso : CycPolyInt nu
  rRel : CycPolyInt nu
  chal_ne : chal ≠ chal'
  rRel_eq : rRel = cycIntSub cycIntOne (cycIntMul chal.invIntPoly chal'.toIntPoly)
  chal_mul_rRel : cycIntMul chal.toIntPoly rRel = cycIntSub chal.toIntPoly chal'.toIntPoly
  rRel_l1_le : cycIntL1Norm rRel ≤ 2
  rRel_infNorm_le : cycIntInfNorm rRel ≤ 2
  sIso_infNorm_le : cycIntInfNorm sIso ≤ 2 * stmt.Bz
  eIso_infNorm_le : cycIntInfNorm eIso ≤ 2 * stmt.Bz
  short_relaxed_rlwe_mod_q :
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q sIso)) (cycIntToZq q eIso) =
      cycZqMul (cycIntToZq q rRel) (stmt.branchU branch)

/-- Construct a `ShortMonomialRelaxedRlweWitness` from any forked response pair on `chal ≠ chal'`. -/
def ShortMonomialRelaxedRlweWitness.ofForkDifference {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (i : Fin R) (b : Bool)
    (chal chal' : SignedMonomialChal nu)
    (hChalNe : chal ≠ chal')
    (dzs dze : CycPolyInt nu)
    (hDzs : cycIntInfNorm dzs ≤ 2 * stmt.Bz) (hDze : cycIntInfNorm dze ≤ 2 * stmt.Bz)
    (hDiffModQ :
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q dzs)) (cycIntToZq q dze) =
      cycZqMul (cycIntToZq q (cycIntSub chal.toIntPoly chal'.toIntPoly)) (stmt.branchU b)) :
    ShortMonomialRelaxedRlweWitness R nu q stmt :=
  let hN := Nat.two_pow_pos nu
  let sIso := cycIntMul chal.invIntPoly dzs
  let eIso := cycIntMul chal.invIntPoly dze
  let ratio := cycIntMul chal.invIntPoly chal'.toIntPoly
  let rRel := cycIntSub cycIntOne ratio
  have hRatioNorms : cycIntL1Norm ratio = 1 ∧ cycIntInfNorm ratio = 1 := by
    unfold ratio SignedMonomialChal.invIntPoly SignedMonomialChal.toIntPoly
      negacyclicSignedMonomialInv cycSignedPow signedMonomial
    rw [negacyclicSignedMonomial_mul hN]
    split
    · exact ⟨negacyclicSignedMonomial_l1Norm_eq_one _ _, negacyclicSignedMonomial_infNorm_eq_one _ _⟩
    · exact ⟨negacyclicSignedMonomial_l1Norm_eq_one _ _, negacyclicSignedMonomial_infNorm_eq_one _ _⟩
  have hOneNorms := cycIntOne_l1_and_inf hN
  have hrL1 : cycIntL1Norm rRel ≤ 2 := by
    have hSub := cycIntL1Norm_sub_le (@cycIntOne (2 ^ nu)) ratio
    rw [hOneNorms.1, hRatioNorms.1] at hSub
    exact hSub
  have hrInf : cycIntInfNorm rRel ≤ 2 := by
    have hSub := cycIntInfNorm_sub_le (@cycIntOne (2 ^ nu)) ratio
    rw [hOneNorms.2, hRatioNorms.2] at hSub
    exact hSub
  have hChalMulR : cycIntMul chal.toIntPoly rRel = cycIntSub chal.toIntPoly chal'.toIntPoly := by
    dsimp only [rRel, ratio]
    rw [cycIntMul_sub_right, cycIntMul_one_right hN, ← cycIntMul_assoc,
        chal.mul_invIntPoly, cycIntMul_one_left hN]
  have hsNorm : cycIntInfNorm sIso ≤ 2 * stmt.Bz := by
    dsimp only [sIso]
    rw [cycIntInfNorm_mul_chalInv_eq]
    exact hDzs
  have heNorm : cycIntInfNorm eIso ≤ 2 * stmt.Bz := by
    dsimp only [eIso]
    rw [cycIntInfNorm_mul_chalInv_eq]
    exact hDze
  have hRelModQ :
      cycZqAdd (cycZqMul stmt.A (cycIntToZq q sIso)) (cycIntToZq q eIso) =
      cycZqMul (cycIntToZq q rRel) (stmt.branchU b) := by
    dsimp only [sIso, eIso]
    rw [cycIntToZq_mul, cycIntToZq_mul]
    have hSwap : cycZqMul stmt.A (cycZqMul (cycIntToZq q chal.invIntPoly) (cycIntToZq q dzs)) =
        cycZqMul (cycIntToZq q chal.invIntPoly) (cycZqMul stmt.A (cycIntToZq q dzs)) := by
      rw [← cycZqMul_assoc, cycZqMul_comm stmt.A (cycIntToZq q chal.invIntPoly), cycZqMul_assoc]
    rw [hSwap, ← cycZqMul_left_distrib, hDiffModQ, ← hChalMulR,
        ← cycZqMul_assoc, ← cycIntToZq_mul,
        ← cycIntMul_assoc, chal.invIntPoly_mul, cycIntMul_one_left hN]
  { repIdx := i
    branch := b
    chal := chal
    chal' := chal'
    sIso := sIso
    eIso := eIso
    rRel := rRel
    chal_ne := hChalNe
    rRel_eq := rfl
    chal_mul_rRel := hChalMulR
    rRel_l1_le := hrL1
    rRel_infNorm_le := hrInf
    sIso_infNorm_le := hsNorm
    eIso_infNorm_le := heNorm
    short_relaxed_rlwe_mod_q := hRelModQ }

/-- Explicit inverse $r_{\mathrm{rel}}^{-1} = c \cdot (c - c')^{-1} \in R_q$ for any odd $q \ge 3$. -/
def ShortMonomialRelaxedRlweWitness.rRelInvZq {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q}
    (w : ShortMonomialRelaxedRlweWitness R nu q stmt) : CycPolyZq nu q :=
  cycZqMul (w.chal.toZqPoly q) (signedMonomialDiffInvZq nu q w.chal w.chal')

/-- For every odd $q \ge 3$, $r_{\mathrm{rel}}$ is a unit in $R_q$ and $(r_{\mathrm{rel}}^{-1} s_{\mathrm{iso}},
    r_{\mathrm{rel}}^{-1} e_{\mathrm{iso}})$ satisfies the exact unrelaxed RLWE equation in $R_q$. -/
theorem short_monomial_witness_rRel_invertible {R nu q : Nat} [NeZero q]
    (hOdd : q % 2 = 1) (hq3 : 3 ≤ q)
    {stmt : RlweOrSigmaStatement nu q}
    (w : ShortMonomialRelaxedRlweWitness R nu q stmt) :
    cycZqMul (cycIntToZq q w.rRel) w.rRelInvZq = cycZqOne ∧
    cycZqMul w.rRelInvZq (cycIntToZq q w.rRel) = cycZqOne ∧
    cycZqAdd
      (cycZqMul stmt.A (cycZqMul w.rRelInvZq (cycIntToZq q w.sIso)))
      (cycZqMul w.rRelInvZq (cycIntToZq q w.eIso)) = stmt.branchU w.branch := by
  have hInvDiff := (signedMonomial_challenge_set_pairwise_invertible nu q hOdd hq3 w.chal w.chal' w.chal_ne).2.1
  have hRight : cycZqMul (cycIntToZq q w.rRel) w.rRelInvZq = cycZqOne := by
    unfold ShortMonomialRelaxedRlweWitness.rRelInvZq SignedMonomialChal.toZqPoly
    rw [← cycZqMul_assoc, cycZqMul_comm (cycIntToZq q w.rRel) (cycIntToZq q w.chal.toIntPoly),
        ← cycIntToZq_mul, w.chal_mul_rRel, cycIntToZq_sub]
    exact hInvDiff
  have hLeft : cycZqMul w.rRelInvZq (cycIntToZq q w.rRel) = cycZqOne := by
    rw [cycZqMul_comm]; exact hRight
  refine ⟨hRight, hLeft, ?_⟩
  have hLin : cycZqAdd
      (cycZqMul stmt.A (cycZqMul w.rRelInvZq (cycIntToZq q w.sIso)))
      (cycZqMul w.rRelInvZq (cycIntToZq q w.eIso)) =
      cycZqMul w.rRelInvZq (cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.sIso)) (cycIntToZq q w.eIso)) := by
    rw [cycZqMul_left_distrib, ← cycZqMul_assoc stmt.A w.rRelInvZq,
        cycZqMul_comm stmt.A w.rRelInvZq, cycZqMul_assoc]
  rw [hLin, w.short_relaxed_rlwe_mod_q, ← cycZqMul_assoc, hLeft,
      cycZqMul_one_left (Nat.two_pow_pos nu)]

/-- Production fork extraction gives an exact modular witness after explicit inversion.
    Shortness belongs to the isometric witness, not to this unrelaxed modular pair. -/
theorem conditioned_production_fork_exact_relation
    {stmt : RlweOrSigmaStatement 10 12289}
    (w : ShortMonomialRelaxedRlweWitness 13 10 12289 stmt) :
    cycZqAdd
      (cycZqMul stmt.A (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.sIso)))
      (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.eIso)) = stmt.branchU w.branch :=
  (short_monomial_witness_rRel_invertible (by decide) (by decide) w).2.2

/-- At production parameters $q = 12289, B_z = 3070$, $(s_{\mathrm{iso}}, e_{\mathrm{iso}})$ has
    $\ell_\infty \le 6140 < 6144 = \lfloor 12289 / 2 \rfloor$ and **zero modular wraparound** over $\mathbb{Z}$! -/
theorem short_monomial_witness_zero_wraparound_production {R nu : Nat}
    {stmt : RlweOrSigmaStatement nu rlweProductionQ}
    (hBz : stmt.Bz ≤ rlweProductionBz)
    (w : ShortMonomialRelaxedRlweWitness R nu rlweProductionQ stmt) :
    cycIntInfNorm w.sIso ≤ 6140 ∧
    cycIntInfNorm w.eIso ≤ 6140 ∧
    6140 < rlweProductionQ / 2 ∧
    cycZqCentered (cycIntToZq rlweProductionQ w.sIso) = w.sIso ∧
    cycZqCentered (cycIntToZq rlweProductionQ w.eIso) = w.eIso := by
  have hs6140 : cycIntInfNorm w.sIso ≤ 2 * rlweProductionBz := by
    have := w.sIso_infNorm_le; unfold rlweProductionBz at *; omega
  have he6140 : cycIntInfNorm w.eIso ≤ 2 * rlweProductionBz := by
    have := w.eIso_infNorm_le; unfold rlweProductionBz at *; omega
  exact ⟨hs6140, he6140, by decide,
    rlwe_fork_difference_zero_modular_wraparound_production w.sIso hs6140,
    rlwe_fork_difference_zero_modular_wraparound_production w.eIso he6140⟩

/-- On same-degree opposite-sign forks (`chal.deg = chal'.deg`), `rRel = 2` identically, yielding
    $A \cdot s_{\mathrm{iso}} + e_{\mathrm{iso}} = 2 \cdot u_b$ with $\|s_{\mathrm{iso}}\|_\infty \le 2 B_z = 6140 < 6144$! -/
theorem short_monomial_witness_same_deg_eq_two {R nu q : Nat} [NeZero q]
    {stmt : RlweOrSigmaStatement nu q}
    (w : ShortMonomialRelaxedRlweWitness R nu q stmt)
    (hSameDeg : w.chal.deg = w.chal'.deg) :
    w.rRel = cycIntScale 2 cycIntOne ∧
    cycZqAdd (cycZqMul stmt.A (cycIntToZq q w.sIso)) (cycIntToZq q w.eIso) =
      cycZqScale 2 (stmt.branchU w.branch) := by
  have hSignNe : w.chal.sign ≠ w.chal'.sign := fun hs =>
    w.chal_ne (SignedMonomialChal.ext hs (congrArg Fin.val hSameDeg))
  have hChalNeg : w.chal'.toIntPoly = cycIntNeg w.chal.toIntPoly := by
    funext k
    unfold SignedMonomialChal.toIntPoly signedMonomial negacyclicSignedMonomial cycIntNeg
    rw [← hSameDeg]
    by_cases hk : k = w.chal.deg
    · simp only [hk, ↓reduceIte]
      cases hs1 : w.chal.sign <;> cases hs2 : w.chal'.sign
      · exact False.elim (hSignNe (hs1.trans hs2.symm))
      · rfl
      · rfl
      · exact False.elim (hSignNe (hs1.trans hs2.symm))
    · simp [hk]
  have hRatioNegOne : cycIntMul w.chal.invIntPoly w.chal'.toIntPoly = cycIntNeg cycIntOne := by
    rw [hChalNeg]
    have hNegR : cycIntNeg w.chal.toIntPoly = cycIntScale (-1) w.chal.toIntPoly := by
      funext k; unfold cycIntNeg cycIntScale; omega
    have hNeg1 : cycIntNeg (@cycIntOne (2 ^ nu)) = cycIntScale (-1) cycIntOne := by
      funext k; unfold cycIntNeg cycIntScale; omega
    rw [hNegR, cycIntMul_scale_right, w.chal.invIntPoly_mul, hNeg1]
  have hrTwo : w.rRel = cycIntScale 2 cycIntOne := by
    rw [w.rRel_eq, hRatioNegOne]
    funext k; unfold cycIntSub cycIntNeg cycIntScale cycIntOne
    split <;> omega
  refine ⟨hrTwo, ?_⟩
  rw [w.short_relaxed_rlwe_mod_q, hrTwo, cycIntToZq_scale, cycIntToZq_one]
  rw [← cycIntToZq_one q, ← cycIntToZq_scale, ← cycIntToZq_toNatInt (stmt.branchU w.branch),
      ← cycIntToZq_mul, cycIntMul_scale_left, cycIntMul_one_left (Nat.two_pow_pos nu),
      cycIntToZq_scale, cycIntToZq_toNatInt]

/-- Short RLWE key relation $A \cdot s^* + e^* = u$ in $R_q$ with $\|s^*\|_\infty, \|e^*\|_\infty \le B^*$. -/
structure ShortRlweKeyRelation {nu q : Nat} [NeZero q]
    (A u : CycPolyZq nu q) (Bsec : Nat) (sTrue eTrue : CycPolyInt nu) : Prop where
  s_short : cycIntInfNorm sTrue ≤ Bsec
  e_short : cycIntInfNorm eTrue ≤ Bsec
  key_eq : cycZqAdd (cycZqMul A (cycIntToZq q sTrue)) (cycIntToZq q eTrue) = u

private theorem modZq_ofInt_eq_zero_iff_of_lt {q : Nat} [NeZero q] {z : Int}
    (hz : z.natAbs < q) : ModZq.ofInt q z = ModZq.zero q ↔ z = 0 := by
  constructor
  · intro hZero
    have hv := ModZq.ofInt_val_int q z
    rw [hZero] at hv
    dsimp only [ModZq.zero] at hv
    have hDef := Int.emod_def z (q : Int)
    rw [← hv] at hDef
    have hDiv : (q : Int) * (z / (q : Int)) = z := by omega
    by_cases hq0 : z / (q : Int) = 0
    · rw [hq0, Int.mul_zero] at hDiv; exact hDiv.symm
    · exfalso
      have hAbsMul : z.natAbs = q * (z / (q : Int)).natAbs := by
        conv => lhs; rw [← hDiv]
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      have hQuotPos : 1 ≤ (z / (q : Int)).natAbs := by omega
      have hGeQ : q ≤ q * (z / (q : Int)).natAbs := by
        simpa using Nat.mul_le_mul_left q hQuotPos
      omega
  · intro hz0; subst hz0; exact ModZq.ofInt_zero q

/-- **Exact Search-RLWE Recovery OR Short-Ring-SIS Dichotomy (`short_monomial_witness_recovers_secret_or_breaks_short_sis`, `H2`)**:
    Against ANY short RLWE secret $(s^*, e^*)$ satisfying $A \cdot s^* + e^* = u_b$ with
    $\|s^*\|_\infty, \|e^*\|_\infty \le B^*$ (`B^* < q / 2` and `2 * stmt.Bz + 2 * B^* < q`; at
    production $q = 12289, B_z = 3070$ this gives $\|s_{\mathrm{sis}}\|_\infty \le 6142 < 6144 = \lfloor q/2 \rfloor$
    for ternary $B^* = 1$ and $\le 6144 < 12289$ for two-branch CRS difference $B^* = 2$), every
    extracted `ShortMonomialRelaxedRlweWitness` constructively (`0 Classical.choice`) yields **either**:
    1. **Exact Integer RLWE Key Recovery**:
       $\mathrm{centered}(r_{\mathrm{rel}}^{-1} \cdot s_{\mathrm{iso}} \bmod q) = s^*$ and
       $\mathrm{centered}(r_{\mathrm{rel}}^{-1} \cdot e_{\mathrm{iso}} \bmod q) = e^*$ over $\mathbb{Z}$, **or**
    2. **Non-Zero Short Ring-SIS Solution**:
       $(s_{\mathrm{sis}}, e_{\mathrm{sis}}) = (s_{\mathrm{iso}} - r_{\mathrm{rel}} \circledast s^*, e_{\mathrm{iso}} - r_{\mathrm{rel}} \circledast e^*)$
       is non-zero in $R_q \times R_q$, satisfies $A \cdot s_{\mathrm{sis}} + e_{\mathrm{sis}} = 0$ in $R_q$,
       and has short $\ell_\infty$ norm $\|s_{\mathrm{sis}}\|_\infty, \|e_{\mathrm{sis}}\|_\infty \le 2 B_z + 2 B^* < q$! -/
theorem short_monomial_witness_recovers_secret_or_breaks_short_sis {R nu q : Nat} [NeZero q]
    (hOdd : q % 2 = 1) (hq3 : 3 ≤ q)
    {stmt : RlweOrSigmaStatement nu q}
    (w : ShortMonomialRelaxedRlweWitness R nu q stmt)
    (Bsec : Nat) (sTrue eTrue : CycPolyInt nu)
    (hBsecLt : Bsec < q / 2)
    (hSisLtQ : 2 * stmt.Bz + 2 * Bsec < q)
    (hKey : ShortRlweKeyRelation stmt.A (stmt.branchU w.branch) Bsec sTrue eTrue) :
    let sSis := cycIntSub w.sIso (cycIntMul w.rRel sTrue)
    let eSis := cycIntSub w.eIso (cycIntMul w.rRel eTrue)
    (cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq q w.sIso)) = sTrue ∧
     cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq q w.eIso)) = eTrue) ∨
    ((cycIntToZq q sSis ≠ cycZqZero ∨ cycIntToZq q eSis ≠ cycZqZero) ∧
     cycIntInfNorm sSis ≤ 2 * stmt.Bz + 2 * Bsec ∧
     cycIntInfNorm eSis ≤ 2 * stmt.Bz + 2 * Bsec ∧
     cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSis)) (cycIntToZq q eSis) = cycZqZero) := by
  intro sSis eSis
  obtain ⟨hsTrue, heTrue, hKeyEq⟩ := hKey
  have hsSisNorm : cycIntInfNorm sSis ≤ 2 * stmt.Bz + 2 * Bsec := by
    dsimp only [sSis]
    have hSub := cycIntInfNorm_sub_le w.sIso (cycIntMul w.rRel sTrue)
    have hMul := cycIntInfNorm_mul_le w.rRel sTrue
    have h1 := w.sIso_infNorm_le
    have h2 : cycIntL1Norm w.rRel * cycIntInfNorm sTrue ≤ 2 * Bsec :=
      Nat.mul_le_mul w.rRel_l1_le hsTrue
    omega
  have heSisNorm : cycIntInfNorm eSis ≤ 2 * stmt.Bz + 2 * Bsec := by
    dsimp only [eSis]
    have hSub := cycIntInfNorm_sub_le w.eIso (cycIntMul w.rRel eTrue)
    have hMul := cycIntInfNorm_mul_le w.rRel eTrue
    have h1 := w.eIso_infNorm_le
    have h2 : cycIntL1Norm w.rRel * cycIntInfNorm eTrue ≤ 2 * Bsec :=
      Nat.mul_le_mul w.rRel_l1_le heTrue
    omega
  have hSisRel : cycZqAdd (cycZqMul stmt.A (cycIntToZq q sSis)) (cycIntToZq q eSis) = cycZqZero := by
    dsimp only [sSis, eSis]
    rw [cycIntToZq_sub, cycIntToZq_sub, cycZqMul_sub_right, cycIntToZq_mul, cycIntToZq_mul]
    have hAMul : cycZqMul stmt.A (cycZqMul (cycIntToZq q w.rRel) (cycIntToZq q sTrue)) =
        cycZqMul (cycIntToZq q w.rRel) (cycZqMul stmt.A (cycIntToZq q sTrue)) := by
      rw [← cycZqMul_assoc, cycZqMul_comm stmt.A (cycIntToZq q w.rRel), cycZqMul_assoc]
    have hSubReorder : ∀ (X1 X2 Y1 Y2 : CycPolyZq nu q),
        cycZqAdd (cycZqSub X1 Y1) (cycZqSub X2 Y2) =
        cycZqSub (cycZqAdd X1 X2) (cycZqAdd Y1 Y2) := by
      intro X1 X2 Y1 Y2; funext k
      let x1 : Int := (X1 k).val
      let x2 : Int := (X2 k).val
      let y1 : Int := (Y1 k).val
      let y2 : Int := (Y2 k).val
      have hx1 : X1 k = ModZq.ofInt q x1 := (ModZq.ofInt_natVal (X1 k)).symm
      have hx2 : X2 k = ModZq.ofInt q x2 := (ModZq.ofInt_natVal (X2 k)).symm
      have hy1 : Y1 k = ModZq.ofInt q y1 := (ModZq.ofInt_natVal (Y1 k)).symm
      have hy2 : Y2 k = ModZq.ofInt q y2 := (ModZq.ofInt_natVal (Y2 k)).symm
      have hIntEq : (x1 - y1) + (x2 - y2) = (x1 + x2) - (y1 + y2) := by omega
      show ModZq.add (ModZq.sub (X1 k) (Y1 k)) (ModZq.sub (X2 k) (Y2 k)) =
           ModZq.sub (ModZq.add (X1 k) (X2 k)) (ModZq.add (Y1 k) (Y2 k))
      rw [hx1, hx2, hy1, hy2]
      simp only [← ModZq.ofInt_add, ← ModZq.ofInt_sub]
      exact congrArg (ModZq.ofInt q) hIntEq
    rw [hSubReorder, w.short_relaxed_rlwe_mod_q, hAMul, ← cycZqMul_left_distrib,
        hKeyEq, cycZqSub_self]
  by_cases hBothZ : cycZqEq (cycIntToZq q sSis) cycZqZero = true ∧
                    cycZqEq (cycIntToZq q eSis) cycZqZero = true
  · left
    have hsZqZero : cycIntToZq q sSis = cycZqZero := (cycZqEq_iff _ _).mp hBothZ.1
    have heZqZero : cycIntToZq q eSis = cycZqZero := (cycZqEq_iff _ _).mp hBothZ.2
    have hsEqInt : w.sIso = cycIntMul w.rRel sTrue := by
      funext k
      have hk := congrFun hsZqZero k
      have hkLt : (sSis k).natAbs < q :=
        Nat.lt_of_le_of_lt (cycCoeff_natAbs_le_infNorm sSis k) (Nat.lt_of_le_of_lt hsSisNorm hSisLtQ)
      have hk0 := (modZq_ofInt_eq_zero_iff_of_lt hkLt).mp hk
      dsimp only [sSis, cycIntSub] at hk0
      omega
    have heEqInt : w.eIso = cycIntMul w.rRel eTrue := by
      funext k
      have hk := congrFun heZqZero k
      have hkLt : (eSis k).natAbs < q :=
        Nat.lt_of_le_of_lt (cycCoeff_natAbs_le_infNorm eSis k) (Nat.lt_of_le_of_lt heSisNorm hSisLtQ)
      have hk0 := (modZq_ofInt_eq_zero_iff_of_lt hkLt).mp hk
      dsimp only [eSis, cycIntSub] at hk0
      omega
    have hInv := (short_monomial_witness_rRel_invertible hOdd hq3 w).2.1
    refine ⟨?_, ?_⟩
    · rw [hsEqInt, cycIntToZq_mul, ← cycZqMul_assoc, hInv, cycZqMul_one_left (Nat.two_pow_pos nu)]
      funext k; unfold cycZqCentered cycIntToZq
      apply ModZq.centered_ofInt_exact
      left
      exact Nat.lt_of_le_of_lt (Nat.le_trans (cycCoeff_natAbs_le_infNorm sTrue k) hsTrue) hBsecLt
    · rw [heEqInt, cycIntToZq_mul, ← cycZqMul_assoc, hInv, cycZqMul_one_left (Nat.two_pow_pos nu)]
      funext k; unfold cycZqCentered cycIntToZq
      apply ModZq.centered_ofInt_exact
      left
      exact Nat.lt_of_le_of_lt (Nat.le_trans (cycCoeff_natAbs_le_infNorm eTrue k) heTrue) hBsecLt
  · right
    have hNz : cycIntToZq q sSis ≠ cycZqZero ∨ cycIntToZq q eSis ≠ cycZqZero := by
      by_cases hsZ : cycZqEq (cycIntToZq q sSis) cycZqZero = true
      · right
        intro heEq
        exact hBothZ ⟨hsZ, (cycZqEq_iff _ _).mpr heEq⟩
      · left
        intro hsEq
        exact hsZ ((cycZqEq_iff _ _).mpr hsEq)
    exact ⟨hNz, hsSisNorm, heSisNorm, hSisRel⟩

private def extractSingleBranchShortWitness {R nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (i : Fin R) (b : Bool)
    (tShared : CycPolyZq nu q)
    (chal chal' : SignedMonomialChal nu)
    (zs ze zs' ze' : CycPolyInt nu)
    (hChalNe : chal ≠ chal')
    (hzs : cycIntInfNorm zs ≤ stmt.Bz) (hze : cycIntInfNorm ze ≤ stmt.Bz)
    (hzs' : cycIntInfNorm zs' ≤ stmt.Bz) (hze' : cycIntInfNorm ze' ≤ stmt.Bz)
    (hEq1 : cycZqAdd (cycZqMul stmt.A (cycIntToZq q zs)) (cycIntToZq q ze) =
      cycZqAdd tShared (cycZqMul (chal.toZqPoly q) (stmt.branchU b)))
    (hEq2 : cycZqAdd (cycZqMul stmt.A (cycIntToZq q zs')) (cycIntToZq q ze') =
      cycZqAdd tShared (cycZqMul (chal'.toZqPoly q) (stmt.branchU b))) :
    ShortMonomialRelaxedRlweWitness R nu q stmt :=
  ShortMonomialRelaxedRlweWitness.ofForkDifference stmt i b chal chal' hChalNe
    (cycIntSub zs zs') (cycIntSub ze ze')
    (by have hSub := cycIntInfNorm_sub_le zs zs'; omega)
    (by have hSub := cycIntInfNorm_sub_le ze ze'; omega)
    (rlwe_sigma_fork_difference_relation stmt.A (stmt.branchU b) tShared
      chal.toIntPoly chal'.toIntPoly zs ze zs' ze' hEq1 hEq2)

/-- Constructive `R`-parallel short isometric signed-monomial witness extractor (`0 Classical.choice`). -/
def extractRlweOrSigmaShortWitnessGen (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin R → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript R nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma R nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma R nu q stmt c' tr' = true) :
    ShortMonomialRelaxedRlweWitness R nu q stmt :=
  let ⟨i, hiNe⟩ := findDiffChalFin R c c' hcNe
  have hRep : verifyRlweOrSigmaRep stmt i (c i) tr = true :=
    (verifyRlweOrSigma_iff R nu q stmt c tr).mp hAcc i
  have hRep' : verifyRlweOrSigmaRep stmt i (c' i) tr' = true :=
    (verifyRlweOrSigma_iff R nu q stmt c' tr').mp hAcc' i
  if hc0Eq : tr.c0 i = tr'.c0 i then
    have hc1Ne : tr.c1 i ≠ tr'.c1 i := by
      intro hc1Eq
      unfold verifyRlweOrSigmaRep at hRep hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hRep hRep'
      have hXor := hRep.1.1.1
      have hXor' := hRep'.1.1.1
      rw [hc0Eq, hc1Eq] at hXor
      exact hiNe (hXor.symm.trans hXor')
    have hU : cycIntInfNorm (tr.zs1 i) ≤ stmt.Bz ∧
              cycIntInfNorm (tr.ze1 i) ≤ stmt.Bz ∧
              cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs1 i))) (cycIntToZq q (tr.ze1 i)) =
                cycZqAdd (tr.t1 i) (cycZqMul ((tr.c1 i).toZqPoly q) stmt.u1) := by
      unfold verifyRlweOrSigmaRep at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep
      exact ⟨hRep.1.1.2.1.2, hRep.1.1.2.2, hRep.2⟩
    have hU' : cycIntInfNorm (tr'.zs1 i) ≤ stmt.Bz ∧
               cycIntInfNorm (tr'.ze1 i) ≤ stmt.Bz ∧
               cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr'.zs1 i))) (cycIntToZq q (tr'.ze1 i)) =
                 cycZqAdd (tr.t1 i) (cycZqMul ((tr'.c1 i).toZqPoly q) stmt.u1) := by
      unfold verifyRlweOrSigmaRep at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep'
      rw [← ht1] at hRep'
      exact ⟨hRep'.1.1.2.1.2, hRep'.1.1.2.2, hRep'.2⟩
    extractSingleBranchShortWitness stmt i true (tr.t1 i)
      (tr.c1 i) (tr'.c1 i) (tr.zs1 i) (tr.ze1 i) (tr'.zs1 i) (tr'.ze1 i)
      hc1Ne hU.1 hU.2.1 hU'.1 hU'.2.1 hU.2.2 hU'.2.2
  else
    have hU : cycIntInfNorm (tr.zs0 i) ≤ stmt.Bz ∧
              cycIntInfNorm (tr.ze0 i) ≤ stmt.Bz ∧
              cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr.zs0 i))) (cycIntToZq q (tr.ze0 i)) =
                cycZqAdd (tr.t0 i) (cycZqMul ((tr.c0 i).toZqPoly q) stmt.u0) := by
      unfold verifyRlweOrSigmaRep at hRep
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep
      exact ⟨hRep.1.1.2.1.1.1, hRep.1.1.2.1.1.2, hRep.1.2⟩
    have hU' : cycIntInfNorm (tr'.zs0 i) ≤ stmt.Bz ∧
               cycIntInfNorm (tr'.ze0 i) ≤ stmt.Bz ∧
               cycZqAdd (cycZqMul stmt.A (cycIntToZq q (tr'.zs0 i))) (cycIntToZq q (tr'.ze0 i)) =
                 cycZqAdd (tr.t0 i) (cycZqMul ((tr'.c0 i).toZqPoly q) stmt.u0) := by
      unfold verifyRlweOrSigmaRep at hRep'
      simp only [Bool.and_eq_true, decide_eq_true_eq, cycZqEq_iff] at hRep'
      rw [← ht0] at hRep'
      exact ⟨hRep'.1.1.2.1.1.1, hRep'.1.1.2.1.1.2, hRep'.1.2⟩
    extractSingleBranchShortWitness stmt i false (tr.t0 i)
      (tr.c0 i) (tr'.c0 i) (tr.zs0 i) (tr.ze0 i) (tr'.zs0 i) (tr'.ze0 i)
      hc0Eq hU.1 hU.2.1 hU'.1 hU'.2.1 hU.2.2 hU'.2.2

/-- **13-Parallel Short Isometric RLWE OR-Sigma Witness Extractor (`extract_rlwe_or_sigma_13_short_witness`, `H2`)**:
    Extracts $(s_{\mathrm{iso}}, e_{\mathrm{iso}}, r_{\mathrm{rel}})$ with **strictly sub-half-modulus $\ell_\infty$ norm**
    $\|s_{\mathrm{iso}}\|_\infty, \|e_{\mathrm{iso}}\|_\infty \le 2 B_z = 6140 < 6144 = \lfloor 12289 / 2 \rfloor$,
    $\|r_{\mathrm{rel}}\|_1 \le 2$, $r_{\mathrm{rel}} \in R_q^\times$, and $A \cdot s_{\mathrm{iso}} + e_{\mathrm{iso}} = r_{\mathrm{rel}} \cdot u_b$! -/
def extract_rlwe_or_sigma_13_short_witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 13 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 13 nu q stmt c' tr' = true) :
    ShortMonomialRelaxedRlweWitness 13 nu q stmt :=
  extractRlweOrSigmaShortWitnessGen 13 nu q stmt c c' tr tr' ht0 ht1 hcNe hAcc hAcc'

/-- Named fork predicate for `R`-parallel OR-Sigma transcripts. -/
structure ValidRlweOrSigmaFork (R nu q : Nat) [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin R → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript R nu q) : Prop where
  t0_eq : tr.t0 = tr'.t0
  t1_eq : tr.t1 = tr'.t1
  chal_ne : c ≠ c'
  acc1 : verifyRlweOrSigma R nu q stmt c tr = true
  acc2 : verifyRlweOrSigma R nu q stmt c' tr' = true

/-- Production $N = 1024, q = 12289$ short extraction soundness (`‖sIso‖_∞, ‖eIso‖_∞ ≤ 6140 < 6144`, zero wraparound). -/
theorem extract_rlwe_or_sigma_13_short_witness_1024_sound
    (stmt : RlweOrSigmaStatement 10 12289)
    (c c' : Fin 13 → SignedMonomialChal 10)
    (tr tr' : RlweOrSigmaTranscript 13 10 12289)
    (hBz : stmt.Bz ≤ rlweProductionBz)
    (hFork : ValidRlweOrSigmaFork 13 10 12289 stmt c c' tr tr') :
    let w := extract_rlwe_or_sigma_13_short_witness stmt c c' tr tr'
      hFork.t0_eq hFork.t1_eq hFork.chal_ne hFork.acc1 hFork.acc2
    cycIntInfNorm w.sIso ≤ 6140 ∧
    cycIntInfNorm w.eIso ≤ 6140 ∧
    6140 < 12289 / 2 ∧
    cycIntL1Norm w.rRel ≤ 2 ∧
    cycZqMul (cycIntToZq 12289 w.rRel) w.rRelInvZq = cycZqOne ∧
    cycZqCentered (cycIntToZq 12289 w.sIso) = w.sIso ∧
    cycZqCentered (cycIntToZq 12289 w.eIso) = w.eIso ∧
    cycZqAdd (cycZqMul stmt.A (cycIntToZq 12289 w.sIso)) (cycIntToZq 12289 w.eIso) =
      cycZqMul (cycIntToZq 12289 w.rRel) (stmt.branchU w.branch) := by
  intro w
  have hNoWrap := short_monomial_witness_zero_wraparound_production hBz w
  have hInv := (short_monomial_witness_rRel_invertible (by decide) (by decide) w).1
  exact ⟨hNoWrap.1, hNoWrap.2.1, hNoWrap.2.2.1, w.rRel_l1_le, hInv,
         hNoWrap.2.2.2.1, hNoWrap.2.2.2.2, w.short_relaxed_rlwe_mod_q⟩

/-- Total choice-free `PSum`-valued computational short witness extractor (`‖sIso‖_∞ ≤ 2 * B_z`). -/
def tryExtractShortMonomialOr13Witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q) :
    PSum (ShortMonomialRelaxedRlweWitness 13 nu q stmt) RlweOrSigmaExtractRefusal :=
  if ht0 : cycAllFin 13 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true then
    if ht1 : cycAllFin 13 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true then
      if hAcc : verifyRlweOrSigma 13 nu q stmt c tr = true then
        if hAcc' : verifyRlweOrSigma 13 nu q stmt c' tr' = true then
          if hcEq : cycAllFin 13 (fun i => decide (c i = c' i)) = true then
            PSum.inr .identicalJointChallenges
          else
            have ht0Eq : tr.t0 = tr'.t0 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht0 i)
            have ht1Eq : tr.t1 = tr'.t1 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht1 i)
            have hcNe : c ≠ c' := by
              intro hEq; apply hcEq
              rw [cycAllFin_eq_true_iff]; intro i; subst hEq; exact decide_eq_true rfl
            PSum.inl (extract_rlwe_or_sigma_13_short_witness stmt c c' tr tr' ht0Eq ht1Eq hcNe hAcc hAcc')
        else
          PSum.inr .secondTranscriptInvalid
      else
        PSum.inr .firstTranscriptInvalid
    else
      PSum.inr .commitmentMismatchT1
  else
    PSum.inr .commitmentMismatchT0

theorem tryExtractShortMonomialOr13Witness_complete {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q)
    (hFork : ValidRlweOrSigmaFork 13 nu q stmt c c' tr tr') :
    ∃ w, tryExtractShortMonomialOr13Witness stmt c c' tr tr' = PSum.inl w := by
  obtain ⟨ht0, ht1, hcNe, hAcc, hAcc'⟩ := hFork
  have ht0Bool : cycAllFin 13 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht0]; exact (cycZqEq_iff _ _).mpr rfl
  have ht1Bool : cycAllFin 13 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht1]; exact (cycZqEq_iff _ _).mpr rfl
  have hcEqFalse : ¬(cycAllFin 13 (fun i => decide (c i = c' i)) = true) := by
    intro hAll; apply hcNe; funext i
    exact of_decide_eq_true ((cycAllFin_eq_true_iff _).mp hAll i)
  unfold tryExtractShortMonomialOr13Witness
  simp only [ht0Bool, ht1Bool, hAcc, hAcc', hcEqFalse, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-! ### 3.0b 24-Challenge `PQ128` Signed-Monomial RLWE OR-Sigma Profile ($R = 24$, $264$ Classical / $132$ Grover Bits)

While $R = 13$ parallel repetitions over the $2 \cdot 2^{10} = 2048$-element signed-monomial set
yield $(2^{11})^{13} = 2^{143}$ joint challenges ($71.5$ Grover bits, below the $128$-bit quantum
threshold), setting $R = 24$ (`rlweOrSigmaPq128Reps`) yields $(2^{11})^{24} = 2^{264} = (2^{132})^2$
joint challenges ($264$ classical bits / $132$ Grover bits $\ge 128$ quantum bits) while preserving
the exact same wraparound-free $\ell_\infty \le 2 B_z = 6140 < 6144 = \lfloor 12289 / 2 \rfloor$
short isometric witness extraction! -/

/-- `PQ128` parallel repetition count `R = 24` (`24 * 11 = 264` classical challenge bits,
    `132` Grover bits `≥ 128` quantum bits). -/
def rlweOrSigmaPq128Reps : Nat := 24

/-- Exact cardinality `(2 * 2^nu)^R` of the `R`-parallel signed-monomial joint challenge space. -/
def rlweOrSigmaChallengeCard (nu R : Nat) : Nat := (2 * 2 ^ nu) ^ R

set_option exponentiation.threshold 512 in
/-- At `nu = 10` (`N = 1024`), `R = 24` gives `2^264 = (2^132)^2 ≥ (2^128)^2` challenge vectors
    (`132` Grover bits), whereas `R = 13` gives `2^143 < (2^72)^2` (`< 72` Grover bits). -/
theorem rlwe_or_sigma_24_pq128_vs_13_grover_ceiling :
    rlweOrSigmaChallengeCard 10 rlweOrSigmaPq128Reps = 2 ^ 264 ∧
    (2 ^ 132) ^ 2 = rlweOrSigmaChallengeCard 10 rlweOrSigmaPq128Reps ∧
    (2 ^ 128) ^ 2 ≤ rlweOrSigmaChallengeCard 10 rlweOrSigmaPq128Reps ∧
    rlweOrSigmaChallengeCard 10 13 = 2 ^ 143 ∧
    rlweOrSigmaChallengeCard 10 13 < (2 ^ 72) ^ 2 := by
  have h24 : rlweOrSigmaChallengeCard 10 rlweOrSigmaPq128Reps = 2 ^ (11 * 24) := by
    unfold rlweOrSigmaChallengeCard rlweOrSigmaPq128Reps
    have hBase : 2 * 2 ^ 10 = 2 ^ 11 := by decide
    rw [hBase, ← Nat.pow_mul]
  have h132 : (2 ^ 132) ^ 2 = 2 ^ (132 * 2) := (Nat.pow_mul 2 132 2).symm
  have h128 : (2 ^ 128) ^ 2 = 2 ^ (128 * 2) := (Nat.pow_mul 2 128 2).symm
  refine ⟨h24, ?_, ?_, by decide, by decide⟩
  · rw [h132, h24]
  · rw [h128, h24]; exact Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 128 * 2 ≤ 11 * 24)

/-- **24-Parallel Cofactor RLWE OR-Sigma Witness Extractor (`extract_rlwe_or_sigma_24_witness`)**:
    Extracts `(s2, e2)` satisfying `A * s2 + e2 ≡ 2 * u_b (mod q)` with `‖s2‖_∞, ‖e2‖_∞ ≤ 2 * 2^nu * B_z`
    from any valid 24-challenge fork. -/
def extract_rlwe_or_sigma_24_witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 24 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 24 nu q stmt c' tr' = true) :
    ExtractedRlweOrSigmaWitness 24 nu q stmt :=
  extractRlweOrSigmaWitnessGen 24 nu q stmt c c' tr tr' ht0 ht1 hcNe hAcc hAcc'

/-- Total choice-free `PSum` computational cofactor extractor for the 24-parallel `PQ128` profile. -/
def tryExtractRlweOrSigma24Witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q) :
    PSum (ExtractedRlweOrSigmaWitness 24 nu q stmt) RlweOrSigmaExtractRefusal :=
  if ht0 : cycAllFin 24 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true then
    if ht1 : cycAllFin 24 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true then
      if hAcc : verifyRlweOrSigma 24 nu q stmt c tr = true then
        if hAcc' : verifyRlweOrSigma 24 nu q stmt c' tr' = true then
          if hcEq : cycAllFin 24 (fun i => decide (c i = c' i)) = true then
            PSum.inr .identicalJointChallenges
          else
            have ht0Eq : tr.t0 = tr'.t0 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht0 i)
            have ht1Eq : tr.t1 = tr'.t1 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht1 i)
            have hcNe : c ≠ c' := by
              intro hEq; apply hcEq
              rw [cycAllFin_eq_true_iff]; intro i; subst hEq; exact decide_eq_true rfl
            PSum.inl (extract_rlwe_or_sigma_24_witness stmt c c' tr tr' ht0Eq ht1Eq hcNe hAcc hAcc')
        else
          PSum.inr .secondTranscriptInvalid
      else
        PSum.inr .firstTranscriptInvalid
    else
      PSum.inr .commitmentMismatchT1
  else
    PSum.inr .commitmentMismatchT0

theorem tryExtractRlweOrSigma24Witness_complete {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 24 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 24 nu q stmt c' tr' = true) :
    ∃ w, tryExtractRlweOrSigma24Witness stmt c c' tr tr' = PSum.inl w := by
  have ht0Bool : cycAllFin 24 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht0]; exact (cycZqEq_iff _ _).mpr rfl
  have ht1Bool : cycAllFin 24 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht1]; exact (cycZqEq_iff _ _).mpr rfl
  have hcEqFalse : ¬(cycAllFin 24 (fun i => decide (c i = c' i)) = true) := by
    intro hAll; apply hcNe; funext i
    exact of_decide_eq_true ((cycAllFin_eq_true_iff _).mp hAll i)
  unfold tryExtractRlweOrSigma24Witness
  simp only [ht0Bool, ht1Bool, hAcc, hAcc', hcEqFalse, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- **24-Parallel `PQ128` Short Isometric RLWE OR-Sigma Witness Extractor
    (`extract_rlwe_or_sigma_24_short_witness`)**:
    Extracts `(sIso, eIso, rRel)` with strictly wraparound-free $\ell_\infty$ norm
    `‖sIso‖_∞, ‖eIso‖_∞ ≤ 2 * B_z` (`6140 < 6144 = ⌊12289 / 2⌋`), `‖rRel‖_1 ≤ 2`,
    `rRel ∈ R_q^×`, and `A * sIso + eIso = rRel * u_b` over the 264-bit / 132-Grover-bit
    24-repetition signed-monomial challenge space! -/
def extract_rlwe_or_sigma_24_short_witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q)
    (ht0 : tr.t0 = tr'.t0) (ht1 : tr.t1 = tr'.t1)
    (hcNe : c ≠ c')
    (hAcc : verifyRlweOrSigma 24 nu q stmt c tr = true)
    (hAcc' : verifyRlweOrSigma 24 nu q stmt c' tr' = true) :
    ShortMonomialRelaxedRlweWitness 24 nu q stmt :=
  extractRlweOrSigmaShortWitnessGen 24 nu q stmt c c' tr tr' ht0 ht1 hcNe hAcc hAcc'

/-- Production $N = 1024, q = 12289$ 24-challenge `PQ128` short extraction soundness
    (`‖sIso‖_∞, ‖eIso‖_∞ ≤ 6140 < 6144`, zero wraparound, invertible `rRel`). -/
theorem extract_rlwe_or_sigma_24_short_witness_1024_sound
    (stmt : RlweOrSigmaStatement 10 12289)
    (c c' : Fin 24 → SignedMonomialChal 10)
    (tr tr' : RlweOrSigmaTranscript 24 10 12289)
    (hBz : stmt.Bz ≤ rlweProductionBz)
    (hFork : ValidRlweOrSigmaFork 24 10 12289 stmt c c' tr tr') :
    let w := extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
      hFork.t0_eq hFork.t1_eq hFork.chal_ne hFork.acc1 hFork.acc2
    cycIntInfNorm w.sIso ≤ 6140 ∧
    cycIntInfNorm w.eIso ≤ 6140 ∧
    6140 < 12289 / 2 ∧
    cycIntL1Norm w.rRel ≤ 2 ∧
    cycZqMul (cycIntToZq 12289 w.rRel) w.rRelInvZq = cycZqOne ∧
    cycZqCentered (cycIntToZq 12289 w.sIso) = w.sIso ∧
    cycZqCentered (cycIntToZq 12289 w.eIso) = w.eIso ∧
    cycZqAdd (cycZqMul stmt.A (cycIntToZq 12289 w.sIso)) (cycIntToZq 12289 w.eIso) =
      cycZqMul (cycIntToZq 12289 w.rRel) (stmt.branchU w.branch) := by
  intro w
  have hNoWrap := short_monomial_witness_zero_wraparound_production hBz w
  have hInv := (short_monomial_witness_rRel_invertible (by decide) (by decide) w).1
  exact ⟨hNoWrap.1, hNoWrap.2.1, hNoWrap.2.2.1, w.rRel_l1_le, hInv,
         hNoWrap.2.2.2.1, hNoWrap.2.2.2.2, w.short_relaxed_rlwe_mod_q⟩

/-- **24-Challenge `PQ128` Secret Recovery or Short Ring-SIS Break
    (`extract_rlwe_or_sigma_24_recovers_secret_or_breaks_short_sis`)**:
    Any valid 24-challenge fork at `N = 1024, q = 12289` either recovers the planted short RLWE
    secret `(sTrue, eTrue)` on the active branch via `rRelInvZq`, OR yields a non-zero short
    homogeneous Ring-SIS vector `(sSis, eSis)` (`‖sSis‖_∞, ‖eSis‖_∞ ≤ 2 * B_z + 2 * B_sec`)! -/
theorem extract_rlwe_or_sigma_24_recovers_secret_or_breaks_short_sis
    (stmt : RlweOrSigmaStatement 10 12289)
    (c c' : Fin 24 → SignedMonomialChal 10)
    (tr tr' : RlweOrSigmaTranscript 24 10 12289)
    (hFork : ValidRlweOrSigmaFork 24 10 12289 stmt c c' tr tr')
    (Bsec : Nat) (sTrue eTrue : CycPolyInt 10)
    (hBsecLt : Bsec < 12289 / 2)
    (hSisLtQ : 2 * stmt.Bz + 2 * Bsec < 12289)
    (hKey : ShortRlweKeyRelation stmt.A
      (stmt.branchU (extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
        hFork.t0_eq hFork.t1_eq hFork.chal_ne hFork.acc1 hFork.acc2).branch)
      Bsec sTrue eTrue) :
    let w := extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
      hFork.t0_eq hFork.t1_eq hFork.chal_ne hFork.acc1 hFork.acc2
    let sSis := cycIntSub w.sIso (cycIntMul w.rRel sTrue)
    let eSis := cycIntSub w.eIso (cycIntMul w.rRel eTrue)
    (cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.sIso)) = sTrue ∧
     cycZqCentered (cycZqMul w.rRelInvZq (cycIntToZq 12289 w.eIso)) = eTrue) ∨
    ((cycIntToZq 12289 sSis ≠ cycZqZero ∨ cycIntToZq 12289 eSis ≠ cycZqZero) ∧
     cycIntInfNorm sSis ≤ 2 * stmt.Bz + 2 * Bsec ∧
     cycIntInfNorm eSis ≤ 2 * stmt.Bz + 2 * Bsec ∧
     cycZqAdd (cycZqMul stmt.A (cycIntToZq 12289 sSis)) (cycIntToZq 12289 eSis) = cycZqZero) :=
  short_monomial_witness_recovers_secret_or_breaks_short_sis (by decide) (by decide)
    (extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr'
      hFork.t0_eq hFork.t1_eq hFork.chal_ne hFork.acc1 hFork.acc2)
    Bsec sTrue eTrue hBsecLt hSisLtQ hKey

/-- Total choice-free `PSum`-valued computational short witness extractor for the 24-challenge
    `PQ128` profile (`‖sIso‖_∞ ≤ 2 * B_z`). -/
def tryExtractShortMonomialOr24Witness {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q) :
    PSum (ShortMonomialRelaxedRlweWitness 24 nu q stmt) RlweOrSigmaExtractRefusal :=
  if ht0 : cycAllFin 24 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true then
    if ht1 : cycAllFin 24 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true then
      if hAcc : verifyRlweOrSigma 24 nu q stmt c tr = true then
        if hAcc' : verifyRlweOrSigma 24 nu q stmt c' tr' = true then
          if hcEq : cycAllFin 24 (fun i => decide (c i = c' i)) = true then
            PSum.inr .identicalJointChallenges
          else
            have ht0Eq : tr.t0 = tr'.t0 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht0 i)
            have ht1Eq : tr.t1 = tr'.t1 := by
              funext i; exact (cycZqEq_iff _ _).mp ((cycAllFin_eq_true_iff _).mp ht1 i)
            have hcNe : c ≠ c' := by
              intro hEq; apply hcEq
              rw [cycAllFin_eq_true_iff]; intro i; subst hEq; exact decide_eq_true rfl
            PSum.inl (extract_rlwe_or_sigma_24_short_witness stmt c c' tr tr' ht0Eq ht1Eq hcNe hAcc hAcc')
        else
          PSum.inr .secondTranscriptInvalid
      else
        PSum.inr .firstTranscriptInvalid
    else
      PSum.inr .commitmentMismatchT1
  else
    PSum.inr .commitmentMismatchT0

theorem tryExtractShortMonomialOr24Witness_complete {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c c' : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q)
    (hFork : ValidRlweOrSigmaFork 24 nu q stmt c c' tr tr') :
    ∃ w, tryExtractShortMonomialOr24Witness stmt c c' tr tr' = PSum.inl w := by
  obtain ⟨ht0, ht1, hcNe, hAcc, hAcc'⟩ := hFork
  have ht0Bool : cycAllFin 24 (fun i => cycZqEq (tr.t0 i) (tr'.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht0]; exact (cycZqEq_iff _ _).mpr rfl
  have ht1Bool : cycAllFin 24 (fun i => cycZqEq (tr.t1 i) (tr'.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; rw [ht1]; exact (cycZqEq_iff _ _).mpr rfl
  have hcEqFalse : ¬(cycAllFin 24 (fun i => decide (c i = c' i)) = true) := by
    intro hAll; apply hcNe; funext i
    exact of_decide_eq_true ((cycAllFin_eq_true_iff _).mp hAll i)
  unfold tryExtractShortMonomialOr24Witness
  simp only [ht0Bool, ht1Bool, hAcc, hAcc', hcEqFalse, ↓reduceDIte]
  exact ⟨_, rfl⟩

/-- Coefficient vector `ζ^(N - 1 - i)` of $(X^N - \zeta^N) / (X - \zeta)$. When $\zeta^N \equiv -1 \pmod q$
    it spans the kernel of evaluation-at-$\zeta$'s complementary factor: $X \cdot h \equiv \zeta \cdot h$ in $R_q$. -/
def cycRootCofactor (N : Nat) (zeta : Int) : NegacyclicPolyInt N :=
  fun i => zeta ^ (N - 1 - i.val)

private theorem cycIntPow_add (a : Int) (m : Nat) : ∀ n : Nat, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, Int.pow_zero, Int.mul_one]
  | n + 1 => by
    rw [← Nat.add_assoc, Int.pow_succ, Int.pow_succ, cycIntPow_add a m n, Int.mul_assoc]

private theorem ModZq.ofInt_eq_of_sub_emod {q : Nat} [NeZero q] {x y : Int}
    (h : (x - y) % (q : Int) = 0) : ModZq.ofInt q x = ModZq.ofInt q y := by
  apply ModZq.ext_int
  rw [ModZq.ofInt_val_int, ModZq.ofInt_val_int]
  have hDef := Int.emod_def (x - y) (q : Int)
  rw [h] at hDef
  have hComm := Int.mul_comm (q : Int) ((x - y) / (q : Int))
  have hx : x = y + ((x - y) / (q : Int)) * (q : Int) := by omega
  calc x % (q : Int) = (y + ((x - y) / (q : Int)) * (q : Int)) % (q : Int) := by rw [← hx]
    _ = y % (q : Int) := Int.add_mul_emod_self_right _ _ _

/-- **Monomials act on the root cofactor by evaluation
    (`negacyclicSignedMonomial_mul_cycRootCofactor`)**:
    if $\zeta^N \equiv -1 \pmod q$ then $(\pm X^k) \cdot h_\zeta \equiv (\pm \zeta^k) \cdot h_\zeta$ in
    $\mathbb{Z}_q[X]/(X^N + 1)$. -/
theorem negacyclicSignedMonomial_mul_cycRootCofactor {N q : Nat} [NeZero q]
    (zeta : Int) (hRoot : (zeta ^ N + 1) % (q : Int) = 0)
    (s : Bool) (k : Fin N) :
    cycIntToZq q (cycIntMul (negacyclicSignedMonomial s k) (cycRootCofactor N zeta)) =
    cycIntToZq q (cycIntScale (signBitToInt s * zeta ^ k.val) (cycRootCofactor N zeta)) := by
  funext j
  show ModZq.ofInt q (cycIntMul (negacyclicSignedMonomial s k) (cycRootCofactor N zeta) j) =
    ModZq.ofInt q (cycIntScale (signBitToInt s * zeta ^ k.val) (cycRootCofactor N zeta) j)
  rw [negacyclicSignedMonomial_mul_apply]
  apply ModZq.ofInt_eq_of_sub_emod
  have hk := k.isLt
  have hj := j.isLt
  by_cases hkj : k.val ≤ j.val
  · simp only [hkj, ↓reduceDIte]
    show (signBitToInt s * zeta ^ (N - 1 - (j.val - k.val)) -
      signBitToInt s * zeta ^ k.val * zeta ^ (N - 1 - j.val)) % (q : Int) = 0
    have hExp : N - 1 - (j.val - k.val) = k.val + (N - 1 - j.val) := by omega
    rw [hExp, cycIntPow_add, ← Int.mul_assoc, Int.sub_self]
    exact Int.zero_emod _
  · simp only [hkj, ↓reduceDIte]
    show (-(signBitToInt s * zeta ^ (N - 1 - (N + j.val - k.val))) -
      signBitToInt s * zeta ^ k.val * zeta ^ (N - 1 - j.val)) % (q : Int) = 0
    have hE1 : N - 1 - (N + j.val - k.val) = k.val - 1 - j.val := by omega
    have hE2 : k.val + (N - 1 - j.val) = (k.val - 1 - j.val) + N := by omega
    have hPow : zeta ^ k.val * zeta ^ (N - 1 - j.val) = zeta ^ (k.val - 1 - j.val) * zeta ^ N := by
      rw [← cycIntPow_add, ← cycIntPow_add, hE2]
    have hFactor : -(signBitToInt s * zeta ^ (N - 1 - (N + j.val - k.val))) -
        signBitToInt s * zeta ^ k.val * zeta ^ (N - 1 - j.val) =
        (-(signBitToInt s * zeta ^ (k.val - 1 - j.val))) * (zeta ^ N + 1) := by
      rw [hE1, Int.mul_assoc, hPow, Int.mul_add, Int.mul_one, Int.neg_mul]
      have hAssoc := Int.mul_assoc (signBitToInt s) (zeta ^ (k.val - 1 - j.val)) (zeta ^ N)
      omega
    rw [hFactor, Int.mul_emod, hRoot, Int.mul_zero, Int.zero_emod]

/-- Linear-recursion modular power `a^e mod q`, evaluated by the kernel without forming `a^e`. -/
private def powModLin (q a : Nat) : Nat → Nat
  | 0 => 1 % q
  | e + 1 => (powModLin q a e * (a % q)) % q

private theorem natPow_mod_eq_powModLin (q a : Nat) : ∀ e : Nat, a ^ e % q = powModLin q a e
  | 0 => by rw [Nat.pow_zero]; rfl
  | e + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, natPow_mod_eq_powModLin q a e]; rfl

private theorem nat_pow_add_one_mod (q a e : Nat)
    (h : (powModLin q a e + 1 % q) % q = 0) : (a ^ e + 1) % q = 0 := by
  rw [Nat.add_mod, natPow_mod_eq_powModLin]; exact h

private theorem nat_pow_add_pow_mod (q a e1 e2 : Nat) :
    (a ^ e1 + a ^ e2) % q = (powModLin q a e1 + powModLin q a e2) % q := by
  rw [Nat.add_mod, natPow_mod_eq_powModLin, natPow_mod_eq_powModLin]

private theorem int_two_sum_sub_emod_of_nat (a b c d q : Nat)
    (h : (a + b) % q = (c + d) % q) :
    ((1 : Int) * (a : Int) + 1 * (b : Int) - 1 * (c : Int) - 1 * (d : Int)) % (q : Int) = 0 := by
  have hE : (1 : Int) * (a : Int) + 1 * (b : Int) - 1 * (c : Int) - 1 * (d : Int) =
      ((a + b : Nat) : Int) - ((c + d : Nat) : Int) := by
    omega
  rw [hE, Int.sub_emod, ← Int.natCast_emod, ← Int.natCast_emod, h, Int.sub_self, Int.zero_emod]

private theorem int_four_term_factor_emod (c1 c2 c3 c4 H n : Int)
    (h : (c1 + c2 - c3 - c4) % n = 0) :
    ((c1 * H + c2 * H - (c3 * H + c4 * H)) - 0) % n = 0 := by
  have hFactor : (c1 * H + c2 * H - (c3 * H + c4 * H)) - 0 = (c1 + c2 - c3 - c4) * H := by
    rw [Int.sub_mul, Int.sub_mul, Int.add_mul]; omega
  rw [hFactor, Int.mul_emod, h, Int.zero_mul, Int.zero_emod]

/-- **A two-term challenge difference vanishing at a root of $X^N + 1$ annihilates the root cofactor
    (`two_term_difference_mul_cycRootCofactor_eq_zero`)**:
    if $\zeta^N \equiv -1$ and $\pm\zeta^{k_1} \pm \zeta^{k_2} \equiv \pm\zeta^{k_3} \pm \zeta^{k_4} \pmod q$, then
    $\big((\pm X^{k_1} \pm X^{k_2}) - (\pm X^{k_3} \pm X^{k_4})\big) \cdot h_\zeta = 0$ in $R_q$. -/
theorem two_term_difference_mul_cycRootCofactor_eq_zero {N q : Nat} [NeZero q]
    (zeta : Int) (hRoot : (zeta ^ N + 1) % (q : Int) = 0)
    (s1 s2 s3 s4 : Bool) (k1 k2 k3 k4 : Fin N)
    (hEval : (signBitToInt s1 * zeta ^ k1.val + signBitToInt s2 * zeta ^ k2.val -
        signBitToInt s3 * zeta ^ k3.val - signBitToInt s4 * zeta ^ k4.val) % (q : Int) = 0) :
    cycIntToZq q (cycIntMul
      (cycIntSub
        (cycIntAdd (negacyclicSignedMonomial s1 k1) (negacyclicSignedMonomial s2 k2))
        (cycIntAdd (negacyclicSignedMonomial s3 k3) (negacyclicSignedMonomial s4 k4)))
      (cycRootCofactor N zeta)) = cycZqZero := by
  rw [cycIntMul_sub_left, cycIntMul_right_distrib, cycIntMul_right_distrib,
      cycIntToZq_sub, cycIntToZq_add, cycIntToZq_add]
  simp only [negacyclicSignedMonomial_mul_cycRootCofactor zeta hRoot]
  rw [← cycIntToZq_add, ← cycIntToZq_add, ← cycIntToZq_sub]
  funext j
  show ModZq.ofInt q _ = ModZq.zero q
  rw [← ModZq.ofInt_zero]
  apply ModZq.ofInt_eq_of_sub_emod
  exact int_four_term_factor_emod _ _ _ _ (cycRootCofactor N zeta j) _ hEval

/-- An element of $R_q$ with a non-zero annihilator has no multiplicative inverse. -/
theorem cycZq_no_inverse_of_annihilator {N q : Nat} [NeZero q] (hN : 0 < N)
    (d h : NegacyclicPolyZq N q)
    (hAnn : cycZqMul d h = cycZqZero) (hNz : h ≠ cycZqZero) :
    ∀ inv : NegacyclicPolyZq N q, cycZqMul d inv ≠ cycZqOne := by
  intro inv hIsOne
  apply hNz
  calc h
    _ = cycZqMul h cycZqOne := (cycZqMul_one_right hN _).symm
    _ = cycZqMul h (cycZqMul d inv) := by rw [hIsOne]
    _ = cycZqMul (cycZqMul h d) inv := (cycZqMul_assoc _ _ _).symm
    _ = cycZqMul (cycZqMul d h) inv := by rw [cycZqMul_comm h d]
    _ = cycZqMul cycZqZero inv := by rw [hAnn]
    _ = cycZqZero := cycZqMul_zero_left inv


/-! ## 4. Inhabitedness Witnesses ($N = 1024$) & Mutation `#tooth` Counterexamples -/

/-- **Inhabitedness Witness 1 (`inhabited_distinct_signedMonomials_1024`)**:
    Explicit distinct signed-monomial pairs at $\nu = 10, N = 1024, q = 12289$ exercising:
    1. Same-degree opposite-sign $(+1, -1)$ (`m = 1`),
    2. Adjacent-degree $(+1, +X)$ (`d = 1 = 2^0 * 1`, full $m = 1024$-term geometric cofactor),
    3. Half-period $(+1, -X^{512})$ (`d = 512 = 2^9 * 1`, $m = 2$-term cofactor $1 - X^{512}$). -/
theorem inhabited_distinct_signedMonomials_1024 :
    let cPos0 : SignedMonomialChal 10 := ⟨false, ⟨0, by decide⟩⟩
    let cNeg0 : SignedMonomialChal 10 := ⟨true, ⟨0, by decide⟩⟩
    let cPos1 : SignedMonomialChal 10 := ⟨false, ⟨1, by decide⟩⟩
    let cNeg512 : SignedMonomialChal 10 := ⟨true, ⟨512, by decide⟩⟩
    cPos0 ≠ cNeg0 ∧
    signedMonomialCofactorSupportSize 10 cPos0 cNeg0 = 1 ∧
    cPos0 ≠ cPos1 ∧
    signedMonomialCofactorSupportSize 10 cPos0 cPos1 = 1024 ∧
    cPos0 ≠ cNeg512 ∧
    signedMonomialCofactorSupportSize 10 cPos0 cNeg512 = 2 ∧
    cycZqMul (cycZqSub (cPos0.toZqPoly 12289) (cPos1.toZqPoly 12289))
      (signedMonomialDiffInvZq 10 12289 cPos0 cPos1) = cycZqOne ∧
    cycZqMul (cycZqSub (cPos0.toZqPoly 12289) (cNeg512.toZqPoly 12289))
      (signedMonomialDiffInvZq 10 12289 cPos0 cNeg512) = cycZqOne := by
  intro cPos0 cNeg0 cPos1 cNeg512
  have hNe0 : cPos0 ≠ cNeg0 := by decide
  have hNe1 : cPos0 ≠ cPos1 := by decide
  have hNe512 : cPos0 ≠ cNeg512 := by decide
  have hInv1 := (signedMonomial_challenge_set_pairwise_invertible 10 12289 (by decide) (by decide) cPos0 cPos1 hNe1).2.1
  have hInv512 := (signedMonomial_challenge_set_pairwise_invertible 10 12289 (by decide) (by decide) cPos0 cNeg512 hNe512).2.1
  exact ⟨hNe0, by decide, hNe1, by decide, hNe512, by decide, hInv1, hInv512⟩

/-- Non-trivial $N = 1024, q = 12289, B_z = 3069$ RLWE OR-Sigma statement (`A = 1 + X`, `s = 1`, `e = X`). -/
def sampleCyc1024PolyA : CycPolyZq 10 12289 :=
  cycIntToZq 12289 (cycIntAdd (signedMonomial 10 false ⟨0, by decide⟩)
    (signedMonomial 10 false ⟨1, by decide⟩))

def sampleCyc1024SecretS : CycPolyInt 10 :=
  signedMonomial 10 false ⟨0, by decide⟩

def sampleCyc1024SecretE : CycPolyInt 10 :=
  signedMonomial 10 false ⟨1, by decide⟩

def sampleCyc1024MaskY : CycPolyInt 10 :=
  signedMonomial 10 false ⟨2, by decide⟩

def sampleRlweOrSigmaStmt1024 : RlweOrSigmaStatement 10 12289 where
  A := sampleCyc1024PolyA
  u0 := cycZqAdd (cycZqMul sampleCyc1024PolyA (cycIntToZq 12289 sampleCyc1024SecretS))
          (cycIntToZq 12289 sampleCyc1024SecretE)
  u1 := cycZqOne
  Bz := rlweProductionBz

/-- **Inhabitedness Witness 2 (`inhabited_rlwe_or_sigma_13_valid_transcripts_1024`)**:
    Proves inhabitedness of valid $N = 1024, q = 12289, R = 13, B_z = 3069$ forked OR-Sigma transcripts
    `(tr, tr')` with non-zero CRS `A = 1 + X`, non-zero secret `(s, e) = (1, X)`, non-zero masks,
    identical commitments, and distinct 13-challenge vectors `c ≠ c'`, where `tryExtractRlweOrSigma13Witness`
    succeeds with `.inl w` and `‖w.s2‖_∞ ≤ 2 * 1024 * 3069`! -/
theorem inhabited_rlwe_or_sigma_13_valid_transcripts_1024 :
    let chA : Fin 13 → SignedMonomialChal 10 := fun _ => ⟨false, ⟨0, by decide⟩⟩
    let chB : Fin 13 → SignedMonomialChal 10 := fun i =>
      if i.val = 0 then ⟨false, ⟨1, by decide⟩⟩ else ⟨false, ⟨0, by decide⟩⟩
    let ys : Fin 13 → CycPolyInt 10 := fun _ => sampleCyc1024MaskY
    let ye : Fin 13 → CycPolyInt 10 := fun _ => sampleCyc1024MaskY
    let cFake : Fin 13 → SignedMonomialChal 10 := fun _ => ⟨true, ⟨3, by decide⟩⟩
    let trA := buildHonestRlweOrSigmaTranscript 13 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA
    let trB := buildHonestRlweOrSigmaTranscript 13 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chB
    chA ≠ chB ∧
    trA.t0 = trB.t0 ∧ trA.t1 = trB.t1 ∧
    verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chA trA = true ∧
    verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chB trB = true ∧
    (∃ w, tryExtractRlweOrSigma13Witness sampleRlweOrSigmaStmt1024 chA chB trA trB = PSum.inl w ∧
          cycIntInfNorm w.s2 ≤ 2 * 1024 * rlweProductionBz ∧
          cycIntInfNorm w.e2 ≤ 2 * 1024 * rlweProductionBz) := by
  intro chA chB ys ye cFake trA trB
  have hChNe : chA ≠ chB := by
    intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    dsimp only [chA, chB] at h0
    revert h0; decide
  have hSame := buildHonestRlweOrSigmaTranscript_same_commitments 13 10 12289
    sampleRlweOrSigmaStmt1024 false sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA chB
  have hNormS : cycIntInfNorm sampleCyc1024SecretS ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretS signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormE : cycIntInfNorm sampleCyc1024SecretE ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretE signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormY : cycIntInfNorm sampleCyc1024MaskY ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024MaskY signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hSafeS : ∀ i : Fin 13, cycIntInfNorm (ys i) + cycIntInfNorm sampleCyc1024SecretS ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hSafeE : ∀ i : Fin 13, cycIntInfNorm (ye i) + cycIntInfNorm sampleCyc1024SecretE ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ye, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hFakeY : ∀ i : Fin 13, cycIntInfNorm (ys i) ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hAccA := buildHonestRlweOrSigmaTranscript_accepts sampleRlweOrSigmaStmt1024 false
    sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA rfl hSafeS hSafeE hFakeY hFakeY
  have hAccB := buildHonestRlweOrSigmaTranscript_accepts sampleRlweOrSigmaStmt1024 false
    sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chB rfl hSafeS hSafeE hFakeY hFakeY
  obtain ⟨w, hw⟩ := tryExtractRlweOrSigma13Witness_complete sampleRlweOrSigmaStmt1024
    chA chB trA trB hSame.1 hSame.2 hChNe hAccA hAccB
  exact ⟨hChNe, hSame.1, hSame.2, hAccA, hAccB, ⟨w, hw, w.s2_infNorm_le, w.e2_infNorm_le⟩⟩

/-- **`#tooth` Witness (a): Non-Power-of-Two Cyclotomic Zero Divisor (`tooth_non_pow2_cyclotomic_X3_plus_1_not_invertible`)**:
    Over the non-power-of-two negacyclic ring $\mathbb{Z}_q[X]/(X^3 + 1)$ ($N = 3$):
    1. For EVERY modulus $q \ge 2$ (including $q = 12289$), the distinct signed monomials
       $c_1 = +1$ and $c_2 = -X$ satisfy $c_1 - c_2 = 1 + X$ and
       $(1 + X) \circledast (1 - X + X^2) = 1 + X^3 = 0$ with $1 - X + X^2 \ne 0$ in $\mathbb{Z}_q[X]/(X^3 + 1)$,
       so $1 + X$ is a **zero divisor** and has **NO multiplicative inverse** (`∀ inv, (1 + X) * inv ≠ 1`)!
    2. Furthermore, at $q = 2$ in $\mathbb{Z}_2[X]/(X^3 + 1)$, $1 - X$ ALSO satisfies
       $(1 - X) \circledast (1 + X + X^2) = 0$ and has no multiplicative inverse! -/
theorem tooth_non_pow2_cyclotomic_X3_plus_1_not_invertible (q : Nat) [NeZero q] (hq2 : 2 ≤ q) :
    let c1 : NegacyclicPolyInt 3 := negacyclicSignedMonomial false ⟨0, by decide⟩
    let c2 : NegacyclicPolyInt 3 := negacyclicSignedMonomial true ⟨1, by decide⟩
    let onePlusX : NegacyclicPolyInt 3 := cycIntSub c1 c2
    let cofactorZeroDiv : NegacyclicPolyInt 3 := fun k =>
      if k.val = 0 then 1 else if k.val = 1 then -1 else 1
    c1 ≠ c2 ∧
    cycIntMul onePlusX cofactorZeroDiv = cycIntZero ∧
    cycIntToZq q cofactorZeroDiv ≠ cycZqZero ∧
    cycZqMul (cycIntToZq q onePlusX) (cycIntToZq q cofactorZeroDiv) = cycZqZero ∧
    (∀ inv : NegacyclicPolyZq 3 q, cycZqMul (cycIntToZq q onePlusX) inv ≠ cycZqOne) ∧
    (let _ : NeZero 2 := ⟨by decide⟩
     let oneMinusX2 : NegacyclicPolyZq 3 2 := cycIntToZq 2
       (cycIntSub (negacyclicSignedMonomial false ⟨0, by decide⟩)
                  (negacyclicSignedMonomial false ⟨1, by decide⟩))
     let geom2 : NegacyclicPolyZq 3 2 := cycIntToZq 2 (fun _ => 1)
     geom2 ≠ cycZqZero ∧ cycZqMul oneMinusX2 geom2 = cycZqZero) := by
  intro c1 c2 onePlusX cofactorZeroDiv
  have hcNe : c1 ≠ c2 := by
    intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    dsimp [c1, c2, negacyclicSignedMonomial, signBitToInt] at h0
    omega
  have hIntZero : cycIntMul onePlusX cofactorZeroDiv = cycIntZero := by
    have h0 : cycIntMul onePlusX cofactorZeroDiv ⟨0, by decide⟩ = 0 := by
      dsimp only [onePlusX, c1, c2, cofactorZeroDiv]; decide
    have h1 : cycIntMul onePlusX cofactorZeroDiv ⟨1, by decide⟩ = 0 := by
      dsimp only [onePlusX, c1, c2, cofactorZeroDiv]; decide
    have h2 : cycIntMul onePlusX cofactorZeroDiv ⟨2, by decide⟩ = 0 := by
      dsimp only [onePlusX, c1, c2, cofactorZeroDiv]; decide
    funext ⟨k, hk⟩
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkCases with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hCofNz : cycIntToZq q cofactorZeroDiv ≠ cycZqZero := by
    intro hZ
    have h0 := congrFun hZ ⟨0, by decide⟩
    change ModZq.ofInt q 1 = ModZq.zero q at h0
    have hv := ModZq.ofInt_val_int q 1
    rw [h0] at hv
    dsimp only [ModZq.zero] at hv
    have hMod1 : (1 : Int) % (q : Int) = 1 := Int.emod_eq_of_lt (by omega) (by omega)
    rw [hMod1] at hv
    omega
  have hZqZero : cycZqMul (cycIntToZq q onePlusX) (cycIntToZq q cofactorZeroDiv) = cycZqZero := by
    rw [← cycIntToZq_mul, hIntZero, cycIntToZq_zero]
  have hNoInv : ∀ inv : NegacyclicPolyZq 3 q, cycZqMul (cycIntToZq q onePlusX) inv ≠ cycZqOne := by
    intro inv hIsOne
    have hAnn : cycIntToZq q cofactorZeroDiv = cycZqZero := by
      calc cycIntToZq q cofactorZeroDiv
        _ = cycZqMul (cycIntToZq q cofactorZeroDiv) cycZqOne :=
            (cycZqMul_one_right (by decide : 0 < 3) _).symm
        _ = cycZqMul (cycIntToZq q cofactorZeroDiv) (cycZqMul (cycIntToZq q onePlusX) inv) := by
            rw [hIsOne]
        _ = cycZqMul (cycZqMul (cycIntToZq q cofactorZeroDiv) (cycIntToZq q onePlusX)) inv :=
            (cycZqMul_assoc _ _ _).symm
        _ = cycZqMul (cycZqMul (cycIntToZq q onePlusX) (cycIntToZq q cofactorZeroDiv)) inv := by
            rw [cycZqMul_comm (cycIntToZq q cofactorZeroDiv) (cycIntToZq q onePlusX)]
        _ = cycZqMul cycZqZero inv := by rw [hZqZero]
        _ = cycZqZero := cycZqMul_zero_left inv
    exact hCofNz hAnn
  refine ⟨hcNe, hIntZero, hCofNz, hZqZero, hNoInv, ?_⟩
  dsimp only
  let _ : NeZero 2 := ⟨by decide⟩
  let oneMinusX2 : NegacyclicPolyZq 3 2 := cycIntToZq 2
    (cycIntSub (@negacyclicSignedMonomial 3 false ⟨0, by decide⟩)
               (@negacyclicSignedMonomial 3 false ⟨1, by decide⟩))
  let geom2 : NegacyclicPolyZq 3 2 := cycIntToZq 2 (fun _ => 1)
  have hGeom2Nz : geom2 ≠ cycZqZero := by
    intro hEq
    have h0 := congrFun hEq ⟨0, by decide⟩
    dsimp only [geom2] at h0
    revert h0; decide
  have hMul2Zero : cycZqMul oneMinusX2 geom2 = cycZqZero := by
    have hm0 : cycZqMul oneMinusX2 geom2 ⟨0, by decide⟩ = (@cycZqZero 3 2 _) ⟨0, by decide⟩ := by
      dsimp only [oneMinusX2, geom2]; decide
    have hm1 : cycZqMul oneMinusX2 geom2 ⟨1, by decide⟩ = (@cycZqZero 3 2 _) ⟨1, by decide⟩ := by
      dsimp only [oneMinusX2, geom2]; decide
    have hm2 : cycZqMul oneMinusX2 geom2 ⟨2, by decide⟩ = (@cycZqZero 3 2 _) ⟨2, by decide⟩ := by
      dsimp only [oneMinusX2, geom2]; decide
    funext ⟨k, hk⟩
    have hkC : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkC with rfl | rfl | rfl
    · exact hm0
    · exact hm1
    · exact hm2
  exact ⟨hGeom2Nz, hMul2Zero⟩

/-- **`#tooth` Witness (b): Even Modulus Non-Invertibility (`tooth_even_modulus_diff_two_not_invertible`)**:
    Over $R_q = \mathbb{Z}_q[X]/(X^{2^\nu} + 1)$ for EVERY $\nu \ge 0$ (including $\nu = 10, N = 1024$)
    and EVERY even modulus $q \ge 2$ (`q % 2 = 0`), the signed-monomial pair $c_1 = +1$, $c_2 = -1$
    satisfies $(c_1 - c_2) \cdot ((q / 2) \cdot 1) = 0$ in $R_q$ and $c_1 - c_2 = 2$ has **NO multiplicative inverse**
    in $R_q$ (`∀ inv, (c1 - c2) * inv ≠ 1`)! -/
theorem tooth_even_modulus_diff_two_not_invertible (nu q : Nat) [NeZero q]
    (hq2 : 2 ≤ q) (hEven : q % 2 = 0) :
    let hN := Nat.two_pow_pos nu
    let c1 : SignedMonomialChal nu := ⟨false, ⟨0, hN⟩⟩
    let c2 : SignedMonomialChal nu := ⟨true, ⟨0, hN⟩⟩
    let diffZq : CycPolyZq nu q := cycZqSub (c1.toZqPoly q) (c2.toZqPoly q)
    let halfQPoly : CycPolyZq nu q := cycZqScale ((q / 2 : Nat) : Int) cycZqOne
    c1 ≠ c2 ∧
    cycZqMul diffZq halfQPoly = cycZqZero ∧
    (4 ≤ q → halfQPoly ≠ cycZqZero) ∧
    (∀ inv : CycPolyZq nu q, cycZqMul diffZq inv ≠ cycZqOne) := by
  intro hN c1 c2 diffZq halfQPoly
  have hcNe : c1 ≠ c2 := by
    intro hEq
    have hs := congrArg SignedMonomialChal.sign hEq
    cases hs
  have hDiffEqTwo : diffZq = cycIntToZq q (cycIntScale 2 cycIntOne) := by
    dsimp only [diffZq]
    unfold SignedMonomialChal.toZqPoly
    rw [← cycIntToZq_sub]
    congr 1
    funext k
    dsimp only [c1, c2, cycIntSub, SignedMonomialChal.toIntPoly, signedMonomial,
      negacyclicSignedMonomial, cycIntScale, cycIntOne]
    rw [signBitToInt_false, signBitToInt_true]
    by_cases hk0 : k.val = 0
    · have hkEq : k = ⟨0, hN⟩ := Fin.ext hk0
      simp [hkEq]
    · have hkNe : k ≠ ⟨0, hN⟩ := fun h => hk0 (congrArg Fin.val h)
      simp [hkNe, hk0]
  have hAnnZero : cycZqMul diffZq halfQPoly = cycZqZero := by
    dsimp only [halfQPoly]
    rw [hDiffEqTwo, ← cycIntToZq_one q, ← cycIntToZq_scale, ← cycIntToZq_mul,
        cycIntMul_scale_left, cycIntMul_scale_right, cycIntMul_one_left hN]
    funext k
    dsimp only [cycIntToZq, cycIntScale, cycIntOne, cycZqZero]
    split
    · rw [Int.mul_one]
      apply ModZq.ext_int
      dsimp only [ModZq.zero]
      rw [ModZq.ofInt_val_int]
      have hNatQ : 2 * (q / 2) = q := by omega
      have hCast := Int.natCast_mul 2 (q / 2)
      have hMulQ : (2 : Int) * ((q / 2 : Nat) : Int) = 0 + 1 * (q : Int) := by omega
      rw [hMulQ, Int.add_mul_emod_self_right, Int.zero_emod]
      rfl
    · rw [Int.mul_zero, Int.mul_zero]; exact ModZq.ofInt_zero q
  have hHalfNz : 4 ≤ q → halfQPoly ≠ cycZqZero := by
    intro hq4 hZ
    have h0 := congrFun hZ ⟨0, hN⟩
    dsimp only [halfQPoly, cycZqScale, cycZqOne, cycZqZero] at h0
    simp only [↓reduceIte] at h0
    rw [← ModZq.ofInt_one, ← ModZq.ofInt_mul, Int.mul_one] at h0
    have hv := ModZq.ofInt_val_int q ((q / 2 : Nat) : Int)
    rw [h0] at hv
    dsimp only [ModZq.zero] at hv
    have hHalfLt : q / 2 < q := by omega
    have hHalfPos : 0 < q / 2 := by omega
    have hHalfMod : ((q / 2 : Nat) : Int) % (q : Int) = ((q / 2 : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (Int.ofNat_lt.mpr hHalfLt)
    rw [hHalfMod] at hv
    omega
  have hNoInv : ∀ inv : CycPolyZq nu q, cycZqMul diffZq inv ≠ cycZqOne := by
    intro inv hOne
    have hMulEq : cycZqMul diffZq inv = cycZqScale 2 inv := by
      rw [hDiffEqTwo, ← cycIntToZq_toNatInt inv, ← cycIntToZq_mul,
          cycIntMul_scale_left, cycIntMul_one_left hN, cycIntToZq_scale, cycIntToZq_toNatInt]
    rw [hMulEq] at hOne
    have hAt0 := congrFun hOne ⟨0, hN⟩
    dsimp only [cycZqScale, cycZqOne] at hAt0
    simp only [↓reduceIte] at hAt0
    rw [← ModZq.ofInt_natVal (inv ⟨0, hN⟩), ← ModZq.ofInt_mul] at hAt0
    have hvL := ModZq.ofInt_val_int q (2 * ((inv ⟨0, hN⟩).val : Int))
    rw [hAt0] at hvL
    dsimp only [ModZq.one] at hvL
    have h1Mod : 1 % q = 1 := Nat.mod_eq_of_lt hq2
    rw [h1Mod] at hvL
    have hDef := Int.emod_def (2 * ((inv ⟨0, hN⟩).val : Int)) (q : Int)
    rw [← hvL] at hDef
    have hDiv : (2 : Int) * ((inv ⟨0, hN⟩).val : Int) =
        (q : Int) * ((2 * ((inv ⟨0, hN⟩).val : Int)) / (q : Int)) + 1 := by omega
    have hQEvenZ : (q : Int) % 2 = 0 := by omega
    have hMod2 : ((2 : Int) * ((inv ⟨0, hN⟩).val : Int)) % 2 = 0 := by omega
    have hRhsMod2 : ((q : Int) * ((2 * ((inv ⟨0, hN⟩).val : Int)) / (q : Int)) + 1) % 2 = 1 := by
      have hMulEven : ((q : Int) * ((2 * ((inv ⟨0, hN⟩).val : Int)) / (q : Int))) % 2 = 0 := by
        rw [Int.mul_emod, hQEvenZ, Int.zero_mul, Int.zero_emod]
      omega
    rw [hDiv] at hMod2
    omega
  exact ⟨hcNe, hAnnZero, hHalfNz, hNoInv⟩

/-- **`#tooth` Witness (c): Computational `PSum` Extractor Refuses Unforked & Overbound Transcripts
    (`tooth_extractor_refuses_unforked_and_overbound`)**:
    1. Calling `tryExtractRlweOrSigma13Witness` on two identical challenge vectors `c = c'` refuses
       with `.inr .identicalJointChallenges`.
    2. Corrupting `zs0` to `‖zs0‖_∞ = B_z + 1` causes `verifyRlweOrSigma` to return `false` and
       `tryExtractRlweOrSigma13Witness` to refuse with `.inr .firstTranscriptInvalid`. -/
theorem tooth_extractor_refuses_unforked_and_overbound :
    let chA : Fin 13 → SignedMonomialChal 10 := fun _ => ⟨false, ⟨0, by decide⟩⟩
    let chB : Fin 13 → SignedMonomialChal 10 := fun i =>
      if i.val = 0 then ⟨false, ⟨1, by decide⟩⟩ else ⟨false, ⟨0, by decide⟩⟩
    let ys : Fin 13 → CycPolyInt 10 := fun _ => sampleCyc1024MaskY
    let cFake : Fin 13 → SignedMonomialChal 10 := fun _ => ⟨true, ⟨3, by decide⟩⟩
    let trA := buildHonestRlweOrSigmaTranscript 13 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ys cFake ys ys chA
    let trB := buildHonestRlweOrSigmaTranscript 13 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ys cFake ys ys chB
    let overPoly : CycPolyInt 10 := fun k =>
      if k.val = 0 then (rlweProductionBz + 1 : Int) else 0
    let trOver : RlweOrSigmaTranscript 13 10 12289 :=
      { trA with zs0 := fun i => if i.val = 0 then overPoly else trA.zs0 i }
    tryExtractRlweOrSigma13Witness sampleRlweOrSigmaStmt1024 chA chA trA trA =
      PSum.inr .identicalJointChallenges ∧
    verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chA trOver = false ∧
    tryExtractRlweOrSigma13Witness sampleRlweOrSigmaStmt1024 chA chB trOver trB =
      PSum.inr .firstTranscriptInvalid := by
  intro chA chB ys cFake trA trB overPoly trOver
  have hSame := buildHonestRlweOrSigmaTranscript_same_commitments 13 10 12289
    sampleRlweOrSigmaStmt1024 false sampleCyc1024SecretS sampleCyc1024SecretE ys ys cFake ys ys chA chB
  have hNormS : cycIntInfNorm sampleCyc1024SecretS ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretS signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormE : cycIntInfNorm sampleCyc1024SecretE ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretE signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormY : cycIntInfNorm sampleCyc1024MaskY ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024MaskY signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hSafeS : ∀ i : Fin 13, cycIntInfNorm (ys i) + cycIntInfNorm sampleCyc1024SecretS ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hSafeE : ∀ i : Fin 13, cycIntInfNorm (ys i) + cycIntInfNorm sampleCyc1024SecretE ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hFakeY : ∀ i : Fin 13, cycIntInfNorm (ys i) ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hAccA : verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chA trA = true :=
    buildHonestRlweOrSigmaTranscript_accepts sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ys cFake ys ys chA rfl hSafeS hSafeE hFakeY hFakeY
  -- 1. Unforked identical challenges refused
  have ht0Self : cycAllFin 13 (fun i => cycZqEq (trA.t0 i) (trA.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; exact (cycZqEq_iff _ _).mpr rfl
  have ht1Self : cycAllFin 13 (fun i => cycZqEq (trA.t1 i) (trA.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; exact (cycZqEq_iff _ _).mpr rfl
  have hcTrue : cycAllFin 13 (fun _ => true) = true := by decide
  have hUnforked : tryExtractRlweOrSigma13Witness sampleRlweOrSigmaStmt1024 chA chA trA trA =
      PSum.inr .identicalJointChallenges := by
    unfold tryExtractRlweOrSigma13Witness
    simp only [ht0Self, ht1Self, hAccA, decide_true, hcTrue, ↓reduceDIte]
  -- 2. Overbound zs0 rejected
  have hOverNotLe : ¬(cycIntInfNorm overPoly ≤ sampleRlweOrSigmaStmt1024.Bz) := by
    intro hLe
    have hc0 := (cycIntInfNorm_le_iff overPoly _).mp hLe ⟨0, by decide⟩
    dsimp [overPoly, sampleRlweOrSigmaStmt1024, rlweProductionBz] at hc0
    omega
  have hRep0False : verifyRlweOrSigmaRep sampleRlweOrSigmaStmt1024 ⟨0, by decide⟩ (chA ⟨0, by decide⟩) trOver = false := by
    unfold verifyRlweOrSigmaRep
    dsimp only [trOver, ↓reduceIte]
    have hDecFalse : decide (cycIntInfNorm overPoly ≤ sampleRlweOrSigmaStmt1024.Bz) = false :=
      decide_eq_false hOverNotLe
    simp [hDecFalse]
  have hVerOverFalse : verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chA trOver = false := by
    cases hb : verifyRlweOrSigma 13 10 12289 sampleRlweOrSigmaStmt1024 chA trOver
    · rfl
    · have h0 := (verifyRlweOrSigma_iff 13 10 12289 sampleRlweOrSigmaStmt1024 chA trOver).mp hb ⟨0, by decide⟩
      rw [hRep0False] at h0; cases h0
  have ht0AB : cycAllFin 13 (fun i => cycZqEq (trOver.t0 i) (trB.t0 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; dsimp [trOver]; rw [hSame.1]; exact (cycZqEq_iff _ _).mpr rfl
  have ht1AB : cycAllFin 13 (fun i => cycZqEq (trOver.t1 i) (trB.t1 i)) = true := by
    rw [cycAllFin_eq_true_iff]; intro i; dsimp [trOver]; rw [hSame.2]; exact (cycZqEq_iff _ _).mpr rfl
  have hRefuseOver : tryExtractRlweOrSigma13Witness sampleRlweOrSigmaStmt1024 chA chB trOver trB =
      PSum.inr .firstTranscriptInvalid := by
    unfold tryExtractRlweOrSigma13Witness
    simp [ht0AB, ht1AB, hVerOverFalse]
  exact ⟨hUnforked, hVerOverFalse, hRefuseOver⟩

set_option exponentiation.threshold 2048 in
/-- **`#tooth` Witness (d): a production two-term challenge difference is a zero divisor of $R_{12289}$
    (`tooth_two_term_challenge_difference_zero_divisor_12289`)**:
    `poly_from_chal20` maps `u = 108` to $X^{108} + X^{512}$ and `u' = 1026` to $X^{2} + X^{513}$.
    Since $12289 \equiv 1 \pmod{2048}$, $X^{1024} + 1$ splits into linear factors over
    $\mathbb{Z}_{12289}$; at the root $\psi = 1945$ ($\psi^{1024} \equiv -1$) both challenges evaluate to
    $11331$. Hence $d(u) - d(u')$ annihilates the non-zero root cofactor $h_\psi$ and has **no inverse**
    in $\mathbb{Z}_{12289}[X]/(X^{1024} + 1)$. Signed-monomial pairwise invertibility therefore does not
    extend to the two-term challenge set, and a fork on such a pair yields only the fork-difference
    relation, never a witness for the branch target itself. -/
theorem tooth_two_term_challenge_difference_zero_divisor_12289 :
    let dU : CycPolyInt 10 :=
      cycIntAdd (signedMonomial 10 false ⟨108, by decide⟩) (signedMonomial 10 false ⟨512, by decide⟩)
    let dU' : CycPolyInt 10 :=
      cycIntAdd (signedMonomial 10 false ⟨2, by decide⟩) (signedMonomial 10 false ⟨513, by decide⟩)
    let delta : CycPolyZq 10 12289 := cycIntToZq 12289 (cycIntSub dU dU')
    let hPsi : CycPolyZq 10 12289 := cycIntToZq 12289 (cycRootCofactor (2 ^ 10) 1945)
    hPsi ≠ cycZqZero ∧
    cycZqMul delta hPsi = cycZqZero ∧
    (∀ inv : CycPolyZq 10 12289, cycZqMul delta inv ≠ cycZqOne) := by
  intro dU dU' delta hPsi
  have hRootNat : (1945 ^ (2 ^ 10) + 1) % 12289 = 0 :=
    nat_pow_add_one_mod 12289 1945 (2 ^ 10) (by decide +kernel)
  have hP : ∀ e : Nat, ((1945 : Int) ^ e) = ((1945 ^ e : Nat) : Int) := fun e => by
    rw [Int.natCast_pow]; rfl
  have hRoot : ((1945 : Int) ^ (2 ^ 10) + 1) % ((12289 : Nat) : Int) = 0 := by
    have hCast : ((1945 : Int) ^ (2 ^ 10) + 1) = (((1945 ^ (2 ^ 10) + 1 : Nat)) : Int) := by
      rw [Int.natCast_add, Int.natCast_pow]; rfl
    rw [hCast, ← Int.natCast_emod, hRootNat]; rfl
  have hNatEval : (1945 ^ 108 + 1945 ^ 512) % 12289 = (1945 ^ 2 + 1945 ^ 513) % 12289 :=
    (nat_pow_add_pow_mod 12289 1945 108 512).trans
      ((by decide +kernel :
          (powModLin 12289 1945 108 + powModLin 12289 1945 512) % 12289 =
          (powModLin 12289 1945 2 + powModLin 12289 1945 513) % 12289).trans
        (nat_pow_add_pow_mod 12289 1945 2 513).symm)
  have hEval : (signBitToInt false * (1945 : Int) ^ (108 : Nat) +
      signBitToInt false * (1945 : Int) ^ (512 : Nat) -
      signBitToInt false * (1945 : Int) ^ (2 : Nat) -
      signBitToInt false * (1945 : Int) ^ (513 : Nat)) % ((12289 : Nat) : Int) = 0 := by
    rw [hP 108, hP 512, hP 2, hP 513]
    exact int_two_sum_sub_emod_of_nat _ _ _ _ 12289 hNatEval
  have hNz : hPsi ≠ cycZqZero := by
    intro hZ
    have h0 := congrFun hZ ⟨1023, by decide⟩
    change ModZq.ofInt 12289 1 = ModZq.zero 12289 at h0
    have hv := congrArg ModZq.val h0
    revert hv; decide
  have hAnn : cycZqMul delta hPsi = cycZqZero := by
    dsimp only [delta, hPsi]
    rw [← cycIntToZq_mul]
    exact two_term_difference_mul_cycRootCofactor_eq_zero (N := 2 ^ 10) (q := 12289) 1945 hRoot
      false false false false ⟨108, by decide⟩ ⟨512, by decide⟩ ⟨2, by decide⟩ ⟨513, by decide⟩ hEval
  exact ⟨hNz, hAnn, cycZq_no_inverse_of_annihilator (Nat.two_pow_pos 10) delta hPsi hAnn hNz⟩

/-- **`#tooth` Witness (e1): Cofactor Norm Bound `2 N B_z = 6287360` Admits Zero-Secret Solution at `q = 12289`
    (`tooth_cofactor_relation_admits_zero_secret_at_12289`, `H2`)**:
    For **every** $A, Y \in R_{12289}$, setting $s_2 = 0$ and $e_2 = \mathrm{centered}(2 \cdot Y \bmod 12289)$
    satisfies $A \cdot s_2 + e_2 = 2 \cdot Y$ in $R_{12289}$ with $\|s_2\|_\infty = 0 \le 6287360$ and
    $\|e_2\|_\infty \le 6144 \le 6287360 = 2 \cdot 1024 \cdot 3070$ without knowing any short secret! -/
theorem tooth_cofactor_relation_admits_zero_secret_at_12289 (A Y : CycPolyZq 10 12289) :
    ∃ eTriv : CycPolyInt 10,
      cycIntInfNorm (@cycIntZero (2 ^ 10)) ≤ 2 * 1024 * rlweProductionBz ∧
      cycIntInfNorm eTriv ≤ 2 * 1024 * rlweProductionBz ∧
      cycZqAdd (cycZqMul A (cycIntToZq 12289 (@cycIntZero (2 ^ 10)))) (cycIntToZq 12289 eTriv) =
        cycZqScale 2 Y := by
  refine ⟨cycZqCentered (cycZqScale 2 Y), ?_, ?_, ?_⟩
  · rw [cycIntInfNorm_le_iff]; intro _; unfold cycIntZero; decide
  · rw [cycIntInfNorm_le_iff]; intro k
    unfold cycZqCentered ModZq.centered rlweProductionBz
    have hLt := (cycZqScale 2 Y k).isLt
    split <;> omega
  · rw [cycIntToZq_zero, cycZqMul_zero_right, cycIntToZq_centered]
    funext k; unfold cycZqAdd cycZqZero ModZq.add ModZq.zero
    apply ModZq.ext
    dsimp only
    rw [Nat.zero_add, Nat.mod_eq_of_lt (cycZqScale 2 Y k).isLt]

/-- **`#tooth` Witness (e2): Short Isometric Bound `2 B_z = 6140 < 6144` Refutes Zero-Secret Forgery at `q = 12289`
    (`tooth_short_monomial_witness_refutes_zero_secret_at_12289`, `H2`)**:
    In contrast to `tooth_cofactor_relation_admits_zero_secret_at_12289`, under `ShortMonomialRelaxedRlweWitness`
    (`‖eIso‖_∞ ≤ 2 * B_z = 6140 < 6144 = ⌊12289/2⌋`), setting $s_{\mathrm{iso}} = 0$ on target $Y = 3072 \cdot 1$
    at relaxation $r_{\mathrm{rel}} = 2$ (`(rRel * Y)_0 = 6144`) has **no** valid integer error $e_{\mathrm{iso}}$! -/
theorem tooth_short_monomial_witness_refutes_zero_secret_at_12289
    (A : CycPolyZq 10 12289) (eIso : CycPolyInt 10)
    (heShort : cycIntInfNorm eIso ≤ 2 * rlweProductionBz) :
    cycZqAdd (cycZqMul A (cycIntToZq 12289 (@cycIntZero (2 ^ 10)))) (cycIntToZq 12289 eIso) ≠
      cycZqScale 2 (cycZqScale 3072 cycZqOne) := by
  intro hEq
  rw [cycIntToZq_zero, cycZqMul_zero_right] at hEq
  have h0 := congrFun hEq ⟨0, by decide⟩
  unfold cycZqAdd cycZqZero cycIntToZq cycZqScale cycZqOne at h0
  simp only [↓reduceIte] at h0
  have hv := congrArg ModZq.val h0
  dsimp only [ModZq.add, ModZq.zero] at hv
  rw [Nat.zero_add, Nat.mod_eq_of_lt (ModZq.ofInt 12289 (eIso ⟨0, by decide⟩)).isLt] at hv
  have hRhs : (ModZq.mul (ModZq.ofInt 12289 2)
      (ModZq.mul (ModZq.ofInt 12289 3072) (ModZq.one 12289))).val = 6144 := by decide
  rw [hRhs] at hv
  have hAbsLe : (eIso ⟨0, by decide⟩).natAbs ≤ 6140 :=
    Nat.le_trans (cycCoeff_natAbs_le_infNorm eIso ⟨0, by decide⟩) heShort
  have hValInt := ModZq.ofInt_val_int 12289 (eIso ⟨0, by decide⟩)
  rw [hv] at hValInt
  have hMod : (eIso ⟨0, by decide⟩) % 12289 = 6144 := hValInt.symm
  omega

/-! ## 5. Mechanical Assurance Gates (`#tooth_pair`, `#verify_inhabited`, `#verify_constructive`) -/

section AssuranceGates

theorem tooth_even_modulus_no_inverse_1024 (inv : CycPolyZq 10 2) :
    cycZqMul
      (cycZqSub ((⟨false, ⟨0, by decide⟩⟩ : SignedMonomialChal 10).toZqPoly 2)
                ((⟨true, ⟨0, by decide⟩⟩ : SignedMonomialChal 10).toZqPoly 2)) inv ≠ cycZqOne :=
  (tooth_even_modulus_diff_two_not_invertible 10 2 (by decide) (by decide)).2.2.2 inv

theorem tooth_two_term_no_inverse_12289 (inv : CycPolyZq 10 12289) :
    cycZqMul (cycIntToZq 12289 (cycIntSub
      (cycIntAdd (signedMonomial 10 false ⟨108, by decide⟩) (signedMonomial 10 false ⟨512, by decide⟩))
      (cycIntAdd (signedMonomial 10 false ⟨2, by decide⟩) (signedMonomial 10 false ⟨513, by decide⟩)))) inv ≠ cycZqOne :=
  tooth_two_term_challenge_difference_zero_divisor_12289.2.2 inv

/-- **`#tooth` Unforked Challenge Vector Refused (`tooth_short_extractor_refuses_identical_challenges`)**:
    Without a challenge fork (`c = c'`), `tryExtractShortMonomialOr13Witness` refuses to emit any
    `ShortMonomialRelaxedRlweWitness` for every statement and transcript pair. -/
theorem tooth_short_extractor_refuses_identical_challenges {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c : Fin 13 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 13 nu q)
    (w : ShortMonomialRelaxedRlweWitness 13 nu q stmt) :
    tryExtractShortMonomialOr13Witness stmt c c tr tr' ≠ PSum.inl w := by
  have hcEq : cycAllFin 13 (fun _ => true) = true := by decide
  unfold tryExtractShortMonomialOr13Witness
  simp only [decide_true, hcEq, ↓reduceDIte]
  split
  · split
    · split
      · split
        · intro h; cases h
        · intro h; cases h
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

theorem witness_short_rlwe_key_relation_inhabited :
    ∃ (stmt : RlweOrSigmaStatement 0 12289)
      (w : ShortMonomialRelaxedRlweWitness 1 0 12289 stmt)
      (sTrue eTrue : CycPolyInt 0),
      ShortRlweKeyRelation stmt.A (stmt.branchU w.branch) 1 sTrue eTrue := by
  let stmt : RlweOrSigmaStatement 0 12289 :=
    { A := cycZqOne
      u0 := fun _ => ModZq.ofInt 12289 2
      u1 := fun _ => ModZq.ofInt 12289 2
      Bz := 3070 }
  let c0 : SignedMonomialChal 0 := ⟨false, ⟨0, by decide⟩⟩
  let c1 : SignedMonomialChal 0 := ⟨true, ⟨0, by decide⟩⟩
  let dzs : CycPolyInt 0 := fun _ => 2
  let dze : CycPolyInt 0 := fun _ => 2
  have hDiff : cycZqAdd (cycZqMul stmt.A (cycIntToZq 12289 dzs)) (cycIntToZq 12289 dze) =
      cycZqMul (cycIntToZq 12289 (cycIntSub c0.toIntPoly c1.toIntPoly)) (stmt.branchU false) := by
    funext ⟨k, hk⟩
    match k with
    | 0 => apply ModZq.ext; rfl
    | _ + 1 => omega
  let w : ShortMonomialRelaxedRlweWitness 1 0 12289 stmt :=
    ShortMonomialRelaxedRlweWitness.ofForkDifference stmt ⟨0, by decide⟩ false c0 c1
      (by decide) dzs dze (by decide) (by decide) hDiff
  refine ⟨stmt, w, (fun _ => 1), (fun _ => 1), by decide, by decide, ?_⟩
  funext ⟨k, hk⟩
  match k with
  | 0 => apply ModZq.ext; rfl
  | _ + 1 => omega

/-- Nonzero secret and error in a degree-two cyclotomic ring (nu = 1). -/
theorem witness_short_rlwe_key_relation_positive_dimension :
    ∃ (stmt : RlweOrSigmaStatement 1 12289)
      (w : ShortMonomialRelaxedRlweWitness 1 1 12289 stmt)
      (sTrue eTrue : CycPolyInt 1),
      ShortRlweKeyRelation stmt.A (stmt.branchU w.branch) 1 sTrue eTrue ∧
      cycIntInfNorm sTrue = 1 ∧ cycIntInfNorm eTrue = 1 := by
  let stmt : RlweOrSigmaStatement 1 12289 :=
    { A := cycZqOne
      u0 := fun _ => ModZq.ofInt 12289 2
      u1 := fun _ => ModZq.ofInt 12289 2
      Bz := 3070 }
  let c0 : SignedMonomialChal 1 := ⟨false, ⟨0, by decide⟩⟩
  let c1 : SignedMonomialChal 1 := ⟨true, ⟨0, by decide⟩⟩
  let dzs : CycPolyInt 1 := fun _ => 2
  let dze : CycPolyInt 1 := fun _ => 2
  have hDiff : cycZqAdd (cycZqMul stmt.A (cycIntToZq 12289 dzs)) (cycIntToZq 12289 dze) =
      cycZqMul (cycIntToZq 12289 (cycIntSub c0.toIntPoly c1.toIntPoly)) (stmt.branchU false) := by
    funext ⟨k, hk⟩
    match k with
    | 0 => apply ModZq.ext; rfl
    | 1 => apply ModZq.ext; rfl
    | _ + 2 => omega
  let w : ShortMonomialRelaxedRlweWitness 1 1 12289 stmt :=
    ShortMonomialRelaxedRlweWitness.ofForkDifference stmt ⟨0, by decide⟩ false c0 c1
      (by decide) dzs dze (by decide) (by decide) hDiff
  refine ⟨stmt, w, (fun _ => 1), (fun _ => 1), ⟨by decide, by decide, ?_⟩, by decide, by decide⟩
  funext ⟨k, hk⟩
  match k with
  | 0 => apply ModZq.ext; rfl
  | 1 => apply ModZq.ext; rfl
  | _ + 2 => omega

theorem witness_valid_rlwe_or_sigma_fork_inhabited :
    ∃ (stmt : RlweOrSigmaStatement 10 12289)
      (c c' : Fin 13 → SignedMonomialChal 10)
      (tr tr' : RlweOrSigmaTranscript 13 10 12289),
      ValidRlweOrSigmaFork 13 10 12289 stmt c c' tr tr' := by
  have h := inhabited_rlwe_or_sigma_13_valid_transcripts_1024
  exact ⟨sampleRlweOrSigmaStmt1024, _, _, _, _,
    ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩

/-- **Inhabitedness Witness 3 (`inhabited_rlwe_or_sigma_24_valid_transcripts_1024`)**:
    Proves inhabitedness of valid $N = 1024, q = 12289, R = 24, B_z = 3070$ forked `PQ128` OR-Sigma
    transcripts `(trA, trB)` with non-zero CRS `A = 1 + X`, non-zero secret `(s, e) = (1, X)`,
    identical commitments, and distinct 24-challenge vectors `chA ≠ chB`, where
    `tryExtractShortMonomialOr24Witness` succeeds with `.inl w` and `‖w.sIso‖_∞, ‖w.eIso‖_∞ ≤ 6140`! -/
theorem inhabited_rlwe_or_sigma_24_valid_transcripts_1024 :
    let chA : Fin 24 → SignedMonomialChal 10 := fun _ => ⟨false, ⟨0, by decide⟩⟩
    let chB : Fin 24 → SignedMonomialChal 10 := fun i =>
      if i.val = 23 then ⟨false, ⟨1, by decide⟩⟩ else ⟨false, ⟨0, by decide⟩⟩
    let ys : Fin 24 → CycPolyInt 10 := fun _ => sampleCyc1024MaskY
    let ye : Fin 24 → CycPolyInt 10 := fun _ => sampleCyc1024MaskY
    let cFake : Fin 24 → SignedMonomialChal 10 := fun _ => ⟨true, ⟨3, by decide⟩⟩
    let trA := buildHonestRlweOrSigmaTranscript 24 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA
    let trB := buildHonestRlweOrSigmaTranscript 24 10 12289 sampleRlweOrSigmaStmt1024 false
      sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chB
    chA ≠ chB ∧
    trA.t0 = trB.t0 ∧ trA.t1 = trB.t1 ∧
    verifyRlweOrSigma 24 10 12289 sampleRlweOrSigmaStmt1024 chA trA = true ∧
    verifyRlweOrSigma 24 10 12289 sampleRlweOrSigmaStmt1024 chB trB = true ∧
    (∃ w, tryExtractShortMonomialOr24Witness sampleRlweOrSigmaStmt1024 chA chB trA trB = PSum.inl w ∧
          cycIntInfNorm w.sIso ≤ 6140 ∧
          cycIntInfNorm w.eIso ≤ 6140) := by
  intro chA chB ys ye cFake trA trB
  have hChNe : chA ≠ chB := by
    intro hEq
    have h23 := congrFun hEq ⟨23, by decide⟩
    dsimp only [chA, chB] at h23
    revert h23; decide
  have hSame := buildHonestRlweOrSigmaTranscript_same_commitments 24 10 12289
    sampleRlweOrSigmaStmt1024 false sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA chB
  have hNormS : cycIntInfNorm sampleCyc1024SecretS ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretS signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormE : cycIntInfNorm sampleCyc1024SecretE ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024SecretE signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hNormY : cycIntInfNorm sampleCyc1024MaskY ≤ 1 := by
    rw [cycIntInfNorm_le_iff]; intro k
    unfold sampleCyc1024MaskY signedMonomial negacyclicSignedMonomial signBitToInt
    split <;> decide
  have hSafeS : ∀ i : Fin 24, cycIntInfNorm (ys i) + cycIntInfNorm sampleCyc1024SecretS ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hSafeE : ∀ i : Fin 24, cycIntInfNorm (ye i) + cycIntInfNorm sampleCyc1024SecretE ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ye, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hFakeY : ∀ i : Fin 24, cycIntInfNorm (ys i) ≤ sampleRlweOrSigmaStmt1024.Bz := by
    intro _; dsimp [ys, sampleRlweOrSigmaStmt1024, rlweProductionBz]; omega
  have hAccA := buildHonestRlweOrSigmaTranscript_accepts sampleRlweOrSigmaStmt1024 false
    sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chA rfl hSafeS hSafeE hFakeY hFakeY
  have hAccB := buildHonestRlweOrSigmaTranscript_accepts sampleRlweOrSigmaStmt1024 false
    sampleCyc1024SecretS sampleCyc1024SecretE ys ye cFake ys ye chB rfl hSafeS hSafeE hFakeY hFakeY
  have hFork : ValidRlweOrSigmaFork 24 10 12289 sampleRlweOrSigmaStmt1024 chA chB trA trB :=
    ⟨hSame.1, hSame.2, hChNe, hAccA, hAccB⟩
  obtain ⟨w, hw⟩ := tryExtractShortMonomialOr24Witness_complete sampleRlweOrSigmaStmt1024
    chA chB trA trB hFork
  have hBz : sampleRlweOrSigmaStmt1024.Bz = 3070 := rfl
  have hsLe : cycIntInfNorm w.sIso ≤ 6140 := by
    have h := w.sIso_infNorm_le; rw [hBz] at h; exact h
  have heLe : cycIntInfNorm w.eIso ≤ 6140 := by
    have h := w.eIso_infNorm_le; rw [hBz] at h; exact h
  exact ⟨hChNe, hSame.1, hSame.2, hAccA, hAccB, ⟨w, hw, hsLe, heLe⟩⟩

theorem witness_valid_rlwe_or_sigma_24_fork_inhabited :
    ∃ (stmt : RlweOrSigmaStatement 10 12289)
      (c c' : Fin 24 → SignedMonomialChal 10)
      (tr tr' : RlweOrSigmaTranscript 24 10 12289),
      ValidRlweOrSigmaFork 24 10 12289 stmt c c' tr tr' := by
  have h := inhabited_rlwe_or_sigma_24_valid_transcripts_1024
  exact ⟨sampleRlweOrSigmaStmt1024, _, _, _, _,
    ⟨h.2.1, h.2.2.1, h.1, h.2.2.2.1, h.2.2.2.2.1⟩⟩

/-- `#tooth`: 13 repetitions (`2^143`) fall strictly below the `(2^128)^2` Grover threshold,
    requiring the 24-repetition (`2^264`) profile for `PQ128` quantum soundness. -/
theorem tooth_rlwe_or_sigma_13_challenge_space_below_pq128_grover :
    ¬ ((2 ^ 128) ^ 2 ≤ rlweOrSigmaChallengeCard 10 13) := by
  decide

/-- `#tooth`: identical 24-challenge vectors are refused by `tryExtractShortMonomialOr24Witness`. -/
theorem tooth_short_24_extractor_refuses_identical_challenges
    {nu q : Nat} [NeZero q]
    (stmt : RlweOrSigmaStatement nu q)
    (c : Fin 24 → SignedMonomialChal nu)
    (tr tr' : RlweOrSigmaTranscript 24 nu q)
    (w : ShortMonomialRelaxedRlweWitness 24 nu q stmt) :
    tryExtractShortMonomialOr24Witness stmt c c tr tr' ≠ PSum.inl w := by
  have hcEq : cycAllFin 24 (fun _ => true) = true := by decide
  unfold tryExtractShortMonomialOr24Witness
  simp only [decide_true, hcEq, ↓reduceDIte]
  split
  · split
    · split
      · split
        · intro h; cases h
        · intro h; cases h
      · intro h; cases h
    · intro h; cases h
  · intro h; cases h

#tooth_pair Qsag.signedMonomial_challenge_set_pairwise_invertible vs Qsag.tooth_even_modulus_no_inverse_1024
#tooth_pair Qsag.signedMonomial_1024_challenge_set_2048_pairwise_invertible vs Qsag.tooth_two_term_no_inverse_12289
#tooth_pair Qsag.extract_rlwe_or_sigma_13_short_witness_1024_sound vs Qsag.tooth_short_monomial_witness_refutes_zero_secret_at_12289
#tooth_pair Qsag.extract_rlwe_or_sigma_24_short_witness_1024_sound vs Qsag.tooth_short_monomial_witness_refutes_zero_secret_at_12289
#tooth_pair Qsag.rlwe_or_sigma_24_pq128_vs_13_grover_ceiling vs Qsag.tooth_rlwe_or_sigma_13_challenge_space_below_pq128_grover
#tooth_pair Qsag.short_monomial_witness_recovers_secret_or_breaks_short_sis vs Qsag.tooth_cofactor_relation_admits_zero_secret_at_12289
#tooth_pair Qsag.tryExtractShortMonomialOr13Witness_complete vs Qsag.tooth_short_extractor_refuses_identical_challenges
#tooth_pair Qsag.tryExtractShortMonomialOr24Witness_complete vs Qsag.tooth_short_24_extractor_refuses_identical_challenges

#verify_inhabited Qsag.short_monomial_witness_recovers_secret_or_breaks_short_sis Qsag.witness_short_rlwe_key_relation_positive_dimension
#verify_inhabited Qsag.extract_rlwe_or_sigma_13_short_witness_1024_sound Qsag.witness_valid_rlwe_or_sigma_fork_inhabited
#verify_inhabited Qsag.tryExtractShortMonomialOr13Witness_complete Qsag.witness_valid_rlwe_or_sigma_fork_inhabited
#verify_inhabited Qsag.extract_rlwe_or_sigma_24_short_witness_1024_sound Qsag.witness_valid_rlwe_or_sigma_24_fork_inhabited
#verify_inhabited Qsag.tryExtractShortMonomialOr24Witness_complete Qsag.witness_valid_rlwe_or_sigma_24_fork_inhabited

#verify_constructive Qsag.cycIntInfNorm_mul_negacyclicSignedMonomial_eq
#verify_constructive Qsag.SignedMonomialChal.ofBitVec_xor
#verify_constructive Qsag.signedMonomial_challenge_set_pairwise_invertible
#verify_constructive Qsag.extract_rlwe_or_sigma_13_short_witness_1024_sound
#verify_constructive Qsag.extract_rlwe_or_sigma_24_short_witness_1024_sound
#verify_constructive Qsag.extract_rlwe_or_sigma_24_recovers_secret_or_breaks_short_sis
#verify_constructive Qsag.rlwe_or_sigma_24_pq128_vs_13_grover_ceiling
#verify_constructive Qsag.short_monomial_witness_recovers_secret_or_breaks_short_sis
#verify_constructive Qsag.tryExtractShortMonomialOr13Witness_complete
#verify_constructive Qsag.tryExtractShortMonomialOr24Witness_complete
#verify_constructive Qsag.tooth_cofactor_relation_admits_zero_secret_at_12289
#verify_constructive Qsag.tooth_short_monomial_witness_refutes_zero_secret_at_12289

end AssuranceGates

end Qsag
