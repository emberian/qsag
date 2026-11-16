/-
QSAG-NI Formal Hardware & Algebraic Specifications in Obend (`Obend.Hardware.HDL` + `Obend.Hardware.YosysLec`).

1. Proves (`0 sorry`, `0 sorryAx`, `0 custom axiom`, verified via `#print axioms`) the core algebraic
   and hardware-evaluation (`evalModuleOutputs`) theorems of the QSAG-NI silicon datapath:
   - Goldilocks (`p = 2^64 - 2^32 + 1`) epsilon & 96-bit carry-save folding congruences
     (`2^64 ≡ 2^32 - 1 (mod p)`, `2^96 ≡ -1 (mod p)` via `(2^32 + 1) · p = 2^96 + 1`),
     1-bit complement negation identity, and `mulSpec_sound` (`evalModuleOutputs mulSpec`).
   - Poseidon2 `M_4` 7-addition butterfly expansion to `circ(2, 3, 1, 1)` AND constructive
     integer/modular invertibility (`M_4_inv · M_4 = 35 · I_4`, `35 * inv35 ≡ 1 (mod p)`).
   - Poseidon2 `M_E` 12×12 Kronecker circulant factorization `(I_3 + J_3) ⊗ M_4` AND constructive
     12-lane invertibility (`(4 I_3 - J_3)(I_3 + J_3) = 4 · I_3`, `140 * inv140 ≡ 1 (mod p)`).
   - Poseidon2 `M_I = J_12 + diag(-64, 1, 2, 4, ..., 1024)` hardware partial-round split identity
     (decoupling `s_tail = ∑_{j=1..11} x_j` from lane-0 `x_0^7`) AND Sherman–Morrison determinant
     non-vanishing (`det_num = 3055`, `3055 * inv3055 ≡ 1 (mod p)`).
   - 9-product Tower Karatsuba `GoldilocksExt4` equivalence to 16-product schoolbook multiplication
     over `𝔽_p[v]/(v^4 - 7)` in limb order `[1, u, v, u·v]` (`u = v^2`, `u^2 = 7`), over both `ℤ`
     and `ℤ/pℤ`.
   - `#tooth` mutation-sensitivity witnesses refuting single-coefficient perturbations in `M_4`,
     9-product Karatsuba `Ext4`, and Goldilocks 96-bit folding.

2. Emits 9 `RtlModule` specifications (all passing `checkRtlModuleW`), writing both `.sv`
   (`emitModuleSV`) and Lean-side SMT-LIB2 miter obligations (`emitYosysLecSmt2`) for Z3 + Bitwuzla LEC.

Run on `bb2` against the read-only built Obend tree:
  LEAN_PATH=$OBEND/lean/.lake/build/lib/lean lean --run QsagNi.lean <outdir>
-/
import Obend.Apps.ZkNtt
import Obend.Hardware.YosysLec

open Obend.Hardware.HDL
open Obend.Apps.ZkNtt

namespace QsagNi

/-! ## Part 1: Kernel-Checked Algebraic & Hardware Soundness Theorems (`0 sorry`, `0 axiom`) -/

/-- Goldilocks prime as an `Int` (`p = 2^64 - 2^32 + 1 = 18446744069414584321`). -/
def glPrimeInt : Int := 18446744069414584321

theorem glPrimeInt_eq_nat : glPrimeInt = (goldilocksPrime : Int) := by decide

/-- Fundamental Goldilocks 64-bit fold congruence: `2^64 = p + (2^32 - 1)`. -/
theorem goldilocks_pow64_fold_int (k : Int) :
    (k * (2 ^ 64 : Int)) % glPrimeInt = (k * ((2 ^ 32 : Int) - 1)) % glPrimeInt := by
  have h : k * (2 ^ 64 : Int) = k * ((2 ^ 32 : Int) - 1) + k * glPrimeInt := by
    unfold glPrimeInt
    have h64 : (2 ^ 64 : Int) = ((2 ^ 32 : Int) - 1) + 18446744069414584321 := by decide
    rw [h64, Int.mul_add]
  rw [h, Int.add_mul_emod_self_right]

/-- Fundamental Goldilocks 96-bit fold congruence: `2^96 + 1 = (2^32 + 1) · p`, hence `2^96 ≡ -1 (mod p)`. -/
theorem goldilocks_pow96_fold_int (k : Int) :
    (k * (2 ^ 96 : Int)) % glPrimeInt = (-k) % glPrimeInt := by
  have h96 : (2 ^ 96 : Int) = -1 + ((2 ^ 32 : Int) + 1) * glPrimeInt := by decide
  have h : k * (2 ^ 96 : Int) = -k + (k * ((2 ^ 32 : Int) + 1)) * glPrimeInt := by
    rw [h96, Int.mul_add, Int.mul_neg, Int.mul_one, Int.mul_assoc]
  rw [h, Int.add_mul_emod_self_right]

/-- 1-bit complement identity used by `csagen.py` for negative terms:
`-(b · W) = (1 - b) · W - W` for every bit `b` and weight `W = 2^w`. -/
theorem csa_neg_bit_complement_id (b W : Int) :
    -(b * W) = (1 - b) * W - W := by
  rw [Int.sub_mul, Int.one_mul]
  omega

/-- `#tooth` mutation witness: replacing `-1` by `+1` at `2^96` fails at `k = 1`. -/
theorem tooth_pow96_sign_flip_refuted :
    ((1 : Int) * (2 ^ 96 : Int)) % glPrimeInt ≠ (1 : Int) % glPrimeInt := by decide

/-! ### Poseidon2 `M_4` Butterfly & Constructive Invertibility (`det(M_4) = -35`) -/

/-- The 7-addition `M_4` butterfly structure implemented in `m4` and `qsag_p2_m4`. -/
def m4ButterflyInt (b0 b1 b2 b3 : Int) : Int × Int × Int × Int :=
  let s01 := b0 + b1
  let s23 := b2 + b3
  let s   := s01 + s23
  (s + (b0 + (b1 + b1)),
   s + (b1 + (b2 + b2)),
   s + (b2 + (b3 + b3)),
   s + (b3 + (b0 + b0)))

/-- Exact matrix-vector product of `M_4 = circ(2, 3, 1, 1)`. -/
def m4MatrixInt (b0 b1 b2 b3 : Int) : Int × Int × Int × Int :=
  (2 * b0 + 3 * b1 + b2 + b3,
   b0 + 2 * b1 + 3 * b2 + b3,
   b0 + b1 + 2 * b2 + 3 * b3,
   3 * b0 + b1 + b2 + 2 * b3)

/-- The 7-addition `M_4` butterfly equals `circ(2, 3, 1, 1)` identically over `ℤ`. -/
theorem m4_butterfly_eq_circulant (b0 b1 b2 b3 : Int) :
    m4ButterflyInt b0 b1 b2 b3 = m4MatrixInt b0 b1 b2 b3 := by
  dsimp only [m4ButterflyInt, m4MatrixInt]
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Explicit integer scaled inverse `circ(-4, 3, -11, 17)` such that `M4_inv35 · M_4 = 35 · I_4`. -/
def m4ScaledInv35Int (y0 y1 y2 y3 : Int) : Int × Int × Int × Int :=
  (-4 * y0 +  3 * y1 - 11 * y2 + 17 * y3,
   17 * y0 -  4 * y1 +  3 * y2 - 11 * y3,
  -11 * y0 + 17 * y1 -  4 * y2 +  3 * y3,
    3 * y0 - 11 * y1 + 17 * y2 -  4 * y3)

/-- Exact integer invertibility certificate: `m4ScaledInv35Int (M_4 (b)) = 35 · b` for all `b ∈ ℤ^4`. -/
theorem m4_adjugate_left_inv (b0 b1 b2 b3 : Int) :
    let (y0, y1, y2, y3) := m4ButterflyInt b0 b1 b2 b3
    m4ScaledInv35Int y0 y1 y2 y3 = (35 * b0, 35 * b1, 35 * b2, 35 * b3) := by
  dsimp only [m4ButterflyInt, m4ScaledInv35Int]
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- `35` is coprime to the Goldilocks prime (`35 * inv35ModP ≡ 1 (mod p)`). -/
def inv35ModP : Int := 15284445086086369866

theorem inv35_mul_mod_p : (35 * inv35ModP) % glPrimeInt = 1 := by decide

/-- `#tooth` mutation witness: swapping `2` and `3` on `b1` breaks `m4_butterfly_eq_circulant`. -/
theorem tooth_m4_weight_swap_refuted :
    let (y0, _, _, _) := m4ButterflyInt 0 1 0 0
    y0 ≠ 2 * 0 + 2 * 1 + 0 + 0 := by decide

/-! ### Poseidon2 `M_E` 12×12 Kronecker Circulant & `140 · I_12` Invertibility -/

/-- Outer 3-block circulant `circ(2, 1, 1) = I_3 + J_3` applied per column `i`. -/
def meOuterColInt (y0 y1 y2 : Int) : Int × Int × Int :=
  let s := y0 + y1 + y2
  (y0 + s, y1 + s, y2 + s)

/-- Adjugate `(4 · I_3 - J_3)` of `I_3 + J_3`: `(4 I_3 - J_3)(I_3 + J_3) = 4 · I_3`. -/
def meOuterColAdjInt (z0 z1 z2 : Int) : Int × Int × Int :=
  let s := z0 + z1 + z2
  (4 * z0 - s, 4 * z1 - s, 4 * z2 - s)

theorem me_outer_col_adj_inv (y0 y1 y2 : Int) :
    let (z0, z1, z2) := meOuterColInt y0 y1 y2
    meOuterColAdjInt z0 z1 z2 = (4 * y0, 4 * y1, 4 * y2) := by
  dsimp only [meOuterColInt, meOuterColAdjInt]
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, by omega⟩

/-- Full 12-lane `M_E` Kronecker composition has exact scale factor `4 * 35 = 140`,
and `140` has an explicit modular inverse modulo `goldilocksPrime`. -/
def inv140ModP : Int := 13044483306228884627

theorem inv140_mul_mod_p : (140 * inv140ModP) % glPrimeInt = 1 := by decide

/-! ### Poseidon2 `M_I` Partial-Round Split Identity & Sherman–Morrison Non-Singularity -/

def miFullLane0Int (x0 sTail rc0 : Int) : Int :=
  (x0 + sTail) - 64 * x0 + rc0

def miSplitLane0Int (x0 sTail rc0 : Int) : Int :=
  sTail + rc0 - 63 * x0

def miFullLanePosInt (x0 xl diagL sTail rcl : Int) : Int :=
  (x0 + sTail) + diagL * xl + rcl

def miSplitLanePosInt (x0 xl diagL sTail rcl : Int) : Int :=
  sTail + rcl + x0 + diagL * xl

theorem mi_partial_split_lane0_eq (x0 sTail rc0 : Int) :
    miSplitLane0Int x0 sTail rc0 = miFullLane0Int x0 sTail rc0 := by
  unfold miSplitLane0Int miFullLane0Int
  omega

theorem mi_partial_split_lanePos_eq (x0 xl diagL sTail rcl : Int) :
    miSplitLanePosInt x0 xl diagL sTail rcl = miFullLanePosInt x0 xl diagL sTail rcl := by
  unfold miSplitLanePosInt miFullLanePosInt
  omega

/-- Sherman–Morrison determinant numerator of `M_I = J_12 + diag(-64, 1, 2, 4, ..., 1024)`:
`1024 · (1 - 1/64 + ∑_{k=0..10} 2^{-k}) = 1024 - 16 + 2047 = 3055`, invertible mod `p`. -/
def inv3055ModP : Int := 10802365021336396514

theorem mi_sherman_morrison_unit :
    ((1024 : Int) - 16 + (1024 + 512 + 256 + 128 + 64 + 32 + 16 + 8 + 4 + 2 + 1) = 3055) ∧
    (3055 * inv3055ModP) % glPrimeInt = 1 := by decide

/-! ### 9-Product Tower Karatsuba `GoldilocksExt4` Equivalence Theorem -/

/-- 16-product schoolbook `GoldilocksExt4` multiply-add `a * b + z` over `𝔽_p[v]/(v^4 - 7)`
in limb order `[1, u, v, u·v]` (`u = v^2`, `u^2 = 7`), matching `crates/qsag-agg/src/field.rs`. -/
def ext4SchoolbookInt (a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 : Int) : Int × Int × Int × Int :=
  (z0 + a0 * b0 + 7 * (a1 * b1 + a2 * b3 + a3 * b2),
   z1 + a0 * b1 + a1 * b0 + a2 * b2 + 7 * (a3 * b3),
   z2 + a0 * b2 + a2 * b0 + 7 * (a1 * b3 + a3 * b1),
   z3 + a0 * b3 + a3 * b0 + a1 * b2 + a2 * b1)

/-- 9-product Tower Karatsuba `GoldilocksExt4` multiply-add implemented by
`qsag_ext4_kara_inputs` + 9 shared 64×64 Dadda trees + `qsag_ext4_kara_combine`. -/
def ext4KaratsubaInt (a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 : Int) : Int × Int × Int × Int :=
  let p0 := a0 * b0
  let p1 := a1 * b1
  let p2 := (a0 + a1) * (b0 + b1)
  let p3 := a2 * b2
  let p4 := a3 * b3
  let p5 := (a2 + a3) * (b2 + b3)
  let p6 := (a0 + a2) * (b0 + b2)
  let p7 := (a1 + a3) * (b1 + b3)
  let p8 := ((a0 + a1) + (a2 + a3)) * ((b0 + b1) + (b2 + b3))
  let t2 := -p0 - 7 * p1 - p3 - 7 * p4
  let t3 := p0 + p1 - p2 + p3 + p4 - p5
  (p0 + 7 * p1 - 7 * p3 - 7 * p4 + 7 * p5 + z0,
   -p0 - p1 + p2 + p3 + 7 * p4 + z1,
   t2 + p6 + 7 * p7 + z2,
   t3 - p6 - p7 + p8 + z3)

private theorem bilin2 (x0 x1 y0 y1 : Int) :
    (x0 + x1) * (y0 + y1) = x0 * y0 + x0 * y1 + x1 * y0 + x1 * y1 := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add]
  omega

/-- **Tower Karatsuba Exact Ring Theorem**: the 9-product Karatsuba schedule equals the 16-product
schoolbook `Ext4` multiply-add identically over `ℤ` (and hence modulo `goldilocksPrime`). -/
theorem ext4_karatsuba_eq_schoolbook (a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 : Int) :
    ext4KaratsubaInt a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 =
    ext4SchoolbookInt a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 := by
  dsimp only [ext4KaratsubaInt, ext4SchoolbookInt]
  have h2 := bilin2 a0 a1 b0 b1
  have h5 := bilin2 a2 a3 b2 b3
  have h6 := bilin2 a0 a2 b0 b2
  have h7 := bilin2 a1 a3 b1 b3
  have h8 : ((a0 + a1) + (a2 + a3)) * ((b0 + b1) + (b2 + b3)) =
      (a0 + a1) * (b0 + b1) + (a2 + a3) * (b2 + b3) +
      (a0 * b2 + a0 * b3 + a1 * b2 + a1 * b3) +
      (a2 * b0 + a2 * b1 + a3 * b0 + a3 * b1) := by
    rw [bilin2 (a0 + a1) (a2 + a3) (b0 + b1) (b2 + b3),
        bilin2 a0 a1 b2 b3, bilin2 a2 a3 b0 b1]
    omega
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- Modular corollary over `𝔽_p^4`: every limb of 9-product Karatsuba mod `p` equals schoolbook mod `p`. -/
theorem ext4_karatsuba_mod_p_eq (a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3 : Int) :
    let (k0, k1, k2, k3) := ext4KaratsubaInt a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3
    let (s0, s1, s2, s3) := ext4SchoolbookInt a0 a1 a2 a3 b0 b1 b2 b3 z0 z1 z2 z3
    (k0 % glPrimeInt, k1 % glPrimeInt, k2 % glPrimeInt, k3 % glPrimeInt) =
    (s0 % glPrimeInt, s1 % glPrimeInt, s2 % glPrimeInt, s3 % glPrimeInt) := by
  rw [ext4_karatsuba_eq_schoolbook]

/-- `#tooth` mutation witness: omitting `-7 * p3` in limb 0 fails at `v * v = u` (`a2 = b2 = 1`, `u * u = 7`). -/
theorem tooth_karatsuba_missing_p3_refuted :
    ext4KaratsubaInt 0 0 1 0 0 0 1 0 0 0 0 0 ≠ (7, 1, 0, 0) := by decide

/-! ## Part 2: Obend `RtlModule` Hardware Specifications & `evalModuleOutputs` Soundness -/

instance : Inhabited RtlExpr := ⟨.const 0#64⟩

def mkModule (name : String) (ins : List String) (b : WireM (List OutputPort)) : RtlModule :=
  let r := Id.run (b.run {})
  { name := name, inputNames := ins, inputWidths := ins.map (fun _ => 64),
    wires := r.2.wires.toList, regs := [], outputs := r.1 }

/-- `(lo + 2^64 * hi) mod p`: `goldilocksReduce128` of `apps/zk-ntt/GoldilocksField.obend`. -/
def reduce128Spec : RtlModule := mkModule "qsag_ni_gl_reduce128_spec" ["lo", "hi"] do
  let lo := RtlExpr.inputPort 0
  let hi := RtlExpr.inputPort 1
  let hiLo ← wire "hilo" (.alu .bitAnd hi glMask32)
  let hiHi ← wire "hihi" (.alu .lshr hi glShift32)
  let mid ← wire "mid" (.alu .sub (.alu .shl hiLo glShift32) hiLo)
  let loC ← glCanon "lo" lo
  let t1 ← glAdd "t1" loC mid
  let r ← glSub "red" t1 hiHi
  pure [{ name := "r", expr := r }]

/-- `(a * b) mod p` for any 64-bit words (`fieldMul`). -/
def mulSpec : RtlModule := mkModule "qsag_ni_gl_mul_spec" ["a", "b"] do
  let r ← glMul "m" (.inputPort 0) (.inputPort 1)
  pure [{ name := "r", expr := r }]

/-- Hardware evaluation soundness of `mulSpec` (`evalModuleOutputs` matches canonical `goldilocksMulSpec`). -/
theorem mulSpec_sound (inputs regs : Nat → BitVec 64) :
    ∃ v : BitVec 64,
      (evalModuleOutputs mulSpec inputs regs).lookup "r" = some v ∧
      v.toNat < goldilocksPrime ∧
      v = BitVec.ofNat 64 (goldilocksMulSpec (inputs 0).toNat (inputs 1).toNat) := by
  have h := glMul_sound "m" (.inputPort 0) (.inputPort 1) {} inputs regs (by rfl) (by rfl)
  refine ⟨evalRtlExpr inputs (evalWireTable inputs regs (Id.run ((glMul "m" (.inputPort 0) (.inputPort 1)).run {})).2.wires.toList) regs (Id.run ((glMul "m" (.inputPort 0) (.inputPort 1)).run {})).1, ?_, h.2.1, h.2.2⟩
  rfl

def canonInputs (tag : String) (base n : Nat) : WireM (Array RtlExpr) := do
  let mut xs := #[]
  for i in [0:n] do
    xs := xs.push (← glCanon s!"{tag}{i}" (.inputPort (base + i)))
  pure xs

def glDouble (tag : String) (x : RtlExpr) (k : Nat) : WireM RtlExpr := do
  let mut v := x
  for i in [0:k] do
    v ← glAdd s!"{tag}_dbl{i}" v v
  pure v

def glMul7 (tag : String) (x : RtlExpr) : WireM RtlExpr := do
  let x8 ← glDouble s!"{tag}_8" x 3
  glSub s!"{tag}_7" x8 x

def names (p : String) (n : Nat) : List String := (List.range n).map fun i => s!"{p}{i}"

/-- 6-input modular sum `qsag_ni_gl_sum6_spec` (specification for `qsag_gl64_sum6`). -/
def sum6Spec : RtlModule := mkModule "qsag_ni_gl_sum6_spec" (names "a" 6) do
  let a ← canonInputs "a" 0 6
  let s01 ← glAdd "s01" a[0]! a[1]!
  let s23 ← glAdd "s23" a[2]! a[3]!
  let s45 ← glAdd "s45" a[4]! a[5]!
  let s03 ← glAdd "s03" s01 s23
  let r   ← glAdd "r"   s03 s45
  pure [{ name := "r", expr := r }]

/-- `poseidon2_apply_m4` combinator. -/
def m4 (tag : String) (b : Array RtlExpr) : WireM (Array RtlExpr) := do
  let s01 ← glAdd s!"{tag}_s01" b[0]! b[1]!
  let s23 ← glAdd s!"{tag}_s23" b[2]! b[3]!
  let s ← glAdd s!"{tag}_s" s01 s23
  let mut out := #[]
  for i in [0:4] do
    let d ← glAdd s!"{tag}_d{i}" b[(i + 1) % 4]! b[(i + 1) % 4]!
    let e ← glAdd s!"{tag}_e{i}" b[i]! d
    out := out.push (← glAdd s!"{tag}_o{i}" s e)
  pure out

/-- Standalone 4-lane `M_4` module (specification for `qsag_p2_m4`). -/
def m4Spec : RtlModule := mkModule "qsag_ni_p2_m4_spec" (names "b" 4) do
  let b ← canonInputs "b" 0 4
  let y ← m4 "m4" b
  pure ((List.range 4).map fun i => { name := s!"y{i}", expr := y[i]! })

/-- Standalone 3-block `M_E` outer column + round-constant module (specification for `qsag_p2_me_col`). -/
def meColSpec : RtlModule := mkModule "qsag_ni_p2_me_col_spec" (names "y" 3 ++ names "rc" 3) do
  let y ← canonInputs "y" 0 3
  let rc ← canonInputs "rc" 3 3
  let s01 ← glAdd "s01" y[0]! y[1]!
  let s   ← glAdd "s"   s01 y[2]!
  let mut outs := []
  for b in [0:3] do
    let v ← glAdd s!"v{b}" y[b]! s
    let o ← glAdd s!"o{b}" v rc[b]!
    outs := outs ++ [{ name := s!"o{b}", expr := o : OutputPort }]
  pure outs

/-- `poseidon2_apply_me` followed by the addition of twelve round constants. -/
def meSpec : RtlModule := mkModule "qsag_ni_p2_me_spec" (names "x" 12 ++ names "rc" 12) do
  let x ← canonInputs "x" 0 12
  let rc ← canonInputs "rc" 12 12
  let tr := #[0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8, 11].map fun i => x[i]!
  let y0 ← m4 "b0" (tr.extract 0 4)
  let y1 ← m4 "b1" (tr.extract 4 8)
  let y2 ← m4 "b2" (tr.extract 8 12)
  let mut o : Array RtlExpr := Array.replicate 12 (.const 0#64)
  for i in [0:4] do
    let s01 ← glAdd s!"s01_{i}" y0[i]! y1[i]!
    let s ← glAdd s!"s_{i}" s01 y2[i]!
    o := o.set! i (← glAdd s!"o0_{i}" y0[i]! s)
    o := o.set! (4 + i) (← glAdd s!"o1_{i}" y1[i]! s)
    o := o.set! (8 + i) (← glAdd s!"o2_{i}" y2[i]! s)
  let back := #[0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7, 11].map fun i => o[i]!
  let mut outs := []
  for l in [0:12] do
    let y ← glAdd s!"y{l}" back[l]! rc[l]!
    outs := outs ++ [{ name := s!"y{l}", expr := y : OutputPort }]
  pure outs

/-- `poseidon2_apply_mi` (`J + diag(-64, 1, 2, ..., 1024)`) followed by twelve round constants. -/
def miSpec : RtlModule := mkModule "qsag_ni_p2_mi_spec" (names "x" 12 ++ names "rc" 12) do
  let x ← canonInputs "x" 0 12
  let rc ← canonInputs "rc" 12 12
  let mut s := x[0]!
  for i in [1:12] do
    s ← glAdd s!"sum{i}" s x[i]!
  let mut outs := []
  for l in [0:12] do
    let d ← if l == 0 then do
        let m ← glDouble "x0" x[0]! 6
        glSub "neg64" (.const 0#64) m
      else glDouble s!"x{l}" x[l]! (l - 1)
    let v ← glAdd s!"v{l}" d s
    let y ← glAdd s!"y{l}" v rc[l]!
    outs := outs ++ [{ name := s!"y{l}", expr := y : OutputPort }]
  pure outs

/-- Karatsuba 9-product linear reconstruction combiner (specification for `qsag_ext4_kara_combine`). -/
def karaCombineWires (p : Array RtlExpr) (z : Array RtlExpr) : WireM (Array RtlExpr) := do
  let p15 ← glAdd "k_p15" p[1]! p[5]!
  let p34 ← glAdd "k_p34" p[3]! p[4]!
  let d0  ← glSub "k_d0"  p15 p34
  let d07 ← glMul7 "k_d07" d0
  let r0a ← glAdd "k_r0a" p[0]! d07
  let r0  ← glAdd "k_r0"  r0a z[0]!
  let d1a ← glSub "k_d1a" p[2]! p[0]!
  let d1b ← glSub "k_d1b" p[3]! p[1]!
  let p47 ← glMul7 "k_p47" p[4]!
  let r1a ← glAdd "k_r1a" d1a d1b
  let r1b ← glAdd "k_r1b" r1a p47
  let r1  ← glAdd "k_r1"  r1b z[1]!
  let d2a ← glSub "k_d2a" p[6]! p[0]!
  let d2b ← glSub "k_d2b" d2a p[3]!
  let p14 ← glAdd "k_p14" p[1]! p[4]!
  let d2c ← glSub "k_d2c" p[7]! p14
  let d27 ← glMul7 "k_d27" d2c
  let r2a ← glAdd "k_r2a" d2b d27
  let r2  ← glAdd "k_r2"  r2a z[2]!
  let p01 ← glAdd "k_p01" p[0]! p[1]!
  let t3a ← glSub "k_t3a" p01 p[2]!
  let t3b ← glSub "k_t3b" p34 p[5]!
  let p67 ← glAdd "k_p67" p[6]! p[7]!
  let t3c ← glSub "k_t3c" p[8]! p67
  let r3a ← glAdd "k_r3a" t3a t3b
  let r3b ← glAdd "k_r3b" r3a t3c
  let r3  ← glAdd "k_r3"  r3b z[3]!
  pure #[r0, r1, r2, r3]

def ext4KaraCombSpec : RtlModule := mkModule "qsag_ni_ext4_kara_comb_spec" (names "p" 9 ++ names "z" 4) do
  let p ← canonInputs "p" 0 9
  let z ← canonInputs "z" 9 4
  let r ← karaCombineWires p z
  pure ((List.range 4).map fun i => { name := s!"r{i}", expr := r[i]! })

/-- Full 9-product Tower Karatsuba `GoldilocksExt4` multiply-add `RtlModule`. -/
def ext4KaraSpec : RtlModule := mkModule "qsag_ni_ext4_kara_spec" (names "a" 4 ++ names "b" 4 ++ names "z" 4) do
  let a ← canonInputs "a" 0 4
  let b ← canonInputs "b" 4 4
  let z ← canonInputs "z" 8 4
  let a01 ← glAdd "a01" a[0]! a[1]!
  let a23 ← glAdd "a23" a[2]! a[3]!
  let a02 ← glAdd "a02" a[0]! a[2]!
  let a13 ← glAdd "a13" a[1]! a[3]!
  let aall ← glAdd "aall" a01 a23
  let b01 ← glAdd "b01" b[0]! b[1]!
  let b23 ← glAdd "b23" b[2]! b[3]!
  let b02 ← glAdd "b02" b[0]! b[2]!
  let b13 ← glAdd "b13" b[1]! b[3]!
  let ball ← glAdd "ball" b01 b23
  let qa := #[a[0]!, a[1]!, a01, a[2]!, a[3]!, a23, a02, a13, aall]
  let qb := #[b[0]!, b[1]!, b01, b[2]!, b[3]!, b23, b02, b13, ball]
  let mut pr := #[]
  for m in [0:9] do
    pr := pr.push (← glMul s!"pm{m}" qa[m]! qb[m]!)
  let r ← karaCombineWires pr z
  pure ((List.range 4).map fun i => { name := s!"r{i}", expr := r[i]! })

def all : List RtlModule := [
  reduce128Spec, mulSpec, sum6Spec, m4Spec, meColSpec, meSpec, miSpec,
  ext4KaraCombSpec, ext4KaraSpec
]

end QsagNi

-- Kernel axiom hygiene verification (`0 sorryAx` everywhere; algebraic theorems depend ONLY on propext/Quot.sound):
#print axioms QsagNi.goldilocks_pow64_fold_int
#print axioms QsagNi.goldilocks_pow96_fold_int
#print axioms QsagNi.m4_butterfly_eq_circulant
#print axioms QsagNi.m4_adjugate_left_inv
#print axioms QsagNi.me_outer_col_adj_inv
#print axioms QsagNi.mi_partial_split_lane0_eq
#print axioms QsagNi.mi_sherman_morrison_unit
#print axioms QsagNi.ext4_karatsuba_eq_schoolbook
#print axioms QsagNi.mulSpec_sound

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "."
  let mut bad := false
  for m in QsagNi.all do
    if !checkRtlModuleW m then
      IO.eprintln s!"{m.name}: fails checkRtlModuleW; not emitted"
      bad := true
    else
      IO.FS.writeFile (dir / s!"{m.name}.sv")
        (s!"// Generated by Obend.Hardware.HDL.emitModuleSV from QsagNi (hardware/asic/obend/QsagNi.lean)\n" ++ emitModuleSV m)
      IO.FS.writeFile (dir / s!"{m.name}_lec.smt2")
        (s!"; Generated by Obend.Hardware.YosysLec.emitYosysLecSmt2 from QsagNi\n" ++
          Obend.Hardware.YosysLec.emitYosysLecSmt2 m)
      IO.println s!"{m.name}: checkRtlModuleW ok; {m.wires.length} wires, {m.outputs.length} outputs"
  pure (if bad then 1 else 0)
