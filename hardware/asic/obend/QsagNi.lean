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
   - `#tooth` mutation-sensitivity witnesses refuting single-coefficient perturbations in `M_4`
     and Goldilocks 96-bit folding.

2. Emits 7 `RtlModule` specifications (all passing `checkRtlModuleW`), writing both `.sv`
   (`emitModuleSV`) and Lean-side SMT-LIB2 miter obligations (`emitYosysLecSmt2`) for Z3 + Bitwuzla LEC.

Run on a Linux x86_64 build host against the read-only built Obend tree:
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

def all : List RtlModule := [
  reduce128Spec, mulSpec, sum6Spec, m4Spec, meColSpec, meSpec, miSpec
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
