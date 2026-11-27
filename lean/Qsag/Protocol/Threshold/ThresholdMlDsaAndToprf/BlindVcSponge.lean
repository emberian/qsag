module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.DkgAndSigning
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ## §4. `BlindVC` Rate-6/Capacity-6 6-Limb `absorbRate6Sponge3` Commitment & ZKBoo Selective Disclosure (`blind_vc.rs`) -/

/-! ### §4.1 6-Limb `Lane6` Digests, `ZkSoundnessProfile` (ROM vs QROM) & Arity-Framed `absorbRate6Sponge3` Binding -/

/-- Maximum canonical Goldilocks attributes per `BlindVC` credential (`MAX_VC_ATTRS = 32`, `blind_vc.rs:43`). -/
def vcMaxAttrs : Nat := 32

/-- Small-credential 3-block ZKBoo rate-6 attribute slot ceiling (`6` slots in `absorbRate6Sponge3`). -/
@[expose] def vcSmallMaxAttrs : Nat := 6

/-- Deployed Poseidon2 Merkle accumulator depth (`VC_ACCUMULATOR_DEPTH = 20`, `blind_vc.rs:45`). -/
def vcAccumulatorDepth : Nat := 20

/-- ZKBoo soundness profile (`ZkSoundnessProfile`, `blind_vc.rs:47, 780-810`):
    - `.classical128`: `219` repetitions (`(2/3)^219 < 2^{-128}` classical ROM soundness,
      whereas `2^{-130} < (2/3)^219` yields `< 65`-bit security against QROM Grover challenge grinding);
    - `.quantum128`: `438` repetitions (`VC_ZKBOO_REPS = 438`, default post-quantum profile:
      `(2/3)^438 < 2^{-256}`, sustaining `≥ 128`-bit QROM soundness against $O(2^{k/2})$ Grover
      amplitude amplification over Fiat-Shamir challenge grinding). -/
inductive ZkSoundnessProfile where
  | classical128
  | quantum128
  deriving DecidableEq, Repr

@[expose] def ZkSoundnessProfile.repetitions : ZkSoundnessProfile → Nat
  | .classical128 => 219
  | .quantum128 => 438

/-- Default post-quantum ZKBoo repetition count (`VC_ZKBOO_REPS = 438`, `blind_vc.rs:47`). -/
def vcZkBooReps : Nat := ZkSoundnessProfile.quantum128.repetitions

/-- Legacy classical-ROM repetition count (`219`, `ZkSoundnessProfile::Classical128`). -/
def vcClassicalZkBooReps : Nat := ZkSoundnessProfile.classical128.repetitions

set_option exponentiation.threshold 1024 in
/-- Parameter arithmetic for 219 and 438 repetitions. These inequalities
alone are neither a ROM nor a QROM adversary theorem: they contain no oracle
query budget, commitment failure term, or adaptive Fiat–Shamir simulation. -/
theorem zkSoundnessProfile_rom_vs_qrom_bounds :
    ZkSoundnessProfile.classical128.repetitions = 219 ∧
    ZkSoundnessProfile.quantum128.repetitions = 438 ∧
    vcZkBooReps = 438 ∧
    ratLe (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions)
      (1, 2 ^ 128) ∧
    ratLe (1, 2 ^ 130)
      (2 ^ ZkSoundnessProfile.classical128.repetitions, 3 ^ ZkSoundnessProfile.classical128.repetitions) ∧
    ratLe (2 ^ ZkSoundnessProfile.quantum128.repetitions, 3 ^ ZkSoundnessProfile.quantum128.repetitions)
      (1, 2 ^ 256) := by
  unfold ZkSoundnessProfile.repetitions vcZkBooReps ratLe
  decide

/-- 6-limb Goldilocks digest (`[u64; 6]`, `VC_DIGEST_LIMBS = 6`, `blind_vc.rs:41`):
    6-limb rate/capacity (`p^6 > 2^{383}`), providing `> 191`-bit classical birthday and
    `≥ 128`-bit (`p^2 > 2^{127.9999999996}`) post-quantum BHT / CNS sponge security. -/
structure Lane6 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  x4 : Goldilocks
  x5 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane6.ext {a b : Lane6}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2)
    (h3 : a.x3 = b.x3) (h4 : a.x4 = b.x4) (h5 : a.x5 = b.x5) : a = b := by
  cases a; cases b; subst h0 h1 h2 h3 h4 h5; rfl

def lane6Zero : Lane6 :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero,
   Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

@[expose] def lane6Add (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1, Goldilocks.add a.x2 b.x2,
   Goldilocks.add a.x3 b.x3, Goldilocks.add a.x4 b.x4, Goldilocks.add a.x5 b.x5⟩

@[expose] def lane6Sub (a b : Lane6) : Lane6 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1, Goldilocks.sub a.x2 b.x2,
   Goldilocks.sub a.x3 b.x3, Goldilocks.sub a.x4 b.x4, Goldilocks.sub a.x5 b.x5⟩

@[expose] def lane6Scale (c : Goldilocks) (a : Lane6) : Lane6 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1, Goldilocks.mul c a.x2,
   Goldilocks.mul c a.x3, Goldilocks.mul c a.x4, Goldilocks.mul c a.x5⟩

def state12Rate6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b0.x0, st.b0.x1, st.b0.x2, st.b0.x3, st.b1.x0, st.b1.x1⟩

def state12Cap6 (st : Poseidon2State12) : Lane6 :=
  ⟨st.b1.x2, st.b1.x3, st.b2.x0, st.b2.x1, st.b2.x2, st.b2.x3⟩

def mkState12Of6 (rate cap : Lane6) : Poseidon2State12 :=
  ⟨⟨rate.x0, rate.x1, rate.x2, rate.x3⟩,
   ⟨rate.x4, rate.x5, cap.x0, cap.x1⟩,
   ⟨cap.x2, cap.x3, cap.x4, cap.x5⟩⟩

private theorem state12Rate6_mk (r c : Lane6) : state12Rate6 (mkState12Of6 r c) = r := rfl
private theorem state12Cap6_mk (r c : Lane6) : state12Cap6 (mkState12Of6 r c) = c := rfl

private theorem mkState12Of6_eta (st : Poseidon2State12) :
    mkState12Of6 (state12Rate6 st) (state12Cap6 st) = st := by
  rcases st with ⟨⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨_, _, _, _⟩⟩
  rfl

/-- Domain tag `"VCATTRV1"` (`0x5643_4154_5452_5631`, `blind_vc.rs:53`). -/
def vcAttrCommitTag : UInt64 := 0x5643415454525631

/-- Domain tag `"VCPRESV1"` (`0x5643_5052_4553_5631`, `blind_vc.rs:54`). -/
def vcPresCommitTag : UInt64 := 0x5643505245535631

/-- Domain tag `"VCSCOPV1"` (`0x5643_5343_4F50_5631`, `blind_vc.rs:55`). -/
def vcScopeTagDom : UInt64 := 0x564353434F505631

/-- Domain tag `"VCMKLEV1"` (`0x5643_4D4B_4C45_5631`, `blind_vc.rs:56`). -/
def vcMerkleNodeTag : UInt64 := 0x56434D4B4C455631

/-- Exact 3-permutation Width-12 (`rate = 6, capacity = 6`) `Poseidon2` sponge (`blind_vc.rs:98-115`):
    absorbs three 6-limb rate chunks `(c0, c1, c2)` with capacity `lane6Zero` and outputs the
    permuted 12-limb state (whose 6-limb rate `state12Rate6` is the 6-limb digest). -/
@[expose] def absorbRate6Sponge3 (c0 c1 c2 : Lane6) : Poseidon2State12 :=
  let p1 := poseidon2Perm12 (mkState12Of6 c0 lane6Zero)
  let p2 := poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p1) c1) (state12Cap6 p1))
  poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 p2) c2) (state12Cap6 p2))

private theorem gold_add_left_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a b = Goldilocks.add a c) : b = c := by
  have hs := congrArg (fun z => Goldilocks.sub z a) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) x = y := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem gold_add_right_cancel_vc {a b c : Goldilocks}
    (h : Goldilocks.add a c = Goldilocks.add b c) : a = b := by
  have hs := congrArg (fun z => Goldilocks.sub z c) h
  have hCancel : ∀ x y : Goldilocks, Goldilocks.sub (Goldilocks.add x y) y = x := fun x y => by
    rw [← goldOfInt_nat x, ← goldOfInt_nat y]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1; omega
  rwa [hCancel, hCancel] at hs

private theorem lane6Add_left_cancel {a b c : Lane6}
    (h : lane6Add a b = lane6Add a c) : b = c :=
  Lane6.ext
    (gold_add_left_cancel_vc (congrArg Lane6.x0 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x1 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x2 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x3 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x4 h))
    (gold_add_left_cancel_vc (congrArg Lane6.x5 h))

/-- Equal output halves of a public permutation. This unrestricted relation
is not a hardness assumption; use `blindVcReachableBinding204` to retain sponge reachability. -/
def Poseidon2Perm12Sponge6Collision (stA stB : Poseidon2State12) : Prop :=
  stA ≠ stB ∧
  (state12Rate6 (poseidon2Perm12 stA) = state12Rate6 (poseidon2Perm12 stB) ∨
   state12Cap6 (poseidon2Perm12 stA) = state12Cap6 (poseidon2Perm12 stB))

/-- Constructive sponge collision reduction (`0 Classical.choice`):
    any two distinct 3-chunk sequences `(c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂)` colliding on
    `state12Rate6 (absorbRate6Sponge3 ...)` exhibit an explicit `Poseidon2Perm12Sponge6Collision`. -/
theorem absorbRate6Sponge3_collision_reduction
    {c0₁ c1₁ c2₁ c0₂ c1₂ c2₂ : Lane6}
    (hNe : (c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂))
    (hDig : state12Rate6 (absorbRate6Sponge3 c0₁ c1₁ c2₁) =
            state12Rate6 (absorbRate6Sponge3 c0₂ c1₂ c2₂)) :
    ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB := by
  let s1₁ := mkState12Of6 c0₁ lane6Zero
  let s1₂ := mkState12Of6 c0₂ lane6Zero
  let p1₁ := poseidon2Perm12 s1₁
  let p1₂ := poseidon2Perm12 s1₂
  let s2₁ := mkState12Of6 (lane6Add (state12Rate6 p1₁) c1₁) (state12Cap6 p1₁)
  let s2₂ := mkState12Of6 (lane6Add (state12Rate6 p1₂) c1₂) (state12Cap6 p1₂)
  let p2₁ := poseidon2Perm12 s2₁
  let p2₂ := poseidon2Perm12 s2₂
  let s3₁ := mkState12Of6 (lane6Add (state12Rate6 p2₁) c2₁) (state12Cap6 p2₁)
  let s3₂ := mkState12Of6 (lane6Add (state12Rate6 p2₂) c2₂) (state12Cap6 p2₂)
  if h3 : s3₁ = s3₂ then
    if h2 : s2₁ = s2₂ then
      have hp2 : p2₁ = p2₂ := congrArg poseidon2Perm12 h2
      have hRate3 : lane6Add (state12Rate6 p2₁) c2₁ = lane6Add (state12Rate6 p2₂) c2₂ := by
        have hr := congrArg state12Rate6 h3
        rwa [state12Rate6_mk, state12Rate6_mk] at hr
      rw [hp2] at hRate3
      have hc2 : c2₁ = c2₂ := lane6Add_left_cancel hRate3
      if h1 : s1₁ = s1₂ then
        have hp1 : p1₁ = p1₂ := congrArg poseidon2Perm12 h1
        have hRate2 : lane6Add (state12Rate6 p1₁) c1₁ = lane6Add (state12Rate6 p1₂) c1₂ := by
          have hr := congrArg state12Rate6 h2
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        rw [hp1] at hRate2
        have hc1 : c1₁ = c1₂ := lane6Add_left_cancel hRate2
        have hc0 : c0₁ = c0₂ := by
          have hr := congrArg state12Rate6 h1
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (by rw [hc0, hc1, hc2]))
      else
        have hCap1 : state12Cap6 p1₁ = state12Cap6 p1₂ := by
          have hc := congrArg state12Cap6 h2
          rwa [state12Cap6_mk, state12Cap6_mk] at hc
        exact ⟨s1₁, s1₂, h1, Or.inr hCap1⟩
    else
      have hCap2 : state12Cap6 p2₁ = state12Cap6 p2₂ := by
        have hc := congrArg state12Cap6 h3
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      exact ⟨s2₁, s2₂, h2, Or.inr hCap2⟩
  else
    exact ⟨s3₁, s3₂, h3, Or.inl hDig⟩

/-- Fixed-arity 3-block ZKBoo credential schema (`1 ≤ arity ≤ 6`; full `1 ≤ arity ≤ 32` is
    formalized by `computeVcPoseidon2CommitFull` below, matching `MAX_VC_ATTRS = 32` in `blind_vc.rs:43`). -/
structure VcSchema where
  schemaId : UInt64
  arity : Nat
  hArityPos : 1 ≤ arity
  hArityLe : arity ≤ vcSmallMaxAttrs
  deriving DecidableEq, Repr

theorem VcSchema.ext {s₁ s₂ : VcSchema}
    (hId : s₁.schemaId = s₂.schemaId) (hAr : s₁.arity = s₂.arity) : s₁ = s₂ := by
  cases s₁; cases s₂; dsimp only at hId hAr; subst hId hAr; rfl

/-- Low 32-bit limb `schema_id & 0xffff_ffff` (`blind_vc.rs:129, 155, 181`). -/
def vcSchemaLo (sid : UInt64) : Goldilocks :=
  Goldilocks.ofNat (sid.toNat % 4294967296)

/-- High 32-bit limb combined with reduced 64-bit domain tag (`blind_vc.rs:130, 156, 184`). -/
def vcSchemaHiWithTag (sid tag : UInt64) : Goldilocks :=
  Goldilocks.add (Goldilocks.ofNat (sid.toNat / 4294967296)) (Goldilocks.ofNat tag.toNat)

/-- Zero-extended slot lookup `attrs[idx]` (`blind_vc.rs:839-845`). -/
def vcAttrAt (attrs : List Goldilocks) (idx : Nat) : Goldilocks :=
  (attrs[idx]?).getD Goldilocks.zero

/-- 13-limb + `1` separator rate-6 chunking for `compute_vc_poseidon2_commit` (`blind_vc.rs:118-137`):
    explicitly absorbs `Goldilocks.ofNat schema.arity` in `c2.x0` followed by separator `1` in `c2.x1`! -/
def vcCommitChunks (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) :
    Lane6 × Lane6 × Lane6 :=
  (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
    vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
   ⟨blind.x0, blind.x1, blind.x2, blind.x3,
    vcSchemaLo schema.schemaId, vcSchemaHiWithTag schema.schemaId tag⟩,
   ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- Arity-framed 6-limb `BlindVC` commitment (`blind_vc.rs:112-138`):
    enforces `attrs.length = schema.arity` (`1 ≤ arity ≤ 6`), absorbs `schema.arity` into the
    3-permutation rate-6/capacity-6 sponge, and squeezes the 6-limb (`> 383`-bit) digest `Lane6`. -/
@[expose] def computeVcPoseidon2Commit
    (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) : Option Lane6 :=
  if attrs.length = schema.arity then
    let (c0, c1, c2) := vcCommitChunks schema attrs blind tag
    some (state12Rate6 (absorbRate6Sponge3 c0 c1 c2))
  else
    none

private theorem vcSchema_limbs_injective {sid₁ sid₂ tag : UInt64}
    (hLo : vcSchemaLo sid₁ = vcSchemaLo sid₂)
    (hHi : vcSchemaHiWithTag sid₁ tag = vcSchemaHiWithTag sid₂ tag) :
    sid₁ = sid₂ := by
  have hx := sid₁.toNat_lt_size
  have hy := sid₂.toNat_lt_size
  have hp : 4294967296 < goldilocksPrime := by decide
  have hPos : 0 < 4294967296 := by decide
  have hxl : sid₁.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₁.toNat hPos) hp
  have hyl : sid₂.toNat % 4294967296 < goldilocksPrime :=
    Nat.lt_trans (Nat.mod_lt sid₂.toNat hPos) hp
  have hdiv1 : sid₁.toNat / 4294967296 < 4294967296 := by
    change sid₁.toNat < 18446744073709551616 at hx
    omega
  have hdiv2 : sid₂.toNat / 4294967296 < 4294967296 := by
    change sid₂.toNat < 18446744073709551616 at hy
    omega
  have hxh : sid₁.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv1 hp
  have hyh : sid₂.toNat / 4294967296 < goldilocksPrime := Nat.lt_trans hdiv2 hp
  have hLoVal := congrArg Goldilocks.val hLo
  simp only [vcSchemaLo, Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyl] at hLoVal
  have hHiSub := gold_add_right_cancel_vc hHi
  have hHiVal := congrArg Goldilocks.val hHiSub
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hxh, Nat.mod_eq_of_lt hyh] at hHiVal
  apply UInt64.toNat_inj.mp
  omega

private theorem vcCommitChunks_injective
    {schema₁ schema₂ : VcSchema} {attrs₁ attrs₂ : List Goldilocks}
    {blind₁ blind₂ : Lane4} {tag : UInt64}
    (hLen₁ : attrs₁.length = schema₁.arity)
    (hLen₂ : attrs₂.length = schema₂.arity)
    (hEq : vcCommitChunks schema₁ attrs₁ blind₁ tag = vcCommitChunks schema₂ attrs₂ blind₂ tag) :
    schema₁ = schema₂ ∧ attrs₁ = attrs₂ ∧ blind₁ = blind₂ := by
  have hArVal := congrArg (fun p => p.2.2.x0.val) hEq
  dsimp only [vcCommitChunks] at hArVal
  have hp6 : 6 < goldilocksPrime := by decide
  have hArLt₁ : schema₁.arity < goldilocksPrime := by
    have hLe := schema₁.hArityLe
    unfold vcSmallMaxAttrs at hLe
    omega
  have hArLt₂ : schema₂.arity < goldilocksPrime := by
    have hLe := schema₂.hArityLe
    unfold vcSmallMaxAttrs at hLe
    omega
  simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hArLt₁, Nat.mod_eq_of_lt hArLt₂] at hArVal
  have hSid : schema₁.schemaId = schema₂.schemaId :=
    vcSchema_limbs_injective
      (congrArg (fun p => p.2.1.x4) hEq)
      (congrArg (fun p => p.2.1.x5) hEq)
  have hSchema : schema₁ = schema₂ := VcSchema.ext hSid hArVal
  have hBlind : blind₁ = blind₂ :=
    Lane4.ext
      (congrArg (fun p => p.2.1.x0) hEq)
      (congrArg (fun p => p.2.1.x1) hEq)
      (congrArg (fun p => p.2.1.x2) hEq)
      (congrArg (fun p => p.2.1.x3) hEq)
  have h0 : vcAttrAt attrs₁ 0 = vcAttrAt attrs₂ 0 := congrArg (fun p => p.1.x0) hEq
  have h1 : vcAttrAt attrs₁ 1 = vcAttrAt attrs₂ 1 := congrArg (fun p => p.1.x1) hEq
  have h2 : vcAttrAt attrs₁ 2 = vcAttrAt attrs₂ 2 := congrArg (fun p => p.1.x2) hEq
  have h3 : vcAttrAt attrs₁ 3 = vcAttrAt attrs₂ 3 := congrArg (fun p => p.1.x3) hEq
  have h4 : vcAttrAt attrs₁ 4 = vcAttrAt attrs₂ 4 := congrArg (fun p => p.1.x4) hEq
  have h5 : vcAttrAt attrs₁ 5 = vcAttrAt attrs₂ 5 := congrArg (fun p => p.1.x5) hEq
  have hLenEq : attrs₁.length = attrs₂.length := by omega
  have hAttrs : attrs₁ = attrs₂ := by
    apply List.ext_getElem hLenEq
    intro i hi1 hi2
    have hLe1 : attrs₁.length ≤ 6 := hLen₁ ▸ schema₁.hArityLe
    have hiMax : i < 6 := by omega
    have hGet1 : vcAttrAt attrs₁ i = attrs₁[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi1]; rfl
    have hGet2 : vcAttrAt attrs₂ i = attrs₂[i] := by
      unfold vcAttrAt; rw [List.getElem?_eq_getElem hi2]; rfl
    rw [← hGet1, ← hGet2]
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  exact ⟨hSchema, hAttrs, hBlind⟩

set_option exponentiation.threshold 1024 in
/-- **Flagship §4.1 Theorem — `BlindVC` 6-Limb Arity-Framed Sponge Commitment Binding
    (`blind_vc_commit_binding_reduces_to_sponge12_collision`)**:
    1. **Explicit Arity Framing**: `computeVcPoseidon2Commit` accepts iff `1 ≤ attrs.length = schema.arity ≤ 6`;
    2. **Same-Arity & Cross-Arity Binding Reduction**: ANY two distinct openings
       `(schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂)` (including cross-arity `[x]` vs `[x, 0]`)
       yielding `some c` constructively exhibit `Poseidon2Perm12Sponge6Collision stA stB`;
    3. **Cross-Domain Non-Confusion**: `vcAttrCommitTag` and `vcPresCommitTag` chunk tuples are disjoint;
    4. **Full 384-Bit Digest Space**: `2 ^ 383 < goldilocksPrime ^ 6`. -/
theorem blind_vc_commit_binding_reduces_to_sponge12_collision :
    (∀ (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema attrs blind tag = some c →
      1 ≤ attrs.length ∧ attrs.length = schema.arity ∧ attrs.length ≤ vcSmallMaxAttrs) ∧
    (∀ (schema₁ schema₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks)
       (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2Commit schema₁ attrs₁ blind₁ tag = some c →
      computeVcPoseidon2Commit schema₂ attrs₂ blind₂ tag = some c →
      (schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂) →
      ∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∧
    (∀ (s₁ s₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks) (blind₁ blind₂ : Lane4),
      s₁.schemaId = s₂.schemaId →
      vcCommitChunks s₁ attrs₁ blind₁ vcAttrCommitTag ≠
        vcCommitChunks s₂ attrs₂ blind₂ vcPresCommitTag) ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro schema attrs blind tag c hCom
    unfold computeVcPoseidon2Commit at hCom
    if hLen : attrs.length = schema.arity then
      exact ⟨hLen ▸ schema.hArityPos, hLen, hLen ▸ schema.hArityLe⟩
    else
      rw [ite_false_of hLen] at hCom; cases hCom
  · intro schema₁ schema₂ attrs₁ attrs₂ blind₁ blind₂ tag c hCom1 hCom2 hNe
    unfold computeVcPoseidon2Commit at hCom1 hCom2
    if hLen1 : attrs₁.length = schema₁.arity then
      rw [ite_true_of hLen1] at hCom1
      if hLen2 : attrs₂.length = schema₂.arity then
        rw [ite_true_of hLen2] at hCom2
        injection hCom1 with hc1
        injection hCom2 with hc2
        have hChunksNe : vcCommitChunks schema₁ attrs₁ blind₁ tag ≠ vcCommitChunks schema₂ attrs₂ blind₂ tag := by
          intro hEq
          obtain ⟨hs, ha, hb⟩ := vcCommitChunks_injective hLen1 hLen2 hEq
          exact hNe (by rw [hs, ha, hb])
        exact absorbRate6Sponge3_collision_reduction hChunksNe (hc1.trans hc2.symm)
      else
        rw [ite_false_of hLen2] at hCom2; cases hCom2
    else
      rw [ite_false_of hLen1] at hCom1; cases hCom1
  · intro s₁ s₂ attrs₁ attrs₂ blind₁ blind₂ hSid hEq
    have hHi := congrArg (fun p => p.2.1.x5) hEq
    dsimp only [vcCommitChunks] at hHi
    rw [hSid] at hHi
    have hTagEq := gold_add_left_cancel_vc hHi
    have hValEq := congrArg Goldilocks.val hTagEq
    have hNeVal : (Goldilocks.ofNat vcAttrCommitTag.toNat).val ≠
        (Goldilocks.ofNat vcPresCommitTag.toNat).val := by
      unfold vcAttrCommitTag vcPresCommitTag
      simp only [Goldilocks.ofNat_val]
      decide
    exact hNeVal hValEq

/-- **`#tooth` (`tooth_unframed_trailing_zero_collision`)**:
    Omitting `schema.arity` from chunk `c2` makes `(arity = 1, [x])` and `(arity = 2, [x, 0])`
    absorb **identical** sponge blocks (`rfl` — zero permutation collision needed!), whereas
    `vcCommitChunks` strictly separates `(s₁, [x])` from `(s₂, [x, 0])` and `computeVcPoseidon2Commit`
    deterministically rejects wrong-arity `[x, 0]` (`= none`)! -/
theorem tooth_unframed_trailing_zero_collision (sid : UInt64) (x : Goldilocks) (blind : Lane4) (tag : UInt64) :
    let s₁ : VcSchema := ⟨sid, 1, by decide, by decide⟩
    let s₂ : VcSchema := ⟨sid, 2, by decide, by decide⟩
    let unframedChunks (attrs : List Goldilocks) : Lane6 × Lane6 × Lane6 :=
      (⟨vcAttrAt attrs 0, vcAttrAt attrs 1, vcAttrAt attrs 2,
        vcAttrAt attrs 3, vcAttrAt attrs 4, vcAttrAt attrs 5⟩,
       ⟨blind.x0, blind.x1, blind.x2, blind.x3, vcSchemaLo sid, vcSchemaHiWithTag sid tag⟩,
       ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)
    [x] ≠ [x, Goldilocks.zero] ∧
    unframedChunks [x] = unframedChunks [x, Goldilocks.zero] ∧
    vcCommitChunks s₁ [x] blind tag ≠ vcCommitChunks s₂ [x, Goldilocks.zero] blind tag ∧
    computeVcPoseidon2Commit s₁ [x, Goldilocks.zero] blind tag = none := by
  refine ⟨(by intro h; injection h with _ hNil; cases hNil), rfl, ?_, rfl⟩
  intro hEq
  obtain ⟨hS, _, _⟩ := vcCommitChunks_injective rfl rfl hEq
  have hAr := congrArg VcSchema.arity hS
  cases hAr

/-! ### §4.2 6-Limb Scope Tag, Merkle Accumulator & Algebraic Boolean Gate Soundness -/

/-- 12-limb + `1` separator rate-6 chunks for `compute_vc_scope_tag` (`blind_vc.rs:145-169`). -/
def vcScopeChunks (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 × Lane6 × Lane6 :=
  (⟨holderBlind.x0, holderBlind.x1, holderBlind.x2, holderBlind.x3, scopeLimbs.x0, scopeLimbs.x1⟩,
   ⟨scopeLimbs.x2, scopeLimbs.x3, Goldilocks.zero, Goldilocks.zero,
    vcSchemaLo sid, vcSchemaHiWithTag sid vcScopeTagDom⟩,
   ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
    Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩)

/-- 6-limb scope-bound pseudonym/nullifier `compute_vc_scope_tag` (`blind_vc.rs:145-170`). -/
def computeVcScopeTag (sid : UInt64) (holderBlind scopeLimbs : Lane4) : Lane6 :=
  let (c0, c1, c2) := vcScopeChunks sid holderBlind scopeLimbs
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- 16-limb + `1` separator rate-6 chunks for `merkle_hash_pair` (`blind_vc.rs:175-199`). -/
def vcMerkleChunks (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 × Lane6 × Lane6 :=
  (left,
   right,
   ⟨vcSchemaLo epoch, Goldilocks.ofNat layer,
    Goldilocks.ofNat vcMerkleNodeTag.toNat, vcSchemaHiWithTag epoch poseidon2ConstIV,
    Goldilocks.one, Goldilocks.zero⟩)

/-- Domain-separated 6-limb Merkle parent hash `merkle_hash_pair` (`blind_vc.rs:175-200`). -/
def vcMerkleHashPair (left right : Lane6) (epoch : UInt64) (layer : Nat) : Lane6 :=
  let (c0, c1, c2) := vcMerkleChunks left right epoch layer
  state12Rate6 (absorbRate6Sponge3 c0 c1 c2)

/-- Arithmetic 6-limb Merkle branch selector (`blind_vc.rs:2000-2035`):
    `delta = b * (sib - cur)`, `left = cur + delta`, `right = sib - delta`. -/
def vcMerkleStepArith (epoch : UInt64) (layer : Nat) (cur sib : Lane6) (b : Goldilocks) : Lane6 :=
  let delta := lane6Scale b (lane6Sub sib cur)
  let left := lane6Add cur delta
  let right := lane6Sub sib delta
  vcMerkleHashPair left right epoch layer

@[expose] def evalVcMerklePathFrom (epoch : UInt64) : Nat → Lane6 → List (Goldilocks × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (b, sib) :: rest =>
    evalVcMerklePathFrom epoch (layer + 1) (vcMerkleStepArith epoch layer cur sib b) rest

/-- Boolean 6-limb Merkle path specification (`false` => `cur` is left child, `true` => `cur` is right child). -/
def evalVcMerklePathBool (epoch : UInt64) : Nat → Lane6 → List (Bool × Lane6) → Lane6
  | _, cur, [] => cur
  | layer, cur, (false, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest
  | layer, cur, (true, sib) :: rest =>
    evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest

/-- Over prime field `Goldilocks`, `b * (1 - b) = 0` holds iff `b = 0 ∨ b = 1` (`blind_vc.rs:1994-1996`). -/
theorem goldilocks_bool_gate_zero_or_one (b : Goldilocks)
    (hZero : Goldilocks.mul b (Goldilocks.sub Goldilocks.one b) = Goldilocks.zero) :
    b = Goldilocks.zero ∨ b = Goldilocks.one := by
  have hVal := congrArg Goldilocks.val hZero
  rw [Goldilocks.mul_val, Goldilocks.zero_val] at hVal
  have hDvd : goldilocksPrime ∣ b.val * (Goldilocks.sub Goldilocks.one b).val :=
    Nat.dvd_of_mod_eq_zero hVal
  if hb0 : b.val = 0 then
    exact Or.inl (Goldilocks.ext hb0)
  else
    right
    have hbLt := b.isLt
    have hNotDvdB : ¬ (goldilocksPrime ∣ b.val) := by
      intro hd
      have hle := Nat.le_of_dvd (by omega) hd
      omega
    have hDvdSub : goldilocksPrime ∣ (Goldilocks.sub Goldilocks.one b).val :=
      (goldilocksPrime_isPrime ()).dvd_mul hDvd hNotDvdB
    have hSubLt := (Goldilocks.sub Goldilocks.one b).isLt
    have hSubVal0 : (Goldilocks.sub Goldilocks.one b).val = 0 := by
      if hs0 : (Goldilocks.sub Goldilocks.one b).val = 0 then exact hs0
      else
        have hle := Nat.le_of_dvd (by omega) hDvdSub
        omega
    have hSubEq0 : Goldilocks.sub Goldilocks.one b = Goldilocks.zero := Goldilocks.ext hSubVal0
    have hAdd := congrArg (fun z => Goldilocks.add z b) hSubEq0
    have hLhs : Goldilocks.add (Goldilocks.sub Goldilocks.one b) b = Goldilocks.one := by
      rw [← goldOfInt_nat Goldilocks.one, ← goldOfInt_nat b]
      simp only [goldOfInt_sub, goldOfInt_add]; congr 1; omega
    have hRhs : Goldilocks.add Goldilocks.zero b = b := by
      rw [← goldOfInt_nat Goldilocks.zero, ← goldOfInt_nat b]
      simp only [Goldilocks.zero_val, goldOfInt_add]; congr 1; omega
    rw [hLhs, hRhs] at hAdd
    exact hAdd.symm

theorem vcMerkleStepArith_zero (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.zero = vcMerkleHashPair cur sib epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; simp
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.zero (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.zero]
    simp only [Goldilocks.zero_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; simp
  simp only [hL, hR]

theorem vcMerkleStepArith_one (epoch : UInt64) (layer : Nat) (cur sib : Lane6) :
    vcMerkleStepArith epoch layer cur sib Goldilocks.one = vcMerkleHashPair sib cur epoch layer := by
  unfold vcMerkleStepArith lane6Scale lane6Sub lane6Add
  dsimp only
  have hL : ∀ c s : Goldilocks, Goldilocks.add c (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = s := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul, goldOfInt_add]
    congr 1; omega
  have hR : ∀ c s : Goldilocks, Goldilocks.sub s (Goldilocks.mul Goldilocks.one (Goldilocks.sub s c)) = c := by
    intro c s
    rw [← goldOfInt_nat c, ← goldOfInt_nat s, ← goldOfInt_nat Goldilocks.one]
    simp only [Goldilocks.one_val, goldOfInt_sub, goldOfInt_mul]
    congr 1; omega
  simp only [hL, hR]

theorem evalVcMerklePathFrom_eq_bool (epoch : UInt64) :
    ∀ (layer : Nat) (cur : Lane6) (steps : List (Goldilocks × Lane6)),
      (∀ p ∈ steps, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one) →
      ∃ boolSteps : List (Bool × Lane6),
        boolSteps.length = steps.length ∧
        evalVcMerklePathFrom epoch layer cur steps =
          evalVcMerklePathBool epoch layer cur boolSteps
  | _, cur, [], _ => ⟨[], rfl, rfl⟩
  | layer, cur, (b, sib) :: rest, hAll => by
    have hb := hAll (b, sib) (.head rest)
    have hRest : ∀ p ∈ rest, p.1 = Goldilocks.zero ∨ p.1 = Goldilocks.one :=
      fun p hp => hAll p (.tail _ hp)
    rcases hb with rfl | rfl
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest hRest
      refine ⟨(false, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_zero, hEq]
    · obtain ⟨bs, hLen, hEq⟩ :=
        evalVcMerklePathFrom_eq_bool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest hRest
      refine ⟨(true, sib) :: bs, by simp [hLen], ?_⟩
      dsimp only [evalVcMerklePathFrom, evalVcMerklePathBool]
      rw [vcMerkleStepArith_one, hEq]

/-- Actual permutation inputs on the three-chunk, zero-capacity sponge path. -/
def spongeTrace204 (chunks : Lane6 × Lane6 × Lane6) (r : Fin 3) : Poseidon2State12 :=
  let s1 := mkState12Of6 chunks.1 lane6Zero
  let p1 := poseidon2Perm12 s1
  let s2 := mkState12Of6 (lane6Add (state12Rate6 p1) chunks.2.1) (state12Cap6 p1)
  let p2 := poseidon2Perm12 s2
  let s3 := mkState12Of6 (lane6Add (state12Rate6 p2) chunks.2.2) (state12Cap6 p2)
  match r.val with | 0 => s1 | 1 => s2 | _ => s3

/-- Collision extraction retaining reachability from the supplied sponge
messages. Unrestricted rate/capacity collisions are not assumed hard. -/
def absorbRate6Sponge3_reachable_collision204
    {c0₁ c1₁ c2₁ c0₂ c1₂ c2₂ : Lane6}
    (hNe : (c0₁, c1₁, c2₁) ≠ (c0₂, c1₂, c2₂))
    (hDig : state12Rate6 (absorbRate6Sponge3 c0₁ c1₁ c2₁) =
            state12Rate6 (absorbRate6Sponge3 c0₂ c1₂ c2₂)) :
    { r : Fin 3 // Poseidon2Perm12Sponge6Collision
      (spongeTrace204 (c0₁, c1₁, c2₁) r) (spongeTrace204 (c0₂, c1₂, c2₂) r) } := by
  let s1₁ := mkState12Of6 c0₁ lane6Zero
  let s1₂ := mkState12Of6 c0₂ lane6Zero
  let p1₁ := poseidon2Perm12 s1₁
  let p1₂ := poseidon2Perm12 s1₂
  let s2₁ := mkState12Of6 (lane6Add (state12Rate6 p1₁) c1₁) (state12Cap6 p1₁)
  let s2₂ := mkState12Of6 (lane6Add (state12Rate6 p1₂) c1₂) (state12Cap6 p1₂)
  let p2₁ := poseidon2Perm12 s2₁
  let p2₂ := poseidon2Perm12 s2₂
  let s3₁ := mkState12Of6 (lane6Add (state12Rate6 p2₁) c2₁) (state12Cap6 p2₁)
  let s3₂ := mkState12Of6 (lane6Add (state12Rate6 p2₂) c2₂) (state12Cap6 p2₂)
  if h3 : s3₁ = s3₂ then
    if h2 : s2₁ = s2₂ then
      have hp2 : p2₁ = p2₂ := congrArg poseidon2Perm12 h2
      have hRate3 : lane6Add (state12Rate6 p2₁) c2₁ = lane6Add (state12Rate6 p2₂) c2₂ := by
        have hr := congrArg state12Rate6 h3
        rwa [state12Rate6_mk, state12Rate6_mk] at hr
      rw [hp2] at hRate3
      have hc2 : c2₁ = c2₂ := lane6Add_left_cancel hRate3
      if h1 : s1₁ = s1₂ then
        have hp1 : p1₁ = p1₂ := congrArg poseidon2Perm12 h1
        have hRate2 : lane6Add (state12Rate6 p1₁) c1₁ = lane6Add (state12Rate6 p1₂) c1₂ := by
          have hr := congrArg state12Rate6 h2
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        rw [hp1] at hRate2
        have hc1 : c1₁ = c1₂ := lane6Add_left_cancel hRate2
        have hc0 : c0₁ = c0₂ := by
          have hr := congrArg state12Rate6 h1
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (by rw [hc0, hc1, hc2]))
      else
        have hCap1 : state12Cap6 p1₁ = state12Cap6 p1₂ := by
          have hc := congrArg state12Cap6 h2
          rwa [state12Cap6_mk, state12Cap6_mk] at hc
        refine ⟨⟨0, by decide⟩, ?_⟩
        simpa only [spongeTrace204] using
          (show Poseidon2Perm12Sponge6Collision s1₁ s1₂ from ⟨h1, Or.inr hCap1⟩)
    else
      have hCap2 : state12Cap6 p2₁ = state12Cap6 p2₂ := by
        have hc := congrArg state12Cap6 h3
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      refine ⟨⟨1, by decide⟩, ?_⟩
      simpa only [spongeTrace204] using
        (show Poseidon2Perm12Sponge6Collision s2₁ s2₂ from ⟨h2, Or.inr hCap2⟩)
  else
    refine ⟨⟨2, by decide⟩, ?_⟩
    simpa only [spongeTrace204] using
      (show Poseidon2Perm12Sponge6Collision s3₁ s3₂ from ⟨h3, Or.inl hDig⟩)


/-- Binding failure reduces to two reachable states on the paths of the actual
well-formed credential openings. This is a reduction, not an assertion of
collision resistance for arbitrary halves of a public permutation. -/
def blindVcReachableBinding204
    (schema₁ schema₂ : VcSchema) (attrs₁ attrs₂ : List Goldilocks)
    (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6)
    (h1 : computeVcPoseidon2Commit schema₁ attrs₁ blind₁ tag = some c)
    (h2 : computeVcPoseidon2Commit schema₂ attrs₂ blind₂ tag = some c)
    (hne : (schema₁, attrs₁, blind₁) ≠ (schema₂, attrs₂, blind₂)) :
    { r : Fin 3 // Poseidon2Perm12Sponge6Collision
      (spongeTrace204 (vcCommitChunks schema₁ attrs₁ blind₁ tag) r)
      (spongeTrace204 (vcCommitChunks schema₂ attrs₂ blind₂ tag) r) } := by
  have hl1 := (blind_vc_commit_binding_reduces_to_sponge12_collision.1
    schema₁ attrs₁ blind₁ tag c h1).2.1
  have hl2 := (blind_vc_commit_binding_reduces_to_sponge12_collision.1
    schema₂ attrs₂ blind₂ tag c h2).2.1
  apply absorbRate6Sponge3_reachable_collision204
  · intro he
    obtain ⟨hs, ha, hb⟩ := vcCommitChunks_injective hl1 hl2 he
    exact hne (by rw [hs, ha, hb])
  · unfold computeVcPoseidon2Commit at h1 h2
    rw [ite_true_of hl1] at h1
    rw [ite_true_of hl2] at h2
    exact (Option.some.inj h1).trans (Option.some.inj h2).symm

theorem evalVcMerklePathBool_nil (epoch : UInt64) (layer : Nat) (cur : Lane6) :
    evalVcMerklePathBool epoch layer cur [] = cur := by rfl

theorem evalVcMerklePathBool_cons_false (epoch : UInt64) (layer : Nat) (cur sib : Lane6)
    (rest : List (Bool × Lane6)) :
    evalVcMerklePathBool epoch layer cur ((false, sib) :: rest) =
      evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair cur sib epoch layer) rest := by rfl

theorem evalVcMerklePathBool_cons_true (epoch : UInt64) (layer : Nat) (cur sib : Lane6)
    (rest : List (Bool × Lane6)) :
    evalVcMerklePathBool epoch layer cur ((true, sib) :: rest) =
      evalVcMerklePathBool epoch (layer + 1) (vcMerkleHashPair sib cur epoch layer) rest := by rfl

theorem vcMerkleHashPair_eq (left right : Lane6) (epoch : UInt64) (layer : Nat) :
    vcMerkleHashPair left right epoch layer =
      state12Rate6 (absorbRate6Sponge3 (vcMerkleChunks left right epoch layer).1
        (vcMerkleChunks left right epoch layer).2.1 (vcMerkleChunks left right epoch layer).2.2) := by
  rfl

/-- The two children are the first two rate chunks of a Merkle node preimage. -/
theorem vcMerkleChunks_children_inj {l r l' r' : Lane6} {epoch : UInt64} {layer : Nat}
    (h : vcMerkleChunks l r epoch layer = vcMerkleChunks l' r' epoch layer) : l = l' ∧ r = r' :=
  ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h⟩

set_option exponentiation.threshold 1024 in
/-- **Rate-6 / Capacity-6 Width-12 `sponge12` 6-Limb Coherence (`blindVc_sponge12_rate6_cap6_six_limb_coherence`)**:
    Locks `BlindVcCollisionFinder` directly to `crates/qsag-cred/src/blind_vc.rs:43, 137-268`:
    1. `vcMaxAttrs = 32` (`MAX_VC_ATTRS = 32`); on the 3-block ZKBoo circuit (`schema : VcSchema`,
       `1 ≤ schema.arity ≤ 6`), `computeVcPoseidon2Commit` accepts iff `attrs.length = schema.arity`,
       absorbs `schema.arity` at `c2.x0` and `10*` pad `1` at `c2.x1` into `absorbRate6Sponge3`
       (with 6 zero-initialized capacity lanes), and squeezes 6 limbs (`Lane6`, `> 2^383` states);
    2. `computeVcScopeTag` absorbs two 6-limb blocks plus the full-block `10*` pad `⟨1, 0, 0, 0, 0, 0⟩`
       (`N = 12` multiple of rate `6`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`);
    3. `vcMerkleHashPair` absorbs left/right 6-limb child digests plus 4 domain limbs and `10*` pad `1`
       at `c2.x4` (`N = 16`) into `absorbRate6Sponge3` and squeezes 6 limbs (`Lane6`). -/
theorem blindVc_sponge12_rate6_cap6_six_limb_coherence
    (schema : VcSchema) (attrs : List Goldilocks) (blind scopeLimbs : Lane4)
    (tag epoch : UInt64) (left right : Lane6) (layer : Nat) :
    ((attrs.length = schema.arity →
        (vcCommitChunks schema attrs blind tag).2.2 =
          ⟨Goldilocks.ofNat schema.arity, Goldilocks.one,
           Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
        computeVcPoseidon2Commit schema attrs blind tag =
          some (state12Rate6 (absorbRate6Sponge3
            (vcCommitChunks schema attrs blind tag).1
            (vcCommitChunks schema attrs blind tag).2.1
            (vcCommitChunks schema attrs blind tag).2.2))) ∧
     (attrs.length ≠ schema.arity → computeVcPoseidon2Commit schema attrs blind tag = none)) ∧
    ((vcScopeChunks schema.schemaId blind scopeLimbs).2.2 =
        ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero,
         Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩ ∧
     computeVcScopeTag schema.schemaId blind scopeLimbs =
        state12Rate6 (absorbRate6Sponge3
          (vcScopeChunks schema.schemaId blind scopeLimbs).1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.1
          (vcScopeChunks schema.schemaId blind scopeLimbs).2.2)) ∧
    ((vcMerkleChunks left right epoch layer).2.2.x4 = Goldilocks.one ∧
     (vcMerkleChunks left right epoch layer).2.2.x5 = Goldilocks.zero ∧
     vcMerkleHashPair left right epoch layer =
        state12Rate6 (absorbRate6Sponge3 left right
          (vcMerkleChunks left right epoch layer).2.2)) ∧
    state12Cap6 (mkState12Of6 (vcCommitChunks schema attrs blind tag).1 lane6Zero) = lane6Zero ∧
    2 ^ 383 < goldilocksPrime ^ 6 := by
  refine ⟨⟨fun hEq => ⟨rfl, ?_⟩, fun hNe => ?_⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, rfl, by decide⟩
  · unfold computeVcPoseidon2Commit; simp only [hEq, ↓reduceIte]
  · unfold computeVcPoseidon2Commit; simp only [hNe, ↓reduceIte]

/-! ## Multi-Block `MAX_VC_ATTRS = 32` `sponge12` Commitment & `"QSAG.MLDSA.NONCE_BURN.V2"` Parity -/

/-- Structural 6-limb rate-block chunker for `sponge12` (`blind_vc.rs:137-154`). -/
def limbsToLane6Blocks : List Goldilocks → List Lane6
  | [] => []
  | [x0] => [⟨x0, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1] => [⟨x0, x1, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2] => [⟨x0, x1, x2, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2, x3] => [⟨x0, x1, x2, x3, Goldilocks.zero, Goldilocks.zero⟩]
  | [x0, x1, x2, x3, x4] => [⟨x0, x1, x2, x3, x4, Goldilocks.zero⟩]
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest =>
    ⟨x0, x1, x2, x3, x4, x5⟩ :: limbsToLane6Blocks rest

private def stripLastLane6 : Lane6 → List Goldilocks
  | ⟨x0, x1, x2, x3, x4, x5⟩ =>
    if x5 ≠ Goldilocks.zero then [x0, x1, x2, x3, x4]
    else if x4 ≠ Goldilocks.zero then [x0, x1, x2, x3]
    else if x3 ≠ Goldilocks.zero then [x0, x1, x2]
    else if x2 ≠ Goldilocks.zero then [x0, x1]
    else if x1 ≠ Goldilocks.zero then [x0]
    else []

private def decodePad1Blocks : List Lane6 → List Goldilocks
  | [] => []
  | [last] => stripLastLane6 last
  | c :: b :: rest => [c.x0, c.x1, c.x2, c.x3, c.x4, c.x5] ++ decodePad1Blocks (b :: rest)

private theorem limbsToLane6Blocks_pad1_nonempty :
    ∀ xs : List Goldilocks, limbsToLane6Blocks (xs ++ [Goldilocks.one]) ≠ []
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] => by simp [limbsToLane6Blocks]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => by simp [limbsToLane6Blocks]

private theorem decodePad1Blocks_limbsToLane6Blocks :
    ∀ xs : List Goldilocks, decodePad1Blocks (limbsToLane6Blocks (xs ++ [Goldilocks.one])) = xs
  | [] => by decide
  | [x0] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2, x3] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | [x0, x1, x2, x3, x4] => by
    have h1 : Goldilocks.one ≠ Goldilocks.zero := by decide
    simp [limbsToLane6Blocks, decodePad1Blocks, stripLastLane6, h1]
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: rest => by
    have hNe := limbsToLane6Blocks_pad1_nonempty rest
    have ih := decodePad1Blocks_limbsToLane6Blocks rest
    simp only [List.cons_append, limbsToLane6Blocks]
    cases hBlk : limbsToLane6Blocks (rest ++ [Goldilocks.one]) with
    | nil => exact absurd hBlk hNe
    | cons b bs =>
      rw [hBlk] at ih
      simp only [decodePad1Blocks, ih]
      rfl

theorem limbsToLane6Blocks_pad1_injective {xs ys : List Goldilocks}
    (hEq : limbsToLane6Blocks (xs ++ [Goldilocks.one]) = limbsToLane6Blocks (ys ++ [Goldilocks.one])) :
    xs = ys := by
  have hDec := congrArg decodePad1Blocks hEq
  rwa [decodePad1Blocks_limbsToLane6Blocks, decodePad1Blocks_limbsToLane6Blocks] at hDec

/-- Multi-block Width-12 (`rate = 6, capacity = 6`) `sponge12` absorption from state `st`. -/
def sponge12AbsorbFrom (st : Poseidon2State12) : List Lane6 → Poseidon2State12
  | [] => st
  | c :: cs =>
    let stNext := poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 st) c) (state12Cap6 st))
    sponge12AbsorbFrom stNext cs

/-- Multi-block `sponge12` starting from the all-zero 12-limb state (`blind_vc.rs:137-154`). -/
def absorbRate6SpongeBlocks (blocks : List Lane6) : Poseidon2State12 :=
  sponge12AbsorbFrom (mkState12Of6 lane6Zero lane6Zero) blocks

private def sponge12Rev : List Lane6 → Poseidon2State12
  | [] => mkState12Of6 lane6Zero lane6Zero
  | c :: prevRev =>
    let prev := sponge12Rev prevRev
    poseidon2Perm12 (mkState12Of6 (lane6Add (state12Rate6 prev) c) (state12Cap6 prev))

private theorem sponge12AbsorbFrom_append (st : Poseidon2State12) :
    ∀ (as bs : List Lane6),
      sponge12AbsorbFrom st (as ++ bs) = sponge12AbsorbFrom (sponge12AbsorbFrom st as) bs
  | [], _ => rfl
  | _ :: as, bs => sponge12AbsorbFrom_append _ as bs

private theorem absorbRate6SpongeBlocks_eq_rev :
    ∀ bs : List Lane6, absorbRate6SpongeBlocks bs = sponge12Rev bs.reverse
  | [] => rfl
  | c :: cs => by
    unfold absorbRate6SpongeBlocks at *
    have hRev : (c :: cs).reverse = cs.reverse ++ [c] := List.reverse_cons
    rw [hRev]
    have hInd : ∀ r : List Lane6,
        sponge12Rev r = sponge12AbsorbFrom (mkState12Of6 lane6Zero lane6Zero) r.reverse := by
      intro r
      induction r with
      | nil => rfl
      | cons d ds ih =>
        simp only [List.reverse_cons, sponge12AbsorbFrom_append, ← ih]
        rfl
    rw [hInd (cs.reverse ++ [c]), List.reverse_append, List.reverse_singleton,
        List.reverse_reverse, List.singleton_append]

private theorem lane6Add_zero_left (c : Lane6) : lane6Add lane6Zero c = c := by
  have hz : ∀ x : Goldilocks, Goldilocks.zero.add x = x := fun x => LawfulCommRing.zero_add x
  rcases c with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [lane6Add, lane6Zero, hz]

theorem absorbRate6SpongeBlocks_three_eq (c0 c1 c2 : Lane6) :
    absorbRate6SpongeBlocks [c0, c1, c2] = absorbRate6Sponge3 c0 c1 c2 := by
  dsimp only [absorbRate6SpongeBlocks, sponge12AbsorbFrom, absorbRate6Sponge3]
  rw [state12Rate6_mk, state12Cap6_mk, lane6Add_zero_left]

/-- Non-initial sponge permutation input whose output capacity vanishes (`6` Goldilocks zeros, `< 2^-383`). -/
def Poseidon2Perm12ZeroCapRoot (st : Poseidon2State12) : Prop :=
  state12Cap6 (poseidon2Perm12 st) = lane6Zero

private theorem sponge12Rev_cap_collision_or_zero_root :
    ∀ {r₁ r₂ : List Lane6},
      r₁ ≠ r₂ →
      state12Cap6 (sponge12Rev r₁) = state12Cap6 (sponge12Rev r₂) →
      (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
      (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st)
  | [], [], hNe, _ => False.elim (hNe rfl)
  | [], c₂ :: t₂, _, hCap => by
    dsimp only [sponge12Rev, state12Cap6_mk] at hCap
    exact Or.inr ⟨_, hCap.symm⟩
  | c₁ :: t₁, [], _, hCap => by
    dsimp only [sponge12Rev, state12Cap6_mk] at hCap
    exact Or.inr ⟨_, hCap⟩
  | c₁ :: t₁, c₂ :: t₂, hNe, hCap => by
    let p₁ := sponge12Rev t₁
    let p₂ := sponge12Rev t₂
    let s₁ := mkState12Of6 (lane6Add (state12Rate6 p₁) c₁) (state12Cap6 p₁)
    let s₂ := mkState12Of6 (lane6Add (state12Rate6 p₂) c₂) (state12Cap6 p₂)
    if hs : s₁ = s₂ then
      have hCapPrev : state12Cap6 p₁ = state12Cap6 p₂ := by
        have hc := congrArg state12Cap6 hs
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      if ht : t₁ = t₂ then
        subst ht
        have hRate : lane6Add (state12Rate6 p₁) c₁ = lane6Add (state12Rate6 p₁) c₂ := by
          have hr := congrArg state12Rate6 hs
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hNe (congrArg (· :: t₁) (lane6Add_left_cancel hRate)))
      else
        exact sponge12Rev_cap_collision_or_zero_root ht hCapPrev
    else
      exact Or.inl ⟨s₁, s₂, hs, Or.inr hCap⟩

theorem absorbRate6SpongeBlocks_collision_reduction {bs₁ bs₂ : List Lane6}
    (hNe₁ : bs₁ ≠ []) (hNe₂ : bs₂ ≠ []) (hDiff : bs₁ ≠ bs₂)
    (hDig : state12Rate6 (absorbRate6SpongeBlocks bs₁) =
            state12Rate6 (absorbRate6SpongeBlocks bs₂)) :
    (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
    (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st) := by
  rw [absorbRate6SpongeBlocks_eq_rev, absorbRate6SpongeBlocks_eq_rev] at hDig
  have hrNe₁ : bs₁.reverse ≠ [] := fun h => hNe₁ (by simpa using congrArg List.reverse h)
  have hrNe₂ : bs₂.reverse ≠ [] := fun h => hNe₂ (by simpa using congrArg List.reverse h)
  have hrDiff : bs₁.reverse ≠ bs₂.reverse :=
    fun h => hDiff (by simpa using congrArg List.reverse h)
  match hR1 : bs₁.reverse, hR2 : bs₂.reverse with
  | [], _ => exact False.elim (hrNe₁ hR1)
  | _, [] => exact False.elim (hrNe₂ hR2)
  | c₁ :: t₁, c₂ :: t₂ =>
    rw [hR1, hR2] at hDig hrDiff
    let p₁ := sponge12Rev t₁
    let p₂ := sponge12Rev t₂
    let s₁ := mkState12Of6 (lane6Add (state12Rate6 p₁) c₁) (state12Cap6 p₁)
    let s₂ := mkState12Of6 (lane6Add (state12Rate6 p₂) c₂) (state12Cap6 p₂)
    if hs : s₁ = s₂ then
      have hCapPrev : state12Cap6 p₁ = state12Cap6 p₂ := by
        have hc := congrArg state12Cap6 hs
        rwa [state12Cap6_mk, state12Cap6_mk] at hc
      if ht : t₁ = t₂ then
        subst ht
        have hRate : lane6Add (state12Rate6 p₁) c₁ = lane6Add (state12Rate6 p₁) c₂ := by
          have hr := congrArg state12Rate6 hs
          rwa [state12Rate6_mk, state12Rate6_mk] at hr
        exact False.elim (hrDiff (congrArg (· :: t₁) (lane6Add_left_cancel hRate)))
      else
        exact sponge12Rev_cap_collision_or_zero_root ht hCapPrev
    else
      exact Or.inl ⟨s₁, s₂, hs, Or.inl hDig⟩

/-- Zero-pad attribute limbs to `max attrs.length 6` slots (`padded[..attrs.len.max(6)]`, `blind_vc.rs:178-179`). -/
def vcPadAttrs (attrs : List Goldilocks) : List Goldilocks :=
  attrs ++ List.replicate (6 - attrs.length) Goldilocks.zero

/-- 7-limb metadata & blind trailer `[blind[0..4], schema_lo, schema_hi + tag, arity]` (`blind_vc.rs:180-185`). -/
def vcCommitTrailerLimbs (schemaId : UInt64) (arity : Nat) (blind : Lane4) (tag : UInt64) :
    List Goldilocks :=
  [blind.x0, blind.x1, blind.x2, blind.x3,
   vcSchemaLo schemaId, vcSchemaHiWithTag schemaId tag, Goldilocks.ofNat arity]

/-- Rate-6 `Lane6` block sequence absorbed by `compute_vc_poseidon2_commit` (`blind_vc.rs:159-190`). -/
def vcCommitFullBlocks (schemaId : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) :
    List Lane6 :=
  limbsToLane6Blocks
    (vcPadAttrs attrs ++ vcCommitTrailerLimbs schemaId attrs.length blind tag ++ [Goldilocks.one])

/-- **Full `MAX_VC_ATTRS = 32` `Poseidon2` Credential Commitment (`computeVcPoseidon2CommitFull`)**:
    Matches `blind_vc.rs:159-190`: accepts iff `1 ≤ attrs.length ≤ vcMaxAttrs` (`= 32`), pads small
    attribute vectors to 6 slots while absorbing all `7..32` attributes into rate-6 / capacity-6
    `absorbRate6SpongeBlocks`, and squeezes the 6-limb digest `Lane6`. -/
def computeVcPoseidon2CommitFull
    (schemaId : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64) : Option Lane6 :=
  if decide (1 ≤ attrs.length ∧ attrs.length ≤ vcMaxAttrs) then
    some (state12Rate6 (absorbRate6SpongeBlocks (vcCommitFullBlocks schemaId attrs blind tag)))
  else
    none

/-- Exact equivalence between `computeVcPoseidon2CommitFull` (`1 ≤ arity ≤ 32`) and the 3-block
    ZKBoo `computeVcPoseidon2Commit` whenever `schema : VcSchema` (`1 ≤ schema.arity ≤ 6`) and
    `attrs.length = schema.arity`. -/
theorem computeVcPoseidon2CommitFull_eq_small
    (schema : VcSchema) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64)
    (hLen : attrs.length = schema.arity) :
    computeVcPoseidon2CommitFull schema.schemaId attrs blind tag =
      computeVcPoseidon2Commit schema attrs blind tag := by
  have hPos : 1 ≤ attrs.length := hLen ▸ schema.hArityPos
  have hLe6 : attrs.length ≤ 6 := hLen ▸ schema.hArityLe
  have hLe32 : attrs.length ≤ vcMaxAttrs := Nat.le_trans hLe6 (by decide)
  have hRange : decide (1 ≤ attrs.length ∧ attrs.length ≤ vcMaxAttrs) = true :=
    decide_eq_true ⟨hPos, hLe32⟩
  unfold computeVcPoseidon2CommitFull computeVcPoseidon2Commit
  rw [hRange]
  simp only [hLen, ↓reduceIte]
  congr 1
  have hBlks : vcCommitFullBlocks schema.schemaId attrs blind tag =
      [(vcCommitChunks schema attrs blind tag).1,
       (vcCommitChunks schema attrs blind tag).2.1,
       (vcCommitChunks schema attrs blind tag).2.2] := by
    unfold vcCommitFullBlocks vcPadAttrs vcCommitTrailerLimbs vcCommitChunks
    rw [← hLen]
    match attrs, hPos, hLe6 with
    | [a0], _, _ => rfl
    | [a0, a1], _, _ => rfl
    | [a0, a1, a2], _, _ => rfl
    | [a0, a1, a2, a3], _, _ => rfl
    | [a0, a1, a2, a3, a4], _, _ => rfl
    | [a0, a1, a2, a3, a4, a5], _, _ => rfl
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, h6 => simp at h6
  rw [hBlks, absorbRate6SpongeBlocks_three_eq]

private theorem vcCommitFullBlocks_injective
    {sid₁ sid₂ : UInt64} {attrs₁ attrs₂ : List Goldilocks} {blind₁ blind₂ : Lane4} {tag : UInt64}
    (hLe₁ : attrs₁.length ≤ vcMaxAttrs) (hLe₂ : attrs₂.length ≤ vcMaxAttrs)
    (hEq : vcCommitFullBlocks sid₁ attrs₁ blind₁ tag = vcCommitFullBlocks sid₂ attrs₂ blind₂ tag) :
    sid₁ = sid₂ ∧ attrs₁ = attrs₂ ∧ blind₁ = blind₂ := by
  unfold vcCommitFullBlocks at hEq
  have hMsgEq := limbsToLane6Blocks_pad1_injective hEq
  have hRevEq := congrArg List.reverse hMsgEq
  simp only [vcCommitTrailerLimbs, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hRevEq
  injection hRevEq with hAr t1
  injection t1 with hHi t2
  injection t2 with hLo t3
  injection t3 with hb3 t4
  injection t4 with hb2 t5
  injection t5 with hb1 t6
  injection t6 with hb0 hPadRevEq
  have hp32 : vcMaxAttrs < goldilocksPrime := by decide
  have hLt₁ : attrs₁.length < goldilocksPrime := Nat.lt_of_le_of_lt hLe₁ hp32
  have hLt₂ : attrs₂.length < goldilocksPrime := Nat.lt_of_le_of_lt hLe₂ hp32
  have hLenEq : attrs₁.length = attrs₂.length := by
    have hv := congrArg Goldilocks.val hAr
    simp only [Goldilocks.ofNat_val, Nat.mod_eq_of_lt hLt₁, Nat.mod_eq_of_lt hLt₂] at hv
    exact hv
  have hSid : sid₁ = sid₂ := vcSchema_limbs_injective hLo hHi
  have hBlind : blind₁ = blind₂ := Lane4.ext hb0 hb1 hb2 hb3
  have hPadEq : vcPadAttrs attrs₁ = vcPadAttrs attrs₂ := by
    simpa only [List.reverse_reverse] using congrArg List.reverse hPadRevEq
  unfold vcPadAttrs at hPadEq
  have hAttrs : attrs₁ = attrs₂ := (List.append_inj hPadEq hLenEq).1
  exact ⟨hSid, hAttrs, hBlind⟩

/-- **Full `1 ≤ arity ≤ 32` `BlindVC` Commitment Acceptance & Sponge Binding
    (`computeVcPoseidon2CommitFull_arity32_binding`)**:
    1. `vcMaxAttrs = 32` (`MAX_VC_ATTRS = 32`); `computeVcPoseidon2CommitFull` accepts iff
       `1 ≤ attrs.length ∧ attrs.length ≤ 32` (including full 32-attribute credentials);
    2. Any two distinct openings `(sid₁, attrs₁, blind₁) ≠ (sid₂, attrs₂, blind₂)` yielding `some c`
       constructively exhibit either `Poseidon2Perm12Sponge6Collision` or `Poseidon2Perm12ZeroCapRoot`. -/
theorem computeVcPoseidon2CommitFull_arity32_binding :
    vcMaxAttrs = 32 ∧
    (∀ (sid : UInt64) (attrs : List Goldilocks) (blind : Lane4) (tag : UInt64),
      (computeVcPoseidon2CommitFull sid attrs blind tag).isSome = true ↔
        1 ≤ attrs.length ∧ attrs.length ≤ 32) ∧
    (∀ (sid₁ sid₂ : UInt64) (attrs₁ attrs₂ : List Goldilocks)
       (blind₁ blind₂ : Lane4) (tag : UInt64) (c : Lane6),
      computeVcPoseidon2CommitFull sid₁ attrs₁ blind₁ tag = some c →
      computeVcPoseidon2CommitFull sid₂ attrs₂ blind₂ tag = some c →
      (sid₁, attrs₁, blind₁) ≠ (sid₂, attrs₂, blind₂) →
      (∃ stA stB : Poseidon2State12, Poseidon2Perm12Sponge6Collision stA stB) ∨
      (∃ st : Poseidon2State12, Poseidon2Perm12ZeroCapRoot st)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro sid attrs blind tag
    unfold computeVcPoseidon2CommitFull vcMaxAttrs
    if h : 1 ≤ attrs.length ∧ attrs.length ≤ 32 then
      simp [h]
    else
      simp [h]
  · intro sid₁ sid₂ attrs₁ attrs₂ blind₁ blind₂ tag c h1 h2 hNe
    unfold computeVcPoseidon2CommitFull at h1 h2
    cases hOk1 : decide (1 ≤ attrs₁.length ∧ attrs₁.length ≤ vcMaxAttrs) with
    | false => rw [hOk1] at h1; cases h1
    | true =>
      cases hOk2 : decide (1 ≤ attrs₂.length ∧ attrs₂.length ≤ vcMaxAttrs) with
      | false => rw [hOk2] at h2; cases h2
      | true =>
        rw [hOk1] at h1
        rw [hOk2] at h2
        simp only [↓reduceIte, Option.some.injEq] at h1 h2
        have hb1 := (of_decide_eq_true hOk1).2
        have hb2 := (of_decide_eq_true hOk2).2
        have hBlkDiff : vcCommitFullBlocks sid₁ attrs₁ blind₁ tag ≠
            vcCommitFullBlocks sid₂ attrs₂ blind₂ tag := by
          intro hEq
          obtain ⟨hs, ha, hbl⟩ := vcCommitFullBlocks_injective hb1 hb2 hEq
          exact hNe (by rw [hs, ha, hbl])
        exact absorbRate6SpongeBlocks_collision_reduction
          (limbsToLane6Blocks_pad1_nonempty _)
          (limbsToLane6Blocks_pad1_nonempty _)
          hBlkDiff (h1.trans h2.symm)

/-- **`#tooth` (`tooth_computeVcPoseidon2CommitFull_rejects_arity33`)**:
    `computeVcPoseidon2CommitFull` rejects attribute lists exceeding `vcMaxAttrs = 32` (`= none`). -/
theorem tooth_computeVcPoseidon2CommitFull_rejects_arity33 :
    ∃ (sid : UInt64) (attrs : List Goldilocks) (blind : Lane4),
      vcMaxAttrs < attrs.length ∧
      computeVcPoseidon2CommitFull sid attrs blind vcAttrCommitTag = none := by
  refine ⟨0, List.replicate 33 Goldilocks.one,
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, by decide, ?_⟩
  unfold computeVcPoseidon2CommitFull vcMaxAttrs
  simp

#tooth_pair computeVcPoseidon2CommitFull_arity32_binding vs tooth_computeVcPoseidon2CommitFull_rejects_arity33

theorem vcSmallMaxAttrs_eq : vcSmallMaxAttrs = 6 := by rfl

#verify_constructive vcSmallMaxAttrs_eq

#verify_constructive computeVcPoseidon2CommitFull_eq_small computeVcPoseidon2CommitFull_arity32_binding

#export_eqns mkState12Of6 state12Rate6 state12Cap6 lane6Zero vcMerkleStepArith vcMerkleHashPair vcMerkleChunks

#export_eqns vcAttrAt

#export_eqns vcCommitChunks vcScopeChunks computeVcScopeTag

@[expose] def seRefl (α : Type) : SimpleEquiv α α where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def seSymm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[expose] def seTrans {α β γ : Type} (e₁ : SimpleEquiv α β) (e₂ : SimpleEquiv β γ) : SimpleEquiv α γ where
  toFun x := e₂.toFun (e₁.toFun x)
  invFun z := e₁.invFun (e₂.invFun z)
  left_inv x := by rw [e₂.left_inv, e₁.left_inv]
  right_inv z := by rw [e₁.right_inv, e₂.right_inv]

@[expose] def seDepProd {α₁ α₂ β₁ β₂ : Type}
    (eqA : SimpleEquiv α₁ α₂)
    (eqB : α₁ → SimpleEquiv β₁ β₂) :
    SimpleEquiv (α₁ × β₁) (α₂ × β₂) where
  toFun p := (eqA.toFun p.1, (eqB p.1).toFun p.2)
  invFun q :=
    let a := eqA.invFun q.1
    (a, (eqB a).invFun q.2)
  left_inv := fun ⟨a, b⟩ => by
    dsimp only
    rw [eqA.left_inv a, (eqB a).left_inv b]
  right_inv := fun ⟨c, d⟩ => by
    dsimp only
    rw [eqA.right_inv c, (eqB (eqA.invFun c)).right_inv d]

end Qsag
end
