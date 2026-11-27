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

