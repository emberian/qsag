module
/-
# Public permutation interface for the deployed two-lane SPN

The state is 256 bits; round constants and the chain tweak are PUBLIC parameters.
This module constructs the inverse, without a secret key or a search/choice operation.
The chain mode returns all 256 bits of P_t(x) XOR x: it has no rate/capacity split,
padding or output truncation. It is not the sponge of the quantum sponge theorems.
No random-permutation distribution or quantum security bound is asserted here.
-/
public import Qsag.Oracle.ParallelSeededSpnPolyBasis
import all Qsag.Oracle.ParallelSeededSpnPolyBasis
public section
namespace Qsag
set_option autoImplicit false

/-- Public reversible primitive. Both directions are exposed to the adversary. -/
structure PublicPermutation (State : Type) where
  forward : State → State
  inverse : State → State
  inverse_forward : ∀ x, inverse (forward x) = x
  forward_inverse : ∀ x, forward (inverse x) = x

private theorem mix_twice_lane (k : Nat) (a b x y : TowerElem k) :
    towerAdd k (towerAdd k x (towerMul k a y))
      (towerMul k a (towerAdd k y (towerMul k b x))) =
    towerMul k (towerAdd k (towerOne k) (towerMul k a b)) x := by
  rw [towerMul_add_distrib, ← towerAdd_assoc,
    towerAdd_assoc k x, towerAdd_self_zero, towerAdd_zero,
    towerAdd_mul_distrib, towerOne_mul, towerMul_assoc]

private theorem det_ne_zero {k : Nat} (mds : ValidSpnMdsPair k) :
    towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB) ≠ towerZero k := by
  intro h
  have he := congrArg (towerAdd k (towerOne k)) h
  rw [towerAdd_cancel, towerAdd_zero] at he
  exact mds.hAB_ne_one he

/-- Inverse of the linear layer: apply M again, divide both lanes by 1+A*B. -/
def publicSpnMixInverse {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) : TowerElem k × TowerElem k :=
  let d := towerInv k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB))
  let z := spnLinearMix k mds.mdsA mds.mdsB st
  (towerMul k d z.1, towerMul k d z.2)

private theorem det_cancel {k : Nat} (mds : ValidSpnMdsPair k) (x : TowerElem k) :
    towerMul k (towerInv k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB)))
      (towerMul k (towerAdd k (towerOne k) (towerMul k mds.mdsA mds.mdsB)) x) = x := by
  rw [← towerMul_assoc, towerMul_comm k (towerInv k _),
    towerMul_inv k _ (det_ne_zero mds), towerOne_mul]

theorem publicSpnMixInverse_left {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) :
    publicSpnMixInverse mds (spnLinearMix k mds.mdsA mds.mdsB st) = st := by
  apply Prod.ext
  · change towerMul k _ (towerAdd k (towerAdd k st.1 (towerMul k mds.mdsA st.2))
      (towerMul k mds.mdsA (towerAdd k st.2 (towerMul k mds.mdsB st.1)))) = st.1
    rw [mix_twice_lane, det_cancel]
  · change towerMul k _ (towerAdd k (towerAdd k st.2 (towerMul k mds.mdsB st.1))
      (towerMul k mds.mdsB (towerAdd k st.1 (towerMul k mds.mdsA st.2)))) = st.2
    rw [mix_twice_lane, towerMul_comm k mds.mdsB mds.mdsA, det_cancel]

theorem publicSpnMixInverse_right {k : Nat} (mds : ValidSpnMdsPair k)
    (st : TowerElem k × TowerElem k) :
    spnLinearMix k mds.mdsA mds.mdsB (publicSpnMixInverse mds st) = st := by
  have h := publicSpnMixInverse_left mds st
  have commute : spnLinearMix k mds.mdsA mds.mdsB (publicSpnMixInverse mds st) =
      publicSpnMixInverse mds (spnLinearMix k mds.mdsA mds.mdsB st) := by
    dsimp only [spnLinearMix, publicSpnMixInverse]
    simp only [towerMul_add_distrib, towerAdd_mul_distrib, towerMul_assoc, towerMul_comm,
      towerMul_left_comm_of_assoc k (towerMul_assoc k)]
  exact commute.trans h

/-- Undo mixing, undo x^7, then undo public round-constant XOR. -/
def publicSpnRoundInverse (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    Tower128 × Tower128 :=
  let z := publicSpnMixInverse mds st
  (towerAdd 7 (towerSbox7Inv128 z.1) rc.1, towerAdd 7 (towerSbox7Inv128 z.2) rc.2)

theorem publicSpnRoundInverse_left (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    publicSpnRoundInverse mds rc (spnRound128 mds.mdsA mds.mdsB rc st) = st := by
  unfold spnRound128 publicSpnRoundInverse
  rw [publicSpnMixInverse_left]
  simp only [towerSbox7Inv128_left_inv, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem publicSpnRoundInverse_right (mds : ValidSpnMdsPair 7) (rc st : Tower128 × Tower128) :
    spnRound128 mds.mdsA mds.mdsB rc (publicSpnRoundInverse mds rc st) = st := by
  unfold spnRound128 publicSpnRoundInverse
  simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerSbox7Inv128_right_inv]
  exact publicSpnMixInverse_right mds st

/-- Generic reverse traversal keeps the recursion independent of field representation. -/
def publicReverseIter {State : Type} (inverseRound : Nat → State → State) : Nat → State → State
  | 0, st => st
  | n + 1, st => publicReverseIter inverseRound n (inverseRound n st)

/-- Rounds are undone in descending order. -/
def publicSpnIterInverse (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128) :=
  publicReverseIter (fun n => publicSpnRoundInverse mds (rcs n))

private theorem reverseIter_left {State : Type}
    (f g : Nat → State → State) (trace : Nat → State → State)
    (hzero : ∀ x, trace 0 x = x)
    (hstep : ∀ n x, trace (n + 1) x = f n (trace n x))
    (hleft : ∀ n x, g n (f n x) = x) (n : Nat) (x : State) :
    publicReverseIter g n (trace n x) = x := by
  induction n with
  | zero => exact hzero x
  | succ n ih =>
    rw [hstep, publicReverseIter, hleft]
    exact ih

private theorem reverseIter_right {State : Type}
    (f g : Nat → State → State) (trace : Nat → State → State)
    (hzero : ∀ x, trace 0 x = x)
    (hstep : ∀ n x, trace (n + 1) x = f n (trace n x))
    (hright : ∀ n x, f n (g n x) = x) (n : Nat) (x : State) :
    trace n (publicReverseIter g n x) = x := by
  induction n generalizing x with
  | zero => exact hzero x
  | succ n ih => rw [publicReverseIter, hstep, ih, hright]

theorem publicSpnIterInverse_left (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128)
    (n : Nat) (st : Tower128 × Tower128) :
    publicSpnIterInverse mds rcs n (spnIterRounds128 mds.mdsA mds.mdsB rcs n st) = st := by
  unfold publicSpnIterInverse
  exact reverseIter_left
    (fun i => spnRound128 mds.mdsA mds.mdsB (rcs i))
    (fun i => publicSpnRoundInverse mds (rcs i))
    (spnIterRounds128 mds.mdsA mds.mdsB rcs)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun i x => publicSpnRoundInverse_left mds (rcs i) x) n st

theorem publicSpnIterInverse_right (mds : ValidSpnMdsPair 7) (rcs : Nat → Tower128 × Tower128)
    (n : Nat) (st : Tower128 × Tower128) :
    spnIterRounds128 mds.mdsA mds.mdsB rcs n (publicSpnIterInverse mds rcs n st) = st := by
  unfold publicSpnIterInverse
  exact reverseIter_right
    (fun i => spnRound128 mds.mdsA mds.mdsB (rcs i))
    (fun i => publicSpnRoundInverse mds (rcs i))
    (spnIterRounds128 mds.mdsA mds.mdsB rcs)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun i x => publicSpnRoundInverse_right mds (rcs i) x) n st

/-- Concrete public inverse in Rust's polynomial basis; no secret input is required. -/
def rustPublicSpnInverse (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  psiTower128Pair (publicSpnIterInverse parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st))

theorem rustPublicSpnInverse_left (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) :
    rustPublicSpnInverse rcs (rustSpnIter rcs spnRounds st) = st := by
  rw [rustSpnIter_eq_tower]
  unfold rustPublicSpnInverse
  rw [polyToTower128Pair_psiTower128Pair]
  have h := publicSpnIterInverse_left parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st)
  simp only [parallelSeededMdsPair] at h ⊢
  rw [h, psiTower128Pair_polyToTower128Pair]

theorem rustPublicSpnInverse_right (rcs : Nat → BitVec 128 × BitVec 128)
    (st : BitVec 128 × BitVec 128) :
    rustSpnIter rcs spnRounds (rustPublicSpnInverse rcs st) = st := by
  rw [rustSpnIter_eq_tower]
  unfold rustPublicSpnInverse
  rw [polyToTower128Pair_psiTower128Pair]
  have h := publicSpnIterInverse_right parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) spnRounds (polyToTower128Pair st)
  simp only [parallelSeededMdsPair] at h ⊢
  rw [h, psiTower128Pair_polyToTower128Pair]

abbrev PublicSpnState := BitVec 128 × BitVec 128

def rustPublicSpn (rcs : Nat → PublicSpnState) : PublicPermutation PublicSpnState where
  forward := rustSpnIter rcs spnRounds
  inverse := rustPublicSpnInverse rcs
  inverse_forward := rustPublicSpnInverse_left rcs
  forward_inverse := rustPublicSpnInverse_right rcs

/-- Whole-state feed-forward, not a sponge and not a secret-key block cipher. -/
def publicSpnFeedForward (p : PublicPermutation PublicSpnState) (x : PublicSpnState) :
    PublicSpnState := ((p.forward x).1 ^^^ x.1, (p.forward x).2 ^^^ x.2)

theorem rustAlgebraicStep_eq_publicFeedForward (rcs : Nat → PublicSpnState)
    (x : PublicSpnState) :
    rustAlgebraicStep rcs x = publicSpnFeedForward (rustPublicSpn rcs) x := by
  simp only [rustAlgebraicStep, publicSpnFeedForward, rustPublicSpn]

/-- Native Rust integer ranges, so no extra natural-number framing alias is admitted. -/
structure PublicChainAddress where
  pkSeed : List UInt8
  pkSeed_length : pkSeed.length = 32
  epoch : Fin (2 ^ 32)
  chainIdx : Fin (2 ^ 16)
  step : UInt8

/-- The family is indexed by the DERIVED tweak. Different addresses need not produce
independent permutations, nor even different tweaks. cSHAKE remains an explicit parameter. -/
def publicChainPermutation
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (address : PublicChainAddress) : PublicPermutation PublicSpnState :=
  rustPublicSpn (rustSpnRoundConstants hash32
    (rustDeriveChainTweak hash32 address.pkSeed address.epoch.val address.chainIdx.val address.step))

/-- Exact lane framing and full-output connection to the deployed chain transcription. -/
theorem rustParallelChainStep_eq_publicFeedForward
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (address : PublicChainAddress) (cur : List UInt8) :
    rustParallelChainStep hash32 address.pkSeed address.epoch.val address.chainIdx.val address.step cur =
      rustLanesToBytes32 (publicSpnFeedForward (publicChainPermutation hash32 address)
        (rustBytes32ToLanes cur)) := by
  simp only [rustParallelChainStep, publicSpnFeedForward, publicChainPermutation, rustPublicSpn, rustAlgebraicStep]

/-- Chain composition preserves the per-position public address. There is no implicit
fixed-permutation iteration: each step may derive different round constants. -/
def publicChainRun
    (hash32 : List UInt8 → List (List UInt8) → List UInt8) :
    List PublicChainAddress → PublicSpnState → PublicSpnState
  | [], x => x
  | address :: rest, x => publicChainRun hash32 rest
      (publicSpnFeedForward (publicChainPermutation hash32 address) x)

def rustPublicChainRun
    (hash32 : List UInt8 → List (List UInt8) → List UInt8) :
    List PublicChainAddress → List UInt8 → List UInt8
  | [], bytes => bytes
  | address :: rest, bytes => rustPublicChainRun hash32 rest
      (rustParallelChainStep hash32 address.pkSeed address.epoch.val address.chainIdx.val address.step bytes)

theorem publicChainRun_bytes
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (addresses : List PublicChainAddress) (x : PublicSpnState) :
    rustPublicChainRun hash32 addresses (rustLanesToBytes32 x) =
      rustLanesToBytes32 (publicChainRun hash32 addresses x) := by
  induction addresses generalizing x with
  | nil => rfl
  | cons address rest ih =>
    simp only [rustPublicChainRun, publicChainRun,
      rustParallelChainStep_eq_publicFeedForward, rustBytes32ToLanes_lanesToBytes32, ih]

/-- A public inverse query constructs a fixed point of this feed-forward mode. This is
NOT a chosen-target preimage attack and does not give a fixed point shared by chain steps. -/
theorem publicSpnFeedForward_fixedPoint (p : PublicPermutation PublicSpnState) :
    publicSpnFeedForward p (p.inverse (0#128, 0#128)) = p.inverse (0#128, 0#128) := by
  unfold publicSpnFeedForward
  rw [p.forward_inverse]
  simp only [BitVec.zero_xor]

theorem publicChain_fixedPoint_bytes
    (hash32 : List UInt8 → List (List UInt8) → List UInt8) (address : PublicChainAddress) :
    let node := rustLanesToBytes32 ((publicChainPermutation hash32 address).inverse (0#128, 0#128))
    rustParallelChainStep hash32 address.pkSeed address.epoch.val address.chainIdx.val address.step node = node := by
  dsimp only
  rw [rustParallelChainStep_eq_publicFeedForward, rustBytes32ToLanes_lanesToBytes32,
    publicSpnFeedForward_fixedPoint]

/-- Idealization requires sampling this type, with a stated distribution. A fixed member
is merely a permutation, and carries no pseudorandomness claim. -/
def identityPublicPermutation : PublicPermutation PublicSpnState where
  forward := id
  inverse := id
  inverse_forward := fun _ => rfl
  forward_inverse := fun _ => rfl

/-- Nonvacuity guard: the permutation laws alone cannot imply collision resistance
of the feed-forward construction. Distinct explicit 256-bit nodes collide. -/
theorem publicPermutation_laws_allow_feedForward_collision :
    (0#128, 0#128) ≠ (1#128, 0#128) ∧
    publicSpnFeedForward identityPublicPermutation (0#128, 0#128) =
      publicSpnFeedForward identityPublicPermutation (1#128, 0#128) := by
  constructor
  · intro h
    have h0 := congrArg Prod.fst h
    contradiction
  · decide

/-- Primitive access includes both public directions. This operational classical subgame
is also available to quantum adversaries, but does not purport to define quantum states. -/
inductive PublicPermutationDirection where
  | forward | inverse
  deriving DecidableEq

def publicPermutationQuery {State : Type} (p : PublicPermutation State)
    (direction : PublicPermutationDirection) (x : State) : State :=
  match direction with
  | .forward => p.forward x
  | .inverse => p.inverse x

/-- Adaptive terminating public-primitive programs. The continuation receives the actual
answer, not an assumed classically observable log of a coherent quantum query. -/
inductive PublicPermutationProgram (State Result : Type) where
  | done : Result → PublicPermutationProgram State Result
  | query : PublicPermutationDirection → State →
      (State → PublicPermutationProgram State Result) → PublicPermutationProgram State Result

/-- Result and separate forward/inverse query counts along the actual execution. -/
def runPublicPermutationProgram {State Result : Type} (p : PublicPermutation State) :
    PublicPermutationProgram State Result → Result × Nat × Nat
  | .done result => (result, 0, 0)
  | .query direction x next =>
      let answer := runPublicPermutationProgram p (next (publicPermutationQuery p direction x))
      match direction with
      | .forward => (answer.1, answer.2.1 + 1, answer.2.2)
      | .inverse => (answer.1, answer.2.1, answer.2.2 + 1)

def publicFixedPointAttack : PublicPermutationProgram PublicSpnState PublicSpnState :=
  .query .inverse (0#128, 0#128) (fun x => .done x)

theorem publicFixedPointAttack_one_inverse (p : PublicPermutation PublicSpnState) :
    runPublicPermutationProgram p publicFixedPointAttack = (p.inverse (0#128, 0#128), 0, 1) := by
  simp only [runPublicPermutationProgram, publicFixedPointAttack, publicPermutationQuery]

/-- Mode-specific fixed-point game, with primitive access charged in each direction.
Mode evaluation for checking the winning relation is one additional forward call.
This event holds for every permutation, hence for every distribution over permutations. -/
def publicFeedForwardFixedPointGame (p : PublicPermutation PublicSpnState)
    (attack : PublicPermutationProgram PublicSpnState PublicSpnState) : Prop :=
  let result := runPublicPermutationProgram p attack
  result.2.1 = 0 ∧ result.2.2 ≤ 1 ∧ publicSpnFeedForward p result.1 = result.1

theorem publicFixedPointAttack_wins (p : PublicPermutation PublicSpnState) :
    publicFeedForwardFixedPointGame p publicFixedPointAttack :=
  ⟨rfl, Nat.le_refl 1, publicSpnFeedForward_fixedPoint p⟩

/-- Separate fresh-image inversion event for the feed-forward mode. A fixed-point
witness is not an automatic winner here: the target depends on challenge x. -/
def publicFeedForwardPreimageGame (p : PublicPermutation PublicSpnState)
    (attack : PublicSpnState → PublicPermutationProgram PublicSpnState PublicSpnState)
    (challenge : PublicSpnState) (forwardBudget inverseBudget : Nat) : Prop :=
  let target := publicSpnFeedForward p challenge
  let result := runPublicPermutationProgram p (attack target)
  result.2.1 ≤ forwardBudget ∧ result.2.2 ≤ inverseBudget ∧
    publicSpnFeedForward p result.1 = target

end Qsag
end
#verify_constructive
  Qsag.rustPublicSpnInverse_left
  Qsag.rustPublicSpnInverse_right
  Qsag.rustParallelChainStep_eq_publicFeedForward
  Qsag.publicChainRun_bytes
  Qsag.publicChain_fixedPoint_bytes
  Qsag.publicPermutation_laws_allow_feedForward_collision
  Qsag.publicFixedPointAttack_wins
