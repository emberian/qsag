module
public import Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Protocol.Signing.ProdCollisionEvents — winning events defined from the extractor output

`prodOutcomeBreak` runs `production_forgery_extract` on a game outcome. `prodTcrOutput` is the
`(target, colliding input)` pair it returns, and `prodTcrEvent` is the executable check
`prodTcrCheck` on that pair. `production_euf_cma_extracted_bound` counts wins against the three
events defined this way. It has no supplied event and no hypothesis covering `ProdSmTcrBreak`,
which is what `production_euf_cma_advantage_bound` requires of its caller.

Scope. The count is a deterministic classification over a finite coin list. It assigns no
probability to the three events and does not model the hash as an oracle, so it is not yet a
bound by a primitive advantage. `prodTcrOutput` is a function of the whole outcome, secret key
included; an adversary that computes it from public data and oracle answers is not constructed
here.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! ### Events defined from the extractor output -/

/-- The reduction run on one experiment outcome: `none` when the outcome is not a win. -/
def prodOutcomeBreak (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    Option (ProdBreakWitness suite params o.sk (productionSigningLog suite params o.sk o.queries)
      o.msgStar o.sigStar) :=
  if hWin : prodEufCmaWin suite params o = true then
    some (production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
      (fun e he hEq => by
        unfold prodEufCmaWin at hWin
        rw [Bool.and_eq_true] at hWin
        exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e, he, hEq⟩))
      (by
        unfold prodEufCmaWin at hWin
        rw [Bool.and_eq_true] at hWin
        exact hWin.1))
  else none

/-- Output of the target-collision reduction on one outcome: the chosen target and the colliding
    input, when the forgery leads to a collision. -/
def prodTcrOutput (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    Option (ProdTargetIdx × List UInt8) :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.tcr w) => some (w.target, w.forged)
  | _ => none

/-- Primitive target-collision win: `prodTcrCheck` on the returned pair. -/
def prodTcrEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodTcrOutput suite params hw o hOneTime with
  | some (t, forged) => prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged
  | none => false

/-- The reduction ends in the FORS index-coverage event. -/
def prodItsrEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.itsr _) => true
  | _ => false

/-- The reduction ends in the preimage event. -/
def prodPreEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.pre _) => true
  | _ => false

/-- A returned pair is a checked collision with an on-path target, at a hash call of the verifier
    on the forgery, and comes from a winning outcome. -/
theorem prodTcrOutput_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (t : ProdTargetIdx) (forged : List UInt8)
    (hOut : prodTcrOutput suite params hw o hOneTime = some (t, forged)) :
    prodEufCmaWin suite params o = true ∧
    t.OnPath params (productionSigningLog suite params o.sk o.queries) o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar) ∧
    t.ForgedCall suite params o.sk o.msgStar o.sigStar forged ∧
    prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged = true := by
  unfold prodTcrOutput at hOut
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hOut; cases hOut
  | some b =>
    rw [hB] at hOut
    have hWin : prodEufCmaWin suite params o = true := by
      unfold prodOutcomeBreak at hB
      split at hB
      · assumption
      · cases hB
    cases b with
    | itsr h => cases hOut
    | pre h => cases hOut
    | tcr w =>
      have hEq : (w.target, w.forged) = (t, forged) := Option.some.inj hOut
      have h1 : w.target = t := congrArg Prod.fst hEq
      have h2 : w.forged = forged := congrArg Prod.snd hEq
      rw [← h1, ← h2]
      exact ⟨hWin, w.onPath, w.call, w.check⟩

theorem prodItsrEvent_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hEv : prodItsrEvent suite params hw o hOneTime = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params o.sk)
      (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar := by
  unfold prodItsrEvent at hEv
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hEv; cases hEv
  | some b =>
    rw [hB] at hEv
    cases b with
    | itsr h => exact h
    | pre h => cases hEv
    | tcr w => cases hEv

theorem prodPreEvent_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hEv : prodPreEvent suite params hw o hOneTime = true) :
    ProdPreimageBreak suite params o.sk (productionSigningLog suite params o.sk o.queries)
      o.msgStar o.sigStar := by
  unfold prodPreEvent at hEv
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hEv; cases hEv
  | some b =>
    rw [hB] at hEv
    cases b with
    | itsr h => cases hEv
    | pre h => exact h
    | tcr w => cases hEv

/-- Every winning outcome lands in one of the three extractor-defined events. -/
theorem prodEufCmaWin_classified (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hWin : prodEufCmaWin suite params o = true) :
    prodItsrEvent suite params hw o hOneTime = true ∨
    prodTcrEvent suite params hw o hOneTime = true ∨
    prodPreEvent suite params hw o hOneTime = true := by
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none =>
    exfalso
    unfold prodOutcomeBreak at hB
    split at hB
    · cases hB
    · rename_i hNo
      exact hNo hWin
  | some b =>
    cases b with
    | itsr h =>
      left
      unfold prodItsrEvent
      rw [hB]
    | pre h =>
      right; right
      unfold prodPreEvent
      rw [hB]
    | tcr w =>
      right; left
      unfold prodTcrEvent prodTcrOutput
      rw [hB]
      exact w.check

/-- **Production EUF-CMA count against extractor-defined events.** The number of winning coins is
    at most the number of coins on which the reduction ends in index coverage, plus the number on
    which the pair it returns passes `prodTcrCheck`, plus the number on which it ends in the
    preimage event. Unlike `production_euf_cma_advantage_bound` there is no supplied event and no
    hypothesis covering `ProdSmTcrBreak`. -/
theorem production_euf_cma_extracted_bound {Ω : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (coins : List Ω) (game : Ω → ProdEufCmaOutcome)
    (hOneTime : ∀ ω, params.statefulJorts = true → ∀ q, q ∈ (game ω).queries →
      ∀ q', q' ∈ (game ω).queries → q.epoch = q'.epoch → q = q') :
    hitCount (fun ω => prodEufCmaWin suite params (game ω)) coins ≤
      hitCount (fun ω => prodItsrEvent suite params hw (game ω) (hOneTime ω)) coins +
      hitCount (fun ω => prodTcrEvent suite params hw (game ω) (hOneTime ω)) coins +
      hitCount (fun ω => prodPreEvent suite params hw (game ω) (hOneTime ω)) coins :=
  hitCount_union_bound _ _ _ _
    (fun ω hWin => prodEufCmaWin_classified suite params hw (game ω) (hOneTime ω) hWin) coins

theorem prodToyRadix : prodToyStatefulParams.w = 4 ∨ prodToyStatefulParams.w = 16 := .inl rfl

theorem prodToyOneTime : prodToyStatefulParams.statefulJorts = true →
    ∀ q, q ∈ ([] : List ProdSigningQuery) → ∀ q', q' ∈ ([] : List ProdSigningQuery) →
      q.epoch = q'.epoch → q = q' :=
  fun _ _ h => by cases h

/-- **The reduction returns a collision on a concrete accepted forgery.** On the accepted toy
    forgery (`prodToyForgery_accepted`, constant hash, empty log) the extractor evaluates, in the
    kernel, to a returned `(target, colliding input)` pair. -/
theorem prodToyForgery_returns_collision :
    (prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime).isSome = true := by
  decide +kernel

/-- Hence a checked on-path collision exists for that forgery, obtained from the extractor. -/
theorem prodToyForgery_checked_collision :
    ∃ t forged,
      t.OnPath prodToyStatefulParams [] prodToyForgery.leafGlobalIdx
        (prodSigForsIdxs crumbToySuite prodToyStatefulParams
          (derivePublicKey crumbToySuite prodToyStatefulParams ⟨[], [], []⟩) [] prodToyForgery) ∧
      prodTcrCheck crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ prodToyForgery.leafGlobalIdx
        t forged = true := by
  cases hOut : prodTcrOutput crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime with
  | none =>
    have h := prodToyForgery_returns_collision
    rw [hOut] at h
    cases h
  | some p =>
    obtain ⟨_, hOn, _, hChk⟩ := prodTcrOutput_sound crumbToySuite prodToyStatefulParams prodToyRadix
      ⟨⟨[], [], []⟩, [], [], prodToyForgery⟩ prodToyOneTime p.1 p.2 hOut
    exact ⟨p.1, p.2, hOn, hChk⟩

end Qsag
end

#verify_constructive Qsag.prodTcrOutput_sound Qsag.prodItsrEvent_sound Qsag.prodPreEvent_sound
#verify_constructive Qsag.prodEufCmaWin_classified Qsag.production_euf_cma_extracted_bound
#verify_constructive Qsag.prodToyForgery_returns_collision Qsag.prodToyForgery_checked_collision
#tooth_pair Qsag.production_euf_cma_extracted_bound vs Qsag.prodEufCmaWin_rejects_signed_message
