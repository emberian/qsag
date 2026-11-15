module
public import Qsag.ProdCollisionEvents
import all Qsag.ProdCollisionEvents
import all Qsag.ProdCollisionExtraction
import all Qsag.ProdCollisionLayers
import all Qsag.ProdCollisionWitness
import all Qsag.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.ProdCollisionAccounting — the candidate targets of one forgery

`ProdSmTcrBreak` ranges over every honest hash input of the key. A returned `ProdTcrWitness` is
narrower: `ProdTargetIdx.OnPath` leaves no free index. `prodPathTargets` lists the candidates for
a forgery with hypertree leaf `leaf` and FORS indices `idxs`:

* per layer, the `subtreeHeight` XMSS nodes on the path, one WOTS public-key compression and
  `ell1 * (w - 1)` chain steps;
* per FORS tree, the `forsHeight` nodes on the path of its opened leaf, and one root compression;
* per logged signature, its `numLayers` layer digests and its message pre-hash.

`ProdTargetIdx.mem_pathTargets` shows every on-path target is in the list and
`prodPathTargets_length` gives its length `prodPathTargetCount params log.length`.
`prodTcrOutput_target_budget` states both for the pair the reduction returns, with the log length
bounded by the number of signing queries.

Scope and limits.
* The list depends on the leaf and FORS indices of the forgery, which the adversary chooses after
  seeing signatures. This is a bound on the targets *selected by one forgery*, not on a target set
  fixed before the experiment. Over all leaves the node, compression and chain targets range over
  the whole hypertree and FORS forest of the key.
* In stateless profiles an on-path node need not have been evaluated by any signing query: it is
  determined by the secret key, not by the log.
* No count of hash evaluations made by the extractor is proved, and no probability is assigned.
-/

public section
namespace Qsag

set_option autoImplicit false

-- FORS tree address, key pair and leaf indices of the forgery.
set_option hygiene false in
local notation:max "FORS_TREE" => (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
set_option hygiene false in
local notation:max "FORS_KP" => (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
set_option hygiene false in
local notation:max "FORS_IDXS" =>
  (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)

theorem prod_length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length = k) → (xs.flatMap f).length = xs.length * k
  | [], _ => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | x :: xs, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      prod_length_flatMap_const f k xs (fun y hy => h y (List.mem_cons_of_mem x hy)),
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem prod_length_range_flatMap_map {β : Type} (n k : Nat) (g : Nat → Nat → β) :
    ((List.range n).flatMap fun x => (List.range k).map (g x)).length = n * k := by
  rw [prod_length_flatMap_const _ k _ (fun x _ => by rw [List.length_map, List.length_range]),
    List.length_range]

theorem prod_length_range_flatMap_flatMap_map {β : Type} (n m k : Nat) (g : Nat → Nat → Nat → β) :
    ((List.range n).flatMap fun x => (List.range m).flatMap fun y =>
      (List.range k).map (g x y)).length = n * (m * k) := by
  rw [prod_length_flatMap_const _ (m * k) _
      (fun x _ => prod_length_range_flatMap_map m k (g x)),
    List.length_range]

theorem prod_length_flatMap_range_map {α β : Type} (xs : List α) (k : Nat) (g : α → Nat → β) :
    (xs.flatMap fun e => (List.range k).map (g e)).length = xs.length * k :=
  prod_length_flatMap_const _ k xs (fun x _ => by rw [List.length_map, List.length_range])

/-- Honest hash inputs on the verification path of a forgery with leaf `leaf` and FORS leaf
    indices `idxs`, over the log `log`. -/
def prodPathTargets (params : PqHashParams) (log : List (List UInt8 × PqHashSig)) (leaf : Nat)
    (idxs : List Nat) : List ProdTargetIdx :=
  ((List.range params.numLayers).flatMap fun l => (List.range params.subtreeHeight).map fun h =>
    ProdTargetIdx.xmssNode l h
      (leaf / 2 ^ (l * params.subtreeHeight) % 2 ^ params.subtreeHeight / 2 ^ (h + 1))) ++
  ((List.range params.numLayers).map ProdTargetIdx.wotsPk ++
  (((List.range params.numLayers).flatMap fun l => (List.range params.ell1).flatMap fun r =>
    (List.range (params.w - 1)).map fun s => ProdTargetIdx.chainStep l r s) ++
  (((List.range params.forsTrees).flatMap fun j => (List.range params.forsHeight).map fun h =>
    ProdTargetIdx.forsNode j h (params.forsHeight - (h + 1)) (idxs.getD j 0 / 2 ^ (h + 1))) ++
  (ProdTargetIdx.forsRoots ::
  ((log.flatMap fun e => (List.range params.numLayers).map fun i =>
    ProdTargetIdx.signedDigest e i) ++
  log.map ProdTargetIdx.preHash)))))

/-- Number of candidate targets of one forgery against a log of `logLen` signatures. -/
def prodPathTargetCount (params : PqHashParams) (logLen : Nat) : Nat :=
  params.numLayers * params.subtreeHeight +
  (params.numLayers +
  (params.numLayers * (params.ell1 * (params.w - 1)) +
  (params.forsTrees * params.forsHeight +
  (logLen * params.numLayers + logLen + 1))))

theorem prodPathTargets_length (params : PqHashParams) (log : List (List UInt8 × PqHashSig))
    (leaf : Nat) (idxs : List Nat) :
    (prodPathTargets params log leaf idxs).length = prodPathTargetCount params log.length := by
  unfold prodPathTargets prodPathTargetCount
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range,
    prod_length_range_flatMap_flatMap_map, prod_length_flatMap_range_map]

theorem prodPathTargetCount_mono (params : PqHashParams) {a b : Nat} (h : a ≤ b) :
    prodPathTargetCount params a ≤ prodPathTargetCount params b := by
  unfold prodPathTargetCount
  have h1 : a * params.numLayers ≤ b * params.numLayers := Nat.mul_le_mul_right _ h
  omega

/-- Every on-path target is one of the listed candidates. -/
theorem ProdTargetIdx.mem_pathTargets (params : PqHashParams)
    (log : List (List UInt8 × PqHashSig)) (leaf : Nat) (idxs : List Nat) :
    ∀ t : ProdTargetIdx, t.OnPath params log leaf idxs → t ∈ prodPathTargets params log leaf idxs
  | .xmssNode l h n, hOn => by
    obtain ⟨hl, hh, hLo, hHi⟩ := hOn
    have hn : leaf / 2 ^ (l * params.subtreeHeight) % 2 ^ params.subtreeHeight / 2 ^ (h + 1) = n :=
      Nat.div_eq_of_lt_le hLo hHi
    unfold prodPathTargets
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_map.mpr ⟨h, List.mem_range.mpr hh, by rw [hn]⟩⟩
  | .wotsPk l, hOn => by
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hOn, rfl⟩
  | .chainStep l r s, hOn => by
    obtain ⟨hl, hr, hs⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
        List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩⟩
  | .forsNode j h d b, hOn => by
    obtain ⟨_, hj, hD, hLo, hHi⟩ := hOn
    have hb : idxs.getD j 0 / 2 ^ (h + 1) = b := Nat.div_eq_of_lt_le hLo hHi
    have hd : params.forsHeight - (h + 1) = d := by rw [← hD, Nat.add_sub_cancel]
    have hh : h < params.forsHeight := by
      rw [← hD]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self h) (Nat.le_add_left _ _)
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
      List.mem_map.mpr ⟨h, List.mem_range.mpr hh, by rw [hd, hb]⟩⟩
  | .forsRoots, hOn => by
    have _hSt : params.statefulJorts = false := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_cons_self
  | .signedDigest e i, hOn => by
    obtain ⟨he, hi, _⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩
  | .preHash e, hOn => by
    obtain ⟨he, _⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨e, he, rfl⟩

theorem productionSigningLog_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    ∀ queries : List ProdSigningQuery,
      (productionSigningLog suite params sk queries).length ≤ queries.length
  | [] => Nat.le_refl 0
  | q :: qs => by
    have ih := productionSigningLog_length_le suite params sk qs
    unfold productionSigningLog
    cases prodSignQuery suite params sk q with
    | none => exact Nat.le_trans ih (Nat.le_succ _)
    | some sig => exact Nat.succ_le_succ ih

/-- The target of a returned witness is one of the candidates of its forgery. -/
theorem ProdTcrWitness.target_mem {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (List UInt8 × PqHashSig)} {msgStar : List UInt8}
    {sigStar : PqHashSig} (w : ProdTcrWitness suite params sk log msgStar sigStar) :
    w.target ∈ prodPathTargets params log sigStar.leafGlobalIdx (FORS_IDXS) :=
  ProdTargetIdx.mem_pathTargets params log _ _ w.target w.onPath

/-- **Target budget of the returned pair.** The target returned on an experiment outcome is one
    of the listed candidates of that forgery, a checked collision with it, and the number of
    candidates is at most `prodPathTargetCount params (number of signing queries)`. -/
theorem prodTcrOutput_target_budget (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (t : ProdTargetIdx) (forged : List UInt8)
    (hOut : prodTcrOutput suite params hw o hOneTime = some (t, forged)) :
    t ∈ prodPathTargets params (productionSigningLog suite params o.sk o.queries)
      o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar) ∧
    (prodPathTargets params (productionSigningLog suite params o.sk o.queries)
      o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar
        o.sigStar)).length ≤ prodPathTargetCount params o.queries.length ∧
    prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged = true := by
  obtain ⟨_, hOn, _, hChk⟩ := prodTcrOutput_sound suite params hw o hOneTime t forged hOut
  refine ⟨ProdTargetIdx.mem_pathTargets params _ _ _ t hOn, ?_, hChk⟩
  rw [prodPathTargets_length]
  exact prodPathTargetCount_mono params (productionSigningLog_length_le suite params o.sk o.queries)

/-- An out-of-range layer is not a candidate target: the bound is not vacuous. -/
theorem prodTargetIdx_layer_out_of_range (params : PqHashParams)
    (log : List (List UInt8 × PqHashSig)) (leaf : Nat) (idxs : List Nat) (layer : Nat)
    (hLayer : params.numLayers ≤ layer) :
    ¬ (ProdTargetIdx.wotsPk layer).OnPath params log leaf idxs :=
  fun hOn => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hOn hLayer)

end Qsag
end

#verify_constructive Qsag.prodPathTargets_length Qsag.prodPathTargetCount_mono
#verify_constructive Qsag.ProdTargetIdx.mem_pathTargets Qsag.productionSigningLog_length_le
#verify_constructive Qsag.ProdTcrWitness.target_mem Qsag.prodTcrOutput_target_budget
#verify_constructive Qsag.prodTargetIdx_layer_out_of_range
