module
/-
# Qsag.Protocol.Signing.HulsingMultiHopReduction — Hop 4 Interactive `Assumptions` Reductions & Master Multi-Hop EUF-CMA Theorem

Completes Hop 4 and the composed standard-model multi-hop EUF-CMA game-playing reduction for both
stateful `Jorts` (`latchOn = true`) and stateless `Baggy` / `Corduroy` / `SLH-DSA` profiles over
unrestricted `pk`-dependent adaptive `(qHash, qSign)` adversaries:

1. **Interactive `Spec.itsrGame` (`Spec.ItsrHard`) Reduction (§1):**
   * `itsrHopReductionAdv` (`Spec.Within qSign`) queries `Spec.itsrOracle` on each admitted signing
     request and outputs `(sigStar.rRand, msgStar)`, establishing `hulsing_hop4a_itsr_bound`, plus
     zero `ITSR` loss (`stateful_itsr_zero_bound`) when `params.statefulJorts = true` or
     `params.forsTrees = 0`.
2. **Interactive `Spec.smDtTcrGame` (`Spec.SmDtTcrHard`) & Open-Seed `SM-DT-TCR` Reductions (§2):**
   * `preCommittedTcrAdv` (`Spec.Within (targets.length + 1)`) commits distinct-tweak targets
     before `.reveal`, receives `pkSeed`, runs `extractIdealPrfTcrWitnessOpt`, and proves the tight
     `1×` bound `hulsing_hop4b_smDtTcr_precommitted_bound` under `Spec.SmDtTcrHard`.
   * `openSeedTcrHopAdv` (`Spec.Within 2`) calls `.reveal` first to obtain `pkSeed`, runs any
     unrestricted `pk`-dependent adaptive `(qHash, qSign)` adversary `A`, commits the extracted
     target under `smDtOpenSeedTcrOracle`, and proves the unconditional tight `1×` bound
     `hulsing_hop4b_openSeedTcr_tight_bound` under `SmDtOpenSeedTcrHard`, paired with negative
     refutation `smDtOpenSeedTcrHard_constHash_refuted`.
3. **Interactive `Spec.smDtPreGame` (`Spec.SmDtPreHard`) + Hop-3 `SmDtUdHard` Secret-Slot Reduction (§3):**
   * `puncturedSlotPreAdv` (`Spec.Within 2`, zero `hCand` restriction) calls `.target` then
     `.reveal`, simulates `pk` and adaptive signing queries from `(pkSeed, yTarget)`, and extracts
     the forged preimage directly into `Spec.smDtPreGame` (`hulsing_hop4c_smDtPre_interactive_bound`
     and `hulsing_hop3_and_hop4c_wots_chain_bound`), with `explicitPreBreak_gives_tweakHash_eq`
     connecting both `.fors` and `.wots` branches of `ExplicitPreBreak` to `suiteTweakHash`.
4. **Master Multi-Hop Standard-Model EUF-CMA Theorem (`hulsing_full_multihop_euf_cma_bound`, §4):**
   * Composes Hop 1 (`hulsing_hop1_prfMsg_idealization`) + Hop 2 (`hulsing_hop2_prfSec_idealization`)
     + Hop 3 (`hulsing_hop3_ud_chain_simulation`) + Hop 4 (`hulsing_hop4_idealPrf_euf_cma_bound`).
-/

public import Qsag.Protocol.Signing.HulsingExplicitClassify
public import Qsag.Protocol.Signing.ProductionParamRefinement
import Qsag.Tactic.AssuranceKit

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag

set_option autoImplicit false

/-! ## §1. Interactive `Spec.itsrGame` (`Spec.ItsrHard`) Reduction -/

/-- Injective flattening of `(leafIdx, j, idxJ)` FORS positions into `Nat`. -/
def encodeForsGlobalPos (params : PqHashParams) (leafIdx j idxJ : Nat) : Nat :=
  (leafIdx * params.forsTrees + j) * 2 ^ params.forsHeight + idxJ

theorem encodeForsGlobalPos_inj {params : PqHashParams} {l₁ j₁ u₁ l₂ j₂ u₂ : Nat}
    (hj₁ : j₁ < params.forsTrees) (hj₂ : j₂ < params.forsTrees)
    (hu₁ : u₁ < 2 ^ params.forsHeight) (hu₂ : u₂ < 2 ^ params.forsHeight)
    (hEq : encodeForsGlobalPos params l₁ j₁ u₁ = encodeForsGlobalPos params l₂ j₂ u₂) :
    l₁ = l₂ ∧ j₁ = j₂ ∧ u₁ = u₂ := by
  unfold encodeForsGlobalPos at hEq
  have hPowPos : 0 < 2 ^ params.forsHeight := Nat.two_pow_pos _
  have hModU := congrArg (· % 2 ^ params.forsHeight) hEq
  rw [Nat.mul_comm _ (2 ^ params.forsHeight), Nat.mul_add_mod, Nat.mod_eq_of_lt hu₁,
    Nat.mul_comm _ (2 ^ params.forsHeight), Nat.mul_add_mod, Nat.mod_eq_of_lt hu₂] at hModU
  have hDivU := congrArg (· / 2 ^ params.forsHeight) hEq
  rw [Nat.mul_comm _ (2 ^ params.forsHeight), Nat.mul_add_div hPowPos, Nat.div_eq_of_lt hu₁,
    Nat.add_zero, Nat.mul_comm _ (2 ^ params.forsHeight), Nat.mul_add_div hPowPos,
    Nat.div_eq_of_lt hu₂, Nat.add_zero] at hDivU
  have hTPos : 0 < params.forsTrees := Nat.lt_of_le_of_lt (Nat.zero_le _) hj₁
  have hModJ := congrArg (· % params.forsTrees) hDivU
  rw [Nat.mul_comm l₁, Nat.mul_add_mod, Nat.mod_eq_of_lt hj₁,
    Nat.mul_comm l₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hj₂] at hModJ
  have hDivJ := congrArg (· / params.forsTrees) hDivU
  rw [Nat.mul_comm l₁, Nat.mul_add_div hTPos, Nat.div_eq_of_lt hj₁, Nat.add_zero,
    Nat.mul_comm l₂, Nat.mul_add_div hTPos, Nat.div_eq_of_lt hj₂, Nat.add_zero] at hDivJ
  exact ⟨hDivJ, hModJ, hModU⟩

/-- Keyed FORS subset selector `hmsg rRand msg` for `Spec.itsrGame`. -/
def forsGlobalSubsetSelector (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (rRand msg : Spec.Bytes) : List Nat :=
  match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot
      (thPreHash suite pk.pkSeed pk.pkRoot msg) with
  | some (leafIdx, idxs) =>
    (List.range params.forsTrees).map fun j =>
      encodeForsGlobalPos params leafIdx j (idxs.getD j 0)
  | none => []

/-- Explicit-randomizer signer core returning a self-verified `PqHashSig` with `sig.rRand = rRand`. -/
def seqSignWithRand (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (q : ProdSigningQuery) (rRand : List UInt8) : Option PqHashSig :=
  let sk0 : PqSecretKey := ⟨skSeed, [], pkSeed⟩
  let pk := derivePublicKey suite params sk0
  let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
  if params.statefulJorts then
    if !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch then none
    else signProductionHypertreeCore suite params sk0 pk q.message mu rRand q.epoch none q.grindLimit
  else
    if !params.productionWellFormed then none
    else
      match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
      | none => none
      | some (leafGlobalIdx, forsIdxs) =>
        signProductionHypertreeCore suite params sk0 pk q.message mu rRand leafGlobalIdx
          (some forsIdxs) q.grindLimit

theorem seqSignWithRand_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed skSeed : List UInt8) (q : ProdSigningQuery) (rRand : List UInt8) (sig : PqHashSig)
    (h : seqSignWithRand suite params pkSeed skSeed q rRand = some sig) :
    sig.rRand = rRand ∧
    verifyProductionPqHashSig suite params (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩)
      q.message sig = true := by
  have coreSound : ∀ leaf fi,
      signProductionHypertreeCore suite params ⟨skSeed, [], pkSeed⟩
        (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩) q.message
        (thPreHash suite (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩).pkSeed
          (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩).pkRoot q.message)
        rRand leaf fi q.grindLimit = some sig →
      sig.rRand = rRand ∧
      verifyProductionPqHashSig suite params (derivePublicKey suite params ⟨skSeed, [], pkSeed⟩)
        q.message sig = true := by
    intro leaf fi hc
    rw [signProductionHypertreeCore_def] at hc; dsimp only at hc
    cases h1 : (if params.statefulJorts = true then some ([], _) else _) with
    | none => rw [h1] at hc; cases hc
    | some fc =>
      rcases fc with ⟨forsOpenings, curRoot⟩; rw [h1] at hc; dsimp only at hc
      cases h2 : signProductionHypertreeLayers suite params _ _ rRand q.grindLimit 0 leaf curRoot
          params.numLayers with
      | none => rw [h2] at hc; cases hc
      | some layerSigs =>
        rw [h2] at hc; dsimp only at hc
        let built : PqHashSig := ⟨rRand, 0, leaf, forsOpenings, layerSigs⟩
        cases hV : verifyProductionPqHashSig suite params _ q.message built
        · change (if verifyProductionPqHashSig suite params _ q.message built = true then
              some built else none) = some sig at hc
          rw [hV] at hc; cases hc
        · change (if verifyProductionPqHashSig suite params _ q.message built = true then
              some built else none) = some sig at hc
          rw [hV] at hc; injection hc with hEq; subst hEq; exact ⟨rfl, hV⟩
  unfold seqSignWithRand at h; dsimp only at h
  cases hSt : params.statefulJorts <;> rw [hSt] at h
  · cases hWf : (!params.productionWellFormed) <;> rw [hWf] at h
    · cases hD : deriveProductionStatelessInputs suite params rRand _ _ _ <;> rw [hD] at h
      · cases h
      · exact coreSound _ _ h
    · cases h
  · cases hG : (!params.productionWellFormed || !params.productionLeafIdxInRange q.epoch) <;>
      rw [hG] at h
    · exact coreSound _ _ h
    · cases h

/-- Sequential-randomizer adaptive tree evaluation threading `(signLog, itsrLog)` in lockstep with
    `Spec.itsrOracle`. -/
def evalSeqRandTree (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) (rand : Nat → Spec.Bytes) :
    ProdAdaptiveTree (List UInt8 × PqHashSig) → Nat → List (List UInt8 × PqHashSig) →
    List (Spec.Bytes × Spec.Bytes) →
    (List UInt8 × PqHashSig) × List (List UInt8 × PqHashSig) × List (Spec.Bytes × Spec.Bytes)
  | .pure out, _, sLog, iLog => (out, sLog, iLog)
  | .hashQuery x next, lo, sLog, iLog =>
    evalSeqRandTree latchOn suite params pkSeed secFn rand (next (suite.rawHash x)) lo sLog iLog
  | .signQuery q next, lo, sLog, iLog =>
    if latchOn = false ∨ lo ≤ q.epoch then
      if (if params.statefulJorts then
            !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
          else !params.productionWellFormed) then
        evalSeqRandTree latchOn suite params pkSeed secFn rand (next none) (q.epoch + 1) sLog iLog
      else
        let rRand := rand iLog.length
        let sigOpt := seqSignWithRand (secOverlaySuite suite pkSeed secFn) params pkSeed [] q rRand
        let sLog' := match sigOpt with | some sig => sLog ++ [(q.message, sig)] | none => sLog
        let iLog' := iLog ++ [(rRand, q.message)]
        evalSeqRandTree latchOn suite params pkSeed secFn rand (next sigOpt) (q.epoch + 1) sLog' iLog'
    else
      evalSeqRandTree latchOn suite params pkSeed secFn rand (next none) lo sLog iLog

/-- Interactive `Spec.Code Spec.byteOracleIface` tree runner querying `Spec.itsrOracle` on each
    admitted well-formed signing request. -/
def itsrHopTreeCode (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) :
    ProdAdaptiveTree (List UInt8 × PqHashSig) → Nat →
    Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes)
  | .pure (msgStar, sigStar), _ => .ret (sigStar.rRand, msgStar)
  | .hashQuery x next, lo =>
    itsrHopTreeCode latchOn suite params pkSeed secFn (next (suite.rawHash x)) lo
  | .signQuery q next, lo =>
    if latchOn = false ∨ lo ≤ q.epoch then
      if (if params.statefulJorts then
            !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
          else !params.productionWellFormed) then
        itsrHopTreeCode latchOn suite params pkSeed secFn (next none) (q.epoch + 1)
      else
        .call q.message (fun rRand =>
          let sigOpt := seqSignWithRand (secOverlaySuite suite pkSeed secFn) params pkSeed [] q rRand
          itsrHopTreeCode latchOn suite params pkSeed secFn (next sigOpt) (q.epoch + 1))
    else
      itsrHopTreeCode latchOn suite params pkSeed secFn (next none) lo

/-- **Interactive `ITSR` Reduction Adversary (`itsrHopReductionAdv`)** in `Spec.Within qSign`. -/
@[expose] def itsrHopReductionAdv {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) :=
  let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
  itsrHopTreeCode latchOn suite params pkSeed secFn ((canonicalizeAdvOptRand A).run pk) 0

private theorem itsrHopTreeCode_within (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat),
      ProdDualBounded qH qS t →
      Spec.Within qS (itsrHopTreeCode latchOn suite params pkSeed secFn t lo)
  | _, qS, .pure (_, _), _, _ => .ret qS _
  | 0, _, .hashQuery _ _, _, h => False.elim h
  | _ + 1, _, .hashQuery x next, lo, h =>
    itsrHopTreeCode_within latchOn suite params pkSeed secFn (next (suite.rawHash x)) lo (h _)
  | _, 0, .signQuery _ _, _, h => False.elim h
  | _, qS + 1, .signQuery q next, lo, h => by
    unfold itsrHopTreeCode
    if hAdm : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hAdm]
      if hG : (if params.statefulJorts then
            !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
          else !params.productionWellFormed) = true then
        rw [ite_eq_left hG]
        exact Spec.Within.mono (Nat.le_succ qS)
          (itsrHopTreeCode_within latchOn suite params pkSeed secFn (next none) (q.epoch + 1)
            (h none))
      else
        rw [ite_eq_right hG]
        exact .call (E := Spec.byteOracleIface) _ _ (fun _ =>
          itsrHopTreeCode_within latchOn suite params pkSeed secFn _ (q.epoch + 1) (h _))
    else
      rw [ite_eq_right hAdm]
      exact Spec.Within.mono (Nat.le_succ qS)
        (itsrHopTreeCode_within latchOn suite params pkSeed secFn (next none) lo (h none))

theorem itsrHopReductionAdv_within {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within qSign (itsrHopReductionAdv latchOn suite params pkSeed secFn A) :=
  itsrHopTreeCode_within latchOn suite params pkSeed secFn _ 0
    ((canonicalizeAdvOptRand A).bounded _)

private theorem itsrHopTreeCode_play (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (qItsr : Nat) (rand : Nat → Spec.Bytes) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat)
      (sLog : List (List UInt8 × PqHashSig)) (iLog : List (Spec.Bytes × Spec.Bytes)),
      ProdDualBounded qH qS t →
      iLog.length + qS ≤ qItsr →
      let ev := evalSeqRandTree latchOn suite params pkSeed secFn rand t lo sLog iLog
      Spec.Code.play (Spec.itsrOracle qItsr rand)
          (itsrHopTreeCode latchOn suite params pkSeed secFn t lo) iLog =
        ((ev.1.2.rRand, ev.1.1), ev.2.2)
  | _, _, .pure (_, _), _, _, _, _, _ => by
    unfold itsrHopTreeCode evalSeqRandTree
    rw [Spec.Code.play_ret]
  | 0, _, .hashQuery _ _, _, _, _, hB, _ => False.elim hB
  | _ + 1, _, .hashQuery x next, lo, sLog, iLog, hB, hBudget =>
    itsrHopTreeCode_play latchOn suite params pkSeed secFn qItsr rand
      (next (suite.rawHash x)) lo sLog iLog (hB _) hBudget
  | _, 0, .signQuery _ _, _, _, _, hB, _ => False.elim hB
  | _, qS + 1, .signQuery q next, lo, sLog, iLog, hB, hBudget => by
    unfold itsrHopTreeCode evalSeqRandTree
    if hAdm : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hAdm, ite_eq_left hAdm]
      if hG : (if params.statefulJorts then
            !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
          else !params.productionWellFormed) = true then
        rw [ite_eq_left hG, ite_eq_left hG]
        exact itsrHopTreeCode_play latchOn suite params pkSeed secFn qItsr rand
          (next none) (q.epoch + 1) sLog iLog (hB none)
          (Decidable.byContradiction (fun _ => by omega))
      else
        rw [ite_eq_right hG, ite_eq_right hG, Spec.Code.play_call, Spec.itsrOracle_eq]
        have hLt : iLog.length < qItsr := Decidable.byContradiction (fun _ => by omega)
        rw [ite_eq_left hLt]
        dsimp only
        refine itsrHopTreeCode_play latchOn suite params pkSeed secFn qItsr rand _ (q.epoch + 1)
          _ (iLog ++ [(rand iLog.length, q.message)]) (hB _) ?_
        rw [List.length_append, List.length_singleton]
        exact Decidable.byContradiction (fun _ => by omega)
    else
      rw [ite_eq_right hAdm, ite_eq_right hAdm]
      exact itsrHopTreeCode_play latchOn suite params pkSeed secFn qItsr rand
        (next none) lo sLog iLog (hB none)
        (Decidable.byContradiction (fun _ => by omega))

private theorem evalSeqRandTree_log_props (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (rand : Nat → Spec.Bytes) :
    ∀ (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat)
      (sLog : List (List UInt8 × PqHashSig)) (iLog : List (Spec.Bytes × Spec.Bytes)),
      let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
      let ev := evalSeqRandTree latchOn suite params pkSeed secFn rand t lo sLog iLog
      (∀ e ∈ sLog, verifyProductionPqHashSig suite params pk e.1 e.2 = true ∧
        (e.2.rRand, e.1) ∈ iLog) →
      ∀ e ∈ ev.2.1, verifyProductionPqHashSig suite params pk e.1 e.2 = true ∧
        (e.2.rRand, e.1) ∈ ev.2.2
  | .pure _, _, _, _, hInv => hInv
  | .hashQuery x next, lo, sLog, iLog, hInv =>
    evalSeqRandTree_log_props latchOn suite params pkSeed secFn rand
      (next (suite.rawHash x)) lo sLog iLog hInv
  | .signQuery q next, lo, sLog, iLog, hInv => by
    unfold evalSeqRandTree
    if hAdm : latchOn = false ∨ lo ≤ q.epoch then
      rw [ite_eq_left hAdm]
      if hG : (if params.statefulJorts then
            !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch
          else !params.productionWellFormed) = true then
        rw [ite_eq_left hG]
        exact evalSeqRandTree_log_props latchOn suite params pkSeed secFn rand
          (next none) (q.epoch + 1) sLog iLog hInv
      else
        rw [ite_eq_right hG]
        dsimp only
        refine evalSeqRandTree_log_props latchOn suite params pkSeed secFn rand
          _ (q.epoch + 1) _ _ (fun e he => ?_)
        cases hSig : seqSignWithRand (secOverlaySuite suite pkSeed secFn) params pkSeed [] q
            (rand iLog.length) with
        | none =>
          rw [hSig] at he
          obtain ⟨hV, hM⟩ := hInv e he
          exact ⟨hV, List.mem_append_left _ hM⟩
        | some sig =>
          rw [hSig] at he
          rcases List.mem_append.mp he with hOld | hSingle
          · obtain ⟨hV, hM⟩ := hInv e hOld
            exact ⟨hV, List.mem_append_left _ hM⟩
          · have hEq := List.mem_singleton.mp hSingle
            subst hEq
            obtain ⟨hR, hVSov⟩ := seqSignWithRand_sound (secOverlaySuite suite pkSeed secFn)
              params pkSeed [] q (rand iLog.length) sig hSig
            have hPkEq : derivePublicKey (secOverlaySuite suite pkSeed secFn) params
                ⟨[], [], pkSeed⟩ = derivePublicKeyIdealPrf suite params pkSeed secFn := by
              rw [derivePublicKeyIdealPrf.public_eqs]
            rw [secOverlaySuite_verify_eq, hPkEq] at hVSov
            refine ⟨hVSov, List.mem_append_right _ ?_⟩
            dsimp only; rw [hR]; exact .head _
    else
      rw [ite_eq_right hAdm]
      exact evalSeqRandTree_log_props latchOn suite params pkSeed secFn rand
        (next none) lo sLog iLog hInv

/-- When `params.statefulJorts = true` (or `params.forsTrees = 0`), `ExplicitItsrCover` has `0` loss. -/
theorem stateful_itsr_zero_bound {n : Nat} (hPos : 0 < n) (suite : TweakableHashSuite)
    (params : PqHashParams) (hNoFors : params.statefulJorts = true ∨ params.forsTrees = 0)
    (pkOf : Fin n → PqPublicKey) (logOf : Fin n → List (List UInt8 × PqHashSig))
    (msgOf : Fin n → List UInt8) (sigOf : Fin n → PqHashSig) (ev : Fin n → Bool)
    (hImp : ∀ ω, ev ω = true →
      ExplicitItsrCover suite params (pkOf ω) (logOf ω) (msgOf ω) (sigOf ω)) :
    Spec.GameBound (Spec.FinGame.mk hPos ev).winProb Spec.RatBound.zero := by
  refine Spec.FinGame.bound_zero_of_forall_lose _ (fun ω => ?_)
  dsimp only; cases hE : ev ω
  · rfl
  · exfalso; have hBrk := hImp ω hE
    rcases hNoFors with hSt | hZ
    · exact Bool.noConfusion (hBrk.stateless.symm.trans hSt)
    · exact Nat.ne_of_gt hBrk.trees_pos hZ

/-- `ExplicitItsrCover` implies `Spec.itsrWin` on `forsGlobalSubsetSelector` whenever every logged
    signature `(m, s) ∈ log` has `(s.rRand, m) ∈ itsrLog` and `(sigStar.rRand, msgStar) ∉ itsrLog`. -/
theorem explicitItsrCover_implies_itsrWin (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig))
    (itsrLog : List (Spec.Bytes × Spec.Bytes)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hAccept : verifyProductionPqHashSig suite params pk msgStar sigStar = true)
    (hLogAccept : ∀ e ∈ log, verifyProductionPqHashSig suite params pk e.1 e.2 = true)
    (hLogSub : ∀ e ∈ log, (e.2.rRand, e.1) ∈ itsrLog)
    (hFreshItsr : (sigStar.rRand, msgStar) ∉ itsrLog)
    (hBrk : ExplicitItsrCover suite params pk log msgStar sigStar) :
    Spec.itsrWin (forsGlobalSubsetSelector suite params pk) itsrLog (sigStar.rRand, msgStar) =
      true := by
  rw [Spec.itsrWin_eq, Bool.and_eq_true]
  refine ⟨by rw [decide_eq_false hFreshItsr]; rfl, ?_⟩
  obtain ⟨_, _, _, idxsStar, _, hDStar, _, _⟩ :=
    verifyProductionPqHashSig_stateless_inv suite params pk msgStar sigStar hBrk.stateless hAccept
  unfold forsGlobalSubsetSelector
  dsimp only
  rw [hDStar, List.all_eq_true]
  intro x hx
  obtain ⟨j, hjR, rfl⟩ := List.mem_map.mp hx
  have hMemSig : (sigStar.leafGlobalIdx, j,
      (prodSigForsIdxs suite params pk msgStar sigStar).getD j 0) ∈
      prodSigForsLeaves suite params pk msgStar sigStar :=
    List.mem_map.mpr ⟨j, hjR, rfl⟩
  obtain ⟨e, he, hMemE⟩ := hBrk.covered _ hMemSig
  unfold prodSigForsLeaves at hMemE
  obtain ⟨j', _, hEqTup⟩ := List.mem_map.mp hMemE
  have hLeafEq : e.2.leafGlobalIdx = sigStar.leafGlobalIdx := congrArg Prod.fst hEqTup
  have hjEq : j' = j := congrArg (fun p => p.2.1) hEqTup
  have hIdxEq : (prodSigForsIdxs suite params pk e.1 e.2).getD j' 0 =
      (prodSigForsIdxs suite params pk msgStar sigStar).getD j 0 :=
    congrArg (fun p => p.2.2) hEqTup
  subst j'
  obtain ⟨_, _, _, idxsE, _, hDE, _, _⟩ :=
    verifyProductionPqHashSig_stateless_inv suite params pk e.1 e.2 hBrk.stateless (hLogAccept e he)
  have hIdxsS : prodSigForsIdxs suite params pk msgStar sigStar = idxsStar := by
    unfold prodSigForsIdxs; rw [hDStar]
  have hIdxsE : prodSigForsIdxs suite params pk e.1 e.2 = idxsE := by
    unfold prodSigForsIdxs; rw [hDE]
  rw [List.any_eq_true]
  refine ⟨(e.2.rRand, e.1), hLogSub e he, decide_eq_true ?_⟩
  dsimp only; rw [hDE]
  exact List.mem_map.mpr ⟨j, hjR, by rw [hLeafEq, ← hIdxsE, hIdxEq, hIdxsS]⟩

/-- **Hop 4a Interactive `ITSR` Reduction (`hulsing_hop4a_itsr_bound`)** into `Spec.ItsrHard`. -/
theorem hulsing_hop4a_itsr_bound {n nC nA qHash qSign : Nat} (latchOn : Bool) (hPos : 0 < n)
    (suite : TweakableHashSuite) (params : PqHashParams) (randLen qItsr : Nat)
    (hqItsr : qSign ≤ qItsr)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (π : Spec.CoinSplit n nC nA)
    (rand : Fin nC → List Spec.Bytes) (hRand : Spec.UniformOn (Spec.ItsrSampleOk randLen qItsr) rand)
    (advA : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (itsrEv : Fin n → Bool)
    (hEvImp : ∀ ω, itsrEv ω = true →
      let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
      let ev := evalSeqRandTree latchOn suite params pkSeed secFn
        (fun i => (rand (π.chal ω)).getD i [])
        ((canonicalizeAdvOptRand (advA (π.advc ω))).run pk) 0 [] []
      verifyProductionPqHashSig suite params pk ev.1.1 ev.1.2 = true ∧
      (ev.1.2.rRand, ev.1.1) ∉ ev.2.2 ∧
      ExplicitItsrCover suite params pk ev.2.1 ev.1.1 ev.1.2)
    {𝒜Itsr : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop}
    (hClassItsr : ∀ a, 𝒜Itsr (itsrHopReductionAdv latchOn suite params pkSeed secFn (advA a)))
    {εItsr : Spec.RatBound}
    (hItsr : Spec.ItsrHard 𝒜Itsr
      (forsGlobalSubsetSelector suite params (derivePublicKeyIdealPrf suite params pkSeed secFn))
      randLen qItsr εItsr) :
    Spec.GameBound (Spec.FinGame.mk hPos itsrEv).winProb εItsr := by
  let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
  let B : Fin nA → Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) := fun a =>
    itsrHopReductionAdv latchOn suite params pkSeed secFn (advA a)
  have hGameB := hItsr n nC nA hPos π rand hRand B hClassItsr
  refine Spec.GameBound.trans (Spec.event_le_reduction_win (Spec.FinGame.mk hPos itsrEv) _
    (fun ω hE => ?_)) hGameB
  obtain ⟨hAcc, hNotIn, hCov⟩ := hEvImp ω hE
  rw [Spec.itsrGame_win, Spec.itsrRun_eq]
  dsimp only [B, itsrHopReductionAdv]
  have hPlay := itsrHopTreeCode_play latchOn suite params pkSeed secFn qItsr
    (fun i => (rand (π.chal ω)).getD i [])
    ((canonicalizeAdvOptRand (advA (π.advc ω))).run pk) 0 [] []
    ((canonicalizeAdvOptRand (advA (π.advc ω))).bounded pk)
    (by rw [List.length_nil, Nat.zero_add]; exact hqItsr)
  rw [hPlay]
  have hLogs := evalSeqRandTree_log_props latchOn suite params pkSeed secFn
    (fun i => (rand (π.chal ω)).getD i [])
    ((canonicalizeAdvOptRand (advA (π.advc ω))).run pk) 0 [] [] (fun _ h => nomatch h)
  exact explicitItsrCover_implies_itsrWin suite params pk _ _ _ _ hAcc
    (fun e he => (hLogs e he).1) (fun e he => (hLogs e he).2) hNotIn hCov

/-! ## §2. Interactive `Spec.smDtTcrGame` (`Spec.SmDtTcrHard`) & Open-Seed `SM-DT-TCR` Reductions -/

/-- Commit an explicit list of `(tweak, msg)` targets sequentially before running `cont`. -/
def commitTargetsThen : List (Spec.Bytes × Spec.Bytes) →
    Spec.Code Spec.targetIface Spec.TargetBreak → Spec.Code Spec.targetIface Spec.TargetBreak
  | [], cont => cont
  | (t, m) :: rest, cont => .call (.target t m) (fun _ => commitTargetsThen rest cont)

theorem commitTargetsThen_within :
    ∀ (targets : List (Spec.Bytes × Spec.Bytes)) {b : Nat}
      {cont : Spec.Code Spec.targetIface Spec.TargetBreak},
      Spec.Within b cont → Spec.Within (targets.length + b) (commitTargetsThen targets cont)
  | [], _, _, hC => by rw [List.length_nil, Nat.zero_add]; exact hC
  | (_, _) :: rest, b, _, hC => by
    unfold commitTargetsThen
    rw [List.length_cons, Nat.succ_add]
    exact .call _ _ (fun _ => commitTargetsThen_within rest hC)

private theorem commitTargetsThen_play (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (qTcr : Nat) (cont : Spec.Code Spec.targetIface Spec.TargetBreak) :
    ∀ (targets : List (Spec.Bytes × Spec.Bytes)) (st : Spec.TargetState),
      st.revealed = false →
      st.targets.length + targets.length ≤ qTcr →
      (targets.map Prod.fst).Nodup →
      (∀ t ∈ targets.map Prod.fst, t ∉ st.targets.map Prod.fst) →
      Spec.Code.play (Spec.smDtTcrOracle th qTcr) (commitTargetsThen targets cont) st =
        Spec.Code.play (Spec.smDtTcrOracle th qTcr) cont { st with targets := st.targets ++ targets }
  | [], st, _, _, _, _ => by unfold commitTargetsThen; rw [List.append_nil]
  | (t, m) :: rest, st, hRev, hLen, hNd, hDisj => by
    unfold commitTargetsThen
    rw [List.length_cons] at hLen
    have hLt : st.targets.length < qTcr := Decidable.byContradiction (fun _ => by omega)
    have htNot : t ∉ st.targets.map Prod.fst := hDisj t List.mem_cons_self
    have hc : st.revealed = false ∧ st.targets.length < qTcr ∧ t ∉ st.targets.map Prod.fst :=
      ⟨hRev, hLt, htNot⟩
    rw [Spec.Code.play_call, Spec.smDtTcrOracle_target, ite_eq_left hc]
    dsimp only
    obtain ⟨htNotRest, hNdRest⟩ := List.nodup_cons.mp hNd
    have hPlayRest := commitTargetsThen_play th qTcr cont rest
      { st with targets := st.targets ++ [(t, m)] } hRev
      (by rw [List.length_append, List.length_singleton]; exact Decidable.byContradiction (fun _ => by omega))
      hNdRest
      (fun t' ht' hInApp => by
        rw [List.map_append, List.map_singleton] at hInApp
        rcases List.mem_append.mp hInApp with hInOld | hInSingle
        · exact hDisj t' (List.mem_cons_of_mem t ht') hInOld
        · have hEqT := List.mem_singleton.mp hInSingle
          exact htNotRest (hEqT ▸ ht'))
    rw [hPlayRest, List.append_assoc]
    rfl

/-- **Pre-Reveal Multi-Target `SM-DT-TCR` Reduction (`preCommittedTcrAdv`)** into `Spec.smDtTcrGame`. -/
@[expose] def preCommittedTcrAdv {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (targets : List (Spec.Bytes × Spec.Bytes)) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) : Spec.Code Spec.targetIface Spec.TargetBreak :=
  commitTargetsThen targets
    (.call .reveal fun seedOpt =>
      .ret (match extractIdealPrfTcrWitnessOpt latchOn suite params hw (seedOpt.getD []) rfMsg secFn
          hRf hOneTimeIfSt A with
        | some w => w.brk
        | none => ⟨[], [], []⟩))

theorem preCommittedTcrAdv_within {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (targets : List (Spec.Bytes × Spec.Bytes)) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within (targets.length + 1)
      (preCommittedTcrAdv latchOn suite params hw targets rfMsg secFn hRf hOneTimeIfSt A) :=
  commitTargetsThen_within targets (.call _ _ (fun _ => .ret 0 _))

/-- **Tight `1×` Pre-Reveal `SM-DT-TCR` Bound (`hulsing_hop4b_smDtTcr_precommitted_bound`)**
    directly under `Spec.SmDtTcrHard`. -/
theorem hulsing_hop4b_smDtTcr_precommitted_bound {n nC nA qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (seedLen qTcr : Nat)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true) (π : Spec.CoinSplit n nC nA)
    (seed : Fin nC → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (targetsA : Fin nA → List (Spec.Bytes × Spec.Bytes))
    (hNd : ∀ a, ((targetsA a).map Prod.fst).Nodup) (hLen : ∀ a, (targetsA a).length ≤ qTcr)
    (rfMsgA secFnA : Fin nA → Spec.Bytes → Spec.Bytes)
    (hRfA : ∀ a x, x.length = 65 → (rfMsgA a x).length = 32)
    (advA : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Tcr : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ a, 𝒜Tcr (preCommittedTcrAdv latchOn suite params hw (targetsA a)
      (rfMsgA a) (secFnA a) (hRfA a) hOneTimeIfSt (advA a)))
    {εTcr : Spec.RatBound} (hTcr : Spec.SmDtTcrHard 𝒜Tcr (suiteTweakHash suite) seedLen qTcr εTcr) :
    let preComEv : Fin n → Bool := fun ω =>
      match extractIdealPrfTcrWitnessOpt latchOn suite params hw (seed (π.chal ω))
          (rfMsgA (π.advc ω)) (secFnA (π.advc ω)) (hRfA (π.advc ω)) hOneTimeIfSt (advA (π.advc ω)) with
      | some w => decide ((w.brk.tweak, w.brk.committed) ∈ targetsA (π.advc ω))
      | none => false
    Spec.GameBound (Spec.FinGame.mk hPos preComEv).winProb εTcr := by
  intro preComEv
  let B : Fin nA → Spec.Code Spec.targetIface Spec.TargetBreak := fun a =>
    preCommittedTcrAdv latchOn suite params hw (targetsA a) (rfMsgA a) (secFnA a)
      (hRfA a) hOneTimeIfSt (advA a)
  have hGameB := hTcr n nC nA hPos π seed hSeed B hClass
  refine Spec.GameBound.trans (Spec.event_le_reduction_win (Spec.FinGame.mk hPos preComEv) _
    (fun ω hEv => ?_)) hGameB
  dsimp only [preComEv] at hEv
  cases hEx : extractIdealPrfTcrWitnessOpt latchOn suite params hw (seed (π.chal ω))
      (rfMsgA (π.advc ω)) (secFnA (π.advc ω)) (hRfA (π.advc ω)) hOneTimeIfSt
      (advA (π.advc ω)) with
  | none => rw [hEx] at hEv; cases hEv
  | some w =>
    rw [hEx] at hEv
    have hMemT : (w.brk.tweak, w.brk.committed) ∈ targetsA (π.advc ω) := of_decide_eq_true hEv
    rw [Spec.smDtTcrGame_win, Spec.smDtTcrRun_eq]
    dsimp only [B, preCommittedTcrAdv]
    let cont : Spec.Code Spec.targetIface Spec.TargetBreak :=
      .call .reveal fun seedOpt =>
        .ret (match extractIdealPrfTcrWitnessOpt latchOn suite params hw (seedOpt.getD [])
            (rfMsgA (π.advc ω)) (secFnA (π.advc ω)) (hRfA (π.advc ω)) hOneTimeIfSt
            (advA (π.advc ω)) with
          | some w' => w'.brk
          | none => ⟨[], [], []⟩)
    have hPlay := commitTargetsThen_play (suiteTweakHash suite) qTcr cont (targetsA (π.advc ω))
      ⟨seed (π.chal ω), [], false⟩ rfl
      (by rw [List.length_nil, Nat.zero_add]; exact hLen (π.advc ω))
      (hNd (π.advc ω)) (fun _ _ h => nomatch h)
    rw [hPlay, List.nil_append]
    dsimp only [cont]
    rw [Spec.Code.play_call, Spec.smDtTcrOracle_reveal, Spec.Code.play_ret]
    dsimp only [Option.getD]
    rw [hEx, Spec.smDtTcrWin_eq]
    dsimp only
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hMemT,
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true w.ne, decide_eq_true w.collides⟩⟩

/-- **Adaptive Open-Seed `SM-DT-TCR` Challenger (`smDtOpenSeedTcrOracle`)** (`[HK22]` / `FIPS 205`):
    allows distinct-tweak target commitments up to budget `q` both before and after `.reveal`,
    capturing Merkle-node and `H_msg` targets whose inputs depend on `pkSeed` and adaptive
    signing queries `q.message`. -/
def smDtOpenSeedTcrOracle (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes) (q : Nat)
    (st : Spec.TargetState) : (qr : Spec.targetIface.Query) → Spec.targetIface.Resp qr × Spec.TargetState
  | .target t m =>
    if st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      (some (th st.seed t m), { st with targets := st.targets ++ [(t, m)] })
    else (none, st)
  | .reveal => (some st.seed, { st with revealed := true })

def smDtOpenSeedTcrGame {n : Nat} (hPos : 0 < n)
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes) (q : Nat)
    (seed : Fin n → Spec.Bytes) (adv : Fin n → Spec.Code Spec.targetIface Spec.TargetBreak) :
    Spec.FinGame n :=
  ⟨hPos, fun ω =>
    let r := Spec.Code.play (smDtOpenSeedTcrOracle th q) (adv ω) ⟨seed ω, [], false⟩
    Spec.smDtTcrWin th r.2 r.1⟩

/-- **Open-Seed `SM-DT-TCR` Hardness (`SmDtOpenSeedTcrHard`)** over `Spec.FinGame`. -/
@[expose] def SmDtOpenSeedTcrHard (𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop)
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes) (seedLen q : Nat)
    (ε : Spec.RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nC nA) (seed : Fin nC → Spec.Bytes),
    Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed →
    ∀ adv : Fin nA → Spec.Code Spec.targetIface Spec.TargetBreak, (∀ a : Fin nA, 𝒜 (adv a)) →
      Spec.GameBound (smDtOpenSeedTcrGame hPos th q (fun ω => seed (π.chal ω))
        (fun ω => adv (π.advc ω))).winProb ε

/-- **Interactive Open-Seed `SM-DT-TCR` Reduction (`openSeedTcrHopAdv`)** (`Spec.Within 2`).
    Calls `.reveal` to learn `pkSeed`, executes any unrestricted `pk`-dependent adaptive
    `(qHash, qSign)` adversary `A`, commits the extracted target, and returns `w.brk`. -/
@[expose] def openSeedTcrHopAdv {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Code Spec.targetIface Spec.TargetBreak :=
  .call .reveal fun seedOpt =>
    let pkSeed := seedOpt.getD []
    match extractIdealPrfTcrWitnessOpt latchOn suite params hw pkSeed rfMsg secFn
        hRf hOneTimeIfSt A with
    | some w => .call (.target w.brk.tweak w.brk.committed) (fun _ => .ret w.brk)
    | none => .ret ⟨[], [], []⟩

theorem openSeedTcrHopAdv_within {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (hRf : ∀ x, x.length = 65 → (rfMsg x).length = 32)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within 2
      (openSeedTcrHopAdv latchOn suite params hw rfMsg secFn hRf hOneTimeIfSt A) := by
  refine .call _ _ (fun seedOpt => ?_)
  dsimp only
  cases extractIdealPrfTcrWitnessOpt latchOn suite params hw (seedOpt.getD []) rfMsg secFn
      hRf hOneTimeIfSt A with
  | some _ => exact .call _ _ (fun _ => .ret 0 _)
  | none => exact .ret 1 _

/-- **Unconditional Tight `1×` Open-Seed `SM-DT-TCR` Bound (`hulsing_hop4b_openSeedTcr_tight_bound`)**
    across all 7 tweakable-hash roles and unrestricted `pk`-dependent adaptive adversaries. -/
theorem hulsing_hop4b_openSeedTcr_tight_bound {n nC nA qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (seedLen qTcr : Nat) (hqTcr : 0 < qTcr)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (π : Spec.CoinSplit n nC nA)
    (seed : Fin nC → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (rfMsgA secFnA : Fin nA → Spec.Bytes → Spec.Bytes)
    (hRfA : ∀ a x, x.length = 65 → (rfMsgA a x).length = 32)
    (advA : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Tcr : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ a, 𝒜Tcr (openSeedTcrHopAdv latchOn suite params hw
      (rfMsgA a) (secFnA a) (hRfA a) hOneTimeIfSt (advA a)))
    {εTcr : Spec.RatBound}
    (hTcr : SmDtOpenSeedTcrHard 𝒜Tcr (suiteTweakHash suite) seedLen qTcr εTcr) :
    let tcrEv : Fin n → Bool := fun ω =>
      (extractIdealPrfTcrWitnessOpt latchOn suite params hw (seed (π.chal ω))
        (rfMsgA (π.advc ω)) (secFnA (π.advc ω)) (hRfA (π.advc ω)) hOneTimeIfSt
        (advA (π.advc ω))).isSome
    Spec.GameBound (Spec.FinGame.mk hPos tcrEv).winProb εTcr := by
  intro tcrEv
  let B : Fin nA → Spec.Code Spec.targetIface Spec.TargetBreak := fun a =>
    openSeedTcrHopAdv latchOn suite params hw (rfMsgA a) (secFnA a)
      (hRfA a) hOneTimeIfSt (advA a)
  have hGameB := hTcr n nC nA hPos π seed hSeed B hClass
  refine Spec.GameBound.trans (Spec.event_le_reduction_win (Spec.FinGame.mk hPos tcrEv) _
    (fun ω hEv => ?_)) hGameB
  dsimp only [tcrEv] at hEv
  cases hEx : extractIdealPrfTcrWitnessOpt latchOn suite params hw (seed (π.chal ω))
      (rfMsgA (π.advc ω)) (secFnA (π.advc ω)) (hRfA (π.advc ω)) hOneTimeIfSt
      (advA (π.advc ω)) with
  | none => rw [hEx] at hEv; cases hEv
  | some w =>
    dsimp only [smDtOpenSeedTcrGame, B, openSeedTcrHopAdv]
    rw [Spec.Code.play_call]
    unfold smDtOpenSeedTcrOracle
    dsimp only [Option.getD]
    rw [hEx, Spec.Code.play_call, Spec.Code.play_ret]
    dsimp only
    have hc : ([] : List (Spec.Bytes × Spec.Bytes)).length < qTcr ∧
        w.brk.tweak ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst :=
      ⟨hqTcr, fun h => nomatch h⟩
    rw [ite_eq_left hc, Spec.smDtTcrWin_eq]
    dsimp only [List.nil_append]
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (.head _),
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true w.ne, decide_eq_true w.collides⟩⟩

/-- `#tooth` A constant tweakable hash is NOT `SmDtOpenSeedTcrHard` for any `ε` with `ε.num < ε.den`. -/
def constOpenSeedTcrAdv : Spec.Code Spec.targetIface Spec.TargetBreak :=
  .call (.target [] [0x00]) (fun _ => .ret ⟨[], [0x00], [0x01]⟩)

theorem smDtOpenSeedTcrHard_constHash_refuted {nC : Nat} (hPos : 0 < nC) (c : Spec.Bytes)
    (seedLen q : Nat) (hq : 0 < q) (seed : Fin nC → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop) (h𝒜 : 𝒜 constOpenSeedTcrAdv)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtOpenSeedTcrHard 𝒜 (fun _ _ _ => c) seedLen q ε := by
  intro hHard
  have hB := hHard nC nC 1 hPos (Spec.CoinSplit.challengerOnly nC) seed hSeed
    (fun _ => constOpenSeedTcrAdv) (fun _ => h𝒜)
  refine Spec.FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε hB
  dsimp only [smDtOpenSeedTcrGame, constOpenSeedTcrAdv]
  rw [Spec.Code.play_call, Spec.Code.play_ret]
  unfold smDtOpenSeedTcrOracle; dsimp only
  have hc : ([] : List (Spec.Bytes × Spec.Bytes)).length < q ∧
      ([] : Spec.Bytes) ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst :=
    ⟨hq, fun h => nomatch h⟩
  rw [ite_eq_left hc, Spec.smDtTcrWin_eq]
  simp only [List.nil_append, List.mem_cons, true_or, decide_true, Bool.true_and]
  decide

/-! ## §3. Interactive `Spec.smDtPreGame` (`Spec.SmDtPreHard`) + Hop-3 `SmDtUdHard` Reductions -/

/-- Every `ExplicitPreBreak` (both `.fors` and `.wots`) yields an explicit `suiteTweakHash`
    target preimage equation under `encodeChainFTweak`. -/
theorem explicitPreBreak_gives_tweakHash_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hBrk : ExplicitPreBreak suite (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩
      log msgStar sigStar) :
    (∃ (j : Nat) (adrs : HashAdrs),
      j < params.forsTrees ∧
      suiteTweakHash suite pkSeed (encodeChainFTweak adrs)
        (sigStar.forsOpenings.getD j ⟨[], []⟩).secretVal =
      forsIndexedLeafFn (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩
        (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) j
        ((prodSigForsIdxs suite params
          (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩)
          msgStar sigStar).getD j 0)) ∨
    (∃ (i r step : Nat) (adrs : HashAdrs),
      i < params.numLayers ∧ r < params.ell1 ∧ step + 1 ≤ params.w - 1 ∧
      suiteTweakHash suite pkSeed (encodeChainFTweak adrs)
        ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
      suiteTweakHash suite pkSeed (encodeChainFTweak adrs)
        (honestChainNode (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩
          (UInt32.ofNat i)
          (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
            2 ^ params.subtreeHeight))
          (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
          r step)) := by
  cases hBrk with
  | fors j hj _ _ _ _ hInv =>
    refine .inl ⟨j, forsLeafHashAdrs
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
      (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight) j
      ((prodSigForsIdxs suite params
        (derivePublicKey (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩)
        msgStar sigStar).getD j 0), hj, ?_⟩
    rw [suiteTweakHash_chainF, ← forsIndexedLeafHash_eq_chainF_adrs]
    exact hInv
  | wots i hi r hr step hstep _ hInv _ =>
    let treeI := UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
      2 ^ params.subtreeHeight)
    let kpI := sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight
    let adrs : HashAdrs := ⟨UInt32.ofNat i, treeI, .wotsHash, UInt32.ofNat kpI,
      UInt32.ofNat r, UInt32.ofNat step⟩
    refine .inr ⟨i, r, step, adrs, hi, hr, hstep, ?_⟩
    rw [suiteTweakHash_chainF, suiteTweakHash_chainF, ← honestChainNode_secOv_succ]
    exact hInv

/-- **Interactive Punctured-Slot `SM-DT-PRE` Reduction (`puncturedSlotPreAdv`)** (`Spec.Within 2`,
    zero `hCand` restriction!).
    Calls `.target targetTweak []` to receive `yTarget`, calls `.reveal` to receive `pkSeed`,
    reconstructs `pkSim pkSeed yTarget` and `signSim pkSeed yTarget`, runs the unrestricted
    `pk`-dependent adaptive `(qHash, qSign)` adversary `A`, and outputs the forged preimage. -/
@[expose] def puncturedSlotPreAdv {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (targetTweak : Spec.Bytes)
    (pkSim : Spec.Bytes → Spec.Bytes → PqPublicKey)
    (signSim : Spec.Bytes → Spec.Bytes → ProdSigningQuery → Option PqHashSig)
    (extractCand : (List UInt8 × PqHashSig) → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Code Spec.targetIface Spec.TargetBreak :=
  .call (.target targetTweak []) fun yOpt =>
    .call .reveal fun seedOpt =>
      let yTarget := yOpt.getD []
      let pkSeed := seedOpt.getD []
      let pk := pkSim pkSeed yTarget
      let out := (evalLatchedAdaptiveTree latchOn suite.rawHash (signSim pkSeed yTarget)
        ((canonicalizeAdvOptRand A).run pk) 0).1
      .ret ⟨targetTweak, [], extractCand out⟩

theorem puncturedSlotPreAdv_within {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (targetTweak : Spec.Bytes)
    (pkSim : Spec.Bytes → Spec.Bytes → PqPublicKey)
    (signSim : Spec.Bytes → Spec.Bytes → ProdSigningQuery → Option PqHashSig)
    (extractCand : (List UInt8 × PqHashSig) → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within 2
      (puncturedSlotPreAdv latchOn suite targetTweak pkSim signSim extractCand A) :=
  .call _ _ (fun _ => .call _ _ (fun _ => .ret 0 _))

/-- **Hop 4c Interactive `SM-DT-PRE` Bound (`hulsing_hop4c_smDtPre_interactive_bound`)**
    directly under `Spec.SmDtPreHard` (`0` `hCand` restriction!). -/
theorem hulsing_hop4c_smDtPre_interactive_bound {n nC nA qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite)
    (seedLen inputLen qPre : Nat) (hqPre : 0 < qPre)
    (targetTweak : Spec.Bytes)
    (pkSim : Fin nA → Spec.Bytes → Spec.Bytes → PqPublicKey)
    (signSim : Fin nA → Spec.Bytes → Spec.Bytes → ProdSigningQuery → Option PqHashSig)
    (extractCand : Fin nA → (List UInt8 × PqHashSig) → Spec.Bytes)
    (π : Spec.CoinSplit n nC nA)
    (sample : Fin nC → Spec.Bytes × List Spec.Bytes)
    (hSample : Spec.UniformOn (Spec.SmDtPreSampleOk seedLen inputLen qPre) sample)
    (advA : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (slotWin : Fin n → Bool)
    (hSlotImp : ∀ ω, slotWin ω = true →
      let pkSeed := (sample (π.chal ω)).1
      let hidden0 := (sample (π.chal ω)).2.getD 0 []
      let yTarget := suiteTweakHash suite pkSeed targetTweak hidden0
      let a := π.advc ω
      let out := (evalLatchedAdaptiveTree latchOn suite.rawHash (signSim a pkSeed yTarget)
        ((canonicalizeAdvOptRand (advA a)).run (pkSim a pkSeed yTarget)) 0).1
      suiteTweakHash suite pkSeed targetTweak (extractCand a out) = yTarget)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClassPre : ∀ a, 𝒜Pre (puncturedSlotPreAdv latchOn suite targetTweak
      (pkSim a) (signSim a) (extractCand a) (advA a)))
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen inputLen qPre εPre) :
    Spec.GameBound (Spec.FinGame.mk hPos slotWin).winProb εPre := by
  let B : Fin nA → Spec.Code Spec.targetIface Spec.TargetBreak := fun a =>
    puncturedSlotPreAdv latchOn suite targetTweak (pkSim a) (signSim a) (extractCand a) (advA a)
  have hGameB := hPre n nC nA hPos π sample hSample B hClassPre
  refine Spec.GameBound.trans (Spec.event_le_reduction_win (Spec.FinGame.mk hPos slotWin) _
    (fun ω hW => ?_)) hGameB
  have hEqDigest := hSlotImp ω hW
  rw [Spec.smDtPreGame.public_eqs]; dsimp only [B, puncturedSlotPreAdv]
  rw [Spec.smDtPreRun.public_eqs]
  have hc : false = false ∧ ([] : List (Spec.Bytes × Spec.Bytes)).length < qPre ∧
      targetTweak ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst :=
    ⟨rfl, hqPre, fun h => nomatch h⟩
  rw [Spec.Code.play_call, Spec.smDtPreOracle_target, ite_eq_left hc]
  dsimp only [List.length_nil, List.nil_append, Option.getD]
  rw [Spec.Code.play_call, Spec.smDtPreOracle_reveal, Spec.Code.play_ret, Spec.smDtPreWin_eq]
  dsimp only [Option.getD, List.any]
  rw [Bool.or_false]
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl, decide_eq_true hEqDigest⟩

/-- **Hop 3 (`SmDtUdHard`) + Hop 4c (`Spec.SmDtPreHard`) WOTS+C Chain-Step Composition.** -/
theorem hulsing_hop3_and_hop4c_wots_chain_bound {n nC_ud nA_ud nC_pre nA_pre qHash qSign : Nat}
    (latchOn : Bool) (hPos : 0 < n) (suite : TweakableHashSuite)
    (seedLen inputLen outLen qUd qPre : Nat) (hqPre : 0 < qPre) (GReal : Spec.FinGame n)
    (πUd : Spec.CoinSplit n nC_ud nA_ud)
    (sampleUd : Fin nC_ud → Spec.Bytes × List Spec.Bytes × List Spec.Bytes)
    (hSampleUd : Spec.UniformOn (SmDtUdSampleOk seedLen inputLen outLen qUd) sampleUd)
    (DUd : Fin nA_ud → Spec.Code Spec.targetIface Bool)
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop} (hClassUd : ∀ a, 𝒜Ud (DUd a))
    {εUd : Spec.RatBound} (hUd : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen inputLen outLen qUd εUd)
    (targetTweak : Spec.Bytes) (pkSim : Fin nA_pre → Spec.Bytes → Spec.Bytes → PqPublicKey)
    (signSim : Fin nA_pre → Spec.Bytes → Spec.Bytes → ProdSigningQuery → Option PqHashSig)
    (extractCand : Fin nA_pre → (List UInt8 × PqHashSig) → Spec.Bytes)
    (πPre : Spec.CoinSplit n nC_pre nA_pre) (samplePre : Fin nC_pre → Spec.Bytes × List Spec.Bytes)
    (hSamplePre : Spec.UniformOn (Spec.SmDtPreSampleOk seedLen inputLen qPre) samplePre)
    (advPre : Fin nA_pre → SeedWithheldEufCmaAdv qHash qSign) (slotSimWin : Fin n → Bool)
    (hRealEq : ∀ ω, GReal.win ω =
      (smDtUdRealGame hPos (suiteTweakHash suite) qUd (fun z => (sampleUd (πUd.chal z)).1)
        (fun z i => (sampleUd (πUd.chal z)).2.1.getD i []) (fun z => DUd (πUd.advc z))).win ω)
    (hSimEq : ∀ ω, slotSimWin ω =
      (smDtUdIdealGame hPos qUd (fun z => (sampleUd (πUd.chal z)).1)
        (fun z i => (sampleUd (πUd.chal z)).2.2.getD i []) (fun z => DUd (πUd.advc z))).win ω)
    (hSlotImp : ∀ ω, slotSimWin ω = true →
      let pkSeed := (samplePre (πPre.chal ω)).1
      let yTarget := suiteTweakHash suite pkSeed targetTweak ((samplePre (πPre.chal ω)).2.getD 0 [])
      let a := πPre.advc ω
      let out := (evalLatchedAdaptiveTree latchOn suite.rawHash (signSim a pkSeed yTarget)
        ((canonicalizeAdvOptRand (advPre a)).run (pkSim a pkSeed yTarget)) 0).1
      suiteTweakHash suite pkSeed targetTweak (extractCand a out) = yTarget)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClassPre : ∀ a, 𝒜Pre (puncturedSlotPreAdv latchOn suite targetTweak
      (pkSim a) (signSim a) (extractCand a) (advPre a)))
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen inputLen qPre εPre) :
    Spec.GameBound GReal.winProb (εPre.add εUd) := by
  have hHop3 := hulsing_hop3_ud_chain_simulation hPos GReal (Spec.FinGame.mk hPos slotSimWin)
    (suiteTweakHash suite) seedLen inputLen outLen qUd πUd sampleUd hSampleUd DUd hClassUd hUd
    hRealEq hSimEq
  have hHop4c := hulsing_hop4c_smDtPre_interactive_bound latchOn hPos suite seedLen inputLen qPre
    hqPre targetTweak pkSim signSim extractCand πPre samplePre hSamplePre advPre slotSimWin
    hSlotImp hClassPre hPre
  exact Spec.RatBound.le_trans hHop3
    (Spec.RatBound.add_le_add hHop4c (Spec.RatBound.le_refl εUd))

/-! ## §4. Master Multi-Hop Standard-Model EUF-CMA Theorem (`hulsing_full_multihop_euf_cma_bound`) -/

/-- **Hop-4 Complete Idealized-PRF EUF-CMA Bound (`hulsing_hop4_idealPrf_euf_cma_bound`).** -/
theorem hulsing_hop4_idealPrf_euf_cma_bound {n nSeed nRest qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (seedLen qTcr : Nat) (hqTcr : 0 < qTcr)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (πSeed : Spec.CoinSplit n nSeed nRest) (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (rfMsgR rfSecR : Fin nRest → Spec.Bytes → Spec.Bytes)
    (hRfR : ∀ r x, x.length = 65 → (rfMsgR r x).length = 32)
    (advR : Fin nRest → SeedWithheldEufCmaAdv qHash qSign) (itsrEv preEv : Fin n → Bool)
    (hItsrImp : ∀ ω,
      let pkSeed := seedS (πSeed.chal ω)
      let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSecR (πSeed.advc ω))
      let signFn := signQueryIdealPrf suite params pkSeed (rfMsgR (πSeed.advc ω)) (rfSecR (πSeed.advc ω))
      let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
        ((canonicalizeAdvOptRand (advR (πSeed.advc ω))).run pk) 0
      ExplicitItsrCover suite params pk (signLogFromOracle signFn run.2) run.1.1 run.1.2 →
      itsrEv ω = true)
    (hPreImp : ∀ ω,
      let pkSeed := seedS (πSeed.chal ω)
      let sov := secOverlaySuite suite pkSeed (rfSecR (πSeed.advc ω))
      let pk := derivePublicKeyIdealPrf suite params pkSeed (rfSecR (πSeed.advc ω))
      let signFn := signQueryIdealPrf suite params pkSeed (rfMsgR (πSeed.advc ω)) (rfSecR (πSeed.advc ω))
      let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
        ((canonicalizeAdvOptRand (advR (πSeed.advc ω))).run pk) 0
      ExplicitPreBreak suite sov params ⟨[], [], pkSeed⟩
        (signLogFromOracle signFn run.2) run.1.1 run.1.2 → preEv ω = true)
    {𝒜Tcr : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClassTcr : ∀ r, 𝒜Tcr (openSeedTcrHopAdv latchOn suite params hw
      (rfMsgR r) (rfSecR r) (hRfR r) hOneTimeIfSt (advR r)))
    {εItsr εTcr εPreTotal : Spec.RatBound}
    (hItsrB : Spec.GameBound (Spec.FinGame.mk hPos itsrEv).winProb εItsr)
    (hTcr : SmDtOpenSeedTcrHard 𝒜Tcr (suiteTweakHash suite) seedLen qTcr εTcr)
    (hPreB : Spec.GameBound (Spec.FinGame.mk hPos preEv).winProb εPreTotal) :
    Spec.GameBound
      (ExecEufCmaIdealPrfGame latchOn hPos suite params
        (fun ω => seedS (πSeed.chal ω)) (fun ω => rfMsgR (πSeed.advc ω))
        (fun ω => rfSecR (πSeed.advc ω)) (fun ω => advR (πSeed.advc ω))).winProb
      ((εItsr.add εTcr).add εPreTotal) := by
  have hTcrB := hulsing_hop4b_openSeedTcr_tight_bound latchOn hPos suite params hw seedLen qTcr
    hqTcr hOneTimeIfSt πSeed seedS hSeed rfMsgR rfSecR hRfR advR hClassTcr hTcr
  refine Spec.event_le_three_reductions _ (Spec.FinGame.mk hPos itsrEv) _
    (Spec.FinGame.mk hPos preEv) (fun ω hW => ?_) hItsrB hTcrB hPreB
  rcases execEufCmaIdealPrf_explicit_classify_opt latchOn hPos suite params hw
      (fun z => seedS (πSeed.chal z)) (fun z => rfMsgR (πSeed.advc z))
      (fun z => rfSecR (πSeed.advc z)) (fun z => advR (πSeed.advc z)) ω
      (hRfR (πSeed.advc ω)) hOneTimeIfSt hW with hI | ⟨w, hwOpt⟩ | hP
  · exact .inl (hItsrImp ω hI)
  · refine .inr (.inl ?_)
    show (extractIdealPrfTcrWitnessOpt latchOn suite params hw (seedS (πSeed.chal ω))
      (rfMsgR (πSeed.advc ω)) (rfSecR (πSeed.advc ω)) (hRfR (πSeed.advc ω))
      hOneTimeIfSt (advR (πSeed.advc ω))).isSome = true
    rw [hwOpt]; rfl
  · exact .inr (.inr (hPreImp ω hP))

/-- Reassociate `(nC1, (nC2, (nSeed, nA)))` so `nSeed` sits at the outer challenger coordinate. -/
def reassocHop4SeedSplit {n nC1 nR1 nC2 nR2 nSeed nA : Nat}
    (π1 : Spec.CoinSplit n nC1 nR1) (π2 : Spec.CoinSplit nR1 nC2 nR2)
    (π3 : Spec.CoinSplit nR2 nSeed nA) : Spec.CoinSplit n nSeed (nC1 * (nC2 * nA)) :=
  let spI := Spec.CoinSplit.prod nC2 nA; let spO := Spec.CoinSplit.prod nC1 (nC2 * nA)
  { chal := fun ω => π3.chal (π2.advc (π1.advc ω))
    advc := fun ω => spO.pair (π1.chal ω) (spI.pair (π2.chal (π1.advc ω)) (π3.advc (π2.advc (π1.advc ω))))
    pair := fun s r =>
      π1.pair (spO.chal r) (π2.pair (spI.chal (spO.advc r)) (π3.pair s (spI.advc (spO.advc r))))
    chal_pair := fun s r => by rw [π1.advc_pair, π2.advc_pair, π3.chal_pair]
    advc_pair := fun s r => by
      rw [π1.chal_pair, π1.advc_pair, π2.chal_pair, π2.advc_pair, π3.advc_pair, spI.pair_eta, spO.pair_eta]
    pair_eta := fun ω => by
      rw [spO.chal_pair, spO.advc_pair, spI.chal_pair, spI.advc_pair, π3.pair_eta, π2.pair_eta, π1.pair_eta] }

/-- Full 3-way split key generator `(skSeed, skPrf, pkSeed)` for `hulsing_full_multihop_euf_cma_bound`. -/
abbrev multiHopFullKeygen {n nC1 nR1 nC2 nR2 nSeed nA : Nat}
    (π1 : Spec.CoinSplit n nC1 nR1) (π2 : Spec.CoinSplit nR1 nC2 nR2) (π3 : Spec.CoinSplit nR2 nSeed nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (seedS : Fin nSeed → Spec.Bytes) (ω : Fin n) : PqSecretKey :=
  ⟨(sampleSec (π2.chal (π1.advc ω))).1, (sampleMsg (π1.chal ω)).1, seedS (π3.chal (π2.advc (π1.advc ω)))⟩

/-- Full 3-way split canonicalized adversary family for `hulsing_full_multihop_euf_cma_bound`. -/
abbrev multiHopFullAdv {n nC1 nR1 nC2 nR2 nSeed nA qHash qSign : Nat}
    (π1 : Spec.CoinSplit n nC1 nR1) (π2 : Spec.CoinSplit nR1 nC2 nR2) (π3 : Spec.CoinSplit nR2 nSeed nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign) (ω : Fin n) :
    SeedWithheldEufCmaAdv qHash qSign :=
  canonicalizeAdvOptRand (adv (π3.advc (π2.advc (π1.advc ω))))

/-- **Master Hülsing–Kudinov / SPHINCS+ (`FIPS 205`) / XMSS-MT Multi-Hop EUF-CMA Theorem
    (`hulsing_full_multihop_euf_cma_bound`).**
    Composes `hulsing_hop1_prfMsg_idealization` (`Spec.PrfHard`), `hulsing_hop2_prfSec_idealization`
    (`Spec.PrfHard`), and `hulsing_hop4_idealPrf_euf_cma_bound` (`ITSR` + `SmDtOpenSeedTcrHard` +
    `SmDtUdHard` / `Spec.SmDtPreHard`). -/
theorem hulsing_full_multihop_euf_cma_bound {n nC1 nR1 nC2 nR2 nSeed nA qHash qSign : Nat}
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (seedLen keyLen qPrfMsg qPrfSec qTcr : Nat)
    (hqPrfMsg : qSign ≤ qPrfMsg) (hqPrfSec : prfSecQueryBudget params qSign ≤ qPrfSec)
    (hqTcr : 0 < qTcr) (π1 : Spec.CoinSplit n nC1 nR1) (π2 : Spec.CoinSplit nR1 nC2 nR2)
    (π3 : Spec.CoinSplit nR2 nSeed nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassMsg : ∀ r1 : Fin nR1, 𝒜Msg (prfMsgHopDistinguisher true suite params
      (seedS (π3.chal (π2.advc r1))) (sampleSec (π2.chal r1)).1 (adv (π3.advc (π2.advc r1)))))
    (hClassSec : ∀ b : Fin (nC1 * nR2),
      let sp := Spec.CoinSplit.prod nC1 nR2
      𝒜Sec (prfSecHopDistinguisher true suite params (seedS (π3.chal (sp.advc b)))
        (sampleMsg (sp.chal b)).2 (adv (π3.advc (sp.advc b)))))
    {𝒜Tcr : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClassTcr : ∀ r4 : Fin (nC1 * (nC2 * nA)),
      let spO := Spec.CoinSplit.prod nC1 (nC2 * nA); let spI := Spec.CoinSplit.prod nC2 nA
      let c1 := spO.chal r4; let c2 := spI.chal (spO.advc r4); let a := spI.advc (spO.advc r4)
      𝒜Tcr (openSeedTcrHopAdv true suite params hw (sampleMsg c1).2 (sampleSec c2).2
        (fun x hx => ((Spec.PrfSampleOk_eq keyLen 65 32 _).mp (hSampleMsg.mem c1)).2 x |>.1 hx)
        (fun _ => rfl) (adv a)))
    (itsrEv preEv : Fin n → Bool)
    (hItsrImp : ∀ ω,
      let pkSeed := seedS (π3.chal (π2.advc (π1.advc ω)))
      let pk := derivePublicKeyIdealPrf suite params pkSeed (sampleSec (π2.chal (π1.advc ω))).2
      let signFn := signQueryIdealPrf suite params pkSeed (sampleMsg (π1.chal ω)).2
        (sampleSec (π2.chal (π1.advc ω))).2
      let run := evalLatchedAdaptiveTree true suite.rawHash signFn
        ((canonicalizeAdvOptRand (adv (π3.advc (π2.advc (π1.advc ω))))).run pk) 0
      ExplicitItsrCover suite params pk (signLogFromOracle signFn run.2) run.1.1 run.1.2 →
      itsrEv ω = true)
    (hPreImp : ∀ ω,
      let pkSeed := seedS (π3.chal (π2.advc (π1.advc ω)))
      let rfS := (sampleSec (π2.chal (π1.advc ω))).2
      let pk := derivePublicKeyIdealPrf suite params pkSeed rfS
      let signFn := signQueryIdealPrf suite params pkSeed (sampleMsg (π1.chal ω)).2 rfS
      let run := evalLatchedAdaptiveTree true suite.rawHash signFn
        ((canonicalizeAdvOptRand (adv (π3.advc (π2.advc (π1.advc ω))))).run pk) 0
      ExplicitPreBreak suite (secOverlaySuite suite pkSeed rfS) params ⟨[], [], pkSeed⟩
        (signLogFromOracle signFn run.2) run.1.1 run.1.2 → preEv ω = true)
    {εPrfMsg εPrfSec εItsr εTcr εPreTotal : Spec.RatBound}
    (hPrfMsg : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (hItsrB : Spec.GameBound (Spec.FinGame.mk hPos itsrEv).winProb εItsr)
    (hTcr : SmDtOpenSeedTcrHard 𝒜Tcr (suiteTweakHash suite) seedLen qTcr εTcr)
    (hPreB : Spec.GameBound (Spec.FinGame.mk hPos preEv).winProb εPreTotal) :
    Spec.GameBound
      (ExecEufCmaGame hPos suite params
        (multiHopFullKeygen π1 π2 π3 sampleMsg sampleSec seedS)
        (multiHopFullAdv π1 π2 π3 adv)).winProb
      ((((εItsr.add εTcr).add εPreTotal).add εPrfSec).add εPrfMsg) := by
  let pkSeedR2 : Fin nR2 → List UInt8 := fun r2 => seedS (π3.chal r2)
  have hSeedLenR2 : ∀ r2, (pkSeedR2 r2).length = seedLen := fun r2 => hSeed.mem (π3.chal r2)
  let advR2 : Fin nR2 → SeedWithheldEufCmaAdv qHash qSign := fun r2 => adv (π3.advc r2)
  have hHop1 := hulsing_hop1_prfMsg_idealization true hPos suite params keyLen qPrfMsg hqPrfMsg
    π1 sampleMsg hSampleMsg (fun r1 => pkSeedR2 (π2.advc r1)) (fun r1 => (sampleSec (π2.chal r1)).1)
    (fun r1 => advR2 (π2.advc r1)) hClassMsg hPrfMsg
  let sp := Spec.CoinSplit.prod nC1 nR2
  let πHop2 : Spec.CoinSplit n nC2 (nC1 * nR2) :=
    { chal := fun ω => π2.chal (π1.advc ω)
      advc := fun ω => sp.pair (π1.chal ω) (π2.advc (π1.advc ω))
      pair := fun c2 b => π1.pair (sp.chal b) (π2.pair c2 (sp.advc b))
      chal_pair := fun c2 b => by rw [π1.advc_pair, π2.chal_pair]
      advc_pair := fun c2 b => by rw [π1.chal_pair, π1.advc_pair, π2.advc_pair, sp.pair_eta]
      pair_eta := fun ω => by rw [sp.chal_pair, sp.advc_pair, π2.pair_eta, π1.pair_eta] }
  have hHop2Raw := hulsing_hop2_prfSec_idealization true hPos suite params seedLen keyLen qPrfSec
    hqPrfSec πHop2 sampleSec hSampleSec (fun b => pkSeedR2 (sp.advc b))
    (fun b => hSeedLenR2 (sp.advc b)) (fun b => (sampleMsg (sp.chal b)).2)
    (fun b => advR2 (sp.advc b)) hClassSec hPrfSec
  let gHop1 := ExecEufCmaRandIdealGame true hPos suite params
    (fun ω => pkSeedR2 (π2.advc (π1.advc ω))) (fun ω => (sampleSec (π2.chal (π1.advc ω))).1)
    (fun ω => (sampleMsg (π1.chal ω)).2) (fun ω => advR2 (π2.advc (π1.advc ω)))
  let gHop2 := ExecEufCmaIdealPrfGame true hPos suite params
    (fun ω => pkSeedR2 (π2.advc (π1.advc ω))) (fun ω => (sampleMsg (π1.chal ω)).2)
    (fun ω => (sampleSec (π2.chal (π1.advc ω))).2) (fun ω => advR2 (π2.advc (π1.advc ω)))
  have hG1Eq : ExecEufCmaRandIdealGame true hPos suite params
      (fun ω => pkSeedR2 (sp.advc (πHop2.advc ω))) (fun ω => (sampleSec (πHop2.chal ω)).1)
      (fun ω => (sampleMsg (sp.chal (πHop2.advc ω))).2)
      (fun ω => advR2 (sp.advc (πHop2.advc ω))) = gHop1 := by
    apply Spec.FinGame.ext_win; intro ω; dsimp only [πHop2, gHop1]
    rw [ExecEufCmaRandIdealGame_win, ExecEufCmaRandIdealGame_win, sp.chal_pair, sp.advc_pair]
  have hG2Eq : ExecEufCmaIdealPrfGame true hPos suite params
      (fun ω => pkSeedR2 (sp.advc (πHop2.advc ω)))
      (fun ω => (sampleMsg (sp.chal (πHop2.advc ω))).2)
      (fun ω => (sampleSec (πHop2.chal ω)).2)
      (fun ω => advR2 (sp.advc (πHop2.advc ω))) = gHop2 := by
    apply Spec.FinGame.ext_win; intro ω; dsimp only [πHop2, gHop2]
    rw [ExecEufCmaIdealPrfGame_win, ExecEufCmaIdealPrfGame_win, sp.chal_pair, sp.advc_pair]
  have hHop2 : Spec.GameBound gHop1.winProb (gHop2.winProb.add εPrfSec) := by
    dsimp only at hHop2Raw; rwa [hG1Eq, hG2Eq] at hHop2Raw
  let π4 := reassocHop4SeedSplit π1 π2 π3
  let spO := Spec.CoinSplit.prod nC1 (nC2 * nA)
  let spI := Spec.CoinSplit.prod nC2 nA
  let rfMsg4 : Fin (nC1 * (nC2 * nA)) → Spec.Bytes → Spec.Bytes :=
    fun r4 => (sampleMsg (spO.chal r4)).2
  let rfSec4 : Fin (nC1 * (nC2 * nA)) → Spec.Bytes → Spec.Bytes :=
    fun r4 => (sampleSec (spI.chal (spO.advc r4))).2
  let adv4 : Fin (nC1 * (nC2 * nA)) → SeedWithheldEufCmaAdv qHash qSign :=
    fun r4 => adv (spI.advc (spO.advc r4))
  have hRf4 : ∀ r4 x, x.length = 65 → (rfMsg4 r4 x).length = 32 :=
    fun r4 x hx => ((Spec.PrfSampleOk_eq keyLen 65 32 _).mp (hSampleMsg.mem (spO.chal r4))).2 x |>.1 hx
  have hHop4Raw := hulsing_hop4_idealPrf_euf_cma_bound true hPos suite params hw seedLen qTcr
    hqTcr (fun _ => rfl) π4 seedS hSeed rfMsg4 rfSec4 hRf4 adv4 itsrEv preEv
    (fun ω hI => by
      dsimp only [π4, reassocHop4SeedSplit, rfMsg4, rfSec4, adv4] at hI
      rw [spO.chal_pair, spO.advc_pair, spI.chal_pair, spI.advc_pair] at hI
      exact hItsrImp ω hI)
    (fun ω hP => by
      dsimp only [π4, reassocHop4SeedSplit, rfMsg4, rfSec4, adv4] at hP
      rw [spO.chal_pair, spO.advc_pair, spI.chal_pair, spI.advc_pair] at hP
      exact hPreImp ω hP)
    hClassTcr hItsrB hTcr hPreB
  have hG2Eq4 : ExecEufCmaIdealPrfGame true hPos suite params
      (fun ω => seedS (π4.chal ω)) (fun ω => rfMsg4 (π4.advc ω))
      (fun ω => rfSec4 (π4.advc ω)) (fun ω => adv4 (π4.advc ω)) = gHop2 := by
    apply Spec.FinGame.ext_win; intro ω
    dsimp only [π4, reassocHop4SeedSplit, rfMsg4, rfSec4, adv4, gHop2, pkSeedR2, advR2]
    rw [ExecEufCmaIdealPrfGame_win, ExecEufCmaIdealPrfGame_win,
      spO.chal_pair, spO.advc_pair, spI.chal_pair, spI.advc_pair]
  have hHop4 : Spec.GameBound gHop2.winProb ((εItsr.add εTcr).add εPreTotal) := by
    rwa [hG2Eq4] at hHop4Raw
  exact Spec.RatBound.le_trans hHop1
    (Spec.RatBound.add_le_add
      (Spec.RatBound.le_trans hHop2
        (Spec.RatBound.add_le_add hHop4 (Spec.RatBound.le_refl εPrfSec)))
      (Spec.RatBound.le_refl εPrfMsg))

/-! ## §5. Inhabitedness Witnesses & Six-Kernel Assurance Audits -/

/-- Joint inhabitedness witness for `hulsing_hop4a_itsr_bound`. -/
theorem inhabited_hulsing_hop4a_itsr_bound :
    ∃ (n nC nA qHash qSign : Nat) (latchOn : Bool),
      0 < n ∧
      ∃ (suite : TweakableHashSuite) (params : PqHashParams) (randLen qItsr : Nat),
        qSign ≤ qItsr ∧
        ∃ (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes)
          (π : Spec.CoinSplit n nC nA) (rand : Fin nC → List Spec.Bytes),
          Spec.UniformOn (Spec.ItsrSampleOk randLen qItsr) rand ∧
          ∃ (advA : Fin nA → SeedWithheldEufCmaAdv qHash qSign) (itsrEv : Fin n → Bool),
            (∀ ω, itsrEv ω = true →
              let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
              let ev := evalSeqRandTree latchOn suite params pkSeed secFn
                (fun i => (rand (π.chal ω)).getD i [])
                ((canonicalizeAdvOptRand (advA (π.advc ω))).run pk) 0 [] []
              verifyProductionPqHashSig suite params pk ev.1.1 ev.1.2 = true ∧
              (ev.1.2.rRand, ev.1.1) ∉ ev.2.2 ∧
              ExplicitItsrCover suite params pk ev.2.1 ev.1.1 ev.1.2) ∧
            ∃ (𝒜Itsr : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop),
              (∀ a, 𝒜Itsr (itsrHopReductionAdv latchOn suite params pkSeed secFn (advA a))) ∧
              ∃ (εItsr : Spec.RatBound),
                Spec.ItsrHard 𝒜Itsr
                  (forsGlobalSubsetSelector suite params
                    (derivePublicKeyIdealPrf suite params pkSeed secFn))
                  randLen qItsr εItsr :=
  ⟨256, 256, 1, 0, 0, true, by decide, poly257MultiLeafSuite, baggyProdParams, 1, 1,
   Nat.zero_le 1, [], (fun _ => []), Spec.CoinSplit.challengerOnly 256, Spec.byte1ItsrSampler,
   Spec.uniformOn_byte1Itsr,
   (fun _ => ⟨fun _ => .pure ([], ⟨[], 0, 0, [], []⟩), fun _ => trivial⟩), (fun _ => false),
   (fun _ h => Bool.noConfusion h), (fun _ => True), (fun _ => trivial), Spec.RatBound.one,
   fun _ _ _ _ _ _ _ _ _ => Spec.FinGame.winProb_le_one _⟩

#verify_kernel
  Qsag.reassocHop4SeedSplit

#verify_constructive
  Qsag.encodeForsGlobalPos_inj
  Qsag.seqSignWithRand_sound
  Qsag.itsrHopReductionAdv_within
  Qsag.stateful_itsr_zero_bound
  Qsag.explicitItsrCover_implies_itsrWin
  Qsag.hulsing_hop4a_itsr_bound
  Qsag.commitTargetsThen_within
  Qsag.preCommittedTcrAdv_within
  Qsag.hulsing_hop4b_smDtTcr_precommitted_bound
  Qsag.openSeedTcrHopAdv_within
  Qsag.hulsing_hop4b_openSeedTcr_tight_bound
  Qsag.smDtOpenSeedTcrHard_constHash_refuted
  Qsag.explicitPreBreak_gives_tweakHash_eq
  Qsag.puncturedSlotPreAdv_within
  Qsag.hulsing_hop4c_smDtPre_interactive_bound
  Qsag.hulsing_hop3_and_hop4c_wots_chain_bound
  Qsag.hulsing_hop4_idealPrf_euf_cma_bound
  Qsag.hulsing_full_multihop_euf_cma_bound
  Qsag.inhabited_hulsing_hop4a_itsr_bound

#verify_inhabited
  Qsag.hulsing_hop4a_itsr_bound
  Qsag.inhabited_hulsing_hop4a_itsr_bound

#tooth_pair Qsag.hulsing_hop4a_itsr_bound vs
  Qsag.tooth_stateful_no_explicitItsrCover
#tooth_pair Qsag.hulsing_hop4b_openSeedTcr_tight_bound vs
  Qsag.smDtOpenSeedTcrHard_constHash_refuted
#tooth_pair Qsag.hulsing_full_multihop_euf_cma_bound vs
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges

end Qsag
end
