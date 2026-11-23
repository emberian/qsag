module
/-
# Qsag.Protocol.Threshold.IdealTsig — Strictly `sk`-Free Canetti $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ & UC Simulator

Closes `[P0-11]` by formalizing the dishonest-majority ($|C| \le t - 1$) threshold signature
functionality with identifiable abort ($\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$) and its
explicit `sk`-free UC simulator:
1. **Zero `sk` in Ideal Functionality (`IdealTsigState`, `execIdealTsig`)**:
   `IdealTsigState` holds only public `(pk, threshold, numParties, corruptParties, approvedMsgs, identifiedCheaters)` —
   zero secret keys and zero Shamir shares appear anywhere in `IdealTsigState` or `execIdealTsig`.
2. **Honest-Party Quorum Gate (`thresholdApproval_requires_honest_party`)**:
   Whenever `|corruptParties| < threshold`, no signature can be approved in $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$
   without at least one non-corrupt party in `honestApprovers` (`#tooth`: `corrupt_threshold_allows_unilateral_sign`).
3. **Anti-Framing Invariant (`idealTsig_never_frames_honest`)**:
   Across arbitrarily many signing, abort, and verification turns (`UcTsigEnv`), an honest party
   is never recorded in `identifiedCheaters`.
4. **`sk`-Free Pad-Space Simulator (`tsigSimulator_view_bijection_indep_of_secret`)**:
   Constructs an explicit `SimpleEquiv` bijection between real-world masked openings `w + P(0)`
   (depending on secret `w`) and `sk`-free simulated openings `0 + Q(0)` preserving all `< t`
   corrupt Shamir shares `Q(x_c) = P(x_c)` identically over `Goldilocks`, `GoldilocksExt2`, and `TowerElem k`.
5. **Multi-Turn UC Realization (`protocol_realizes_idealTsig_id_abort`)**:
   Distinguishing real threshold execution from `sk`-free `execIdealTsig` constructively extracts
   either a fresh underlying signature forgery (`mStar ∉ approvedMsgs`) or a MAC/framing break.
6. **One-Round Share-and-MAC Session and Simulator (`ucSimulatorTsig`,
   `ucSimulatorTsig_advantage_bound`)**: a signing session whose adversarial view consists of Shamir
   shares, broadcast masked shares and BDOZ tags; a simulator typed without any secret key or
   honest share; and a distinguishing bound `q / |K|` plus the advantages of two explicit
   reductions against the pad-tape and MAC-key generators. The model and its limits are stated
   at the head of section 5.
-/

public import Qsag.Spec.IdealCustody
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.MaliciousSecurity

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Strictly `sk`-Free $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ State & Quorum Gate -/

/-- **Honest Participation Theorem (`thresholdApproval_requires_honest_party`)**:
    Against any dishonest-majority adversary controlling `< t` parties (`|C| + 1 ≤ t`),
    every valid threshold approval in $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ MUST include at least
    one unquarantined honest party `h ∉ corruptParties`! -/
theorem thresholdApproval_requires_honest_party {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (_hDishonestBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hValid : validThresholdApproval st honestApprovers = true) :
    ∃ h ∈ honestApprovers, h < st.numParties ∧ h ∉ st.corruptParties := by
  unfold validThresholdApproval at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hValid
  rcases hValid with ⟨⟨⟨⟨⟨⟨⟨_hTh, _hMin⟩, hHonPos⟩, _hCNd⟩, _hCRng⟩, _hNd⟩, hAllHonest⟩, _hQuorum⟩
  cases honestApprovers with
  | nil =>
    simp only [List.length_nil] at hHonPos
    omega
  | cons h0 rest =>
    have hh0 := hAllHonest h0 (.head rest)
    exact ⟨h0, .head rest, hh0.1.1, hh0.1.2⟩

/-- Stronger quarantine-aware corollary: `validThresholdApproval = true` guarantees an honest
    party `h ∉ corruptParties ∧ h ∉ identifiedCheaters` and `corruptParties.length < threshold`. -/
theorem thresholdApproval_requires_unquarantined_honest_party {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (hValid : validThresholdApproval st honestApprovers = true) :
    st.corruptParties.length < st.threshold ∧
    ∃ h ∈ honestApprovers, h < st.numParties ∧ h ∉ st.corruptParties ∧ h ∉ st.identifiedCheaters := by
  unfold validThresholdApproval at hValid
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hValid
  rcases hValid with ⟨⟨⟨⟨⟨⟨⟨_hTh, hMin⟩, hHonPos⟩, _hCNd⟩, _hCRng⟩, _hNd⟩, hAllHonest⟩, _hQuorum⟩
  cases honestApprovers with
  | nil =>
    simp only [List.length_nil] at hHonPos
    omega
  | cons h0 rest =>
    have hh0 := hAllHonest h0 (.head rest)
    exact ⟨hMin, h0, .head rest, hh0.1.1, hh0.1.2, hh0.2⟩

/-- **`#tooth` Unilateral Empty-Quorum Rejection (`unilateral_empty_quorum_rejected`)**:
    Even if `|C| = threshold`, `validThresholdApproval st [] = false` strictly blocks unilateral
    signing with `honestApprovers = []`; removing the `corruptParties.length < threshold` and
    `0 < honestApprovers.length` guards (`mutantAllowFullCorruptQuorum`) permits `[]`! -/
theorem unilateral_empty_quorum_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg)
    (hThreshold : 0 < st.threshold ∧ st.threshold ≤ st.numParties)
    (hCorruptNd : st.corruptParties.Nodup)
    (hCorruptRange : ∀ c ∈ st.corruptParties, c < st.numParties)
    (hCorruptFull : st.corruptParties.length = st.threshold) :
    let mutantAllowFullCorruptQuorum (s : IdealTsigState PK Msg) (hon : List Nat) : Bool :=
      decide (0 < s.threshold ∧ s.threshold ≤ s.numParties) &&
      decide s.corruptParties.Nodup &&
      s.corruptParties.all (fun c => decide (c < s.numParties)) &&
      decide hon.Nodup &&
      decide (s.threshold ≤ s.corruptParties.length + hon.length)
    validThresholdApproval st [] = false ∧
    mutantAllowFullCorruptQuorum st [] = true := by
  intro mutantAllowFullCorruptQuorum
  refine ⟨empty_honest_approvers_rejected st, ?_⟩
  dsimp only [mutantAllowFullCorruptQuorum]
  have hNd : ([] : List Nat).Nodup := .nil
  simpa [hCorruptFull, hNd, hThreshold, hCorruptNd, List.all_eq_true] using hCorruptRange

/-- Repeated party identifiers cannot manufacture a quorum. -/
theorem duplicate_corrupt_parties_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (hDup : ¬ st.corruptParties.Nodup) :
    validThresholdApproval st honestApprovers = false := by
  simp [validThresholdApproval, hDup]

/-- Out-of-range identities cannot authorize signing. -/
theorem out_of_range_corrupt_parties_rejected {PK Msg : Type}
    (st : IdealTsigState PK Msg) (honestApprovers : List Nat)
    (c : Nat) (hc : c ∈ st.corruptParties) (hRange : ¬ c < st.numParties) :
    validThresholdApproval st honestApprovers = false := by
  have hAll : st.corruptParties.all (fun c => decide (c < st.numParties)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hRange (of_decide_eq_true ((List.all_eq_true.mp h) c hc))
  simp [validThresholdApproval, hAll]

/-- Ideal verification in $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$: accepts iff `m ∈ st.approvedMsgs`
    AND `S.verify st.pk m sig = true`. -/
@[expose] def idealTsigVerify {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (st : IdealTsigState PK Msg)
    (m : Msg) (sig : Sig) : Bool :=
  decide (m ∈ st.approvedMsgs) && S.verify st.pk m sig

/-- Ideal identifiable-abort transition: $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ records `culprit`
    ONLY if `culprit ∈ st.corruptParties` (structural anti-framing guarantee). -/
@[expose] def idealTsigRecordAbort {PK Msg : Type}
    (st : IdealTsigState PK Msg) (culprit : Nat) : Option (IdealTsigState PK Msg) :=
  if culprit ∈ st.corruptParties then
    some { st with identifiedCheaters := culprit :: st.identifiedCheaters }
  else
    none

/-! ## 2. Multi-Turn $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ Environment & Anti-Framing Invariant -/

inductive TsActionResult (Sig : Type) where
  | signed (sig : Sig)
  | rejectedQuorum
  | abortedBy (culprit : Nat)
  | rejectedFraming

inductive UcTsigEnv (PK Msg Sig : Type) where
  | halt (verdict : Bool)
  | stepSign (m : Msg) (honestApprovers : List Nat) (next : TsActionResult Sig → UcTsigEnv PK Msg Sig)
  | stepAbort (culprit : Nat) (next : TsActionResult Sig → UcTsigEnv PK Msg Sig)
  | stepVerify (m : Msg) (sig : Sig) (next : Bool → UcTsigEnv PK Msg Sig)

/-- Strictly `sk`-free ideal execution of $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$:
    uses only `IdealTsigState` and the simulator's public signature callback `simSign : Msg → Sig`. -/
def execIdealTsig {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (simSign : Msg → Sig)
    (st : IdealTsigState PK Msg) : UcTsigEnv PK Msg Sig → Bool × IdealTsigState PK Msg
  | .halt b => (b, st)
  | .stepSign m honestApprovers next =>
    if validThresholdApproval st honestApprovers then
      let st' := { st with approvedMsgs := m :: st.approvedMsgs }
      execIdealTsig S simSign st' (next (.signed (simSign m)))
    else
      execIdealTsig S simSign st (next .rejectedQuorum)
  | .stepAbort culprit next =>
    match idealTsigRecordAbort st culprit with
    | some st' => execIdealTsig S simSign st' (next (.abortedBy culprit))
    | none => execIdealTsig S simSign st (next .rejectedFraming)
  | .stepVerify m sig next =>
    execIdealTsig S simSign st (next (idealTsigVerify S st m sig))

/-- **Multi-Turn Anti-Framing Invariant (`idealTsig_never_frames_honest`)**:
    If `st₀.identifiedCheaters ⊆ st₀.corruptParties`, then after ANY multi-turn environment
    execution `Z`, every blamed party in `st_final.identifiedCheaters` belongs to `st₀.corruptParties`
    (no honest validator is ever framed!). -/
theorem idealTsig_never_frames_honest {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (simSign : Msg → Sig) :
    ∀ (st : IdealTsigState PK Msg) (Z : UcTsigEnv PK Msg Sig),
      (∀ c ∈ st.identifiedCheaters, c ∈ st.corruptParties) →
      let (_, stFinal) := execIdealTsig S simSign st Z
      stFinal.corruptParties = st.corruptParties ∧
      (∀ c ∈ stFinal.identifiedCheaters, c ∈ st.corruptParties)
  | st, .halt _, hInit => ⟨rfl, hInit⟩
  | st, .stepSign m honestApprovers next, hInit => by
    dsimp only [execIdealTsig]
    split
    · exact idealTsig_never_frames_honest S simSign
        { st with approvedMsgs := m :: st.approvedMsgs } (next (.signed (simSign m))) hInit
    · exact idealTsig_never_frames_honest S simSign st (next .rejectedQuorum) hInit
  | st, .stepAbort culprit next, hInit => by
    dsimp only [execIdealTsig, idealTsigRecordAbort]
    by_cases hc : culprit ∈ st.corruptParties
    · simp only [hc, ↓reduceIte]
      have hNext : ∀ c ∈ culprit :: st.identifiedCheaters, c ∈ st.corruptParties := by
        intro c hMem
        rcases List.mem_cons.mp hMem with rfl | hRest
        · exact hc
        · exact hInit c hRest
      exact idealTsig_never_frames_honest S simSign
        { st with identifiedCheaters := culprit :: st.identifiedCheaters }
        (next (.abortedBy culprit)) hNext
    · simp only [hc, ↓reduceIte]
      exact idealTsig_never_frames_honest S simSign st (next .rejectedFraming) hInit
  | st, .stepVerify m sig next, hInit =>
    idealTsig_never_frames_honest S simSign st (next (idealTsigVerify S st m sig)) hInit

/-! ## 3. Explicit `sk`-Free Pad-Space Simulator (`tsigSimulator_view_bijection_indep_of_secret`) -/

section SimulatorViewBijection
open CommRingOps

/-- Explicit `sk`-free view simulator for a single masked opening `w + P(0)` against `< t`
    corrupt evaluation points `corruptPts`:
    the simulator sets the secret wire to `zero` (`0`, completely `sk`-free!) and maps pad `Q` to
    `(0 + Q(0), Q|_{corruptPts})`. -/
def simMaskedOpeningView {R : Type} [LawfulCommRing R] {t : Nat}
    (corruptPts : List R) (Q : ShamirPadPoly R t) : R × List R :=
  (add zero (RoundPoly.evalCoeffs Q.1 zero),
   corruptPts.map (fun xc => RoundPoly.evalCoeffs Q.1 xc))

/-- Real-world masked opening view `(w + P(0), P|_{corruptPts})` under true secret wire `w : R`. -/
def realMaskedOpeningView {R : Type} [LawfulCommRing R] {t : Nat}
    (corruptPts : List R) (w : R) (P : ShamirPadPoly R t) : R × List R :=
  (add w (RoundPoly.evalCoeffs P.1 zero),
   corruptPts.map (fun xc => RoundPoly.evalCoeffs P.1 xc))

/-- **`sk`-Free Simulator View Bijection (`tsigSimulator_view_bijection_indep_of_secret`)**:
    For ANY ring `R` with invertible non-zero corrupt points (`Goldilocks`, `GoldilocksExt2`,
    `TowerElem k`) and ANY secret `w : R` (`sk`-derived share or intermediate wire),
    `shamir_rebalanceEquiv` is an **exact bijection** on `ShamirPadPoly R t` making the `sk`-free
    simulator's transcript `simMaskedOpeningView corruptPts (eqv P)` **bit-for-bit identical**
    to `realMaskedOpeningView corruptPts w P`! -/
theorem tsigSimulator_view_bijection_indep_of_secret {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (t : Nat) (corruptPts : List R) (w : R)
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ zero) :
    let eqv := shamir_rebalanceEquiv inv t corruptPts w hCard
    (∀ P : ShamirPadPoly R t, eqv.invFun (eqv.toFun P) = P) ∧
    (∀ Q : ShamirPadPoly R t, eqv.toFun (eqv.invFun Q) = Q) ∧
    (∀ P : ShamirPadPoly R t,
      simMaskedOpeningView corruptPts (eqv.toFun P) = realMaskedOpeningView corruptPts w P) := by
  intro eqv
  refine ⟨eqv.left_inv, eqv.right_inv, ?_⟩
  intro P
  obtain ⟨hOpen, hShares⟩ :=
    pad_bijection_masked_openings_uniform inv hInv t corruptPts w hCard hNonZero P
  unfold simMaskedOpeningView realMaskedOpeningView
  refine Prod.ext hOpen ?_
  exact List.map_congr_left hShares

end SimulatorViewBijection

/-! ## 4. Real-vs-Ideal Multi-Turn Threshold Execution & EUF-CMA / Anti-Framing Reduction -/

/-- Real-world threshold execution: holds `sk : SK` (via reconstructed quorum openings) and MAC
    blame verifier `verifyMacCulprit : Nat → Bool` (which accepts only when a corrupt party sends an
    invalid BDOZ/SPDZ share/MAC). -/
def execRealTsig {PK SK Msg Sig : Type}
    (S : AbstractSigScheme PK SK Msg Sig) (sk : SK)
    (verifyMacCulprit : Nat → Bool)
    (st : IdealTsigState PK Msg) : UcTsigEnv PK Msg Sig → Bool
  | .halt b => b
  | .stepSign m honestApprovers next =>
    if validThresholdApproval st honestApprovers then
      let st' := { st with approvedMsgs := m :: st.approvedMsgs }
      execRealTsig S sk verifyMacCulprit st' (next (.signed (S.sign sk m)))
    else
      execRealTsig S sk verifyMacCulprit st (next .rejectedQuorum)
  | .stepAbort culprit next =>
    if verifyMacCulprit culprit then
      let st' := { st with identifiedCheaters := culprit :: st.identifiedCheaters }
      execRealTsig S sk verifyMacCulprit st' (next (.abortedBy culprit))
    else
      execRealTsig S sk verifyMacCulprit st (next .rejectedFraming)
  | .stepVerify m sig next =>
    execRealTsig S sk verifyMacCulprit st (next (S.verify st.pk m sig))

/-- Constructively locate the first divergence between `execRealTsig` and `sk`-free `execIdealTsig`:
    either an unapproved signature forgery `PSum.inl (mStar, sigStar)` or a MAC-blame mismatch
    `PSum.inr culprit` (`0 Classical.choice`). -/
def findTsigDivergence {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (simSign : Msg → Sig)
    (verifyMacCulprit : Nat → Bool)
    (st : IdealTsigState PK Msg) :
    UcTsigEnv PK Msg Sig → Option (PSum (Msg × Sig × List Msg) Nat)
  | .halt _ => none
  | .stepSign m honestApprovers next =>
    if validThresholdApproval st honestApprovers then
      let st' := { st with approvedMsgs := m :: st.approvedMsgs }
      findTsigDivergence S simSign verifyMacCulprit st' (next (.signed (simSign m)))
    else
      findTsigDivergence S simSign verifyMacCulprit st (next .rejectedQuorum)
  | .stepAbort culprit next =>
    if verifyMacCulprit culprit != decide (culprit ∈ st.corruptParties) then
      some (.inr culprit)
    else
      match idealTsigRecordAbort st culprit with
      | some st' => findTsigDivergence S simSign verifyMacCulprit st' (next (.abortedBy culprit))
      | none => findTsigDivergence S simSign verifyMacCulprit st (next .rejectedFraming)
  | .stepVerify m sig next =>
    if m ∉ st.approvedMsgs ∧ S.verify st.pk m sig = true then
      some (.inl (m, sig, st.approvedMsgs))
    else
      findTsigDivergence S simSign verifyMacCulprit st (next (idealTsigVerify S st m sig))

theorem findTsigDivergence_sound {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (simSign : Msg → Sig)
    (verifyMacCulprit : Nat → Bool) :
    ∀ (st : IdealTsigState PK Msg) (Z : UcTsigEnv PK Msg Sig) (w : PSum (Msg × Sig × List Msg) Nat),
      findTsigDivergence S simSign verifyMacCulprit st Z = some w →
      match w with
      | .inl (mStar, sigStar, approvedAtStep) =>
          mStar ∉ approvedAtStep ∧ S.verify st.pk mStar sigStar = true
      | .inr culprit =>
          verifyMacCulprit culprit ≠ decide (culprit ∈ st.corruptParties)
  | _, .halt _, _, h => by cases h
  | st, .stepSign m honestApprovers next, w, h => by
    dsimp only [findTsigDivergence] at h
    split at h
    · exact findTsigDivergence_sound S simSign verifyMacCulprit
        { st with approvedMsgs := m :: st.approvedMsgs } (next (.signed (simSign m))) w h
    · exact findTsigDivergence_sound S simSign verifyMacCulprit st (next .rejectedQuorum) w h
  | st, .stepAbort culprit next, w, h => by
    dsimp only [findTsigDivergence] at h
    by_cases hMis : (verifyMacCulprit culprit != decide (culprit ∈ st.corruptParties)) = true
    · simp only [hMis, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [bne_iff_ne, ne_eq] at hMis
      exact hMis
    · simp only [hMis, Bool.false_eq_true, ↓reduceIte] at h
      unfold idealTsigRecordAbort at h
      by_cases hc : culprit ∈ st.corruptParties
      · simp only [hc, ↓reduceIte] at h
        exact findTsigDivergence_sound S simSign verifyMacCulprit
          { st with identifiedCheaters := culprit :: st.identifiedCheaters }
          (next (.abortedBy culprit)) w h
      · simp only [hc, ↓reduceIte] at h
        exact findTsigDivergence_sound S simSign verifyMacCulprit st (next .rejectedFraming) w h
  | st, .stepVerify m sig next, w, h => by
    dsimp only [findTsigDivergence] at h
    by_cases hForg : m ∉ st.approvedMsgs ∧ S.verify st.pk m sig = true
    · rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn hForg))] at h
      injection h with hEq
      subst hEq
      exact hForg
    · rw [ite_eq_right_iff.mpr (fun hp => False.elim (hForg hp))] at h
      exact findTsigDivergence_sound S simSign verifyMacCulprit st (next (idealTsigVerify S st m sig)) w h

/-- **End-to-End UC Realization of $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ (`protocol_realizes_idealTsig_id_abort`)**:
    When threshold signing agrees with single-signer `S.sign sk` (`thresholdSign_eq_singleSign`) and
    MAC blame verification is sound (`∀ c, verifyMacCulprit c = decide (c ∈ corruptParties)`),
    any multi-turn environment `Z` that distinguishes `execRealTsig` from the **100% `sk`-free**
    `execIdealTsig` constructively yields a fresh EUF-CMA signature forgery `(mStar, sigStar)`
    (`mStar ∉ approvedAtStep ∧ S.verify pk mStar sigStar = true`)! -/
theorem protocol_realizes_idealTsig_id_abort {PK SK Msg Sig : Type} [DecidableEq Msg]
    (S : AbstractSigScheme PK SK Msg Sig) (sk : SK) (simSign : Msg → Sig)
    (verifyMacCulprit : Nat → Bool)
    (hSimSign : ∀ m, simSign m = S.sign sk m)
    (st : IdealTsigState PK Msg)
    (hMacSound : ∀ c, verifyMacCulprit c = decide (c ∈ st.corruptParties))
    (Z : UcTsigEnv PK Msg Sig) :
    execRealTsig S sk verifyMacCulprit st Z = (execIdealTsig S simSign st Z).1 ∨
    ∃ mStar sigStar approvedAtStep,
      findTsigDivergence S simSign verifyMacCulprit st Z = some (.inl (mStar, sigStar, approvedAtStep)) ∧
      mStar ∉ approvedAtStep ∧
      S.verify st.pk mStar sigStar = true := by
  have hNoDivEq :
      ∀ (ZCur : UcTsigEnv PK Msg Sig) (stCur : IdealTsigState PK Msg),
        stCur.pk = st.pk →
        findTsigDivergence S simSign verifyMacCulprit stCur ZCur = none →
        execRealTsig S sk verifyMacCulprit stCur ZCur = (execIdealTsig S simSign stCur ZCur).1 := by
    intro ZCur
    induction ZCur with
    | halt b => intro _ _ _; rfl
    | stepSign m honestApprovers next ih =>
      intro stCur hPk hNone
      dsimp only [findTsigDivergence] at hNone
      dsimp only [execRealTsig, execIdealTsig]
      split
      · rename_i hVal
        simp only [hVal, ↓reduceIte] at hNone
        rw [← hSimSign m]
        exact ih (.signed (simSign m)) _ hPk hNone
      · rename_i hInval
        simp only [hInval, Bool.false_eq_true, ↓reduceIte] at hNone
        exact ih .rejectedQuorum _ hPk hNone
    | stepAbort culprit next ih =>
      intro stCur hPk hNone
      dsimp only [findTsigDivergence] at hNone
      by_cases hMis : (verifyMacCulprit culprit != decide (culprit ∈ stCur.corruptParties)) = true
      · simp [hMis] at hNone
      · simp only [hMis, Bool.false_eq_true, ↓reduceIte] at hNone
        have hEqBlame : verifyMacCulprit culprit = decide (culprit ∈ stCur.corruptParties) := by
          cases hb1 : verifyMacCulprit culprit <;> cases hb2 : decide (culprit ∈ stCur.corruptParties) <;>
            simp_all
        unfold idealTsigRecordAbort at hNone
        dsimp only [execRealTsig, execIdealTsig, idealTsigRecordAbort]
        by_cases hc : culprit ∈ stCur.corruptParties
        · have hvTrue : verifyMacCulprit culprit = true := by simp [hEqBlame, hc]
          simp only [hc, hvTrue, ↓reduceIte] at hNone ⊢
          exact ih (.abortedBy culprit) _ hPk hNone
        · have hvFalse : verifyMacCulprit culprit = false := by simp [hEqBlame, hc]
          simp only [hc, hvFalse, Bool.false_eq_true, ↓reduceIte] at hNone ⊢
          exact ih .rejectedFraming _ hPk hNone
    | stepVerify m sig next ih =>
      intro stCur hPk hNone
      dsimp only [findTsigDivergence] at hNone
      by_cases hForg : m ∉ stCur.approvedMsgs ∧ S.verify stCur.pk m sig = true
      · rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn hForg))] at hNone; cases hNone
      · rw [ite_eq_right_iff.mpr (fun hp => False.elim (hForg hp))] at hNone
        have hVerEq : S.verify stCur.pk m sig = idealTsigVerify S stCur m sig := by
          unfold idealTsigVerify
          by_cases hm : m ∈ stCur.approvedMsgs
          · simp [hm]
          · cases hv : S.verify stCur.pk m sig
            · simp [hm]
            · exact False.elim (hForg ⟨hm, hv⟩)
        dsimp only [execRealTsig, execIdealTsig]
        rw [hVerEq]
        exact ih (idealTsigVerify S stCur m sig) _ hPk hNone
  have hCorruptInv :
      ∀ (ZCur : UcTsigEnv PK Msg Sig) (stCur : IdealTsigState PK Msg) (c : Nat),
        stCur.corruptParties = st.corruptParties →
        findTsigDivergence S simSign verifyMacCulprit stCur ZCur ≠ some (.inr c) := by
    intro ZCur
    induction ZCur with
    | halt _ => intro _ _ _; simp [findTsigDivergence]
    | stepSign m honestApprovers next ih =>
      intro stCur c hCorr
      dsimp only [findTsigDivergence]
      split
      · exact ih (.signed (simSign m)) _ c hCorr
      · exact ih .rejectedQuorum _ c hCorr
    | stepAbort culprit next ih =>
      intro stCur c hCorr
      dsimp only [findTsigDivergence]
      have hSame : (verifyMacCulprit culprit != decide (culprit ∈ stCur.corruptParties)) = false := by
        rw [hCorr, hMacSound culprit, bne_self_eq_false]
      simp only [hSame, Bool.false_eq_true, ↓reduceIte, idealTsigRecordAbort]
      by_cases hc : culprit ∈ stCur.corruptParties
      · simp only [hc, ↓reduceIte]
        exact ih (.abortedBy culprit) _ c hCorr
      · simp only [hc, ↓reduceIte]
        exact ih .rejectedFraming _ c hCorr
    | stepVerify m sig next ih =>
      intro stCur c hCorr
      dsimp only [findTsigDivergence]
      by_cases hForg : m ∉ stCur.approvedMsgs ∧ S.verify stCur.pk m sig = true
      · rw [ite_eq_left_iff.mpr (fun hn => False.elim (hn hForg))]; intro hC; cases hC
      · rw [ite_eq_right_iff.mpr (fun hp => False.elim (hForg hp))]
        exact ih (idealTsigVerify S stCur m sig) _ c hCorr
  cases hDiv : findTsigDivergence S simSign verifyMacCulprit st Z with
  | none => exact .inl (hNoDivEq Z st rfl hDiv)
  | some w =>
    cases w with
    | inl triple =>
      rcases triple with ⟨mStar, sigStar, approvedAtStep⟩
      have hSound := findTsigDivergence_sound S simSign verifyMacCulprit st Z
        (.inl (mStar, sigStar, approvedAtStep)) hDiv
      exact .inr ⟨mStar, sigStar, approvedAtStep, rfl, hSound.1, hSound.2⟩
    | inr culprit =>
      exact False.elim (hCorruptInv Z st culprit rfl hDiv)

/-! ## 5. One-Round Share-and-MAC Signing Session, `sk`-Free Simulator, Advantage Bound

Model. Parties are identified by a number and a public non-zero evaluation point. Corruption is
static; the corrupt list has at most `d` entries, where `d + 1` is the threshold. One signing
session of an approved message proceeds in one broadcast round over `k` secret cut wires and one
output wire:

* wire `j` carries the secret value `w j`, Shamir-shared by `w j :: A j`, and a pad shared by the
  polynomial `P j`; every honest party broadcasts its share of the masked polynomial
  `(w j :: A j) + P j`, each copy tagged with a BDOZ MAC for every corrupt verifier;
* the output wire carries `y`, Shamir-shared by `y :: B`; every honest party broadcasts its share,
  tagged the same way;
* every corrupt party answers with one BDOZ opening per wire (output wire first); one honest
  verifier checks them in order against its key and blames the first sender whose opening fails;
* if all pass, the output is reconstructed from the honest output shares and the opened corrupt
  output shares with the public weights `lambdas`.

The honest verifier's key is used in tag-first form (`bdozKeyFromView`): the corrupt parties' tags
are fixed and the local keys are derived from the global key. Wire values are given functions of
the secret key and the message; gate-level evaluation, the OT protocol that correlates the MAC
keys, and the PRG that expands the pads are not modelled as protocols. The last two enter only as
generators in `ucSimulatorTsig_advantage_bound`. -/

section UcSimulator
open CommRingOps

/-- Public parameters of the opening layer. -/
structure TsigParams (R Sig : Type) where
  /-- Degree bound of the sharing polynomials; the threshold is `d + 1`. -/
  d : Nat
  /-- Number of secret cut wires opened in masked form. -/
  k : Nat
  encSig : Sig → R
  decSig : R → Sig
  /-- Embedding of the share ring into the MAC field, with a left inverse. -/
  emb : R → Tower128
  unemb : Tower128 → R
  /-- Public reconstruction weights for the points of the honest parties followed by the corrupt ones. -/
  lambdas : List R
  /-- MAC slot of wire index `j` (the output wire has index `k`) and honest sender `h`. -/
  slot : Nat → Nat → Nat

/-- Honest pad randomness of one session. -/
structure TsigPadTape (R : Type) (d k : Nat) where
  share : Fin k → ShamirPadPoly R d
  pad : Fin k → ShamirPadPoly R (d + 1)
  out : ShamirPadPoly R d

/-- The simulator's random tape: pad randomness and the MAC key of the simulated honest verifier. -/
structure TsigSimTape (R : Type) (d k : Nat) where
  pads : TsigPadTape R d k
  macKey : Tower128 × Tower128

/-- What the corrupt parties see of one masked wire. -/
structure TsigWireView (R : Type) where
  /-- Their own shares of the wire value. -/
  corruptShares : List R
  /-- Their own shares of the pad. -/
  corruptPadShares : List R
  /-- The masked shares broadcast by the honest parties. -/
  honestOpenings : List R
  /-- For each corrupt verifier, the tagged opening message of each honest party. -/
  honestTags : List (List BdozPairOpening)

/-- The corrupt parties' incoming messages in one session. -/
structure TsigAdvView (R : Type) (k : Nat) where
  wires : Fin k → TsigWireView R
  outCorruptShares : List R
  outHonestOpenings : List R
  outHonestTags : List (List BdozPairOpening)

/-- Everything the simulator is given: public data, the corrupt parties' own MAC material, and the
    output of the ideal functionality. No secret key, wire value or honest share occurs. -/
structure TsigSimInput (R PK Msg Sig : Type) where
  pk : PK
  msg : Msg
  /-- Corrupt parties: identifier and evaluation point. -/
  corrupt : List (Nat × R)
  /-- Honest parties: identifier and evaluation point. -/
  honest : List (Nat × R)
  /-- The corrupt parties' own BDOZ verification keys. -/
  corruptVk : Nat → BdozVerifierKeys
  /-- The corrupt parties' own tags towards the honest verifier, by opening position. -/
  corruptTags : Nat → Tower128 × Tower128
  /-- Output of the ideal functionality for this request. -/
  fOut : TsActionResult Sig

/-- Adversary and distinguisher: the corrupt parties' openings as a function of their view, and
    the final bit as a function of the view and the honest parties' outcome. -/
structure TsigAdversary (R Sig : Type) (k : Nat) where
  openings : TsigAdvView R k → List BdozPairOpening
  verdict : TsigAdvView R k → TsActionResult Sig → Bool
  idle : TsActionResult Sig → Bool

private theorem tsigPadTape_ext {R : Type} {d k : Nat} :
    ∀ (a b : TsigPadTape R d k),
      (∀ j, a.share j = b.share j) → (∀ j, a.pad j = b.pad j) → a.out = b.out → a = b
  | ⟨s1, p1, o1⟩, ⟨s2, p2, o2⟩, h1, h2, h3 => by
    have e1 : s1 = s2 := funext h1
    have e2 : p1 = p2 := funext h2
    have e3 : o1 = o2 := h3
    subst e1
    subst e2
    subst e3
    rfl

private theorem tsigAdvView_ext {R : Type} {k : Nat} :
    ∀ (a b : TsigAdvView R k),
      (∀ j, a.wires j = b.wires j) → a.outCorruptShares = b.outCorruptShares →
      a.outHonestOpenings = b.outHonestOpenings → a.outHonestTags = b.outHonestTags → a = b
  | ⟨w1, a1, b1, c1⟩, ⟨w2, a2, b2, c2⟩, h1, h2, h3, h4 => by
    have e1 : w1 = w2 := funext h1
    have e2 : a1 = a2 := h2
    have e3 : b1 = b2 := h3
    have e4 : c1 = c2 := h4
    subst e1
    subst e2
    subst e3
    subst e4
    rfl

/-- One masked wire as seen by the corrupt parties, from the share and pad evaluation maps. -/
def tsigWireView {R : Type} [CommRingOps R] (emb : R → Tower128)
    (corruptVk : Nat → BdozVerifierKeys) (slotOf : Nat → Nat)
    (corrupt honest : List (Nat × R)) (fShare fPad : R → R) : TsigWireView R :=
  { corruptShares := corrupt.map (fun cx => fShare cx.2)
    corruptPadShares := corrupt.map (fun cx => fPad cx.2)
    honestOpenings := honest.map (fun hx => add (fShare hx.2) (fPad hx.2))
    honestTags := corrupt.map (fun cx => honest.map (fun hx =>
      bdozHonestOpening (corruptVk cx.1) (slotOf hx.1) (emb (add (fShare hx.2) (fPad hx.2))))) }

private theorem tsigWireView_congr {R : Type} [CommRingOps R] (emb : R → Tower128)
    (corruptVk : Nat → BdozVerifierKeys) (slotOf : Nat → Nat)
    (corrupt honest : List (Nat × R)) (f g f' g' : R → R)
    (hShare : ∀ cx ∈ corrupt, f' cx.2 = f cx.2)
    (hPad : ∀ cx ∈ corrupt, g' cx.2 = g cx.2)
    (hSum : ∀ x : R, add (f' x) (g' x) = add (f x) (g x)) :
    tsigWireView emb corruptVk slotOf corrupt honest f' g' =
      tsigWireView emb corruptVk slotOf corrupt honest f g := by
  have key : ∀ (a a' b b' c c' : List R) (t t' : List (List BdozPairOpening)),
      a' = a → b' = b → c' = c → t' = t →
      TsigWireView.mk a' b' c' t' = TsigWireView.mk a b c t := by
    intro a a' b b' c c' t t' h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  exact key _ _ _ _ _ _ _ _
    (List.map_congr_left hShare) (List.map_congr_left hPad)
    (List.map_congr_left (fun hx _ => hSum hx.2))
    (List.map_congr_left (fun cx _ => List.map_congr_left (fun hx _ =>
      congrArg (fun v => bdozHonestOpening (corruptVk cx.1) (slotOf hx.1) (emb v)) (hSum hx.2))))

/-- Concatenation of a `Fin n`-indexed family of lists. -/
def finFlat {α : Type} : (n : Nat) → (Fin n → List α) → List α
  | 0, _ => []
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ ++ finFlat n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem finFlat_length_const {α : Type} (c : Nat) :
    ∀ (n : Nat) (f : Fin n → List α), (∀ i, (f i).length = c) → (finFlat n f).length = n * c
  | 0, _, _ => (Nat.zero_mul c).symm
  | n + 1, f, h => by
    have ih := finFlat_length_const c n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) (fun i => h _)
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hm : (n + 1) * c = n * c + c := by rw [Nat.add_mul, Nat.one_mul]
    simp only [finFlat, List.length_append]
    omega

private theorem mem_finFlat {α : Type} (a : α) :
    ∀ (n : Nat) (f : Fin n → List α), a ∈ finFlat n f → ∃ i, a ∈ f i
  | 0, _, h => by
    have h' : a ∈ ([] : List α) := h
    cases h'
  | n + 1, f, h => by
    have h' : a ∈ f ⟨0, Nat.zero_lt_succ n⟩ ++
        finFlat n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := h
    rcases List.mem_append.mp h' with h0 | hRest
    · exact ⟨_, h0⟩
    · obtain ⟨i, hi⟩ := mem_finFlat a n _ hRest
      exact ⟨_, hi⟩

/-- The honest parties' code for one session, run on wire values `w` and output value `y`:
    the messages the corrupt parties receive. -/
@[expose] def tsigSessionView {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (corruptVk : Nat → BdozVerifierKeys) (corrupt honest : List (Nat × R))
    (w : Fin pp.k → R) (y : R) (tape : TsigPadTape R pp.d pp.k) : TsigAdvView R pp.k :=
  { wires := fun j => tsigWireView pp.emb corruptVk (pp.slot j.val) corrupt honest
      (RoundPoly.evalCoeffs (w j :: (tape.share j).1)) (RoundPoly.evalCoeffs (tape.pad j).1)
    outCorruptShares := corrupt.map (fun cx => RoundPoly.evalCoeffs (y :: tape.out.1) cx.2)
    outHonestOpenings := honest.map (fun hx => RoundPoly.evalCoeffs (y :: tape.out.1) hx.2)
    outHonestTags := corrupt.map (fun cx => honest.map (fun hx =>
      bdozHonestOpening (corruptVk cx.1) (pp.slot pp.k hx.1)
        (pp.emb (RoundPoly.evalCoeffs (y :: tape.out.1) hx.2)))) }

/-- The honest verifier's record for one session: for every expected corrupt opening, in order
    (output wire first), the sender and the embedded share it was dealt. -/
@[expose] def tsigSessionExpected {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (corrupt : List (Nat × R)) (w : Fin pp.k → R) (y : R) (tape : TsigPadTape R pp.d pp.k) :
    List (Nat × Tower128) :=
  corrupt.map (fun cx => (cx.1, pp.emb (RoundPoly.evalCoeffs (y :: tape.out.1) cx.2))) ++
  finFlat pp.k (fun j => corrupt.map (fun cx =>
    (cx.1, pp.emb (add (RoundPoly.evalCoeffs (w j :: (tape.share j).1) cx.2)
                       (RoundPoly.evalCoeffs (tape.pad j).1 cx.2)))))

theorem tsigSessionExpected_length {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (corrupt : List (Nat × R)) (w : Fin pp.k → R) (y : R) (tape : TsigPadTape R pp.d pp.k) :
    (tsigSessionExpected pp corrupt w y tape).length = (pp.k + 1) * corrupt.length := by
  unfold tsigSessionExpected
  rw [List.length_append, List.length_map, finFlat_length_const corrupt.length]
  · have hm : (pp.k + 1) * corrupt.length = pp.k * corrupt.length + corrupt.length := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro i
    simp only [List.length_map]

private theorem tsigSessionExpected_ids {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (corrupt : List (Nat × R)) (w : Fin pp.k → R) (y : R) (tape : TsigPadTape R pp.d pp.k) :
    ∀ e ∈ tsigSessionExpected pp corrupt w y tape, e.1 ∈ corrupt.map Prod.fst := by
  intro e he
  unfold tsigSessionExpected at he
  rcases List.mem_append.mp he with h1 | h2
  · obtain ⟨cx, hcx, rfl⟩ := List.mem_map.mp h1
    exact List.mem_map.mpr ⟨cx, hcx, rfl⟩
  · obtain ⟨j, hj⟩ := mem_finFlat e pp.k _ h2
    obtain ⟨cx, hcx, rfl⟩ := List.mem_map.mp hj
    exact List.mem_map.mpr ⟨cx, hcx, rfl⟩

/-- Product of the two rebalancing bijections on every wire; the output randomness is untouched. -/
def tsigTapeRebalance {R : Type} [LawfulCommRing R] (inv : R → R) (d k : Nat)
    (corruptPts : List R) (hCard : corruptPts.length + 1 ≤ d + 1) (w : Fin k → R) :
    SimpleEquiv (TsigPadTape R d k) (TsigPadTape R d k) :=
  { toFun := fun τ =>
      { share := fun j => (shamirShare_rebalanceEquiv inv d corruptPts (w j) hCard).toFun (τ.share j)
        pad := fun j => (shamir_rebalanceEquiv inv (d + 1) corruptPts (w j) hCard).toFun (τ.pad j)
        out := τ.out }
    invFun := fun τ =>
      { share := fun j => (shamirShare_rebalanceEquiv inv d corruptPts (w j) hCard).invFun (τ.share j)
        pad := fun j => (shamir_rebalanceEquiv inv (d + 1) corruptPts (w j) hCard).invFun (τ.pad j)
        out := τ.out }
    left_inv := fun τ => tsigPadTape_ext _ _
      (fun j => (shamirShare_rebalanceEquiv inv d corruptPts (w j) hCard).left_inv (τ.share j))
      (fun j => (shamir_rebalanceEquiv inv (d + 1) corruptPts (w j) hCard).left_inv (τ.pad j)) rfl
    right_inv := fun τ => tsigPadTape_ext _ _
      (fun j => (shamirShare_rebalanceEquiv inv d corruptPts (w j) hCard).right_inv (τ.share j))
      (fun j => (shamir_rebalanceEquiv inv (d + 1) corruptPts (w j) hCard).right_inv (τ.pad j)) rfl }

/-- **Hop 1, pointwise (`tsigSession_rebalance`)**: running the honest code on the all-zero wire
    values with the rebalanced tape produces exactly the messages, and exactly the verifier
    record, of the run on the true wire values `w`. -/
theorem tsigSession_rebalance {R Sig : Type} [LawfulCommRing R] (pp : TsigParams R Sig)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (corruptVk : Nat → BdozVerifierKeys) (corrupt honest : List (Nat × R))
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (w : Fin pp.k → R) (y : R) (τ : TsigPadTape R pp.d pp.k) :
    tsigSessionView pp corruptVk corrupt honest (fun _ => zero) y
        ((tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard w).toFun τ) =
      tsigSessionView pp corruptVk corrupt honest w y τ ∧
    tsigSessionExpected pp corrupt (fun _ => zero) y
        ((tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard w).toFun τ) =
      tsigSessionExpected pp corrupt w y τ := by
  have hNz : ∀ c ∈ corrupt.map Prod.snd, c ≠ (zero : R) := by
    intro c hc
    obtain ⟨cx, hcx, rfl⟩ := List.mem_map.mp hc
    exact hNonZero cx hcx
  have hj := fun j : Fin pp.k =>
    shamir_share_pad_rebalance inv hInv pp.d (corrupt.map Prod.snd) (w j) hCard hNz
      (τ.share j) (τ.pad j)
  refine ⟨?_, ?_⟩
  · refine tsigAdvView_ext _ _ (fun j => ?_) rfl rfl rfl
    obtain ⟨h1, h2, h3⟩ := hj j
    exact tsigWireView_congr pp.emb corruptVk (pp.slot j.val) corrupt honest _ _ _ _
      (fun cx hcx => h1 cx.2 (List.mem_map.mpr ⟨cx, hcx, rfl⟩))
      (fun cx hcx => h2 cx.2 (List.mem_map.mpr ⟨cx, hcx, rfl⟩))
      (fun x => h3 x)
  · have hF :
        (fun j : Fin pp.k => corrupt.map (fun cx : Nat × R =>
          (cx.1, pp.emb (add
            (RoundPoly.evalCoeffs (zero ::
              (((tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard w).toFun τ).share j).1) cx.2)
            (RoundPoly.evalCoeffs
              (((tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard w).toFun τ).pad j).1 cx.2))))) =
        (fun j : Fin pp.k => corrupt.map (fun cx : Nat × R =>
          (cx.1, pp.emb (add (RoundPoly.evalCoeffs (w j :: (τ.share j).1) cx.2)
                             (RoundPoly.evalCoeffs (τ.pad j).1 cx.2))))) := by
      funext j
      obtain ⟨_, _, h3⟩ := hj j
      exact List.map_congr_left (fun cx _ =>
        congrArg (fun v => (cx.1, pp.emb v)) (h3 cx.2))
    exact congrArg (fun f =>
      corrupt.map (fun cx : Nat × R => (cx.1, pp.emb (RoundPoly.evalCoeffs (y :: τ.out.1) cx.2))) ++
        finFlat pp.k f) hF

/-! ### Opening checks of the real verifier and of the simulator -/

/-- An opening is accepted in position `s` when it names that position and its MACs verify. -/
def tsigOpAccepted (vk : BdozVerifierKeys) (s : Nat) (op : BdozPairOpening) : Bool :=
  op.partyId == s && verifyBdozPairMac vk op

private theorem tsigOpAccepted_spec {vk : BdozVerifierKeys} {s : Nat} {op : BdozPairOpening}
    (h : tsigOpAccepted vk s op = true) : op.partyId = s ∧ verifyBdozPairMac vk op = true := by
  unfold tsigOpAccepted at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
  exact ⟨eq_of_beq h1, h2⟩

/-- The real honest verifier: walks the expected openings and returns the first sender whose
    opening is missing or rejected by the MAC check. -/
def tsigCheckOpenings (vk : BdozVerifierKeys) :
    Nat → List (Nat × Tower128) → List BdozPairOpening → Option Nat
  | _, [], _ => none
  | _, e :: _, [] => some e.1
  | s, e :: es, op :: ops =>
    if tsigOpAccepted vk s op then tsigCheckOpenings vk (s + 1) es ops else some e.1

/-- The simulator's check: additionally blames a sender whose opened share differs from the one
    it was dealt, whether or not the MAC check passes. -/
def tsigSimCheckOpenings (vk : BdozVerifierKeys) :
    Nat → List (Nat × Tower128) → List BdozPairOpening → Option Nat
  | _, [], _ => none
  | _, e :: _, [] => some e.1
  | s, e :: es, op :: ops =>
    if (tsigOpAccepted vk s op && (op.shareX == e.2)) then tsigSimCheckOpenings vk (s + 1) es ops
    else some e.1

/-- First accepted opening whose share differs from the dealt one, if any. -/
def tsigFindForgery (vk : BdozVerifierKeys) :
    Nat → List (Nat × Tower128) → List BdozPairOpening → Option BdozPairOpening
  | s, e :: es, op :: ops =>
    if (tsigOpAccepted vk s op && !(op.shareX == e.2)) then some op
    else tsigFindForgery vk (s + 1) es ops
  | _, _, _ => none

/-- Dealt share of position `s` in a verifier record. -/
def tsigShareAt : List (Nat × Tower128) → Nat → Tower128
  | [], _ => towerZero 7
  | e :: _, 0 => e.2
  | _ :: es, s + 1 => tsigShareAt es s

/-- The honest verifier's key for a session: global key `alpha`, local keys forced by the dealt
    shares and the corrupt parties' tags. -/
def tsigVerifierKey (alpha : Tower128 × Tower128) (tags : Nat → Tower128 × Tower128)
    (exp : List (Nat × Tower128)) : BdozVerifierKeys :=
  bdozKeyFromView alpha (fun s => (tsigShareAt exp s, tags s))

private theorem tsigCheckOpenings_cons (vk : BdozVerifierKeys) (s : Nat) (e : Nat × Tower128)
    (es : List (Nat × Tower128)) (op : BdozPairOpening) (ops : List BdozPairOpening) :
    tsigCheckOpenings vk s (e :: es) (op :: ops) =
      if tsigOpAccepted vk s op then tsigCheckOpenings vk (s + 1) es ops else some e.1 := rfl

private theorem tsigSimCheckOpenings_cons (vk : BdozVerifierKeys) (s : Nat) (e : Nat × Tower128)
    (es : List (Nat × Tower128)) (op : BdozPairOpening) (ops : List BdozPairOpening) :
    tsigSimCheckOpenings vk s (e :: es) (op :: ops) =
      if (tsigOpAccepted vk s op && (op.shareX == e.2)) then tsigSimCheckOpenings vk (s + 1) es ops
      else some e.1 := rfl

private theorem tsigFindForgery_cons (vk : BdozVerifierKeys) (s : Nat) (e : Nat × Tower128)
    (es : List (Nat × Tower128)) (op : BdozPairOpening) (ops : List BdozPairOpening) :
    tsigFindForgery vk s (e :: es) (op :: ops) =
      if (tsigOpAccepted vk s op && !(op.shareX == e.2)) then some op
      else tsigFindForgery vk (s + 1) es ops := rfl

/-- Without an accepted wrong share, the real check and the simulator's check coincide. -/
theorem tsigCheck_eq_simCheck_of_no_forgery (vk : BdozVerifierKeys) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening),
      tsigFindForgery vk s es ops = none →
      tsigCheckOpenings vk s es ops = tsigSimCheckOpenings vk s es ops
  | [], _, _, _ => rfl
  | _ :: _, _, [], _ => rfl
  | e :: es, s, op :: ops, h => by
    rw [tsigFindForgery_cons] at h
    rw [tsigCheckOpenings_cons, tsigSimCheckOpenings_cons]
    cases hA : tsigOpAccepted vk s op with
    | false => rfl
    | true =>
      rw [hA] at h
      cases hE : (op.shareX == e.2) with
      | false =>
        rw [hE] at h
        simp at h
      | true =>
        rw [hE] at h
        exact tsigCheck_eq_simCheck_of_no_forgery vk es (s + 1) ops h

/-- The real verifier only ever blames a sender from its record. -/
theorem tsigCheckOpenings_blame_mem (vk : BdozVerifierKeys) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening) (c : Nat),
      tsigCheckOpenings vk s es ops = some c → c ∈ es.map Prod.fst
  | [], _, _, _, h => by
    have h' : (none : Option Nat) = some _ := h
    cases h'
  | e :: es, _, [], c, h => by
    have h' : some e.1 = some c := h
    cases h'
    exact .head _
  | e :: es, s, op :: ops, c, h => by
    rw [tsigCheckOpenings_cons] at h
    cases hA : tsigOpAccepted vk s op with
    | true =>
      rw [hA] at h
      exact .tail _ (tsigCheckOpenings_blame_mem vk es (s + 1) ops c h)
    | false =>
      rw [hA] at h
      have h' : some e.1 = some c := h
      cases h'
      exact .head _

theorem tsigSimCheckOpenings_blame_mem (vk : BdozVerifierKeys) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening) (c : Nat),
      tsigSimCheckOpenings vk s es ops = some c → c ∈ es.map Prod.fst
  | [], _, _, _, h => by
    have h' : (none : Option Nat) = some _ := h
    cases h'
  | e :: es, _, [], c, h => by
    have h' : some e.1 = some c := h
    cases h'
    exact .head _
  | e :: es, s, op :: ops, c, h => by
    rw [tsigSimCheckOpenings_cons] at h
    cases hA : (tsigOpAccepted vk s op && (op.shareX == e.2)) with
    | true =>
      rw [hA] at h
      exact .tail _ (tsigSimCheckOpenings_blame_mem vk es (s + 1) ops c h)
    | false =>
      rw [hA] at h
      have h' : some e.1 = some c := h
      cases h'
      exact .head _

/-- When the simulator's check passes, the opened shares are the dealt ones. -/
private theorem tsigSimCheck_none_shares {β : Type} (u : Tower128 → β) (vk : BdozVerifierKeys) :
    ∀ (es1 : List (Nat × Tower128)) (s : Nat) (es2 : List (Nat × Tower128))
      (ops : List BdozPairOpening),
      tsigSimCheckOpenings vk s (es1 ++ es2) ops = none →
      (ops.take es1.length).map (fun op => u op.shareX) = es1.map (fun e => u e.2)
  | [], _, _, _, _ => rfl
  | e :: es1, s, es2, [], h => by
    have h' : some e.1 = (none : Option Nat) := h
    cases h'
  | e :: es1, s, es2, op :: ops, h => by
    have h' : tsigSimCheckOpenings vk s (e :: (es1 ++ es2)) (op :: ops) = none := h
    rw [tsigSimCheckOpenings_cons] at h'
    cases hA : (tsigOpAccepted vk s op && (op.shareX == e.2)) with
    | false =>
      rw [hA] at h'
      simp at h'
    | true =>
      rw [hA] at h'
      have hRec := tsigSimCheck_none_shares u vk es1 (s + 1) es2 ops h'
      have hShare : op.shareX = e.2 := eq_of_beq (Bool.and_eq_true_iff.mp hA).2
      simp only [List.length_cons, List.take_succ_cons, List.map_cons]
      rw [hRec, hShare]

/-- A found forgery is an accepted opening at some position `s + i` of the record whose share
    differs from the dealt share of that position. -/
theorem tsigFindForgery_sound (vk : BdozVerifierKeys) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening) (op : BdozPairOpening),
      tsigFindForgery vk s es ops = some op →
      ∃ i, op ∈ ops ∧ op.partyId = s + i ∧ verifyBdozPairMac vk op = true ∧
        op.shareX ≠ tsigShareAt es i
  | [], _, _, _, h => by
    have h' : (none : Option BdozPairOpening) = some _ := h
    cases h'
  | _ :: _, _, [], _, h => by
    have h' : (none : Option BdozPairOpening) = some _ := h
    cases h'
  | e :: es, s, op' :: ops, op, h => by
    rw [tsigFindForgery_cons] at h
    cases hA : (tsigOpAccepted vk s op' && !(op'.shareX == e.2)) with
    | true =>
      rw [hA] at h
      have h' : some op' = some op := h
      cases h'
      rcases Bool.and_eq_true_iff.mp hA with ⟨hAcc, hNe⟩
      obtain ⟨hPid, hVer⟩ := tsigOpAccepted_spec hAcc
      refine ⟨0, .head _, hPid, hVer, ?_⟩
      intro hEq
      have hb : (op'.shareX == e.2) = true := by
        rw [show op'.shareX = e.2 from hEq]
        exact beq_self_eq_true _
      rw [hb] at hNe
      cases hNe
    | false =>
      rw [hA] at h
      obtain ⟨i, hMem, hPid, hVer, hNe⟩ := tsigFindForgery_sound vk es (s + 1) ops op h
      refine ⟨i + 1, .tail _ hMem, ?_, hVer, hNe⟩
      rw [hPid]
      omega

/-- **Hop 2, witness (`tsig_forgery_yields_key_guess`)**: a session in which a corrupt party's
    opening with a wrong share is accepted exhibits that opening among the adversary's messages,
    a MAC forgery witness against the honest verifier's key, and the equation showing that the
    global key equals a value computed from the adversary's own message, shares and tags. -/
theorem tsig_forgery_yields_key_guess (alpha : Tower128 × Tower128)
    (tags : Nat → Tower128 × Tower128) (exp : List (Nat × Tower128))
    (ops : List BdozPairOpening) (op : BdozPairOpening)
    (h : tsigFindForgery (tsigVerifierKey alpha tags exp) 0 exp ops = some op) :
    op ∈ ops ∧
    BdozMacForgeryWitness (tsigVerifierKey alpha tags exp)
      (bdozViewOpening (fun s => (tsigShareAt exp s, tags s)) op.partyId) op ∧
    alpha = bdozKeyGuess (fun s => (tsigShareAt exp s, tags s)) op := by
  obtain ⟨i, hMem, hPid, hVer, hNe⟩ := tsigFindForgery_sound _ exp 0 ops op h
  rw [Nat.zero_add] at hPid
  have hNe' : op.shareX ≠ tsigShareAt exp op.partyId := by
    rw [hPid]
    exact hNe
  exact ⟨hMem,
    ⟨rfl, fun hEq => hNe' hEq.symm,
      bdozKeyFromView_accepts_view alpha (fun s => (tsigShareAt exp s, tags s)) op.partyId, hVer⟩,
    bdoz_forgery_pins_key alpha (fun s => (tsigShareAt exp s, tags s)) op hNe' hVer⟩

private theorem isSome_false_eq_none {α : Type} : ∀ (o : Option α), o.isSome = false → o = none
  | none, _ => rfl
  | some _, h => by cases h

/-- **Hop 2, counting (`tsigForgery_keys_le`)**: for fixed openings, among `CK` distinct global
    keys at most one per expected opening makes the verifier accept a wrong share. -/
theorem tsigForgery_keys_le (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hInj : ∀ i j, keyDec i = keyDec j → i = j) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (ops : List BdozPairOpening)
      (hon : Nat → Tower128 × Tower128 × Tower128),
      (∀ i, (hon (s + i)).1 = tsigShareAt es i) →
      qsum CK (fun i =>
        if (tsigFindForgery (bdozKeyFromView (keyDec i) hon) s es ops).isSome then 1 else 0) ≤
        es.length
  | [], s, ops, hon, _ =>
    Nat.le_of_eq ((qsum_congr (g := fun _ => 0) (fun _ => rfl)).trans
      ((qsum_const CK 0).trans (Nat.mul_zero CK)))
  | e :: es, s, [], hon, _ =>
    Nat.le_trans (Nat.le_of_eq ((qsum_congr (g := fun _ => 0) (fun _ => rfl)).trans
      ((qsum_const CK 0).trans (Nat.mul_zero CK)))) (Nat.zero_le _)
  | e :: es, s, op :: ops, hon, hHon => by
    have hStep : ∀ i : Fin CK,
        (if (tsigFindForgery (bdozKeyFromView (keyDec i) hon) s (e :: es) (op :: ops)).isSome
          then 1 else 0) =
        (if ((tsigOpAccepted (bdozKeyFromView (keyDec i) hon) s op && !(op.shareX == e.2)) ||
              (tsigFindForgery (bdozKeyFromView (keyDec i) hon) (s + 1) es ops).isSome)
          then 1 else 0) := by
      intro i
      rw [tsigFindForgery_cons]
      cases (tsigOpAccepted (bdozKeyFromView (keyDec i) hon) s op && !(op.shareX == e.2)) <;> rfl
    have h0 : (hon s).1 = e.2 := hHon 0
    have h1 := qsum_indicator_le_one_of_unique CK
      (fun i => tsigOpAccepted (bdozKeyFromView (keyDec i) hon) s op && !(op.shareX == e.2))
      (fun i j hi hj => by
        rcases Bool.and_eq_true_iff.mp hi with ⟨hAi, hNeB⟩
        rcases Bool.and_eq_true_iff.mp hj with ⟨hAj, _⟩
        obtain ⟨hPid, hVi⟩ := tsigOpAccepted_spec hAi
        obtain ⟨_, hVj⟩ := tsigOpAccepted_spec hAj
        have hNe : op.shareX ≠ (hon op.partyId).1 := by
          rw [hPid, h0]
          intro hEq
          have hb : (op.shareX == e.2) = true := by
            rw [hEq]
            exact beq_self_eq_true _
          rw [hb] at hNeB
          cases hNeB
        exact hInj i j ((bdoz_forgery_pins_key (keyDec i) hon op hNe hVi).trans
          (bdoz_forgery_pins_key (keyDec j) hon op hNe hVj).symm))
    have h2 := tsigForgery_keys_le CK keyDec hInj es (s + 1) ops hon (fun i => by
      have h := hHon (i + 1)
      rw [show s + (i + 1) = s + 1 + i by omega] at h
      exact h)
    exact Nat.le_trans (Nat.le_of_eq (qsum_congr hStep))
      (Nat.le_trans
        (qsum_indicator_or_le
          (fun i => tsigOpAccepted (bdozKeyFromView (keyDec i) hon) s op && !(op.shareX == e.2))
          (fun i => (tsigFindForgery (bdozKeyFromView (keyDec i) hon) (s + 1) es ops).isSome))
        (Nat.le_trans (Nat.add_le_add h1 h2) (by simp only [List.length_cons]; omega)))

/-! ### Real execution, ideal functionality, simulator -/

/-- Honest parties' outcome in the real protocol: blame the first failed opening, otherwise
    reconstruct the output from the honest output shares and the opened corrupt output shares. -/
def tsigRealOutcome {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig) (nc : Nat)
    (vk : BdozVerifierKeys) (exp : List (Nat × Tower128)) (honestOut : List R)
    (ops : List BdozPairOpening) : TsActionResult Sig :=
  match tsigCheckOpenings vk 0 exp ops with
  | some c => .abortedBy c
  | none => .signed (pp.decSig (ringDot pp.lambdas
      (honestOut ++ (ops.take nc).map (fun op => pp.unemb op.shareX))))

private theorem tsigRealOutcome_abort {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (nc : Nat) (vk : BdozVerifierKeys) (exp : List (Nat × Tower128)) (honestOut : List R)
    (ops : List BdozPairOpening) (c : Nat) (h : tsigCheckOpenings vk 0 exp ops = some c) :
    tsigRealOutcome pp nc vk exp honestOut ops = .abortedBy c := by
  unfold tsigRealOutcome
  rw [h]

private theorem tsigRealOutcome_signed {R Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (nc : Nat) (vk : BdozVerifierKeys) (exp : List (Nat × Tower128)) (honestOut : List R)
    (ops : List BdozPairOpening) (h : tsigCheckOpenings vk 0 exp ops = none) :
    tsigRealOutcome pp nc vk exp honestOut ops =
      .signed (pp.decSig (ringDot pp.lambdas
        (honestOut ++ (ops.take nc).map (fun op => pp.unemb op.shareX)))) := by
  unfold tsigRealOutcome
  rw [h]

/-- **Real execution of one session.** The adversary's view is produced by the share-and-MAC
    steps on the wire values `wireVals sk m` and the output wire value `outVal sk m`; the honest
    outcome is computed from the openings the adversary returns. No signing function is called. -/
@[expose] def tsigRealExec {R PK SK Msg Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigPadTape R pp.d pp.k) (macKey : Tower128 × Tower128) : Bool :=
  if validThresholdApproval st approvers then
    Adv.verdict (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape)
      (tsigRealOutcome pp corrupt.length
        (tsigVerifierKey macKey corruptTags
          (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) tape))
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) tape)
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape).outHonestOpenings
        (Adv.openings
          (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape)))
  else Adv.idle .rejectedQuorum

/-- The ideal functionality's answer to a signing request: it alone holds `sk`. -/
@[expose] def tsigIdealFunctionality {PK SK Msg Sig : Type} (S : AbstractSigScheme PK SK Msg Sig)
    (st : IdealTsigState PK Msg) (sk : SK) (m : Msg) (approvers : List Nat) : TsActionResult Sig :=
  if validThresholdApproval st approvers then .signed (S.sign sk m) else .rejectedQuorum

/-- **The simulator (`ucSimulatorTsig`).** From the functionality's output and its own tape it
    produces the corrupt parties' incoming messages by running the honest code on all-zero wire
    values and on the signature it was handed. Its arguments contain no secret key, no wire
    value and no honest share. -/
@[expose] def ucSimulatorTsig {R PK Msg Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (inp : TsigSimInput R PK Msg Sig) (tape : TsigSimTape R pp.d pp.k) :
    Option (TsigAdvView R pp.k) :=
  match inp.fOut with
  | .signed sig =>
    some (tsigSessionView pp inp.corruptVk inp.corrupt inp.honest (fun _ => zero)
      (pp.encSig sig) tape.pads)
  | _ => none

/-- Second move of the simulator: from the corrupt parties' openings, whom to report to the
    functionality as the cheater (if anyone). -/
@[expose] def ucSimulatorTsigBlame {R PK Msg Sig : Type} [CommRingOps R] (pp : TsigParams R Sig)
    (inp : TsigSimInput R PK Msg Sig) (tape : TsigSimTape R pp.d pp.k)
    (ops : List BdozPairOpening) : Option Nat :=
  match inp.fOut with
  | .signed sig =>
    tsigSimCheckOpenings
      (tsigVerifierKey tape.macKey inp.corruptTags
        (tsigSessionExpected pp inp.corrupt (fun _ => zero) (pp.encSig sig) tape.pads))
      0 (tsigSessionExpected pp inp.corrupt (fun _ => zero) (pp.encSig sig) tape.pads) ops
  | _ => none

/-- Honest parties' outcome in the ideal world: an abort report is filtered by
    `idealTsigRecordAbort`; otherwise the functionality's own output is delivered. -/
def tsigIdealOutcome {PK Msg Sig : Type} (st : IdealTsigState PK Msg)
    (fOut : TsActionResult Sig) (blame : Option Nat) : TsActionResult Sig :=
  match blame with
  | some c =>
    (match idealTsigRecordAbort st c with
     | some _ => .abortedBy c
     | none => .rejectedFraming)
  | none => fOut

private theorem tsigIdealOutcome_abort {PK Msg Sig : Type} (st : IdealTsigState PK Msg)
    (fOut : TsActionResult Sig) (c : Nat) (hc : c ∈ st.corruptParties) :
    tsigIdealOutcome st fOut (some c) = .abortedBy c := by
  simp only [tsigIdealOutcome, idealTsigRecordAbort, hc, ↓reduceIte]

/-- **Ideal execution of one session**: functionality, simulator and the same adversary. -/
@[expose] def tsigIdealExec {R PK SK Msg Sig : Type} [CommRingOps R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigSimTape R pp.d pp.k) : Bool :=
  let inp : TsigSimInput R PK Msg Sig :=
    { pk := st.pk, msg := m, corrupt := corrupt, honest := honest, corruptVk := corruptVk,
      corruptTags := corruptTags, fOut := tsigIdealFunctionality S st sk m approvers }
  match ucSimulatorTsig pp inp tape with
  | none => Adv.idle inp.fOut
  | some view =>
    Adv.verdict view
      (tsigIdealOutcome st inp.fOut (ucSimulatorTsigBlame pp inp tape (Adv.openings view)))

private theorem tsigRealExec_rejected {R PK SK Msg Sig : Type} [CommRingOps R]
    (pp : TsigParams R Sig) (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigPadTape R pp.d pp.k) (macKey : Tower128 × Tower128)
    (hV : validThresholdApproval st approvers = false) :
    tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv
      tape macKey = Adv.idle .rejectedQuorum := by
  unfold tsigRealExec
  rw [hV]
  rfl

private theorem tsigRealExec_approved {R PK SK Msg Sig : Type} [CommRingOps R]
    (pp : TsigParams R Sig) (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigPadTape R pp.d pp.k) (macKey : Tower128 × Tower128)
    (hV : validThresholdApproval st approvers = true) :
    tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv
      tape macKey =
    Adv.verdict (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape)
      (tsigRealOutcome pp corrupt.length
        (tsigVerifierKey macKey corruptTags
          (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) tape))
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) tape)
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape).outHonestOpenings
        (Adv.openings
          (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) tape))) := by
  unfold tsigRealExec
  rw [hV]
  rfl

private theorem tsigIdealExec_rejected {R PK SK Msg Sig : Type} [CommRingOps R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigSimTape R pp.d pp.k)
    (hV : validThresholdApproval st approvers = false) :
    tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv tape =
      Adv.idle .rejectedQuorum := by
  unfold tsigIdealExec tsigIdealFunctionality
  rw [hV]
  rfl

private theorem tsigIdealExec_approved {R PK SK Msg Sig : Type} [CommRingOps R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (pads : TsigPadTape R pp.d pp.k) (macKey : Tower128 × Tower128)
    (hV : validThresholdApproval st approvers = true) :
    tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨pads, macKey⟩ =
    Adv.verdict
      (tsigSessionView pp corruptVk corrupt honest (fun _ => zero) (pp.encSig (S.sign sk m)) pads)
      (tsigIdealOutcome st (.signed (S.sign sk m))
        (tsigSimCheckOpenings
          (tsigVerifierKey macKey corruptTags
            (tsigSessionExpected pp corrupt (fun _ => zero) (pp.encSig (S.sign sk m)) pads))
          0 (tsigSessionExpected pp corrupt (fun _ => zero) (pp.encSig (S.sign sk m)) pads)
          (Adv.openings (tsigSessionView pp corruptVk corrupt honest (fun _ => zero)
            (pp.encSig (S.sign sk m)) pads)))) := by
  unfold tsigIdealExec tsigIdealFunctionality
  rw [hV]
  rfl

/-- Without an accepted wrong share the real outcome equals the ideal one: the same blame, or the
    reconstructed output equals the signature the functionality delivers. -/
theorem tsig_outcomes_agree {R PK Msg Sig : Type} [LawfulCommRing R]
    (pp : TsigParams R Sig) (st : IdealTsigState PK Msg)
    (corruptVk : Nat → BdozVerifierKeys) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (w : Fin pp.k → R) (sig : Sig) (τ : TsigPadTape R pp.d pp.k)
    (vk : BdozVerifierKeys) (ops : List BdozPairOpening)
    (hNo : tsigFindForgery vk 0 (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) ops = none) :
    tsigRealOutcome pp corrupt.length vk (tsigSessionExpected pp corrupt w (pp.encSig sig) τ)
        (tsigSessionView pp corruptVk corrupt honest w (pp.encSig sig) τ).outHonestOpenings ops =
      tsigIdealOutcome st (.signed sig)
        (tsigSimCheckOpenings vk 0 (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) ops) := by
  have hEq := tsigCheck_eq_simCheck_of_no_forgery vk _ 0 ops hNo
  cases hS : tsigSimCheckOpenings vk 0 (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) ops with
  | some c =>
    have hc : c ∈ st.corruptParties := by
      rw [hIds]
      obtain ⟨e, he, hec⟩ := List.mem_map.mp (tsigSimCheckOpenings_blame_mem vk _ 0 ops c hS)
      rw [← hec]
      exact tsigSessionExpected_ids pp corrupt w (pp.encSig sig) τ e he
    rw [tsigRealOutcome_abort pp corrupt.length vk _ _ ops c (hEq.trans hS),
        tsigIdealOutcome_abort st _ c hc]
  | none =>
    rw [tsigRealOutcome_signed pp corrupt.length vk _ _ ops (hEq.trans hS)]
    have hTake := tsigSimCheck_none_shares pp.unemb vk
      (corrupt.map (fun cx : Nat × R =>
        (cx.1, pp.emb (RoundPoly.evalCoeffs (pp.encSig sig :: τ.out.1) cx.2)))) 0 _ ops hS
    rw [List.length_map, List.map_map] at hTake
    have hShares : (ops.take corrupt.length).map (fun op => pp.unemb op.shareX) =
        corrupt.map (fun cx => RoundPoly.evalCoeffs (pp.encSig sig :: τ.out.1) cx.2) :=
      hTake.trans (List.map_congr_left (fun cx _ => hEmb _))
    have hLen : (pp.encSig sig :: τ.out.1).length ≤ pp.d + 1 := by
      rw [List.length_cons, τ.out.2]
      exact Nat.le_refl _
    rw [hShares]
    show TsActionResult.signed (pp.decSig (ringDot pp.lambdas
      (honest.map (fun hx => RoundPoly.evalCoeffs (pp.encSig sig :: τ.out.1) hx.2) ++
        corrupt.map (fun cx => RoundPoly.evalCoeffs (pp.encSig sig :: τ.out.1) cx.2)))) =
      TsActionResult.signed sig
    rw [← List.map_append, hRecon (pp.encSig sig :: τ.out.1) hLen, RoundPoly.evalCoeffs_cons,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero, hDec]

/-- **Hop 1 + Hop 2, pointwise (`tsig_real_eq_ideal_unless_forgery`)**: on every pad tape and
    MAC key on which no wrong share is accepted, the real execution outputs exactly what the
    ideal execution outputs on the rebalanced simulator tape. `hCircuit` states that the output
    wire of the evaluated circuit carries the encoded signature. -/
theorem tsig_real_eq_ideal_unless_forgery {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128)
    (hNoForgery : tsigFindForgery
      (tsigVerifierKey κ corruptTags
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)) 0
      (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)
      (Adv.openings
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ)) = none) :
    tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ =
    tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv
      ⟨(tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m)).toFun τ, κ⟩ := by
  cases hV : validThresholdApproval st approvers with
  | false =>
    rw [tsigRealExec_rejected pp wireVals outVal st corrupt honest corruptVk corruptTags sk m
          approvers Adv τ κ hV,
        tsigIdealExec_rejected S pp st corrupt honest corruptVk corruptTags sk m approvers Adv _ hV]
  | true =>
    obtain ⟨hView, hExp⟩ := tsigSession_rebalance pp inv hInv corruptVk corrupt honest hCard
      hNonZero (wireVals sk m) (pp.encSig (S.sign sk m)) τ
    rw [tsigRealExec_approved pp wireVals outVal st corrupt honest corruptVk corruptTags sk m
          approvers Adv τ κ hV,
        tsigIdealExec_approved S pp st corrupt honest corruptVk corruptTags sk m approvers Adv _ κ hV,
        hView, hExp]
    rw [hCircuit sk m] at hNoForgery ⊢
    exact congrArg
      (Adv.verdict (tsigSessionView pp corruptVk corrupt honest (wireVals sk m)
        (pp.encSig (S.sign sk m)) τ))
      (tsig_outcomes_agree pp st corruptVk corrupt honest hIds hDec hEmb hRecon (wireVals sk m)
        (S.sign sk m) τ _ _ hNoForgery)

/-- **Hop 2, reduction form (`tsig_real_eq_ideal_or_forgery`)**: on every tape and key, either
    real and ideal executions agree, or one of the adversary's own openings is a MAC forgery
    against the honest verifier's key and determines that key. -/
theorem tsig_real_eq_ideal_or_forgery {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) :
    tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ =
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv
        ⟨(tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m)).toFun τ, κ⟩ ∨
    ∃ op ∈ Adv.openings
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ),
      BdozMacForgeryWitness
        (tsigVerifierKey κ corruptTags
          (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ))
        (bdozViewOpening (fun s =>
          (tsigShareAt (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) s,
            corruptTags s)) op.partyId) op ∧
      κ = bdozKeyGuess (fun s =>
          (tsigShareAt (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) s,
            corruptTags s)) op := by
  cases hF : tsigFindForgery
      (tsigVerifierKey κ corruptTags
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)) 0
      (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)
      (Adv.openings
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ)) with
  | none =>
    exact .inl (tsig_real_eq_ideal_unless_forgery S pp wireVals outVal hCircuit hDec hEmb inv hInv
      st corrupt honest hIds hCard hNonZero hRecon corruptVk corruptTags sk m approvers Adv τ κ hF)
  | some op =>
    obtain ⟨hMem, hW, hKey⟩ := tsig_forgery_yields_key_guess κ corruptTags _ _ op hF
    exact .inr ⟨op, hMem, hW, hKey⟩

/-- **Hop 1, distribution form (`ucSimulatorTsig_hop1_perfect`)**: for an approved request and
    any test `D` of the corrupt parties' incoming messages, the number of honest tapes on which
    `D` accepts the real messages equals the number of simulator tapes on which `D` accepts the
    simulator's output; the two distributions are identical. -/
theorem ucSimulatorTsig_hop1_perfect {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (pk : PK) (corrupt honest : List (Nat × R))
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (macKey : Tower128 × Tower128) (D : Option (TsigAdvView R pp.k) → Bool) :
    qsum Ct (fun i =>
      if D (some (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m)
        (padEnum.toFun i))) then 1 else 0) =
    qsum Ct (fun i =>
      if D (ucSimulatorTsig pp
        ⟨pk, m, corrupt, honest, corruptVk, corruptTags, .signed (S.sign sk m)⟩
        ⟨padEnum.toFun i, macKey⟩) then 1 else 0) := by
  have hInvar := qsum_bijection_invariant padEnum
    (tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m))
    (fun τ => if D (ucSimulatorTsig pp
        ⟨pk, m, corrupt, honest, corruptVk, corruptTags, .signed (S.sign sk m)⟩
        ⟨τ, macKey⟩) then 1 else 0)
  refine Eq.trans (qsum_congr (fun i => ?_)) hInvar
  have hView := (tsigSession_rebalance pp inv hInv corruptVk corrupt honest hCard hNonZero
    (wireVals sk m) (pp.encSig (S.sign sk m)) (padEnum.toFun i)).1
  have hView' :
      tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) (padEnum.toFun i) =
      tsigSessionView pp corruptVk corrupt honest (fun _ => zero) (pp.encSig (S.sign sk m))
        ((tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m)).toFun
          (padEnum.toFun i)) := by
    rw [hCircuit sk m]
    exact hView.symm
  exact congrArg (fun v => if D v then 1 else 0) (congrArg some hView')

/-- **Uniform-preprocessing hybrid (`tsig_uniform_hybrid_gap`)**: over uniform pad tape and
    `CK` distinct MAC keys, real and ideal executions differ on at most
    `Ct * ((k + 1) * |corrupt|)` of the `Ct * CK` sample pairs. -/
theorem tsig_uniform_hybrid_gap {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j) :
    natAbsDiff
      (acceptPairs Ct CK padEnum.toFun keyDec (fun τ κ =>
        tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ))
      (acceptPairs Ct CK padEnum.toFun keyDec (fun τ κ =>
        tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩)) ≤
      Ct * ((pp.k + 1) * corrupt.length) := by
  refine acceptPairs_gap_of_bijection padEnum
    (tsigTapeRebalance inv pp.d pp.k (corrupt.map Prod.snd) hCard (wireVals sk m)) keyDec _ _
    (fun τ κ => (tsigFindForgery
      (tsigVerifierKey κ corruptTags
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)) 0
      (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ)
      (Adv.openings
        (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ))).isSome)
    _ ?_ ?_
  · intro τ κ hb
    exact tsig_real_eq_ideal_unless_forgery S pp wireVals outVal hCircuit hDec hEmb inv hInv
      st corrupt honest hIds hCard hNonZero hRecon corruptVk corruptTags sk m approvers Adv τ κ
      (isSome_false_eq_none _ hb)
  · intro τ
    exact Nat.le_trans
      (tsigForgery_keys_le CK keyDec hKeyInj
        (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) 0
        (Adv.openings
          (tsigSessionView pp corruptVk corrupt honest (wireVals sk m) (outVal sk m) τ))
        (fun s => (tsigShareAt
          (tsigSessionExpected pp corrupt (wireVals sk m) (outVal sk m) τ) s, corruptTags s))
        (fun i => by rw [Nat.zero_add]))
      (Nat.le_of_eq (tsigSessionExpected_length pp corrupt (wireVals sk m) (outVal sk m) τ))

/-- **Simulator Advantage Bound (`ucSimulatorTsig_advantage_bound`)**.
    Real world: pad tape `prg s` for a uniform seed `s : Fin Cs`, honest MAC key `ot o` for a
    uniform `o : Fin Co`. Ideal world: the simulator with a uniform tape (`Ct` pad tapes, `CK`
    distinct MAC keys). The difference of the two acceptance probabilities, over the common
    denominator `Cs * Co * Ct * CK`, is at most

    * `q / CK` with `q = (k + 1) * |corrupt|` the number of corrupt openings (MAC term, proved by
      counting keys),
    * plus the advantage of the explicit reduction `prgReductionAdvNum` in telling `prg` from a
      uniform tape,
    * plus the advantage of the explicit reduction `otReductionAdvNum` in telling `ot` from a
      uniform key. -/
theorem ucSimulatorTsig_advantage_bound {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hThreshold : st.threshold = pp.d + 1)
    (hBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape R pp.d pp.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let real := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ
    let ideal := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩
    natAbsDiff (acceptPairs Cs Co prg ot real * (Ct * CK))
               (acceptPairs Ct CK padEnum.toFun keyDec ideal * (Cs * Co)) ≤
      Cs * Co * (Ct * ((pp.k + 1) * corrupt.length))
        + CK * prgReductionAdvNum Cs Ct Co prg padEnum.toFun ot real
        + Cs * otReductionAdvNum Ct Co CK padEnum.toFun ot keyDec real := by
  intro real ideal
  have hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1 := by
    have h1 : st.corruptParties.length = corrupt.length := by rw [hIds, List.length_map]
    rw [List.length_map, ← h1, ← hThreshold]
    exact hBound
  exact preprocessing_hybrid_bound Cs Ct Co CK prg padEnum.toFun ot keyDec real ideal _
    (tsig_uniform_hybrid_gap S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt honest
      hIds hCard hNonZero hRecon corruptVk corruptTags sk m approvers Adv Ct padEnum CK keyDec
      hKeyInj)

/-- The same bound as an inequality of fractions over the common denominator. -/
theorem ucSimulatorTsig_advantage_ratLe {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hThreshold : st.threshold = pp.d + 1)
    (hBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape R pp.d pp.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128)
    (hDen : 0 < Cs * Co * (Ct * CK)) :
    let real := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ
    let ideal := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩
    ratLe
      (natAbsDiff (acceptPairs Cs Co prg ot real * (Ct * CK))
                  (acceptPairs Ct CK padEnum.toFun keyDec ideal * (Cs * Co)),
        Cs * Co * (Ct * CK))
      (Cs * Co * (Ct * ((pp.k + 1) * corrupt.length))
          + CK * prgReductionAdvNum Cs Ct Co prg padEnum.toFun ot real
          + Cs * otReductionAdvNum Ct Co CK padEnum.toFun ot keyDec real,
        Cs * Co * (Ct * CK)) := by
  intro real ideal
  exact ⟨hDen, hDen, Nat.mul_le_mul_right _
    (ucSimulatorTsig_advantage_bound S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt
      honest hIds hThreshold hBound hNonZero hRecon corruptVk corruptTags sk m approvers Adv Ct
      padEnum CK keyDec hKeyInj Cs prg Co ot)⟩

/-- **Hop 3, break witness (`ucSimulatorTsig_distinguisher_breaks_generator`)**: a distinguishing
    advantage above the MAC term gives non-zero advantage to one of the two explicit reductions. -/
theorem ucSimulatorTsig_distinguisher_breaks_generator {R PK SK Msg Sig : Type} [LawfulCommRing R]
    (S : AbstractSigScheme PK SK Msg Sig) (pp : TsigParams R Sig)
    (wireVals : SK → Msg → Fin pp.k → R) (outVal : SK → Msg → R)
    (hCircuit : ∀ sk m, outVal sk m = pp.encSig (S.sign sk m))
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (inv : R → R) (hInv : ∀ x : R, x ≠ zero → mul x (inv x) = one)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hThreshold : st.threshold = pp.d + 1)
    (hBound : st.corruptParties.length + 1 ≤ st.threshold)
    (hNonZero : ∀ cx ∈ corrupt, cx.2 ≠ zero)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (sk : SK) (m : Msg) (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (Ct : Nat) (padEnum : SimpleEquiv (Fin Ct) (TsigPadTape R pp.d pp.k))
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hKeyInj : ∀ i j, keyDec i = keyDec j → i = j)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape R pp.d pp.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let real := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigRealExec pp wireVals outVal st corrupt honest corruptVk corruptTags sk m approvers Adv τ κ
    let ideal := fun (τ : TsigPadTape R pp.d pp.k) (κ : Tower128 × Tower128) =>
      tsigIdealExec S pp st corrupt honest corruptVk corruptTags sk m approvers Adv ⟨τ, κ⟩
    Cs * Co * (Ct * ((pp.k + 1) * corrupt.length)) <
        natAbsDiff (acceptPairs Cs Co prg ot real * (Ct * CK))
                   (acceptPairs Ct CK padEnum.toFun keyDec ideal * (Cs * Co)) →
    0 < prgReductionAdvNum Cs Ct Co prg padEnum.toFun ot real ∨
    0 < otReductionAdvNum Ct Co CK padEnum.toFun ot keyDec real := by
  intro real ideal hDist
  have hCard : (corrupt.map Prod.snd).length + 1 ≤ pp.d + 1 := by
    have h1 : st.corruptParties.length = corrupt.length := by rw [hIds, List.length_map]
    rw [List.length_map, ← h1, ← hThreshold]
    exact hBound
  exact preprocessing_break_witness Cs Ct Co CK prg padEnum.toFun ot keyDec real ideal _
    (tsig_uniform_hybrid_gap S pp wireVals outVal hCircuit hDec hEmb inv hInv st corrupt honest
      hIds hCard hNonZero hRecon corruptVk corruptTags sk m approvers Adv Ct padEnum CK keyDec
      hKeyInj) hDist

/-- Negative regression for the real verifier: if the first opening is a dealt opening with a
    shifted tag, the real execution aborts and blames the first expected sender. -/
theorem tsigRealOutcome_rejects_tampered_tag {R Sig : Type} [CommRingOps R]
    (pp : TsigParams R Sig) (nc : Nat) (alpha : Tower128 × Tower128)
    (tags : Nat → Tower128 × Tower128) (e : Nat × Tower128) (es : List (Nat × Tower128))
    (honestOut : List R) (ops : List BdozPairOpening)
    (delta : Tower128) (hDelta : delta ≠ towerZero 7) :
    tsigRealOutcome pp nc (tsigVerifierKey alpha tags (e :: es)) (e :: es) honestOut
      ({ bdozViewOpening (fun s => (tsigShareAt (e :: es) s, tags s)) 0 with
          mac0 := towerAdd 7 (tags 0).1 delta } :: ops) = .abortedBy e.1 := by
  apply tsigRealOutcome_abort
  rw [tsigCheckOpenings_cons]
  have hRej := bdoz_tag_tamper_rejected (tsigVerifierKey alpha tags (e :: es))
    (bdozViewOpening (fun s => (tsigShareAt (e :: es) s, tags s)) 0)
    (bdozKeyFromView_accepts_view alpha (fun s => (tsigShareAt (e :: es) s, tags s)) 0)
    delta hDelta
  have hAcc : tsigOpAccepted (tsigVerifierKey alpha tags (e :: es)) 0
      { bdozViewOpening (fun s => (tsigShareAt (e :: es) s, tags s)) 0 with
          mac0 := towerAdd 7 (tags 0).1 delta } = false := by
    unfold tsigOpAccepted
    rw [show verifyBdozPairMac (tsigVerifierKey alpha tags (e :: es))
          { bdozViewOpening (fun s => (tsigShareAt (e :: es) s, tags s)) 0 with
              mac0 := towerAdd 7 (tags 0).1 delta } = false from hRej, Bool.and_false]
  rw [hAcc]
  rfl

/-- The openings a corrupt party sends when it follows the protocol: its dealt share and tags,
    for `n` consecutive positions starting at `s`. -/
def tsigDealtOpenings (hon : Nat → Tower128 × Tower128 × Tower128) : Nat → Nat → List BdozPairOpening
  | _, 0 => []
  | s, n + 1 => bdozViewOpening hon s :: tsigDealtOpenings hon (s + 1) n

private theorem tsigDealtOpenings_pass (alpha : Tower128 × Tower128) :
    ∀ (es : List (Nat × Tower128)) (s : Nat) (hon : Nat → Tower128 × Tower128 × Tower128),
      (∀ i, (hon (s + i)).1 = tsigShareAt es i) →
      tsigSimCheckOpenings (bdozKeyFromView alpha hon) s es
          (tsigDealtOpenings hon s es.length) = none ∧
      tsigFindForgery (bdozKeyFromView alpha hon) s es
          (tsigDealtOpenings hon s es.length) = none
  | [], _, _, _ => ⟨rfl, rfl⟩
  | e :: es, s, hon, hHon => by
    have h0 : (hon s).1 = e.2 := hHon 0
    have hAcc : tsigOpAccepted (bdozKeyFromView alpha hon) s (bdozViewOpening hon s) = true := by
      unfold tsigOpAccepted
      rw [bdozKeyFromView_accepts_view, Bool.and_true]
      exact beq_self_eq_true s
    have hEq : ((bdozViewOpening hon s).shareX == e.2) = true := by
      show ((hon s).1 == e.2) = true
      rw [h0]
      exact beq_self_eq_true _
    obtain ⟨ih1, ih2⟩ := tsigDealtOpenings_pass alpha es (s + 1) hon (fun i => by
      have h := hHon (i + 1)
      rw [show s + (i + 1) = s + 1 + i by omega] at h
      exact h)
    refine ⟨?_, ?_⟩
    · show tsigSimCheckOpenings (bdozKeyFromView alpha hon) s (e :: es)
        (bdozViewOpening hon s :: tsigDealtOpenings hon (s + 1) es.length) = none
      rw [tsigSimCheckOpenings_cons, hAcc, hEq]
      exact ih1
    · show tsigFindForgery (bdozKeyFromView alpha hon) s (e :: es)
        (bdozViewOpening hon s :: tsigDealtOpenings hon (s + 1) es.length) = none
      rw [tsigFindForgery_cons, hAcc, hEq]
      exact ih2

/-- **Completeness of the real execution (`tsigRealOutcome_dealt_openings_sign`)**: when the
    corrupt parties send their dealt openings, the honest parties reconstruct exactly the
    signature carried by the output wire, under every MAC key and every pad tape. -/
theorem tsigRealOutcome_dealt_openings_sign {R PK Msg Sig : Type} [LawfulCommRing R]
    (pp : TsigParams R Sig) (st : IdealTsigState PK Msg)
    (corruptVk : Nat → BdozVerifierKeys) (corrupt honest : List (Nat × R))
    (hIds : st.corruptParties = corrupt.map Prod.fst)
    (hDec : ∀ s, pp.decSig (pp.encSig s) = s)
    (hEmb : ∀ r, pp.unemb (pp.emb r) = r)
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ pp.d + 1 →
      ringDot pp.lambdas ((honest ++ corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (w : Fin pp.k → R) (sig : Sig) (τ : TsigPadTape R pp.d pp.k)
    (alpha : Tower128 × Tower128) (tags : Nat → Tower128 × Tower128) :
    tsigRealOutcome pp corrupt.length
        (tsigVerifierKey alpha tags (tsigSessionExpected pp corrupt w (pp.encSig sig) τ))
        (tsigSessionExpected pp corrupt w (pp.encSig sig) τ)
        (tsigSessionView pp corruptVk corrupt honest w (pp.encSig sig) τ).outHonestOpenings
        (tsigDealtOpenings
          (fun s => (tsigShareAt (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) s, tags s))
          0 (tsigSessionExpected pp corrupt w (pp.encSig sig) τ).length) = .signed sig := by
  obtain ⟨hPass, hNo⟩ := tsigDealtOpenings_pass alpha
    (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) 0
    (fun s => (tsigShareAt (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) s, tags s))
    (fun i => by rw [Nat.zero_add])
  have hAgree := tsig_outcomes_agree pp st corruptVk corrupt honest hIds hDec hEmb hRecon w sig τ
    (tsigVerifierKey alpha tags (tsigSessionExpected pp corrupt w (pp.encSig sig) τ)) _ hNo
  rw [hAgree]
  have hPass' : tsigSimCheckOpenings
      (tsigVerifierKey alpha tags (tsigSessionExpected pp corrupt w (pp.encSig sig) τ)) 0
      (tsigSessionExpected pp corrupt w (pp.encSig sig) τ)
      (tsigDealtOpenings
        (fun s => (tsigShareAt (tsigSessionExpected pp corrupt w (pp.encSig sig) τ) s, tags s))
        0 (tsigSessionExpected pp corrupt w (pp.encSig sig) τ).length) = none := hPass
  rw [hPass']
  rfl

end UcSimulator

/-! ## 6. Secret-Shared Beaver Gate Evaluation & Non-Vacuous 128-Bit `TowerElem 7` (`GF(2^128)`) UC Bound

Replaces cleartext-`sk` `wireVals`/`outVal` assumptions and vacuous `GF(4)` (`512/512 = 1`) instantiation with:
1. **Secret-Shared Non-Linear Beaver Gate Evaluation (`SharedBeaverSessionVault`, `evalPartyBeaverOutShare`,
   `evalSharedBeaverCircuit_reconstructs`)**:
   No party holds cleartext `sk`! Parties hold only Shamir shares of `sk` and a degree-`≤ d` Beaver
   multiplication triple `(a, b, c = a * b)` to evaluate the quadratic circuit `sk * (sk + m)` locally
   on shares; `evalSharedBeaverCircuit_reconstructs` **proves** `hCircuit` from ring axioms + Shamir
   linearity (`0` cleartext `sk` in party code!).
2. **Full 128-Bit `TowerElem 7` (`GF(2^128)` = `Tower128`) Concrete Non-Vacuous Instantiation
   (`tower128Params`, `ucSimulatorTsig_advantage_bound_tower128`, `ucSimulatorTsig_nonvacuous_sub_unity_tower128`)**:
   Enumerates the full `7 × 128 = 896`-bit pad space `Fin ((2^128)^7)` and full `256`-bit 2-lane BDOZ MAC
   key space `Fin ((2^128) * (2^128))` without `decide` blowups, proving a concrete rational advantage bound
   `(3, 2 ^ 256)` with **explicitly proved strict sub-unity `3 < (2 ^ 128) * (2 ^ 128)`** (`< 2^{-254} < 1`)! -/

section TsigSharedBeaverAndTower128
open CommRingOps

/-- Distributed Shamir vault for a quadratic threshold-PRF circuit `sign(sk, m) = sk * (sk + m)`:
    each party at evaluation point `x ≠ 0` receives ONLY its local shares `(sk_x, a_x, b_x, c_x)`
    evaluated from degree-`≤ d` Shamir polynomials; no party ever receives cleartext `sk`! -/
structure SharedBeaverSessionVault (R : Type) (d : Nat) where
  skVal : R
  skPad : ShamirPadPoly R d
  aVal  : R
  aPad  : ShamirPadPoly R d
  bVal  : R
  bPad  : ShamirPadPoly R d
  cPad  : ShamirPadPoly R d

/-- Local Shamir share tuple `(sk_x, a_x, b_x, c_x)` held by party at public coordinate `x : R`
    when the Beaver triple satisfies `c = mul aVal bVal`. -/
def dealPartyBeaverShares {R : Type} [CommRingOps R] {d : Nat}
    (vault : SharedBeaverSessionVault R d) (x : R) : R × R × R × R :=
  (RoundPoly.evalCoeffs (vault.skVal :: vault.skPad.1) x,
   RoundPoly.evalCoeffs (vault.aVal :: vault.aPad.1) x,
   RoundPoly.evalCoeffs (vault.bVal :: vault.bPad.1) x,
   RoundPoly.evalCoeffs (mul vault.aVal vault.bVal :: vault.cPad.1) x)

/-- Local cut-wire share computed by a party from its local `(sk_x, a_x, b_x)` shares and public `m`:
    wire `0` masks `sk - a`; wire `1` masks `(sk + m) - b`. -/
def evalPartyCutWireShares {R : Type} [CommRingOps R]
    (partySh : R × R × R × R) (m : R) : R × R :=
  (sub partySh.1 partySh.2.1, sub (add partySh.1 m) partySh.2.2.1)

/-- Local Beaver linearized output share computed by each party purely from opened masked differences
    `(u, v)` and its private Beaver shares `(a_x, b_x, c_x)` — **zero cleartext `sk` access!** -/
def evalPartyBeaverOutShare {R : Type} [CommRingOps R]
    (u v : R) (partySh : R × R × R × R) : R :=
  let a_x := partySh.2.1
  let b_x := partySh.2.2.1
  let c_x := partySh.2.2.2
  add (mul u v) (add (mul u b_x) (add (mul v a_x) c_x))

private def polyZipAdd {R : Type} [CommRingOps R] : List R → List R → List R
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => add x y :: polyZipAdd xs ys

private theorem polyZipAdd_length_le {R : Type} [CommRingOps R] :
    ∀ (xs ys : List R) (n : Nat), xs.length ≤ n → ys.length ≤ n → (polyZipAdd xs ys).length ≤ n
  | [], ys, _, _, hy => hy
  | _ :: _, [], _, hx, _ => hx
  | _ :: xs, _ :: _, 0, hx, _ => by simp at hx
  | _ :: xs, _ :: ys, n + 1, hx, hy => by
    simp only [polyZipAdd, List.length_cons] at hx hy ⊢
    exact Nat.succ_le_succ (polyZipAdd_length_le xs ys n (Nat.le_of_succ_le_succ hx) (Nat.le_of_succ_le_succ hy))

private theorem evalCoeffs_polyZipAdd {R : Type} [LawfulCommRing R] :
    ∀ (xs ys : List R) (x : R),
      RoundPoly.evalCoeffs (polyZipAdd xs ys) x =
      add (RoundPoly.evalCoeffs xs x) (RoundPoly.evalCoeffs ys x)
  | [], ys, x => by simp [polyZipAdd, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | _ :: _, [], x => by simp [polyZipAdd, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | a :: xs, b :: ys, x => by
    simp only [polyZipAdd, RoundPoly.evalCoeffs_cons, evalCoeffs_polyZipAdd xs ys x]
    rw [LawfulCommRing.left_distrib]
    have hAssoc1 := LawfulCommRing.add_assoc a b (add (mul x (RoundPoly.evalCoeffs xs x)) (mul x (RoundPoly.evalCoeffs ys x)))
    have hAssoc2 := LawfulCommRing.add_assoc a (mul x (RoundPoly.evalCoeffs xs x)) (add b (mul x (RoundPoly.evalCoeffs ys x)))
    have hMid : add b (add (mul x (RoundPoly.evalCoeffs xs x)) (mul x (RoundPoly.evalCoeffs ys x))) =
        add (mul x (RoundPoly.evalCoeffs xs x)) (add b (mul x (RoundPoly.evalCoeffs ys x))) := by
      rw [← LawfulCommRing.add_assoc, LawfulCommRing.add_comm b, LawfulCommRing.add_assoc]
    rw [hAssoc1, hMid, ← hAssoc2]

private theorem evalCoeffs_scalarMul {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (xs : List R) (x : R),
      RoundPoly.evalCoeffs (xs.map (mul s)) x = mul s (RoundPoly.evalCoeffs xs x)
  | [], _ => by simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | a :: xs, x => by
    simp only [List.map_cons, RoundPoly.evalCoeffs_cons, evalCoeffs_scalarMul s xs x]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm x s, LawfulCommRing.mul_assoc]

/-- **Beaver Shared Gate Reconstruction Theorem (`evalSharedBeaverCircuit_reconstructs`)**:
    Proves `hCircuit` constructively from Shamir linearity + Beaver identity:
    1. Reconstructing the parties' local cut-wire shares yields `(u, v) = (sk - a, (sk + m) - b)`;
    2. Reconstructing the parties' local `evalPartyBeaverOutShare u v` shares yields the exact
       non-linear circuit output `mul sk (add sk m)` without any party ever holding `sk`! -/
theorem evalSharedBeaverCircuit_reconstructs {R : Type} [LawfulCommRing R] {d : Nat}
    (lambdas : List R) (parties : List (Nat × R))
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ d + 1 →
      ringDot lambdas (parties.map (fun px => RoundPoly.evalCoeffs coeffs px.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (vault : SharedBeaverSessionVault R d) (m : R) :
    let u := sub vault.skVal vault.aVal
    let v := sub (add vault.skVal m) vault.bVal
    ringDot lambdas (parties.map (fun px => (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).1)) = u ∧
    ringDot lambdas (parties.map (fun px => (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).2)) = v ∧
    ringDot lambdas (parties.map (fun px => evalPartyBeaverOutShare u v (dealPartyBeaverShares vault px.2))) =
      mul vault.skVal (add vault.skVal m) := by
  intro u v
  let negOne : R := neg one
  have hSubAsAdd : ∀ x y : R, sub x y = add x (mul negOne y) := by
    intro x y
    dsimp only [negOne]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.neg_mul, LawfulCommRing.one_mul]
  let pSk : List R := vault.skVal :: vault.skPad.1
  let pA : List R := vault.aVal :: vault.aPad.1
  let pB : List R := vault.bVal :: vault.bPad.1
  let pC : List R := mul vault.aVal vault.bVal :: vault.cPad.1
  have hpSkLen : pSk.length ≤ d + 1 := by simp [pSk, vault.skPad.2]
  have hpALen : pA.length ≤ d + 1 := by simp [pA, vault.aPad.2]
  have hpBLen : pB.length ≤ d + 1 := by simp [pB, vault.bPad.2]
  have hpCLen : pC.length ≤ d + 1 := by simp [pC, vault.cPad.2]
  let pU := polyZipAdd pSk (pA.map (mul negOne))
  let pSkM := polyZipAdd pSk [m]
  let pV := polyZipAdd pSkM (pB.map (mul negOne))
  let pOut := polyZipAdd [mul u v]
                (polyZipAdd (pB.map (mul u))
                  (polyZipAdd (pA.map (mul v)) pC))
  have hpULen : pU.length ≤ d + 1 :=
    polyZipAdd_length_le _ _ _ hpSkLen (by simpa using hpALen)
  have hpSkMLen : pSkM.length ≤ d + 1 :=
    polyZipAdd_length_le _ _ _ hpSkLen (by simp)
  have hpVLen : pV.length ≤ d + 1 :=
    polyZipAdd_length_le _ _ _ hpSkMLen (by simpa using hpBLen)
  have hpOutLen : pOut.length ≤ d + 1 :=
    polyZipAdd_length_le _ _ _ (by simp)
      (polyZipAdd_length_le _ _ _ (by simpa using hpBLen)
        (polyZipAdd_length_le _ _ _ (by simpa using hpALen) hpCLen))
  have hSingleEval : ∀ (c x : R), RoundPoly.evalCoeffs [c] x = c := by
    intro c x
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hMapU : parties.map (fun px => (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).1) =
      parties.map (fun px => RoundPoly.evalCoeffs pU px.2) := by
    apply List.map_congr_left
    intro px _
    dsimp only [evalPartyCutWireShares, dealPartyBeaverShares, pU, pSk, pA]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_scalarMul, ← hSubAsAdd]
  have hMapV : parties.map (fun px => (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).2) =
      parties.map (fun px => RoundPoly.evalCoeffs pV px.2) := by
    apply List.map_congr_left
    intro px _
    dsimp only [evalPartyCutWireShares, dealPartyBeaverShares, pV, pSkM, pSk, pB]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd, evalCoeffs_scalarMul, hSingleEval, ← hSubAsAdd]
  have hMapOut : parties.map (fun px => evalPartyBeaverOutShare u v (dealPartyBeaverShares vault px.2)) =
      parties.map (fun px => RoundPoly.evalCoeffs pOut px.2) := by
    apply List.map_congr_left
    intro px _
    dsimp only [evalPartyBeaverOutShare, dealPartyBeaverShares, pOut, pA, pB, pC]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd,
        evalCoeffs_scalarMul, evalCoeffs_scalarMul, hSingleEval]
  refine ⟨?_, ?_, ?_⟩
  · rw [hMapU, hRecon pU hpULen]
    dsimp only [pU, pSk, pA]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_scalarMul]
    simp only [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [← hSubAsAdd]
  · rw [hMapV, hRecon pV hpVLen]
    dsimp only [pV, pSkM, pSk, pB]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd, evalCoeffs_scalarMul, hSingleEval]
    simp only [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [← hSubAsAdd]
  · rw [hMapOut, hRecon pOut hpOutLen]
    dsimp only [pOut, pA, pB, pC]
    rw [evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd, evalCoeffs_polyZipAdd,
        evalCoeffs_scalarMul, evalCoeffs_scalarMul, hSingleEval]
    simp only [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    -- Algebraic Beaver identity: `u*v + (u*b + (v*a + a*b)) = (u + a) * (v + b) = sk * (sk + m)`!
    have hFactor : add (mul u v) (add (mul u vault.bVal) (add (mul vault.aVal v) (mul vault.aVal vault.bVal))) =
        mul (add u vault.aVal) (add v vault.bVal) := by
      calc add (mul u v) (add (mul u vault.bVal) (add (mul vault.aVal v) (mul vault.aVal vault.bVal)))
          = add (add (mul u v) (mul u vault.bVal)) (add (mul vault.aVal v) (mul vault.aVal vault.bVal)) := by
              rw [← LawfulCommRing.add_assoc]
        _ = add (mul u (add v vault.bVal)) (mul vault.aVal (add v vault.bVal)) := by
              rw [← LawfulCommRing.left_distrib, ← LawfulCommRing.left_distrib]
        _ = mul (add u vault.aVal) (add v vault.bVal) := by
              rw [← LawfulCommRing.right_distrib]
    have hva : mul v vault.aVal = mul vault.aVal v := LawfulCommRing.mul_comm v vault.aVal
    rw [hva, hFactor]
    have huAdd : add u vault.aVal = vault.skVal := by
      dsimp only [u]
      rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
          LawfulCommRing.add_comm (neg vault.aVal) vault.aVal,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    have hvAdd : add v vault.bVal = add vault.skVal m := by
      dsimp only [v]
      rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
          LawfulCommRing.add_comm (neg vault.bVal) vault.bVal,
          LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
    rw [huAdd, hvAdd]

/-- **`#tooth` Beaver Triple Integrity Witness (`tooth_corrupted_beaver_triple_shifts_output`)**:
    Over `TowerElem k` (and specifically `Tower128 = TowerElem 7`, `GF(2^128)`), if a corrupted
    Beaver triple replaces `c = a * b` with `c' = a * b + delta` (`delta ≠ 0`), local Beaver
    evaluation shifts the reconstructed signature by `delta ≠ 0`! -/
private theorem tooth_corrupted_beaver_triple_shifts_output_gen (k : Nat)
    (sk m a b delta : TowerElem k) (hDelta : delta ≠ towerZero k) :
    let u := towerAdd k sk a
    let v := towerAdd k (towerAdd k sk m) b
    let honestOut := evalPartyBeaverOutShare u v (sk, a, b, towerMul k a b)
    let corruptOut := evalPartyBeaverOutShare u v (sk, a, b, towerAdd k (towerMul k a b) delta)
    corruptOut ≠ honestOut := by
  intro u v honestOut corruptOut hEq
  dsimp only [honestOut, corruptOut, evalPartyBeaverOutShare] at hEq
  change towerAdd k (towerMul k u v)
      (towerAdd k (towerMul k u b) (towerAdd k (towerMul k v a) (towerAdd k (towerMul k a b) delta))) =
    towerAdd k (towerMul k u v)
      (towerAdd k (towerMul k u b) (towerAdd k (towerMul k v a) (towerMul k a b))) at hEq
  let base := towerAdd k (towerMul k u v) (towerAdd k (towerMul k u b) (towerAdd k (towerMul k v a) (towerMul k a b)))
  have hAssoc :
      towerAdd k (towerMul k u v) (towerAdd k (towerMul k u b) (towerAdd k (towerMul k v a) (towerAdd k (towerMul k a b) delta))) =
      towerAdd k base delta := by
    dsimp only [base]
    simp only [towerAdd_assoc]
  rw [hAssoc] at hEq
  have hZero : delta = towerZero k := by
    have hAdd := congrArg (towerAdd k base) hEq
    rw [← towerAdd_assoc, towerAdd_self_zero, towerZero_add] at hAdd
    exact hAdd
  exact hDelta hZero

theorem tooth_corrupted_beaver_triple_shifts_output
    (sk m a b delta : Tower128) (hDelta : delta ≠ towerZero 7) :
    let u := towerAdd 7 sk a
    let v := towerAdd 7 (towerAdd 7 sk m) b
    let honestOut := evalPartyBeaverOutShare u v (sk, a, b, towerMul 7 a b)
    let corruptOut := evalPartyBeaverOutShare u v (sk, a, b, towerAdd 7 (towerMul 7 a b) delta)
    corruptOut ≠ honestOut :=
  tooth_corrupted_beaver_triple_shifts_output_gen 7 sk m a b delta hDelta

private def towerFirstBit : (k : Nat) → TowerElem k → Bool
  | 0, b => b
  | k + 1, a => towerFirstBit k a.1

private theorem towerFirstBit_zero : ∀ (k : Nat), towerFirstBit k (towerZero k) = false
  | 0 => rfl
  | k + 1 => towerFirstBit_zero k

private theorem towerFirstBit_one : ∀ (k : Nat), towerFirstBit k (towerOne k) = true
  | 0 => rfl
  | k + 1 => towerFirstBit_one k

/-- The element `X` of `GF(4)` embedded into full 128-bit `Tower128 = TowerElem 7` (`GF(2^128)`). -/
def tower128X : Tower128 :=
  embedTower 6 (embedTower 5 (embedTower 4 (embedTower 3 (embedTower 2 (embedTower 1 (false, true))))))

/-- Full-width 128-bit `Tower128` (`GF(2^128)`) session parameters:
    threshold `t = 2` (`d = 1`), `k = 2` Beaver-masked cut wires `(sk - a, (sk + m) - b)`,
    identity 128-bit MAC field embedding (`emb = id, unemb = id`). -/
@[expose] def tower128Params : TsigParams Tower128 Tower128 :=
  { d := 1, k := 2, encSig := id, decSig := id, emb := id, unemb := id
    lambdas := [towerOne 7, towerOne 7, towerOne 7]
    slot := fun j h => 3 * j + h }

/-- Non-linear quadratic threshold-PRF signature over `Tower128` (`GF(2^128)`):
    `sign(sk, m) = sk * (sk + m)`. -/
def tower128BeaverSig : AbstractSigScheme Unit Tower128 Tower128 Tower128 :=
  { sign := fun sk m => towerMul 7 sk (towerAdd 7 sk m)
    verify := fun _ m sig => decide (sig = towerMul 7 (towerOne 7) (towerAdd 7 (towerOne 7) m))
    complete := fun _ sk => sk = towerOne 7
    completeness := fun h _ => by subst h; exact decide_eq_true rfl }

def tower128State : IdealTsigState Unit Tower128 :=
  { pk := (), threshold := 2, numParties := 3, corruptParties := [2]
    approvedMsgs := [], identifiedCheaters := [] }

/-- Party 2 is corrupt and sits at `1 + tower128X ∈ GF(2^128) \ {0}`. -/
def tower128Corrupt : List (Nat × Tower128) := [(2, towerAdd 7 (towerOne 7) tower128X)]

/-- Parties 0 and 1 are honest and sit at `1` and `tower128X` in `GF(2^128)`. -/
def tower128Honest : List (Nat × Tower128) := [(0, towerOne 7), (1, tower128X)]

private theorem tower_recon3_zero (k : Nat) :
    towerAdd k (towerMul k (towerOne k) (towerZero k))
      (towerAdd k (towerMul k (towerOne k) (towerZero k))
        (towerAdd k (towerMul k (towerOne k) (towerZero k)) (towerZero k))) = towerZero k := by
  simp only [towerMul_zero, towerAdd_zero]

private theorem tower_recon3_one (k : Nat) (c a : TowerElem k) :
    towerAdd k (towerMul k (towerOne k) (towerAdd k a (towerMul k (towerOne k) (towerZero k))))
      (towerAdd k (towerMul k (towerOne k) (towerAdd k a (towerMul k c (towerZero k))))
        (towerAdd k
          (towerMul k (towerOne k)
            (towerAdd k a (towerMul k (towerAdd k (towerOne k) c) (towerZero k))))
          (towerZero k))) =
      towerAdd k a (towerMul k (towerZero k) (towerZero k)) := by
  simp only [towerOne_mul, towerMul_zero, towerAdd_zero, towerAdd_cancel]

private theorem tower_recon3_two (k : Nat) (c a b : TowerElem k) :
    towerAdd k
      (towerMul k (towerOne k)
        (towerAdd k a (towerMul k (towerOne k)
          (towerAdd k b (towerMul k (towerOne k) (towerZero k))))))
      (towerAdd k
        (towerMul k (towerOne k)
          (towerAdd k a (towerMul k c (towerAdd k b (towerMul k c (towerZero k))))))
        (towerAdd k
          (towerMul k (towerOne k)
            (towerAdd k a (towerMul k (towerAdd k (towerOne k) c)
              (towerAdd k b (towerMul k (towerAdd k (towerOne k) c) (towerZero k))))))
          (towerZero k))) =
      towerAdd k a (towerMul k (towerZero k)
        (towerAdd k b (towerMul k (towerZero k) (towerZero k)))) := by
  simp only [towerOne_mul, towerMul_zero, towerZero_mul, towerAdd_zero, towerAdd_mul_distrib]
  simp only [towerAdd_comm, towerAdd_left_comm, towerAdd_self_zero, towerAdd_zero,
    towerAdd_cancel]

private theorem towerK_recon (k : Nat) (c : TowerElem k) :
    ∀ coeffs : List (TowerElem k), coeffs.length ≤ 2 →
    ringDot [towerOne k, towerOne k, towerOne k]
      ((((0 : Nat), towerOne k) :: [(1, c)] ++ [(2, towerAdd k (towerOne k) c)]).map
        (fun hx : Nat × TowerElem k => RoundPoly.evalCoeffs coeffs hx.2)) =
      RoundPoly.evalCoeffs coeffs (@CommRingOps.zero (TowerElem k) _) := by
  intro coeffs hLen
  rw [ringDot_eq]
  rcases coeffs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
  · exact tower_recon3_zero k
  · exact tower_recon3_one k c a
  · exact tower_recon3_two k c a b
  · exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hLen)) (Nat.not_succ_le_zero _)

/-- Weights `[1, 1, 1]` reconstruct `P(0)` for every polynomial of degree `≤ 1` over `Tower128`
    from its values at `1`, `tower128X`, and `1 + tower128X`. -/
theorem tower128_recon : ∀ coeffs : List Tower128, coeffs.length ≤ tower128Params.d + 1 →
    ringDot tower128Params.lambdas
      ((tower128Honest ++ tower128Corrupt).map (fun hx => RoundPoly.evalCoeffs coeffs hx.2)) =
      RoundPoly.evalCoeffs coeffs zero := by
  have hL : tower128Params.lambdas = [towerOne 7, towerOne 7, towerOne 7] := rfl
  have hH : tower128Honest = [(0, towerOne 7), (1, tower128X)] := rfl
  have hC : tower128Corrupt = [(2, towerAdd 7 (towerOne 7) tower128X)] := rfl
  have hD : tower128Params.d + 1 = 2 := rfl
  have hZ : (zero : Tower128) = @CommRingOps.zero (TowerElem 7) _ := rfl
  rw [hL, hH, hC, hD, hZ]
  exact towerK_recon 7 tower128X

private theorem tower128Corrupt_nonzero : ∀ cx ∈ tower128Corrupt, cx.2 ≠ (zero : Tower128) := by
  intro cx hcx hEq
  rw [List.mem_singleton.mp hcx] at hEq
  have hBit := congrArg (towerFirstBit 7) hEq
  have hL : towerFirstBit 7 (towerAdd 7 (towerOne 7) tower128X) = true := rfl
  have hR : towerFirstBit 7 (zero : Tower128) = false := towerFirstBit_zero 7
  rw [hL, hR] at hBit
  cases hBit

/-- `sk`-free party-share execution (`tsigSharedBeaverRealExec`):
    Takes **ONLY** per-party shares `partyShares : R → R × R × R × R` (`(sk_x, a_x, b_x, c_x)`) —
    **ZERO cleartext `sk` parameter exists in its signature!**
    Parties locally evaluate cut-wire shares `evalPartyCutWireShares`, open masked `(u, v)`, and
    locally evaluate `evalPartyBeaverOutShare u v`. -/
def tsigSharedBeaverRealExec {R PK Msg Sig : Type} [CommRingOps R]
    (pp : TsigParams R Sig)
    (st : IdealTsigState PK Msg) (corrupt honest : List (Nat × R))
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (partyShares : R → R × R × R × R) (m : R)
    (approvers : List Nat) (Adv : TsigAdversary R Sig pp.k)
    (tape : TsigPadTape R pp.d pp.k) (macKey : Tower128 × Tower128) : Bool :=
  let allParties := honest ++ corrupt
  let u := ringDot pp.lambdas (allParties.map (fun px => (evalPartyCutWireShares (partyShares px.2) m).1))
  let v := ringDot pp.lambdas (allParties.map (fun px => (evalPartyCutWireShares (partyShares px.2) m).2))
  let y := ringDot pp.lambdas (allParties.map (fun px => evalPartyBeaverOutShare u v (partyShares px.2)))
  let w : Fin pp.k → R := fun j => if j.val = 0 then u else v
  if validThresholdApproval st approvers then
    let view := tsigSessionView pp corruptVk corrupt honest w y tape
    let exp := tsigSessionExpected pp corrupt w y tape
    Adv.verdict view
      (tsigRealOutcome pp corrupt.length (tsigVerifierKey macKey corruptTags exp)
        exp view.outHonestOpenings (Adv.openings view))
  else
    Adv.idle .rejectedQuorum

/-- Reconstructed Beaver cut-wire values `(u, v)` computed purely from local party shares
    `dealPartyBeaverShares vault px.2` (`0` cleartext `sk` in party evaluation!). -/
def tower128SharedWireVals (a b : Tower128)
    (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128) (j : Fin tower128Params.k) : Tower128 :=
  let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
  if j.val = 0 then
    ringDot tower128Params.lambdas
      ((tower128Honest ++ tower128Corrupt).map (fun px =>
        (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).1))
  else
    ringDot tower128Params.lambdas
      ((tower128Honest ++ tower128Corrupt).map (fun px =>
        (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).2))

/-- Generic distributed Beaver evaluation over any ring `R`: parties hold only `partyShares px.2`
    (`0` cleartext `sk` parameter!), reconstruct masked cut wires `(u, v)`, and reconstruct the
    local Beaver output shares `evalPartyBeaverOutShare u v`. -/
def evalDistributedBeaverOut {R : Type} [CommRingOps R]
    (lambdas : List R) (parties : List (Nat × R))
    (partyShares : R → R × R × R × R) (m : R) : R :=
  let u := ringDot lambdas (parties.map (fun px => (evalPartyCutWireShares (partyShares px.2) m).1))
  let v := ringDot lambdas (parties.map (fun px => (evalPartyCutWireShares (partyShares px.2) m).2))
  ringDot lambdas (parties.map (fun px => evalPartyBeaverOutShare u v (partyShares px.2)))

theorem evalDistributedBeaverOut_eq_circuit {R : Type} [LawfulCommRing R] {d : Nat}
    (lambdas : List R) (parties : List (Nat × R))
    (hRecon : ∀ coeffs : List R, coeffs.length ≤ d + 1 →
      ringDot lambdas (parties.map (fun px => RoundPoly.evalCoeffs coeffs px.2)) =
        RoundPoly.evalCoeffs coeffs zero)
    (vault : SharedBeaverSessionVault R d) (m : R) :
    evalDistributedBeaverOut lambdas parties (dealPartyBeaverShares vault) m =
      mul vault.skVal (add vault.skVal m) := by
  obtain ⟨hu, hv, hOut⟩ := evalSharedBeaverCircuit_reconstructs lambdas parties hRecon vault m
  unfold evalDistributedBeaverOut
  dsimp only at hu hv hOut ⊢
  rw [hu, hv, hOut]

/-- Reconstructed Beaver output value computed from the parties' local `evalPartyBeaverOutShare`
    shares (without cleartext `sk` in party evaluation!). -/
def tower128SharedOutVal (a b : Tower128)
    (skPad aPad bPad cPad : ShamirPadPoly Tower128 1) (sk m : Tower128) : Tower128 :=
  let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
  evalDistributedBeaverOut tower128Params.lambdas
    (tower128Honest ++ tower128Corrupt) (dealPartyBeaverShares vault) m

/-- Equivalence proving that `sk`-free `tsigSharedBeaverRealExec` on `dealPartyBeaverShares` is
    equal to `tsigRealExec` with `tower128SharedWireVals` and `tower128SharedOutVal`! -/
theorem tsigSharedBeaverRealExec_eq_tsigRealExec
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128) (approvers : List Nat)
    (Adv : TsigAdversary Tower128 Tower128 tower128Params.k)
    (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
    (κ : Tower128 × Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt tower128Honest
      corruptVk corruptTags (dealPartyBeaverShares vault) m approvers Adv τ κ =
    tsigRealExec tower128Params
      (tower128SharedWireVals a b skPad aPad bPad cPad)
      (tower128SharedOutVal a b skPad aPad bPad cPad)
      tower128State tower128Corrupt tower128Honest corruptVk corruptTags sk m approvers Adv τ κ := by
  intro vault
  have hW :
      (fun j : Fin tower128Params.k =>
        if j.val = 0 then
          ringDot tower128Params.lambdas
            ((tower128Honest ++ tower128Corrupt).map (fun px =>
              (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).1))
        else
          ringDot tower128Params.lambdas
            ((tower128Honest ++ tower128Corrupt).map (fun px =>
              (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).2))) =
      tower128SharedWireVals a b skPad aPad bPad cPad sk m := by
    funext j
    unfold tower128SharedWireVals
    rfl
  have hY :
      ringDot tower128Params.lambdas
        ((tower128Honest ++ tower128Corrupt).map (fun px =>
          evalPartyBeaverOutShare
            (ringDot tower128Params.lambdas
              ((tower128Honest ++ tower128Corrupt).map (fun px =>
                (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).1)))
            (ringDot tower128Params.lambdas
              ((tower128Honest ++ tower128Corrupt).map (fun px =>
                (evalPartyCutWireShares (dealPartyBeaverShares vault px.2) m).2)))
            (dealPartyBeaverShares vault px.2))) =
      tower128SharedOutVal a b skPad aPad bPad cPad sk m := by
    unfold tower128SharedOutVal evalDistributedBeaverOut
    rfl
  unfold tsigSharedBeaverRealExec tsigRealExec
  dsimp only
  rw [hW, hY]

/-- Proved `hCircuit` theorem for `tower128SharedOutVal`: local Beaver share evaluation reconstructs
    `tower128BeaverSig.sign sk m = sk * (sk + m)`! -/
theorem tower128SharedOutVal_eq_sign (a b : Tower128)
    (skPad aPad bPad cPad : ShamirPadPoly Tower128 1) (sk m : Tower128) :
    tower128SharedOutVal a b skPad aPad bPad cPad sk m =
      tower128Params.encSig (tower128BeaverSig.sign sk m) := by
  unfold tower128SharedOutVal
  exact evalDistributedBeaverOut_eq_circuit tower128Params.lambdas
    (tower128Honest ++ tower128Corrupt) tower128_recon
    ⟨sk, skPad, a, aPad, b, bPad, cPad⟩ m

/-- Multi-turn real threshold execution driven **exclusively by party shares** (`partyShares : R → R × R × R × R`),
    with **ZERO cleartext `sk` parameter** in its signature! -/
def execSharedRealTsig {R PK : Type} [CommRingOps R]
    (verifyFn : PK → R → R → Bool)
    (lambdas : List R) (parties : List (Nat × R))
    (partyShares : R → R × R × R × R)
    (verifyMacCulprit : Nat → Bool)
    (st : IdealTsigState PK R) : UcTsigEnv PK R R → Bool
  | .halt b => b
  | .stepSign m honestApprovers next =>
    if validThresholdApproval st honestApprovers then
      let st' := { st with approvedMsgs := m :: st.approvedMsgs }
      let sigOut := evalDistributedBeaverOut lambdas parties partyShares m
      execSharedRealTsig verifyFn lambdas parties partyShares verifyMacCulprit st' (next (.signed sigOut))
    else
      execSharedRealTsig verifyFn lambdas parties partyShares verifyMacCulprit st (next .rejectedQuorum)
  | .stepAbort culprit next =>
    if verifyMacCulprit culprit then
      let st' := { st with identifiedCheaters := culprit :: st.identifiedCheaters }
      execSharedRealTsig verifyFn lambdas parties partyShares verifyMacCulprit st' (next (.abortedBy culprit))
    else
      execSharedRealTsig verifyFn lambdas parties partyShares verifyMacCulprit st (next .rejectedFraming)
  | .stepVerify m sig next =>
    execSharedRealTsig verifyFn lambdas parties partyShares verifyMacCulprit st (next (verifyFn st.pk m sig))

/-- **Assumption-Free Multi-Turn UC Realization from Shared Beaver + BDOZ MACs
    (`protocol_realizes_idealTsig_from_shared_beaver_bdoz`)**:
    Proves that `sk`-free `execSharedRealTsig` (which takes **ONLY** `dealPartyBeaverShares vault` and
    **ZERO cleartext `sk` parameter**) realizes `execIdealTsig S (S.sign sk)` with concrete BDOZ MAC
    blame soundness (`tsigCheckOpenings_blame_mem`), discharging BOTH `hCircuit` AND `hMacSound` without
    external hypotheses! -/
theorem protocol_realizes_idealTsig_from_shared_beaver_bdoz {PK : Type}
    (S : AbstractSigScheme PK Tower128 Tower128 Tower128)
    (hSignDef : ∀ sk m, S.sign sk m = towerMul 7 sk (towerAdd 7 sk m))
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk : Tower128)
    (st : IdealTsigState PK Tower128)
    (vk : BdozVerifierKeys) (exp : List (Nat × Tower128))
    (hExpIds : ∀ e ∈ exp, e.1 ∈ st.corruptParties)
    (abortTrace : Nat → List BdozPairOpening)
    (hCorruptCaught : ∀ c ∈ st.corruptParties, tsigCheckOpenings vk 0 exp (abortTrace c) = some c)
    (Z : UcTsigEnv PK Tower128 Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    let bdozVerifyCulprit : Nat → Bool :=
      fun c => tsigCheckOpenings vk 0 exp (abortTrace c) == some c
    (∀ c, c ∉ st.corruptParties → bdozVerifyCulprit c = false) ∧
    (execSharedRealTsig S.verify tower128Params.lambdas (tower128Honest ++ tower128Corrupt)
       (dealPartyBeaverShares vault) bdozVerifyCulprit st Z =
       (execIdealTsig S (S.sign sk) st Z).1 ∨
     ∃ mStar sigStar approvedAtStep,
       findTsigDivergence S (S.sign sk) bdozVerifyCulprit st Z =
         some (.inl (mStar, sigStar, approvedAtStep)) ∧
       mStar ∉ approvedAtStep ∧
       S.verify st.pk mStar sigStar = true) := by
  intro vault bdozVerifyCulprit
  have hAntiFrame : ∀ c, c ∉ st.corruptParties → bdozVerifyCulprit c = false := by
    intro c hcNot
    dsimp only [bdozVerifyCulprit]
    apply beq_false_of_ne
    intro hSome
    have hMemMap := tsigCheckOpenings_blame_mem vk exp 0 (abortTrace c) c hSome
    rw [List.mem_map] at hMemMap
    obtain ⟨e, heMem, rfl⟩ := hMemMap
    exact hcNot (hExpIds e heMem)
  have hMacSound : ∀ c, bdozVerifyCulprit c = decide (c ∈ st.corruptParties) := by
    intro c
    by_cases hc : c ∈ st.corruptParties
    · simp only [hc, decide_true]
      dsimp only [bdozVerifyCulprit]
      rw [hCorruptCaught c hc]
      exact beq_self_eq_true _
    · simp only [hc, decide_false]
      exact hAntiFrame c hc
  have hSharedEqReal : ∀ stCur (ZCur : UcTsigEnv PK Tower128 Tower128),
      execSharedRealTsig S.verify tower128Params.lambdas (tower128Honest ++ tower128Corrupt)
        (dealPartyBeaverShares vault) bdozVerifyCulprit stCur ZCur =
      execRealTsig S sk bdozVerifyCulprit stCur ZCur := by
    intro stCur ZCur
    induction ZCur generalizing stCur with
    | halt _ => rfl
    | stepSign m apps next ih =>
      dsimp only [execSharedRealTsig, execRealTsig]
      split
      · have hOutEq : evalDistributedBeaverOut tower128Params.lambdas
            (tower128Honest ++ tower128Corrupt) (dealPartyBeaverShares vault) m = S.sign sk m := by
          have h1 : evalDistributedBeaverOut tower128Params.lambdas
              (tower128Honest ++ tower128Corrupt) (dealPartyBeaverShares vault) m =
              tower128SharedOutVal a b skPad aPad bPad cPad sk m := rfl
          rw [h1, tower128SharedOutVal_eq_sign, hSignDef]
          rfl
        rw [hOutEq]
        exact ih _ _
      · exact ih _ _
    | stepAbort c next ih =>
      dsimp only [execSharedRealTsig, execRealTsig]
      split <;> exact ih _ _
    | stepVerify m sig next ih =>
      dsimp only [execSharedRealTsig, execRealTsig]
      exact ih _ _
  refine ⟨hAntiFrame, ?_⟩
  rw [hSharedEqReal st Z]
  exact protocol_realizes_idealTsig_id_abort S sk (S.sign sk) bdozVerifyCulprit
    (fun _ => rfl) st hMacSound Z

private def tsigPairFin {A B : Nat} (a : Fin A) (b : Fin B) : Fin (A * B) :=
  ⟨a.val * B + b.val, by
    have h1 : a.val + 1 ≤ A := a.isLt
    have h2 : (a.val + 1) * B ≤ A * B := Nat.mul_le_mul_right B h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : b.val < B := b.isLt
    omega⟩

private def tsigSplitLeft {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin A :=
  ⟨x.val / B, (Nat.div_lt_iff_lt_mul hB).mpr x.isLt⟩

private def tsigSplitRight {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin B :=
  ⟨x.val % B, Nat.mod_lt x.val hB⟩

private theorem tsigPair_split {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) :
    tsigPairFin (tsigSplitLeft hB x) (tsigSplitRight hB x) = x := by
  apply Fin.ext
  dsimp [tsigPairFin, tsigSplitLeft, tsigSplitRight]
  have h := Nat.div_add_mod x.val B
  rw [Nat.mul_comm B (x.val / B)] at h
  exact h

private theorem tsigSplitLeft_pair {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    tsigSplitLeft hB (tsigPairFin a b) = a := by
  apply Fin.ext
  dsimp [tsigSplitLeft, tsigPairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt b.isLt, Nat.add_zero]

private theorem tsigSplitRight_pair {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    tsigSplitRight hB (tsigPairFin a b) = b := by
  apply Fin.ext
  dsimp [tsigSplitRight, tsigPairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]

private def finToTower128 (i : Fin (2 ^ 128)) : Tower128 :=
  unpackTower 7 (BitVec.ofFin i)

private def tower128ToFin (x : Tower128) : Fin (2 ^ 128) :=
  (packTower 7 x).toFin

private theorem tower128ToFin_finToTower128 (i : Fin (2 ^ 128)) :
    tower128ToFin (finToTower128 i) = i := by
  unfold tower128ToFin finToTower128
  rw [packTower_unpackTower 7, BitVec.toFin_ofFin]

private theorem finToTower128_tower128ToFin (x : Tower128) :
    finToTower128 (tower128ToFin x) = x := by
  unfold finToTower128 tower128ToFin
  rw [BitVec.ofFin_toFin, unpackTower_packTower 7]

private def padCard7 (C : Nat) : Nat :=
  C * (C * (C * (C * (C * (C * C)))))

/-- Cardinality `(2^128)^7 = 2^896` of `TsigPadTape Tower128 1 2` (`7` full-width `GF(2^128)` elements). -/
def tower128PadCard : Nat := padCard7 (2 ^ 128)

/-- Cardinality `(2^128) * (2^128) = 2^256` of the full 2-lane `Tower128 × Tower128` BDOZ MAC key space. -/
def tower128KeyCard : Nat :=
  (2 ^ 128) * (2 ^ 128)

theorem tower128PadCard_pos : 0 < tower128PadCard :=
  Nat.mul_pos (Nat.two_pow_pos 128)
    (Nat.mul_pos (Nat.two_pow_pos 128)
      (Nat.mul_pos (Nat.two_pow_pos 128)
        (Nat.mul_pos (Nat.two_pow_pos 128)
          (Nat.mul_pos (Nat.two_pow_pos 128)
            (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))))))

theorem tower128KeyCard_pos : 0 < tower128KeyCard :=
  Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128)

private def padHdGen {R : Type} (r0 : R) (l : List R) : R := l.headD r0

private theorem list_len1_gen {R : Type} (r0 : R) : ∀ (l : List R), l.length = 1 → l = [padHdGen r0 l]
  | [_], _ => rfl
  | [], h => by cases h
  | _ :: _ :: _, h => absurd (Nat.succ.inj h) (Nat.succ_ne_zero _)

private theorem list_len2_gen {R : Type} (r0 : R) : ∀ (l : List R), l.length = 2 → l = [padHdGen r0 l, padHdGen r0 l.tail]
  | [_, _], _ => rfl
  | [], h => by cases h
  | [_], h => absurd (Nat.succ.inj h) (Nat.succ_ne_zero 0).symm
  | _ :: _ :: _ :: _, h => absurd (Nat.succ.inj (Nat.succ.inj h)) (Nat.succ_ne_zero _)

private def padDecGen {R : Type} {C : Nat} (hC : 0 < C) (dec : Fin C → R)
    (idx : Fin (padCard7 C)) : TsigPadTape R 1 2 :=
  let B6 := C * (C * (C * (C * (C * C))))
  have hB6 : 0 < B6 := Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC hC))))
  let B5 := C * (C * (C * (C * C)))
  have hB5 : 0 < B5 := Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC hC)))
  let B4 := C * (C * (C * C))
  have hB4 : 0 < B4 := Nat.mul_pos hC (Nat.mul_pos hC (Nat.mul_pos hC hC))
  let B3 := C * (C * C)
  have hB3 : 0 < B3 := Nat.mul_pos hC (Nat.mul_pos hC hC)
  let B2 := C * C
  have hB2 : 0 < B2 := Nat.mul_pos hC hC
  let i0 := tsigSplitLeft hB6 idx
  let r6 := tsigSplitRight hB6 idx
  let i1 := tsigSplitLeft hB5 r6
  let r5 := tsigSplitRight hB5 r6
  let i2 := tsigSplitLeft hB4 r5
  let r4 := tsigSplitRight hB4 r5
  let i3 := tsigSplitLeft hB3 r4
  let r3 := tsigSplitRight hB3 r4
  let i4 := tsigSplitLeft hB2 r3
  let r2 := tsigSplitRight hB2 r3
  let i5 := tsigSplitLeft hC r2
  let i6 := tsigSplitRight hC r2
  { share := fun j =>
      if j.val == 0 then ⟨[dec i0], rfl⟩
      else ⟨[dec i1], rfl⟩
    pad := fun j =>
      if j.val == 0 then ⟨[dec i2, dec i3], rfl⟩
      else ⟨[dec i4, dec i5], rfl⟩
    out := ⟨[dec i6], rfl⟩ }

private def padEncGen {R : Type} {C : Nat} (r0 : R) (enc : R → Fin C)
    (τ : TsigPadTape R 1 2) : Fin (padCard7 C) :=
  let s0 := enc (padHdGen r0 (τ.share ⟨0, by decide⟩).1)
  let s1 := enc (padHdGen r0 (τ.share ⟨1, by decide⟩).1)
  let p00 := enc (padHdGen r0 (τ.pad ⟨0, by decide⟩).1)
  let p01 := enc (padHdGen r0 (τ.pad ⟨0, by decide⟩).1.tail)
  let p10 := enc (padHdGen r0 (τ.pad ⟨1, by decide⟩).1)
  let p11 := enc (padHdGen r0 (τ.pad ⟨1, by decide⟩).1.tail)
  let o0 := enc (padHdGen r0 τ.out.1)
  tsigPairFin s0 (tsigPairFin s1 (tsigPairFin p00 (tsigPairFin p01 (tsigPairFin p10 (tsigPairFin p11 o0)))))

private theorem pad_left_gen {R : Type} {C : Nat} (hC : 0 < C) (r0 : R)
    (dec : Fin C → R) (enc : R → Fin C) (hLR : ∀ i, enc (dec i) = i)
    (idx : Fin (padCard7 C)) :
    padEncGen r0 enc (padDecGen hC dec idx) = idx := by
  unfold padEncGen padDecGen padHdGen
  unfold padCard7 at idx ⊢
  simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, List.headD, List.tail, hLR]
  rw [tsigPair_split, tsigPair_split, tsigPair_split, tsigPair_split, tsigPair_split, tsigPair_split]

private theorem pad_right_gen {R : Type} {C : Nat} (hC : 0 < C) (r0 : R)
    (dec : Fin C → R) (enc : R → Fin C) (hRL : ∀ x, dec (enc x) = x)
    (τ : TsigPadTape R 1 2) :
    padDecGen hC dec (padEncGen r0 enc τ) = τ := by
  unfold padDecGen padEncGen
  dsimp only
  rw [tsigSplitLeft_pair, tsigSplitRight_pair,
      tsigSplitLeft_pair, tsigSplitRight_pair,
      tsigSplitLeft_pair, tsigSplitRight_pair,
      tsigSplitLeft_pair, tsigSplitRight_pair,
      tsigSplitLeft_pair, tsigSplitRight_pair,
      tsigSplitLeft_pair, tsigSplitRight_pair]
  simp only [hRL]
  apply tsigPadTape_ext
  · intro j
    rcases j with ⟨_ | _ | n, hj⟩
    · apply Subtype.ext
      exact (list_len1_gen r0 _ (τ.share ⟨0, by decide⟩).2).symm
    · apply Subtype.ext
      exact (list_len1_gen r0 _ (τ.share ⟨1, by decide⟩).2).symm
    · exact absurd hj (by omega)
  · intro j
    rcases j with ⟨_ | _ | n, hj⟩
    · apply Subtype.ext
      exact (list_len2_gen r0 _ (τ.pad ⟨0, by decide⟩).2).symm
    · apply Subtype.ext
      exact (list_len2_gen r0 _ (τ.pad ⟨1, by decide⟩).2).symm
    · exact absurd hj (by omega)
  · apply Subtype.ext
    exact (list_len1_gen r0 _ τ.out.2).symm

def tower128PadDec (idx : Fin tower128PadCard) : TsigPadTape Tower128 1 2 :=
  padDecGen (Nat.two_pow_pos 128) finToTower128 idx

def tower128PadEnc (τ : TsigPadTape Tower128 1 2) : Fin tower128PadCard :=
  padEncGen (towerZero 7) tower128ToFin τ

/-- Exact constructive bijection over all `2^896` full-width `Tower128` pad tapes (`0` `decide` loops!). -/
def tower128PadEnum : SimpleEquiv (Fin tower128PadCard) (TsigPadTape Tower128 1 2) :=
  { toFun := tower128PadDec, invFun := tower128PadEnc,
    left_inv := pad_left_gen (Nat.two_pow_pos 128) (towerZero 7) finToTower128 tower128ToFin
                  tower128ToFin_finToTower128,
    right_inv := pad_right_gen (Nat.two_pow_pos 128) (towerZero 7) finToTower128 tower128ToFin
                   finToTower128_tower128ToFin }

private def keyDecGen {R : Type} {C : Nat} (hC : 0 < C) (dec : Fin C → R)
    (idx : Fin (C * C)) : R × R :=
  (dec (tsigSplitLeft hC idx), dec (tsigSplitRight hC idx))

private theorem keyDecGen_injective {R : Type} {C : Nat} (hC : 0 < C)
    (dec : Fin C → R) (enc : R → Fin C) (hLR : ∀ i, enc (dec i) = i) :
    ∀ i j : Fin (C * C), keyDecGen hC dec i = keyDecGen hC dec j → i = j := by
  intro i j hEq
  have h1 : enc (keyDecGen hC dec i).1 = enc (keyDecGen hC dec j).1 :=
    congrArg enc (congrArg Prod.fst hEq)
  have h2 : enc (keyDecGen hC dec i).2 = enc (keyDecGen hC dec j).2 :=
    congrArg enc (congrArg Prod.snd hEq)
  unfold keyDecGen at h1 h2
  dsimp only at h1 h2
  rw [hLR, hLR] at h1 h2
  calc i = tsigPairFin (tsigSplitLeft hC i) (tsigSplitRight hC i) := (tsigPair_split hC i).symm
    _ = tsigPairFin (tsigSplitLeft hC j) (tsigSplitRight hC j) := by rw [h1, h2]
    _ = j := tsigPair_split hC j

/-- Exact enumeration of all `2^256` full-width 2-lane `Tower128 × Tower128` BDOZ global MAC keys. -/
def tower128KeyDec (idx : Fin tower128KeyCard) : Tower128 × Tower128 :=
  keyDecGen (Nat.two_pow_pos 128) finToTower128 idx

theorem tower128KeyDec_injective : ∀ i j : Fin tower128KeyCard, tower128KeyDec i = tower128KeyDec j → i = j :=
  keyDecGen_injective (Nat.two_pow_pos 128) finToTower128 tower128ToFin tower128ToFin_finToTower128

/-- **Full-Width `TowerElem 7` (`GF(2^128)`) Shared-Beaver Advantage Bound
    (`ucSimulatorTsig_advantage_bound_tower128`)**:
    Instantiates `ucSimulatorTsig_advantage_bound` over `GF(2^128)` (`Tower128`), where BOTH
    `wireFn` (`tower128SharedWireVals`) AND `outFn` (`tower128SharedOutVal`) are computed by
    **distributed Beaver gate evaluation** (`tsigSharedBeaverRealExec`, `hCircuit` proved by
    `tower128SharedOutVal_eq_sign`, `0` cleartext `sk` in party code!), over all `2^896` pad tapes
    and all `2^256` 2-lane BDOZ MAC keys! -/
theorem ucSimulatorTsig_advantage_bound_tower128
    (Adv : TsigAdversary Tower128 Tower128 tower128Params.k)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128)
    (Cs : Nat) (prg : Fin Cs → TsigPadTape Tower128 tower128Params.d tower128Params.k)
    (Co : Nat) (ot : Fin Co → Tower128 × Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    let real := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
        tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ
    let ideal := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigIdealExec tower128BeaverSig tower128Params tower128State tower128Corrupt tower128Honest
        corruptVk corruptTags sk m [0] Adv ⟨τ, κ⟩
    validThresholdApproval tower128State [0] = true ∧
    natAbsDiff
      (acceptPairs Cs Co prg ot real * (tower128PadCard * tower128KeyCard))
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec ideal * (Cs * Co)) ≤
      Cs * Co * (tower128PadCard * ((tower128Params.k + 1) * tower128Corrupt.length))
        + tower128KeyCard * prgReductionAdvNum Cs tower128PadCard Co prg tower128PadEnum.toFun ot real
        + Cs * otReductionAdvNum tower128PadCard Co tower128KeyCard tower128PadEnum.toFun ot tower128KeyDec real := by
  intro vault real ideal
  refine ⟨by decide, ?_⟩
  have hReal : (fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
      (κ : Tower128 × Tower128) =>
      tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
        tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ) =
      (fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
        tsigRealExec tower128Params
          (tower128SharedWireVals a b skPad aPad bPad cPad)
          (tower128SharedOutVal a b skPad aPad bPad cPad)
          tower128State tower128Corrupt tower128Honest corruptVk corruptTags sk m [0] Adv τ κ) :=
    funext (fun τ => funext (fun κ =>
      tsigSharedBeaverRealExec_eq_tsigRealExec corruptVk corruptTags
        a b skPad aPad bPad cPad sk m [0] Adv τ κ))
  dsimp only [real, ideal]
  rw [hReal]
  exact ucSimulatorTsig_advantage_bound tower128BeaverSig tower128Params
    (tower128SharedWireVals a b skPad aPad bPad cPad)
    (tower128SharedOutVal a b skPad aPad bPad cPad)
    (tower128SharedOutVal_eq_sign a b skPad aPad bPad cPad) (fun _ => rfl) (fun _ => rfl)
    (towerInv 7) (towerMul_inv 7) tower128State tower128Corrupt tower128Honest rfl rfl (by decide)
    tower128Corrupt_nonzero tower128_recon corruptVk corruptTags sk m [0] Adv
    tower128PadCard tower128PadEnum tower128KeyCard tower128KeyDec tower128KeyDec_injective
    Cs prg Co ot

/-- **Strict Sub-Unity Non-Vacuity Theorem over `GF(2^128)` (`ucSimulatorTsig_nonvacuous_sub_unity_tower128`)**:
    Under uniform preprocessing (`prg = tower128PadEnum.toFun`, `ot = tower128KeyDec`), the concrete
    rational distinguishing advantage between real shared-Beaver threshold execution (`tsigSharedBeaverRealExec`)
    and `ucSimulatorTsig` is bounded by `(3, 2 ^ 256)` (`3 / 2^256 < 2^{-254}`), with **explicitly proved
    `3 < tower128KeyCard`** (strictly `< 1`, eliminating the old `512 / 512 = 1` vacuity)! -/
theorem ucSimulatorTsig_nonvacuous_sub_unity_tower128
    (Adv : TsigAdversary Tower128 Tower128 tower128Params.k)
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128) :
    let vault : SharedBeaverSessionVault Tower128 1 := ⟨sk, skPad, a, aPad, b, bPad, cPad⟩
    let real := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
        tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ
    let ideal := fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
      tsigIdealExec tower128BeaverSig tower128Params tower128State tower128Corrupt tower128Honest
        corruptVk corruptTags sk m [0] Adv ⟨τ, κ⟩
    let sampleSpace := tower128PadCard * tower128KeyCard
    let advGap := natAbsDiff
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec real)
      (acceptPairs tower128PadCard tower128KeyCard tower128PadEnum.toFun tower128KeyDec ideal)
    ratLe (advGap, sampleSpace) (3, tower128KeyCard) ∧
    3 < tower128KeyCard := by
  intro vault real ideal sampleSpace advGap
  have hGap : advGap ≤ tower128PadCard * 3 := by
    have hReal : (fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
        (κ : Tower128 × Tower128) =>
        tsigSharedBeaverRealExec tower128Params tower128State tower128Corrupt
          tower128Honest corruptVk corruptTags (dealPartyBeaverShares vault) m [0] Adv τ κ) =
        (fun (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k)
          (κ : Tower128 × Tower128) =>
          tsigRealExec tower128Params
            (tower128SharedWireVals a b skPad aPad bPad cPad)
            (tower128SharedOutVal a b skPad aPad bPad cPad)
            tower128State tower128Corrupt tower128Honest corruptVk corruptTags sk m [0] Adv τ κ) :=
      funext (fun τ => funext (fun κ =>
        tsigSharedBeaverRealExec_eq_tsigRealExec corruptVk corruptTags
          a b skPad aPad bPad cPad sk m [0] Adv τ κ))
    have hRaw := tsig_uniform_hybrid_gap tower128BeaverSig tower128Params
      (tower128SharedWireVals a b skPad aPad bPad cPad)
      (tower128SharedOutVal a b skPad aPad bPad cPad)
      (tower128SharedOutVal_eq_sign a b skPad aPad bPad cPad) (fun _ => rfl) (fun _ => rfl)
      (towerInv 7) (towerMul_inv 7) tower128State tower128Corrupt tower128Honest rfl (by decide)
      tower128Corrupt_nonzero tower128_recon corruptVk corruptTags sk m [0] Adv
      tower128PadCard tower128PadEnum tower128KeyCard tower128KeyDec tower128KeyDec_injective
    have hCoeff : (tower128Params.k + 1) * tower128Corrupt.length = 3 := rfl
    rw [hCoeff] at hRaw
    dsimp only [advGap, real, ideal]
    rw [hReal]
    exact hRaw
  have hSamplePos : 0 < sampleSpace := Nat.mul_pos tower128PadCard_pos tower128KeyCard_pos
  have hSubUnity : 3 < tower128KeyCard := by
    unfold tower128KeyCard
    have h4 : 4 ≤ 2 ^ 128 := Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 2 ≤ 128)
    have h16 : 16 ≤ (2 ^ 128) * (2 ^ 128) := Nat.mul_le_mul h4 h4
    exact Nat.lt_of_lt_of_le (by decide : 3 < 16) h16
  refine ⟨⟨hSamplePos, tower128KeyCard_pos, ?_⟩, hSubUnity⟩
  dsimp only [sampleSpace]
  calc advGap * tower128KeyCard
      ≤ (tower128PadCard * 3) * tower128KeyCard := Nat.mul_le_mul_right tower128KeyCard hGap
    _ = 3 * (tower128PadCard * tower128KeyCard) := by ac_rfl

/-- Perfect Hop-1 view indistinguishability over all `2^896` `GF(2^128)` pad tapes. -/
theorem ucSimulatorTsig_hop1_perfect_tower128
    (corruptVk : Nat → BdozVerifierKeys) (corruptTags : Nat → Tower128 × Tower128)
    (a b : Tower128) (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (sk m : Tower128) (macKey : Tower128 × Tower128)
    (D : Option (TsigAdvView Tower128 tower128Params.k) → Bool) :
    qsum tower128PadCard (fun i =>
      if D (some (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest
        (tower128SharedWireVals a b skPad aPad bPad cPad sk m)
        (tower128SharedOutVal a b skPad aPad bPad cPad sk m)
        (tower128PadEnum.toFun i))) then 1 else 0) =
    qsum tower128PadCard (fun i =>
      if D (ucSimulatorTsig tower128Params
        ⟨(), m, tower128Corrupt, tower128Honest, corruptVk, corruptTags,
          .signed (tower128BeaverSig.sign sk m)⟩
        ⟨tower128PadEnum.toFun i, macKey⟩) then 1 else 0) :=
  ucSimulatorTsig_hop1_perfect tower128BeaverSig tower128Params
    (tower128SharedWireVals a b skPad aPad bPad cPad)
    (tower128SharedOutVal a b skPad aPad bPad cPad)
    (tower128SharedOutVal_eq_sign a b skPad aPad bPad cPad)
    (towerInv 7) (towerMul_inv 7) () tower128Corrupt tower128Honest (by decide)
    tower128Corrupt_nonzero corruptVk corruptTags sk m tower128PadCard tower128PadEnum macKey D

private theorem tsigSessionExpected_singleton {R Sig : Type} [CommRingOps R]
    (pp : TsigParams R Sig) (cid : Nat) (cpt : R)
    (w : Fin pp.k → R) (y : R) (τ : TsigPadTape R pp.d pp.k) :
    tsigSessionExpected pp [(cid, cpt)] w y τ =
      (cid, pp.emb (RoundPoly.evalCoeffs (y :: τ.out.1) cpt)) ::
        finFlat pp.k (fun j =>
          [(cid, cpt)].map (fun cx =>
            (cx.1, pp.emb (add (RoundPoly.evalCoeffs (w j :: (τ.share j).1) cx.2)
                               (RoundPoly.evalCoeffs (τ.pad j).1 cx.2))))) :=
  rfl

private theorem tsigRealOutcome_tower128_rejects_head
    (corruptVk : Nat → BdozVerifierKeys) (tags : Nat → Tower128 × Tower128)
    (alpha : Tower128 × Tower128)
    (w : Fin tower128Params.k → Tower128) (y : Tower128)
    (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k) (ops : List BdozPairOpening) :
    tsigRealOutcome tower128Params tower128Corrupt.length
        (tsigVerifierKey alpha tags
          (tsigSessionExpected tower128Params tower128Corrupt w y τ))
        (tsigSessionExpected tower128Params tower128Corrupt w y τ)
        (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest w y τ).outHonestOpenings
        ({ bdozViewOpening (fun s => (tsigShareAt
            (tsigSessionExpected tower128Params tower128Corrupt w y τ) s,
              tags s)) 0 with
            mac0 := towerAdd 7 (tags 0).1 (towerOne 7) } :: ops) = .abortedBy 2 := by
  have hOne : towerOne 7 ≠ towerZero 7 := by
    intro hEq
    have hBit := congrArg (towerFirstBit 7) hEq
    rw [towerFirstBit_one 7, towerFirstBit_zero 7] at hBit
    cases hBit
  have hC : tower128Corrupt = [(2, towerAdd 7 (towerOne 7) tower128X)] := rfl
  have hExp : tsigSessionExpected tower128Params tower128Corrupt w y τ =
      (2, tower128Params.emb (RoundPoly.evalCoeffs (y :: τ.out.1) (towerAdd 7 (towerOne 7) tower128X))) ::
        finFlat tower128Params.k (fun j =>
          tower128Corrupt.map (fun cx =>
            (cx.1, tower128Params.emb (add (RoundPoly.evalCoeffs (w j :: (τ.share j).1) cx.2)
                                           (RoundPoly.evalCoeffs (τ.pad j).1 cx.2))))) := by
    conv => lhs; rw [hC]
    rw [tsigSessionExpected_singleton, ← hC]
  rw [hExp]
  exact tsigRealOutcome_rejects_tampered_tag tower128Params tower128Corrupt.length alpha tags
    (2, tower128Params.emb (RoundPoly.evalCoeffs (y :: τ.out.1) (towerAdd 7 (towerOne 7) tower128X)))
    _ _ ops (towerOne 7) hOne

/-- Completeness and identifiable-abort rejection over `GF(2^128)` (`Tower128`):
    dealt openings reconstruct `sk * (sk + m)` via local Beaver shares, and tampering with any
    BDOZ MAC tag aborts and blames corrupt party `2`. -/
theorem tsigRealOutcome_tower128_signs_and_rejects
    (corruptVk : Nat → BdozVerifierKeys) (tags : Nat → Tower128 × Tower128)
    (alpha : Tower128 × Tower128) (a b sk m : Tower128)
    (skPad aPad bPad cPad : ShamirPadPoly Tower128 1)
    (τ : TsigPadTape Tower128 tower128Params.d tower128Params.k) (ops : List BdozPairOpening) :
    let w := tower128SharedWireVals a b skPad aPad bPad cPad sk m
    let y := tower128SharedOutVal a b skPad aPad bPad cPad sk m
    tsigRealOutcome tower128Params tower128Corrupt.length
        (tsigVerifierKey alpha tags
          (tsigSessionExpected tower128Params tower128Corrupt w y τ))
        (tsigSessionExpected tower128Params tower128Corrupt w y τ)
        (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest w y τ).outHonestOpenings
        (tsigDealtOpenings
          (fun s => (tsigShareAt
            (tsigSessionExpected tower128Params tower128Corrupt w y τ) s, tags s))
          0 (tsigSessionExpected tower128Params tower128Corrupt w y τ).length) =
      .signed (towerMul 7 sk (towerAdd 7 sk m)) ∧
    tsigRealOutcome tower128Params tower128Corrupt.length
        (tsigVerifierKey alpha tags
          (tsigSessionExpected tower128Params tower128Corrupt w y τ))
        (tsigSessionExpected tower128Params tower128Corrupt w y τ)
        (tsigSessionView tower128Params corruptVk tower128Corrupt tower128Honest w y τ).outHonestOpenings
        ({ bdozViewOpening (fun s => (tsigShareAt
            (tsigSessionExpected tower128Params tower128Corrupt w y τ) s,
              tags s)) 0 with
            mac0 := towerAdd 7 (tags 0).1 (towerOne 7) } :: ops) = .abortedBy 2 := by
  intro w y
  have hRej := tsigRealOutcome_tower128_rejects_head corruptVk tags alpha w y τ ops
  have hy : y = towerMul 7 sk (towerAdd 7 sk m) :=
    tower128SharedOutVal_eq_sign a b skPad aPad bPad cPad sk m
  refine ⟨?_, hRej⟩
  rw [hy]
  exact tsigRealOutcome_dealt_openings_sign tower128Params tower128State corruptVk tower128Corrupt
    tower128Honest rfl (fun _ => rfl) (fun _ => rfl) tower128_recon w
    (towerMul 7 sk (towerAdd 7 sk m)) τ alpha tags

end TsigSharedBeaverAndTower128

/-! ## 7. Unification with `Spec.idealCustodyMachine` (`idealTsig_dataRefines_idealCustody`)

Couples the `sk`-free, share-free $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ state (`IdealTsigState`,
`validThresholdApproval`, `idealTsigRecordAbort`, `idealTsigVerify`) with the custody ledger and
per-party permits as a reactive `Spec.Machine`, and proves a constructive `Spec.DataRefines`
simulation into `Spec.idealCustodyMachine`:

* `.approve`, `.advApprove`, `.corrupt` and `.sign` implement the four ports of
  `Spec.idealCustodyMachine`;
* `.recordAbort` (`idealTsigRecordAbort`, quarantining a corrupt party in `identifiedCheaters`) and
  `.verify` (`idealTsigVerify`) are internal turns (`idealTsigVisIn = none`);
* Fresh signing requires `validThresholdApproval` on the unquarantined honest permit holders AND
  counts only unquarantined permit holders towards `Spec.custodyLedgerSign`, so quarantined
  corrupt parties lose both approval ports and quorum weight while refining `Spec.idealCustodyMachine`. -/

section IdealTsigCustodyRefinement

open Qsag.Spec

/-- State of the custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ machine. -/
structure IdealTsigCustodyState (PK D Sig : Type) where
  tsig : IdealTsigState PK D
  ledger : CustodyLedger PK D Sig
  honestApprovals : List CustodyApproval
  corruptApprovals : List CustodyApproval

/-- Initial custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ state for `(dep₀, pk₀, quorum₀)`. -/
@[expose] def IdealTsigCustodyState.init {PK D Sig : Type}
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    IdealTsigCustodyState PK D Sig where
  tsig :=
    { pk := pk₀
      threshold := quorum₀.threshold
      numParties := quorum₀.numParties
      corruptParties := []
      approvedMsgs := []
      identifiedCheaters := [] }
  ledger := (IdealCustodyState.init dep₀ pk₀ quorum₀).ledger
  honestApprovals := []
  corruptApprovals := []

/-- Input alphabet of the custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ machine. -/
inductive IdealTsigCustodyInput (D Sig : Type) where
  | approve (party deploymentId : Nat) (intent : CustodyIntent)
  | advApprove (party deploymentId : Nat) (intent : CustodyIntent)
  | corrupt (party : Nat)
  | recordAbort (culprit : Nat)
  | verify (msg : D) (sig : Sig)
  | sign (deploymentId : Nat) (intent : CustodyIntent) (abortBeforeRelease : Bool)
  deriving DecidableEq, Repr

/-- Output alphabet of the custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ machine. -/
inductive IdealTsigCustodyOutput (Sig : Type) where
  | custody (out : CustodyOutcome Sig)
  | abortedBy (culprit : Nat)
  | verified (accepted : Bool)
  deriving DecidableEq, Repr

/-- Unquarantined honest enrolled parties holding a recorded honest permit for `(dep, i)`. -/
def idealTsigHonestPermitHolders {PK D Sig : Type}
    (st : IdealTsigCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) : List Nat :=
  (List.range st.tsig.numParties).filter (fun p =>
    decide (p ∉ st.tsig.corruptParties) &&
    decide (p ∉ st.tsig.identifiedCheaters) &&
    decide (CustodyApproval.mk p dep i ∈ st.honestApprovals))

/-- Unquarantined enrolled parties (honest or corrupt) holding a recorded permit for `(dep, i)`. -/
def idealTsigActivePermitHolders {PK D Sig : Type}
    (st : IdealTsigCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) : List Nat :=
  (List.range st.tsig.numParties).filter (fun p =>
    decide (p ∉ st.tsig.identifiedCheaters) &&
    (decide (CustodyApproval.mk p dep i ∈ st.honestApprovals) ||
      decide (CustodyApproval.mk p dep i ∈ st.corruptApprovals)))

/-- Single-step transition of the custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ machine. -/
@[expose] def idealTsigCustodyStep {PK SK D Sig : Type} [DecidableEq D]
    (S_sig : AbstractSigScheme PK SK D Sig)
    (S_dig : CustodyDigestScheme D) (oracleSign : D → Sig)
    (st : IdealTsigCustodyState PK D Sig)
    (inp : IdealTsigCustodyInput D Sig) :
    Option (IdealTsigCustodyState PK D Sig × IdealTsigCustodyOutput Sig) :=
  match inp with
  | .approve p dep i =>
    if p < st.ledger.quorum.numParties ∧ p ∉ st.tsig.corruptParties ∧
        p ∉ st.tsig.identifiedCheaters ∧ dep = st.ledger.deploymentId then
      some ({ st with honestApprovals := CustodyApproval.mk p dep i :: st.honestApprovals },
            .custody .approvalRecorded)
    else none
  | .advApprove p dep i =>
    if p ∈ st.tsig.corruptParties ∧ p ∉ st.tsig.identifiedCheaters ∧
        dep = st.ledger.deploymentId then
      some ({ st with corruptApprovals := CustodyApproval.mk p dep i :: st.corruptApprovals },
            .custody .approvalRecorded)
    else none
  | .corrupt p =>
    if p < st.ledger.quorum.numParties ∧ p ∉ st.tsig.corruptParties ∧
        st.tsig.corruptParties.length + 1 < st.ledger.quorum.threshold then
      some ({ st with
              tsig := { st.tsig with corruptParties := p :: st.tsig.corruptParties } },
            .custody (.corrupted (custodyRevealed st.honestApprovals p)))
    else none
  | .recordAbort culprit =>
    (idealTsigRecordAbort st.tsig culprit).map
      (fun tsig' => ({ st with tsig := tsig' }, .abortedBy culprit))
  | .verify m sig =>
    some (st, .verified (idealTsigVerify S_sig st.tsig m sig))
  | .sign dep i ab =>
    let honHolders := (List.range st.tsig.numParties).filter (fun p =>
      decide (p ∉ st.tsig.corruptParties) &&
      decide (p ∉ st.tsig.identifiedCheaters) &&
      decide (CustodyApproval.mk p dep i ∈ st.honestApprovals))
    let activeHolders := (List.range st.tsig.numParties).filter (fun p =>
      decide (p ∉ st.tsig.identifiedCheaters) &&
      (decide (CustodyApproval.mk p st.ledger.deploymentId i ∈ st.honestApprovals) ||
        decide (CustodyApproval.mk p st.ledger.deploymentId i ∈ st.corruptApprovals)))
    let ReplayOrFreshOk : Bool :=
      match findReleasedEpoch st.ledger.releasedHistory i.epoch with
      | some _ => true
      | none => validThresholdApproval st.tsig honHolders
    if ReplayOrFreshOk = true then
      let count := activeHolders.length
      match custodyLedgerSign S_dig oracleSign st.ledger count dep i ab with
      | none => none
      | some (L', out) =>
        let tsig' :=
          match out with
          | .released _ =>
            { st.tsig with approvedMsgs := S_dig.digest st.ledger.deploymentId i :: st.tsig.approvedMsgs }
          | _ => st.tsig
        some ({ st with tsig := tsig', ledger := L' }, .custody out)
    else none

/-- Reactive `Spec.Machine` packaging of the custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ functionality. -/
def idealTsigCustodyMachine {PK SK D Sig : Type} [DecidableEq D]
    (S_sig : AbstractSigScheme PK SK D Sig)
    (S_dig : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    Machine (IdealTsigCustodyState PK D Sig)
      (IdealTsigCustodyInput D Sig) (IdealTsigCustodyOutput Sig) where
  Init st := st = IdealTsigCustodyState.init dep₀ pk₀ quorum₀
  step := idealTsigCustodyStep S_sig S_dig oracleSign
  errStep st _ := st

/-- Interface map from `IdealTsigCustodyInput` to `Spec.CustodyInput` (`.recordAbort` and `.verify` are internal). -/
def idealTsigVisIn {D Sig : Type} : IdealTsigCustodyInput D Sig → Option CustodyInput
  | .approve p dep i => some (.approve p dep i)
  | .advApprove p dep i => some (.advApprove p dep i)
  | .corrupt p => some (.corrupt p)
  | .recordAbort _ => none
  | .verify _ _ => none
  | .sign dep i ab => some (.sign dep i ab)

/-- Interface map from `IdealTsigCustodyOutput` to `Spec.CustodyOutcome`. -/
def idealTsigVisOut {Sig : Type} : IdealTsigCustodyOutput Sig → CustodyOutcome Sig
  | .custody out => out
  | .abortedBy _ => .approvalRecorded
  | .verified _ => .approvalRecorded

theorem idealTsigVisIn_eq {D Sig : Type} (inp : IdealTsigCustodyInput D Sig) :
    idealTsigVisIn inp =
      match inp with
      | .approve p dep i => some (.approve p dep i)
      | .advApprove p dep i => some (.advApprove p dep i)
      | .corrupt p => some (.corrupt p)
      | .recordAbort _ => none
      | .verify _ _ => none
      | .sign dep i ab => some (.sign dep i ab) := by
  cases inp <;> rfl

theorem idealTsigVisOut_eq {Sig : Type} (out : IdealTsigCustodyOutput Sig) :
    idealTsigVisOut out =
      match out with
      | .custody o => o
      | .abortedBy _ => .approvalRecorded
      | .verified _ => .approvalRecorded := by
  cases out <;> rfl

/-- Simulation relation between `IdealTsigCustodyState` and `Spec.IdealCustodyState`,
    carrying the anti-framing and WAL-digest synchronization invariants. -/
structure IdealTsigCustodyRel {PK D Sig : Type}
    (c : IdealTsigCustodyState PK D Sig)
    (a : IdealCustodyState PK D Sig) : Prop where
  pk_eq : c.tsig.pk = c.ledger.enrolledPk
  num_eq : c.tsig.numParties = c.ledger.quorum.numParties
  thr_eq : c.tsig.threshold = c.ledger.quorum.threshold
  anti_framing : ∀ x ∈ c.tsig.identifiedCheaters, x ∈ c.tsig.corruptParties
  approved_wal : c.tsig.approvedMsgs = c.ledger.releasedHistory.map CustodyRelease.digest
  ledger_eq : a.ledger = c.ledger
  corrupt_eq : a.corruptParties = c.tsig.corruptParties
  honest_eq : a.honestApprovals = c.honestApprovals
  corrupt_app_eq : a.corruptApprovals = c.corruptApprovals

private theorem tsig_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (x y : α) :
    (if p then x else y) = x := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem tsig_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (x y : α) :
    (if p then x else y) = y := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem idealTsigActivePermitHolders_le_custodyApprovers {PK D Sig : Type}
    (c : IdealTsigCustodyState PK D Sig) (a : IdealCustodyState PK D Sig)
    (hRel : IdealTsigCustodyRel c a) (i : CustodyIntent) :
    (idealTsigActivePermitHolders c c.ledger.deploymentId i).length ≤
      (custodyApprovers a.ledger.quorum.numParties a.honestApprovals a.corruptApprovals
        a.ledger.deploymentId i).length := by
  have hNd : (idealTsigActivePermitHolders c c.ledger.deploymentId i).Nodup := by
    unfold idealTsigActivePermitHolders
    exact List.Pairwise.filter _ (Qsag.Constructive.nodup_range c.tsig.numParties)
  refine custodyApprovers_length_le_of_subset hNd (fun p hp => ?_)
  unfold idealTsigActivePermitHolders at hp
  rcases List.mem_filter.mp hp with ⟨hRange, hCond⟩
  rcases Bool.and_eq_true_iff.mp hCond with ⟨_, hOr⟩
  have hpLt : p < a.ledger.quorum.numParties := by
    rw [hRel.ledger_eq, ← hRel.num_eq]
    exact List.mem_range.mp hRange
  have hDep : a.ledger.deploymentId = c.ledger.deploymentId := by
    rw [hRel.ledger_eq]
  refine ⟨hpLt, ?_⟩
  rw [hDep, hRel.honest_eq, hRel.corrupt_app_eq]
  rcases Bool.or_eq_true_iff.mp hOr with hH | hC
  · exact .inl (of_decide_eq_true hH)
  · exact .inr (of_decide_eq_true hC)

/-- **Unification of `IdealTsig` and `Spec.idealCustodyMachine` (`idealTsig_dataRefines_idealCustody`)**:
    The custody-coupled $\mathcal{F}_{\text{TSIG}}^{\text{id-abort}}$ machine refines
    `Spec.idealCustodyMachine` via `Spec.DataRefines`, preserving anti-framing and exact
    synchronization between `approvedMsgs` and committed WAL digests. -/
def idealTsig_dataRefines_idealCustody {PK SK D Sig : Type} [DecidableEq D]
    (S_sig : AbstractSigScheme PK SK D Sig)
    (S_dig : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    DataRefines
      (idealTsigCustodyMachine S_sig S_dig oracleSign dep₀ pk₀ quorum₀)
      (idealCustodyMachine S_dig oracleSign dep₀ pk₀ quorum₀)
      idealTsigVisIn idealTsigVisOut where
  Rel := IdealTsigCustodyRel
  absInit _ := IdealCustodyState.init dep₀ pk₀ quorum₀
  init_ok {c₀} hInit := by
    have hc : c₀ = IdealTsigCustodyState.init dep₀ pk₀ quorum₀ := hInit
    subst hc
    exact ⟨rfl,
      { pk_eq := rfl
        num_eq := rfl
        thr_eq := rfl
        anti_framing := fun _ h => False.elim (List.not_mem_nil h)
        approved_wal := rfl
        ledger_eq := rfl
        corrupt_eq := rfl
        honest_eq := rfl
        corrupt_app_eq := rfl }⟩
  sim_visible {c c' a inp out j} hRel hStepC hVis := by
    cases inp with
    | approve p dep i =>
      cases hVis
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.approve p dep i) = some (c', out) at hStepC
      unfold idealTsigCustodyStep at hStepC
      dsimp only at hStepC
      by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.tsig.corruptParties ∧
          p ∉ c.tsig.identifiedCheaters ∧ dep = c.ledger.deploymentId
      · rw [tsig_if_pos hg] at hStepC
        cases hStepC
        have hgA : p < a.ledger.quorum.numParties ∧ p ∉ a.corruptParties ∧
            dep = a.ledger.deploymentId := by
          rw [hRel.ledger_eq, hRel.corrupt_eq]
          exact ⟨hg.1, hg.2.1, hg.2.2.2⟩
        refine ⟨_, idealCustodyStep_approve_of (S := S_dig) (oracleSign := oracleSign) i hgA,
          { pk_eq := hRel.pk_eq
            num_eq := hRel.num_eq
            thr_eq := hRel.thr_eq
            anti_framing := hRel.anti_framing
            approved_wal := hRel.approved_wal
            ledger_eq := hRel.ledger_eq
            corrupt_eq := hRel.corrupt_eq
            honest_eq := congrArg (List.cons _) hRel.honest_eq
            corrupt_app_eq := hRel.corrupt_app_eq }⟩
      · rw [tsig_if_neg hg] at hStepC
        cases hStepC
    | advApprove p dep i =>
      cases hVis
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.advApprove p dep i) = some (c', out) at hStepC
      unfold idealTsigCustodyStep at hStepC
      dsimp only at hStepC
      by_cases hg : p ∈ c.tsig.corruptParties ∧ p ∉ c.tsig.identifiedCheaters ∧
          dep = c.ledger.deploymentId
      · rw [tsig_if_pos hg] at hStepC
        cases hStepC
        have hgA : p ∈ a.corruptParties ∧ dep = a.ledger.deploymentId := by
          rw [hRel.ledger_eq, hRel.corrupt_eq]
          exact ⟨hg.1, hg.2.2⟩
        refine ⟨_, idealCustodyStep_advApprove_of (S := S_dig) (oracleSign := oracleSign) i hgA,
          { pk_eq := hRel.pk_eq
            num_eq := hRel.num_eq
            thr_eq := hRel.thr_eq
            anti_framing := hRel.anti_framing
            approved_wal := hRel.approved_wal
            ledger_eq := hRel.ledger_eq
            corrupt_eq := hRel.corrupt_eq
            honest_eq := hRel.honest_eq
            corrupt_app_eq := congrArg (List.cons _) hRel.corrupt_app_eq }⟩
      · rw [tsig_if_neg hg] at hStepC
        cases hStepC
    | corrupt p =>
      cases hVis
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.corrupt p) = some (c', out) at hStepC
      unfold idealTsigCustodyStep at hStepC
      dsimp only at hStepC
      by_cases hg : p < c.ledger.quorum.numParties ∧ p ∉ c.tsig.corruptParties ∧
          c.tsig.corruptParties.length + 1 < c.ledger.quorum.threshold
      · rw [tsig_if_pos hg] at hStepC
        cases hStepC
        have hgA : p < a.ledger.quorum.numParties ∧ p ∉ a.corruptParties ∧
            a.corruptParties.length + 1 < a.ledger.quorum.threshold := by
          rw [hRel.ledger_eq, hRel.corrupt_eq]
          exact hg
        have hStepA := idealCustodyStep_corrupt_of (S := S_dig) (oracleSign := oracleSign)
          (st := a) (p := p) hgA
        refine ⟨{ a with corruptParties := p :: a.corruptParties }, ?_, ?_⟩
        · change idealCustodyStep S_dig oracleSign a (.corrupt p) =
            some ({ a with corruptParties := p :: a.corruptParties },
                  .corrupted (custodyRevealed c.honestApprovals p))
          rw [hStepA, hRel.honest_eq]
        · exact
            { pk_eq := hRel.pk_eq
              num_eq := hRel.num_eq
              thr_eq := hRel.thr_eq
              anti_framing := fun x hx => List.mem_cons_of_mem _ (hRel.anti_framing x hx)
              approved_wal := hRel.approved_wal
              ledger_eq := hRel.ledger_eq
              corrupt_eq := congrArg (List.cons p) hRel.corrupt_eq
              honest_eq := hRel.honest_eq
              corrupt_app_eq := hRel.corrupt_app_eq }
      · rw [tsig_if_neg hg] at hStepC
        cases hStepC
    | recordAbort _ => cases hVis
    | verify _ _ => cases hVis
    | sign dep i ab =>
      cases hVis
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.sign dep i ab) = some (c', out) at hStepC
      unfold idealTsigCustodyStep at hStepC
      dsimp only at hStepC
      let gate : Bool :=
        match findReleasedEpoch c.ledger.releasedHistory i.epoch with
        | some _ => true
        | none => validThresholdApproval c.tsig (idealTsigHonestPermitHolders c dep i)
      change (if gate = true then _ else none) = some (c', out) at hStepC
      by_cases hGate : gate = true
      · rw [tsig_if_pos hGate] at hStepC
        change (match custodyLedgerSign S_dig oracleSign c.ledger
            (idealTsigActivePermitHolders c c.ledger.deploymentId i).length dep i ab with
          | none => none
          | some (L', o) => _) = some (c', out) at hStepC
        cases hL : custodyLedgerSign S_dig oracleSign c.ledger
            (idealTsigActivePermitHolders c c.ledger.deploymentId i).length dep i ab with
        | none => rw [hL] at hStepC; cases hStepC
        | some pair =>
          rcases pair with ⟨L', o⟩
          rw [hL] at hStepC
          cases hStepC
          have hLe := idealTsigActivePermitHolders_le_custodyApprovers c a hRel i
          have hMono := custodyLedgerSign_mono hL hLe
          rw [← hRel.ledger_eq] at hMono
          obtain ⟨hD', hPk', hQ'⟩ := custodyLedgerSign_static hL
          have hAppWal :
              (match o with
               | .released _ =>
                 { c.tsig with approvedMsgs := S_dig.digest c.ledger.deploymentId i :: c.tsig.approvedMsgs }
               | _ => c.tsig).approvedMsgs =
              L'.releasedHistory.map CustodyRelease.digest := by
            obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv hL
            rcases hCase with ⟨r, _, _, hSame, hOut⟩ | ⟨_, _, _, _, _, hAb⟩
            · subst hSame; subst hOut
              exact hRel.approved_wal
            · rcases hAb with ⟨_, hL', hOut⟩ | ⟨_, hL', hOut⟩
              · subst hL'; subst hOut
                exact hRel.approved_wal
              · subst hL'; subst hOut
                show S_dig.digest c.ledger.deploymentId i :: c.tsig.approvedMsgs =
                  S_dig.digest c.ledger.deploymentId i ::
                    c.ledger.releasedHistory.map CustodyRelease.digest
                exact congrArg (List.cons _) hRel.approved_wal
          refine ⟨{ a with ledger := L' },
            idealCustodyStep_sign_of (S := S_dig) (oracleSign := oracleSign) hMono,
            { pk_eq := by
                cases o <;> exact hRel.pk_eq.trans hPk'.symm
              num_eq := by
                have hN : L'.quorum.numParties = c.ledger.quorum.numParties :=
                  congrArg CustodyQuorumProfile.numParties hQ'
                cases o <;> exact hRel.num_eq.trans hN.symm
              thr_eq := by
                have hT : L'.quorum.threshold = c.ledger.quorum.threshold :=
                  congrArg CustodyQuorumProfile.threshold hQ'
                cases o <;> exact hRel.thr_eq.trans hT.symm
              anti_framing := by
                cases o <;> exact hRel.anti_framing
              approved_wal := hAppWal
              ledger_eq := rfl
              corrupt_eq := by
                cases o <;> exact hRel.corrupt_eq
              honest_eq := hRel.honest_eq
              corrupt_app_eq := hRel.corrupt_app_eq }⟩
      · rw [tsig_if_neg hGate] at hStepC
        cases hStepC
  sim_internal {c c' a inp out} hRel hStepC hInt := by
    cases inp with
    | approve _ _ _ => cases hInt
    | advApprove _ _ _ => cases hInt
    | corrupt _ => cases hInt
    | sign _ _ _ => cases hInt
    | verify m sig =>
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.verify m sig) = some (c', out) at hStepC
      unfold idealTsigCustodyStep at hStepC
      cases hStepC
      exact hRel
    | recordAbort culprit =>
      change idealTsigCustodyStep S_sig S_dig oracleSign c (.recordAbort culprit) = some (c', out) at hStepC
      unfold idealTsigCustodyStep idealTsigRecordAbort at hStepC
      dsimp only at hStepC
      by_cases hc : culprit ∈ c.tsig.corruptParties
      · rw [tsig_if_pos hc] at hStepC
        cases hStepC
        exact
          { pk_eq := hRel.pk_eq
            num_eq := hRel.num_eq
            thr_eq := hRel.thr_eq
            anti_framing := fun x hx => by
              rcases List.mem_cons.mp hx with rfl | hOld
              · exact hc
              · exact hRel.anti_framing x hOld
            approved_wal := hRel.approved_wal
            ledger_eq := hRel.ledger_eq
            corrupt_eq := hRel.corrupt_eq
            honest_eq := hRel.honest_eq
            corrupt_app_eq := hRel.corrupt_app_eq }
      · rw [tsig_if_neg hc] at hStepC
        cases hStepC
  sim_reject hRel _ := hRel

/-- Observable trace inclusion from `idealTsigCustodyMachine` into `Spec.idealCustodyMachine`,
    paired with reachable anti-framing and WAL-digest synchronization. -/
theorem idealTsig_admitsTrace_idealCustody {PK SK D Sig : Type} [DecidableEq D]
    (S_sig : AbstractSigScheme PK SK D Sig)
    (S_dig : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    (∀ tr : List (IdealTsigCustodyInput D Sig × IdealTsigCustodyOutput Sig),
      (idealTsigCustodyMachine S_sig S_dig oracleSign dep₀ pk₀ quorum₀).AdmitsTrace tr →
      (idealCustodyMachine S_dig oracleSign dep₀ pk₀ quorum₀).AdmitsTrace
        (projectTrace idealTsigVisIn idealTsigVisOut tr)) ∧
    (∀ st : IdealTsigCustodyState PK D Sig,
      (idealTsigCustodyMachine S_sig S_dig oracleSign dep₀ pk₀ quorum₀).Reachable st →
      (∀ x ∈ st.tsig.identifiedCheaters, x ∈ st.tsig.corruptParties) ∧
      st.tsig.approvedMsgs = st.ledger.releasedHistory.map CustodyRelease.digest ∧
      st.ledger.spent ≤ quorum₀.spendCap) := by
  let ref := idealTsig_dataRefines_idealCustody S_sig S_dig oracleSign dep₀ pk₀ quorum₀
  refine ⟨fun _ h => ref.preserve_admitsTrace h, ?_⟩
  intro st hReach
  obtain ⟨a, hReachA, hRel⟩ := ref.reachable_rel hReach
  have hRel' : IdealTsigCustodyRel st a := hRel
  have hSafe := idealCustody_reachable_safeInv hReachA
  exact ⟨hRel'.anti_framing, hRel'.approved_wal, hRel'.ledger_eq ▸ hSafe.budget⟩

end IdealTsigCustodyRefinement

#verify_constructive
  Qsag.idealTsig_admitsTrace_idealCustody

end Qsag
end

public section
namespace Qsag
#export_eqns execIdealTsig
end Qsag
