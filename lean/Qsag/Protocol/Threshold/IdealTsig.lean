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

public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.UcGames
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
