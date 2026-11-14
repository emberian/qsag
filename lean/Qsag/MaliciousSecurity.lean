module
/-
# Qsag.MaliciousSecurity — Dishonest-Majority MACs, Anti-DFA Cut Gate, Resharing & Simplex Safety

Self-contained Lean 4.35 active-security formalization closing `[P0-05..10]`
(`0` Mathlib, `0` sorry, `0` custom axioms, `0 Classical.choice`):

1. **MAC-Authenticated & Share-Level Frobenius Booleanity (`towerFrobenius_eq_zero_iff_bit`,
   `#tooth` `frobenius_unauthenticated_offset_break`, `dkg_frobenius_booleanity_soundness`,
   `verifySharedDkgFrobenius_complete`, `verifySharedDkgFrobenius_sound`,
   `#tooth` `tooth_shared_dkg_frobenius_rejects_nonbinary_shares`)**:
   Proves $x^2 \oplus x = 0 \iff x \in \{0, 1\}$ at every binary tower level $\mathcal{T}_k$
   (`Tower8`, `Tower128`), demonstrates via `#tooth` why unauthenticated openings fail against
   additive offsets, and proves over distributed `(t, n)` Shamir Beaver squaring + zero-sum tower
   MAC verification that accepted openings constructively enforce booleanity, catch a corrupted
   Beaver triple, or recover the secret MAC key $\alpha$.
2. **Pre-Opening Pairwise-PRF Zero-Mask & `SPDZ`/`BDOZ` Batch MAC Soundness (`[P0-08]`,
   `pairwiseZeroMasks_sum_eq_zero`, `spdz_batch_mac_soundness`, `bdoz_2lane_mac_soundness`,
   `extractBdozCheaterOrValid`, `honest_party_never_slashed`)**:
   Verifies linear MAC combinations over pre-existing shares masked by pairwise-PRF zero-sum masks
   (zero cleartext wire broadcast prior to MAC verification), proves from coefficient non-vanishing
   (`poly_coeffs_zero_of_vanish_nodup`) that any non-zero wire deviation batch has $\le L$ challenge
   roots over `GoldilocksExt2` and 2-lane `Tower128`, and constructively (`PSum`, `0 Classical.choice`)
   pinpoints a `SlashingReceipt` on deviating parties while guaranteeing honest parties are never slashed.
3. **Active 3-Party `FLNW17` Replicated View Cross-Check (`rss_flnw_active_open_sound`,
   `#tooth` `rss_passive_open_vulnerable_to_additive_fault`)**:
   Exploits 2-of-3 share replication so every share $s_k$ is cross-checked between the two parties
   holding it; against $\le 1$ Byzantine party, accepted openings equal `reconstructRssWord` with
   zero error probability.
4. **Multi-Turn MAC-Before-Open Anti-DFA Trace Invariant & Canonical Share-Byte Binding
   (`mac_before_open_blocks_faulted_cut_leakage`, `encodeCutShareBytes_injective`,
   `mac_before_open_canonical_bytes_sound`, `canonical_mac_before_open_blocks_faulted_cut_leakage`,
   `#tooth` `open_before_mac_leaks_faulted_cut`, `#tooth` `tooth_canonical_cut_rejects_mismatched_bytes`)**:
   Proves across arbitrary-length signing traces that gating cut-boundary openings strictly behind
   batch MAC verification and injective 16-byte `Tower128` encoding prevents any faulted WOTS+ /
   `TSW` / `PRF_msg` value from ever reaching the adversary.
5. **Cleartext-Free Dynamic `(t, n) → (t', n')` Quorum Resharing `Π_reshare` & `(t' - 1)` View Bijection
   (`reshare_preserves_public_key_and_refreshes_degree`,
   `reshare_from_shares_without_cleartext_recombines_secret`, `reshare_corrupt_view_bijection`)**:
   Proves share-to-share sub-polynomial resharing preserves the shared secret and `derivePublicKey`
   without reconstructing `sk`, zeroes old shares, and induces an exact `SimpleEquiv` bijection on
   any `< t'` corrupt new-committee view.
6. **Constructive Simplex Quorum Intersection, Shared Threshold Keys & Crash-Resilient `Jorts` WAL Safety
   (`extractHonestQuorumIntersection`, `jorts_quorum_never_double_signs`,
   `walJortsNode_no_equivocation_across_crashes`, `threshold_jorts_wal_quorum_never_double_signs`)**:
   Constructively (`0 Classical.choice`) extracts an honest validator in $Q_1 \cap Q_2$ whenever
   $n = 3f + 1$, $|Q_1|, |Q_2| \ge 2f + 1$, and $|B| \le f$, proving two threshold quorums over a
   single shared key with durable crash-resilient WAL latches can never certify distinct messages
   in the same `Jorts` slot even across arbitrary power-loss crash/reboot events.
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.UcGames
public import Qsag.Preprocessing
public import Qsag.HashSigs
public import Qsag.HypertreeEufCma
public import Qsag.ThresholdMpc

import all Qsag.Goldilocks
import all Qsag.UcGames
import all Qsag.Preprocessing
import all Qsag.ThresholdMpc

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. MAC-Authenticated Frobenius Booleanity (`dkg_frobenius_booleanity_soundness`) -/

/-- Frobenius booleanity polynomial $F(x) = x^2 \oplus x$ over binary tower $\mathcal{T}_k$. -/
@[expose] def towerFrobeniusPoly (k : Nat) (x : TowerElem k) : TowerElem k :=
  towerAdd k (towerMul k x x) x

/-- **Exact Frobenius Field Characterization (`towerFrobenius_eq_zero_iff_bit`)**:
    At every tower level $k \ge 0$ (including $\mathcal{T}_3 = \mathbb{F}_{2^8}$ and
    $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$), $x^2 \oplus x = 0 \iff x \in \{0, 1\}$. -/
theorem towerFrobenius_eq_zero_iff_bit (k : Nat) (x : TowerElem k) :
    towerFrobeniusPoly k x = towerZero k ↔ (x = towerZero k ∨ x = towerOne k) := by
  unfold towerFrobeniusPoly
  constructor
  · intro hZero
    have hFactor : towerAdd k (towerMul k x x) x =
        towerMul k x (towerAdd k x (towerOne k)) := by
      rw [towerMul_add_distrib, towerMul_one]
    rw [hFactor] at hZero
    rcases (towerMul_eq_zero_iff k x (towerAdd k x (towerOne k))).mp hZero with hx0 | hx1
    · exact Or.inl hx0
    · right
      have hAdd := congrArg (fun z => towerAdd k z (towerOne k)) hx1
      simpa only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using hAdd
  · rintro (rfl | rfl)
    · simp [towerMul_zero]
    · rw [towerOne_mul, towerAdd_self_zero]

/-- **`#tooth` Unauthenticated Frobenius Vulnerability (`frobenius_unauthenticated_offset_break`)**:
    Without MAC verification on the opened value $y = x^2 \oplus x$, a malicious dealer holding
    non-boolean $x = (0, 1) \in \mathcal{T}_3 \setminus \{0, 1\}$ (`towerFrobeniusPoly 3 x ≠ 0`)
    injects additive offset $\Delta = x^2 \oplus x$ so the shifted opening $y \oplus \Delta = 0$ passes! -/
theorem frobenius_unauthenticated_offset_break :
    let x : TowerElem 3 := (towerZero 2, towerOne 2)
    x ≠ towerZero 3 ∧ x ≠ towerOne 3 ∧
    towerFrobeniusPoly 3 x ≠ towerZero 3 ∧
    towerAdd 3 (towerFrobeniusPoly 3 x) (towerFrobeniusPoly 3 x) = towerZero 3 := by
  have hx0 : ((towerZero 2, towerOne 2) : TowerElem 3) ≠ towerZero 3 :=
    fun h => by cases congrArg (fun p : TowerElem 3 => p.2.1.1) h
  have hx1 : ((towerZero 2, towerOne 2) : TowerElem 3) ≠ towerOne 3 :=
    fun h => by cases congrArg (fun p : TowerElem 3 => p.1.1.1) h
  have hFrobNe : towerFrobeniusPoly 3 ((towerZero 2, towerOne 2) : TowerElem 3) ≠ towerZero 3 :=
    fun h => by
      rcases (towerFrobenius_eq_zero_iff_bit 3 _).mp h with h0 | h1
      · exact hx0 h0
      · exact hx1 h1
  exact ⟨hx0, hx1, hFrobNe, towerAdd_self_zero 3 _⟩

/-- Constructive witness that an adversary has algebraically recovered the global MAC key $\alpha$
    via $\Delta\gamma = \alpha \cdot \Delta x$ with $\Delta x \neq 0$. -/
structure MacKeyRecoveryWitness (k : Nat) (alpha deltaX deltaGamma : TowerElem k) : Prop where
  deltaX_ne : deltaX ≠ towerZero k
  mac_relation : deltaGamma = towerMul k alpha deltaX
  recovered_eq : towerMul k deltaGamma (towerInv k deltaX) = alpha

/-- Information-theoretic linear MAC check $\Delta\gamma = \alpha \cdot (x_{\text{opened}} - x_{\text{true}})$. -/
@[expose] def verifyLinearMacEquation {R : Type} [CommRingOps R] [DecidableEq R]
    (alpha xTrue xOpened deltaGamma : R) : Bool :=
  decide (deltaGamma = CommRingOps.mul alpha (CommRingOps.sub xOpened xTrue))

/-- **MAC-Authenticated Frobenius Booleanity (`dkg_frobenius_booleanity_soundness`)**:
    Suppose secret share `[x]` and Beaver-squared share `[xSq]` (`xSq = x * x` over $\mathcal{T}_k$)
    are embedded into $\mathcal{T}_{k+d}$ (e.g. $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$)
    and authenticated under global MAC key $\alpha$.
    If the MAC-authenticated linear opening of $y = x_{\text{sq}} \oplus x$ equals $0$,
    we constructively (`0 Classical.choice`) obtain EITHER $x \in \{0, 1\}$ OR an exact
    `MacKeyRecoveryWitness` recovering $\alpha = \Delta\gamma \cdot (\Delta y)^{-1}$! -/
def dkg_frobenius_booleanity_soundness
    (k d : Nat) (alpha : TowerElem (k + d))
    (x : TowerElem k) (yOpened : TowerElem k) (deltaGamma : TowerElem (k + d))
    (hMac : verifyLinearMacEquation alpha
              (embedTowerChain k d (towerFrobeniusPoly k x))
              (embedTowerChain k d yOpened) deltaGamma = true)
    (hZeroOpen : yOpened = towerZero k) :
    PSum (x = towerZero k ∨ x = towerOne k)
         (MacKeyRecoveryWitness (k + d) alpha
           (towerAdd (k + d) (embedTowerChain k d yOpened)
             (embedTowerChain k d (towerFrobeniusPoly k x))) deltaGamma) :=
  let yTrue := towerFrobeniusPoly k x
  if hEq : yOpened = yTrue then
    .inl ((towerFrobenius_eq_zero_iff_bit k x).mp (hEq.symm.trans hZeroOpen))
  else
    let embTrue := embedTowerChain k d yTrue
    let embOpen := embedTowerChain k d yOpened
    let deltaY  := towerAdd (k + d) embOpen embTrue
    have hDeltaNe : deltaY ≠ towerZero (k + d) := fun hZ => by
      have hEmbEq : embOpen = embTrue := by
        have h1 := congrArg (fun z => towerAdd (k + d) z embTrue) hZ
        simpa only [deltaY, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using h1
      exact hEq (embedTowerChain_injective k d yOpened yTrue hEmbEq)
    have hMacEq : deltaGamma = towerMul (k + d) alpha deltaY := of_decide_eq_true hMac
    let recAlpha := towerMul (k + d) deltaGamma (towerInv (k + d) deltaY)
    have hRecEq : recAlpha = alpha := by
      dsimp only [recAlpha]
      rw [hMacEq, towerMul_assoc, towerMul_inv (k + d) deltaY hDeltaNe, towerMul_one]
    .inr { deltaX_ne := hDeltaNe
           mac_relation := hMacEq
           recovered_eq := hRecEq }

/-! ### 1b. Share-Level Distributed Frobenius Squaring & Zero-Sum Tower MAC Verification -/

/-- Party-local zero-sum MAC residual shares $\sigma_i = (\gamma_i \oplus \alpha_i \cdot y_{\text{open}}) \oplus z_i$
    over $\mathcal{T}_m$ (`m = k + d`, e.g. $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$). -/
def computeTowerMacSigmas (m : Nat) (openedVal : TowerElem m)
    (macShares alphaShares zeroMasks : List (TowerElem m)) : List (TowerElem m) :=
  ringListZipAdd (shareZipSub macShares (shareScale openedVal alphaShares)) zeroMasks

/-- Distributed zero-sum MAC check $\bigoplus_i \sigma_i = 0$ over $\mathcal{T}_m$. -/
def verifyTowerZeroSumMac (m : Nat) (sigmas : List (TowerElem m)) : Bool :=
  decide (ringListSum sigmas = towerZero m)

theorem verifyTowerZeroSumMac_complete (m : Nat)
    (trueVal openedVal : TowerElem m)
    (macShares alphaShares zeroMasks : List (TowerElem m))
    (hMacLen : macShares.length = alphaShares.length)
    (_hMaskLen : zeroMasks.length = alphaShares.length)
    (hMacSum : ringListSum macShares = towerMul m (ringListSum alphaShares) trueVal)
    (hZeroMask : ringListSum zeroMasks = towerZero m)
    (hEq : openedVal = trueVal) :
    verifyTowerZeroSumMac m (computeTowerMacSigmas m openedVal macShares alphaShares zeroMasks) = true := by
  have hScaleLen : (shareScale openedVal alphaShares).length = alphaShares.length :=
    shareScale_length openedVal alphaShares
  have hSum : ringListSum (computeTowerMacSigmas m openedVal macShares alphaShares zeroMasks) = towerZero m := by
    unfold computeTowerMacSigmas
    rw [ringListSum_zipAdd, ringListSum_zipSub (hMacLen.trans hScaleLen.symm), ringListSum_scale]
    change towerAdd m (towerAdd m (ringListSum macShares) (towerMul m openedVal (ringListSum alphaShares)))
      (ringListSum zeroMasks) = towerZero m
    rw [hZeroMask, towerAdd_zero, hEq, hMacSum, towerMul_comm m trueVal (ringListSum alphaShares),
        towerAdd_self_zero]
  unfold verifyTowerZeroSumMac
  exact decide_eq_true hSum

theorem verifyTowerZeroSumMac_forged_pins_key (m : Nat)
    (alpha trueVal openedVal deltaSigma : TowerElem m)
    (sigmas : List (TowerElem m))
    (hNe : openedVal ≠ trueVal)
    (hSum : ringListSum sigmas =
      towerAdd m (towerAdd m (towerMul m alpha trueVal) deltaSigma) (towerMul m alpha openedVal))
    (hVer : verifyTowerZeroSumMac m sigmas = true) :
    MacKeyRecoveryWitness m alpha (towerAdd m openedVal trueVal) deltaSigma := by
  let deltaY := towerAdd m openedVal trueVal
  have hDeltaNe : deltaY ≠ towerZero m := fun hZ => by
    have h1 := congrArg (fun z => towerAdd m z trueVal) hZ
    have hEq : openedVal = trueVal := by
      simpa only [deltaY, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using h1
    exact hNe hEq
  have hZero : ringListSum sigmas = towerZero m := of_decide_eq_true hVer
  rw [hSum] at hZero
  have hRearr : towerAdd m (towerAdd m (towerMul m alpha trueVal) deltaSigma) (towerMul m alpha openedVal) =
      towerAdd m deltaSigma (towerMul m alpha deltaY) := by
    dsimp only [deltaY]
    rw [towerMul_add_distrib, towerAdd_comm m (towerMul m alpha trueVal) deltaSigma,
        towerAdd_assoc, towerAdd_comm m (towerMul m alpha trueVal) (towerMul m alpha openedVal)]
  rw [hRearr] at hZero
  have hRel : deltaSigma = towerMul m alpha deltaY := by
    have h1 := congrArg (fun z => towerAdd m z (towerMul m alpha deltaY)) hZero
    simpa only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using h1
  have hRec : towerMul m deltaSigma (towerInv m deltaY) = alpha := by
    rw [hRel, towerMul_assoc, towerMul_inv m deltaY hDeltaNe, towerMul_one]
  exact { deltaX_ne := hDeltaNe, mac_relation := hRel, recovered_eq := hRec }

/-- **Share-Level Distributed Frobenius Booleanity Verifier (`evalSharedDkgFrobenius`)**:
    1. Parties run `(t, n)` share-level Beaver squaring `evalSharedBeaverMul lambdas xSh xSh sqTriple`,
       producing shares `sqSh` of $x^2$ while opening only masked differences $(x - a, x - b)$.
    2. Parties locally form Frobenius residual shares `frobSh := shareZipSub sqSh xSh` ($[x^2 \oplus x]$).
    3. Parties verify BOTH $y_{\text{opened}} = 0$ AND the lifted $\mathcal{T}_{k+d}$ zero-sum MAC
       `verifyTowerZeroSumMac (k + d) sigmas`, aborting (`= none`) on any non-zero residual or MAC fault. -/
def evalSharedDkgFrobenius (k d : Nat)
    (lambdas xSh : List (TowerElem k))
    (sqTriple : SharedBeaverTriple (TowerElem k))
    (yOpened : TowerElem k)
    (sigmas : List (TowerElem (k + d))) : Option (List (TowerElem k)) :=
  let (sqSh, _, _) := evalSharedBeaverMul lambdas xSh xSh sqTriple
  let frobSh := shareZipSub sqSh xSh
  if decide (yOpened = towerZero k) && verifyTowerZeroSumMac (k + d) sigmas then
    some frobSh
  else
    none

/-- **Distributed Frobenius Booleanity Completeness (`verifySharedDkgFrobenius_complete`)**:
    Honest `(t, n)` shares `xSh` of a bit $x \in \{0, 1\}$ with a valid Beaver triple and valid
    additive $\mathcal{T}_{k+d}$ MAC shares pass `evalSharedDkgFrobenius` (`= some frobSh`) with
    `ringDot lambdas frobSh = 0`. -/
theorem verifySharedDkgFrobenius_complete (k d : Nat)
    (lambdas xSh : List (TowerElem k))
    (sqTriple : SharedBeaverTriple (TowerElem k))
    (macFrob alphaShares zeroMasks : List (TowerElem (k + d)))
    (hSumOne : ringListSum lambdas = towerOne k)
    (hXLen : xSh.length = lambdas.length)
    (hBit : ringDot lambdas xSh = towerZero k ∨ ringDot lambdas xSh = towerOne k)
    (hTr : sqTriple.validAt lambdas)
    (hMacLen : macFrob.length = alphaShares.length)
    (hMaskLen : zeroMasks.length = alphaShares.length)
    (hZeroMask : ringListSum zeroMasks = towerZero (k + d))
    (hMacSum : ringListSum macFrob =
      towerMul (k + d) (ringListSum alphaShares)
        (embedTowerChain k d (ringDot lambdas (shareZipSub (evalSharedBeaverMul lambdas xSh xSh sqTriple).1 xSh)))) :
    let frobSh := shareZipSub (evalSharedBeaverMul lambdas xSh xSh sqTriple).1 xSh
    let yOpened := ringDot lambdas frobSh
    let sigmas := computeTowerMacSigmas (k + d) (embedTowerChain k d yOpened) macFrob alphaShares zeroMasks
    evalSharedDkgFrobenius k d lambdas xSh sqTriple yOpened sigmas = some frobSh ∧
    yOpened = towerZero k := by
  obtain ⟨hSqLen, _, _, hSqDot⟩ :=
    evalSharedBeaverMul_correct lambdas xSh xSh sqTriple hSumOne hXLen hXLen hTr
  let frobSh := shareZipSub (evalSharedBeaverMul lambdas xSh xSh sqTriple).1 xSh
  have hFrobEq : ringDot lambdas frobSh = towerFrobeniusPoly k (ringDot lambdas xSh) := by
    dsimp only [frobSh, evalSharedBeaverMul]
    rw [ringDot_zipSub (hSqLen.trans hXLen.symm), hSqDot]
    rfl
  have hY0 : ringDot lambdas frobSh = towerZero k :=
    hFrobEq.trans ((towerFrobenius_eq_zero_iff_bit k (ringDot lambdas xSh)).mpr hBit)
  have hMacOk := verifyTowerZeroSumMac_complete (k + d)
    (embedTowerChain k d (ringDot lambdas frobSh))
    (embedTowerChain k d (ringDot lambdas frobSh))
    macFrob alphaShares zeroMasks hMacLen hMaskLen hMacSum hZeroMask rfl
  refine ⟨?_, hY0⟩
  unfold evalSharedDkgFrobenius
  dsimp only
  change (if decide (ringDot lambdas frobSh = towerZero k) &&
      verifyTowerZeroSumMac (k + d)
        (computeTowerMacSigmas (k + d) (embedTowerChain k d (ringDot lambdas frobSh))
          macFrob alphaShares zeroMasks) then some frobSh else none) = some frobSh
  rw [decide_eq_true hY0, hMacOk]
  rfl

/-- **Distributed Frobenius Booleanity Soundness (`verifySharedDkgFrobenius_sound`)**:
    Without assuming external `hZeroOpen` or `hMac` hypotheses, any transcript accepted by
    `evalSharedDkgFrobenius` constructively (`PSum`, `0 Classical.choice`) yields EITHER:
    1. Honest booleanity `ringDot lambdas xSh ∈ {0, 1}`, OR
    2. A corrupted Beaver squaring triple `c ≠ a · b` (caught by `Preprocessing` sacrifice), OR
    3. An algebraic `MacKeyRecoveryWitness` recovering the global MAC key $\alpha \in \mathcal{T}_{k+d}$! -/
def verifySharedDkgFrobenius_sound (k d : Nat)
    (lambdas xSh : List (TowerElem k))
    (sqTriple : SharedBeaverTriple (TowerElem k))
    (yOpened : TowerElem k)
    (alpha deltaSigma : TowerElem (k + d))
    (sigmas : List (TowerElem (k + d)))
    (frobSh : List (TowerElem k))
    (hSumOne : ringListSum lambdas = towerOne k)
    (hXLen : xSh.length = lambdas.length)
    (hALen : sqTriple.aShares.length = lambdas.length)
    (hBLen : sqTriple.bShares.length = lambdas.length)
    (hCLen : sqTriple.cShares.length = lambdas.length)
    (hMacSum : ringListSum sigmas =
      towerAdd (k + d)
        (towerAdd (k + d)
          (towerMul (k + d) alpha (embedTowerChain k d (ringDot lambdas frobSh)))
          deltaSigma)
        (towerMul (k + d) alpha (embedTowerChain k d yOpened)))
    (hAccept : evalSharedDkgFrobenius k d lambdas xSh sqTriple yOpened sigmas = some frobSh) :
    PSum (ringDot lambdas xSh = towerZero k ∨ ringDot lambdas xSh = towerOne k)
      (PSum (ringDot lambdas sqTriple.cShares ≠
              towerMul k (ringDot lambdas sqTriple.aShares) (ringDot lambdas sqTriple.bShares))
            (MacKeyRecoveryWitness (k + d) alpha
              (towerAdd (k + d) (embedTowerChain k d yOpened) (embedTowerChain k d (ringDot lambdas frobSh)))
              deltaSigma)) :=
  if hcEq : ringDot lambdas sqTriple.cShares =
      towerMul k (ringDot lambdas sqTriple.aShares) (ringDot lambdas sqTriple.bShares) then
    have hCondAndEq :
        (decide (yOpened = towerZero k) && verifyTowerZeroSumMac (k + d) sigmas) = true ∧
        shareZipSub (evalSharedBeaverMul lambdas xSh xSh sqTriple).1 xSh = frobSh := by
      unfold evalSharedDkgFrobenius at hAccept
      dsimp only at hAccept
      cases hCond : decide (yOpened = towerZero k) && verifyTowerZeroSumMac (k + d) sigmas with
      | false => rw [hCond] at hAccept; cases hAccept
      | true =>
        rw [hCond] at hAccept
        exact ⟨rfl, Option.some.inj hAccept⟩
    let yTrue := ringDot lambdas frobSh
    if hOpenEq : yOpened = yTrue then
      .inl (by
        have hValid : sqTriple.validAt lambdas := ⟨hALen, hBLen, hCLen, hcEq⟩
        obtain ⟨hSqLen, _, _, hSqDot⟩ :=
          evalSharedBeaverMul_correct lambdas xSh xSh sqTriple hSumOne hXLen hXLen hValid
        have hY0 : yOpened = towerZero k := of_decide_eq_true (Bool.and_eq_true_iff.mp hCondAndEq.1).1
        have hFrobDot : yTrue = towerFrobeniusPoly k (ringDot lambdas xSh) := by
          dsimp only [yTrue]
          rw [← hCondAndEq.2]
          dsimp only [evalSharedBeaverMul]
          rw [ringDot_zipSub (hSqLen.trans hXLen.symm), hSqDot]
          rfl
        exact (towerFrobenius_eq_zero_iff_bit k (ringDot lambdas xSh)).mp
          (hFrobDot.symm.trans (hOpenEq.symm.trans hY0)))
    else
      .inr (.inr (by
        have hMacOk : verifyTowerZeroSumMac (k + d) sigmas = true :=
          (Bool.and_eq_true_iff.mp hCondAndEq.1).2
        have hEmbNe : embedTowerChain k d yOpened ≠ embedTowerChain k d yTrue :=
          fun hEmb => hOpenEq (embedTowerChain_injective k d yOpened yTrue hEmb)
        exact verifyTowerZeroSumMac_forged_pins_key (k + d) alpha
          (embedTowerChain k d yTrue) (embedTowerChain k d yOpened) deltaSigma sigmas
          hEmbNe hMacSum hMacOk))
  else
    .inr (.inl hcEq)

def demoTower3Pt2 : TowerElem 3 := (towerZero 2, towerOne 2)

def demoTower3Lambdas2 : List (TowerElem 3) :=
  let diffInv := towerInv 3 (towerAdd 3 (towerOne 3) demoTower3Pt2)
  [towerMul 3 demoTower3Pt2 diffInv, towerMul 3 (towerOne 3) diffInv]

def demoTower3BeaverSq : SharedBeaverTriple (TowerElem 3) :=
  -- Degree-1 2-party shares at [1, α] for a = 1 (1 + α·X -> [1⊕α, 1⊕α²]), b = 1, c = 1:
  let s1 := [towerAdd 3 (towerOne 3) demoTower3Pt2,
             towerAdd 3 (towerOne 3) (towerMul 3 demoTower3Pt2 demoTower3Pt2)]
  { aShares := s1, bShares := s1, cShares := s1 }

/-- **Inhabitedness Witness (`shared_dkg_frobenius_inhabited`)**:
    Degree-1 Shamir shares of boolean $x = 1 \in \mathcal{T}_3$ pass `evalSharedDkgFrobenius`
    over $\mathcal{T}_3 \hookrightarrow \mathcal{T}_7$ (`k = 3, d = 4`). -/
theorem shared_dkg_frobenius_inhabited :
    let xSh := [towerAdd 3 (towerOne 3) demoTower3Pt2,
                towerAdd 3 (towerOne 3) (towerMul 3 demoTower3Pt2 demoTower3Pt2)]
    let mask7 : TowerElem 7 := (towerOne 6, towerOne 6)
    let sigmas := computeTowerMacSigmas 7 (towerZero 7) [mask7, mask7] [towerOne 7, towerOne 7] [mask7, mask7]
    (evalSharedDkgFrobenius 3 4 demoTower3Lambdas2 xSh demoTower3BeaverSq (towerZero 3) sigmas).isSome = true := by
  decide +kernel

/-- **`#tooth` Non-Binary Shares Rejected by `evalSharedDkgFrobenius`
    (`tooth_shared_dkg_frobenius_rejects_nonbinary_shares`)**:
    When parties hold Shamir shares of non-binary $x = (0, 1) \in \mathcal{T}_3 \setminus \{0, 1\}$,
    `evalSharedDkgFrobenius` rejects BOTH the honest opening $y = x^2 \oplus x \neq 0$ AND a forged
    announcement $y_{\text{bad}} = 0$ against the committee's lifted $\mathcal{T}_7$ MAC shares! -/
theorem tooth_shared_dkg_frobenius_rejects_nonbinary_shares :
    let xBad := demoTower3Pt2
    let xSh := [towerAdd 3 xBad (towerOne 3), towerAdd 3 xBad demoTower3Pt2]
    let frobSh := shareZipSub (evalSharedBeaverMul demoTower3Lambdas2 xSh xSh demoTower3BeaverSq).1 xSh
    let yTrue := ringDot demoTower3Lambdas2 frobSh
    let alpha0 : TowerElem 7 := (towerZero 6, towerOne 6)
    let alpha1 : TowerElem 7 := (towerOne 6, towerZero 6)
    let alphaSum := towerAdd 7 alpha0 alpha1
    let mac0 := towerMul 7 alpha0 (embedTowerChain 3 4 yTrue)
    let mac1 := towerAdd 7 (towerMul 7 alpha1 (embedTowerChain 3 4 yTrue)) (towerZero 7)
    let honestSigmas := computeTowerMacSigmas 7 (embedTowerChain 3 4 yTrue)
      [mac0, mac1] [alpha0, alpha1] [towerZero 7, towerZero 7]
    let forgedZeroSigmas := computeTowerMacSigmas 7 (embedTowerChain 3 4 (towerZero 3))
      [mac0, mac1] [alpha0, alpha1] [towerZero 7, towerZero 7]
    alphaSum ≠ towerZero 7 ∧
    evalSharedDkgFrobenius 3 4 demoTower3Lambdas2 xSh demoTower3BeaverSq yTrue honestSigmas = none ∧
    evalSharedDkgFrobenius 3 4 demoTower3Lambdas2 xSh demoTower3BeaverSq (towerZero 3) forgedZeroSigmas = none := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 2. Polynomial Coefficient Non-Vanishing, `SPDZ` & 2-Lane `BDOZ` Batch MAC Soundness -/

/-- Pairwise antisymmetric PRF zero-sum mask cancellation (`[P0-08]`):
    $(r_{i,j} - r_{j,i}) + (r_{j,i} - r_{i,j}) = 0$ in every `LawfulCommRing R`, enabling pre-opening
    MAC residual checks without broadcasting unmasked shares. -/
theorem pairwiseZeroMasks_sum_eq_zero {R : Type} [LawfulCommRing R] (r_ij r_ji : R) :
    CommRingOps.add (CommRingOps.sub r_ij r_ji) (CommRingOps.sub r_ji r_ij) = CommRingOps.zero := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
      LawfulCommRing.add_assoc r_ij (CommRingOps.neg r_ji),
      ← LawfulCommRing.add_assoc (CommRingOps.neg r_ji) r_ji (CommRingOps.neg r_ij),
      LawfulCommRing.add_left_neg,
      LawfulCommRing.zero_add,
      LawfulCommRing.add_right_neg]

private def quotLinLocal {R : Type} [CommRingOps R] : List R → R → List R
  | [], _ => []
  | [_], _ => []
  | _ :: c₁ :: cs, r => RoundPoly.evalCoeffs (c₁ :: cs) r :: quotLinLocal (c₁ :: cs) r

private theorem quotLinLocal_length {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (r : R), (quotLinLocal cs r).length = cs.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: c₁ :: cs, r => by
    simp only [quotLinLocal, List.length_cons, quotLinLocal_length (c₁ :: cs) r]
    simp

private theorem evalCoeffs_eq_mul_quotLinLocal_add {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r x : R),
      RoundPoly.evalCoeffs cs x =
        CommRingOps.add
          (CommRingOps.mul (CommRingOps.sub x r) (RoundPoly.evalCoeffs (quotLinLocal cs r) x))
          (RoundPoly.evalCoeffs cs r)
  | [], _, _ => by
    simp [quotLinLocal, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [_], _, _ => by
    simp [quotLinLocal, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  | c₀ :: c₁ :: cs, r, x => by
    let tl := c₁ :: cs
    have ih := evalCoeffs_eq_mul_quotLinLocal_add tl r x
    change CommRingOps.add c₀ (CommRingOps.mul x (RoundPoly.evalCoeffs tl x)) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub x r)
          (CommRingOps.add (RoundPoly.evalCoeffs tl r) (CommRingOps.mul x (RoundPoly.evalCoeffs (quotLinLocal tl r) x))))
        (CommRingOps.add c₀ (CommRingOps.mul r (RoundPoly.evalCoeffs tl r)))
    rw [ih, LawfulCommRing.left_distrib x, LawfulCommRing.left_distrib (CommRingOps.sub x r),
        LawfulCommRing.sub_mul x r (RoundPoly.evalCoeffs tl r)]
    have hcommX : CommRingOps.mul (CommRingOps.sub x r)
        (CommRingOps.mul x (RoundPoly.evalCoeffs (quotLinLocal tl r) x)) =
        CommRingOps.mul x
          (CommRingOps.mul (CommRingOps.sub x r) (RoundPoly.evalCoeffs (quotLinLocal tl r) x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub x r) x,
          LawfulCommRing.mul_assoc]
    rw [hcommX]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul r (RoundPoly.evalCoeffs tl r))
    let A := CommRingOps.mul r (RoundPoly.evalCoeffs tl r)
    let B := CommRingOps.mul x (RoundPoly.evalCoeffs tl r)
    let C := CommRingOps.mul x (CommRingOps.mul (CommRingOps.sub x r) (RoundPoly.evalCoeffs (quotLinLocal tl r) x))
    change CommRingOps.add A (CommRingOps.add c₀ (CommRingOps.add C B)) =
      CommRingOps.add A (CommRingOps.add (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A))
    rw [← LawfulCommRing.add_assoc A (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A),
        ← LawfulCommRing.add_assoc A (CommRingOps.sub B A) C,
        LawfulCommRing.add_sub_cancel_left A B,
        LawfulCommRing.add_comm C B,
        LawfulCommRing.add_comm c₀ A,
        ← LawfulCommRing.add_assoc A c₀ (CommRingOps.add B C),
        LawfulCommRing.add_comm A c₀,
        LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        ← LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        LawfulCommRing.add_comm (CommRingOps.add c₀ A) (CommRingOps.add B C)]

private theorem coeffs_zero_of_eval_and_quotLinear_zero {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : R),
      RoundPoly.evalCoeffs cs r = CommRingOps.zero →
      (∀ q ∈ quotLinLocal cs r, q = CommRingOps.zero) →
      ∀ c ∈ cs, c = CommRingOps.zero
  | [], _, _, _, _, h => by cases h
  | [c₀], _, hEv, _, c, hc => by
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hEv
    rcases List.mem_singleton.mp hc with rfl
    exact hEv
  | c₀ :: c₁ :: tl, r, hEv, hQ, c, hc => by
    have hEvTl : RoundPoly.evalCoeffs (c₁ :: tl) r = CommRingOps.zero := by
      exact hQ (RoundPoly.evalCoeffs (c₁ :: tl) r) (by simp [quotLinLocal])
    have hQTl : ∀ q ∈ quotLinLocal (c₁ :: tl) r, q = CommRingOps.zero :=
      fun q hq => hQ q (by simp [quotLinLocal, hq])
    have ihTl := coeffs_zero_of_eval_and_quotLinear_zero (c₁ :: tl) r hEvTl hQTl
    have hc0 : c₀ = CommRingOps.zero := by
      change CommRingOps.add c₀ (CommRingOps.mul r (RoundPoly.evalCoeffs (c₁ :: tl) r)) = CommRingOps.zero at hEv
      rw [hEvTl, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hEv
      exact hEv
    rcases List.mem_cons.mp hc with rfl | hMemTl
    · exact hc0
    · exact ihTl c hMemTl

/-- **Coefficient Vanishing Theorem (`poly_coeffs_zero_of_vanish_nodup`)**:
    Over any integral domain `[LawfulCommRing R] [NoZeroDivisors R]`, if a polynomial `cs` of formal
    length $\le |S|$ vanishes on every point of a `Nodup` list `S`, then **every coefficient of `cs`
    is identically zero**. -/
theorem poly_coeffs_zero_of_vanish_nodup
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (S : List R) (cs : List R),
      S.Nodup →
      cs.length ≤ S.length →
      (∀ r ∈ S, RoundPoly.evalCoeffs cs r = CommRingOps.zero) →
      ∀ c ∈ cs, c = CommRingOps.zero
  | [], cs, _, hLen, _, c, hc => by
    cases cs with
    | nil => cases hc
    | cons _ _ => simp at hLen
  | s0 :: sRest, cs, .cons hs0Not hNdRest, hLen, hZero, c, hc => by
    have hs0Ev : RoundPoly.evalCoeffs cs s0 = CommRingOps.zero := hZero s0 (.head _)
    let q := quotLinLocal cs s0
    have hqLen : q.length ≤ sRest.length := by
      dsimp only [q]
      rw [quotLinLocal_length]
      simp only [List.length_cons] at hLen
      omega
    have hqZero : ∀ r ∈ sRest, RoundPoly.evalCoeffs q r = CommRingOps.zero := by
      intro r hr
      have hrEv := hZero r (.tail _ hr)
      have hFac := evalCoeffs_eq_mul_quotLinLocal_add cs s0 r
      rw [hrEv, hs0Ev, LawfulCommRing.add_zero] at hFac
      have hrNe : r ≠ s0 := fun hEq => hs0Not r hr hEq.symm
      have hSubNe : CommRingOps.sub r s0 ≠ CommRingOps.zero :=
        fun hSub => hrNe (LawfulCommRing.sub_eq_zero_iff.mp hSub)
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hFac.symm with hBad | hOk
      · exact False.elim (hSubNe hBad)
      · exact hOk
    have hqCoeffs := poly_coeffs_zero_of_vanish_nodup sRest q hNdRest hqLen hqZero
    exact coeffs_zero_of_eval_and_quotLinear_zero cs s0 hs0Ev hqCoeffs c hc

private def findNonzeroEval {R : Type} [CommRingOps R] [DecidableEq R] (cs : List R) :
    (xs : List R) →
    PSum { r : R // RoundPoly.evalCoeffs cs r ≠ CommRingOps.zero }
         (∀ r ∈ xs, RoundPoly.evalCoeffs cs r = CommRingOps.zero)
  | [] => .inr (fun _ hm => by cases hm)
  | x :: xs =>
    if hx : RoundPoly.evalCoeffs cs x = CommRingOps.zero then
      match findNonzeroEval cs xs with
      | .inl w => .inl w
      | .inr hRest => .inr (fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hTl
          · exact hx
          · exact hRest r hTl)
    else
      .inl ⟨x, hx⟩

private theorem exists_eval_nonzero_of_coeff_nonzero
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (L : Nat) (cs S : List R)
    (hNodup : S.Nodup) (hCsLen : cs.length ≤ L + 1) (hDom : L + 1 ≤ S.length)
    (hNonzero : ∃ c ∈ cs, c ≠ CommRingOps.zero) :
    ∃ x₀ : R, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero := by
  match findNonzeroEval cs (S.take (L + 1)) with
  | .inl ⟨x₀, hx₀⟩ => exact ⟨x₀, hx₀⟩
  | .inr hAll =>
    exfalso
    obtain ⟨d, hdMem, hdNe⟩ := hNonzero
    have hTakeLen : (S.take (L + 1)).length = L + 1 := List.length_take_of_le hDom
    have hNdTake : (S.take (L + 1)).Nodup := (List.take_sublist (L + 1) S).nodup hNodup
    have hZeroAll := poly_coeffs_zero_of_vanish_nodup (S.take (L + 1)) cs hNdTake
      (by rw [hTakeLen]; exact hCsLen) hAll
    exact hdNe (hZeroAll d hdMem)

/-- Batch MAC linear combination $\Delta X(r) = \sum_{j=0}^{L-1} \Delta x_j \cdot r^{j+1}$. -/
@[expose] def batchDeviationPoly {R : Type} [CommRingOps R] (deltas : List R) (r : R) : R :=
  RoundPoly.evalCoeffs (CommRingOps.zero :: deltas) r

/-- **Dishonest-Majority `SPDZ` Batch MAC Soundness (`spdz_batch_mac_soundness`)**:
    Over `GoldilocksExt2` ($|\mathbb{F}_{p^2}| \approx 2^{128}$):
    1. **Challenge Root Bound**: For ANY batch `deltas` of $\le L$ wire deviations containing at least
       one non-zero forgery `d ≠ 0`, and ANY `Nodup` challenge domain `S` with $|S| \ge L + 1$, at most
       $L$ challenges $r \in S$ yield $\Delta X(r) = 0$.
    2. **Unique MAC Key Pinning (`1 / |\mathbb{F}_{p^2}|`)**: Whenever $\Delta X(r) \neq 0$, an adversary
       passing $\Delta\Gamma = \alpha \cdot \Delta X(r)$ constructively recovers $\alpha = \Delta\Gamma \cdot \Delta X(r)^{-1}$! -/
theorem spdz_batch_mac_soundness
    (L : Nat) (deltas : List GoldilocksExt2) (S : List GoldilocksExt2)
    (hNodup : S.Nodup) (hLen : deltas.length ≤ L) (hDom : L + 1 ≤ S.length)
    (hNonzero : ∃ d ∈ deltas, d ≠ GoldilocksExt2.zero) :
    (S.filter (fun r => decide (batchDeviationPoly deltas r = GoldilocksExt2.zero))).length ≤ L ∧
    (∀ (alpha r deltaGamma : GoldilocksExt2),
      batchDeviationPoly deltas r ≠ GoldilocksExt2.zero →
      verifyLinearMacEquation alpha GoldilocksExt2.zero (batchDeviationPoly deltas r) deltaGamma = true →
      CommRingOps.mul deltaGamma (GoldilocksExt2.inv (batchDeviationPoly deltas r)) = alpha) := by
  let cs : List GoldilocksExt2 := GoldilocksExt2.zero :: deltas
  have hCsLen : cs.length ≤ L + 1 := Nat.succ_le_succ hLen
  have hExEval : ∃ x₀ : GoldilocksExt2, RoundPoly.evalCoeffs cs x₀ ≠ GoldilocksExt2.zero := by
    obtain ⟨d, hdMem, hdNe⟩ := hNonzero
    exact exists_eval_nonzero_of_coeff_nonzero L cs S hNodup hCsLen hDom ⟨d, .tail _ hdMem, hdNe⟩
  refine ⟨RoundPoly.roots_nodup_length_le L cs S hNodup hCsLen hExEval, ?_⟩
  intro alpha r deltaGamma hDxNe hVer
  have hEq : deltaGamma = CommRingOps.mul alpha (CommRingOps.sub (batchDeviationPoly deltas r) GoldilocksExt2.zero) :=
    of_decide_eq_true hVer
  have hSub0 : CommRingOps.sub (batchDeviationPoly deltas r) GoldilocksExt2.zero = batchDeviationPoly deltas r := by
    change CommRingOps.sub (batchDeviationPoly deltas r) CommRingOps.zero = batchDeviationPoly deltas r
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.neg_zero, LawfulCommRing.add_zero]
  rw [hSub0] at hEq
  rw [hEq, LawfulCommRing.mul_assoc, GoldilocksExt2.mul_inv_cancel hDxNe, LawfulCommRing.mul_one]

/-- Pairwise 2-lane `Tower128` BDOZ MAC share held by party $j$ and verified by party $i$:
    $m_{j,i}^{(0)} = k_{i,j}^{(0)} \oplus \alpha_i^{(0)} \cdot x_j$ and
    $m_{j,i}^{(1)} = k_{i,j}^{(1)} \oplus \alpha_i^{(1)} \cdot x_j$ (`2 × 128 = 256`-bit key!). -/
structure BdozPairOpening where
  partyId : Nat
  shareX  : Tower128
  mac0    : Tower128
  mac1    : Tower128
  deriving DecidableEq

structure BdozVerifierKeys where
  alpha0 : Tower128
  alpha1 : Tower128
  localK : Nat → (Tower128 × Tower128)

@[expose] def verifyBdozPairMac (vk : BdozVerifierKeys) (op : BdozPairOpening) : Bool :=
  let (k0, k1) := vk.localK op.partyId
  (op.mac0 == towerAdd 7 k0 (towerMul 7 vk.alpha0 op.shareX)) &&
  (op.mac1 == towerAdd 7 k1 (towerMul 7 vk.alpha1 op.shareX))

/-- Slashing receipt pinpointing the exact deviating `PartyId` during BDOZ identifiable abort. -/
structure SlashingReceipt (vk : BdozVerifierKeys) where
  cheater : BdozPairOpening
  invalid : verifyBdozPairMac vk cheater = false

/-- Constructive `0 Classical.choice` BDOZ cheater extractor (`extractBdozCheaterOrValid`):
    walks submitted `BdozPairOpening`s and returns EITHER a `SlashingReceipt` on an invalid
    party OR a proof that every party's 2-lane BDOZ MAC verified cleanly! -/
def extractBdozCheaterOrValid (vk : BdozVerifierKeys) :
    (ops : List BdozPairOpening) →
    PSum (PSigma (fun op => op ∈ ops ∧ verifyBdozPairMac vk op = false))
         (∀ op ∈ ops, verifyBdozPairMac vk op = true)
  | [] => .inr (fun _ h => by cases h)
  | op :: rest =>
    match hVer : verifyBdozPairMac vk op with
    | false => .inl ⟨op, .head _, hVer⟩
    | true =>
      match extractBdozCheaterOrValid vk rest with
      | .inl ⟨bad, hMem, hBad⟩ => .inl ⟨bad, .tail _ hMem, hBad⟩
      | .inr hAll => .inr (fun y hy => by
          rcases List.mem_cons.mp hy with rfl | hTl
          · exact hVer
          · exact hAll y hTl)

/-- **Anti-Framing Guarantee (`honest_party_never_slashed`)**:
    Any honest party $j$ computing $m_{j,i}^{(\ell)} = k_{i,j}^{(\ell)} \oplus \alpha_i^{(\ell)} \cdot x_j$
    passes `verifyBdozPairMac` unconditionally and can NEVER be accused by `extractBdozCheaterOrValid`! -/
theorem honest_party_never_slashed (vk : BdozVerifierKeys) (j : Nat) (xj : Tower128) :
    let (k0, k1) := vk.localK j
    let honestOp : BdozPairOpening :=
      { partyId := j
        shareX  := xj
        mac0    := towerAdd 7 k0 (towerMul 7 vk.alpha0 xj)
        mac1    := towerAdd 7 k1 (towerMul 7 vk.alpha1 xj) }
    verifyBdozPairMac vk honestOp = true := by
  simp [verifyBdozPairMac]

/-- Two accepted, different openings for one party pin both MAC keys to public deltas. -/
theorem bdoz_pair_key_recovery
    (vk : BdozVerifierKeys) (opHon opAdv : BdozPairOpening)
    (hPid : opHon.partyId = opAdv.partyId)
    (hNe : opHon.shareX ≠ opAdv.shareX)
    (hVerH : verifyBdozPairMac vk opHon = true)
    (hVerA : verifyBdozPairMac vk opAdv = true) :
    let dxInv := towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)
    towerMul 7 (towerAdd 7 opAdv.mac0 opHon.mac0) dxInv = vk.alpha0 ∧
    towerMul 7 (towerAdd 7 opAdv.mac1 opHon.mac1) dxInv = vk.alpha1 := by
  unfold verifyBdozPairMac at hVerH hVerA
  rw [← hPid] at hVerA
  rcases Bool.and_eq_true_iff.mp hVerH with ⟨hH0, hH1⟩
  rcases Bool.and_eq_true_iff.mp hVerA with ⟨hA0, hA1⟩
  have hmH0 : opHon.mac0 = towerAdd 7 (vk.localK opHon.partyId).1 (towerMul 7 vk.alpha0 opHon.shareX) := eq_of_beq hH0
  have hmH1 : opHon.mac1 = towerAdd 7 (vk.localK opHon.partyId).2 (towerMul 7 vk.alpha1 opHon.shareX) := eq_of_beq hH1
  have hmA0 : opAdv.mac0 = towerAdd 7 (vk.localK opHon.partyId).1 (towerMul 7 vk.alpha0 opAdv.shareX) := eq_of_beq hA0
  have hmA1 : opAdv.mac1 = towerAdd 7 (vk.localK opHon.partyId).2 (towerMul 7 vk.alpha1 opAdv.shareX) := eq_of_beq hA1
  let dx := towerAdd 7 opAdv.shareX opHon.shareX
  have hDxNe : dx ≠ towerZero 7 := fun hZ => by
    have h1 := congrArg (fun z => towerAdd 7 z opHon.shareX) hZ
    have hEqX : opAdv.shareX = opHon.shareX := by
      simpa only [dx, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using h1
    exact hNe hEqX.symm
  have hCancelK : ∀ (k alpha : Tower128),
      towerAdd 7 (towerAdd 7 k (towerMul 7 alpha opAdv.shareX))
                 (towerAdd 7 k (towerMul 7 alpha opHon.shareX)) =
      towerMul 7 alpha dx := by
    intro k alpha
    dsimp only [dx]
    rw [towerAdd_assoc 7 k, towerAdd_left_comm 7 _ k, towerAdd_cancel 7 k, ← towerMul_add_distrib]
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [hmA0, hmH0, hCancelK, towerMul_assoc, towerMul_inv 7 dx hDxNe, towerMul_one]
  · rw [hmA1, hmH1, hCancelK, towerMul_assoc, towerMul_inv 7 dx hDxNe, towerMul_one]

/-- **2-Lane `Tower128` BDOZ Batch MAC Soundness (`bdoz_2lane_mac_soundness`)**:
    1. Any non-zero batch of $\le L$ wire deviations in $\mathcal{T}_7 = \mathbb{F}_{2^{128}}$ has
       $\le L$ challenge roots in any `Nodup` domain $S$ ($|S| \ge L + 1$).
    2. When $\Delta x_j \neq 0$ on party $j$'s share, passing `verifyBdozPairMac` simultaneously pins
       **both** independent 128-bit keys $(\alpha_i^{(0)}, \alpha_i^{(1)}) \in \mathcal{T}_7^2$
       ($2^{-256}$ key-guessing probability!). -/
theorem bdoz_2lane_mac_soundness
    (L : Nat) (deltas : List Tower128) (S : List Tower128)
    (hNodup : S.Nodup) (hLen : deltas.length ≤ L) (hDom : L + 1 ≤ S.length)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    (S.filter (fun r => decide (batchDeviationPoly deltas r = towerZero 7))).length ≤ L ∧
    (∀ (vk : BdozVerifierKeys) (opHon opAdv : BdozPairOpening),
      opHon.partyId = opAdv.partyId →
      opHon.shareX ≠ opAdv.shareX →
      verifyBdozPairMac vk opHon = true →
      verifyBdozPairMac vk opAdv = true →
      let dxInv := towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)
      towerMul 7 (towerAdd 7 opAdv.mac0 opHon.mac0) dxInv = vk.alpha0 ∧
      towerMul 7 (towerAdd 7 opAdv.mac1 opHon.mac1) dxInv = vk.alpha1) := by
  let cs : List Tower128 := towerZero 7 :: deltas
  have hCsLen : cs.length ≤ L + 1 := Nat.succ_le_succ hLen
  have hExEval : ∃ x₀ : Tower128, RoundPoly.evalCoeffs cs x₀ ≠ towerZero 7 := by
    obtain ⟨d, hdMem, hdNe⟩ := hNonzero
    exact exists_eval_nonzero_of_coeff_nonzero L cs S hNodup hCsLen hDom ⟨d, .tail _ hdMem, hdNe⟩
  refine ⟨RoundPoly.roots_nodup_length_le L cs S hNodup hCsLen hExEval, ?_⟩
  exact bdoz_pair_key_recovery

/-! ### 2b. BDOZ Tag-First Key View, Forgery Witness and Key-Counting Bound -/

theorem verifyBdozPairMac_eq (vk : BdozVerifierKeys) (op : BdozPairOpening) :
    verifyBdozPairMac vk op =
      ((op.mac0 == towerAdd 7 (vk.localK op.partyId).1 (towerMul 7 vk.alpha0 op.shareX)) &&
       (op.mac1 == towerAdd 7 (vk.localK op.partyId).2 (towerMul 7 vk.alpha1 op.shareX))) := by
  unfold verifyBdozPairMac
  generalize vk.localK op.partyId = kk
  cases kk
  rfl

/-- The opening message an honest prover sends for share `x` in slot `j`, as dealt under `vk`. -/
@[expose] def bdozHonestOpening (vk : BdozVerifierKeys) (j : Nat) (x : Tower128) : BdozPairOpening :=
  { partyId := j
    shareX  := x
    mac0    := towerAdd 7 (vk.localK j).1 (towerMul 7 vk.alpha0 x)
    mac1    := towerAdd 7 (vk.localK j).2 (towerMul 7 vk.alpha1 x) }

theorem bdozHonestOpening_accepted (vk : BdozVerifierKeys) (j : Nat) (x : Tower128) :
    verifyBdozPairMac vk (bdozHonestOpening vk j x) = true := by
  rw [verifyBdozPairMac_eq]
  simp [bdozHonestOpening]

/-- What a prover holds for slot `s` after preprocessing: its share and both tags. -/
@[expose] def bdozViewOpening (hon : Nat → Tower128 × Tower128 × Tower128) (s : Nat) :
    BdozPairOpening :=
  { partyId := s, shareX := (hon s).1, mac0 := (hon s).2.1, mac1 := (hon s).2.2 }

/-- Verifier key in tag-first form: the global key `alpha` together with the local keys forced
    by the prover's view `hon` (share and tags of every slot), `k = tag + alpha * share`. -/
@[expose] def bdozKeyFromView (alpha : Tower128 × Tower128)
    (hon : Nat → Tower128 × Tower128 × Tower128) : BdozVerifierKeys :=
  { alpha0 := alpha.1
    alpha1 := alpha.2
    localK := fun s =>
      (towerAdd 7 (hon s).2.1 (towerMul 7 alpha.1 (hon s).1),
       towerAdd 7 (hon s).2.2 (towerMul 7 alpha.2 (hon s).1)) }

/-- Every global key is consistent with the prover's view. -/
theorem bdozKeyFromView_accepts_view (alpha : Tower128 × Tower128)
    (hon : Nat → Tower128 × Tower128 × Tower128) (s : Nat) :
    verifyBdozPairMac (bdozKeyFromView alpha hon) (bdozViewOpening hon s) = true := by
  rw [verifyBdozPairMac_eq]
  simp [bdozKeyFromView, bdozViewOpening, towerAdd_assoc]

/-- Conversely every verifier key that accepts the prover's slot-`s` view has the tag-first local
    key in that slot, so the tag-first family is exactly the set of keys the prover cannot rule out. -/
theorem bdozKeyFromView_complete (vk : BdozVerifierKeys)
    (hon : Nat → Tower128 × Tower128 × Tower128) (s : Nat)
    (hAcc : verifyBdozPairMac vk (bdozViewOpening hon s) = true) :
    vk.localK s = (bdozKeyFromView (vk.alpha0, vk.alpha1) hon).localK s := by
  rw [verifyBdozPairMac_eq] at hAcc
  rcases Bool.and_eq_true_iff.mp hAcc with ⟨h0, h1⟩
  have e0 : (hon s).2.1 = towerAdd 7 (vk.localK s).1 (towerMul 7 vk.alpha0 (hon s).1) := eq_of_beq h0
  have e1 : (hon s).2.2 = towerAdd 7 (vk.localK s).2 (towerMul 7 vk.alpha1 (hon s).1) := eq_of_beq h1
  apply Prod.ext
  · show (vk.localK s).1 = towerAdd 7 (hon s).2.1 (towerMul 7 vk.alpha0 (hon s).1)
    have h := congrArg (fun z => towerAdd 7 z (towerMul 7 vk.alpha0 (hon s).1)) e0
    simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] at h
    exact h.symm
  · show (vk.localK s).2 = towerAdd 7 (hon s).2.2 (towerMul 7 vk.alpha1 (hon s).1)
    have h := congrArg (fun z => towerAdd 7 z (towerMul 7 vk.alpha1 (hon s).1)) e1
    simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] at h
    exact h.symm

/-- The key guess an accepted tampered opening `op` commits to; computed from `op` and the
    prover's own view only. -/
@[expose] def bdozKeyGuess (hon : Nat → Tower128 × Tower128 × Tower128) (op : BdozPairOpening) :
    Tower128 × Tower128 :=
  let dxInv := towerInv 7 (towerAdd 7 op.shareX (hon op.partyId).1)
  (towerMul 7 (towerAdd 7 op.mac0 (hon op.partyId).2.1) dxInv,
   towerMul 7 (towerAdd 7 op.mac1 (hon op.partyId).2.2) dxInv)

/-- An accepted opening with a share different from the dealt one pins the global key. -/
theorem bdoz_forgery_pins_key (alpha : Tower128 × Tower128)
    (hon : Nat → Tower128 × Tower128 × Tower128) (op : BdozPairOpening)
    (hNe : op.shareX ≠ (hon op.partyId).1)
    (hAcc : verifyBdozPairMac (bdozKeyFromView alpha hon) op = true) :
    alpha = bdozKeyGuess hon op := by
  obtain ⟨h0, h1⟩ := bdoz_pair_key_recovery (bdozKeyFromView alpha hon)
    (bdozViewOpening hon op.partyId) op rfl (fun h => hNe h.symm)
    (bdozKeyFromView_accepts_view alpha hon op.partyId) hAcc
  exact Prod.ext h0.symm h1.symm

/-- MAC forgery witness: two accepted openings of one slot with different shares. -/
structure BdozMacForgeryWitness (vk : BdozVerifierKeys) (opHon opAdv : BdozPairOpening) : Prop where
  same_slot : opHon.partyId = opAdv.partyId
  share_ne : opHon.shareX ≠ opAdv.shareX
  honest_accepted : verifyBdozPairMac vk opHon = true
  forged_accepted : verifyBdozPairMac vk opAdv = true

/-- A forgery witness is a correct guess of both global key lanes. -/
theorem BdozMacForgeryWitness.key_guess {vk : BdozVerifierKeys} {opHon opAdv : BdozPairOpening}
    (h : BdozMacForgeryWitness vk opHon opAdv) :
    vk.alpha0 = towerMul 7 (towerAdd 7 opAdv.mac0 opHon.mac0)
                  (towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)) ∧
    vk.alpha1 = towerMul 7 (towerAdd 7 opAdv.mac1 opHon.mac1)
                  (towerInv 7 (towerAdd 7 opAdv.shareX opHon.shareX)) := by
  obtain ⟨h0, h1⟩ := bdoz_pair_key_recovery vk opHon opAdv h.same_slot h.share_ne
    h.honest_accepted h.forged_accepted
  exact ⟨h0.symm, h1.symm⟩

theorem bdozMacForgeryWitness_requires_acceptance {vk : BdozVerifierKeys}
    {opHon opAdv : BdozPairOpening} (hRej : verifyBdozPairMac vk opAdv = false) :
    ¬ BdozMacForgeryWitness vk opHon opAdv := by
  intro h
  rw [h.forged_accepted] at hRej
  cases hRej

/-- **Key-Counting Bound for a Fixed Tampered Opening
    (`bdoz_tampered_opening_accepting_keys_le_one`)**: among any `CK` distinct global keys
    consistent with the prover's view, at most one accepts a fixed opening whose share differs
    from the dealt share. -/
theorem bdoz_tampered_opening_accepting_keys_le_one
    (CK : Nat) (keyDec : Fin CK → Tower128 × Tower128)
    (hInj : ∀ i j, keyDec i = keyDec j → i = j)
    (hon : Nat → Tower128 × Tower128 × Tower128) (op : BdozPairOpening)
    (hNe : op.shareX ≠ (hon op.partyId).1) :
    finSum CK (fun i =>
      if verifyBdozPairMac (bdozKeyFromView (keyDec i) hon) op then 1 else 0) ≤ 1 :=
  finSum_indicator_le_one_of_unique CK
    (fun i => verifyBdozPairMac (bdozKeyFromView (keyDec i) hon) op)
    (fun i j hi hj => hInj i j
      ((bdoz_forgery_pins_key (keyDec i) hon op hNe hi).trans
        (bdoz_forgery_pins_key (keyDec j) hon op hNe hj).symm))

/-- Negative regression: shifting a tag of an accepted opening by any non-zero amount makes the
    verifier reject it, under every key. -/
theorem bdoz_tag_tamper_rejected (vk : BdozVerifierKeys) (op : BdozPairOpening)
    (hAcc : verifyBdozPairMac vk op = true) (delta : Tower128) (hDelta : delta ≠ towerZero 7) :
    verifyBdozPairMac vk { op with mac0 := towerAdd 7 op.mac0 delta } = false := by
  rw [verifyBdozPairMac_eq] at hAcc
  rcases Bool.and_eq_true_iff.mp hAcc with ⟨h0, _⟩
  have e0 : op.mac0 = towerAdd 7 (vk.localK op.partyId).1 (towerMul 7 vk.alpha0 op.shareX) :=
    eq_of_beq h0
  have hFalse : (towerAdd 7 op.mac0 delta ==
      towerAdd 7 (vk.localK op.partyId).1 (towerMul 7 vk.alpha0 op.shareX)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    have e1 := eq_of_beq hb
    rw [← e0] at e1
    have h2 := congrArg (fun z => towerAdd 7 op.mac0 z) e1
    simp only [towerAdd_cancel, towerAdd_self_zero] at h2
    exact hDelta h2
  rw [verifyBdozPairMac_eq]
  show ((towerAdd 7 op.mac0 delta ==
      towerAdd 7 (vk.localK op.partyId).1 (towerMul 7 vk.alpha0 op.shareX)) &&
    (op.mac1 == towerAdd 7 (vk.localK op.partyId).2 (towerMul 7 vk.alpha1 op.shareX))) = false
  rw [hFalse, Bool.false_and]

/-- The key-guess forgery: shifting the dealt share by `delta` and each tag by `alpha * delta` is
    accepted. This is the only way past the check, and it requires knowing `alpha`. -/
theorem bdoz_key_guess_forgery_accepted (alpha : Tower128 × Tower128)
    (hon : Nat → Tower128 × Tower128 × Tower128) (s : Nat) (delta : Tower128) :
    verifyBdozPairMac (bdozKeyFromView alpha hon)
      ⟨s, towerAdd 7 (hon s).1 delta,
          towerAdd 7 (hon s).2.1 (towerMul 7 alpha.1 delta),
          towerAdd 7 (hon s).2.2 (towerMul 7 alpha.2 delta)⟩ = true := by
  rw [verifyBdozPairMac_eq]
  simp [bdozKeyFromView, towerMul_add_distrib, towerAdd_assoc]

/-- The forgery witness is inhabited exactly by a correct key guess, and the guess extracted from
    the forged opening is the key. -/
theorem bdozMacForgeryWitness_of_key_guess (alpha : Tower128 × Tower128)
    (hon : Nat → Tower128 × Tower128 × Tower128) (s : Nat) (delta : Tower128)
    (hDelta : delta ≠ towerZero 7) :
    BdozMacForgeryWitness (bdozKeyFromView alpha hon) (bdozViewOpening hon s)
      ⟨s, towerAdd 7 (hon s).1 delta,
          towerAdd 7 (hon s).2.1 (towerMul 7 alpha.1 delta),
          towerAdd 7 (hon s).2.2 (towerMul 7 alpha.2 delta)⟩ ∧
    alpha = bdozKeyGuess hon
      ⟨s, towerAdd 7 (hon s).1 delta,
          towerAdd 7 (hon s).2.1 (towerMul 7 alpha.1 delta),
          towerAdd 7 (hon s).2.2 (towerMul 7 alpha.2 delta)⟩ := by
  have hNe : towerAdd 7 (hon s).1 delta ≠ (hon s).1 := by
    intro h
    have h2 := congrArg (fun z => towerAdd 7 (hon s).1 z) h
    simp only [towerAdd_cancel, towerAdd_self_zero] at h2
    exact hDelta h2
  have hAcc := bdoz_key_guess_forgery_accepted alpha hon s delta
  exact ⟨⟨rfl, fun h => hNe h.symm, bdozKeyFromView_accepts_view alpha hon s, hAcc⟩,
    bdoz_forgery_pins_key alpha hon _ hNe hAcc⟩

theorem bdozMacForgeryWitness_inhabited :
    ∃ vk opHon opAdv, BdozMacForgeryWitness vk opHon opAdv :=
  ⟨_, _, _, (bdozMacForgeryWitness_of_key_guess (towerOne 7, towerZero 7)
    (fun _ => (towerZero 7, towerOne 7, towerZero 7)) 0 (towerOne 7) (by decide +kernel)).1⟩

/-- Inhabitedness of the counting bound: two distinct candidate keys, one tampered opening. -/
theorem bdoz_key_counting_inhabited :
    finSum 2 (fun i =>
      if verifyBdozPairMac
          (bdozKeyFromView (if i.val = 0 then (towerOne 7, towerZero 7) else (towerZero 7, towerZero 7))
            (fun _ => (towerZero 7, towerOne 7, towerZero 7)))
          ⟨0, towerOne 7, towerZero 7, towerZero 7⟩ then 1 else 0) ≤ 1 := by
  have hNe : (⟨0, towerOne 7, towerZero 7, towerZero 7⟩ : BdozPairOpening).shareX ≠
      ((fun _ => (towerZero 7, towerOne 7, towerZero 7) :
        Nat → Tower128 × Tower128 × Tower128)
          (⟨0, towerOne 7, towerZero 7, towerZero 7⟩ : BdozPairOpening).partyId).1 := by
    decide +kernel
  refine bdoz_tampered_opening_accepting_keys_le_one 2
    (fun i => if i.val = 0 then (towerOne 7, towerZero 7) else (towerZero 7, towerZero 7))
    ?_ (fun _ => (towerZero 7, towerOne 7, towerZero 7))
    ⟨0, towerOne 7, towerZero 7, towerZero 7⟩ hNe
  have hOneNe : ¬ ((towerOne 7, towerZero 7) : Tower128 × Tower128) =
      (towerZero 7, towerZero 7) := by decide +kernel
  intro i j h
  match i, j, h with
  | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | ⟨0, _⟩, ⟨1, _⟩, h => exact absurd h hOneNe
  | ⟨1, _⟩, ⟨0, _⟩, h => exact absurd h.symm hOneNe
  | ⟨1, _⟩, ⟨1, _⟩, _ => rfl
  | ⟨n + 2, hn⟩, _, _ => exact absurd hn (Nat.not_lt.mpr (Nat.le_add_left 2 n))
  | _, ⟨n + 2, hn⟩, _ => exact absurd hn (Nat.not_lt.mpr (Nat.le_add_left 2 n))

/-! ## 3. Active 3-Party `FLNW17` Replicated View Cross-Check (`rss_flnw_active_open_sound`) -/

/-- Each party $i \in \{0, 1, 2\}$ announces BOTH shares in its 2-of-3 RSS view:
    Party 0 announces `(p0_x0, p0_x1)`, Party 1 `(p1_x1, p1_x2)`, Party 2 `(p2_x2, p2_x0)`. -/
structure RssActiveOpenMsg where
  p0_x0 : UInt64
  p0_x1 : UInt64
  p1_x1 : UInt64
  p1_x2 : UInt64
  p2_x2 : UInt64
  p2_x0 : UInt64
  deriving DecidableEq, Repr

/-- Cross-checks all 3 replicated share pairs before outputting `p0_x0 ^^^ p1_x1 ^^^ p2_x2`. -/
@[expose] def verifyRssActiveOpen (m : RssActiveOpenMsg) : Option UInt64 :=
  if (m.p0_x0 == m.p2_x0) && (m.p0_x1 == m.p1_x1) && (m.p1_x2 == m.p2_x2) then
    some (m.p0_x0 ^^^ m.p1_x1 ^^^ m.p2_x2)
  else
    none

/-- **`#tooth` Passive RSS Open Vulnerability (`rss_passive_open_vulnerable_to_additive_fault`)**:
    Without cross-checking replicated shares, a single corrupt Party 0 flipping `x0 ↦ x0 ^^^ Δ`
    shifts the reconstructed word by arbitrary `Δ ≠ 0`! -/
theorem rss_passive_open_vulnerable_to_additive_fault (w : RssWord64) (delta : UInt64) (hNe : delta ≠ 0) :
    reconstructRssWord { w with x0 := w.x0 ^^^ delta } ≠ reconstructRssWord w := by
  intro hEq
  unfold reconstructRssWord at hEq
  dsimp only at hEq
  have hBit : delta = 0 := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i _
    have hi := congrArg (fun u : UInt64 => u.toBitVec.getLsbD i) hEq
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor, UInt64.toBitVec_ofNat, BitVec.getLsbD_zero] at hi ⊢
    revert hi
    cases w.x0.toBitVec.getLsbD i <;> cases w.x1.toBitVec.getLsbD i <;>
      cases w.x2.toBitVec.getLsbD i <;> cases delta.toBitVec.getLsbD i <;> decide
  exact hNe hBit

/-- **Active 3-Party `FLNW17` Cross-Check Soundness (`rss_flnw_active_open_sound`)**:
    When at most 1 party `corruptIdx ∈ {0, 1, 2}` deviates (so the remaining 2 parties report their
    true `RssWord64` views), `verifyRssActiveOpen m = some out` **unconditionally forces**
    `out = reconstructRssWord trueShares` (`0` forgery probability!). -/
theorem rss_flnw_active_open_sound
    (trueShares : RssWord64) (m : RssActiveOpenMsg) (corruptIdx : Nat) (out : UInt64)
    (hHon0 : corruptIdx ≠ 0 → m.p0_x0 = trueShares.x0 ∧ m.p0_x1 = trueShares.x1)
    (hHon1 : corruptIdx ≠ 1 → m.p1_x1 = trueShares.x1 ∧ m.p1_x2 = trueShares.x2)
    (hHon2 : corruptIdx ≠ 2 → m.p2_x2 = trueShares.x2 ∧ m.p2_x0 = trueShares.x0)
    (hAccept : verifyRssActiveOpen m = some out) :
    out = reconstructRssWord trueShares := by
  unfold verifyRssActiveOpen at hAccept
  split at hAccept
  · rename_i hChecks
    simp only [Option.some.injEq] at hAccept
    rcases Bool.and_eq_true_iff.mp hChecks with ⟨h01, h2⟩
    rcases Bool.and_eq_true_iff.mp h01 with ⟨hc0, hc1⟩
    have e0 : m.p0_x0 = m.p2_x0 := eq_of_beq hc0
    have e1 : m.p0_x1 = m.p1_x1 := eq_of_beq hc1
    have e2 : m.p1_x2 = m.p2_x2 := eq_of_beq h2
    subst hAccept
    unfold reconstructRssWord
    by_cases hc : corruptIdx = 0
    · obtain ⟨h1a, _⟩ := hHon1 (by omega)
      obtain ⟨h2a, h2b⟩ := hHon2 (by omega)
      rw [e0, h2b, h1a, h2a]
    · obtain ⟨h0a, h0b⟩ := hHon0 hc
      by_cases hc' : corruptIdx = 1
      · obtain ⟨h2a, _⟩ := hHon2 (by omega)
        rw [h0a, ← e1, h0b, h2a]
      · obtain ⟨_, h1b⟩ := hHon1 hc'
        rw [h0a, ← e1, h0b, ← e2, h1b]
  · cases hAccept

/-! ## 4. Multi-Turn MAC-Before-Open Anti-DFA Trace Safety (`mac_before_open_blocks_faulted_cut_leakage`) -/

/-- Each cut carries the opening checked against the verifier's existing MAC keys. -/
structure CutCandidateOpening where
  epoch : Nat
  trueCutBytes : List UInt8
  candidateBytes : List UInt8
  opening : BdozPairOpening

structure MaliciousSignerState where
  nextEpoch : Nat
  releasedHistory : List (Nat × List UInt8)
  abortedCount : Nat
  poisoned : Bool
  deriving DecidableEq, Repr

/-- Failure poisons the session before any candidate bytes are released. -/
def stepMacBeforeOpenSignTurn (vk : BdozVerifierKeys)
    (st : MaliciousSignerState) (turn : CutCandidateOpening) : MaliciousSignerState :=
  if st.poisoned then
    { st with abortedCount := st.abortedCount + 1 }
  else if turn.epoch == st.nextEpoch && verifyBdozPairMac vk turn.opening then
    { st with nextEpoch := turn.epoch + 1
              releasedHistory := (turn.epoch, turn.candidateBytes) :: st.releasedHistory }
  else
    { st with poisoned := true, abortedCount := st.abortedCount + 1 }

def runMacBeforeOpenTrace (vk : BdozVerifierKeys) :
    MaliciousSignerState → List CutCandidateOpening → MaliciousSignerState
  | st, [] => st
  | st, t :: ts => runMacBeforeOpenTrace vk (stepMacBeforeOpenSignTurn vk st t) ts

/-- A failed concrete MAC check releases no candidate and irreversibly poisons this session. -/
theorem failed_cut_mac_rejected (vk : BdozVerifierKeys) (st : MaliciousSignerState)
    (t : CutCandidateOpening) (hFail : verifyBdozPairMac vk t.opening = false) :
    (stepMacBeforeOpenSignTurn vk st t).releasedHistory = st.releasedHistory ∧
    (stepMacBeforeOpenSignTurn vk st t).poisoned = true := by
  cases hp : st.poisoned <;> simp [stepMacBeforeOpenSignTurn, hp, hFail]

/-- Arbitrarily many later turns cannot release anything after poisoning. -/
theorem poisoned_cut_session_releases_nothing (vk : BdozVerifierKeys)
    (turns : List CutCandidateOpening) (st : MaliciousSignerState) (hp : st.poisoned = true) :
    (runMacBeforeOpenTrace vk st turns).releasedHistory = st.releasedHistory ∧
    (runMacBeforeOpenTrace vk st turns).poisoned = true := by
  induction turns generalizing st with
  | nil => exact ⟨rfl, hp⟩
  | cons t ts ih =>
    simpa [runMacBeforeOpenTrace, stepMacBeforeOpenSignTurn, hp] using
      ih { st with abortedCount := st.abortedCount + 1 } hp

private theorem released_cut_origin (vk : BdozVerifierKeys) (turns : List CutCandidateOpening)
    (st : MaliciousSignerState) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk st turns).releasedHistory,
      pair ∈ st.releasedHistory ∨ ∃ t ∈ turns,
        pair = (t.epoch, t.candidateBytes) ∧ verifyBdozPairMac vk t.opening = true := by
  induction turns generalizing st with
  | nil => intro pair h; exact .inl h
  | cons t ts ih =>
    intro pair h
    rcases ih (stepMacBeforeOpenSignTurn vk st t) pair h with hStep | ⟨u, hu, heq, hmac⟩
    · unfold stepMacBeforeOpenSignTurn at hStep
      split at hStep
      · exact .inl hStep
      · split at hStep
        next hGuard =>
          rcases List.mem_cons.mp hStep with heq | hOld
          · exact .inr ⟨t, .head _, heq, (Bool.and_eq_true_iff.mp hGuard).2⟩
          · exact .inl hOld
        next => exact .inl hStep
    · exact .inr ⟨u, .tail _ hu, heq, hmac⟩

/-- Every released value comes from an actual turn and passed the concrete MAC verifier.
Byte integrity additionally requires a binding between the authenticated shares and byte encoding. -/
theorem mac_before_open_released_origin
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        verifyBdozPairMac vk t.opening = true := by
  intro pair h
  rcases released_cut_origin vk turns ⟨initialEpoch, [], 0, false⟩ pair h with hOld | hNew
  · cases hOld
  · exact hNew

/-- With a byte/share binding, a released fault yields both MAC keys from the actual
opening deltas. The integrity disjunction is essential: a finite MAC admits key guessing. -/
theorem mac_before_open_blocks_faulted_cut_leakage
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat)
    (honestOpening : CutCandidateOpening → BdozPairOpening)
    (hHonest : ∀ t ∈ turns, verifyBdozPairMac vk (honestOpening t) = true)
    (hParty : ∀ t ∈ turns, (honestOpening t).partyId = t.opening.partyId)
    (hBind : ∀ t ∈ turns, t.candidateBytes ≠ t.trueCutBytes →
      (honestOpening t).shareX ≠ t.opening.shareX) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        verifyBdozPairMac vk t.opening = true ∧
        (t.candidateBytes = t.trueCutBytes ∨
          let dxInv := towerInv 7 (towerAdd 7 t.opening.shareX (honestOpening t).shareX)
          towerMul 7 (towerAdd 7 t.opening.mac0 (honestOpening t).mac0) dxInv = vk.alpha0 ∧
          towerMul 7 (towerAdd 7 t.opening.mac1 (honestOpening t).mac1) dxInv = vk.alpha1) := by
  intro pair h
  obtain ⟨t, ht, heq, hMac⟩ := mac_before_open_released_origin vk turns initialEpoch pair h
  refine ⟨t, ht, heq, hMac, ?_⟩
  by_cases hEq : t.candidateBytes = t.trueCutBytes
  · exact .inl hEq
  · exact .inr (bdoz_pair_key_recovery vk (honestOpening t) t.opening
      (hParty t ht) (hBind t ht hEq) (hHonest t ht) hMac)

/-- A concrete corrupted opening fails verification and releases nothing. -/
theorem open_before_mac_leaks_faulted_cut :
    let vk : BdozVerifierKeys := ⟨towerOne 7, towerOne 7, fun _ => (towerZero 7, towerZero 7)⟩
    let t : CutCandidateOpening := ⟨0, [0], [1], ⟨0, towerZero 7, towerOne 7, towerZero 7⟩⟩
    verifyBdozPairMac vk t.opening = false ∧
    (stepMacBeforeOpenSignTurn vk ⟨0, [], 0, false⟩ t).releasedHistory = [] ∧
    (stepMacBeforeOpenSignTurn vk ⟨0, [], 0, false⟩ t).poisoned = true := by
  decide +kernel

/-! ### 4b. Canonical 16-Byte `Tower128` Cut-Share Encoding & Hypothesis-Free Binding (`C1-3`) -/

/-- Canonical big-endian 16-byte wire encoding of a 128-bit `Tower128` cut share. -/
def encodeCutShareBytes (x : Tower128) : List UInt8 :=
  be 16 (packTower 7 x).toNat

theorem encodeCutShareBytes_length (x : Tower128) :
    (encodeCutShareBytes x).length = 16 :=
  length_be 16 (packTower 7 x).toNat

/-- **Canonical Cut-Share Byte Injectivity (`encodeCutShareBytes_injective`)**:
    Distinct `Tower128` shares NEVER collide under `encodeCutShareBytes`, eliminating any external
    `hBind` assumption between `candidateBytes` and `opening.shareX`. -/
theorem encodeCutShareBytes_injective {x y : Tower128}
    (h : encodeCutShareBytes x = encodeCutShareBytes y) : x = y := by
  unfold encodeCutShareBytes at h
  have hPow : (2 : Nat) ^ (2 ^ 7) = 256 ^ 16 := by decide
  have hxLt : (packTower 7 x).toNat < 256 ^ 16 := hPow ▸ (packTower 7 x).isLt
  have hyLt : (packTower 7 y).toNat < 256 ^ 16 := hPow ▸ (packTower 7 y).isLt
  have hNat : (packTower 7 x).toNat = (packTower 7 y).toNat := be_injective hxLt hyLt h
  exact packTower_injective 7 x y (BitVec.eq_of_toNat_eq hNat)

/-- Construct a `CutCandidateOpening` whose byte payloads are canonically derived from shares. -/
def mkCanonicalCutCandidateOpening
    (epoch : Nat) (honestShareX : Tower128) (opening : BdozPairOpening) : CutCandidateOpening :=
  { epoch := epoch
    trueCutBytes := encodeCutShareBytes honestShareX
    candidateBytes := encodeCutShareBytes opening.shareX
    opening := opening }

/-- Predicate stating that `t`'s wire bytes are canonically encoded from `t.opening.shareX`
    and `honestOp.shareX` via `encodeCutShareBytes`. -/
def CutCandidateOpening.CanonicallyBound
    (t : CutCandidateOpening) (honestOp : BdozPairOpening) : Prop :=
  t.candidateBytes = encodeCutShareBytes t.opening.shareX ∧
  t.trueCutBytes = encodeCutShareBytes honestOp.shareX

/-- **Hypothesis-Free Canonical MAC-Before-Open Soundness (`mac_before_open_canonical_bytes_sound`)**:
    When `CutCandidateOpening`s satisfy `CanonicallyBound` (e.g. built by `mkCanonicalCutCandidateOpening`),
    byte-to-share binding `candidateBytes ≠ trueCutBytes → honestOpening.shareX ≠ opening.shareX` is
    discharged **internally** from `encodeCutShareBytes_injective` with zero external `hBind` hypothesis! -/
theorem mac_before_open_canonical_bytes_sound
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat)
    (honestOpening : CutCandidateOpening → BdozPairOpening)
    (hHonest : ∀ t ∈ turns, verifyBdozPairMac vk (honestOpening t) = true)
    (hParty : ∀ t ∈ turns, (honestOpening t).partyId = t.opening.partyId)
    (hCanon : ∀ t ∈ turns, t.CanonicallyBound (honestOpening t)) :
    ∀ pair ∈ (runMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        verifyBdozPairMac vk t.opening = true ∧
        (t.candidateBytes = t.trueCutBytes ∨
          let dxInv := towerInv 7 (towerAdd 7 t.opening.shareX (honestOpening t).shareX)
          towerMul 7 (towerAdd 7 t.opening.mac0 (honestOpening t).mac0) dxInv = vk.alpha0 ∧
          towerMul 7 (towerAdd 7 t.opening.mac1 (honestOpening t).mac1) dxInv = vk.alpha1) := by
  apply mac_before_open_blocks_faulted_cut_leakage vk turns initialEpoch honestOpening hHonest hParty
  intro t ht hBytesNe hShareEq
  obtain ⟨hCand, hTrue⟩ := hCanon t ht
  exact hBytesNe (hCand.trans ((congrArg encodeCutShareBytes hShareEq.symm).trans hTrue.symm))

/-- Wire-enforced canonical MAC-before-open transition: explicitly checks BOTH
    `turn.candidateBytes == encodeCutShareBytes turn.opening.shareX` AND `verifyBdozPairMac`
    before releasing `turn.candidateBytes`, poisoning the session on any byte/share mismatch! -/
def stepCanonicalMacBeforeOpenSignTurn (vk : BdozVerifierKeys)
    (st : MaliciousSignerState) (turn : CutCandidateOpening) : MaliciousSignerState :=
  if st.poisoned then
    { st with abortedCount := st.abortedCount + 1 }
  else if (turn.epoch == st.nextEpoch) &&
          (turn.candidateBytes == encodeCutShareBytes turn.opening.shareX) &&
          verifyBdozPairMac vk turn.opening then
    { st with nextEpoch := turn.epoch + 1
              releasedHistory := (turn.epoch, turn.candidateBytes) :: st.releasedHistory }
  else
    { st with poisoned := true, abortedCount := st.abortedCount + 1 }

def runCanonicalMacBeforeOpenTrace (vk : BdozVerifierKeys) :
    MaliciousSignerState → List CutCandidateOpening → MaliciousSignerState
  | st, [] => st
  | st, t :: ts => runCanonicalMacBeforeOpenTrace vk (stepCanonicalMacBeforeOpenSignTurn vk st t) ts

private theorem released_canonical_cut_origin (vk : BdozVerifierKeys) (turns : List CutCandidateOpening)
    (st : MaliciousSignerState) :
    ∀ pair ∈ (runCanonicalMacBeforeOpenTrace vk st turns).releasedHistory,
      pair ∈ st.releasedHistory ∨ ∃ t ∈ turns,
        pair = (t.epoch, t.candidateBytes) ∧
        t.candidateBytes = encodeCutShareBytes t.opening.shareX ∧
        verifyBdozPairMac vk t.opening = true := by
  induction turns generalizing st with
  | nil => intro pair h; exact .inl h
  | cons t ts ih =>
    intro pair h
    rcases ih (stepCanonicalMacBeforeOpenSignTurn vk st t) pair h with hStep | ⟨u, hu, heq, hcb, hmac⟩
    · unfold stepCanonicalMacBeforeOpenSignTurn at hStep
      split at hStep
      · exact .inl hStep
      · split at hStep
        next hGuard =>
          rcases Bool.and_eq_true_iff.mp hGuard with ⟨hLeft, hMac⟩
          rcases Bool.and_eq_true_iff.mp hLeft with ⟨_, hCandB⟩
          rcases List.mem_cons.mp hStep with heq | hOld
          · exact .inr ⟨t, .head _, heq, eq_of_beq hCandB, hMac⟩
          · exact .inl hOld
        next => exact .inl hStep
    · exact .inr ⟨u, .tail _ hu, heq, hcb, hmac⟩

/-- **Wire-Enforced Canonical MAC-Before-Open Multi-Turn Safety
    (`canonical_mac_before_open_blocks_faulted_cut_leakage`)**:
    Even against arbitrary untrusted wire `CutCandidateOpening`s (with zero `CanonicallyBound` or
    `hBind` assumption on `t.candidateBytes`!), `runCanonicalMacBeforeOpenTrace` guarantees every
    released `(epoch, bytes)` equals `encodeCutShareBytes (honestOpening t).shareX` or pins both
    128-bit BDOZ keys `(vk.alpha0, vk.alpha1)`. -/
theorem canonical_mac_before_open_blocks_faulted_cut_leakage
    (vk : BdozVerifierKeys) (turns : List CutCandidateOpening) (initialEpoch : Nat)
    (honestOpening : CutCandidateOpening → BdozPairOpening)
    (hHonest : ∀ t ∈ turns, verifyBdozPairMac vk (honestOpening t) = true)
    (hParty : ∀ t ∈ turns, (honestOpening t).partyId = t.opening.partyId) :
    ∀ pair ∈ (runCanonicalMacBeforeOpenTrace vk ⟨initialEpoch, [], 0, false⟩ turns).releasedHistory,
      ∃ t ∈ turns, pair = (t.epoch, t.candidateBytes) ∧
        t.candidateBytes = encodeCutShareBytes t.opening.shareX ∧
        verifyBdozPairMac vk t.opening = true ∧
        (t.candidateBytes = encodeCutShareBytes (honestOpening t).shareX ∨
          let dxInv := towerInv 7 (towerAdd 7 t.opening.shareX (honestOpening t).shareX)
          towerMul 7 (towerAdd 7 t.opening.mac0 (honestOpening t).mac0) dxInv = vk.alpha0 ∧
          towerMul 7 (towerAdd 7 t.opening.mac1 (honestOpening t).mac1) dxInv = vk.alpha1) := by
  intro pair h
  rcases released_canonical_cut_origin vk turns ⟨initialEpoch, [], 0, false⟩ pair h with hOld | ⟨t, ht, heq, hcb, hMac⟩
  · cases hOld
  · refine ⟨t, ht, heq, hcb, hMac, ?_⟩
    cases hEqB : (t.candidateBytes == encodeCutShareBytes (honestOpening t).shareX) with
    | true => exact .inl (eq_of_beq hEqB)
    | false =>
      have hShareNe : (honestOpening t).shareX ≠ t.opening.shareX := by
        intro hSame
        have hEq : t.candidateBytes = encodeCutShareBytes (honestOpening t).shareX :=
          hcb.trans (congrArg encodeCutShareBytes hSame.symm)
        rw [hEq, beq_self_eq_true] at hEqB
        cases hEqB
      exact .inr (bdoz_pair_key_recovery vk (honestOpening t) t.opening
        (hParty t ht) hShareNe (hHonest t ht) hMac)

private theorem bdozHonestOpening_verifies (vk : BdozVerifierKeys) (j : Nat) (x : Tower128) :
    verifyBdozPairMac vk (bdozHonestOpening vk j x) = true := by
  simp [verifyBdozPairMac, bdozHonestOpening]

private theorem stepCanonical_rejects_mismatched (vk : BdozVerifierKeys)
    (ep : Nat) (trueB candB : List UInt8) (op : BdozPairOpening)
    (hMismatch : candB ≠ encodeCutShareBytes op.shareX) :
    stepCanonicalMacBeforeOpenSignTurn vk ⟨ep, [], 0, false⟩ ⟨ep, trueB, candB, op⟩ =
      ⟨ep, [], 1, true⟩ := by
  have hBeqF : (candB == encodeCutShareBytes op.shareX) = false := beq_false_of_ne hMismatch
  unfold stepCanonicalMacBeforeOpenSignTurn
  dsimp only
  rw [beq_self_eq_true ep, hBeqF]
  rfl

private theorem stepCanonical_accepts_canonical (vk : BdozVerifierKeys)
    (ep : Nat) (honX : Tower128) (op : BdozPairOpening)
    (hMac : verifyBdozPairMac vk op = true) :
    stepCanonicalMacBeforeOpenSignTurn vk ⟨ep, [], 0, false⟩
        (mkCanonicalCutCandidateOpening ep honX op) =
      ⟨ep + 1, [(ep, encodeCutShareBytes op.shareX)], 0, false⟩ := by
  unfold stepCanonicalMacBeforeOpenSignTurn mkCanonicalCutCandidateOpening
  dsimp only
  rw [beq_self_eq_true ep, beq_self_eq_true (encodeCutShareBytes op.shareX), hMac]
  rfl

/-- **`#tooth` Mismatched `candidateBytes` Rejected Even Under Valid BDOZ MAC
    (`tooth_canonical_cut_rejects_mismatched_bytes`)**:
    If an adversary submits a valid `BdozPairOpening` (`verifyBdozPairMac = true`) while substituting
    mismatched `candidateBytes ≠ encodeCutShareBytes opening.shareX`, `stepCanonicalMacBeforeOpenSignTurn`
    releases nothing and irreversibly poisons the session, whereas honest canonical bytes are released! -/
theorem tooth_canonical_cut_rejects_mismatched_bytes :
    let vk : BdozVerifierKeys := ⟨towerOne 7, towerOne 7, fun _ => (towerZero 7, towerZero 7)⟩
    let honOp := bdozHonestOpening vk 0 (towerOne 7)
    let badTurn : CutCandidateOpening :=
      ⟨0, encodeCutShareBytes (towerOne 7), encodeCutShareBytes (towerZero 7), honOp⟩
    let goodTurn := mkCanonicalCutCandidateOpening 0 (towerOne 7) honOp
    verifyBdozPairMac vk badTurn.opening = true ∧
    (stepCanonicalMacBeforeOpenSignTurn vk ⟨0, [], 0, false⟩ badTurn).releasedHistory = [] ∧
    (stepCanonicalMacBeforeOpenSignTurn vk ⟨0, [], 0, false⟩ badTurn).poisoned = true ∧
    (stepCanonicalMacBeforeOpenSignTurn vk ⟨0, [], 0, false⟩ goodTurn).releasedHistory =
      [(0, encodeCutShareBytes (towerOne 7))] := by
  intro vk honOp badTurn goodTurn
  have hMac : verifyBdozPairMac vk honOp = true := bdozHonestOpening_verifies vk 0 (towerOne 7)
  have hMismatch : encodeCutShareBytes (towerZero 7) ≠ encodeCutShareBytes (towerOne 7) :=
    fun h => towerOne_ne_zero 7 (encodeCutShareBytes_injective h).symm
  have hBad := stepCanonical_rejects_mismatched vk 0 (encodeCutShareBytes (towerOne 7))
    (encodeCutShareBytes (towerZero 7)) honOp hMismatch
  have hGood := stepCanonical_accepts_canonical vk 0 (towerOne 7) honOp hMac
  have hShare : honOp.shareX = towerOne 7 := rfl
  refine ⟨hMac, ?_, ?_, ?_⟩
  · dsimp only [badTurn]; rw [hBad]
  · dsimp only [badTurn]; rw [hBad]
  · dsimp only [goodTurn]; rw [hGood, hShare]

/-! ## 5. Dynamic `(t, n) → (t', n')` Quorum Resharing `Π_reshare` & Proactive Refresh -/

/-- Pointwise addition of two polynomial coefficient lists (`(f + g)(X)`). -/
def addPolyCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], gs => gs
  | fs, [] => fs
  | f :: fs, g :: gs => CommRingOps.add f g :: addPolyCoeffs fs gs

theorem addPolyCoeffs_length {R : Type} [CommRingOps R] :
    ∀ (fs gs : List R), (addPolyCoeffs fs gs).length = Nat.max fs.length gs.length
  | [], gs => by simp [addPolyCoeffs]
  | f :: fs, [] => by simp [addPolyCoeffs]
  | f :: fs, g :: gs => by
    simp only [addPolyCoeffs, List.length_cons, addPolyCoeffs_length fs gs, Nat.succ_max_succ]

theorem evalCoeffs_addPolyCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (fs gs : List R) (x : R),
      RoundPoly.evalCoeffs (addPolyCoeffs fs gs) x =
        CommRingOps.add (RoundPoly.evalCoeffs fs x) (RoundPoly.evalCoeffs gs x)
  | [], gs, x => by simp [addPolyCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | f :: fs, [], x => by simp [addPolyCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | f :: fs, g :: gs, x => by
    simp only [addPolyCoeffs, RoundPoly.evalCoeffs, evalCoeffs_addPolyCoeffs fs gs x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

/-- Sum of sub-polynomials $\sum_{i \in Q_{\text{old}}} g_i(X)$ dealt during `(t, n) → (t', n')` resharing. -/
def sumSubPolys {R : Type} [CommRingOps R] : List (List R) → List R
  | [] => []
  | p :: ps => addPolyCoeffs p (sumSubPolys ps)

theorem sumSubPolys_length_le {R : Type} [CommRingOps R] (tPrime : Nat) :
    ∀ (polys : List (List R)),
      (∀ p ∈ polys, p.length ≤ tPrime) →
      (sumSubPolys polys).length ≤ tPrime
  | [], _ => Nat.zero_le tPrime
  | p :: ps, hAll => by
    simp only [sumSubPolys, addPolyCoeffs_length]
    exact Nat.max_le.mpr ⟨hAll p (.head _),
      sumSubPolys_length_le tPrime ps (fun q hq => hAll q (.tail _ hq))⟩

theorem evalCoeffs_sumSubPolys {R : Type} [LawfulCommRing R] (x : R) :
    ∀ (polys : List (List R)),
      RoundPoly.evalCoeffs (sumSubPolys polys) x =
        (polys.map (fun p => RoundPoly.evalCoeffs p x)).foldr CommRingOps.add CommRingOps.zero
  | [] => rfl
  | p :: ps => by
    simp only [sumSubPolys, List.map_cons, List.foldr_cons,
      evalCoeffs_addPolyCoeffs, evalCoeffs_sumSubPolys x ps]

/-- **Dynamic `(t, n) → (t', n')` Quorum Resharing Soundness
    (`reshare_preserves_public_key_and_refreshes_degree`)**:
    When old quorum members deal sub-polynomials `subPolys` of formal length $\le t'$ whose constant
    terms sum to the original secret `skScalar` (including `Π_refresh` where old shares add degree-$< t$
    zero-constant polynomials), the combined polynomial `G = sumSubPolys subPolys`:
    1. Has formal degree $< t'$ (`G.length ≤ t'`),
    2. Evaluates at `0` to the **exact same secret** `skScalar`,
    3. Gives every new committee member $\alpha'_p$ the exact share $\sum_i g_i(\alpha'_p)$, and
    4. Preserves `derivePublicKey suite params sk` identically across committee rotation! -/
theorem reshare_preserves_public_key_and_refreshes_degree
    {R : Type} [LawfulCommRing R]
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (encodeSecret : R → List UInt8)
    (skScalar : R) (hSkSeed : sk.skSeed = encodeSecret skScalar)
    (tPrime : Nat) (subPolys : List (List R))
    (hDeg : ∀ p ∈ subPolys, p.length ≤ tPrime)
    (hConstSum : (subPolys.map (fun p => RoundPoly.evalCoeffs p CommRingOps.zero)).foldr
                   CommRingOps.add CommRingOps.zero = skScalar) :
    let G := sumSubPolys subPolys
    let skAfter : PqSecretKey := { sk with skSeed := encodeSecret (RoundPoly.evalCoeffs G CommRingOps.zero) }
    G.length ≤ tPrime ∧
    RoundPoly.evalCoeffs G CommRingOps.zero = skScalar ∧
    (∀ alphaNew : R,
      RoundPoly.evalCoeffs G alphaNew =
        (subPolys.map (fun p => RoundPoly.evalCoeffs p alphaNew)).foldr CommRingOps.add CommRingOps.zero) ∧
    derivePublicKey suite params skAfter = derivePublicKey suite params sk := by
  have hZero : RoundPoly.evalCoeffs (sumSubPolys subPolys) CommRingOps.zero = skScalar := by
    rw [evalCoeffs_sumSubPolys CommRingOps.zero subPolys, hConstSum]
  refine ⟨sumSubPolys_length_le tPrime subPolys hDeg, hZero,
          fun alphaNew => evalCoeffs_sumSubPolys alphaNew subPolys, ?_⟩
  have hSkEq : ({ sk with skSeed := encodeSecret (RoundPoly.evalCoeffs (sumSubPolys subPolys) CommRingOps.zero) } : PqSecretKey) = sk := by
    cases sk
    dsimp only at hSkSeed ⊢
    rw [hZero, ← hSkSeed]
  rw [hSkEq]

/-! ### 5b. Cleartext-Free Share-to-Share Resharing, Old-Share Zeroization & `(t' - 1)` View Bijection (`C1-3`) -/

/-- Each old quorum party `i` deals $g_i(X) = (\lambda_i \cdot s_i) + \sum_{k=1}^{t'-1} r_{i,k} X^k$
    directly from its local share `s_i` and Lagrange weight `λ_i` — `sk` is NEVER reconstructed! -/
def dealReshareSubPolys {R : Type} [CommRingOps R] :
    List R → List R → List (List R) → List (List R)
  | l :: ls, s :: ss, tl :: tls =>
    (CommRingOps.mul l s :: tl) :: dealReshareSubPolys ls ss tls
  | _, _, _ => []

/-- Post-reshare old-committee state explicitly zeroizing the retired share (`heldShare := none`)
    immediately after transmitting sub-shares to the new committee. -/
structure OldPartyReshareView (R : Type) where
  partyIdx  : Nat
  heldShare : Option R
  deriving DecidableEq, Repr

def eraseOldShareAfterReshare {R : Type} (v : OldPartyReshareView R) : OldPartyReshareView R :=
  { v with heldShare := none }

theorem eraseOldShareAfterReshare_wipes {R : Type} (v : OldPartyReshareView R) :
    (eraseOldShareAfterReshare v).heldShare = none := by
  rfl

private theorem dealReshareSubPolys_deg {R : Type} [CommRingOps R] (tPrime : Nat) :
    ∀ (ls ss : List R) (tls : List (List R)),
      (∀ tl ∈ tls, tl.length + 1 ≤ tPrime) →
      ∀ p ∈ dealReshareSubPolys ls ss tls, p.length ≤ tPrime
  | l :: ls, s :: ss, tl :: tls, hTls, p, hp => by
    simp only [dealReshareSubPolys, List.mem_cons] at hp
    rcases hp with rfl | hRest
    · simp only [List.length_cons]
      exact hTls tl (.head _)
    · exact dealReshareSubPolys_deg tPrime ls ss tls (fun q hq => hTls q (.tail _ hq)) p hRest
  | [], _, _, _, _, hp => by cases hp
  | _ :: _, [], _, _, _, hp => by cases hp
  | _ :: _, _ :: _, [], _, _, hp => by cases hp

private theorem dealReshareSubPolys_constSum {R : Type} [LawfulCommRing R] :
    ∀ (ls ss : List R) (tls : List (List R)),
      ss.length = ls.length →
      tls.length = ls.length →
      ((dealReshareSubPolys ls ss tls).map (fun p => RoundPoly.evalCoeffs p CommRingOps.zero)).foldr
        CommRingOps.add CommRingOps.zero = ringDot ls ss
  | [], [], [], _, _ => rfl
  | l :: ls, s :: ss, tl :: tls, hSLen, hTLen => by
    simp only [dealReshareSubPolys, List.map_cons, List.foldr_cons, RoundPoly.evalCoeffs,
      LawfulCommRing.zero_mul, LawfulCommRing.add_zero, ringDot,
      dealReshareSubPolys_constSum ls ss tls (Nat.succ.inj hSLen) (Nat.succ.inj hTLen)]

/-- **Cleartext-Free Share-to-Share `(t, n) → (t', n')` Resharing Soundness
    (`reshare_from_shares_without_cleartext_recombines_secret`)**:
    Old quorum shares `(oldLambdas, oldShares)` reshared via `dealReshareSubPolys` (with zero
    cleartext `sk` materialization!) produce new committee shares at `Q_new : ShamirQuorum R t'`
    whose Lagrange recombination equals `lagrangeCombine oldLambdas oldShares` identically! -/
theorem reshare_from_shares_without_cleartext_recombines_secret
    {R : Type} [LawfulCommRing R]
    (oldLambdas oldShares : List R) (randomTails : List (List R))
    (tPrime : Nat) (Q_new : ShamirQuorum R tPrime)
    (hSLen : oldShares.length = oldLambdas.length)
    (hTLen : randomTails.length = oldLambdas.length)
    (hTailDeg : ∀ tl ∈ randomTails, tl.length + 1 ≤ tPrime) :
    let subPolys := dealReshareSubPolys oldLambdas oldShares randomTails
    let G := sumSubPolys subPolys
    let newQuorumShares := Q_new.pts.map (fun x' =>
      (subPolys.map (fun p => RoundPoly.evalCoeffs p x')).foldr CommRingOps.add CommRingOps.zero)
    G.length ≤ tPrime ∧
    RoundPoly.evalCoeffs G CommRingOps.zero = lagrangeCombine oldLambdas oldShares ∧
    lagrangeCombine Q_new.lambdas newQuorumShares = lagrangeCombine oldLambdas oldShares := by
  intro subPolys G newQuorumShares
  have hDeg : ∀ p ∈ subPolys, p.length ≤ tPrime :=
    dealReshareSubPolys_deg tPrime oldLambdas oldShares randomTails hTailDeg
  have hGLen : G.length ≤ tPrime := sumSubPolys_length_le tPrime subPolys hDeg
  have hG0 : RoundPoly.evalCoeffs G CommRingOps.zero = lagrangeCombine oldLambdas oldShares := by
    dsimp only [G]
    rw [evalCoeffs_sumSubPolys CommRingOps.zero subPolys,
        dealReshareSubPolys_constSum oldLambdas oldShares randomTails hSLen hTLen]
    rfl
  have hNewEq : newQuorumShares = Q_new.pts.map (fun x' => RoundPoly.evalCoeffs G x') := by
    apply List.map_congr_left
    intro x' _
    exact (evalCoeffs_sumSubPolys x' subPolys).symm
  refine ⟨hGLen, hG0, ?_⟩
  unfold lagrangeCombine
  rw [hNewEq, lagrangeAtZero_evalCoeffs Q_new.lambdas Q_new.pts G tPrime hGLen Q_new.sum_one Q_new.kills_higher]
  exact hG0

/-- **`(t' - 1)` Corrupt New-Committee Reshare View Bijection (`reshare_corrupt_view_bijection`)**:
    For ANY `< t'` corrupt new-committee points `corruptNewPts` (`corruptNewPts.length + 1 ≤ t'`,
    `∀ c ∈ corruptNewPts, c ≠ 0`) and ANY two weighted honest old shares `w₁, w₂ : R`,
    `shamir_rebalanceEquiv` gives an explicit `SimpleEquiv` bijection on degree-`< t'` honest
    sub-polynomials shifting the constant term from `w₁` to `w₂` while keeping every corrupt new
    member's received sub-share **identical** (`RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc`)! -/
theorem reshare_corrupt_view_bijection
    {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ CommRingOps.zero → CommRingOps.mul x (inv x) = CommRingOps.one)
    (tPrime : Nat) (corruptNewPts : List R) (w₁ w₂ : R)
    (hCard : corruptNewPts.length + 1 ≤ tPrime)
    (hNonZero : ∀ c ∈ corruptNewPts, c ≠ CommRingOps.zero)
    (P : ShamirPadPoly R tPrime)
    (hConst₁ : RoundPoly.evalCoeffs P.1 CommRingOps.zero = w₁) :
    let eqv := shamir_rebalanceEquiv inv tPrime corruptNewPts (CommRingOps.sub w₂ w₁) hCard
    let Q := eqv.toFun P
    eqv.invFun Q = P ∧
    RoundPoly.evalCoeffs Q.1 CommRingOps.zero = w₂ ∧
    (∀ xc ∈ corruptNewPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc) := by
  intro eqv Q
  obtain ⟨hAt0, hCorr⟩ := pad_bijection_masked_openings_uniform
    inv hInv tPrime corruptNewPts (CommRingOps.sub w₂ w₁) hCard hNonZero P
  have hQ0 : RoundPoly.evalCoeffs Q.1 CommRingOps.zero = w₂ := by
    rw [← LawfulCommRing.zero_add (RoundPoly.evalCoeffs Q.1 CommRingOps.zero)]
    dsimp only [Q, eqv]
    rw [hAt0, hConst₁, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
        LawfulCommRing.add_left_neg, LawfulCommRing.add_zero]
  exact ⟨eqv.left_inv P, hQ0, hCorr⟩

/-- **`#tooth` Tightness at Full `t'` Collusion (`tooth_reshare_full_tPrime_collusion_distinguishes`)**:
    If an adversary corrupts `t'` distinct new-committee members (`corruptNewPts.length = t'`),
    no two sub-polynomials with distinct weighted shares `w₁ ≠ w₂` can produce identical views! -/
theorem tooth_reshare_full_tPrime_collusion_distinguishes
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R]
    (tPrime : Nat) (corruptNewPts : List R)
    (hFull : corruptNewPts.length = tPrime) (hNodup : corruptNewPts.Nodup)
    (P Q : ShamirPadPoly R tPrime)
    (hDistinct : RoundPoly.evalCoeffs P.1 CommRingOps.zero ≠ RoundPoly.evalCoeffs Q.1 CommRingOps.zero) :
    ¬ (∀ xc ∈ corruptNewPts, RoundPoly.evalCoeffs P.1 xc = RoundPoly.evalCoeffs Q.1 xc) := by
  intro hSame
  have hNe := full_collusion_breaks_hiding tPrime corruptNewPts hFull hNodup
    (RoundPoly.evalCoeffs Q.1 CommRingOps.zero) (RoundPoly.evalCoeffs P.1 CommRingOps.zero)
    hDistinct.symm P Q hSame
  rw [LawfulCommRing.add_comm (RoundPoly.evalCoeffs Q.1 CommRingOps.zero) (RoundPoly.evalCoeffs P.1 CommRingOps.zero)] at hNe
  exact hNe rfl

/-- Concrete `(2, 3) → (2, 4)` `Goldilocks` share-to-share reshare witness: old quorum `{1, 2}`
    reshares secret `5` (`oldShares = [12, 19]`) to new quorum `{2, 3}` without reconstructing `5`. -/
theorem reshare_from_shares_inhabited :
    let oldShares := [Goldilocks.ofNat 12, Goldilocks.ofNat 19]
    let tails := [[Goldilocks.ofNat 31], [Goldilocks.ofNat 47]]
    let subPolys := dealReshareSubPolys shamirGoldilocksQuorum12.lambdas oldShares tails
    let newSharesAt23 := shamirGoldilocksQuorum23.pts.map (fun x' =>
      (subPolys.map (fun p => RoundPoly.evalCoeffs p x')).foldr CommRingOps.add CommRingOps.zero)
    oldShares ≠ newSharesAt23 ∧
    lagrangeCombine shamirGoldilocksQuorum23.lambdas newSharesAt23 = Goldilocks.ofNat 5 ∧
    (eraseOldShareAfterReshare ⟨1, some (Goldilocks.ofNat 12)⟩).heldShare = none := by
  refine ⟨by decide +kernel, by decide +kernel, rfl⟩

/-! ## 6. Constructive Simplex Quorum Intersection & `Jorts` Non-Equivocation -/

private theorem filter_partition_length {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.length = (xs.filter p).length + (xs.filter (fun x => !p x)).length
  | [] => rfl
  | x :: xs => by
    simp only [List.filter]
    cases p x <;> simp only [Bool.not_true, Bool.not_false, List.length_cons, filter_partition_length p xs] <;> omega

private theorem mem_filter_iff_local {α : Type} (p : α → Bool) (x : α) :
    ∀ (xs : List α), x ∈ xs.filter p ↔ x ∈ xs ∧ p x = true
  | [] => by simp
  | y :: ys => by
    simp only [List.filter]
    cases hp : p y
    · simp only [mem_filter_iff_local p x ys, List.mem_cons]
      constructor
      · exact fun ⟨hm, hpx⟩ => ⟨Or.inr hm, hpx⟩
      · rintro ⟨rfl | hm, hpx⟩
        · rw [hp] at hpx; cases hpx
        · exact ⟨hm, hpx⟩
    · simp only [List.mem_cons, mem_filter_iff_local p x ys]
      constructor
      · rintro (rfl | ⟨hm, hpx⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr hm, hpx⟩
      · rintro ⟨rfl | hm, hpx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hpx⟩

private theorem nodup_filter_bool {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.Nodup → (xs.filter p).Nodup
  | [], _ => .nil
  | _ :: tl, .cons hNot hTl => by
    simp only [List.filter]
    cases p _
    · exact nodup_filter_bool p hTl
    · exact .cons (fun b hb => hNot b ((mem_filter_iff_local p b tl).mp hb).1) (nodup_filter_bool p hTl)

private theorem filter_eq_pos_of_mem {α : Type} [DecidableEq α] (x : α) :
    ∀ (v : List α), x ∈ v → 1 ≤ (v.filter (fun y => decide (y = x))).length
  | [], h => by cases h
  | y :: ys, h => by
    simp only [List.filter]
    by_cases hyx : y = x
    · simp [hyx]
    · simp only [hyx, decide_false]
      rcases List.mem_cons.mp h with rfl | hTail
      · exact False.elim (hyx rfl)
      · exact filter_eq_pos_of_mem x ys hTail

private theorem nodup_subset_length_le {α : Type} [DecidableEq α] :
    ∀ (xs v : List α),
      xs.Nodup →
      (∀ x ∈ xs, x ∈ v) →
      xs.length ≤ v.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, v, .cons hxNot hNdXs, hSub => by
    let pEq : α → Bool := fun y => decide (y = x)
    have hPart := filter_partition_length pEq v
    have hPos : 1 ≤ (v.filter pEq).length := filter_eq_pos_of_mem x v (hSub x (.head _))
    have hSubRest : ∀ y ∈ xs, y ∈ v.filter (fun y => !pEq y) := by
      intro y hy
      apply (mem_filter_iff_local (fun y => !pEq y) y v).mpr
      refine ⟨hSub y (.tail _ hy), ?_⟩
      have hNe : y ≠ x := fun hEq => hxNot y hy hEq.symm
      simp [pEq, hNe]
    have ih := nodup_subset_length_le xs (v.filter (fun y => !pEq y)) hNdXs hSubRest
    simp only [List.length_cons]
    omega

private theorem nodup_append_disjoint {α : Type} :
    ∀ {xs ys : List α},
      xs.Nodup → ys.Nodup → (∀ x ∈ xs, x ∉ ys) → (xs ++ ys).Nodup
  | [], ys, _, hys, _ => hys
  | x :: xs, ys, .cons hxXs hNdXs, hys, hDisj => by
    simp only [List.cons_append]
    refine .cons ?_ (nodup_append_disjoint hNdXs hys (fun z hz => hDisj z (.tail _ hz)))
    intro b hb
    rcases List.mem_append.mp hb with hbX | hbY
    · exact hxXs b hbX
    · exact fun hEq => hDisj x (.head _) (hEq ▸ hbY)

/-- **Constructive Byzantine Quorum Intersection (`extractHonestQuorumIntersection`)**:
    Given validator set `V` of size $3f + 1$, two duplicate-free quorums `Q₁, Q₂ ⊆ V` of size
    $\ge 2f + 1$, and any Byzantine subset `corrupt` of size $\le f$, constructively (`0 Classical`)
    extracts an **honest validator** `h ∈ Q₁ ∩ Q₂ \ corrupt`! -/
def extractHonestQuorumIntersection {PartyId : Type} [DecidableEq PartyId]
    (f : Nat) (V Q₁ Q₂ corrupt : List PartyId)
    (_hVNodup : V.Nodup) (hVLen : V.length ≤ 3 * f + 1)
    (hQ1Nd : Q₁.Nodup) (hQ1Sub : ∀ x ∈ Q₁, x ∈ V) (hQ1Len : 2 * f + 1 ≤ Q₁.length)
    (hQ2Nd : Q₂.Nodup) (hQ2Sub : ∀ x ∈ Q₂, x ∈ V) (hQ2Len : 2 * f + 1 ≤ Q₂.length)
    (hCorruptLen : corrupt.length ≤ f) :
    PSigma (fun h : PartyId => h ∈ Q₁ ∧ h ∈ Q₂ ∧ h ∉ corrupt) :=
  let inQ2 : PartyId → Bool := fun x => decide (x ∈ Q₂)
  let inter := Q₁.filter inQ2
  let diff1 := Q₁.filter (fun x => !inQ2 x)
  have hQ1Part : Q₁.length = inter.length + diff1.length := filter_partition_length inQ2 Q₁
  have hUnionNd : (diff1 ++ Q₂).Nodup := by
    refine nodup_append_disjoint (nodup_filter_bool _ hQ1Nd) hQ2Nd ?_
    intro x hx hIn2
    have hxP := ((mem_filter_iff_local (fun x => !inQ2 x) x Q₁).mp hx).2
    simp [inQ2, hIn2] at hxP
  have hUnionSub : ∀ x ∈ diff1 ++ Q₂, x ∈ V := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hQ1Sub x ((mem_filter_iff_local (fun x => !inQ2 x) x Q₁).mp hx1).1
    · exact hQ2Sub x hx2
  have hUnionLe : (diff1 ++ Q₂).length ≤ V.length := nodup_subset_length_le _ V hUnionNd hUnionSub
  have hInterGe : f + 1 ≤ inter.length := by
    rw [List.length_append] at hUnionLe
    omega
  let isCorrupt : PartyId → Bool := fun x => decide (x ∈ corrupt)
  let interBad := inter.filter isCorrupt
  let interHon := inter.filter (fun x => !isCorrupt x)
  have hInterPart : inter.length = interBad.length + interHon.length :=
    filter_partition_length isCorrupt inter
  have hInterNd : inter.Nodup := nodup_filter_bool inQ2 hQ1Nd
  have hBadNd : interBad.Nodup := nodup_filter_bool isCorrupt hInterNd
  have hBadSub : ∀ x ∈ interBad, x ∈ corrupt := by
    intro x hx
    have hp := ((mem_filter_iff_local isCorrupt x inter).mp hx).2
    exact of_decide_eq_true hp
  have hBadLe : interBad.length ≤ corrupt.length := nodup_subset_length_le interBad corrupt hBadNd hBadSub
  have hHonPos : 1 ≤ interHon.length := by omega
  match hHonEq : interHon with
  | [] => False.elim (by simp at hHonPos)
  | h :: _ =>
    have hMemHon : h ∈ interHon := by rw [hHonEq]; exact .head _
    have ⟨hMemInter, hNotCorrB⟩ := (mem_filter_iff_local (fun x => !isCorrupt x) h inter).mp hMemHon
    have ⟨hInQ1, hInQ2B⟩ := (mem_filter_iff_local inQ2 h Q₁).mp hMemInter
    ⟨h, hInQ1, of_decide_eq_true hInQ2B, fun hc => by simp [isCorrupt, hc] at hNotCorrB⟩

/-- **Simplex Consensus Quorum Non-Equivocation (`jorts_quorum_never_double_signs`)**:
    Suppose validator set `V` ($|V| \le 3f + 1$) executes Simplex consensus with at most $f$ Byzantine
    validators `corrupt`, and every honest validator `p ∉ corrupt` gates its per-slot `Jorts` signature
    behind a monotonic `EpochLatchState` (`execEpochLatchTrace` in `HypertreeEufCma.lean`).
    Then NO two quorums `Q₁, Q₂ ⊆ V` of size $\ge 2f + 1$ can ever certify distinct block messages
    `msg₁ ≠ msg₂` in the same consensus slot/epoch `slot`! -/
theorem jorts_quorum_never_double_signs
    {PartyId : Type} [DecidableEq PartyId]
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PartyId → PqSecretKey) (optRand : PartyId → List UInt8) (maxGrind : Nat)
    (f slot : Nat) (msg₁ msg₂ : List UInt8)
    (V Q₁ Q₂ corrupt : List PartyId)
    (hVNodup : V.Nodup) (hVLen : V.length ≤ 3 * f + 1)
    (hQ1Nd : Q₁.Nodup) (hQ1Sub : ∀ x ∈ Q₁, x ∈ V) (hQ1Len : 2 * f + 1 ≤ Q₁.length)
    (hQ2Nd : Q₂.Nodup) (hQ2Sub : ∀ x ∈ Q₂, x ∈ V) (hQ2Len : 2 * f + 1 ≤ Q₂.length)
    (hCorruptLen : corrupt.length ≤ f)
    (traces : PartyId → List (Nat × List UInt8))
    (hCert1 : ∀ p ∈ Q₁, p ∉ corrupt →
      ∃ sig₁, (slot, msg₁, sig₁) ∈ (execEpochLatchTrace suite params (sk p) (optRand p) maxGrind ⟨0, none⟩ (traces p)).2)
    (hCert2 : ∀ p ∈ Q₂, p ∉ corrupt →
      ∃ sig₂, (slot, msg₂, sig₂) ∈ (execEpochLatchTrace suite params (sk p) (optRand p) maxGrind ⟨0, none⟩ (traces p)).2) :
    msg₁ = msg₂ := by
  let ⟨h, hIn1, hIn2, hHonest⟩ := extractHonestQuorumIntersection f V Q₁ Q₂ corrupt
    hVNodup hVLen hQ1Nd hQ1Sub hQ1Len hQ2Nd hQ2Sub hQ2Len hCorruptLen
  obtain ⟨sig₁, hEm1⟩ := hCert1 h hIn1 hHonest
  obtain ⟨sig₂, hEm2⟩ := hCert2 h hIn2 hHonest
  exact epochLatch_trace_no_equivocation suite params (sk h) (optRand h) maxGrind (traces h)
    slot msg₁ sig₁ msg₂ sig₂ hEm1 hEm2

/-! ### 6b. Single Shared Threshold Key + Crash-Resilient Monotone Disk WAL `Jorts` Safety (`C1-3`) -/

/-- Crash-resilient per-validator `Jorts` state holding a durable disk WAL high-water mark
    `walHighWater` (persisted across power-loss crashes) alongside volatile `ramCachedShare`
    (wiped to `none` on crash/reboot) and the network audit log `emittedVotes`. -/
structure WalJortsNodeState where
  walHighWater   : Option (Nat × List UInt8)
  ramCachedShare : Option (Nat × List UInt8 × Goldilocks)
  emittedVotes   : List (Nat × List UInt8 × Goldilocks)
  deriving DecidableEq, Repr

def initWalJortsState : WalJortsNodeState :=
  { walHighWater := none, ramCachedShare := none, emittedVotes := [] }

/-- Multi-turn adversarial node schedule interleaving signing requests with power-loss crashes. -/
inductive WalJortsEvent where
  | signReq (slot : Nat) (msg : List UInt8)
  | powerLossCrashAndReboot
  deriving DecidableEq, Repr

/-- Write-ahead monotonic `Jorts` partial-share signing transition:
    1. `.powerLossCrashAndReboot` wipes volatile `ramCachedShare := none` while durable `walHighWater` survives.
    2. `.signReq slot msg` persists `walHighWater := some (slot, msg)` BEFORE emitting `(slot, msg, myShare)`
       when `walHighWater = none` or `hwSlot < slot`, allows idempotent retry of the exact `(hwSlot, hwMsg)`,
       and rejects every stale or equivocating request (`slot < hwSlot` or `slot = hwSlot ∧ msg ≠ hwMsg`). -/
def stepWalJortsNode (myShare : Goldilocks) (st : WalJortsNodeState) (ev : WalJortsEvent) : WalJortsNodeState :=
  match ev with
  | .powerLossCrashAndReboot =>
    { st with ramCachedShare := none }
  | .signReq slot msg =>
    match st.walHighWater with
    | none =>
      { walHighWater   := some (slot, msg)
        ramCachedShare := some (slot, msg, myShare)
        emittedVotes   := (slot, msg, myShare) :: st.emittedVotes }
    | some (hwSlot, hwMsg) =>
      if slot == hwSlot && decide (msg = hwMsg) then
        { st with ramCachedShare := some (slot, msg, myShare)
                  emittedVotes   := (slot, msg, myShare) :: st.emittedVotes }
      else if decide (hwSlot < slot) then
        { walHighWater   := some (slot, msg)
          ramCachedShare := some (slot, msg, myShare)
          emittedVotes   := (slot, msg, myShare) :: st.emittedVotes }
      else
        st

def runWalJortsTrace (myShare : Goldilocks) : WalJortsNodeState → List WalJortsEvent → WalJortsNodeState
  | st, [] => st
  | st, ev :: evs => runWalJortsTrace myShare (stepWalJortsNode myShare st ev) evs

def WalJortsNodeState.WellFormed (st : WalJortsNodeState) : Prop :=
  (∀ sl m sh, (sl, m, sh) ∈ st.emittedVotes →
    ∃ hwSlot hwMsg, st.walHighWater = some (hwSlot, hwMsg) ∧ (sl < hwSlot ∨ (sl = hwSlot ∧ m = hwMsg))) ∧
  (∀ sl m₁ sh₁ m₂ sh₂,
    (sl, m₁, sh₁) ∈ st.emittedVotes → (sl, m₂, sh₂) ∈ st.emittedVotes → m₁ = m₂)

private theorem stepWalJortsNode_preserves_wellFormed
    (myShare : Goldilocks) (st : WalJortsNodeState) (ev : WalJortsEvent)
    (hWf : st.WellFormed) :
    (stepWalJortsNode myShare st ev).WellFormed := by
  obtain ⟨hBound, hNoEq⟩ := hWf
  cases ev with
  | powerLossCrashAndReboot =>
    exact ⟨hBound, hNoEq⟩
  | signReq slot msg =>
    unfold stepWalJortsNode
    cases hHw : st.walHighWater with
    | none =>
      have hEmpty : ∀ sl m sh, (sl, m, sh) ∉ st.emittedVotes := by
        intro sl m sh hMem
        obtain ⟨_, _, hSome, _⟩ := hBound sl m sh hMem
        rw [hHw] at hSome
        cases hSome
      refine ⟨?_, ?_⟩
      · intro sl m sh hMem
        rcases List.mem_cons.mp hMem with hEq | hOld
        · injection hEq with hSl hRest
          injection hRest with hM _
          exact ⟨slot, msg, rfl, Or.inr ⟨hSl, hM⟩⟩
        · exact False.elim (hEmpty sl m sh hOld)
      · intro sl m₁ sh₁ m₂ sh₂ hMem1 hMem2
        rcases List.mem_cons.mp hMem1 with hEq1 | hOld1
        · rcases List.mem_cons.mp hMem2 with hEq2 | hOld2
          · injection hEq1 with _ hR1; injection hR1 with hM1 _
            injection hEq2 with _ hR2; injection hR2 with hM2 _
            exact hM1.trans hM2.symm
          · exact False.elim (hEmpty sl m₂ sh₂ hOld2)
        · exact False.elim (hEmpty sl m₁ sh₁ hOld1)
    | some pair =>
      rcases pair with ⟨hwSlot, hwMsg⟩
      dsimp only
      generalize hRetryEq : (slot == hwSlot && decide (msg = hwMsg)) = retryB
      cases retryB with
      | true =>
        simp only [↓reduceIte]
        rcases Bool.and_eq_true_iff.mp hRetryEq with ⟨hSlB, hMsgB⟩
        have hSlEq : slot = hwSlot := eq_of_beq hSlB
        have hMsgEq : msg = hwMsg := of_decide_eq_true hMsgB
        refine ⟨?_, ?_⟩
        · intro sl m sh hMem
          rcases List.mem_cons.mp hMem with hEq | hOld
          · injection hEq with h1 hR; injection hR with h2 _
            exact ⟨hwSlot, hwMsg, rfl, Or.inr ⟨h1.trans hSlEq, h2.trans hMsgEq⟩⟩
          · obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m sh hOld
            rw [hHw] at hSome; injection hSome with hPair
            injection hPair with hE1 hE2
            subst hE1; subst hE2
            exact ⟨hwSlot, hwMsg, rfl, hOrd⟩
        · intro sl m₁ sh₁ m₂ sh₂ hMem1 hMem2
          rcases List.mem_cons.mp hMem1 with hEq1 | hOld1
          · injection hEq1 with hS1 hR1; injection hR1 with hM1 _
            rcases List.mem_cons.mp hMem2 with hEq2 | hOld2
            · injection hEq2 with _ hR2; injection hR2 with hM2 _
              exact hM1.trans hM2.symm
            · obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m₂ sh₂ hOld2
              rw [hHw] at hSome; injection hSome with hPair
              injection hPair with hE1 hE2
              rcases hOrd with hLt | ⟨hEqS, hEqM⟩
              · omega
              · rw [hM1, hMsgEq, hEqM, hE2]
          · rcases List.mem_cons.mp hMem2 with hEq2 | hOld2
            · injection hEq2 with hS2 hR2; injection hR2 with hM2 _
              obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m₁ sh₁ hOld1
              rw [hHw] at hSome; injection hSome with hPair
              injection hPair with hE1 hE2
              rcases hOrd with hLt | ⟨hEqS, hEqM⟩
              · omega
              · rw [hM2, hMsgEq, hEqM, hE2]
            · exact hNoEq sl m₁ sh₁ m₂ sh₂ hOld1 hOld2
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        generalize hAdvEq : decide (hwSlot < slot) = advB
        cases advB with
        | true =>
          simp only [↓reduceIte]
          have hLtSlot : hwSlot < slot := of_decide_eq_true hAdvEq
          refine ⟨?_, ?_⟩
          · intro sl m sh hMem
            rcases List.mem_cons.mp hMem with hEq | hOld
            · injection hEq with h1 hR; injection hR with h2 _
              exact ⟨slot, msg, rfl, Or.inr ⟨h1, h2⟩⟩
            · obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m sh hOld
              rw [hHw] at hSome; injection hSome with hPair
              injection hPair with hE1 _
              refine ⟨slot, msg, rfl, Or.inl ?_⟩
              rcases hOrd with hLt | ⟨hEqS, _⟩ <;> omega
          · intro sl m₁ sh₁ m₂ sh₂ hMem1 hMem2
            rcases List.mem_cons.mp hMem1 with hEq1 | hOld1
            · injection hEq1 with hS1 hR1; injection hR1 with hM1 _
              rcases List.mem_cons.mp hMem2 with hEq2 | hOld2
              · injection hEq2 with _ hR2; injection hR2 with hM2 _
                exact hM1.trans hM2.symm
              · obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m₂ sh₂ hOld2
                rw [hHw] at hSome; injection hSome with hPair
                injection hPair with hE1 _
                exfalso
                rcases hOrd with hLt | ⟨hEqS, _⟩ <;> omega
            · rcases List.mem_cons.mp hMem2 with hEq2 | hOld2
              · injection hEq2 with hS2 _
                obtain ⟨hwS', hwM', hSome, hOrd⟩ := hBound sl m₁ sh₁ hOld1
                rw [hHw] at hSome; injection hSome with hPair
                injection hPair with hE1 _
                exfalso
                rcases hOrd with hLt | ⟨hEqS, _⟩ <;> omega
              · exact hNoEq sl m₁ sh₁ m₂ sh₂ hOld1 hOld2
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hBound, hNoEq⟩

/-- **Crash-Resilient Disk WAL Node Non-Equivocation (`walJortsNode_no_equivocation_across_crashes`)**:
    Across ANY multi-turn event trace `evs` interleaving `.signReq` and `.powerLossCrashAndReboot`,
    an honest node never emits partial shares for two distinct messages `m₁ ≠ m₂` at the same `slot`! -/
theorem walJortsNode_no_equivocation_across_crashes
    (myShare : Goldilocks) (evs : List WalJortsEvent)
    (slot : Nat) (m₁ : List UInt8) (sh₁ : Goldilocks) (m₂ : List UInt8) (sh₂ : Goldilocks)
    (h1 : (slot, m₁, sh₁) ∈ (runWalJortsTrace myShare initWalJortsState evs).emittedVotes)
    (h2 : (slot, m₂, sh₂) ∈ (runWalJortsTrace myShare initWalJortsState evs).emittedVotes) :
    m₁ = m₂ := by
  have hPres : ∀ (es : List WalJortsEvent) (st : WalJortsNodeState),
      st.WellFormed → (runWalJortsTrace myShare st es).WellFormed := by
    intro es
    induction es with
    | nil => intro st hWf; exact hWf
    | cons e rest ih =>
      intro st hWf
      exact ih (stepWalJortsNode myShare st e) (stepWalJortsNode_preserves_wellFormed myShare st e hWf)
  have hInitWf : initWalJortsState.WellFormed := by
    refine ⟨?_, ?_⟩
    · intro _ _ _ h; dsimp only [initWalJortsState] at h; cases h
    · intro _ _ _ _ _ h _; dsimp only [initWalJortsState] at h; cases h
  exact (hPres evs initWalJortsState hInitWf).2 slot m₁ sh₁ m₂ sh₂ h1 h2

/-- **Shared-Key Threshold `Jorts` Quorum + Crash-Resilient WAL Safety
    (`threshold_jorts_wal_quorum_never_double_signs`)**:
    Suppose validator set `V` ($|V| \le 3f + 1$, Byzantine `corrupt` $\le f$) holds Shamir shares
    `evalCoeffs skPoly (evalPoint p)` of ONE single degree-$< (2f + 1)$ threshold secret key `skPoly`,
    and each honest validator gates partial-share emission behind `runWalJortsTrace` (surviving
    arbitrary `.powerLossCrashAndReboot` events). Then:
    1. Both threshold-$(2f+1)$ quorums `Q₁, Q₂` recombine to the **exact same** shared secret key
       `RoundPoly.evalCoeffs skPoly Goldilocks.zero`, AND
    2. NO two quorums `Q₁, Q₂ ⊆ V` of size $\ge 2f + 1$ can ever certify distinct messages
       `msg₁ ≠ msg₂` in the same consensus `slot`! -/
theorem threshold_jorts_wal_quorum_never_double_signs
    {PartyId : Type} [DecidableEq PartyId]
    (f slot : Nat) (msg₁ msg₂ : List UInt8)
    (skPoly : List Goldilocks) (hDeg : skPoly.length ≤ 2 * f + 1)
    (evalPoint : PartyId → Goldilocks)
    (V Q₁ Q₂ corrupt : List PartyId)
    (SQ₁ SQ₂ : ShamirQuorum Goldilocks (2 * f + 1))
    (hPts1 : SQ₁.pts = Q₁.map evalPoint) (hPts2 : SQ₂.pts = Q₂.map evalPoint)
    (hVNodup : V.Nodup) (hVLen : V.length ≤ 3 * f + 1)
    (hQ1Nd : Q₁.Nodup) (hQ1Sub : ∀ x ∈ Q₁, x ∈ V) (hQ1Len : 2 * f + 1 ≤ Q₁.length)
    (hQ2Nd : Q₂.Nodup) (hQ2Sub : ∀ x ∈ Q₂, x ∈ V) (hQ2Len : 2 * f + 1 ≤ Q₂.length)
    (hCorruptLen : corrupt.length ≤ f)
    (traces : PartyId → List WalJortsEvent)
    (hCert1 : ∀ p ∈ Q₁, p ∉ corrupt →
      ∃ sh₁, (slot, msg₁, sh₁) ∈
        (runWalJortsTrace (RoundPoly.evalCoeffs skPoly (evalPoint p)) initWalJortsState (traces p)).emittedVotes)
    (hCert2 : ∀ p ∈ Q₂, p ∉ corrupt →
      ∃ sh₂, (slot, msg₂, sh₂) ∈
        (runWalJortsTrace (RoundPoly.evalCoeffs skPoly (evalPoint p)) initWalJortsState (traces p)).emittedVotes) :
    lagrangeCombine SQ₁.lambdas (Q₁.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p))) =
      RoundPoly.evalCoeffs skPoly Goldilocks.zero ∧
    lagrangeCombine SQ₂.lambdas (Q₂.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p))) =
      RoundPoly.evalCoeffs skPoly Goldilocks.zero ∧
    msg₁ = msg₂ := by
  have hRec1 : lagrangeCombine SQ₁.lambdas (Q₁.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p))) =
      RoundPoly.evalCoeffs skPoly Goldilocks.zero := by
    unfold lagrangeCombine
    have hMap1 : Q₁.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p)) =
        SQ₁.pts.map (fun x => RoundPoly.evalCoeffs skPoly x) := by
      rw [hPts1, List.map_map]; rfl
    rw [hMap1]
    exact lagrangeAtZero_evalCoeffs SQ₁.lambdas SQ₁.pts skPoly (2 * f + 1) hDeg SQ₁.sum_one SQ₁.kills_higher
  have hRec2 : lagrangeCombine SQ₂.lambdas (Q₂.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p))) =
      RoundPoly.evalCoeffs skPoly Goldilocks.zero := by
    unfold lagrangeCombine
    have hMap2 : Q₂.map (fun p => RoundPoly.evalCoeffs skPoly (evalPoint p)) =
        SQ₂.pts.map (fun x => RoundPoly.evalCoeffs skPoly x) := by
      rw [hPts2, List.map_map]; rfl
    rw [hMap2]
    exact lagrangeAtZero_evalCoeffs SQ₂.lambdas SQ₂.pts skPoly (2 * f + 1) hDeg SQ₂.sum_one SQ₂.kills_higher
  let ⟨h, hIn1, hIn2, hHonest⟩ := extractHonestQuorumIntersection f V Q₁ Q₂ corrupt
    hVNodup hVLen hQ1Nd hQ1Sub hQ1Len hQ2Nd hQ2Sub hQ2Len hCorruptLen
  obtain ⟨sh₁, hEm1⟩ := hCert1 h hIn1 hHonest
  obtain ⟨sh₂, hEm2⟩ := hCert2 h hIn2 hHonest
  exact ⟨hRec1, hRec2,
    walJortsNode_no_equivocation_across_crashes
      (RoundPoly.evalCoeffs skPoly (evalPoint h)) (traces h) slot msg₁ sh₁ msg₂ sh₂ hEm1 hEm2⟩

/-- **`#tooth` Sub-Threshold Corrupt Subset Cannot Assemble a $(2f + 1)$-Quorum
    (`tooth_subthreshold_corrupt_cannot_form_quorum`)**:
    When `corrupt.length ≤ f`, ANY candidate signer subset `Q ⊆ corrupt` with `Q.Nodup` satisfies
    `Q.length < 2 * f + 1`, failing the threshold quorum requirement! -/
theorem tooth_subthreshold_corrupt_cannot_form_quorum
    {PartyId : Type} [DecidableEq PartyId]
    (f : Nat) (Q corrupt : List PartyId)
    (hQNd : Q.Nodup) (hSub : ∀ x ∈ Q, x ∈ corrupt) (hCorrupt : corrupt.length ≤ f) :
    ¬ (2 * f + 1 ≤ Q.length) := by
  have hLe : Q.length ≤ corrupt.length := nodup_subset_length_le Q corrupt hQNd hSub
  omega

/-- **`#tooth` Crash-Replay Refusal & Multi-Slot Inhabitedness Witness
    (`tooth_wal_latch_blocks_equivocation_after_crash`)**:
    On trace `[signReq 1 [0xAA], powerLossCrashAndReboot, signReq 1 [0xBB], signReq 2 [0xCC]]`:
    1. `.powerLossCrashAndReboot` wipes `ramCachedShare` to `none`, yet durable `walHighWater = some (1, [0xAA])` persists;
    2. Post-crash equivocation `signReq 1 [0xBB]` is **rejected** (never enters `emittedVotes`);
    3. Valid higher-slot `signReq 2 [0xCC]` succeeds, inhabiting multi-slot crash-recovery execution! -/
theorem tooth_wal_latch_blocks_equivocation_after_crash :
    let sh := Goldilocks.ofNat 19
    let afterCrash := runWalJortsTrace sh initWalJortsState
      [.signReq 1 [0xAA], .powerLossCrashAndReboot]
    let finalSt := runWalJortsTrace sh initWalJortsState
      [.signReq 1 [0xAA], .powerLossCrashAndReboot, .signReq 1 [0xBB], .signReq 2 [0xCC]]
    afterCrash.ramCachedShare = none ∧
    afterCrash.walHighWater = some (1, [0xAA]) ∧
    (1, [0xBB], sh) ∉ finalSt.emittedVotes ∧
    finalSt.emittedVotes = [(2, [0xCC], sh), (1, [0xAA], sh)] := by
  refine ⟨rfl, rfl, by decide +kernel, rfl⟩

end Qsag
end
