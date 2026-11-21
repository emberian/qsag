module
/-
# Qsag.Protocol.Signing.FullAdaptiveEufCma — `hCand`-Free Interactive Full-Adversary EUF-CMA

Eliminates the offline `pk`-independence restriction (`hCand`) of
`poly257MultiLeaf_adaptive_forger_bound` (`ExecEufCmaClosedGame` §6.2) constructively:

1. **Interactive Target/Reveal `SM-DT-PRE` Reduction (`multiLeafInteractivePreAdv`):**
   Queries `.target (chain0Tweak (s / 3) (s % 3)) []` on `Spec.smDtPreOracle` (`multiLeafStep0Th`)
   to obtain the hidden step-1 WOTS+C digest, calls `.reveal` to obtain `pkSeed`, reconstructs the
   exact simulated public key `pkSim` and `puncturedSignQuery` oracle inside the `Code`
   continuation, runs **any unrestricted, `pk`-dependent, adaptive `(qHash, qSign)` adversary
   `adv`**, and outputs the extracted preimage `TargetBreak` in `Spec.Within 2`.
2. **`hCand`-Free Universal Theorem (`poly257MultiLeaf_full_adaptive_forger_bound`):**
   Quantifies universally over **all** `adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign` with zero
   `candOf` or `hCand` restriction on how `adv` branches on `pkSeed`, `pkRoot`, `rawHash`, or prior
   adaptive signatures.
3. **Strict Subsumption Witness (`pkDependentAdaptiveForger`):**
   Explicit `pk`-dependent and adaptive-signature-dependent forger that inspects `pk.pkRoot` and the
   response of `signQuery` at `epoch = 0`:
   * `pkDependentAdaptiveForger_violates_hCand`: proves `¬ ∃ candOf, ...`, so the legacy `hCand`
     theorem cannot be applied to `pkDependentAdaptiveForger`;
   * `pkDependentAdaptiveForger_unconditional_bound`: proves `win z0 = true` (`winCount > 0`)
     together with the unconditional `< 1` bound `36 / 256 < 1` via
     `poly257MultiLeaf_full_adaptive_forger_bound` and `multiLeafStep0Th_smDtPreHard_within`.
-/

public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Step-0 Tweakable Hash & Constructive `WithinPreQueries` Hardness -/

/-- Step-0 tweakable hash underlying `poly257MultiLeafSuite`: maps a 1-byte secret `[b]` under
    `seed` and `tweak = chain0Tweak kp r` to the 32-byte `0xB1` chain carrier encoding `(hi, lo)`. -/
@[expose] def multiLeafStep0Th (seed tweak msg : Spec.Bytes) : Spec.Bytes :=
  match msg with
  | [b] =>
    let kp := (tweak.headD 0).toNat
    let r := (tweak.getD 1 0).toNat
    encodeChainNode 0xB1 kp r
      ((Spec.byteXorHash seed (chain0Tweak kp r) [b]).headD 0)
      ((Spec.poly257Hash seed (chain0Tweak kp r) [b]).getD 2 0)
  | _ => [0xFF]

theorem multiLeafStep0Th_hiLo_eq_honest (sk : PqSecretKey) (s : Fin 12) :
    ((multiLeafStep0Th sk.pkSeed (chain0Tweak (s.1 / 3) (s.1 % 3))
        [sk.skSeed.getD s.1 0]).getD 3 0,
     (multiLeafStep0Th sk.pkSeed (chain0Tweak (s.1 / 3) (s.1 % 3))
        [sk.skSeed.getD s.1 0]).getD 4 0) =
      honestSlotHiLo sk (s.1 / 3) (s.1 % 3) := by
  have hkp : s.1 / 3 < 4 := by have := s.2; omega
  have hr : s.1 % 3 < 3 := Nat.mod_lt _ (by decide)
  have hkp8 : (UInt8.ofNat (s.1 / 3)).toNat = s.1 / 3 := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hr8 : (UInt8.ofNat (s.1 % 3)).toNat = s.1 % 3 := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have hSlot : 3 * (s.1 / 3) + s.1 % 3 = s.1 := Nat.div_add_mod s.1 3
  dsimp only [multiLeafStep0Th]
  rw [chain0Tweak.public_eqs]
  simp only [List.headD, List.getD_cons_zero, List.getD_cons_succ,
    hkp8, hr8, encodeChainNode.public_eqs, honestSlotHiLo.public_eqs, hSlot, List.cons_append]

theorem multiLeafStep0Th_oneByte_inj (seed tweak cand : Spec.Bytes) (b : UInt8)
    (hEq : multiLeafStep0Th seed tweak cand = multiLeafStep0Th seed tweak [b]) :
    cand = [b] := by
  cases cand with
  | nil =>
    dsimp only [multiLeafStep0Th] at hEq
    have hLen := congrArg List.length hEq
    rw [encodeChainNode.public_eqs] at hLen
    simp at hLen
  | cons b' rest =>
    cases rest with
    | nil =>
      have hByte3 : (multiLeafStep0Th seed tweak [b']).getD 3 0 =
          (multiLeafStep0Th seed tweak [b]).getD 3 0 :=
        congrArg (fun l => l.getD 3 0) hEq
      dsimp only [multiLeafStep0Th] at hByte3
      rw [encodeChainNode.public_eqs, encodeChainNode.public_eqs] at hByte3
      simp only [List.cons_append, List.getD_cons_succ, List.getD_cons_zero] at hByte3
      exact congrArg (· :: []) (byteXorHash_headD_inj _ _ hByte3)
    | cons _ _ =>
      dsimp only [multiLeafStep0Th] at hEq
      have hLen := congrArg List.length hEq
      rw [encodeChainNode.public_eqs] at hLen
      simp at hLen

private def firstTargetTweak : Spec.Code Spec.targetIface Spec.TargetBreak → Option Spec.Bytes
  | .ret _ => none
  | .call (.target t _) _ => some t
  | .call .reveal _ => none

private theorem smDtPreOracle_revealed_targets
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (hidden : Nat → Spec.Bytes) :
    ∀ (c : Spec.Code Spec.targetIface Spec.TargetBreak) (st : Spec.TargetState),
      st.revealed = true ∨ st.targets.length = 1 →
      (Spec.Code.play (Spec.smDtPreOracle th 1 hidden) c st).2.targets = st.targets
  | .ret _, st, _ => by rw [Spec.Code.play_ret]
  | .call .reveal k, st, _ => by
    rw [Spec.Code.play_call, Spec.smDtPreOracle_reveal]
    exact smDtPreOracle_revealed_targets th hidden (k (some st.seed)) { st with revealed := true }
      (.inl rfl)
  | .call (.target t d) k, st, hFull => by
    rw [Spec.Code.play_call]
    have hStep : Spec.smDtPreOracle th 1 hidden st (.target t d) = (none, st) := by
      rw [Spec.smDtPreOracle_target]
      rcases hFull with hRev | hLen
      · simp [hRev]
      · simp [hLen]
    rw [hStep]
    exact smDtPreOracle_revealed_targets th hidden (k none) st hFull

private theorem smDtPreOracle_init_targets
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (seed : Spec.Bytes) (hidden : Nat → Spec.Bytes)
    (c : Spec.Code Spec.targetIface Spec.TargetBreak) :
    (Spec.Code.play (Spec.smDtPreOracle th 1 hidden) c ⟨seed, [], false⟩).2.targets =
      match firstTargetTweak c with
      | none => []
      | some t => [(t, hidden 0)] := by
  cases c with
  | ret _ => rw [Spec.Code.play_ret]; rfl
  | call qr k =>
    cases qr with
    | reveal =>
      rw [Spec.Code.play_call, Spec.smDtPreOracle_reveal]
      exact smDtPreOracle_revealed_targets th hidden (k (some seed)) ⟨seed, [], true⟩ (.inl rfl)
    | target t d =>
      rw [Spec.Code.play_call]
      have hStep : Spec.smDtPreOracle th 1 hidden ⟨seed, [], false⟩ (.target t d) =
          (some (th seed t (hidden 0)), ⟨seed, [(t, hidden 0)], false⟩) := by
        rw [Spec.smDtPreOracle_target]
        simp
      rw [hStep]
      exact smDtPreOracle_revealed_targets th hidden (k (some (th seed t (hidden 0))))
        ⟨seed, [(t, hidden 0)], false⟩ (.inr rfl)

private theorem smDtPreOracle_final_seed
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (hidden : Nat → Spec.Bytes) :
    ∀ (c : Spec.Code Spec.targetIface Spec.TargetBreak) (st : Spec.TargetState),
      (Spec.Code.play (Spec.smDtPreOracle th 1 hidden) c st).2.seed = st.seed
  | .ret _, st => by rw [Spec.Code.play_ret]
  | .call .reveal k, st => by
    rw [Spec.Code.play_call, Spec.smDtPreOracle_reveal]
    exact smDtPreOracle_final_seed th hidden (k (some st.seed)) { st with revealed := true }
  | .call (.target t d) k, st => by
    rw [Spec.Code.play_call, Spec.smDtPreOracle_target]
    split
    · exact smDtPreOracle_final_seed th hidden _ _
    · exact smDtPreOracle_final_seed th hidden _ _

private theorem boundedPreAdv_mem_dict_wins (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (seed tweak : Spec.Bytes) (hidden : Nat → Spec.Bytes) (dict : List Spec.Bytes)
    (hMem : hidden 0 ∈ dict) :
    Spec.smDtPreWin th
      (Spec.Code.play (Spec.smDtPreOracle th 1 hidden)
        (Spec.boundedPreAdv th tweak dict) ⟨seed, [], false⟩).2
      (Spec.Code.play (Spec.smDtPreOracle th 1 hidden)
        (Spec.boundedPreAdv th tweak dict) ⟨seed, [], false⟩).1 = true := by
  rw [Spec.boundedPreAdv_eq, Spec.smDtPreWin_eq, Spec.Code.play_call]
  have hStep1 : Spec.smDtPreOracle th 1 hidden ⟨seed, [], false⟩ (.target tweak []) =
      (some (th seed tweak (hidden 0)), ⟨seed, [(tweak, hidden 0)], false⟩) := by
    rw [Spec.smDtPreOracle_target]; simp
  rw [hStep1, Spec.Code.play_call, Spec.smDtPreOracle_reveal, Spec.Code.play_ret]
  dsimp only [Option.getD]
  have hPred : (fun m' => decide (some (th seed tweak m') = some (th seed tweak (hidden 0))))
      (hidden 0) = true := decide_eq_true rfl
  have hFound := Spec.firstByteString_spec
    (fun m' => decide (some (th seed tweak m') = some (th seed tweak (hidden 0))))
    dict (hidden 0) hMem hPred
  have hCol : th seed tweak
      (Spec.firstByteString
        (fun m' => decide (some (th seed tweak m') = some (th seed tweak (hidden 0)))) dict) =
      th seed tweak (hidden 0) :=
    Option.some.inj (of_decide_eq_true hFound)
  exact List.any_eq_true.mpr ⟨(tweak, hidden 0), List.Mem.head _,
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl, decide_eq_true hCol⟩⟩

/-- **Unconditional `WithinPreQueries` Hardness of `multiLeafStep0Th`
    (`multiLeafStep0Th_smDtPreHard_within`).**
    Proved constructively (`0 Classical.choice`) by per-slice reduction on `CoinSplit.challengerOnly`
    into `Spec.poly257Hash_smDtPreHard_within`. -/
theorem multiLeafStep0Th_smDtPreHard_within (qTarget qEval : Nat) :
    Spec.SmDtPreHard (Spec.WithinPreQueries qTarget qEval) multiLeafStep0Th 1 1 1
      ⟨qEval + 1, 256, by decide⟩ := by
  intro n nC nA hPos π sample hSample adv hAdv
  have hCard : n = nC * nA := π.card_eq
  have hnCPos : 0 < nC := Nat.pos_of_mul_pos_right (hCard ▸ hPos)
  let winAt (c : Fin nC) (a : Fin nA) : Bool :=
    Spec.smDtPreWin multiLeafStep0Th
      (Spec.Code.play (Spec.smDtPreOracle multiLeafStep0Th 1 (fun i => (sample c).2.getD i []))
        (adv a) ⟨(sample c).1, [], false⟩).2
      (Spec.Code.play (Spec.smDtPreOracle multiLeafStep0Th 1 (fun i => (sample c).2.getD i []))
        (adv a) ⟨(sample c).1, [], false⟩).1
  unfold Spec.GameBound Spec.RatBound.le Spec.FinGame.winProb Spec.FinGame.winCount
  dsimp only
  rw [π.sampleSum_eq]
  conv => rhs; rw [hCard]
  have hSwap : Spec.sampleSum nC (fun c => Spec.sampleSum nA (fun a =>
      if (Spec.smDtPreGame hPos multiLeafStep0Th 1
          (fun ω => (sample (π.chal ω)).1)
          (fun ω i => (sample (π.chal ω)).2.getD i [])
          (fun ω => adv (π.advc ω))).win (π.pair c a)
      then 1 else 0)) =
      Spec.sampleSum nA (fun a => Spec.sampleSum nC (fun c =>
        if winAt c a then 1 else 0)) := by
    have hExt : Spec.sampleSum nC (fun c => Spec.sampleSum nA (fun a =>
        if (Spec.smDtPreGame hPos multiLeafStep0Th 1
            (fun ω => (sample (π.chal ω)).1)
            (fun ω i => (sample (π.chal ω)).2.getD i [])
            (fun ω => adv (π.advc ω))).win (π.pair c a)
        then 1 else 0)) =
        Spec.sampleSum nC (fun c => Spec.sampleSum nA (fun a =>
          if winAt c a then 1 else 0)) :=
      Spec.sampleSum_ext (fun c => Spec.sampleSum_ext (fun a => by
        simp only [Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs,
          π.chal_pair, π.advc_pair, winAt]))
    exact hExt.trans (Spec.sampleSum_comm nC nA _)
  rw [hSwap]
  have hPerA : ∀ a : Fin nA,
      Spec.sampleSum nC (fun c => if winAt c a then 1 else 0) * 256 ≤ (qEval + 1) * nC := by
    intro a
    have hAdvA := hAdv a
    rw [Spec.WithinPreQueries_eq] at hAdvA
    obtain ⟨_, dict, hDictLen, hDictMem⟩ := hAdvA
    let t₀ := (firstTargetTweak (adv a)).getD []
    let gStep : Spec.FinGame nC := Spec.FinGame.mk hnCPos (fun c => winAt c a)
    let gPoly : Spec.FinGame nC :=
      Spec.smDtPreGame hnCPos Spec.poly257Hash 1
        (fun c => (sample ((Spec.CoinSplit.challengerOnly nC).chal c)).1)
        (fun c i => (sample ((Spec.CoinSplit.challengerOnly nC).chal c)).2.getD i [])
        (fun _ => Spec.boundedPreAdv Spec.poly257Hash t₀ dict)
    have hPolyBound : Spec.GameBound gPoly.winProb ⟨qEval + 1, 256, by decide⟩ :=
      Spec.poly257Hash_smDtPreHard_within 2 qEval nC nC 1 hnCPos
        (Spec.CoinSplit.challengerOnly nC) sample hSample
        (fun _ => Spec.boundedPreAdv Spec.poly257Hash t₀ dict)
        (fun _ => Spec.boundedPreAdv_mem_within Spec.poly257Hash t₀ dict hDictLen)
    have hRed : Spec.GameBound gStep.winProb gPoly.winProb :=
      Spec.event_le_reduction_win gStep gPoly (fun c hW => by
        have hSampleOk := hSample.mem c
        rw [Spec.SmDtPreSampleOk_eq] at hSampleOk
        have hHidLen1 : ((sample c).2.getD 0 []).length = 1 := by
          have hL := hSampleOk.2.1
          cases hList : (sample c).2 with
          | nil => rw [hList] at hL; cases hL
          | cons m0 _ =>
            have hm0Mem : m0 ∈ (sample c).2 := by rw [hList]; exact List.mem_cons_self
            exact hSampleOk.2.2 m0 hm0Mem
        obtain ⟨b, hbEq⟩ : ∃ b : UInt8, (sample c).2.getD 0 [] = [b] := by
          cases hM0 : (sample c).2.getD 0 [] with
          | nil => rw [hM0] at hHidLen1; cases hHidLen1
          | cons b rest =>
            cases rest with
            | nil => exact ⟨b, rfl⟩
            | cons _ _ => rw [hM0] at hHidLen1; cases hHidLen1
        let playRes := Spec.Code.play
          (Spec.smDtPreOracle multiLeafStep0Th 1 (fun i => (sample c).2.getD i []))
          (adv a) ⟨(sample c).1, [], false⟩
        have hWinPred : Spec.smDtPreWin multiLeafStep0Th playRes.2 playRes.1 = true := hW
        rw [Spec.smDtPreWin_eq] at hWinPred
        obtain ⟨e, heInTargets, hAnd⟩ := List.any_eq_true.mp hWinPred
        obtain ⟨hTwDec, hThDec⟩ := Bool.and_eq_true_iff.mp hAnd
        have hTwEq := of_decide_eq_true hTwDec
        have hThEq := of_decide_eq_true hThDec
        have hSeedEq : playRes.2.seed = (sample c).1 :=
          smDtPreOracle_final_seed multiLeafStep0Th _ (adv a) _
        have hTargs := smDtPreOracle_init_targets multiLeafStep0Th (sample c).1
          (fun i => (sample c).2.getD i []) (adv a)
        change playRes.2.targets = _ at hTargs
        cases hFt : firstTargetTweak (adv a) with
        | none =>
          rw [hFt] at hTargs
          rw [hTargs] at heInTargets
          nomatch heInTargets
        | some t =>
          rw [hFt] at hTargs
          rw [hTargs] at heInTargets
          have hPairEq := List.mem_singleton.mp heInTargets
          have hmEq : e.2 = (sample c).2.getD 0 [] := congrArg Prod.snd hPairEq
          rw [hSeedEq, hmEq, hbEq] at hThEq
          have hCandEq : playRes.1.candidate = [b] :=
            multiLeafStep0Th_oneByte_inj (sample c).1 e.1 playRes.1.candidate b hThEq
          have hInCons := hDictMem
            (Spec.smDtPreOracle multiLeafStep0Th 1 (fun i => (sample c).2.getD i []))
            ⟨(sample c).1, [], false⟩
          change playRes.1.candidate ∈ [] :: dict at hInCons
          rw [hCandEq] at hInCons
          have hbInDict : [b] ∈ dict := by
            rcases List.mem_cons.mp hInCons with hNil | hIn
            · cases hNil
            · exact hIn
          simp only [gPoly, Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs,
            Spec.CoinSplit.challengerOnly_chal]
          exact boundedPreAdv_mem_dict_wins Spec.poly257Hash (sample c).1 t₀
            (fun i => (sample c).2.getD i []) dict (hbEq ▸ hbInDict))
    exact Spec.GameBound.trans hRed hPolyBound
  have hMulSum :
      Spec.sampleSum nA (fun a => Spec.sampleSum nC (fun c => if winAt c a then 1 else 0)) * 256 ≤
      Spec.sampleSum nA (fun _ => (qEval + 1) * nC) := by
    rw [← Spec.sampleSum_mul_right]
    exact Spec.sampleSum_le nA _ _ hPerA
  rw [Spec.sampleSum_const] at hMulSum
  refine Nat.le_trans hMulSum ?_
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_refl _

/-! ## §2. Genuine Interactive Target/Reveal Reduction (`hCand`-Free Universal Theorem) -/

/-- **Interactive Target/Reveal `SM-DT-PRE` Reduction (`multiLeafInteractivePreAdv`).** -/
@[expose] def multiLeafInteractivePreAdv {nA qHash qSign : Nat}
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (s : Fin 12) (advCoin : Fin (pow256 23 * nA)) :
    Spec.Code Spec.targetIface Spec.TargetBreak :=
  let tweak := chain0Tweak (s.1 / 3) (s.1 % 3)
  .call (.target tweak []) fun yOpt =>
    .call .reveal fun seedOpt =>
      let y := yOpt.getD []
      let endpt : UInt8 × UInt8 := (y.getD 3 0, y.getD 4 0)
      let pkSeed := seedOpt.getD []
      let spAdv := Spec.CoinSplit.prod (pow256 23) nA
      let other23 := byteVecSampler 23 (spAdv.chal advCoin)
      let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
      let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
        (puncturedSignQuery pkSeed s endpt other23)
        ((adv (spAdv.advc advCoin)).run pkSim) 0).1
      let cand :=
        if simOut.2.leafGlobalIdx = s.1 / 3 then
          extractSigChainCand simOut.2 (s.1 % 3)
        else []
      .ret ⟨tweak, [], cand⟩

theorem multiLeafInteractivePreAdv_within {nA qHash qSign : Nat}
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    (s : Fin 12) (advCoin : Fin (pow256 23 * nA)) :
    Spec.Within 2 (multiLeafInteractivePreAdv adv s advCoin) :=
  .call _ _ (fun _ => .call _ _ (fun _ => .ret 0 _))

/-- **`hCand`-Free Universal Full-Adaptive EUF-CMA Bound (`poly257MultiLeaf_full_adaptive_forger_bound`).** -/
theorem poly257MultiLeaf_full_adaptive_forger_bound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ (s : Fin 12) (c : Fin (pow256 23 * nA)), 𝒜 (multiLeafInteractivePreAdv adv s c))
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard 𝒜 multiLeafStep0Th 1 1 1 εPre) :
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 εPre) := by
  let R : Fin 12 → Spec.FinGame ((256 * pow256 24) * nA) := fun s =>
    Spec.smDtPreGame hPos multiLeafStep0Th 1
      (fun z => (Spec.byte1SeedAndPreSampler
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).chal z)).1)
      (fun z i => (Spec.byte1SeedAndPreSampler
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).chal z)).2.getD i [])
      (fun z => multiLeafInteractivePreAdv adv s
        ((puncturedKeyAndAdvSplit nA (slot24Of12 s)).advc z))
  have hRed := Spec.event_le_reduction_win
    (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
      (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
      (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z)))
    (Spec.FinGame.mk hPos (anySlotWins 12 R))
    (fun ω hW => by
      obtain ⟨s, hsDiv, _, _, hSimEq, hExtrEq⟩ :=
        poly257MultiLeaf_punctured_sim_sound hPos adv ω hW
      refine anySlotWins_of_win 12 R ω s ?_
      let π₀ := Spec.CoinSplit.prod (256 * pow256 24) nA
      let o := execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen (π₀.chal z)) (fun z => adv (π₀.advc z)) ω
      let πs := puncturedKeyAndAdvSplit nA (slot24Of12 s)
      obtain ⟨hSeedC, hHidC, _, _, _⟩ := puncturedKeyAndAdvSplit_coords s ω
      have hSeedEq : (Spec.byte1SeedAndPreSampler (πs.chal ω)).1 = o.sk.pkSeed := hSeedC
      have hHid0Eq : ((Spec.byte1SeedAndPreSampler (πs.chal ω)).2.getD 0 []) =
          [o.sk.skSeed.getD s.1 0] := by
        rw [hHidC]; rfl
      show (R s).win ω = true
      simp only [R, Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs]
      unfold multiLeafInteractivePreAdv
      let tweak := chain0Tweak (s.1 / 3) (s.1 % 3)
      let hiddenFn := fun i : Nat => (Spec.byte1SeedAndPreSampler (πs.chal ω)).2.getD i []
      rw [Spec.Code.play_call]
      have hStep1 : Spec.smDtPreOracle multiLeafStep0Th 1 hiddenFn
          ⟨(Spec.byte1SeedAndPreSampler (πs.chal ω)).1, [], false⟩ (.target tweak []) =
          (some (multiLeafStep0Th o.sk.pkSeed tweak [o.sk.skSeed.getD s.1 0]),
           ⟨o.sk.pkSeed, [(tweak, [o.sk.skSeed.getD s.1 0])], false⟩) := by
        rw [Spec.smDtPreOracle_target]
        dsimp only [hiddenFn]
        simp only [List.length_nil, Nat.zero_lt_one, List.map_nil, List.not_mem_nil,
          not_false_eq_true, and_self, ↓reduceIte, List.nil_append, hSeedEq, hHid0Eq]
      rw [hStep1, Spec.Code.play_call, Spec.smDtPreOracle_reveal, Spec.Code.play_ret]
      simp only [Option.getD, tweak, multiLeafStep0Th_hiLo_eq_honest o.sk s]
      have hSimFst : (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery o.sk.pkSeed s (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
            (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω))))
          ((adv ((Spec.CoinSplit.prod (pow256 23) nA).advc (πs.advc ω))).run
            (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s
              (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
              (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω)))))) 0).1 =
          (o.msgStar, o.sigStar) := congrArg Prod.fst hSimEq
      have hLeafHit : (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery o.sk.pkSeed s (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
            (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω))))
          ((adv ((Spec.CoinSplit.prod (pow256 23) nA).advc (πs.advc ω))).run
            (pkFromTbl o.sk.pkSeed (puncturedSlotTbl o.sk.pkSeed s
              (honestSlotHiLo o.sk (s.1 / 3) (s.1 % 3))
              (byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) nA).chal (πs.advc ω)))))) 0).1.2.leafGlobalIdx =
          s.1 / 3 := by
        rw [hSimFst]; exact hsDiv.symm
      rw [ite_eq_left hLeafHit, hExtrEq, Spec.smDtPreWin_eq]
      exact List.any_eq_true.mpr ⟨(tweak, [o.sk.skSeed.getD s.1 0]), List.Mem.head _,
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true rfl, decide_eq_true rfl⟩⟩)
  have hEach : ∀ s : Fin 12, Spec.GameBound (R s).winProb εPre := fun s =>
    hPre _ _ _ hPos (puncturedKeyAndAdvSplit nA (slot24Of12 s))
      Spec.byte1SeedAndPreSampler Spec.uniformOn_byte1SeedAndPre
      (multiLeafInteractivePreAdv adv s) (hClass s)
  exact Spec.GameBound.trans hRed (anySlotWins_bound hPos 12 R hEach)

theorem poly257MultiLeaf_full_adaptive_within2_bound {nA qHash qSign : Nat}
    (hPos : 0 < (256 * pow256 24) * nA)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {εPre : Spec.RatBound}
    (hPre : Spec.SmDtPreHard (Spec.Within 2) multiLeafStep0Th 1 1 1 εPre) :
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams
        (fun z => multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) nA).chal z))
        (fun z => adv ((Spec.CoinSplit.prod (256 * pow256 24) nA).advc z))).winProb
      (Spec.RatBound.scale 12 εPre) :=
  poly257MultiLeaf_full_adaptive_forger_bound hPos adv
    (multiLeafInteractivePreAdv_within adv) hPre

/-! ## §3. `pk`-Dependent & Signature-Adaptive Witness Strictly Subsuming Legacy `hCand` -/

def pkDependentAdaptiveForger : SeedWithheldEufCmaAdv 3 1 where
  run pk :=
    .signQuery ⟨[0, 0], [], 0, 1⟩ (fun sig0Opt =>
      let lsig0 := match sig0Opt with
        | some s => s.layerSigs.headD ⟨0, [], []⟩
        | none => ⟨0, [], []⟩
      let c0 := lsig0.wotsChains.getD 0 zero32
      let c2 := lsig0.wotsChains.getD 2 zero32
      let guessByte : UInt8 :=
        if sig0Opt.isSome && decide ((pk.pkRoot.getD 4 0).toNat % 2 = 0) then 0x00 else 0x01
      stepChain3Adaptive pk.pkSeed 0 0 c0 (fun c0End =>
        .pure ([0, 1],
          { rRand := zero32
            msgTswCtr := 0
            leafGlobalIdx := 0
            forsOpenings := []
            layerSigs := [⟨0, c0End :: encodeStep0Secret guessByte :: c2 ::
              List.replicate 125 crumb32, lsig0.authPath⟩] })))
  bounded pk := by
    unfold ProdDualBounded
    intro sig0Opt
    dsimp only
    rw [stepChain3Adaptive.public_eqs]
    exact fun _ _ _ => trivial

private theorem evalLatched_pkDependent_shape
    (sign : ProdSigningQuery → Option PqHashSig) (pk : PqPublicKey) :
    let out := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash sign
      (pkDependentAdaptiveForger.run pk) 0).1
    let sig0Opt := sign ⟨[0, 0], [], 0, 1⟩
    let lsig0 := match sig0Opt with
      | some s => s.layerSigs.headD ⟨0, [], []⟩
      | none => ⟨0, [], []⟩
    let guessByte : UInt8 :=
      if sig0Opt.isSome && decide ((pk.pkRoot.getD 4 0).toNat % 2 = 0) then 0x00 else 0x01
    out = ([0, 1],
      { rRand := zero32
        msgTswCtr := 0
        leafGlobalIdx := 0
        forsOpenings := []
        layerSigs := [⟨0,
          wotsChainSteps poly257MultiLeafSuite pk.pkSeed 0 0 0 0 0 3
            (lsig0.wotsChains.getD 0 zero32) ::
          encodeStep0Secret guessByte ::
          lsig0.wotsChains.getD 2 zero32 ::
          List.replicate 125 crumb32,
          lsig0.authPath⟩] }) := by
  unfold pkDependentAdaptiveForger
  dsimp only
  rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0)),
    evalLatched_stepChain3Adaptive]
  simp only [evalLatchedAdaptiveTree.public_eqs]

theorem pkDependentAdaptiveForger_violates_hCand :
    ¬ ∃ (candOf : Fin 12 → Fin (pow256 23 * 1) → Spec.Bytes),
        ∀ (s : Fin 12) (c : Fin (pow256 23 * 1)) (pkSeed : List UInt8) (endpt : UInt8 × UInt8),
          let spAdv := Spec.CoinSplit.prod (pow256 23) 1
          let other23 := byteVecSampler 23 (spAdv.chal c)
          let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
          let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
            (puncturedSignQuery pkSeed s endpt other23)
            (pkDependentAdaptiveForger.run pkSim) 0).1
          simOut.2.leafGlobalIdx = s.1 / 3 →
          extractSigChainCand simOut.2 (s.1 % 3) ≠ [] →
          extractSigChainCand simOut.2 (s.1 % 3) = candOf s c := by
  rintro ⟨candOf, hCand⟩
  let s1 : Fin 12 := ⟨1, by decide⟩
  let c0 : Fin (pow256 23 * 1) :=
    (Spec.CoinSplit.prod (pow256 23) 1).pair (zeroVecCoin 23) ⟨0, Nat.one_pos⟩
  let other23 := byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) 1).chal c0)
  have evalCandAt : ∀ hi : UInt8,
      let pkSim := pkFromTbl [0x00] (puncturedSlotTbl [0x00] s1 (hi, 0x00) other23)
      let simOut := (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
        (puncturedSignQuery [0x00] s1 (hi, 0x00) other23)
        (pkDependentAdaptiveForger.run pkSim) 0).1
      simOut.2.leafGlobalIdx = s1.1 / 3 ∧
      extractSigChainCand simOut.2 (s1.1 % 3) =
        [if decide (hi.toNat % 2 = 0) then 0x00 else 0x01] := by
    intro hi
    let pkSim := pkFromTbl [0x00] (puncturedSlotTbl [0x00] s1 (hi, 0x00) other23)
    have hShape := evalLatched_pkDependent_shape
      (puncturedSignQuery [0x00] s1 (hi, 0x00) other23) pkSim
    have hSome := puncturedSignQuery_s1_00_isSome [0x00] (hi, 0x00) other23
    have hByte4 := pkFromTbl_puncturedSlotTbl_s1_byte4 [0x00] hi 0x00 other23
    change pkSim.pkRoot.getD 4 0 = hi at hByte4
    refine ⟨by rw [hShape]; dsimp only [s1], ?_⟩
    rw [hShape, hSome, hByte4, Bool.true_and]
    change extractSigChainCand _ 1 = _
    rw [extractSigChainCand.public_eqs]
    simp only [List.headD, List.getD_cons_succ, List.getD_cons_zero,
      decodeStep0Byte_encodeStep0Secret]
  obtain ⟨hL0, hC0⟩ := evalCandAt 0x00
  obtain ⟨hL1, hC1⟩ := evalCandAt 0x01
  have hEq0 : ([0x00] : Spec.Bytes) = candOf s1 c0 := by
    have hNe0 : ([0x00] : Spec.Bytes) ≠ [] := List.cons_ne_nil _ _
    have hSim0 : ([if decide ((0x00 : UInt8).toNat % 2 = 0) then (0x00 : UInt8) else 0x01]) =
        [0x00] := rfl
    rw [hSim0] at hC0
    have hNeCand0 : extractSigChainCand
        (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery [0x00] s1 (0x00, 0x00) other23)
          (pkDependentAdaptiveForger.run
            (pkFromTbl [0x00] (puncturedSlotTbl [0x00] s1 (0x00, 0x00) other23))) 0).1.2
        (s1.1 % 3) ≠ [] := by
      rw [hC0]; exact hNe0
    exact hC0.symm.trans (hCand s1 c0 [0x00] (0x00, 0x00) hL0 hNeCand0)
  have hEq1 : ([0x01] : Spec.Bytes) = candOf s1 c0 := by
    have hNe1 : ([0x01] : Spec.Bytes) ≠ [] := List.cons_ne_nil _ _
    have hSim1 : ([if decide ((0x01 : UInt8).toNat % 2 = 0) then (0x00 : UInt8) else 0x01]) =
        [0x01] := rfl
    rw [hSim1] at hC1
    have hNeCand1 : extractSigChainCand
        (evalLatchedAdaptiveTree true poly257MultiLeafSuite.rawHash
          (puncturedSignQuery [0x00] s1 (0x01, 0x00) other23)
          (pkDependentAdaptiveForger.run
            (pkFromTbl [0x00] (puncturedSlotTbl [0x00] s1 (0x01, 0x00) other23))) 0).1.2
        (s1.1 % 3) ≠ [] := by
      rw [hC1]; exact hNe1
    exact hC1.symm.trans (hCand s1 c0 [0x00] (0x01, 0x00) hL1 hNeCand1)
  have hAbsurd : ([0x00] : Spec.Bytes) = [0x01] := hEq0.trans hEq1.symm
  exact absurd hAbsurd (by decide)

theorem pkDependentInteractivePreAdv_mem_within
    (s : Fin 12) (c : Fin (pow256 23 * 1)) :
    Spec.WithinPreQueries 2 3
      (multiLeafInteractivePreAdv (fun _ : Fin 1 => pkDependentAdaptiveForger) s c) := by
  rw [Spec.WithinPreQueries_eq]
  refine ⟨multiLeafInteractivePreAdv_within _ s c,
    [[0x00], [0x01], match decodeStep0Byte zero32 with | none => [] | some v => [v]],
    Nat.le_refl 3, ?_⟩
  intro oracle st
  unfold multiLeafInteractivePreAdv
  rw [Spec.Code.play_call, Spec.Code.play_call, Spec.Code.play_ret]
  dsimp only
  let y := (oracle st (.target (chain0Tweak (s.1 / 3) (s.1 % 3)) [])).1.getD []
  let st1 := (oracle st (.target (chain0Tweak (s.1 / 3) (s.1 % 3)) [])).2
  let pkSeed := (oracle st1 .reveal).1.getD []
  let endpt : UInt8 × UInt8 := (y.getD 3 0, y.getD 4 0)
  let other23 := byteVecSampler 23 ((Spec.CoinSplit.prod (pow256 23) 1).chal c)
  let pkSim := pkFromTbl pkSeed (puncturedSlotTbl pkSeed s endpt other23)
  have hShape := evalLatched_pkDependent_shape
    (puncturedSignQuery pkSeed s endpt other23) pkSim
  rw [hShape]
  dsimp only
  by_cases hDiv0 : 0 = s.1 / 3
  · rw [ite_eq_left hDiv0]
    have hsCases : s.1 = 0 ∨ s.1 = 1 ∨ s.1 = 2 := by have := s.2; omega
    rcases hsCases with hs0 | hs1 | hs2
    · have hMod0 : s.1 % 3 = 0 := by rw [hs0]
      rw [hMod0, extractSigChainCand_stepChain3_empty pkSim.pkSeed 0 0 _ (by decide) (by decide)]
      exact List.Mem.head _
    · have hMod1 : s.1 % 3 = 1 := by rw [hs1]
      rw [hMod1, extractSigChainCand.public_eqs]
      simp only [List.headD, List.getD_cons_succ, List.getD_cons_zero,
        decodeStep0Byte_encodeStep0Secret]
      cases ((puncturedSignQuery pkSeed s endpt other23 ⟨[0, 0], [], 0, 1⟩).isSome &&
          decide ((pkSim.pkRoot.getD 4 0).toNat % 2 = 0))
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exact List.Mem.tail _ (List.Mem.head _)
    · have hsEq2 : s = ⟨2, by decide⟩ := Fin.ext hs2
      subst hsEq2
      change extractSigChainCand _ 2 ∈ _
      rw [puncturedSignQuery_s2_00_none, extractSigChainCand.public_eqs]
      simp only [List.headD, List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
      cases decodeStep0Byte zero32
      · exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · rw [ite_eq_right hDiv0]
    exact List.Mem.head _

theorem pkDependentAdaptiveForger_unconditional_bound :
    let hPos : 0 < (256 * pow256 24) * 1 :=
      Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos
    let keygen := fun z : Fin ((256 * pow256 24) * 1) =>
      multiLeaf24Keygen ((Spec.CoinSplit.prod (256 * pow256 24) 1).chal z)
    let adv := fun _ : Fin ((256 * pow256 24) * 1) => pkDependentAdaptiveForger
    let z0 : Fin ((256 * pow256 24) * 1) :=
      (Spec.CoinSplit.prod (256 * pow256 24) 1).pair
        ((Spec.CoinSplit.prod 256 (pow256 24)).pair ⟨0, by decide⟩ (zeroVecCoin 24))
        ⟨0, Nat.one_pos⟩
    (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams keygen adv).win z0 = true ∧
    Spec.GameBound
      (ExecEufCmaGame hPos poly257MultiLeafSuite multiLeaf4JortsParams keygen adv).winProb
      (Spec.RatBound.scale 12 ⟨4, 256, by decide⟩) ∧
    (Spec.RatBound.scale 12 ⟨4, 256, by decide⟩).lt Spec.RatBound.one := by
  intro hPos keygen adv z0
  refine ⟨?_,
    poly257MultiLeaf_full_adaptive_forger_bound hPos (fun _ => pkDependentAdaptiveForger)
      pkDependentInteractivePreAdv_mem_within (multiLeafStep0Th_smDtPreHard_within 2 3),
    by decide⟩
  have hSk0 : keygen z0 = ⟨List.replicate 24 0x00, [], [0x00]⟩ := by
    dsimp only [keygen, z0]
    rw [(Spec.CoinSplit.prod (256 * pow256 24) 1).chal_pair, multiLeaf24Keygen.public_eqs,
      (Spec.CoinSplit.prod 256 (pow256 24)).chal_pair,
      (Spec.CoinSplit.prod 256 (pow256 24)).advc_pair,
      byteVecSampler_zeroVecCoin 24, Spec.byte1SeedSampler.public_eqs]
    rfl
  have hS0 : prodSignQuery poly257MultiLeafSuite multiLeaf4JortsParams (keygen z0)
      ⟨[0, 0], [], 0, 1⟩ = some (honestMultiLeafSig (keygen z0) 0 0) :=
    prodSignQuery_poly257MultiLeaf_valid (keygen z0) (by decide : 0 < 4) (by decide : 0 < 3)
      Nat.one_pos []
  have hPkRoot4Even : ((derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams
      (keygen z0)).pkRoot.getD 4 0).toNat % 2 = 0 := by
    rw [derivePublicKey_poly257MultiLeaf, hSk0, pkFromTbl.public_eqs, rootFromTbl.public_eqs,
      packLeaf3.public_eqs]
    simp only [List.cons_append, List.nil_append, List.getD_cons_succ, List.getD_cons_zero]
    rw [honestSlotHiLo.public_eqs, chain0Tweak.public_eqs, Spec.byteXorHash_eq]
    dsimp only [List.headD]
    decide
  have hPkSeedEq : (derivePublicKey poly257MultiLeafSuite multiLeaf4JortsParams
      (keygen z0)).pkSeed = (keygen z0).pkSeed := by
    unfold derivePublicKey; rfl
  rw [ExecEufCmaGame, execEufCmaGameWith_win]
  have hOutEq : execEufCmaOutcome true poly257MultiLeafSuite multiLeaf4JortsParams keygen adv z0 =
      let lsig0 := (honestMultiLeafSig (keygen z0) 0 0).layerSigs.headD ⟨0, [], []⟩
      let c0End := wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 0 0 0 3
        (lsig0.wotsChains.getD 0 zero32)
      let c2 := lsig0.wotsChains.getD 2 zero32
      ⟨keygen z0, [⟨[0, 0], [], 0, 1⟩], [0, 1],
       { rRand := zero32
         msgTswCtr := 0
         leafGlobalIdx := 0
         forsOpenings := []
         layerSigs := [⟨0, c0End :: encodeStep0Secret 0x00 :: c2 :: List.replicate 125 crumb32,
           lsig0.authPath⟩] }⟩ := by
    unfold execEufCmaOutcome
    dsimp only [adv, pkDependentAdaptiveForger]
    rw [evalLatchedAdaptiveTree_sign, ite_eq_left (Or.inr (Nat.zero_le 0)), hS0]
    dsimp only [Option.isSome, Bool.true_and]
    rw [decide_eq_true hPkRoot4Even, hPkSeedEq, evalLatched_stepChain3Adaptive]
    simp only [evalLatchedAdaptiveTree.public_eqs, Bool.and_self, ↓reduceIte]
  rw [hOutEq, prodEufCmaWin_eq]
  dsimp only
  rw [productionSigningLog_cons, hS0, productionSigningLog_nil]
  dsimp only [List.append, List.map]
  refine Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true (by decide : ([0, 1] : List UInt8) ∉ [[0, 0]])⟩
  rw [honestMultiLeafSig.public_eqs]
  dsimp only [List.headD]
  have hGet0 : ((List.range 128).map (fun r =>
      wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 0 r 0
        ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
        (wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 0 r))).getD 0 zero32 =
      wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 0 0 := by
    rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.1,
      wotsChainSteps_zero]
  have hGet2 : ((List.range 128).map (fun r =>
      wotsChainSteps poly257MultiLeafSuite (keygen z0).pkSeed 0 0 0 r 0
        ((extractBaseWDigits 4 128 (encodeSubMsg3Hmsg 0)).getD r 0)
        (wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 0 r))).getD 2 zero32 =
      wotsSecretBase poly257MultiLeafSuite (keygen z0) 0 0 0 2 := by
    rw [list_getD_map_range 128 _ zero32 (by decide), encodeSubMsg3Hmsg_explicit_digits.2.2.1,
      wotsChainSteps_zero]
  rw [hGet0, hGet2]
  refine verify_assembled_leaf_sig (keygen z0) (by decide : 0 < 4) (by decide : 1 < 3) _ _ _ ?_ ?_ ?_
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.1]
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.1, wotsChainSteps_zero, wotsSecretBase_eq,
      poly257MultiLeaf_thSecretPrf]
    have hu0 : (UInt32.ofNat 0).toNat = 0 := rfl
    have hu1 : (UInt32.ofNat 1).toNat = 1 := rfl
    dsimp only
    rw [hu0, hu1, ite_eq_left (by decide : 0 < 4 ∧ 1 < 3), hSk0]
    rfl
  · rw [encodeSubMsg3Hmsg_explicit_digits.2.2.2.2.2.1, wotsChainSteps_zero]

theorem inhabited_poly257MultiLeaf_full_adaptive_forger_bound :
    ∃ (nA qHash qSign : Nat),
      0 < (256 * pow256 24) * nA ∧
      ∃ (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
        (𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop),
        (∀ (s : Fin 12) (c : Fin (pow256 23 * nA)), 𝒜 (multiLeafInteractivePreAdv adv s c)) ∧
        ∃ εPre : Spec.RatBound,
          Spec.SmDtPreHard 𝒜 multiLeafStep0Th 1 1 1 εPre :=
  ⟨1, 3, 1,
   Nat.mul_pos (Nat.mul_pos (by decide) (pow256_pos 24)) Nat.one_pos,
   fun _ => pkDependentAdaptiveForger,
   Spec.WithinPreQueries 2 3,
   pkDependentInteractivePreAdv_mem_within,
   ⟨4, 256, by decide⟩,
   multiLeafStep0Th_smDtPreHard_within 2 3⟩

#verify_constructive
  Qsag.multiLeafStep0Th_hiLo_eq_honest
  Qsag.multiLeafStep0Th_oneByte_inj
  Qsag.multiLeafStep0Th_smDtPreHard_within
  Qsag.multiLeafInteractivePreAdv_within
  Qsag.poly257MultiLeaf_full_adaptive_forger_bound
  Qsag.poly257MultiLeaf_full_adaptive_within2_bound
  Qsag.pkDependentAdaptiveForger_violates_hCand
  Qsag.pkDependentInteractivePreAdv_mem_within
  Qsag.pkDependentAdaptiveForger_unconditional_bound
  Qsag.inhabited_poly257MultiLeaf_full_adaptive_forger_bound

#verify_inhabited
  Qsag.poly257MultiLeaf_full_adaptive_forger_bound
  Qsag.inhabited_poly257MultiLeaf_full_adaptive_forger_bound

#tooth_pair Qsag.poly257MultiLeaf_full_adaptive_forger_bound vs
  Qsag.tooth_poly257MultiLeaf_unlatched_reuse_forges
#tooth_pair Qsag.pkDependentAdaptiveForger_unconditional_bound vs
  Qsag.pkDependentAdaptiveForger_violates_hCand

end Qsag
end
