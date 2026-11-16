module
/-
# Qsag.Spec.IdealCustody — Ideal Separated Threshold Custody Functionality

Layer-0 ideal functionality for threshold custody, as one reactive `Machine` with four ports:

* `.approve party deploymentId intent` — the port of an enrolled, non-corrupt custodian. It records an
  approval permit `(party, deploymentId, intent)`; a corrupted party's port is closed.
* `.advApprove party deploymentId intent` — the adversary's port. It records a permit only for a party
  that is already corrupted.
* `.corrupt party` — adaptive corruption. It reveals the party's approval history, moves the party to
  the adversary, and is refused once it would bring the number of corruptions to `threshold`.
* `.sign deploymentId intent abortBeforeRelease` — release. It carries no approver list and no spend
  argument: the quorum is counted over the recorded permits for exactly `(deploymentId, intent)`, the
  amount charged is `intent.spend`, and the oracle signs `digest deploymentId intent`.

The state is bound to an immutable `deploymentId`. The ledger part (`CustodyLedger`: spend budget,
epoch write-ahead log, session set, quarantine latch) and its signing transition `custodyLedgerSign`
take the number of approving parties as an argument.

Scope of the refinements into this functionality: `Qsag.Top.certCustodyMachine`, a certificate-pool
coordinator model with a raw certificate interface that reuses `custodyLedgerSign`, is related to it
on traces without a forgery event. The real coordinator `Custody.submitRecorded` is related to it by
`Qsag.Top.separatedCustody_refines_idealCustody_of` on runs satisfying three named, unproved run
assumptions (no forgery event, a single deployment, increasing leaves); that theorem covers the
verdict and state correspondence only, not the signature output or WAL replay. The `IdealTsig`, ELF,
MIR, RSS and WAL machines are not proved to refine this functionality.

The digest is a parameter (`CustodyDigestScheme`) whose only law is joint injectivity in
`(deploymentId, intent)`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Intents, permits, digests -/

/-- The complete custody intent. Every field is covered by the approval permits, by the digest
    that is signed, and by the write-ahead-log identity. -/
structure CustodyIntent where
  sessionId : Nat
  round : Nat
  epoch : Nat
  spend : Nat
  payload : Bytes
  deriving Repr

theorem CustodyIntent.eq_of_fields : ∀ {a b : CustodyIntent},
    a.sessionId = b.sessionId → a.round = b.round → a.epoch = b.epoch → a.spend = b.spend →
    a.payload = b.payload → a = b
  | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl => rfl

/-- Field-wise decidable equality, exposed so that importing modules can evaluate custody runs. -/
instance instDecidableEqCustodyIntent : DecidableEq CustodyIntent := fun a b =>
  if h : a.sessionId = b.sessionId ∧ a.round = b.round ∧ a.epoch = b.epoch ∧
      a.spend = b.spend ∧ a.payload = b.payload then
    .isTrue (CustodyIntent.eq_of_fields h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
  else .isFalse (fun he => h (by rw [he]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-- An approval permit: `party` approved `intent` for deployment `deploymentId`. -/
structure CustodyApproval where
  party : Nat
  deploymentId : Nat
  intent : CustodyIntent
  deriving Repr

theorem CustodyApproval.eq_of_fields : ∀ {a b : CustodyApproval},
    a.party = b.party → a.deploymentId = b.deploymentId → a.intent = b.intent → a = b
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl, rfl, rfl => rfl

instance instDecidableEqCustodyApproval : DecidableEq CustodyApproval := fun a b =>
  if h : a.party = b.party ∧ a.deploymentId = b.deploymentId ∧ a.intent = b.intent then
    .isTrue (CustodyApproval.eq_of_fields h.1 h.2.1 h.2.2)
  else .isFalse (fun he => h (by rw [he]; exact ⟨rfl, rfl, rfl⟩))

/-- Digest of `(deploymentId, intent)` committed into the signing transition and the WAL.
    `digest_inj` is the binding law required of the instantiation. -/
structure CustodyDigestScheme (D : Type) where
  digest : Nat → CustodyIntent → D
  digest_inj : ∀ {d d' : Nat} {i i' : CustodyIntent}, digest d i = digest d' i' → d = d' ∧ i = i'

/-- The identity digest: the pair itself. It shows the binding law is satisfiable. -/
@[expose] def CustodyDigestScheme.transparent : CustodyDigestScheme (Nat × CustodyIntent) where
  digest d i := (d, i)
  digest_inj h := ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Inputs of the ideal custody functionality, one constructor per port. -/
inductive CustodyInput where
  | approve (party deploymentId : Nat) (intent : CustodyIntent)
  | advApprove (party deploymentId : Nat) (intent : CustodyIntent)
  | corrupt (party : Nat)
  | sign (deploymentId : Nat) (intent : CustodyIntent) (abortBeforeRelease : Bool)
  deriving DecidableEq, Repr

/-- Observable response on an accepted input. `corrupted` carries the state revealed to the
    adversary: the intents the newly corrupted party had approved. -/
inductive CustodyOutcome (Sig : Type) where
  | approvalRecorded
  | corrupted (revealed : List CustodyIntent)
  | released (sig : Sig)
  | replayedFromWal (sig : Sig)
  | abortedQuarantined
  deriving DecidableEq, Repr

/-- A committed WAL record: the intent, the digest that was signed, and the signature. -/
structure CustodyRelease (D Sig : Type) where
  intent : CustodyIntent
  digest : D
  sig : Sig

/-! ## 2. The ledger: budget, epoch WAL, sessions, quarantine -/

/-- Deployment-bound ledger. `authorized` lists every intent that consumed budget (released, or
    aborted after authorization); `releasedHistory` is the multi-epoch WAL replay table. -/
structure CustodyLedger (PK D Sig : Type) where
  deploymentId : Nat
  enrolledPk : PK
  quorum : CustodyQuorumProfile
  poisoned : Bool
  spent : Nat
  nextFreshEpoch : Nat
  usedSessions : List Nat
  authorized : List CustodyIntent
  releasedHistory : List (CustodyRelease D Sig)

/-- Charge `i.spend`, consume its session and epoch, and log `i` as authorized. -/
@[expose] def CustodyLedger.authorize {PK D Sig : Type}
    (L : CustodyLedger PK D Sig) (i : CustodyIntent) : CustodyLedger PK D Sig :=
  { L with
    spent := L.spent + i.spend
    nextFreshEpoch := i.epoch + 1
    usedSessions := i.sessionId :: L.usedSessions
    authorized := i :: L.authorized }

/-- Look up the committed record for epoch `ep` across the whole WAL. -/
@[expose] def findReleasedEpoch {D Sig : Type}
    (hist : List (CustodyRelease D Sig)) (ep : Nat) : Option (CustodyRelease D Sig) :=
  match hist with
  | [] => none
  | r :: rest => if ep = r.intent.epoch then some r else findReleasedEpoch rest ep

/-- Signing transition of the ledger, given the number `approvalCount` of distinct parties holding
    a permit for `(L.deploymentId, i)`. A committed epoch replays its signature only for the intent
    with the committed digest; a fresh epoch needs the quorum and room for `i.spend` in the budget. -/
@[expose] def custodyLedgerSign {PK D Sig : Type} [DecidableEq D]
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (L : CustodyLedger PK D Sig) (approvalCount : Nat)
    (dep : Nat) (i : CustodyIntent) (abortBeforeRelease : Bool) :
    Option (CustodyLedger PK D Sig × CustodyOutcome Sig) :=
  if L.poisoned = false ∧ dep = L.deploymentId then
    match findReleasedEpoch L.releasedHistory i.epoch with
    | some r =>
      if S.digest L.deploymentId i = r.digest then some (L, .replayedFromWal r.sig) else none
    | none =>
      if L.nextFreshEpoch ≤ i.epoch ∧ i.sessionId ∉ L.usedSessions ∧
          L.quorum.threshold ≤ approvalCount ∧ L.spent + i.spend ≤ L.quorum.spendCap then
        if abortBeforeRelease = true then
          some ({ L.authorize i with poisoned := true }, .abortedQuarantined)
        else
          some ({ L.authorize i with
                  releasedHistory :=
                    ⟨i, S.digest L.deploymentId i, oracleSign (S.digest L.deploymentId i)⟩ ::
                      L.releasedHistory },
                .released (oracleSign (S.digest L.deploymentId i)))
      else none
  else none

/-! ## 3. The ideal functionality -/

/-- State of the ideal custody functionality: the ledger, the adaptively grown corruption set, the
    permits recorded through honest custodians' ports and those recorded through the adversary's. -/
structure IdealCustodyState (PK D Sig : Type) where
  ledger : CustodyLedger PK D Sig
  corruptParties : List Nat
  honestApprovals : List CustodyApproval
  corruptApprovals : List CustodyApproval

/-- Initial state: nothing spent, no party corrupted, no permit recorded. -/
@[expose] def IdealCustodyState.init {PK D Sig : Type}
    (dep : Nat) (pk : PK) (quorum : CustodyQuorumProfile) : IdealCustodyState PK D Sig :=
  { ledger :=
      { deploymentId := dep
        enrolledPk := pk
        quorum := quorum
        poisoned := false
        spent := 0
        nextFreshEpoch := 0
        usedSessions := []
        authorized := []
        releasedHistory := [] }
    corruptParties := []
    honestApprovals := []
    corruptApprovals := [] }

/-- The enrolled parties holding a permit for exactly `(dep, i)`, each counted once. -/
@[expose] def custodyApprovers (numParties : Nat) (honest corrupt : List CustodyApproval)
    (dep : Nat) (i : CustodyIntent) : List Nat :=
  (List.range numParties).filter (fun p =>
    decide (CustodyApproval.mk p dep i ∈ honest) || decide (CustodyApproval.mk p dep i ∈ corrupt))

/-- State revealed when `p` is corrupted: the intents `p` approved through its own port. -/
@[expose] def custodyRevealed (honest : List CustodyApproval) (p : Nat) : List CustodyIntent :=
  (honest.filter (fun a => decide (a.party = p))).map CustodyApproval.intent

/-- Single-step transition of the ideal custody functionality. -/
@[expose] def idealCustodyStep {PK D Sig : Type} [DecidableEq D]
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (st : IdealCustodyState PK D Sig) (inp : CustodyInput) :
    Option (IdealCustodyState PK D Sig × CustodyOutcome Sig) :=
  match inp with
  | .approve p dep i =>
    if p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧ dep = st.ledger.deploymentId then
      some ({ st with honestApprovals := CustodyApproval.mk p dep i :: st.honestApprovals },
            .approvalRecorded)
    else none
  | .advApprove p dep i =>
    if p ∈ st.corruptParties ∧ dep = st.ledger.deploymentId then
      some ({ st with corruptApprovals := CustodyApproval.mk p dep i :: st.corruptApprovals },
            .approvalRecorded)
    else none
  | .corrupt p =>
    if p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
        st.corruptParties.length + 1 < st.ledger.quorum.threshold then
      some ({ st with corruptParties := p :: st.corruptParties },
            .corrupted (custodyRevealed st.honestApprovals p))
    else none
  | .sign dep i ab =>
    (custodyLedgerSign S oracleSign st.ledger
      (custodyApprovers st.ledger.quorum.numParties st.honestApprovals st.corruptApprovals
        st.ledger.deploymentId i).length dep i ab).map
      (fun r => ({ st with ledger := r.1 }, r.2))

/-- `Machine` packaging of the ideal custody functionality for deployment `dep₀`. -/
@[expose] def idealCustodyMachine {PK D Sig : Type} [DecidableEq D]
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    Machine (IdealCustodyState PK D Sig) CustodyInput (CustodyOutcome Sig) where
  Init st := st = IdealCustodyState.init dep₀ pk₀ quorum₀
  step := idealCustodyStep S oracleSign
  errStep st _ := st

/-! ## 4. Elementary facts -/

private theorem custody_if_pos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem custody_if_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem length_filter_ne_lt (x : Nat) :
    ∀ (M : List Nat), x ∈ M → (M.filter (fun y => decide (y ≠ x))).length < M.length
  | [], h => False.elim (List.not_mem_nil h)
  | y :: M, h => by
    by_cases hy : y = x
    · have hf : (y :: M).filter (fun z => decide (z ≠ x)) = M.filter (fun z => decide (z ≠ x)) :=
        List.filter_cons_of_neg (fun hd => (of_decide_eq_true hd) hy)
      rw [hf, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have hf : (y :: M).filter (fun z => decide (z ≠ x)) =
          y :: M.filter (fun z => decide (z ≠ x)) :=
        List.filter_cons_of_pos (decide_eq_true hy)
      have hx : x ∈ M := by
        rcases List.mem_cons.mp h with hEq | hTail
        · exact absurd hEq.symm hy
        · exact hTail
      rw [hf, List.length_cons, List.length_cons]
      exact Nat.succ_lt_succ (length_filter_ne_lt x M hx)

private theorem nodup_subset_length :
    ∀ (L M : List Nat), L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, M, hNd, hSub => by
    rw [List.nodup_cons] at hNd
    have hSub' : ∀ z ∈ xs, z ∈ M.filter (fun y => decide (y ≠ x)) := fun z hz =>
      List.mem_filter.mpr ⟨hSub z (List.mem_cons_of_mem _ hz),
        decide_eq_true (fun hzx => hNd.1 (hzx ▸ hz))⟩
    have ih := nodup_subset_length xs _ hNd.2 hSub'
    have hlt := length_filter_ne_lt x M (hSub x List.mem_cons_self)
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih hlt)

private theorem all_mem_or_exists_not_mem (C : List Nat) :
    ∀ (L : List Nat), (∀ p ∈ L, p ∈ C) ∨ (∃ p, p ∈ L ∧ p ∉ C)
  | [] => .inl (fun _ h => False.elim (List.not_mem_nil h))
  | x :: xs => by
    by_cases hx : x ∈ C
    · rcases all_mem_or_exists_not_mem C xs with hAll | ⟨p, hp, hpC⟩
      · refine .inl (fun p hp => ?_)
        rcases List.mem_cons.mp hp with hEq | hTail
        · exact hEq ▸ hx
        · exact hAll p hTail
      · exact .inr ⟨p, List.mem_cons_of_mem _ hp, hpC⟩
    · exact .inr ⟨x, List.mem_cons_self, hx⟩

/-- Pigeonhole: a duplicate-free list longer than `C` has an element outside `C`. -/
private theorem exists_not_mem_of_length_lt {L C : List Nat}
    (hNd : L.Nodup) (hLt : C.length < L.length) : ∃ p, p ∈ L ∧ p ∉ C := by
  rcases all_mem_or_exists_not_mem C L with hAll | h
  · exact absurd (nodup_subset_length L C hNd hAll) (Nat.not_le_of_gt hLt)
  · exact h

theorem findReleasedEpoch_some {D Sig : Type}
    {hist : List (CustodyRelease D Sig)} {ep : Nat} {r : CustodyRelease D Sig}
    (h : findReleasedEpoch hist ep = some r) : r ∈ hist ∧ r.intent.epoch = ep := by
  induction hist with
  | nil =>
    unfold findReleasedEpoch at h
    cases h
  | cons hd tl ih =>
    unfold findReleasedEpoch at h
    by_cases he : ep = hd.intent.epoch
    · rw [custody_if_pos he] at h
      cases h
      exact ⟨List.mem_cons_self, he.symm⟩
    · rw [custody_if_neg he] at h
      exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- A committed record is found under its own epoch, however many later epochs were committed. -/
theorem findReleasedEpoch_of_mem_nodup {D Sig : Type}
    {hist : List (CustodyRelease D Sig)} {r : CustodyRelease D Sig}
    (hMem : r ∈ hist)
    (hNd : (hist.map (fun x => x.intent.epoch)).Nodup) :
    findReleasedEpoch hist r.intent.epoch = some r := by
  induction hist with
  | nil => exact False.elim (List.not_mem_nil hMem)
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hNd
    unfold findReleasedEpoch
    rcases List.mem_cons.mp hMem with hEq | hIn
    · rw [hEq]
      exact custody_if_pos rfl _ _
    · have hNe : ¬ (r.intent.epoch = hd.intent.epoch) := fun hE =>
        hNd.1 (hE ▸ List.mem_map_of_mem (f := fun x => x.intent.epoch) hIn)
      rw [custody_if_neg hNe]
      exact ih hIn hNd.2

theorem custodyApprovers_nodup (numParties : Nat) (honest corrupt : List CustodyApproval)
    (dep : Nat) (i : CustodyIntent) :
    (custodyApprovers numParties honest corrupt dep i).Nodup := by
  unfold custodyApprovers
  exact List.Pairwise.filter _ (Qsag.Constructive.nodup_range numParties)

theorem mem_custodyApprovers {numParties : Nat} {honest corrupt : List CustodyApproval}
    {dep : Nat} {i : CustodyIntent} {p : Nat}
    (h : p ∈ custodyApprovers numParties honest corrupt dep i) :
    p < numParties ∧
      (CustodyApproval.mk p dep i ∈ honest ∨ CustodyApproval.mk p dep i ∈ corrupt) := by
  unfold custodyApprovers at h
  rcases List.mem_filter.mp h with ⟨hR, hV⟩
  refine ⟨List.mem_range.mp hR, ?_⟩
  rcases Bool.or_eq_true_iff.mp hV with h1 | h1
  · exact .inl (of_decide_eq_true h1)
  · exact .inr (of_decide_eq_true h1)

/-- A duplicate-free list of enrolled parties that all hold a permit for `(dep, i)` is no longer
    than the list of approvers. -/
theorem custodyApprovers_length_le_of_subset {numParties : Nat} {parties : List Nat}
    {honest corrupt : List CustodyApproval} {dep : Nat} {i : CustodyIntent}
    (hNd : parties.Nodup)
    (hSub : ∀ p ∈ parties, p < numParties ∧
      (CustodyApproval.mk p dep i ∈ honest ∨ CustodyApproval.mk p dep i ∈ corrupt)) :
    parties.length ≤ (custodyApprovers numParties honest corrupt dep i).length := by
  refine nodup_subset_length parties _ hNd (fun p hp => ?_)
  unfold custodyApprovers
  exact List.mem_filter.mpr ⟨List.mem_range.mpr (hSub p hp).1,
    Bool.or_eq_true_iff.mpr ((hSub p hp).2.imp decide_eq_true decide_eq_true)⟩

/-- Honest-quorum intersection: when the adversary's permits all belong to the `corruptP` parties
    and fewer than `t` parties are corrupted, a `t`-quorum of permit holders for `(dep, i)` contains
    a party outside `corruptP`, and that party's permit was recorded through its own port. -/
theorem custodyApprovers_honest_witness {numParties t : Nat}
    {honest corruptA : List CustodyApproval} {corruptP : List Nat}
    {dep : Nat} {i : CustodyIntent}
    (hBudget : corruptP.length < t)
    (hQuorum : t ≤ (custodyApprovers numParties honest corruptA dep i).length)
    (hOwned : ∀ a ∈ corruptA, a.party ∈ corruptP) :
    ∃ p, p < numParties ∧ p ∉ corruptP ∧ CustodyApproval.mk p dep i ∈ honest := by
  obtain ⟨p, hp, hpC⟩ := exists_not_mem_of_length_lt
    (custodyApprovers_nodup numParties honest corruptA dep i)
    (Nat.lt_of_lt_of_le hBudget hQuorum)
  obtain ⟨hLt, hRec⟩ := mem_custodyApprovers hp
  rcases hRec with hH | hC
  · exact ⟨p, hLt, hpC, hH⟩
  · exact absurd (hOwned _ hC) hpC

/-- Corruption reveals only permits the corrupted party itself recorded. -/
theorem custodyRevealed_mem {honest : List CustodyApproval} {p : Nat} {i : CustodyIntent}
    (h : i ∈ custodyRevealed honest p) : ∃ a ∈ honest, a.party = p ∧ a.intent = i := by
  unfold custodyRevealed at h
  obtain ⟨a, ha, hEq⟩ := List.mem_map.mp h
  obtain ⟨hm, hd⟩ := List.mem_filter.mp ha
  exact ⟨a, hm, of_decide_eq_true hd, hEq⟩

/-! ## 5. Inversion of the transition -/

section Step

variable {PK D Sig : Type} [DecidableEq D]
variable {S : CustodyDigestScheme D} {oracleSign : D → Sig}

/-- Every accepted ledger signing step is a WAL replay of the committed digest, or a fresh
    authorization (quorum met, session and epoch fresh, `i.spend` within budget) that aborts into
    quarantine or commits `digest L.deploymentId i` with its signature. -/
theorem custodyLedgerSign_inv
    {L L' : CustodyLedger PK D Sig} {n dep : Nat} {i : CustodyIntent} {ab : Bool}
    {out : CustodyOutcome Sig}
    (h : custodyLedgerSign S oracleSign L n dep i ab = some (L', out)) :
    L.poisoned = false ∧ dep = L.deploymentId ∧
    ((∃ r, findReleasedEpoch L.releasedHistory i.epoch = some r ∧
        S.digest L.deploymentId i = r.digest ∧ L' = L ∧ out = .replayedFromWal r.sig) ∨
     (findReleasedEpoch L.releasedHistory i.epoch = none ∧
      L.nextFreshEpoch ≤ i.epoch ∧ i.sessionId ∉ L.usedSessions ∧
      L.quorum.threshold ≤ n ∧ L.spent + i.spend ≤ L.quorum.spendCap ∧
      ((ab = true ∧ L' = { L.authorize i with poisoned := true } ∧ out = .abortedQuarantined) ∨
       (ab = false ∧
        L' = { L.authorize i with
               releasedHistory :=
                 ⟨i, S.digest L.deploymentId i, oracleSign (S.digest L.deploymentId i)⟩ ::
                   L.releasedHistory } ∧
        out = .released (oracleSign (S.digest L.deploymentId i)))))) := by
  unfold custodyLedgerSign at h
  by_cases hg : L.poisoned = false ∧ dep = L.deploymentId
  · rw [custody_if_pos hg] at h
    refine ⟨hg.1, hg.2, ?_⟩
    cases hf : findReleasedEpoch L.releasedHistory i.epoch with
    | some r =>
      rw [hf] at h
      dsimp only at h
      by_cases hd : S.digest L.deploymentId i = r.digest
      · rw [custody_if_pos hd] at h
        cases h
        exact .inl ⟨r, rfl, hd, rfl, rfl⟩
      · rw [custody_if_neg hd] at h
        cases h
    | none =>
      rw [hf] at h
      dsimp only at h
      by_cases hq : L.nextFreshEpoch ≤ i.epoch ∧ i.sessionId ∉ L.usedSessions ∧
          L.quorum.threshold ≤ n ∧ L.spent + i.spend ≤ L.quorum.spendCap
      · rw [custody_if_pos hq] at h
        cases ab with
        | true =>
          rw [custody_if_pos rfl] at h
          cases h
          exact .inr ⟨rfl, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, .inl ⟨rfl, rfl, rfl⟩⟩
        | false =>
          rw [custody_if_neg Bool.false_ne_true] at h
          cases h
          exact .inr ⟨rfl, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2, .inr ⟨rfl, rfl, rfl⟩⟩
      · rw [custody_if_neg hq] at h
        cases h
  · rw [custody_if_neg hg] at h
    cases h

private theorem custodyLedgerSign_of_found
    {L : CustodyLedger PK D Sig} {n dep : Nat} {i : CustodyIntent} {ab : Bool}
    {r : CustodyRelease D Sig}
    (hP : L.poisoned = false) (hD : dep = L.deploymentId)
    (hF : findReleasedEpoch L.releasedHistory i.epoch = some r) :
    custodyLedgerSign S oracleSign L n dep i ab =
      if S.digest L.deploymentId i = r.digest then some (L, .replayedFromWal r.sig) else none := by
  unfold custodyLedgerSign
  rw [custody_if_pos (And.intro hP hD), hF]

/-- The ledger's signing transition reads the approval count only through `threshold ≤ count`:
    an accepted step stays accepted, with the same result, for any larger count. -/
theorem custodyLedgerSign_mono
    {L : CustodyLedger PK D Sig} {n m dep : Nat} {i : CustodyIntent} {ab : Bool}
    {r : CustodyLedger PK D Sig × CustodyOutcome Sig}
    (h : custodyLedgerSign S oracleSign L n dep i ab = some r) (hnm : n ≤ m) :
    custodyLedgerSign S oracleSign L m dep i ab = some r := by
  rcases r with ⟨L', out⟩
  obtain ⟨hP, hD, hCase⟩ := custodyLedgerSign_inv h
  rcases hCase with ⟨rec, hF, hDig, hSame, hOut⟩ | ⟨hF, hEp, hSess, hQ, hCap, hAb⟩
  · rw [custodyLedgerSign_of_found hP hD hF, custody_if_pos hDig, hSame, hOut]
  · unfold custodyLedgerSign
    rw [custody_if_pos (And.intro hP hD), hF]
    dsimp only
    rw [custody_if_pos (show L.nextFreshEpoch ≤ i.epoch ∧ i.sessionId ∉ L.usedSessions ∧
      L.quorum.threshold ≤ m ∧ L.spent + i.spend ≤ L.quorum.spendCap from
      ⟨hEp, hSess, Nat.le_trans hQ hnm, hCap⟩)]
    rcases hAb with ⟨hab, hL', hOut⟩ | ⟨hab, hL', hOut⟩
    · subst hab
      subst hL'
      subst hOut
      exact custody_if_pos rfl _ _
    · subst hab
      subst hL'
      subst hOut
      exact custody_if_neg Bool.false_ne_true _ _

theorem idealCustodyStep_approve_inv
    {st st' : IdealCustodyState PK D Sig} {p dep : Nat} {i : CustodyIntent}
    {out : CustodyOutcome Sig}
    (h : idealCustodyStep S oracleSign st (.approve p dep i) = some (st', out)) :
    (p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧ dep = st.ledger.deploymentId) ∧
    st' = { st with honestApprovals := CustodyApproval.mk p dep i :: st.honestApprovals } ∧
    out = .approvalRecorded := by
  unfold idealCustodyStep at h
  dsimp only at h
  by_cases hg : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
      dep = st.ledger.deploymentId
  · rw [custody_if_pos hg] at h
    cases h
    exact ⟨hg, rfl, rfl⟩
  · rw [custody_if_neg hg] at h
    cases h

theorem idealCustodyStep_advApprove_inv
    {st st' : IdealCustodyState PK D Sig} {p dep : Nat} {i : CustodyIntent}
    {out : CustodyOutcome Sig}
    (h : idealCustodyStep S oracleSign st (.advApprove p dep i) = some (st', out)) :
    (p ∈ st.corruptParties ∧ dep = st.ledger.deploymentId) ∧
    st' = { st with corruptApprovals := CustodyApproval.mk p dep i :: st.corruptApprovals } ∧
    out = .approvalRecorded := by
  unfold idealCustodyStep at h
  dsimp only at h
  by_cases hg : p ∈ st.corruptParties ∧ dep = st.ledger.deploymentId
  · rw [custody_if_pos hg] at h
    cases h
    exact ⟨hg, rfl, rfl⟩
  · rw [custody_if_neg hg] at h
    cases h

/-- An accepted corruption adds exactly `p`, keeps the corruption count below `threshold`, leaves
    the ledger and every permit in place, and reveals `p`'s own approvals. -/
theorem idealCustodyStep_corrupt_inv
    {st st' : IdealCustodyState PK D Sig} {p : Nat} {out : CustodyOutcome Sig}
    (h : idealCustodyStep S oracleSign st (.corrupt p) = some (st', out)) :
    (p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
      st.corruptParties.length + 1 < st.ledger.quorum.threshold) ∧
    st' = { st with corruptParties := p :: st.corruptParties } ∧
    out = .corrupted (custodyRevealed st.honestApprovals p) := by
  unfold idealCustodyStep at h
  dsimp only at h
  by_cases hg : p < st.ledger.quorum.numParties ∧ p ∉ st.corruptParties ∧
      st.corruptParties.length + 1 < st.ledger.quorum.threshold
  · rw [custody_if_pos hg] at h
    cases h
    exact ⟨hg, rfl, rfl⟩
  · rw [custody_if_neg hg] at h
    cases h

theorem idealCustodyStep_sign_inv
    {st st' : IdealCustodyState PK D Sig} {dep : Nat} {i : CustodyIntent} {ab : Bool}
    {out : CustodyOutcome Sig}
    (h : idealCustodyStep S oracleSign st (.sign dep i ab) = some (st', out)) :
    ∃ L', custodyLedgerSign S oracleSign st.ledger
        (custodyApprovers st.ledger.quorum.numParties st.honestApprovals st.corruptApprovals
          st.ledger.deploymentId i).length dep i ab = some (L', out) ∧
      st' = { st with ledger := L' } := by
  unfold idealCustodyStep at h
  dsimp only at h
  cases hL : custodyLedgerSign S oracleSign st.ledger
      (custodyApprovers st.ledger.quorum.numParties st.honestApprovals st.corruptApprovals
        st.ledger.deploymentId i).length dep i ab with
  | none =>
    rw [hL] at h
    cases h
  | some r =>
    rcases r with ⟨L', out'⟩
    rw [hL] at h
    cases h
    exact ⟨L', rfl, rfl⟩

/-! ## 6. Safety invariant -/

/-- Safety invariant of the ideal custody functionality for deployment `dep₀`. -/
structure IdealCustodyState.SafeInv
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile)
    (st : IdealCustodyState PK D Sig) : Prop where
  /-- The deployment identifier, enrolled key and quorum profile never change. -/
  deployment : st.ledger.deploymentId = dep₀
  enrolled : st.ledger.enrolledPk = pk₀
  profile : st.ledger.quorum = quorum₀
  /-- Fewer than `threshold` parties are corrupted, each enrolled and listed once. -/
  corruptBudget : st.corruptParties.length < quorum₀.threshold
  corruptEnrolled : ∀ p ∈ st.corruptParties, p < quorum₀.numParties
  corruptNodup : st.corruptParties.Nodup
  /-- Every permit is for this deployment; adversarial permits belong to corrupted parties. -/
  honestBound : ∀ a ∈ st.honestApprovals, a.deploymentId = dep₀ ∧ a.party < quorum₀.numParties
  corruptBound : ∀ a ∈ st.corruptApprovals, a.deploymentId = dep₀ ∧ a.party ∈ st.corruptParties
  /-- The amount spent is the sum of `intent.spend` over the authorized intents, within budget. -/
  accounting : st.ledger.spent = (st.ledger.authorized.map CustodyIntent.spend).sum
  budget : st.ledger.spent ≤ quorum₀.spendCap
  sessions : st.ledger.usedSessions = st.ledger.authorized.map CustodyIntent.sessionId
  sessionsNodup : st.ledger.usedSessions.Nodup
  /-- Every authorized intent holds a permit recorded through an honest custodian's port. -/
  honestAuthorized : ∀ i ∈ st.ledger.authorized,
    ∃ p, p < quorum₀.numParties ∧ CustodyApproval.mk p dep₀ i ∈ st.honestApprovals
  /-- WAL records are below the epoch watermark, commit `digest dep₀ intent`, carry the oracle's
      signature on that digest, were authorized, and have pairwise distinct epochs. -/
  walFresh : ∀ r ∈ st.ledger.releasedHistory, r.intent.epoch < st.ledger.nextFreshEpoch
  walCommit : ∀ r ∈ st.ledger.releasedHistory,
    r.digest = S.digest dep₀ r.intent ∧ r.sig = oracleSign r.digest
  walAuthorized : ∀ r ∈ st.ledger.releasedHistory, r.intent ∈ st.ledger.authorized
  walNodup : (st.ledger.releasedHistory.map (fun r => r.intent.epoch)).Nodup
  /-- Until quarantine, the authorized intents are exactly the released ones. -/
  unpoisoned : st.ledger.poisoned = false →
    st.ledger.authorized = st.ledger.releasedHistory.map CustodyRelease.intent

omit [DecidableEq D] in
theorem IdealCustodyState.init_safeInv
    (S : CustodyDigestScheme D) (oracleSign : D → Sig)
    (dep₀ : Nat) (pk₀ : PK) (quorum₀ : CustodyQuorumProfile) :
    (IdealCustodyState.init dep₀ pk₀ quorum₀ : IdealCustodyState PK D Sig).SafeInv
      S oracleSign dep₀ pk₀ quorum₀ where
  deployment := rfl
  enrolled := rfl
  profile := rfl
  corruptBudget := quorum₀.h_pos
  corruptEnrolled := fun _ h => False.elim (List.not_mem_nil h)
  corruptNodup := List.Pairwise.nil
  honestBound := fun _ h => False.elim (List.not_mem_nil h)
  corruptBound := fun _ h => False.elim (List.not_mem_nil h)
  accounting := rfl
  budget := Nat.zero_le _
  sessions := rfl
  sessionsNodup := List.Pairwise.nil
  honestAuthorized := fun _ h => False.elim (List.not_mem_nil h)
  walFresh := fun _ h => False.elim (List.not_mem_nil h)
  walCommit := fun _ h => False.elim (List.not_mem_nil h)
  walAuthorized := fun _ h => False.elim (List.not_mem_nil h)
  walNodup := List.Pairwise.nil
  unpoisoned := fun _ => rfl

/-- An accepted fresh signing step (release or abort) has an approver that is enrolled, not
    corrupted at signing time, and whose permit for `(deploymentId, i)` came through its own port. -/
theorem idealCustodyStep_sign_fresh_has_honest_approver
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st st' : IdealCustodyState PK D Sig} {dep : Nat} {i : CustodyIntent} {ab : Bool}
    {out : CustodyOutcome Sig}
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hStep : idealCustodyStep S oracleSign st (.sign dep i ab) = some (st', out))
    (hFresh : findReleasedEpoch st.ledger.releasedHistory i.epoch = none) :
    dep = dep₀ ∧
    ∃ p, p < quorum₀.numParties ∧ p ∉ st.corruptParties ∧
      CustodyApproval.mk p dep₀ i ∈ st.honestApprovals := by
  obtain ⟨L', hL, _⟩ := idealCustodyStep_sign_inv hStep
  obtain ⟨_, hDep, hCase⟩ := custodyLedgerSign_inv hL
  refine ⟨hDep.trans hInv.deployment, ?_⟩
  rcases hCase with ⟨r, hF, _⟩ | ⟨_, _, _, hQ, _, _⟩
  · rw [hFresh] at hF
    cases hF
  · have hB : st.corruptParties.length < st.ledger.quorum.threshold := by
      rw [hInv.profile]
      exact hInv.corruptBudget
    obtain ⟨p, hp, hpC, hm⟩ :=
      custodyApprovers_honest_witness hB hQ (fun a ha => (hInv.corruptBound a ha).2)
    rw [hInv.profile] at hp
    rw [hInv.deployment] at hm
    exact ⟨p, hp, hpC, hm⟩

theorem idealCustodyStep_preserves_safeInv
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st st' : IdealCustodyState PK D Sig} {inp : CustodyInput} {out : CustodyOutcome Sig}
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hStep : idealCustodyStep S oracleSign st inp = some (st', out)) :
    st'.SafeInv S oracleSign dep₀ pk₀ quorum₀ := by
  cases inp with
  | approve p dep i =>
    obtain ⟨hg, hSt, _⟩ := idealCustodyStep_approve_inv hStep
    subst hSt
    exact { hInv with
      honestBound := fun a ha => by
        rcases List.mem_cons.mp ha with hEq | hTail
        · rw [hEq]
          exact ⟨hg.2.2.trans hInv.deployment, hInv.profile ▸ hg.1⟩
        · exact hInv.honestBound a hTail
      honestAuthorized := fun j hj => by
        obtain ⟨q, hq, hm⟩ := hInv.honestAuthorized j hj
        exact ⟨q, hq, List.mem_cons_of_mem _ hm⟩ }
  | advApprove p dep i =>
    obtain ⟨hg, hSt, _⟩ := idealCustodyStep_advApprove_inv hStep
    subst hSt
    exact { hInv with
      corruptBound := fun a ha => by
        rcases List.mem_cons.mp ha with hEq | hTail
        · rw [hEq]
          exact ⟨hg.2.trans hInv.deployment, hg.1⟩
        · exact hInv.corruptBound a hTail }
  | corrupt p =>
    obtain ⟨hg, hSt, _⟩ := idealCustodyStep_corrupt_inv hStep
    subst hSt
    exact { hInv with
      corruptBudget := hInv.profile ▸ hg.2.2
      corruptEnrolled := fun q hq => by
        rcases List.mem_cons.mp hq with hEq | hTail
        · rw [hEq]
          exact hInv.profile ▸ hg.1
        · exact hInv.corruptEnrolled q hTail
      corruptNodup := List.nodup_cons.mpr ⟨hg.2.1, hInv.corruptNodup⟩
      corruptBound := fun a ha =>
        ⟨(hInv.corruptBound a ha).1, List.mem_cons_of_mem _ (hInv.corruptBound a ha).2⟩ }
  | sign dep i ab =>
    obtain ⟨L', hL, hSt⟩ := idealCustodyStep_sign_inv hStep
    obtain ⟨hUnp, _, hCase⟩ := custodyLedgerSign_inv hL
    rcases hCase with ⟨r, _, _, hSame, _⟩ | ⟨hFresh, hEp, hSess, _, hCap, hAb⟩
    · subst hSame
      subst hSt
      exact hInv
    · obtain ⟨_, p, hp, _, hm⟩ :=
        idealCustodyStep_sign_fresh_has_honest_approver hInv hStep hFresh
      have hCap' : st.ledger.spent + i.spend ≤ quorum₀.spendCap := hInv.profile ▸ hCap
      have hAcc : st.ledger.spent + i.spend =
          ((i :: st.ledger.authorized).map CustodyIntent.spend).sum := by
        rw [List.map_cons, List.sum_cons, ← hInv.accounting, Nat.add_comm]
      have hHonest : ∀ j ∈ i :: st.ledger.authorized,
          ∃ q, q < quorum₀.numParties ∧ CustodyApproval.mk q dep₀ j ∈ st.honestApprovals :=
        fun j hj => by
          rcases List.mem_cons.mp hj with hEq | hTail
          · rw [hEq]
            exact ⟨p, hp, hm⟩
          · exact hInv.honestAuthorized j hTail
      have hOld : ∀ r ∈ st.ledger.releasedHistory, r.intent.epoch < i.epoch + 1 := fun r hr =>
        Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt (hInv.walFresh r hr)) hEp)
      rcases hAb with ⟨_, hL', _⟩ | ⟨_, hL', _⟩
      · subst hL'
        subst hSt
        exact { hInv with
          accounting := hAcc
          budget := hCap'
          sessions := congrArg (List.cons i.sessionId) hInv.sessions
          sessionsNodup := List.nodup_cons.mpr ⟨hSess, hInv.sessionsNodup⟩
          honestAuthorized := hHonest
          walFresh := hOld
          walAuthorized := fun r hr => List.mem_cons_of_mem _ (hInv.walAuthorized r hr)
          unpoisoned := fun h => Bool.noConfusion (show true = false from h) }
      · subst hL'
        subst hSt
        exact { hInv with
          accounting := hAcc
          budget := hCap'
          sessions := congrArg (List.cons i.sessionId) hInv.sessions
          sessionsNodup := List.nodup_cons.mpr ⟨hSess, hInv.sessionsNodup⟩
          honestAuthorized := hHonest
          walFresh := fun r hr => by
            rcases List.mem_cons.mp hr with hEq | hTail
            · rw [hEq]
              exact Nat.lt_succ_self _
            · exact hOld r hTail
          walCommit := fun r hr => by
            rcases List.mem_cons.mp hr with hEq | hTail
            · rw [hEq]
              exact ⟨congrArg (fun d => S.digest d i) hInv.deployment, rfl⟩
            · exact hInv.walCommit r hTail
          walAuthorized := fun r hr => by
            rcases List.mem_cons.mp hr with hEq | hTail
            · rw [hEq]
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hInv.walAuthorized r hTail)
          walNodup := List.nodup_cons.mpr ⟨fun hm' => by
            obtain ⟨r, hr, he⟩ := List.mem_map.mp hm'
            have h1 : r.intent.epoch < st.ledger.nextFreshEpoch := hInv.walFresh r hr
            rw [he] at h1
            exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 hEp), hInv.walNodup⟩
          unpoisoned := fun _ => congrArg (List.cons i) (hInv.unpoisoned hUnp) }

/-- The invariant holds along every valid trace, corruption steps and rejected inputs included. -/
theorem idealCustody_validTrace_safeInv
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s s' : IdealCustodyState PK D Sig} {tr : List (CustodyInput × CustodyOutcome Sig)}
    (hInv : s.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s tr s') :
    s'.SafeInv S oracleSign dep₀ pk₀ quorum₀ := by
  induction hTr with
  | nil _ => exact hInv
  | accept hStep _ ih => exact ih (idealCustodyStep_preserves_safeInv hInv hStep)
  | reject _ _ _ ih => exact ih hInv

theorem idealCustody_reachable_safeInv
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st : IdealCustodyState PK D Sig}
    (hR : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable st) :
    st.SafeInv S oracleSign dep₀ pk₀ quorum₀ := by
  obtain ⟨s₀, tr, hInit, hTr⟩ := hR
  have h0 : s₀ = IdealCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  exact idealCustody_validTrace_safeInv
    (IdealCustodyState.init_safeInv S oracleSign dep₀ pk₀ quorum₀) hTr

/-! ## 7. Expenditure, authorization and WAL identity on reachable states -/

/-- Cumulative spend is the sum of `intent.spend` over the authorized intents, never exceeds the
    budget, every authorized intent holds an honest custodian's permit for this deployment, and
    before quarantine the authorized intents are exactly the released ones. -/
theorem idealCustody_reachable_spend_accounting
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st : IdealCustodyState PK D Sig}
    (hR : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable st) :
    st.ledger.spent = (st.ledger.authorized.map CustodyIntent.spend).sum ∧
    st.ledger.spent ≤ quorum₀.spendCap ∧
    (∀ i ∈ st.ledger.authorized,
      ∃ p, p < quorum₀.numParties ∧ CustodyApproval.mk p dep₀ i ∈ st.honestApprovals) ∧
    (st.ledger.poisoned = false →
      st.ledger.spent =
        ((st.ledger.releasedHistory.map CustodyRelease.intent).map CustodyIntent.spend).sum) := by
  have hInv := idealCustody_reachable_safeInv hR
  refine ⟨hInv.accounting, hInv.budget, hInv.honestAuthorized, fun hU => ?_⟩
  rw [← hInv.unpoisoned hU]
  exact hInv.accounting

/-- Every released signature on a reachable state is the oracle's signature on
    `digest dep₀ intent` for an intent approved through an honest custodian's port. -/
theorem idealCustody_reachable_release_honestly_approved
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st : IdealCustodyState PK D Sig} {r : CustodyRelease D Sig}
    (hR : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Reachable st)
    (hRel : r ∈ st.ledger.releasedHistory) :
    r.sig = oracleSign (S.digest dep₀ r.intent) ∧
    ∃ p, p < quorum₀.numParties ∧ CustodyApproval.mk p dep₀ r.intent ∈ st.honestApprovals := by
  have hInv := idealCustody_reachable_safeInv hR
  obtain ⟨hDig, hSig⟩ := hInv.walCommit r hRel
  refine ⟨?_, hInv.honestAuthorized _ (hInv.walAuthorized r hRel)⟩
  rw [hSig, hDig]

omit [DecidableEq D] in
/-- WAL identity: a committed digest determines the deployment and the whole intent. -/
theorem idealCustody_wal_digest_binds
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st : IdealCustodyState PK D Sig} {r : CustodyRelease D Sig}
    {dep : Nat} {i : CustodyIntent}
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hRel : r ∈ st.ledger.releasedHistory)
    (hDig : S.digest dep i = r.digest) :
    dep = dep₀ ∧ i = r.intent :=
  S.digest_inj (hDig.trans (hInv.walCommit r hRel).1)

/-- A fresh release charges exactly `i.spend`, signs `digest deploymentId i`, and logs `i`. -/
theorem idealCustodyStep_release_spec
    {st st' : IdealCustodyState PK D Sig} {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hStep : idealCustodyStep S oracleSign st (.sign dep i ab) = some (st', .released sig)) :
    dep = st.ledger.deploymentId ∧
    sig = oracleSign (S.digest st.ledger.deploymentId i) ∧
    st'.ledger.spent = st.ledger.spent + i.spend ∧
    i ∈ st'.ledger.authorized ∧
    st.ledger.quorum.threshold ≤
      (custodyApprovers st.ledger.quorum.numParties st.honestApprovals st.corruptApprovals
        st.ledger.deploymentId i).length := by
  obtain ⟨L', hL, hSt⟩ := idealCustodyStep_sign_inv hStep
  obtain ⟨_, hDep, hCase⟩ := custodyLedgerSign_inv hL
  rcases hCase with ⟨r, _, _, _, hOut⟩ | ⟨_, _, _, hQ, _, hAb⟩
  · cases hOut
  · rcases hAb with ⟨_, _, hOut⟩ | ⟨_, hL', hOut⟩
    · cases hOut
    · subst hL'
      subst hSt
      cases hOut
      exact ⟨hDep, rfl, rfl, List.mem_cons_self, hQ⟩

/-- A WAL replay returns the committed signature of the same full intent and changes nothing. -/
theorem idealCustodyStep_replay_binds_intent
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st st' : IdealCustodyState PK D Sig} {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hStep : idealCustodyStep S oracleSign st (.sign dep i ab) = some (st', .replayedFromWal sig)) :
    st' = st ∧ dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ r ∈ st.ledger.releasedHistory, r.intent = i ∧ r.sig = sig := by
  obtain ⟨L', hL, hSt⟩ := idealCustodyStep_sign_inv hStep
  obtain ⟨_, hDep, hCase⟩ := custodyLedgerSign_inv hL
  rcases hCase with ⟨r, hF, hDig, hSame, hOut⟩ | ⟨_, _, _, _, _, hAb⟩
  · subst hSame
    subst hSt
    cases hOut
    obtain ⟨hMem, _⟩ := findReleasedEpoch_some hF
    obtain ⟨hCommit, hSig⟩ := hInv.walCommit r hMem
    have hI : i = r.intent := (S.digest_inj (hDig.trans hCommit)).2
    refine ⟨rfl, hDep.trans hInv.deployment, ?_, r, hMem, hI.symm, rfl⟩
    rw [hSig, hCommit, hI]
  · rcases hAb with ⟨_, _, hOut⟩ | ⟨_, _, hOut⟩
    · cases hOut
    · cases hOut

/-- Multi-epoch WAL retry and conflict rejection: retrying the committed intent of any committed
    epoch replays its signature without changing the state, and any other intent at that epoch
    (a different payload, spend, round or session) is rejected. -/
theorem idealCustodyStep_wal_retry_and_conflict
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (st : IdealCustodyState PK D Sig) (r : CustodyRelease D Sig)
    (iConflict : CustodyIntent) (abRetry abConflict : Bool)
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hUnpoisoned : st.ledger.poisoned = false)
    (hCommitted : r ∈ st.ledger.releasedHistory)
    (hConfEp : iConflict.epoch = r.intent.epoch) (hConfDiff : iConflict ≠ r.intent) :
    idealCustodyStep S oracleSign st (.sign dep₀ r.intent abRetry) =
      some (st, .replayedFromWal r.sig) ∧
    idealCustodyStep S oracleSign st (.sign dep₀ iConflict abConflict) = none := by
  have hLookup := findReleasedEpoch_of_mem_nodup hCommitted hInv.walNodup
  have hCommit := (hInv.walCommit r hCommitted).1
  have hDig : S.digest st.ledger.deploymentId r.intent = r.digest := by
    rw [hInv.deployment]
    exact hCommit.symm
  have hLookup' : findReleasedEpoch st.ledger.releasedHistory iConflict.epoch = some r := by
    rw [hConfEp]
    exact hLookup
  have hNe : ¬ (S.digest st.ledger.deploymentId iConflict = r.digest) := fun hEq =>
    hConfDiff (S.digest_inj (hEq.trans hCommit)).2
  refine ⟨?_, ?_⟩
  · unfold idealCustodyStep
    dsimp only
    rw [custodyLedgerSign_of_found hUnpoisoned hInv.deployment.symm hLookup, custody_if_pos hDig]
    rfl
  · unfold idealCustodyStep
    dsimp only
    rw [custodyLedgerSign_of_found hUnpoisoned hInv.deployment.symm hLookup', custody_if_neg hNe]
    rfl

/-- Sticky quarantine: once poisoned, the functionality refuses every signing request. -/
theorem idealCustodyStep_poisoned_rejects
    (st : IdealCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) (ab : Bool)
    (hPois : st.ledger.poisoned = true) :
    idealCustodyStep S oracleSign st (.sign dep i ab) = none := by
  unfold idealCustodyStep
  dsimp only
  unfold custodyLedgerSign
  rw [custody_if_neg (fun h => Bool.noConfusion (hPois.symm.trans h.1))]
  rfl

/-! ## 8. Rejection of unauthorized behaviour -/

/-- No honest permit for exactly this `(deployment, intent)`, no signature: naming parties does
    not help, and a permit for a different intent (e.g. the same payload with another `spend`)
    does not count. -/
theorem idealCustodyStep_sign_unapproved_rejected
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    (st : IdealCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) (ab : Bool)
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hNone : ∀ p, CustodyApproval.mk p dep₀ i ∉ st.honestApprovals)
    (hFresh : findReleasedEpoch st.ledger.releasedHistory i.epoch = none) :
    idealCustodyStep S oracleSign st (.sign dep i ab) = none := by
  cases hS : idealCustodyStep S oracleSign st (.sign dep i ab) with
  | none => rfl
  | some res =>
    rcases res with ⟨st', out⟩
    obtain ⟨_, p, _, _, hm⟩ := idealCustodyStep_sign_fresh_has_honest_approver hInv hS hFresh
    exact absurd hm (hNone p)

/-- Deployment binding of the signing port. -/
theorem idealCustodyStep_sign_wrong_deployment_rejected
    (st : IdealCustodyState PK D Sig) (dep : Nat) (i : CustodyIntent) (ab : Bool)
    (hDep : dep ≠ st.ledger.deploymentId) :
    idealCustodyStep S oracleSign st (.sign dep i ab) = none := by
  unfold idealCustodyStep
  dsimp only
  unfold custodyLedgerSign
  rw [custody_if_neg (fun h => hDep h.2)]
  rfl

/-- Deployment binding of the permits: an approval for another deployment is not recorded. -/
theorem idealCustodyStep_approve_wrong_deployment_rejected
    (st : IdealCustodyState PK D Sig) (p dep : Nat) (i : CustodyIntent)
    (hDep : dep ≠ st.ledger.deploymentId) :
    idealCustodyStep S oracleSign st (.approve p dep i) = none := by
  unfold idealCustodyStep
  dsimp only
  exact custody_if_neg (fun h => hDep h.2.2) _ _

/-- The corruption budget: a corruption that would reach `threshold` is refused. -/
theorem idealCustodyStep_corrupt_over_budget_rejected
    (st : IdealCustodyState PK D Sig) (p : Nat)
    (hFull : st.ledger.quorum.threshold ≤ st.corruptParties.length + 1) :
    idealCustodyStep S oracleSign st (.corrupt p) = none := by
  unfold idealCustodyStep
  dsimp only
  exact custody_if_neg (fun h => Nat.not_le_of_gt h.2.2 hFull) _ _

/-- After corruption the party's own port is closed. -/
theorem idealCustodyStep_approve_corrupted_rejected
    (st : IdealCustodyState PK D Sig) (p dep : Nat) (i : CustodyIntent)
    (hCorrupt : p ∈ st.corruptParties) :
    idealCustodyStep S oracleSign st (.approve p dep i) = none := by
  unfold idealCustodyStep
  dsimp only
  exact custody_if_neg (fun h => h.2.1 hCorrupt) _ _

/-- The adversary cannot record a permit for a party it has not corrupted. -/
theorem idealCustodyStep_advApprove_honest_rejected
    (st : IdealCustodyState PK D Sig) (p dep : Nat) (i : CustodyIntent)
    (hHonest : p ∉ st.corruptParties) :
    idealCustodyStep S oracleSign st (.advApprove p dep i) = none := by
  unfold idealCustodyStep
  dsimp only
  exact custody_if_neg (fun h => hHonest h.1) _ _

/-! ## 9. Trace-level provenance -/

/-- A permit in the honest list after a step was there before, or the step is that party's own
    `.approve` for this deployment, taken while the party was enrolled and not corrupted. -/
theorem idealCustodyStep_honestApproval_provenance
    {st st' : IdealCustodyState PK D Sig} {inp : CustodyInput} {out : CustodyOutcome Sig}
    {a : CustodyApproval}
    (hStep : idealCustodyStep S oracleSign st inp = some (st', out))
    (ha : a ∈ st'.honestApprovals) :
    a ∈ st.honestApprovals ∨
    (inp = .approve a.party a.deploymentId a.intent ∧ out = .approvalRecorded ∧
      a.party ∉ st.corruptParties ∧ a.party < st.ledger.quorum.numParties ∧
      a.deploymentId = st.ledger.deploymentId) := by
  cases inp with
  | approve p dep i =>
    obtain ⟨hg, hSt, hOut⟩ := idealCustodyStep_approve_inv hStep
    subst hSt
    rcases List.mem_cons.mp ha with hEq | hTail
    · subst hEq
      exact .inr ⟨rfl, hOut, hg.2.1, hg.1, hg.2.2⟩
    · exact .inl hTail
  | advApprove p dep i =>
    obtain ⟨_, hSt, _⟩ := idealCustodyStep_advApprove_inv hStep
    subst hSt
    exact .inl ha
  | corrupt p =>
    obtain ⟨_, hSt, _⟩ := idealCustodyStep_corrupt_inv hStep
    subst hSt
    exact .inl ha
  | sign dep i ab =>
    obtain ⟨L', _, hSt⟩ := idealCustodyStep_sign_inv hStep
    subst hSt
    exact .inl ha

private theorem idealCustodyStep_authorized_mono
    {st st' : IdealCustodyState PK D Sig} {inp : CustodyInput} {out : CustodyOutcome Sig}
    {j : CustodyIntent}
    (hStep : idealCustodyStep S oracleSign st inp = some (st', out))
    (hj : j ∈ st.ledger.authorized) : j ∈ st'.ledger.authorized := by
  cases inp with
  | approve p dep i =>
    obtain ⟨_, hSt, _⟩ := idealCustodyStep_approve_inv hStep
    subst hSt
    exact hj
  | advApprove p dep i =>
    obtain ⟨_, hSt, _⟩ := idealCustodyStep_advApprove_inv hStep
    subst hSt
    exact hj
  | corrupt p =>
    obtain ⟨_, hSt, _⟩ := idealCustodyStep_corrupt_inv hStep
    subst hSt
    exact hj
  | sign dep i ab =>
    obtain ⟨L', hL, hSt⟩ := idealCustodyStep_sign_inv hStep
    obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv hL
    subst hSt
    rcases hCase with ⟨r, _, _, hSame, _⟩ | ⟨_, _, _, _, _, hAb⟩
    · subst hSame
      exact hj
    · rcases hAb with ⟨_, hL', _⟩ | ⟨_, hL', _⟩
      · subst hL'
        exact List.mem_cons_of_mem _ hj
      · subst hL'
        exact List.mem_cons_of_mem _ hj

private theorem idealCustody_validTrace_authorized_mono
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s s' : IdealCustodyState PK D Sig} {tr : List (CustodyInput × CustodyOutcome Sig)}
    {j : CustodyIntent}
    (hj : j ∈ s.ledger.authorized)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s tr s') :
    j ∈ s'.ledger.authorized := by
  induction hTr with
  | nil _ => exact hj
  | accept hStep _ ih => exact ih (idealCustodyStep_authorized_mono hStep hj)
  | reject _ _ _ ih => exact ih hj

/-- Honest permits present at the end of a trace were present at its start or were recorded by an
    accepted `.approve` event of the trace. -/
theorem idealCustody_validTrace_honestApproval_provenance
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s s' : IdealCustodyState PK D Sig} {tr : List (CustodyInput × CustodyOutcome Sig)}
    {a : CustodyApproval}
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s tr s')
    (ha : a ∈ s'.honestApprovals) :
    a ∈ s.honestApprovals ∨
    (CustodyInput.approve a.party a.deploymentId a.intent,
      (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ tr := by
  induction hTr with
  | nil _ => exact .inl ha
  | accept hStep _ ih =>
    rcases ih ha with hMid | hEv
    · rcases idealCustodyStep_honestApproval_provenance hStep hMid with hOld | ⟨hInp, hOut, _⟩
      · exact .inl hOld
      · rw [hInp, hOut]
        exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ hEv)
  | reject _ _ _ ih => exact ih ha

/-- A `.released` event of a trace is for this deployment, carries the oracle's signature on
    `digest dep₀ i`, and leaves `i` in the authorized log at the end of the trace. -/
theorem idealCustody_validTrace_release_authorized
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s s' : IdealCustodyState PK D Sig} {tr : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hInv : s.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s tr s')
    (hEv : (CustodyInput.sign dep i ab, CustodyOutcome.released sig) ∈ tr) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧ i ∈ s'.ledger.authorized := by
  induction hTr with
  | nil _ => exact False.elim (List.not_mem_nil hEv)
  | accept hStep hRest ih =>
    rcases List.mem_cons.mp hEv with hEq | hTail
    · cases hEq
      obtain ⟨hDep, hSig, _, hAuth, _⟩ := idealCustodyStep_release_spec hStep
      refine ⟨hDep.trans hInv.deployment, ?_, idealCustody_validTrace_authorized_mono hAuth hRest⟩
      rw [hSig, hInv.deployment]
    · exact ih (idealCustodyStep_preserves_safeInv hInv hStep) hTail
  | reject _ _ _ ih => exact ih hInv hEv

/-- **Honest authorization of every emitted signature.** In any trace of the ideal custody
    functionality from its initial state, a released signature is the oracle's signature on
    `digest dep₀ i`, and the same trace contains an accepted `.approve p dep₀ i` by an enrolled
    party `p` (accepted only while `p` was not corrupted). -/
theorem idealCustody_trace_release_honestly_approved
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s₀ s : IdealCustodyState PK D Sig} {tr : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hInit : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Init s₀)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s₀ tr s)
    (hEv : (CustodyInput.sign dep i ab, CustodyOutcome.released sig) ∈ tr) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyInput.approve p dep₀ i, (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ tr := by
  have h0 : s₀ = IdealCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  have hInv0 := IdealCustodyState.init_safeInv (PK := PK) S oracleSign dep₀ pk₀ quorum₀
  obtain ⟨hDep, hSig, hAuth⟩ := idealCustody_validTrace_release_authorized hInv0 hTr hEv
  obtain ⟨p, hp, hm⟩ := (idealCustody_validTrace_safeInv hInv0 hTr).honestAuthorized i hAuth
  refine ⟨hDep, hSig, p, hp, ?_⟩
  rcases idealCustody_validTrace_honestApproval_provenance hTr hm with hOld | hEvA
  · exact False.elim (List.not_mem_nil hOld)
  · exact hEvA

/-- The same statement for admitted traces, in the form transported by `Refines`. -/
theorem idealCustody_admitsTrace_release_honestly_approved
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {tr : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {sig : Sig}
    (hAdmits : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).AdmitsTrace tr)
    (hEv : (CustodyInput.sign dep i ab, CustodyOutcome.released sig) ∈ tr) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyInput.approve p dep₀ i, (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ tr := by
  obtain ⟨s₀, s, hInit, hTr⟩ := hAdmits
  exact idealCustody_trace_release_honestly_approved hInit hTr hEv

/-- An accepted signing step that outputs a signature (fresh release or WAL replay) is for this
    deployment, outputs the oracle's signature on `digest dep₀ i`, and finds a permit for
    `(dep₀, i)` already recorded through an enrolled custodian's own port. -/
theorem idealCustodyStep_sign_output_honest
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {st st' : IdealCustodyState PK D Sig} {dep : Nat} {i : CustodyIntent} {ab : Bool}
    {out : CustodyOutcome Sig} {sig : Sig}
    (hInv : st.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hStep : idealCustodyStep S oracleSign st (.sign dep i ab) = some (st', out))
    (hOut : out = .released sig ∨ out = .replayedFromWal sig) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧ CustodyApproval.mk p dep₀ i ∈ st.honestApprovals := by
  rcases hOut with hO | hO
  · subst hO
    obtain ⟨hD, hSig, _, _, _⟩ := idealCustodyStep_release_spec hStep
    obtain ⟨L', hL, _⟩ := idealCustodyStep_sign_inv hStep
    obtain ⟨_, _, hCase⟩ := custodyLedgerSign_inv hL
    rcases hCase with ⟨r, _, _, _, hBad⟩ | ⟨hF, _⟩
    · cases hBad
    · obtain ⟨_, p, hp, _, hm⟩ := idealCustodyStep_sign_fresh_has_honest_approver hInv hStep hF
      refine ⟨hD.trans hInv.deployment, ?_, p, hp, hm⟩
      rw [hSig, hInv.deployment]
  · subst hO
    obtain ⟨_, hD, hSig, r, hr, hI, _⟩ := idealCustodyStep_replay_binds_intent hInv hStep
    obtain ⟨p, hp, hm⟩ := hInv.honestAuthorized _ (hInv.walAuthorized r hr)
    rw [hI] at hm
    exact ⟨hD, hSig, p, hp, hm⟩

/-- Along a trace from a state satisfying the invariant, every signature output (fresh release or
    WAL replay) for `i` is preceded by an honest permit for `(dep₀, i)`: one already recorded in the
    starting state, or an accepted `.approve p dep₀ i` strictly earlier in the trace. -/
theorem idealCustody_validTrace_signature_approved_before
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s s' : IdealCustodyState PK D Sig} {tr pre post : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {out : CustodyOutcome Sig} {sig : Sig}
    (hInv : s.SafeInv S oracleSign dep₀ pk₀ quorum₀)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s tr s')
    (hSplit : tr = pre ++ (CustodyInput.sign dep i ab, out) :: post)
    (hOut : out = .released sig ∨ out = .replayedFromWal sig) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyApproval.mk p dep₀ i ∈ s.honestApprovals ∨
       (CustodyInput.approve p dep₀ i,
         (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ pre) := by
  induction hTr generalizing pre with
  | nil _ => cases pre <;> cases hSplit
  | @accept a a1 _ inp o rest hStep _ ih =>
    cases pre with
    | nil =>
      rw [List.nil_append] at hSplit
      have hHead := (List.cons.inj hSplit).1
      cases hHead
      obtain ⟨hD, hS, p, hp, hm⟩ := idealCustodyStep_sign_output_honest hInv hStep hOut
      exact ⟨hD, hS, p, hp, .inl hm⟩
    | cons x pre' =>
      rw [List.cons_append] at hSplit
      have hx : (inp, o) = x := (List.cons.inj hSplit).1
      obtain ⟨hD, hS, p, hp, hm⟩ :=
        ih (idealCustodyStep_preserves_safeInv hInv hStep) (List.cons.inj hSplit).2
      refine ⟨hD, hS, p, hp, ?_⟩
      rcases hm with hm | hm
      · rcases idealCustodyStep_honestApproval_provenance hStep hm with hOld | ⟨hI, hO, _⟩
        · exact .inl hOld
        · refine .inr ?_
          rw [← hx, hI, hO]
          exact List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ hm)
  | reject _ _ _ ih => exact ih hInv hSplit

/-- **Every signature output is preceded by an honest approval.** In any trace of the ideal
    custody functionality from its initial state, a signature output for `i` (fresh release or WAL
    replay) is the oracle's signature on `digest dep₀ i`, and an accepted `.approve p dep₀ i` by an
    enrolled party `p` occurs strictly earlier in the trace. -/
theorem idealCustody_trace_signature_approved_before
    {dep₀ : Nat} {pk₀ : PK} {quorum₀ : CustodyQuorumProfile}
    {s₀ s : IdealCustodyState PK D Sig} {tr pre post : List (CustodyInput × CustodyOutcome Sig)}
    {dep : Nat} {i : CustodyIntent} {ab : Bool} {out : CustodyOutcome Sig} {sig : Sig}
    (hInit : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).Init s₀)
    (hTr : (idealCustodyMachine S oracleSign dep₀ pk₀ quorum₀).ValidTrace s₀ tr s)
    (hSplit : tr = pre ++ (CustodyInput.sign dep i ab, out) :: post)
    (hOut : out = .released sig ∨ out = .replayedFromWal sig) :
    dep = dep₀ ∧ sig = oracleSign (S.digest dep₀ i) ∧
    ∃ p, p < quorum₀.numParties ∧
      (CustodyInput.approve p dep₀ i,
        (CustodyOutcome.approvalRecorded : CustodyOutcome Sig)) ∈ pre := by
  have h0 : s₀ = IdealCustodyState.init dep₀ pk₀ quorum₀ := hInit
  subst h0
  obtain ⟨hD, hS, p, hp, hm⟩ := idealCustody_validTrace_signature_approved_before
    (IdealCustodyState.init_safeInv (PK := PK) S oracleSign dep₀ pk₀ quorum₀) hTr hSplit hOut
  rcases hm with hm | hm
  · exact False.elim (List.not_mem_nil hm)
  · exact ⟨hD, hS, p, hp, hm⟩

end Step

/-! ## 10. Concrete instance: 2-of-3 custody for deployment `7`, budget `100` -/

/-- 2-of-3 quorum with spend cap `100`. -/
def custodyToothQuorum : CustodyQuorumProfile :=
  { numParties := 3, threshold := 2, spendCap := 100, h_pos := by decide, h_le := by decide }

/-- An intent spending `40`. -/
def custodyToothIntent : CustodyIntent :=
  { sessionId := 1, round := 0, epoch := 0, spend := 40, payload := [0x51, 0x53] }

/-- State reached from the initial state of deployment `7` by feeding `inps` in order. -/
def custodyToothRun (inps : List CustodyInput) :
    IdealCustodyState Unit (Nat × CustodyIntent) (Nat × CustodyIntent) :=
  inps.foldl
    (fun s inp =>
      ((idealCustodyMachine CustodyDigestScheme.transparent id 7 () custodyToothQuorum).runStep
        s inp).1)
    (IdealCustodyState.init 7 () custodyToothQuorum)

/-- With two honest approvals of the intent, signing releases the signature on
    `digest 7 intent` and charges `intent.spend = 40`. -/
theorem idealCustody_tooth_quorum_releases :
    (idealCustodyStep CustodyDigestScheme.transparent id
      (custodyToothRun [.approve 0 7 custodyToothIntent, .approve 1 7 custodyToothIntent])
      (.sign 7 custodyToothIntent false)).map (fun r => (r.1.ledger.spent, r.2)) =
    some (40, .released (7, custodyToothIntent)) := by
  decide +kernel

/-- Audit counterexample `spend := 0`: the two custodians approved the intent spending `40`; the
    same payload, session and epoch with `spend := 0` has no permit and is refused. -/
theorem idealCustody_tooth_zero_spend_rejected :
    ¬ ((idealCustodyStep CustodyDigestScheme.transparent id
        (custodyToothRun [.approve 0 7 custodyToothIntent, .approve 1 7 custodyToothIntent])
        (.sign 7 { custodyToothIntent with spend := 0 } false)).isSome = true) := by
  decide +kernel

/-- Audit counterexample "named but never approved": with one corrupted party voting and no
    honest custodian having approved, signing is refused. -/
theorem idealCustody_tooth_unapproved_rejected :
    ¬ ((idealCustodyStep CustodyDigestScheme.transparent id
        (custodyToothRun [.corrupt 2, .advApprove 2 7 custodyToothIntent])
        (.sign 7 custodyToothIntent false)).isSome = true) := by
  decide +kernel

/-- A second corruption would reach the threshold `2` and is refused. -/
theorem idealCustody_tooth_corruption_over_budget :
    ¬ ((idealCustodyStep CustodyDigestScheme.transparent id
        (custodyToothRun [.corrupt 2]) (.corrupt 1)).isSome = true) := by
  decide +kernel

/-- Permits for deployment `7` do not authorize a signature for deployment `8`. -/
theorem idealCustody_tooth_wrong_deployment_rejected :
    ¬ ((idealCustodyStep CustodyDigestScheme.transparent id
        (custodyToothRun [.approve 0 7 custodyToothIntent, .approve 1 7 custodyToothIntent])
        (.sign 8 custodyToothIntent false)).isSome = true) := by
  decide +kernel

#verify_constructive
  Qsag.Spec.findReleasedEpoch_some
  Qsag.Spec.findReleasedEpoch_of_mem_nodup
  Qsag.Spec.custodyApprovers_nodup
  Qsag.Spec.mem_custodyApprovers
  Qsag.Spec.custodyApprovers_honest_witness
  Qsag.Spec.custodyRevealed_mem
  Qsag.Spec.custodyLedgerSign_inv
  Qsag.Spec.idealCustodyStep_approve_inv
  Qsag.Spec.idealCustodyStep_advApprove_inv
  Qsag.Spec.idealCustodyStep_corrupt_inv
  Qsag.Spec.idealCustodyStep_sign_inv
  Qsag.Spec.IdealCustodyState.init_safeInv
  Qsag.Spec.idealCustodyStep_sign_fresh_has_honest_approver
  Qsag.Spec.idealCustodyStep_preserves_safeInv
  Qsag.Spec.idealCustody_validTrace_safeInv
  Qsag.Spec.idealCustody_reachable_safeInv
  Qsag.Spec.idealCustody_reachable_spend_accounting
  Qsag.Spec.idealCustody_reachable_release_honestly_approved
  Qsag.Spec.idealCustody_wal_digest_binds
  Qsag.Spec.idealCustodyStep_release_spec
  Qsag.Spec.idealCustodyStep_replay_binds_intent
  Qsag.Spec.idealCustodyStep_wal_retry_and_conflict
  Qsag.Spec.idealCustodyStep_poisoned_rejects
  Qsag.Spec.idealCustodyStep_sign_unapproved_rejected
  Qsag.Spec.idealCustodyStep_sign_wrong_deployment_rejected
  Qsag.Spec.idealCustodyStep_approve_wrong_deployment_rejected
  Qsag.Spec.idealCustodyStep_corrupt_over_budget_rejected
  Qsag.Spec.idealCustodyStep_approve_corrupted_rejected
  Qsag.Spec.idealCustodyStep_advApprove_honest_rejected
  Qsag.Spec.idealCustodyStep_honestApproval_provenance
  Qsag.Spec.idealCustody_validTrace_honestApproval_provenance
  Qsag.Spec.idealCustody_validTrace_release_authorized
  Qsag.Spec.idealCustody_trace_release_honestly_approved
  Qsag.Spec.idealCustody_admitsTrace_release_honestly_approved
  Qsag.Spec.custodyLedgerSign_mono
  Qsag.Spec.custodyApprovers_length_le_of_subset
  Qsag.Spec.idealCustodyStep_sign_output_honest
  Qsag.Spec.idealCustody_validTrace_signature_approved_before
  Qsag.Spec.idealCustody_trace_signature_approved_before
  Qsag.Spec.idealCustody_tooth_quorum_releases

#tooth_pair Qsag.Spec.idealCustody_reachable_spend_accounting vs
  Qsag.Spec.idealCustody_tooth_zero_spend_rejected
#tooth_pair Qsag.Spec.idealCustody_trace_release_honestly_approved vs
  Qsag.Spec.idealCustody_tooth_unapproved_rejected
#tooth_pair Qsag.Spec.idealCustodyStep_corrupt_inv vs
  Qsag.Spec.idealCustody_tooth_corruption_over_budget
#tooth_pair Qsag.Spec.idealCustody_wal_digest_binds vs
  Qsag.Spec.idealCustody_tooth_wrong_deployment_rejected
#tooth_pair Qsag.Spec.idealCustodyStep_sign_fresh_has_honest_approver vs
  Qsag.Spec.idealCustodyStep_sign_unapproved_rejected

end Qsag.Spec
end
