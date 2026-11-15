module
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssParticipantGateWeights
import all Qsag.Exec.RssSigningBackend
import all Qsag.Exec.RssSigningHashCalls
import all Qsag.Exec.RssParticipantGateWeights
import all Qsag.Exec.RssParticipantGateChecks
import all Qsag.Exec.RssParticipantMachine
import all Qsag.Exec.RssParticipantKeccak
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.Rss256TernaryRound
import Qsag.Tactic.AssuranceKit

/-! Exact extraction from retained participant histories. The extraction is a
private global observer, NOT an implemented distributed consistency protocol.
It rejects unequal lengths, mismatched round identifiers/constants, replicated
operands and received outputs. Products are deliberately NOT tested here: they
are the committed relation inputs to the weighted checker.

Each extracted UInt64 is one sponge's Keccak lane (64 bit positions). The Rust
packed64 transpose swaps those positions with sponge-instance bits. Coordinates
below make that distinction explicit; no packed64 correspondence is inferred.
-/
public section
namespace Qsag.RssParticipant.GateChecks
open Rss256ProductProof
set_option autoImplicit false
set_option maxRecDepth 8192

abbrev GateTriple := GateRecord × GateRecord × GateRecord

/-- Unlike zip, never silently discards an unmatched party suffix. -/
def zipExact3 {A : Type} : List A → List A → List A → Option (List (A × A × A))
  | [], [], [] => some []
  | a :: as, b :: bs, c :: cs => do
      let tail ← zipExact3 as bs cs
      pure ((a, b, c) :: tail)
  | _, _, _ => none

inductive Aligned3 {A : Type} (P : A → A → A → Prop) : List A → List A → List A → Prop
  | nil : Aligned3 P [] [] []
  | cons {a b c : A} {as bs cs : List A} : P a b c → Aligned3 P as bs cs →
      Aligned3 P (a :: as) (b :: bs) (c :: cs)

theorem zipExact3_of_aligned {A : Type} {P : A → A → A → Prop}
    {as bs cs : List A} (h : Aligned3 P as bs cs) :
    ∃ zs, zipExact3 as bs cs = some zs ∧ ∀ z ∈ zs, P z.1 z.2.1 z.2.2 := by
  induction h with
  | nil => exact ⟨[], rfl, by simp⟩
  | @cons a b c as bs cs habc _ ih =>
    rcases ih with ⟨zs, hz, hp⟩
    refine ⟨(a, b, c) :: zs, by simp [zipExact3, hz], ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact habc
    · exact hp z hz

theorem zipExact3_lengths {A : Type} (as bs cs : List A) (zs : List (A × A × A))
    (h : zipExact3 as bs cs = some zs) :
    as.length = zs.length ∧ bs.length = zs.length ∧ cs.length = zs.length := by
  induction as generalizing bs cs zs with
  | nil =>
    cases bs <;> cases cs <;> simp_all [zipExact3]
  | cons a as ih =>
    cases bs with
    | nil => simp [zipExact3] at h
    | cons b bs =>
      cases cs with
      | nil => simp [zipExact3] at h
      | cons c cs =>
        cases ht : zipExact3 as bs cs with
        | none => simp [zipExact3, ht] at h
        | some tail =>
          simp [zipExact3, ht] at h
          subst zs
          rcases ih bs cs tail ht with ⟨ha, hb, hc⟩
          simp [ha, hb, hc]

def replicas (a b c : GateRecord) : Prop :=
  a.lhsNext = b.lhsOwn ∧ b.lhsNext = c.lhsOwn ∧ c.lhsNext = a.lhsOwn ∧
  a.rhsNext = b.rhsOwn ∧ b.rhsNext = c.rhsOwn ∧ c.rhsNext = a.rhsOwn

instance (a b c : GateRecord) : Decidable (replicas a b c) := by
  exact inferInstanceAs (Decidable (
    a.lhsNext = b.lhsOwn ∧ b.lhsNext = c.lhsOwn ∧ c.lhsNext = a.lhsOwn ∧
    a.rhsNext = b.rhsOwn ∧ b.rhsNext = c.rhsOwn ∧ c.rhsNext = a.rhsOwn))

structure IndexedGate where
  cut : Nat
  subcall : Nat
  round : Nat
  lane : Nat
  records : GateTriple

/-- `bit` is Keccak's within-lane bit; `instance` is explicitly the single
participant sponge, not a packed-word bit. A later packed adapter must map it. -/
structure GateBitCoordinate where
  cut : Nat
  subcall : Nat
  round : Nat
  lane : Nat
  bit : Fin 64
  spongeInstance : Nat

def bitCoordinate (g : IndexedGate) (bit : Fin 64) : GateBitCoordinate :=
  ⟨g.cut, g.subcall, g.round, g.lane, bit, 0⟩

def indexGates (cut subcall round : Nat) : Nat → List GateTriple → List IndexedGate
  | _, [] => []
  | lane, g :: gs => ⟨cut, subcall, round, lane, g⟩ :: indexGates cut subcall round (lane + 1) gs

theorem indexGates_records (cut subcall round lane : Nat) (gs : List GateTriple) :
    (indexGates cut subcall round lane gs).map IndexedGate.records = gs := by
  induction gs generalizing lane with
  | nil => rfl
  | cons g gs ih => simp [indexGates, ih]

theorem indexGates_coordinates (cut subcall round lane : Nat) (gs : List GateTriple)
    (g : IndexedGate) (h : g ∈ indexGates cut subcall round lane gs) :
    g.cut = cut ∧ g.subcall = subcall ∧ g.round = round ∧
      lane ≤ g.lane ∧ g.lane < lane + gs.length := by
  induction gs generalizing lane with
  | nil => simp [indexGates] at h
  | cons head tail ih =>
    simp only [indexGates, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨rfl, rfl, rfl, Nat.le_refl _, by simp only [List.length_cons]; omega⟩
    · rcases ih (lane + 1) h with ⟨hc, hs, hr, hlo, hhi⟩
      exact ⟨hc, hs, hr, by omega, by simp only [List.length_cons]; omega⟩

def roundLinked (a b c : RoundEvidence) : Prop :=
  a.round = b.round ∧ b.round = c.round ∧ a.rc = b.rc ∧ b.rc = c.rc ∧
  a.receivedOutput = b.ownOutput ∧ b.receivedOutput = c.ownOutput ∧
  c.receivedOutput = a.ownOutput

instance (a b c : RoundEvidence) : Decidable (roundLinked a b c) := by
  exact inferInstanceAs (Decidable (
    a.round = b.round ∧ b.round = c.round ∧ a.rc = b.rc ∧ b.rc = c.rc ∧
    a.receivedOutput = b.ownOutput ∧ b.receivedOutput = c.ownOutput ∧
    c.receivedOutput = a.ownOutput))

def extractRound (cut subcall : Nat) (a b c : RoundEvidence) : Option (List IndexedGate) := do
  if ¬ roundLinked a b c then none else
  let gs ← zipExact3 a.gates b.gates c.gates
  if gs.length ≠ 25 then none else
  if gs.all (fun g => decide (replicas g.1 g.2.1 g.2.2)) then
    some (indexGates cut subcall a.round 0 gs)
  else none

def extractRounds (cut subcall : Nat) :
    List RoundEvidence → List RoundEvidence → List RoundEvidence → Option (List IndexedGate)
  | [], [], [] => some []
  | a :: as, b :: bs, c :: cs => do
      let head ← extractRound cut subcall a b c
      let tail ← extractRounds cut subcall as bs cs
      pure (head ++ tail)
  | _, _, _ => none

def extractHash (h : RssSigning.HashEvidence) : Option (List IndexedGate) :=
  extractRounds h.cut h.subcall h.nodes.n0.evidence h.nodes.n1.evidence h.nodes.n2.evidence

def extractHashes : List RssSigning.HashEvidence → Option (List IndexedGate)
  | [] => some []
  | h :: hs => do
      let head ← extractHash h
      let tail ← extractHashes hs
      pure (head ++ tail)

def extractAnswer (answer : RssSigning.UnverifiedAnswer) : Option (List IndexedGate) :=
  extractHashes answer.evidence

theorem wrong_received_output_rejected (cut subcall : Nat) (a b c : RoundEvidence)
    (h : a.receivedOutput ≠ b.ownOutput) : extractRound cut subcall a b c = none := by
  have hl : ¬ roundLinked a b c := fun hh => h hh.2.2.2.2.1
  simp [extractRound, hl]

theorem unmatched_round_suffix_rejected (cut subcall : Nat) (a : RoundEvidence)
    (as bs : List RoundEvidence) : extractRounds cut subcall (a :: as) bs [] = none := by
  cases bs <;> rfl

/-- Coordinate bit order: the outer tree branch consumes the LOW index bit,
matching mu0,mu1,... followed by nu0,nu1,... after actual layout conversion. -/
def tabulateGates : (depth : Nat) → (Nat → GateTriple) → GateTable depth
  | 0, f => .leaf (f 0)
  | depth + 1, f => .branch
      (tabulateGates depth (fun i => f (2 * i)))
      (tabulateGates depth (fun i => f (2 * i + 1)))

theorem tabulateGates_valid_iff : ∀ (depth : Nat) (f : Nat → GateTriple),
    gateTableValid (tabulateGates depth f) ↔
      ∀ i, i < 2 ^ depth → relation (f i).1 (f i).2.1 (f i).2.2 := by
  intro depth
  induction depth with
  | zero =>
    intro f
    simp only [tabulateGates, gateTableValid, Nat.pow_zero]
    constructor
    · intro h i hi
      have he : i = 0 := by omega
      simpa only [he] using h
    · intro h
      exact h 0 (by decide)
  | succ depth ih =>
    intro f
    simp only [tabulateGates, gateTableValid, ih, Nat.pow_succ]
    constructor
    · intro h i hi
      have hd := Nat.div_add_mod i 2
      have hr := Nat.mod_lt i (by decide : 0 < 2)
      have hq : i / 2 < 2 ^ depth := by omega
      by_cases he : i % 2 = 0
      · have hiEq : i = 2 * (i / 2) := by omega
        rw [hiEq]
        exact h.1 (i / 2) hq
      · have hiEq : i = 2 * (i / 2) + 1 := by omega
        rw [hiEq]
        exact h.2 (i / 2) hq
    · intro h
      constructor
      · intro i hi
        exact h (2 * i) (by omega)
      · intro i hi
        exact h (2 * i + 1) (by omega)

def zeroGate : GateRecord := ⟨0, 0, 0, 0, 0⟩
def zeroTriple : GateTriple := (zeroGate, zeroGate, zeroGate)

def indexedTable (depth : Nat) (gates : List IndexedGate) : GateTable depth :=
  tabulateGates depth (fun i => (gates.map IndexedGate.records).getD i zeroTriple)

/-- Capacity is checked, so a too-shallow tree never silently truncates gates. -/
def answerTable (depth : Nat) (answer : RssSigning.UnverifiedAnswer) : Option (GateTable depth) := do
  let gates ← extractAnswer answer
  if gates.length ≤ 2 ^ depth then some (indexedTable depth gates) else none

theorem honest_gate_records_aligned (s : RssKState) (r : Nat → RssPrfZeroSeeds) :
    Aligned3 (fun a b c => replicas a b c ∧ relation a b c)
      (gateRecords ⟨s.s0, s.s1⟩ (mask0 r))
      (gateRecords ⟨s.s1, s.s2⟩ (mask1 r))
      (gateRecords ⟨s.s2, s.s0⟩ (mask2 r)) := by
  unfold gateRecords
  repeat first
    | apply Aligned3.cons
    | apply And.intro
    | exact honest_relation ⟨_, _, _⟩ ⟨_, _, _⟩ ⟨_, _, _⟩
    | exact Aligned3.nil
    | rfl

def answerWeightAccept (depth : Nat) (answer : RssSigning.UnverifiedAnswer)
    (gs : ChallengeTuple depth) : Bool :=
  match answerTable depth answer with
  | none => false
  | some t => decide (weightEval gs (claimedCoeffs t) = weightEval gs (trueCoeffs t))

/-- The counted checker now consumes the exact concrete signer evidence. The
invalid index concerns that evidence's gate records, not an arbitrary table. -/
theorem answer_bad_gate_weight_bound (depth : Nat) (answer : RssSigning.UnverifiedAnswer)
    (gates : List IndexedGate) (hextract : extractAnswer answer = some gates)
    (hcap : gates.length ≤ 2 ^ depth)
    (hbad : ∃ i, i < gates.length ∧
      let g := (gates.map IndexedGate.records).getD i zeroTriple
      ¬ relation g.1 g.2.1 g.2.2)
    (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S depth).filter (answerWeightAccept depth answer)).length ≤
      weightBadBound S.length depth := by
  have hi : ¬ gateTableValid (indexedTable depth gates) := by
    intro hv
    rcases hbad with ⟨i, hi, hbad⟩
    exact hbad ((tabulateGates_valid_iff depth _).mp hv i (by omega))
  have he : answerTable depth answer = some (indexedTable depth gates) := by
    simp [answerTable, hextract, hcap]
  have hp : answerWeightAccept depth answer = fun gs => decide
      (weightEval gs (claimedCoeffs (indexedTable depth gates)) =
        weightEval gs (trueCoeffs (indexedTable depth gates))) := by
    funext gs
    simp [answerWeightAccept, he]
  rw [hp]
  exact invalid_weighted_claim_equal_le depth (indexedTable depth gates) hi S hS

theorem extractRound_of_aligned (cut subcall : Nat) (a b c : RoundEvidence)
    (hl : roundLinked a b c)
    (hg : Aligned3 (fun a b c => replicas a b c ∧ relation a b c) a.gates b.gates c.gates)
    (hlen : a.gates.length = 25) :
    ∃ gates, extractRound cut subcall a b c = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  obtain ⟨zs, hz, hall⟩ := zipExact3_of_aligned hg
  have hzs : zs.length = 25 := by
    have hh := (zipExact3_lengths _ _ _ _ hz).1
    omega
  have hreps : zs.all (fun g => decide (replicas g.1 g.2.1 g.2.2)) = true := by
    apply List.all_eq_true.mpr
    intro z hz
    exact decide_eq_true_iff.mpr (hall z hz).1
  refine ⟨indexGates cut subcall a.round 0 zs, ?_, ?_⟩
  · simp [extractRound, hl, hz, hzs, hreps]
  · intro g hg
    have hmem : g.records ∈ (indexGates cut subcall a.round 0 zs).map IndexedGate.records :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    rw [indexGates_records] at hmem
    exact (hall g.records hmem).2

def goodRound (a b c : RoundEvidence) : Prop :=
  roundLinked a b c ∧
  Aligned3 (fun a b c => replicas a b c ∧ relation a b c) a.gates b.gates c.gates ∧
  a.gates.length = 25

theorem extractRounds_of_aligned (cut subcall : Nat) {as bs cs : List RoundEvidence}
    (h : Aligned3 goodRound as bs cs) :
    ∃ gates, extractRounds cut subcall as bs cs = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  induction h with
  | nil => exact ⟨[], rfl, by simp⟩
  | @cons a b c as bs cs habc _ ih =>
    rcases extractRound_of_aligned cut subcall a b c habc.1 habc.2.1 habc.2.2 with
      ⟨head, hh, hp⟩
    rcases ih with ⟨tail, ht, htp⟩
    refine ⟨head ++ tail, by simp [extractRounds, hh, ht], ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · exact htp g hg

theorem inconsistent_gate_replica_rejected (cut subcall : Nat) (a b c : RoundEvidence)
    (zs : List GateTriple) (hz : zipExact3 a.gates b.gates c.gates = some zs)
    (g : GateTriple) (hg : g ∈ zs) (hbad : ¬ replicas g.1 g.2.1 g.2.2) :
    extractRound cut subcall a b c = none := by
  have hn : zs.all (fun t => decide (replicas t.1 t.2.1 t.2.2)) ≠ true := by
    intro h
    exact hbad (decide_eq_true_iff.mp (List.all_eq_true.mp h g hg))
  simp [extractRound, hz, hn]

theorem triple_getD_valid (triples : List GateTriple)
    (h : ∀ t ∈ triples, relation t.1 t.2.1 t.2.2) (i : Nat) :
    let t := triples.getD i zeroTriple
    relation t.1 t.2.1 t.2.2 := by
  induction triples generalizing i with
  | nil => exact show relation zeroGate zeroGate zeroGate from by decide
  | cons head tail ih =>
    cases i with
    | zero => exact h head (by simp)
    | succ i => exact ih (fun t ht => h t (by simp [ht])) i

theorem indexedTable_valid (depth : Nat) (gates : List IndexedGate)
    (h : ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2) :
    gateTableValid (indexedTable depth gates) := by
  apply (tabulateGates_valid_iff depth _).mpr
  intro i _
  apply triple_getD_valid
  intro t ht
  rcases List.mem_map.mp ht with ⟨g, hg, rfl⟩
  exact h g hg

theorem weightEval_zeroCoeffs : ∀ (depth : Nat) (gs : ChallengeTuple depth),
    weightEval gs (zeroCoeffs depth) = towerZero 7 := by
  intro depth
  induction depth with
  | zero => intro gs; cases gs; rfl
  | succ depth ih =>
    intro gs
    cases gs with | cons mu rest =>
    simp only [zeroCoeffs, weightEval, ih, towerMul_zero, towerAdd_zero]

theorem validTable_weighted_claim_eq (depth : Nat) (t : GateTable depth)
    (h : gateTableValid t) (gs : ChallengeTuple depth) :
    weightEval gs (claimedCoeffs t) = weightEval gs (trueCoeffs t) := by
  have he := (gateCoeffs_zero_iff depth t).mpr h
  have hz : towerAdd 7 (weightEval gs (claimedCoeffs t)) (weightEval gs (trueCoeffs t)) =
      towerZero 7 := by
    rw [← weighted_claim_defect, he, weightEval_zeroCoeffs]
  have hc := congrArg (fun v => towerAdd 7 v (weightEval gs (trueCoeffs t))) hz
  simpa only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] using hc

#verify_constructive zipExact3_of_aligned zipExact3_lengths indexGates_records indexGates_coordinates
  wrong_received_output_rejected unmatched_round_suffix_rejected
  tabulateGates_valid_iff honest_gate_records_aligned answer_bad_gate_weight_bound
  extractRound_of_aligned extractRounds_of_aligned inconsistent_gate_replica_rejected
  triple_getD_valid indexedTable_valid weightEval_zeroCoeffs validTable_weighted_claim_eq
end Qsag.RssParticipant.GateChecks
end
