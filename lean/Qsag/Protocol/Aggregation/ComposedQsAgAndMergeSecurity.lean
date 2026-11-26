module
public import Qsag.Math.Tactic.CommRing
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Aggregation.HemOpening
public section
namespace Qsag.Composed
set_option autoImplicit false
/-! Composition boundaries for `hem_quorum.rs`, `sig.rs`, and `lib.rs`.
The native signature verifier is concrete. WHIR extraction and custody-origin security remain
explicit reduction interfaces: acceptance alone does not prove that a human approved a message.
The privacy theorem concerns independent, private epoch polynomials and erased prior shares,
not public commitments, network packets, or deterministic publicly seeded dealer randomness. -/
open Aggregation
@[expose] def weight {n : Nat} (b : BitVec n) : Nat :=
  qsum n fun i => if b.getLsbD i.val then 1 else 0
theorem weight_union {n : Nat} (a b : BitVec n) (h : a &&& b = 0#n) :
    weight (a ||| b) = weight a + weight b := by
  unfold weight
  rw [← qsum_add]
  apply qsum_congr
  intro i
  have hz := congrArg (fun x : BitVec n => x.getLsbD i.val) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hz
  simp only [BitVec.getLsbD_or]
  cases ha : a.getLsbD i.val <;> cases hb : b.getLsbD i.val <;> simp_all
inductive SigningMode where
  | shared (msg : List UInt8)
  | perSigner (messages : List (List UInt8))
  deriving DecidableEq
def SigningMode.message (m : SigningMode) (v : Nat) : List UInt8 :=
  match m with
  | .shared msg => msg
  | .perSigner msgs => msgs.getD v []
def firstActive {n : Nat} (b : BitVec n) : Nat :=
  ((List.range n).find? b.getLsbD).getD n
/-- Honest approvals are log entries bound to the same epoch and native message. -/
structure Custody where
  state : IdealTsigState AggValidatorPk (List UInt8)
  epoch : Nat
  honestApprovers : List Nat
  approvalLog : Nat → Nat → List UInt8 → Bool
def quorumParticipated (q : Custody) (msg : List UInt8) : Bool :=
  validThresholdApproval q.state q.honestApprovers &&
    q.honestApprovers.all (fun p => q.approvalLog p q.epoch msg)
theorem honest_threshold (q : Custody) (msg : List UInt8)
    (h : quorumParticipated q msg = true) :
    1 ≤ q.state.threshold - q.state.corruptParties.length ∧
    q.state.threshold - q.state.corruptParties.length ≤ q.honestApprovers.length ∧
    q.honestApprovers.Nodup ∧
    ∀ p ∈ q.honestApprovers,
      p ∉ q.state.corruptParties ∧ q.approvalLog p q.epoch msg = true := by
  simp only [quorumParticipated, Bool.and_eq_true, List.all_eq_true] at h
  have hv := h.1
  simp only [validThresholdApproval, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hf⟩, _⟩, _⟩, _⟩, hn⟩, hh⟩, ht⟩ := hv
  have hc := List.length_filter_le (fun c => decide (c ∉ q.state.identifiedCheaters))
    q.state.corruptParties
  refine ⟨by omega, by omega, hn, ?_⟩
  intro p hp
  exact ⟨(hh p hp).1.2, h.2 p hp⟩
/-- A fresh valid native signature outside the custody approval log is the quorum forgery
bad event. Its probability is a cryptographic premise, not a consequence of signature syntax. -/
@[expose] def QuorumForgery (geom : AggSigGeometry) (q : Custody) (msg : List UInt8) : Prop :=
  ∃ sig : AggNativeSignature,
    verifyAggNativeSig geom q.state.pk msg sig = true ∧ quorumParticipated q msg = false
/-- Exact finite-tape union accounting. Divide all terms by the common tape count to obtain
`ε_total ≤ ε_whir_qrom + Σ_{v∈B} ε_quorum_v`; no independence is needed. -/
theorem composed_advantage_bound {tapes validators : Nat}
    (total outer : Fin tapes → Bool) (quorum : Fin tapes → Fin validators → Bool)
    (B : BitVec validators)
    (cover : ∀ ω, total ω = true → outer ω = true ∨
      ∃ v : Fin validators, B.getLsbD v.val = true ∧ quorum ω v = true) :
    (qsum tapes fun ω => if total ω then 1 else 0) ≤
    (qsum tapes fun ω => if outer ω then 1 else 0) +
    qsum validators (fun v => if B.getLsbD v.val then
      qsum tapes (fun ω => if quorum ω v then 1 else 0) else 0) := by
  have point : ∀ ω, (if total ω then 1 else 0) ≤
      (if outer ω then 1 else 0) +
      qsum validators (fun v => if B.getLsbD v.val && quorum ω v then 1 else 0) := by
    intro ω
    cases ht : total ω with
    | false => simp
    | true =>
      rcases cover ω ht with ho | ⟨v, hv, hq⟩
      · simp [ho]
      · have terms : ∀ i : Fin validators, (if i = v then 1 else 0) ≤
            (if B.getLsbD i.val && quorum ω i then 1 else 0) := by
          intro i; by_cases hi : i = v
          · subst i; simp [hv, hq]
          · simp [hi]
        have this := qsum_le_qsum terms
        rw [qsum_eq_indicator] at this
        simp only [↓reduceIte]; omega
  have h := qsum_le_qsum point
  rw [qsum_add, qsum_comm] at h
  have eq : (qsum validators fun v => qsum tapes
      (fun ω => if B.getLsbD v.val && quorum ω v then 1 else 0)) =
      qsum validators (fun v => if B.getLsbD v.val then
        qsum tapes (fun ω => if quorum ω v then 1 else 0) else 0) := by
    apply qsum_congr; intro v; cases B.getLsbD v.val <;> simp [qsum_const]
  rwa [eq] at h
private theorem listLengthInduction {α : Type} (P : List α → Prop)
    (step : ∀ l, (∀ m, m.length < l.length → P m) → P l) (l : List α) : P l := by
  induction hn : l.length using Nat.strongRecOn generalizing l with
  | ind n ih => exact step l fun m hm => ih m.length (by omega) m rfl
/-! Constructive interpolation by synthetic division, the triangular form of Vandermonde
elimination. Every polynomial below is an ordinary monomial coefficient list of fixed length. -/
section Interpolation
variable {F : Type} [LawfulCommRing F]
open CommRingOps
def insertEval (x y : F) : List F → List F
  | [] => [y]
  | a :: p => sub y (mul x a) :: insertEval x a p
theorem insert_length (x y : F) (p : List F) :
    (insertEval x y p).length = p.length + 1 := by
  induction p generalizing y with
  | nil => rfl
  | cons a p ih => simp [insertEval, ih]
theorem eval_insert (x y z : F) (p : List F) :
    RoundPoly.evalCoeffs (insertEval x y p) z =
      add y (mul (sub z x) (RoundPoly.evalCoeffs p z)) := by
  induction p generalizing y with
  | nil => simp [insertEval, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]
  | cons a p ih =>
    simp only [insertEval, RoundPoly.evalCoeffs_cons, ih]
    constructive_ring
theorem eval_insert_self (x y : F) (p : List F) :
    RoundPoly.evalCoeffs (insertEval x y p) x = y := by
  rw [eval_insert, LawfulCommRing.sub_self, LawfulCommRing.zero_mul,
    LawfulCommRing.add_zero]
theorem quot_insert (x y : F) (p : List F) :
    RoundPoly.quotLinear (insertEval x y p) x = p := by
  induction p generalizing y with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => simp [insertEval, RoundPoly.quotLinear, RoundPoly.evalCoeffs,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons b p =>
      change RoundPoly.evalCoeffs (insertEval x a (b :: p)) x ::
        RoundPoly.quotLinear (insertEval x a (b :: p)) x = a :: b :: p
      rw [eval_insert_self, ih]
theorem insert_quot (x : F) (p : List F) (hp : p ≠ []) :
    insertEval x (RoundPoly.evalCoeffs p x) (RoundPoly.quotLinear p x) = p := by
  induction p with
  | nil => exact False.elim (hp rfl)
  | cons a p ih =>
    cases p with
    | nil => simp [insertEval, RoundPoly.evalCoeffs, RoundPoly.quotLinear,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | cons b p =>
      change sub (add a (mul x (RoundPoly.evalCoeffs (b :: p) x)))
        (mul x (RoundPoly.evalCoeffs (b :: p) x)) ::
        insertEval x (RoundPoly.evalCoeffs (b :: p) x)
          (RoundPoly.quotLinear (b :: p) x) = _
      rw [ih (by simp)]
      congr 1
      constructive_ring
def vectors (domain : List F) : Nat → List (List F)
  | 0 => [[]]
  | k + 1 => domain.flatMap fun a => (vectors domain k).map (a :: ·)
omit [LawfulCommRing F] in
theorem vectors_length (domain : List F) (k : Nat) :
    (vectors domain k).length = domain.length ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [vectors, List.length_flatMap, List.length_map, ih]
    rw [List.map_const', List.sum_replicate_nat, Nat.pow_succ, Nat.mul_comm]
omit [LawfulCommRing F] in
theorem vectors_mem (domain : List F) (complete : ∀ a : F, a ∈ domain)
    (k : Nat) (p : List F) : p ∈ vectors domain k ↔ p.length = k := by
  induction k generalizing p with
  | zero =>
    constructor
    · intro h; have hp : p = [] := List.mem_singleton.mp h; rw [hp]; rfl
    · intro h; rw [List.eq_nil_of_length_eq_zero h]; exact .head []
  | succ k ih =>
    cases p with
    | nil =>
      constructor
      · intro h
        obtain ⟨a, _, hm⟩ := List.mem_flatMap.mp h
        obtain ⟨q, _, he⟩ := List.mem_map.mp hm
        cases he
      · intro h; cases h
    | cons a p =>
      constructor
      · intro h
        obtain ⟨b, _, hm⟩ := List.mem_flatMap.mp h
        obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
        obtain ⟨rfl, rfl⟩ := List.cons.inj he
        exact congrArg Nat.succ ((ih _).mp hq)
      · intro h
        exact List.mem_flatMap.mpr ⟨a, complete a,
          List.mem_map.mpr ⟨p, (ih p).mpr (Nat.succ.inj h), rfl⟩⟩
omit [LawfulCommRing F] in
theorem vectors_nodup (domain : List F) (hd : domain.Nodup) (k : Nat) :
    (vectors domain k).Nodup := by
  induction k with
  | zero => simp [vectors]
  | succ k ih =>
    unfold vectors
    change List.Pairwise (· ≠ ·) _
    rw [List.pairwise_flatMap]
    constructor
    · intro a _
      exact (List.pairwise_map.mpr (ih.imp fun h => by simpa using h))
    · apply hd.imp
      intro a b hab p hp q hq
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
      intro heq
      exact hab (List.cons.inj heq).1
variable (inv : F → F)
def residual (x y : F) (obs : List (F × F)) : List (F × F) :=
  obs.map fun o => (o.1, mul (inv (sub o.1 x)) (sub o.2 y))
def solutions (domain : List F) (free : Nat) : List (F × F) → List (List F)
  | [] => vectors domain free
  | (x,y) :: obs => (solutions domain free (residual inv x y obs)).map (insertEval x y)
termination_by obs => obs.length
decreasing_by simp [residual]
/-- This length is the actual number of enumerated consistent coefficient vectors, not a
postulated field-cardinality formula. Distinctness and exhaustiveness are proved below. -/
theorem solutions_length (domain : List F) (free : Nat) (obs : List (F × F)) :
    (solutions inv domain free obs).length = domain.length ^ free := by
  induction obs using listLengthInduction with
  | step obs ih =>
    cases obs with
    | nil => simpa only [solutions] using vectors_length domain free
    | cons o obs =>
      rcases o with ⟨x,y⟩
      simp only [solutions, List.length_map]
      apply ih
      simp [residual]
theorem solutions_nodup (domain : List F) (hd : domain.Nodup)
    (free : Nat) (obs : List (F × F)) : (solutions inv domain free obs).Nodup := by
  induction obs using listLengthInduction with
  | step obs ih =>
    cases obs with
    | nil => simpa only [solutions] using vectors_nodup domain hd free
    | cons o obs =>
      rcases o with ⟨x,y⟩
      simp only [solutions]
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp _ (ih _ (by simp [residual]))
      intro p q hneq heq
      apply hneq
      have := congrArg (fun p => RoundPoly.quotLinear p x) heq
      simpa only [quot_insert] using this
/-- Solving one nonzero Vandermonde pivot is reversible. -/
theorem pivot (hinv : ∀ x : F, x ≠ zero → mul x (inv x) = one) (x y z w a : F) (hz : z ≠ x) :
    add y (mul (sub z x) a) = w ↔ a = mul (inv (sub z x)) (sub w y) := by
  have hi := hinv (sub z x) (fun h => hz (LawfulCommRing.sub_eq_zero_iff.mp h))
  have hi' : mul (inv (sub z x)) (sub z x) = one := by
    rw [LawfulCommRing.mul_comm]; exact hi
  constructor
  · intro h
    rw [← h]
    have hs : sub (add y (mul (sub z x) a)) y = mul (sub z x) a := by
      constructive_ring
    rw [hs, ← LawfulCommRing.mul_assoc, hi', LawfulCommRing.one_mul]
  · intro h
    rw [h, ← LawfulCommRing.mul_assoc, hi, LawfulCommRing.one_mul,
      LawfulCommRing.add_sub_cancel_left]
def Matches (p : List F) (obs : List (F × F)) : Prop :=
  ∀ o ∈ obs, RoundPoly.evalCoeffs p o.1 = o.2
theorem solutions_exact (hinv : ∀ x : F, x ≠ zero → mul x (inv x) = one) (domain : List F) (complete : ∀ a : F, a ∈ domain)
    (free : Nat) (obs : List (F × F)) (distinct : (obs.map Prod.fst).Nodup)
    (p : List F) : p ∈ solutions inv domain free obs ↔
      p.length = free + obs.length ∧ Matches p obs := by
  induction obs using listLengthInduction generalizing p with
  | step obs ih =>
    cases obs with
    | nil => simp [solutions, vectors_mem domain complete, Matches]
    | cons o obs =>
      rcases o with ⟨x,y⟩
      have hn := List.pairwise_cons.mp distinct
      have hd : ((residual inv x y obs).map Prod.fst).Nodup := by
        simp only [residual, List.map_map, Function.comp_def]
        exact hn.2
      have shorter : (residual inv x y obs).length < ((x,y) :: obs).length := by
        simp [residual]
      have nz : ∀ o ∈ obs, o.1 ≠ x := by
        intro o ho
        exact Ne.symm (hn.1 o.1 (List.mem_map.mpr ⟨o, ho, rfl⟩))
      simp only [solutions, List.mem_map]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨hl, hm⟩ := (ih _ shorter hd q).mp hq
        refine ⟨?_, ?_⟩
        · simp only [residual, List.length_map] at hl
          rw [insert_length]; simp only [List.length_cons]; omega
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact eval_insert_self x y q
          · rw [eval_insert]
            apply (pivot inv hinv x y o.1 o.2 _ (nz o ho)).mpr
            exact hm _ (List.mem_map.mpr ⟨o, ho, rfl⟩)
      · rintro ⟨hl, hm⟩
        have hp : p ≠ [] := by intro he; simp [he] at hl
        have hx : RoundPoly.evalCoeffs p x = y := hm (x,y) (.head obs)
        refine ⟨RoundPoly.quotLinear p x, ?_, ?_⟩
        · apply (ih _ shorter hd _).mpr
          refine ⟨?_, ?_⟩
          · simp only [RoundPoly.quotLinear_length, residual, List.length_map]
            simp only [List.length_cons] at hl; omega
          · intro o ho
            simp only [residual] at ho
            obtain ⟨u, hu, heq⟩ := List.mem_map.mp ho
            subst o
            apply (pivot inv hinv x y u.1 u.2 _ (nz u hu)).mp
            have he := RoundPoly.evalCoeffs_eq_mul_quotLinear_add p x u.1
            rw [hx, LawfulCommRing.add_comm] at he
            exact he.symm.trans (hm u (.tail _ hu))
        · rw [← hx]; exact insert_quot x p hp
end Interpolation
section Epochs
variable {F : Type} [LawfulCommRing F]
open CommRingOps
structure Epoch (F : Type) where
  threshold : Nat
  numParties : Nat
  corruptPoints : List F
  observed : F → F
def Epoch.Valid (e : Epoch F) : Prop :=
  e.corruptPoints.length < e.threshold ∧ e.threshold ≤ e.numParties ∧
    (zero :: e.corruptPoints).Nodup
def observations (s : F) (e : Epoch F) : List (F × F) :=
  (zero, s) :: e.corruptPoints.map (fun x => (x, e.observed x))
def epochPolys (inv : F → F) (domain : List F) (s : F) (e : Epoch F) : List (List F) :=
  solutions inv domain (e.threshold - 1 - e.corruptPoints.length) (observations s e)
def epochCompatible (s : F) (e : Epoch F) (p : List F) : Prop :=
  p.length = e.threshold ∧ RoundPoly.evalCoeffs p zero = s ∧
    ∀ x ∈ e.corruptPoints, RoundPoly.evalCoeffs p x = e.observed x
theorem epoch_exact (inv : F → F)
    (hi : ∀ x : F, x ≠ zero → mul x (inv x) = one)
    (domain : List F) (hc : ∀ a : F, a ∈ domain) (s : F) (e : Epoch F)
    (valid : e.Valid) (p : List F) :
    p ∈ epochPolys inv domain s e ↔ epochCompatible s e p := by
  have hd : ((observations s e).map Prod.fst).Nodup := by
    simpa [observations, List.map_map, Function.comp_def] using valid.2.2
  rw [epochPolys, solutions_exact inv hi domain hc _ _ hd]
  have ht : e.threshold - 1 - e.corruptPoints.length + (observations s e).length =
      e.threshold := by
    have := valid.1
    simp only [observations, List.length_cons, List.length_map]; omega
  rw [ht]
  simp [Matches, observations, epochCompatible]
/-- Each transition contributes independent effective polynomial coefficients. This is the
share-view experiment after successful private resharing and old-share erasure. -/
def transcripts (inv : F → F) (domain : List F) (s : F) :
    List (Epoch F) → List (List (List F))
  | [] => [[]]
  | e :: es => (epochPolys inv domain s e).flatMap fun p =>
    (transcripts inv domain s es).map (p :: ·)
def compatible (s : F) : List (Epoch F) → List (List F) → Prop
  | [], [] => True
  | e :: es, p :: ps => epochCompatible s e p ∧ compatible s es ps
  | _, _ => False
theorem transcripts_exact (inv : F → F)
    (hi : ∀ x : F, x ≠ zero → mul x (inv x) = one)
    (domain : List F) (hc : ∀ a : F, a ∈ domain) (s : F) (es : List (Epoch F))
    (hv : ∀ e ∈ es, e.Valid) (ps : List (List F)) :
    ps ∈ transcripts inv domain s es ↔ compatible s es ps := by
  induction es generalizing ps with
  | nil => cases ps <;> simp [transcripts, compatible]
  | cons e es ih =>
    cases ps with
    | nil => simp [transcripts, compatible]
    | cons p ps =>
      simp [transcripts, List.mem_flatMap, List.mem_map, compatible,
        epoch_exact inv hi domain hc s e (hv e (.head es)),
        ih (fun e he => hv e (.tail _ he))]
theorem transcripts_nodup (inv : F → F) (domain : List F) (hd : domain.Nodup)
    (s : F) (es : List (Epoch F)) : (transcripts inv domain s es).Nodup := by
  induction es with
  | nil => simp [transcripts]
  | cons e es ih =>
    change List.Pairwise (· ≠ ·) _
    rw [transcripts, List.pairwise_flatMap]
    constructor
    · intro p _; apply List.pairwise_map.mpr
      exact ih.imp fun h => by simpa using h
    · apply (solutions_nodup inv domain hd _ (observations s e)).imp
      intro a b hab p hp q hq
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hq
      exact fun he => hab (List.cons.inj he).1
/-- Exact uniform fibers for arbitrary dynamic thresholds and arbitrary mobile traces.
There is no restriction on the union of corrupted identities across different epochs.
Together with exhaustiveness and absence of duplicates this is exact cardinality, so every
secret induces the same view probability (and statistical distance zero) under uniform coins. -/
theorem mobile_uniform_fibers (inv : F → F)
    (hi : ∀ x : F, x ≠ zero → mul x (inv x) = one)
    (domain : List F) (hd : domain.Nodup) (hc : ∀ a : F, a ∈ domain)
    (s : F) (es : List (Epoch F)) (hv : ∀ e ∈ es, e.Valid) :
    (transcripts inv domain s es).Nodup ∧
    (∀ ps, ps ∈ transcripts inv domain s es ↔ compatible s es ps) ∧
    (transcripts inv domain s es).length =
      (es.map fun e => domain.length ^ (e.threshold - 1 - e.corruptPoints.length)).prod := by
  refine ⟨transcripts_nodup inv domain hd s es,
    transcripts_exact inv hi domain hc s es hv, ?_⟩
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [transcripts, List.length_flatMap, List.length_map,
      ih (fun e he => hv e (.tail _ he)), List.map_const', List.sum_replicate_nat,
      epochPolys, solutions_length, List.map_cons, List.prod_cons]
/-- Without erasure, observations from successive corruptions constrain the SAME polynomial.
At threshold many distinct points the solution set contains exactly one polynomial. -/
theorem retained_shares_determine_secret (inv : F → F)
    (hi : ∀ x : F, x ≠ zero → mul x (inv x) = one)
    (domain : List F) (hc : ∀ a : F, a ∈ domain) (obs : List (F × F))
    (hd : (obs.map Prod.fst).Nodup) (p q : List F)
    (hp : p.length = obs.length) (mp : Matches p obs)
    (hq : q.length = obs.length) (mq : Matches q obs) :
    p = q ∧ RoundPoly.evalCoeffs p zero = RoundPoly.evalCoeffs q zero := by
  have oneSol := solutions_length inv domain 0 obs
  have pm : p ∈ solutions inv domain 0 obs :=
    (solutions_exact inv hi domain hc 0 obs hd p).mpr (by simpa using And.intro hp mp)
  have qm : q ∈ solutions inv domain 0 obs :=
    (solutions_exact inv hi domain hc 0 obs hd q).mpr (by simpa using And.intro hq mq)
  cases hs : solutions inv domain 0 obs with
  | nil => rw [hs] at pm; cases pm
  | cons a tail =>
    have ht : tail = [] := by
      rw [hs] at oneSol
      simp only [List.length_cons, Nat.pow_zero] at oneSol
      apply List.eq_nil_of_length_eq_zero; omega
    rw [hs, ht, List.mem_singleton] at pm qm
    exact ⟨pm.trans qm.symm, congrArg (fun p => RoundPoly.evalCoeffs p zero) (pm.trans qm.symm)⟩
end Epochs
/-! Reachable fixtures and mutations. The fixtures that evaluate `checkTree` on `exampleTree`
(`inhabited_tree`, `tooth_overlap`, `inhabited_reduction`, `inhabited_shard_bound`) and their
audits are in `Tests/CompositionInstances.lean`. The leaf-verifier fixture tests the structural layer;
it is deliberately not represented as a deployed WHIR proof. -/
def exampleCustody : Custody :=
  ⟨⟨⟨.xmssPoseidon2, ⟨Goldilocks.zero,Goldilocks.zero,Goldilocks.zero,Goldilocks.zero⟩, ⟨Goldilocks.zero,Goldilocks.zero,Goldilocks.zero,Goldilocks.zero⟩⟩, 2, 3, [0], [], []⟩,
    7, [1], fun p ep msg => decide (p = 1 ∧ ep = 7 ∧ msg = [1])⟩
theorem inhabited_approval : ∃ q msg, quorumParticipated q msg = true :=
  ⟨exampleCustody, [1], by decide⟩
/-- The weakened capacity check accepts a fully corrupt quorum with zero honest approvals.
The production structural checker also has an independent nonempty-honest guard: deleting
only its strict-fault guard does NOT remove that second defense. -/
theorem tooth_full_corrupt : ∃ q : Custody,
    q.state.threshold = q.state.corruptParties.length ∧ q.honestApprovers = [] ∧
    q.state.threshold ≤ q.state.corruptParties.length + q.honestApprovers.length ∧
    quorumParticipated q [1] = false :=
  ⟨{ exampleCustody with state.threshold := 1, honestApprovers := [] },
    by decide, rfl, by decide, by decide⟩
/-- Removing the outer term from a union bound loses attacks that only break extraction. -/
theorem tooth_omit_outer : ∃ total outer : Fin 1 → Bool,
    (∀ ω, total ω = true → outer ω = true) ∧
    (qsum 1 fun ω => if total ω then 1 else 0) > 0 :=
  ⟨fun _ => true, fun _ => true, fun _ _ => rfl, by
    show (qsum 1 fun _ => 1) > 0
    rw [qsum_const]; decide⟩
local instance : DecidableEq (TowerElem 1) := towerDecidableEq 1
local instance : DecidableEq (Bool × Bool) := towerDecidableEq 1
local instance : LawfulCommRing (Bool × Bool) := towerRing 1
def fourElements : List (TowerElem 1) := [(false,false),(false,true),(true,false),(true,true)]
theorem four_complete (x : TowerElem 1) : x ∈ fourElements := by
  rcases x with ⟨a,b⟩; cases a <;> cases b
  · exact .head _
  · exact .tail _ (.head _)
  · exact .tail _ (.tail _ (.head _))
  · exact .tail _ (.tail _ (.tail _ (.head _)))
def firstEpoch : Epoch (TowerElem 1) := ⟨2, 2, [(true,false)], fun _ => (false,true)⟩
def secondEpoch : Epoch (TowerElem 1) := ⟨2, 2, [(false,true)], fun _ => (true,true)⟩
theorem inhabited_mobile : ∃ domain : List (TowerElem 1), ∃ es : List (Epoch (TowerElem 1)),
    domain.Nodup ∧ (∀ x : TowerElem 1, x ∈ domain) ∧
    (∀ x : TowerElem 1, x ≠ CommRingOps.zero →
      CommRingOps.mul x (towerInv 1 x) = CommRingOps.one) ∧
    (∀ e ∈ es, e.Valid) := by
  refine ⟨fourElements, [firstEpoch, secondEpoch], by decide, four_complete, towerMul_inv 1, ?_⟩
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> unfold Epoch.Valid <;> decide
theorem mobile_covers_entire_roster :
    firstEpoch.Valid ∧ secondEpoch.Valid ∧
    firstEpoch.corruptPoints ++ secondEpoch.corruptPoints = [(true,false),(false,true)] := by
  refine ⟨?_, ?_, rfl⟩
  · change (1 < 2 ∧ 2 ≤ 2 ∧ ([(false,false),(true,false)] : List (TowerElem 1)).Nodup)
    decide
  · change (1 < 2 ∧ 2 ≤ 2 ∧ ([(false,false),(false,true)] : List (TowerElem 1)).Nodup)
    decide
/-- Retaining both epochs' shares of an unrefreshed degree-one polynomial distinguishes
secrets, although each individual epoch corrupts fewer than two custodians. -/
theorem tooth_retained_polynomial : ∃ p q : List (TowerElem 1),
    epochCompatible (true,false) firstEpoch p ∧
    epochCompatible (false,false) firstEpoch q ∧
    RoundPoly.evalCoeffs p (false,true) ≠ RoundPoly.evalCoeffs q (false,true) := by
  refine ⟨[(true,false),(true,true)], [(false,false),(false,true)], ?_, ?_, ?_⟩
  · unfold epochCompatible; decide
  · unfold epochCompatible; decide
  · decide
theorem inhabited_union : ∃ total outer : Fin 2 → Bool,
    ∃ quorum : Fin 2 → Fin 2 → Bool, ∃ B : BitVec 2,
    (∀ ω, total ω = true → outer ω = true ∨
      ∃ v : Fin 2, B.getLsbD v.val = true ∧ quorum ω v = true) ∧
    (qsum 2 fun ω => if total ω then 1 else 0) = 2 := by
  refine ⟨(fun _ => true), (fun ω => decide (ω.val = 0)),
    (fun ω v => decide (ω.val = 1 ∧ v.val = 1)), 3#2, ?_, ?_⟩
  · decide
  · show (qsum 2 fun _ => 1) = 2
    rw [qsum_const]
theorem inhabited_reconstruction : ∃ domain : List (TowerElem 1),
    domain.Nodup ∧ (∀ x : TowerElem 1, x ∈ domain) ∧
    (∀ x : TowerElem 1, x ≠ CommRingOps.zero →
      CommRingOps.mul x (towerInv 1 x) = CommRingOps.one) ∧
    ∃ obs : List (TowerElem 1 × TowerElem 1), (obs.map Prod.fst).Nodup ∧
    ∃ p q : List (TowerElem 1),
      (p.length = obs.length ∧ Matches p obs) ∧ (q.length = obs.length ∧ Matches q obs) := by
  refine ⟨fourElements, by decide, four_complete, towerMul_inv 1, [((true,false),(false,true)),((false,true),(false,false))],
    by decide, [(true,false),(true,true)], [(true,false),(true,true)], ?_, ?_⟩ <;>
    (unfold Matches; decide)
#verify_constructive weight_union honest_threshold
#verify_constructive composed_advantage_bound
#verify_constructive insert_length eval_insert eval_insert_self quot_insert insert_quot
#verify_constructive vectors_length vectors_mem vectors_nodup solutions_length solutions_nodup
#verify_constructive pivot solutions_exact epoch_exact transcripts_exact transcripts_nodup
#verify_constructive mobile_uniform_fibers retained_shares_determine_secret

#verify_constructive mobile_covers_entire_roster
#verify_inhabited honest_threshold inhabited_approval

#verify_constructive inhabited_union tooth_omit_outer
#verify_inhabited retained_shares_determine_secret inhabited_reconstruction
#verify_inhabited solutions_exact inhabited_reconstruction
#verify_inhabited mobile_uniform_fibers inhabited_mobile


#tooth_pair honest_threshold vs tooth_full_corrupt


#tooth_pair mobile_uniform_fibers vs tooth_retained_polynomial
#tooth_pair epoch_exact vs tooth_retained_polynomial
#tooth_pair solutions_exact vs tooth_retained_polynomial
#tooth_pair retained_shares_determine_secret vs tooth_retained_polynomial
/-- Publicly determined nonconstant coefficients make even one share distinguish secrets. -/
theorem tooth_public_coefficients {F : Type} [LawfulCommRing F] (s t x : F) (r : List F)
    (hne : s ≠ t) : RoundPoly.evalCoeffs (s :: r) x ≠ RoundPoly.evalCoeffs (t :: r) x := by
  intro h
  apply hne
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul x (RoundPoly.evalCoeffs r x))
  simpa only [RoundPoly.evalCoeffs_cons, LawfulCommRing.add_comm] using h
#tooth_pair mobile_uniform_fibers vs tooth_public_coefficients
end Qsag.Composed

/-! ## Bridges from the committee AIR and the HEM opening batch to `ExtractionBoundary` -/
namespace Qsag.CompositionInstances
open Qsag.Composed


end Qsag.CompositionInstances

namespace Qsag.Composed
/-! ### Exports for lane agg-whir-cert -/

/-- Defining statement of `QuorumForgery`: a verifying native signature under the custody key on a
message the quorum did not participate in. -/
theorem quorumForgery_iff (geom : AggSigGeometry) (q : Custody) (msg : List UInt8) :
    QuorumForgery geom q msg ↔
      ∃ sig : AggNativeSignature,
        verifyAggNativeSig geom q.state.pk msg sig = true ∧ quorumParticipated q msg = false :=
  Iff.rfl

-- Equations for the symbolic instances of `Tests/CompositionInstances`; no body is exposed.
#export_eqns firstActive quorumParticipated
  SigningMode.message
-- `inhabited_union` is this module's witness; the pair is certified here for `Tests/CompositionInstances`.
#verify_inhabited composed_advantage_bound inhabited_union

end Qsag.Composed
