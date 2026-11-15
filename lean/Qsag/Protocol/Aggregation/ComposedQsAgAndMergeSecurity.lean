module
public import Qsag.Tactic.ConstructiveRing
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Threshold.ThresholdApproval
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Oracle.UcGames
public section
namespace Qsag.Composed
set_option autoImplicit false
/-! Composition boundaries for `hem_quorum.rs`, `sig.rs`, and `lib.rs`.
The native signature verifier is concrete. WHIR extraction and custody-origin security remain
explicit reduction interfaces: acceptance alone does not prove that a human approved a message.
The privacy theorem concerns independent, private epoch polynomials and erased prior shares,
not public commitments, network packets, or deterministic publicly seeded dealer randomness. -/
open Aggregation
def weight {n : Nat} (b : BitVec n) : Nat :=
  finSum n fun i => if b.getLsbD i.val then 1 else 0
theorem weight_union {n : Nat} (a b : BitVec n) (h : a &&& b = 0#n) :
    weight (a ||| b) = weight a + weight b := by
  unfold weight
  rw [← finSum_add]
  apply finSum_congr
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
structure Header where
  committeeRoot : List UInt8
  profile : AggSigProfile
  regime : Qsag.WhirSecurityRegime
  mode : SigningMode
  deriving DecidableEq
structure Shard (n : Nat) where
  header : Header
  bitmap : BitVec n
  /-- Bytes supplied to the leaf verifier; no plaintext signature openings are assumed. -/
  proof : List UInt8
  numVars : Nat
  schedule : WhirSchedule
inductive MergeTree (n : Nat) where
  | leaf (shard : Shard n)
  | branch (left right : MergeTree n) (mergedBitmap : BitVec n)
def MergeTree.bitmap {n : Nat} : MergeTree n → BitVec n
  | .leaf s => s.bitmap
  | .branch _ _ b => b
def MergeTree.leaves {n : Nat} : MergeTree n → List (Shard n)
  | .leaf s => [s]
  | .branch l r _ => l.leaves ++ r.leaves
def firstActive {n : Nat} (b : BitVec n) : Nat :=
  ((List.range n).find? b.getLsbD).getD n
/-- The budget counts branches, as in Rust; a leaf is permitted at remaining depth zero.
Header equality pins both supported regimes; classical acceptance is never promoted to QROM. -/
def checkTree {n : Nat} (root : Header) (verify : Shard n → Bool) :
    Nat → MergeTree n → Bool
  | _, .leaf s => decide (s.header = root) &&
    decide (2 ≤ s.numVars ∧ s.numVars ≤ 24 ∧ s.schedule = root.regime.schedule s.numVars) &&
    decide (0 < weight s.bitmap) && verify s
  | 0, .branch _ _ _ => false
  | d + 1, .branch l r b =>
    decide (l.bitmap &&& r.bitmap = 0#n) && decide (b = l.bitmap ||| r.bitmap) &&
    decide (firstActive l.bitmap < firstActive r.bitmap) &&
    checkTree root verify d l && checkTree root verify d r
/-- Every validator has exactly one leaf occurrence, and all leaf headers and proofs verify.
`countP = 1` counts occurrences, including repeated identical leaf objects. -/
theorem binary_merge_sound {n : Nat} (root : Header) (verify : Shard n → Bool)
    (tree : MergeTree n) (d : Nat) (h : checkTree root verify d tree = true) :
    weight tree.bitmap = (tree.leaves.map fun s => weight s.bitmap).sum ∧
    (∀ v : Nat, (tree.leaves.countP fun s => s.bitmap.getLsbD v) =
      if tree.bitmap.getLsbD v then 1 else 0) ∧
    (∀ s ∈ tree.leaves, s.header = root ∧ verify s = true ∧
      2 ≤ s.numVars ∧ s.numVars ≤ 24 ∧ s.schedule = root.regime.schedule s.numVars) ∧
    tree.leaves.length ≤ 2 ^ d := by
  induction tree generalizing d with
  | leaf s =>
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨by simp [MergeTree.bitmap, MergeTree.leaves], ?_, ?_, ?_⟩
    · intro v; change (if s.bitmap.getLsbD v then 1 else 0) = _; rfl
    · intro a ha; simp only [MergeTree.leaves, List.mem_singleton] at ha
      subst a; exact ⟨h.1.1.1, h.2, h.1.1.2⟩
    · simpa [MergeTree.leaves] using Nat.one_le_two_pow
  | branch l r b il ir =>
    cases d with
    | zero => cases h
    | succ d =>
      simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hd, hb⟩, _⟩, hl⟩, hr⟩ := h
      obtain ⟨wl, cl, sl, dl⟩ := il d hl
      obtain ⟨wr, cr, sr, dr⟩ := ir d hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · change weight b = _
        rw [hb, weight_union _ _ hd, wl, wr]
        simp only [MergeTree.leaves, List.map_append, List.sum_append]
      · intro v
        have hz := congrArg (fun x : BitVec n => x.getLsbD v) hd
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hz
        change List.countP _ (l.leaves ++ r.leaves) = if b.getLsbD v then 1 else 0
        rw [List.countP_append, cl, cr, hb, BitVec.getLsbD_or]
        cases ha : l.bitmap.getLsbD v <;> cases hb : r.bitmap.getLsbD v <;>
          simp_all
      · intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact sl s hs
        · exact sr s hs
      · simp only [MergeTree.leaves, List.length_append, Nat.pow_succ]
        omega
theorem depth_sixteen {n : Nat} (root : Header) (verify : Shard n → Bool)
    (tree : MergeTree n) (h : checkTree root verify 16 tree = true) :
    tree.leaves.length ≤ 65536 := (binary_merge_sound root verify tree 16 h).2.2.2
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
def QuorumForgery (geom : AggSigGeometry) (q : Custody) (msg : List UInt8) : Prop :=
  ∃ sig : AggNativeSignature,
    verifyAggNativeSig geom q.state.pk msg sig = true ∧ quorumParticipated q msg = false
/-- The outer adapter must be discharged by WHIR/Merkle extraction for the deployed AIR.
It binds the accepted bytes to the enrolled keys and exact per-validator messages. -/
structure ExtractionBoundary {n : Nat} (geom : AggSigGeometry)
    (custody : Fin n → Custody) (verify : Shard n → Bool) (bad : Shard n → Prop) : Prop where
  extract : ∀ s, verify s = true → bad s ∨
    ∀ v : Fin n, s.bitmap.getLsbD v.val = true →
      ∃ sig, verifyAggNativeSig geom (custody v).state.pk
        (s.header.mode.message v.val) sig = true
theorem quorum_aggregation_reduction {n : Nat} (geom : AggSigGeometry)
    (custody : Fin n → Custody) (verify : Shard n → Bool) (bad : Shard n → Prop)
    (boundary : ExtractionBoundary geom custody verify bad) (s : Shard n)
    (accepted : verify s = true) (v : Fin n) (active : s.bitmap.getLsbD v.val = true) :
    bad s ∨ QuorumForgery geom (custody v) (s.header.mode.message v.val) ∨
    (1 ≤ (custody v).state.threshold - (custody v).state.corruptParties.length ∧
     (custody v).state.threshold - (custody v).state.corruptParties.length ≤
       (custody v).honestApprovers.length ∧
     (custody v).honestApprovers.Nodup ∧
     ∀ p ∈ (custody v).honestApprovers, p ∉ (custody v).state.corruptParties ∧
       (custody v).approvalLog p (custody v).epoch (s.header.mode.message v.val) = true) := by
  rcases boundary.extract s accepted with hb | hs
  · exact .inl hb
  · obtain ⟨sig, hv⟩ := hs v active
    cases hq : quorumParticipated (custody v) (s.header.mode.message v.val) with
    | false => exact .inr (.inl ⟨sig, hv, hq⟩)
    | true => exact .inr (.inr (honest_threshold _ _ hq))
/-- Exact finite-tape union accounting. Divide all terms by the common tape count to obtain
`ε_total ≤ ε_whir_qrom + Σ_{v∈B} ε_quorum_v`; no independence is needed. -/
theorem composed_advantage_bound {tapes validators : Nat}
    (total outer : Fin tapes → Bool) (quorum : Fin tapes → Fin validators → Bool)
    (B : BitVec validators)
    (cover : ∀ ω, total ω = true → outer ω = true ∨
      ∃ v : Fin validators, B.getLsbD v.val = true ∧ quorum ω v = true) :
    (finSum tapes fun ω => if total ω then 1 else 0) ≤
    (finSum tapes fun ω => if outer ω then 1 else 0) +
    finSum validators (fun v => if B.getLsbD v.val then
      finSum tapes (fun ω => if quorum ω v then 1 else 0) else 0) := by
  have point : ∀ ω, (if total ω then 1 else 0) ≤
      (if outer ω then 1 else 0) +
      finSum validators (fun v => if B.getLsbD v.val && quorum ω v then 1 else 0) := by
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
        have this := finSum_le_finSum terms
        rw [finSum_eq_indicator] at this
        simp only [↓reduceIte]; omega
  have h := finSum_le_finSum point
  rw [finSum_add, finSum_comm] at h
  have eq : (finSum validators fun v => finSum tapes
      (fun ω => if B.getLsbD v.val && quorum ω v then 1 else 0)) =
      finSum validators (fun v => if B.getLsbD v.val then
        finSum tapes (fun ω => if quorum ω v then 1 else 0) else 0) := by
    apply finSum_congr; intro v; cases B.getLsbD v.val <;> simp [finSum_const]
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
/-- Composed finite-tape advantage from the extraction adapter, with no numerical security
literals. The forgery event is tested on the concrete native verifier and approval log. -/
theorem quorum_advantage_from_extraction {n tapes : Nat} (geom : AggSigGeometry)
    (custody : Fin n → Custody) (verify : Shard n → Bool) (outer : Shard n → Bool)
    (boundary : ExtractionBoundary geom custody verify (fun s => outer s = true))
    (shards : Fin tapes → Shard n) (attack : Fin tapes → Bool) (B : BitVec n)
    (forgery : Fin tapes → Fin n → Bool)
    (game : ∀ ω, attack ω = true → verify (shards ω) = true ∧
      ∃ v : Fin n, B.getLsbD v.val = true ∧ (shards ω).bitmap.getLsbD v.val = true ∧
        quorumParticipated (custody v) ((shards ω).header.mode.message v.val) = false)
    (detect : ∀ ω v, QuorumForgery geom (custody v)
      ((shards ω).header.mode.message v.val) → forgery ω v = true) :
    (finSum tapes fun ω => if attack ω then 1 else 0) ≤
    (finSum tapes fun ω => if outer (shards ω) then 1 else 0) +
    finSum n (fun v => if B.getLsbD v.val then
      finSum tapes (fun ω => if forgery ω v then 1 else 0) else 0) := by
  apply composed_advantage_bound
  intro ω hw
  obtain ⟨ha, v, hb, hv, hq⟩ := game ω hw
  rcases boundary.extract (shards ω) ha with ho | hs
  · exact .inl ho
  · obtain ⟨sig, hsig⟩ := hs v hv
    exact .inr ⟨v, hb, detect ω v ⟨sig, hsig, hq⟩⟩
/-- The bad event is a union over independently verified leaf batches, not over internal
branches. This also applies when leaf proofs and adversary coins are arbitrarily correlated. -/
def treeBad {n : Nat} (bad : Shard n → Bool) : MergeTree n → Bool
  | .leaf s => bad s
  | .branch l r _ => treeBad bad l || treeBad bad r
theorem tree_union_bound {n tapes : Nat} (bad : Fin tapes → Shard n → Bool)
    (tree : MergeTree n) :
    (finSum tapes fun ω => if treeBad (bad ω) tree then 1 else 0) ≤
      (tree.leaves.map fun s => finSum tapes fun ω => if bad ω s then 1 else 0).sum := by
  induction tree with
  | leaf s =>
    change (finSum tapes fun ω => if bad ω s then 1 else 0) ≤ _
    simp only [MergeTree.leaves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact Nat.le_refl _
  | branch l r b il ir =>
    have h := finSum_indicator_or_le (fun ω => treeBad (bad ω) l)
      (fun ω => treeBad (bad ω) r)
    change (finSum tapes fun ω => if treeBad (bad ω) l || treeBad (bad ω) r then 1 else 0) ≤ _
    simp only [MergeTree.leaves, List.map_append, List.sum_append]
    omega
theorem additive_shard_bound {n tapes : Nat} (bad : Fin tapes → Shard n → Bool)
    (root : Header) (verify : Shard n → Bool) (tree : MergeTree n)
    (_accepted : checkTree root verify 16 tree = true) :
    tree.leaves.length ≤ 65536 ∧
    (finSum tapes fun ω => if treeBad (bad ω) tree then 1 else 0) ≤
      (tree.leaves.map fun s => finSum tapes fun ω => if bad ω s then 1 else 0).sum :=
  ⟨depth_sixteen root verify tree _accepted, tree_union_bound bad tree⟩
/-- An accepted root bit selects an accepted leaf under exactly the root statement.
Use this witness in the quorum reduction and sum its bad events with the preceding bound. -/
theorem selected_leaf {n : Nat} (root : Header) (verify : Shard n → Bool)
    (tree : MergeTree n) (v : Nat) (h : checkTree root verify 16 tree = true)
    (active : tree.bitmap.getLsbD v = true) :
    ∃ s ∈ tree.leaves, s.bitmap.getLsbD v = true ∧ s.header = root ∧ verify s = true := by
  have hs := binary_merge_sound root verify tree 16 h
  have hc := hs.2.1 v
  simp only [active, ite_true] at hc
  have hp : 0 < tree.leaves.countP (fun s => s.bitmap.getLsbD v) := by omega
  obtain ⟨s, hm, hb⟩ := List.countP_pos_iff.mp hp
  exact ⟨s, hm, hb, (hs.2.2.1 s hm).1, (hs.2.2.1 s hm).2.1⟩
theorem merged_quorum_reduction {n : Nat} (geom : AggSigGeometry)
    (custody : Fin n → Custody) (verify : Shard n → Bool) (bad : Shard n → Prop)
    (boundary : ExtractionBoundary geom custody verify bad) (root : Header)
    (tree : MergeTree n) (h : checkTree root verify 16 tree = true) (v : Fin n)
    (active : tree.bitmap.getLsbD v.val = true) :
    (∃ s ∈ tree.leaves, bad s) ∨
    QuorumForgery geom (custody v) (root.mode.message v.val) ∨
    quorumParticipated (custody v) (root.mode.message v.val) = true := by
  obtain ⟨s, hs, hv, hh, ha⟩ := selected_leaf root verify tree v.val h active
  rcases boundary.extract s ha with hb | hex
  · exact .inl ⟨s, hs, hb⟩
  · obtain ⟨sig, hsig⟩ := hex v hv
    rw [hh] at hsig
    cases hq : quorumParticipated (custody v) (root.mode.message v.val) with
    | false => exact .inr (.inl ⟨sig, hsig, hq⟩)
    | true => exact .inr (.inr rfl)
theorem schedule_floor {n : Nat} (root : Header) (verify : Shard n → Bool)
    (tree : MergeTree n) (h : checkTree root verify 16 tree = true)
    (s : Shard n) (hs : s ∈ tree.leaves) (st : WhirStageSpec) (ht : st ∈ s.schedule.stages) :
    2 ^ root.regime.queryExponentBits ≤ st.queryErrorDenominator := by
  obtain ⟨_, _, h2, h24, he⟩ := (binary_merge_sound root verify tree 16 h).2.2.1 s hs
  rw [he] at ht
  exact whirSchedule_stage_query_ge root.regime s.numVars h2 h24 st ht
/-! Reachable fixtures and mutations. The leaf-verifier fixture tests the structural layer;
it is deliberately not represented as a deployed WHIR proof. -/
def exampleHeader : Header := ⟨[0], .xmssPoseidon2, .bciksJohnsonQrom128, .shared [1]⟩
def exampleShard (b : BitVec 2) : Shard 2 := ⟨exampleHeader, b, [1], 2, (Qsag.WhirSecurityRegime.bciksJohnsonQrom128).schedule 2⟩
def exampleVerifier (s : Shard 2) : Bool := s.proof == [1]
def exampleTree : MergeTree 2 := .branch (.leaf (exampleShard 1#2))
  (.leaf (exampleShard 2#2)) 3#2
theorem inhabited_tree : ∃ root verify tree,
    checkTree (n := 2) root verify 16 tree = true ∧ tree.bitmap.getLsbD 0 = true ∧
    ∃ s ∈ tree.leaves, ∃ st : WhirStageSpec, st ∈ s.schedule.stages :=
  ⟨exampleHeader, exampleVerifier, exampleTree, by decide, by decide,
    exampleShard 1#2, by simp [exampleTree, MergeTree.leaves],
    (whirStageSchedule 2).stages.headD ⟨0,0,0⟩, by decide⟩
theorem tooth_overlap : ∃ a b : BitVec 2,
    a &&& b ≠ 0#2 ∧ weight (a ||| b) < weight a + weight b ∧
    checkTree exampleHeader exampleVerifier 16
      (.branch (.leaf (exampleShard a)) (.leaf (exampleShard b)) (a ||| b)) = false :=
  ⟨1#2, 1#2, by decide, by decide, by decide⟩
theorem tooth_downgrade : ∃ s : Shard 2,
    s.header.regime ≠ exampleHeader.regime ∧
    checkTree exampleHeader exampleVerifier 16 (.leaf s) = false :=
  ⟨{ exampleShard 1#2 with header.regime := .bciksJohnsonClassical128 }, by decide, by decide⟩
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
    (finSum 1 fun ω => if total ω then 1 else 0) > 0 :=
  ⟨fun _ => true, fun _ => true, fun _ _ => rfl, by decide⟩
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
/-- The outer-bad branch is reachable; the honest approval branch has its own fixture. -/
theorem inhabited_reduction : ∃ geom custody verify bad,
    ExtractionBoundary (n := 2) geom custody verify bad ∧
    ∃ s : Shard 2, ∃ v : Fin 2, verify s = true ∧ s.bitmap.getLsbD v.val = true ∧
    ∃ root tree, checkTree root verify 16 tree = true ∧ tree.bitmap.getLsbD v.val = true := by
  refine ⟨compactAuditGeom, (fun _ => exampleCustody), exampleVerifier,
    (fun _ => True), ⟨fun _ _ => .inl trivial⟩, exampleShard 1#2, ⟨0, by decide⟩,
    by decide, by decide, exampleHeader, exampleTree, by decide, by decide⟩
theorem inhabited_union : ∃ total outer : Fin 2 → Bool,
    ∃ quorum : Fin 2 → Fin 2 → Bool, ∃ B : BitVec 2,
    (∀ ω, total ω = true → outer ω = true ∨
      ∃ v : Fin 2, B.getLsbD v.val = true ∧ quorum ω v = true) ∧
    (finSum 2 fun ω => if total ω then 1 else 0) = 2 := by
  refine ⟨(fun _ => true), (fun ω => decide (ω.val = 0)),
    (fun ω v => decide (ω.val = 1 ∧ v.val = 1)), 3#2, ?_, ?_⟩ <;> decide
theorem inhabited_composed_game : ∃ (geom : AggSigGeometry) (custody : Fin 2 → Custody)
    (verify outer : Shard 2 → Bool),
    ExtractionBoundary (n := 2) geom custody verify (fun s => outer s = true) ∧
    ∃ shards : Fin 1 → Shard 2, ∃ attack : Fin 1 → Bool, ∃ B : BitVec 2,
    ∃ forgery : Fin 1 → Fin 2 → Bool,
    (∀ ω, attack ω = true → verify (shards ω) = true ∧
      ∃ v : Fin 2, B.getLsbD v.val = true ∧ (shards ω).bitmap.getLsbD v.val = true ∧
        quorumParticipated (custody v) ((shards ω).header.mode.message v.val) = false) ∧
    (∀ ω v, QuorumForgery geom (custody v)
      ((shards ω).header.mode.message v.val) → forgery ω v = true) := by
  refine ⟨compactAuditGeom, (fun _ => { exampleCustody with honestApprovers := [] }),
    exampleVerifier, (fun _ => true), ⟨fun _ _ => .inl rfl⟩,
    (fun _ => exampleShard 1#2), (fun _ => true), 1#2, (fun _ _ => true), ?_, ?_⟩
  · intro ω _; exact ⟨rfl, ⟨0, by decide⟩, by decide,
      by change (1#2).getLsbD 0 = true; decide, rfl⟩
  · intro _ _ _; rfl
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
theorem inhabited_shard_bound : ∃ root verify tree, ∃ bad : Fin 2 → Shard 2 → Bool,
    checkTree root verify 16 tree = true ∧
    (finSum 2 fun ω => if treeBad (bad ω) tree then 1 else 0) = 2 :=
  ⟨exampleHeader, exampleVerifier, exampleTree, (fun _ _ => true), by decide, by decide⟩
#verify_constructive weight_union binary_merge_sound depth_sixteen honest_threshold
#verify_constructive quorum_aggregation_reduction composed_advantage_bound quorum_advantage_from_extraction
#verify_constructive insert_length eval_insert eval_insert_self quot_insert insert_quot
#verify_constructive vectors_length vectors_mem vectors_nodup solutions_length solutions_nodup
#verify_constructive pivot solutions_exact epoch_exact transcripts_exact transcripts_nodup
#verify_constructive mobile_uniform_fibers retained_shares_determine_secret
#verify_constructive tree_union_bound additive_shard_bound selected_leaf schedule_floor
#verify_constructive merged_quorum_reduction mobile_covers_entire_roster
#verify_inhabited binary_merge_sound inhabited_tree
#verify_inhabited additive_shard_bound inhabited_shard_bound
#verify_inhabited depth_sixteen inhabited_tree
#verify_inhabited selected_leaf inhabited_tree
#verify_inhabited schedule_floor inhabited_tree
#verify_inhabited honest_threshold inhabited_approval
#verify_inhabited quorum_aggregation_reduction inhabited_reduction
#verify_inhabited merged_quorum_reduction inhabited_reduction
#verify_inhabited composed_advantage_bound inhabited_union
#verify_inhabited quorum_advantage_from_extraction inhabited_composed_game
#verify_inhabited retained_shares_determine_secret inhabited_reconstruction
#verify_inhabited solutions_exact inhabited_reconstruction
#verify_inhabited mobile_uniform_fibers inhabited_mobile
#tooth_pair binary_merge_sound vs tooth_overlap
#tooth_pair binary_merge_sound vs tooth_downgrade
#tooth_pair schedule_floor vs tooth_downgrade
#tooth_pair honest_threshold vs tooth_full_corrupt
#tooth_pair quorum_aggregation_reduction vs tooth_full_corrupt
#tooth_pair merged_quorum_reduction vs tooth_full_corrupt
#tooth_pair composed_advantage_bound vs tooth_omit_outer
#tooth_pair quorum_advantage_from_extraction vs tooth_omit_outer
#tooth_pair mobile_uniform_fibers vs tooth_retained_polynomial
#tooth_pair epoch_exact vs tooth_retained_polynomial
#tooth_pair solutions_exact vs tooth_retained_polynomial
#tooth_pair retained_shares_determine_secret vs tooth_retained_polynomial
#tooth_pair additive_shard_bound vs tooth_overlap
/-- Publicly determined nonconstant coefficients make even one share distinguish secrets. -/
theorem tooth_public_coefficients {F : Type} [LawfulCommRing F] (s t x : F) (r : List F)
    (hne : s ≠ t) : RoundPoly.evalCoeffs (s :: r) x ≠ RoundPoly.evalCoeffs (t :: r) x := by
  intro h
  apply hne
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul x (RoundPoly.evalCoeffs r x))
  simpa only [RoundPoly.evalCoeffs_cons, LawfulCommRing.add_comm] using h
#tooth_pair mobile_uniform_fibers vs tooth_public_coefficients
end Qsag.Composed
