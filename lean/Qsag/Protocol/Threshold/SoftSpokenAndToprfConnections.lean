module
public import Qsag.Protocol.Threshold.LatticePreprocessingFull
public import Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 600

abbrev SliceField := Math.Gf2Pow128
abbrev SliceResponse := SliceField → SliceField →
  (SliceField × SliceField) × (Nat → SoftSpokenSliceClaim SliceField)

/-- Count accepting keys in the high-disagreement branch. The response sees
    both column hash keys before it chooses the claimed compressed values. -/
def highDisagreementPass (ss : List (SoftSpokenSliceCols SliceField)) (adv : SliceResponse)
    (u v : SliceField) : Nat :=
  let a := adv u v
  if 121 ≤ softspokenActiveSlices u v a.1 ss then
    bvSum (2 * ss.length) (fun d => if softspokenAllSlicesPass u v a.1 a.2 ss d then 1 else 0)
  else 0

private theorem highDisagreement_le (ss : List (SoftSpokenSliceCols SliceField))
    (len : ss.length = 128) (adv : SliceResponse) (u v : SliceField) :
    highDisagreementPass ss adv u v ≤ 2^14 := by
  unfold highDisagreementPass
  dsimp only
  split
  · rename_i ha
    have h := (softspoken_vole_subspace_soundness 0 [] .nil ss adv).1 u v
    apply Nat.le_trans h
    apply Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 4) (show
      ss.length - softspokenActiveSlices u v (adv u v).1 ss ≤ 7 by omega))
    decide
  · exact Nat.zero_le _

private theorem sum_map_le_const {T : Type} (l : List T) (f : T → Nat)
    (b : Nat) (h : ∀ t ∈ l, f t ≤ b) : (l.map f).sum ≤ l.length * b := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm] using
      Nat.add_le_add (h t (.head _)) (ih (fun u hu => h u (.tail _ hu)))

/-- Union bound in the product experiment (two hash keys, one 256-bit
    correlation). The collision branch uses a pair of columns fixed in advance.
    At least 121 active slices cost 242 bits, leaving slack in a 241-bit budget. -/
theorem softspoken_high_disagreement_and_fixed_collision
    (B : Nat) (S : List SliceField) (nd : S.Nodup)
    (ss : List (SoftSpokenSliceCols SliceField)) (len : ss.length = 128) (adv : SliceResponse)
    (l r : SoftSpokenSliceCols SliceField) (hl : l ∈ ss) (hr : r ∈ ss)
    (same : l.xCol.payload.length = r.xCol.payload.length)
    (size : l.xCol.payload.length ≤ B) (ne : l.xCol ≠ r.xCol) :
    (S.map fun u => (S.map (highDisagreementPass ss adv u)).sum).sum +
      otExtHashZeroPairCount S (otExtColSub l.xCol r.xCol) * 2^256 ≤
      S.length * (S.length * 2^14) + B^2 * 2^256 := by
  apply Nat.add_le_add
  · exact sum_map_le_const _ _ _ fun u _ => sum_map_le_const _ _ _ fun v _ =>
      highDisagreement_le ss len adv u v
  · exact Nat.mul_le_mul_right _ (((softspoken_vole_subspace_soundness B S nd ss adv).2.1
      l hl r hr same size ne).1)


/-- A Boolean coordinate of a selective-abort query is unrestricted,
    impossible, or pinned. Compiling the query requires no bit of Δ. -/
inductive CoordinateGuard where | free | impossible | pin (b : Bool)

def CoordinateGuard.ofTest (t : Bool → Bool) : CoordinateGuard :=
  match t false,t true with
  | false,false => .impossible
  | false,true => .pin true
  | true,false => .pin false
  | true,true => .free

def CoordinateGuard.allows : CoordinateGuard → Bool → Bool
  | .free,_ => true
  | .impossible,_ => false
  | .pin a,b => a == b

private theorem allows_ofTest (t : Bool → Bool) (b : Bool) :
    (CoordinateGuard.ofTest t).allows b = t b := by
  cases b <;> cases hf : t false <;> cases ht : t true <;> simp [CoordinateGuard.ofTest,hf,ht,CoordinateGuard.allows]

inductive SliceQuery : Nat → Type where
  | nil : SliceQuery 0
  | cons {n : Nat} (lo hi : CoordinateGuard) (rest : SliceQuery n) : SliceQuery (n+1)

def SliceQuery.member : {n : Nat} → SliceQuery n → BitVec (2*n) → Bool
  | _,.nil,_ => true
  | _,@SliceQuery.cons n lo hi rest,d =>
    lo.allows (d.getLsbD (2*n)) && hi.allows (d.getLsbD (2*n+1)) &&
      rest.member (d.setWidth (2*n))

def compileSliceQuery (u v : SliceField) (adv : SliceResponse) :
    (ss : List (SoftSpokenSliceCols SliceField)) → SliceQuery ss.length
  | [] => .nil
  | sl :: rest =>
    let (x,claims) := adv u v
    let xh := otExtCheckHash u v sl.xCol
    let cl := claims rest.length
    .cons (.ofTest (otSingleColPasses (otExtCheckHash u v sl.tLoCol) xh cl.tLoHat x))
      (.ofTest (otSingleColPasses (otExtCheckHash u v sl.tHiCol) xh cl.tHiHat x))
      (compileSliceQuery u v adv rest)

theorem simulated_selective_abort_exact (u v : SliceField) (adv : SliceResponse)
    (ss : List (SoftSpokenSliceCols SliceField)) (d : BitVec (2*ss.length)) :
    (compileSliceQuery u v adv ss).member d =
      softspokenAllSlicesPass u v (adv u v).1 (adv u v).2 ss d := by
  induction ss with
  | nil => simp only [compileSliceQuery, SliceQuery.member, softspokenAllSlicesPass.public_eq_1]
  | cons sl rest ih => simp only [compileSliceQuery,SliceQuery.member,allows_ofTest,ih,
      softspokenAllSlicesPass.public_eq_2,otF4SlicePasses.public_eq_1]

/-- A simulator of the consistency decision can abort on high disagreement.
    Its sole key-dependent operation otherwise is a coordinate-subspace query. -/
def simulateConsistency (u v : SliceField) (adv : SliceResponse)
    (ss : List (SoftSpokenSliceCols SliceField)) (d : BitVec (2*ss.length)) : Bool :=
  if 121 ≤ softspokenActiveSlices u v (adv u v).1 ss then false
  else (compileSliceQuery u v adv ss).member d

def consistencyDisagreements (ss : List (SoftSpokenSliceCols SliceField))
    (adv : SliceResponse) (u v : SliceField) : Nat :=
  bvSum (2*ss.length) fun d => if simulateConsistency u v adv ss d =
      softspokenAllSlicesPass u v (adv u v).1 (adv u v).2 ss d then 0 else 1

private theorem consistency_count_eq (ss : List (SoftSpokenSliceCols SliceField))
    (adv : SliceResponse) (u v : SliceField) :
    consistencyDisagreements ss adv u v = highDisagreementPass ss adv u v := by
  unfold consistencyDisagreements simulateConsistency highDisagreementPass
  dsimp only
  split
  · congr 1
    funext d
    cases softspokenAllSlicesPass u v (adv u v).1 (adv u v).2 ss d <;> rfl
  · simp only [simulated_selective_abort_exact,↓reduceIte,bvSum_const,Nat.mul_zero]

/-- For the accept/abort observation, couple real and simulated decisions on
    the same hash keys and correlation. Count the fixed-pair collision as a
    total loss. The common sample space has 2^512 elements. -/
theorem softspoken_consistency_simulation_budget
    (B : Nat) (S : List SliceField) (nd : S.Nodup) (full : S.length = 2^128)
    (ss : List (SoftSpokenSliceCols SliceField)) (len : ss.length = 128) (adv : SliceResponse)
    (l r : SoftSpokenSliceCols SliceField) (hl : l ∈ ss) (hr : r ∈ ss)
    (same : l.xCol.payload.length = r.xCol.payload.length)
    (size : l.xCol.payload.length ≤ B) (ne : l.xCol ≠ r.xCol) :
    (S.map fun u => (S.map (consistencyDisagreements ss adv u)).sum).sum +
      otExtHashZeroPairCount S (otExtColSub l.xCol r.xCol) * 2^256 ≤
        (2^15+B^2)*2^256 := by
  simp only [funext (consistency_count_eq ss adv _)]
  have h := softspoken_high_disagreement_and_fixed_collision B S nd ss len adv l r hl hr same size ne
  rw [full] at h
  exact Nat.le_trans h (by rw [Nat.add_mul]; apply Nat.add_le_add_right; decide +kernel)

/-- With the requested common denominator the strict target has an exact block ceiling. -/
theorem softspoken_budget_lt_128_iff (B : Nat) :
    2^15 + B^2 < 2^128 ↔ B < 2^64 := by
  constructor
  · intro h
    apply Nat.lt_of_not_ge
    intro hb
    have hm := Nat.pow_le_pow_left hb 2
    change (2^128 : Nat) ≤ B^2 at hm
    omega
  · intro h
    have hle : B ≤ 2^64-1 := by omega
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.pow_le_pow_left hle 2) _) (by decide +kernel)

namespace SpdzToprf
open CommRingOps

/-- A strategy chooses its next input and tampering from previously released values.
    Each history describes a full family over the *same* initial MAC-key sample. -/
structure EvaluationWorlds (n : Nat) where
  material : GoldilocksExt2 → SpdzServers n × SpdzSession n
  k : Lane4
  x : Lane4
  adv : EvalTamper
  key : ∀ a, (material a).1.macKey = a
  servers : ∀ a, ServersValid (material a).1 k
  sessions : ∀ a, SessionValid (material a).1 (material a).2
  plane : ∀ a b, SameValuePlane (material a).1 (material b).1 (material a).2 (material b).2

abbrev keyAt := MacBlind.goldilocksExt2Enum.toFun

def EvaluationWorlds.fooled {n : Nat} (e : EvaluationWorlds n) (i : Fin (goldilocksPrime^2)) :=
  evalFooled (e.material (keyAt i)).1 (e.material (keyAt i)).2 e.k e.x e.adv

private theorem one_fooled {n : Nat} (e : EvaluationWorlds n) :
    qsum _ (fun i => if e.fooled i then 1 else 0) ≤ 1 := by
  apply qsum_indicator_le_one_of_unique
  intro i j hi hj
  have h := evalFooled_macKey_unique e.k e.x e.adv (e.servers _) (e.servers _)
    (e.sessions _) (e.sessions _) (e.plane _ _) hi hj
  rw [e.key,e.key] at h
  exact (MacBlind.goldilocksExt2Enum.left_inv i).symm.trans
    ((congrArg MacBlind.goldilocksExt2Enum.invFun h).trans (MacBlind.goldilocksExt2Enum.left_inv j))

/-- Stop on rejection or the first incorrect release. On that release, charge
    this event only if all blinding randomizers survived. -/
def firstForgedRelease {n : Nat} (choose : List Lane4 → EvaluationWorlds n)
    (i : Fin (goldilocksPrime^2)) : Nat → List Lane4 → Bool
  | 0, _ => false
  | q+1, hist =>
    let e := choose hist
    let m := e.material (keyAt i)
    let v := spdzEval m.1 m.2 e.x e.adv
    if !v.accept then false else
    if v.out = evalAlgebraicOprf e.k e.x then firstForgedRelease choose i q (v.out :: hist)
    else e.fooled i

theorem adaptive_mac_forgery_bound {n : Nat} (choose : List Lane4 → EvaluationWorlds n) (Q : Nat) :
    ∀ hist, qsum (goldilocksPrime^2) (fun i => if firstForgedRelease choose i Q hist then 1 else 0) ≤ Q := by
  induction Q with
  | zero => intro hist; simp only [firstForgedRelease, Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero, Nat.le_refl]
  | succ q ih =>
    intro hist
    let e := choose hist
    let next := evalAlgebraicOprf e.k e.x :: hist
    let later := fun i => firstForgedRelease choose i q next
    apply Nat.le_trans (m := qsum _ (fun i => if e.fooled i || later i then 1 else 0))
    · apply qsum_le_qsum
      intro i
      let m := e.material (keyAt i)
      let v := spdzEval m.1 m.2 e.x e.adv
      change (if (if !v.accept then false else if v.out = evalAlgebraicOprf e.k e.x then
        firstForgedRelease choose i q (v.out :: hist) else e.fooled i) then 1 else 0) ≤ _
      by_cases acc : (!v.accept) = true
      · simp only [acc, ↓reduceIte]; exact Nat.zero_le _
      · simp only [acc]
        by_cases good : v.out = evalAlgebraicOprf e.k e.x
        · rw [ite_eq_left good, good]
          change (if later i then 1 else 0) ≤ _
          cases e.fooled i <;> cases later i <;> decide
        · rw [ite_eq_right good]
          cases e.fooled i <;> cases later i <;> decide
    · apply Nat.le_trans (qsum_indicator_or_le _ _)
      exact Nat.le_trans (Nat.add_le_add (one_fooled e) (ih next)) (by omega)

/-- Each corrupt summand is fixed before its matching honest draw, but can
    depend on all earlier draws, including those of earlier evaluations. -/
def adaptiveCancellation (pick : List GoldilocksExt2 → GoldilocksExt2) :
    List GoldilocksExt2 → List GoldilocksExt2 → Bool
  | _, [] => false
  | hist, r :: rs => decide (add r (pick hist) = zero) || adaptiveCancellation pick (r :: hist) rs

private theorem sum_constant (m b : Nat) :
    nsum MacBlind.goldilocksExt2Enum m (fun _ => b) = (goldilocksPrime^2)^m * b := by
  induction m with
  | zero => simp [nsum]
  | succ m ih =>
    change qsum _ (fun _ => nsum MacBlind.goldilocksExt2Enum m (fun _ => b)) = _
    rw [qsum_const, ih, Nat.pow_succ (goldilocksPrime^2) m]; ac_rfl

private theorem one_cancellation (c : GoldilocksExt2) :
    qsum (goldilocksPrime^2) (fun i => if add (keyAt i) c = zero then 1 else 0) ≤ 1 := by
  let N := goldilocksPrime^2
  let test := fun i : Fin N => decide (add (keyAt i) c = zero)
  have eqv : (fun i : Fin N => if add (keyAt i) c = zero then 1 else 0) =
      (fun i => if test i then 1 else 0) := by funext i; simp only [test, decide_eq_true_eq]
  rw [eqv]
  apply qsum_indicator_le_one_of_unique N test
  intro i j hi hj
  have h₁ := of_decide_eq_true (show decide (add (keyAt i) c = zero) = true from hi)
  have h₂ := of_decide_eq_true (show decide (add (keyAt j) c = zero) = true from hj)
  have h := LawfulCommRing.add_left_cancel ((LawfulCommRing.add_comm c _).trans
    (h₁.trans (h₂.symm.trans (LawfulCommRing.add_comm _ c))))
  exact (MacBlind.goldilocksExt2Enum.left_inv i).symm.trans
    ((congrArg MacBlind.goldilocksExt2Enum.invFun h).trans (MacBlind.goldilocksExt2Enum.left_inv j))

theorem adaptive_cancellation_count (pick : List GoldilocksExt2 → GoldilocksExt2) (m : Nat) :
    ∀ hist, (goldilocksPrime^2) * nsum MacBlind.goldilocksExt2Enum m
      (fun rs => if adaptiveCancellation pick hist rs then 1 else 0) ≤ m * (goldilocksPrime^2)^m := by
  let N := goldilocksPrime^2
  induction m with
  | zero => intro hist; simp [nsum, adaptiveCancellation]
  | succ m ih =>
    intro hist
    let hit := fun i => if add (keyAt i) (pick hist) = zero then 1 else 0
    rw [nsum, ← qsum_mul_left]
    apply Nat.le_trans (m := qsum N (fun i => hit i * (N * N^m) + m * N^m))
    · apply qsum_le_qsum
      intro i
      by_cases h : add (keyAt i) (pick hist) = zero
      · simp only [adaptiveCancellation, keyAt] at h ⊢
        simp [hit, keyAt, h, sum_constant, N]
      · change N * nsum _ m (fun rs => if adaptiveCancellation pick hist (keyAt i :: rs) then 1 else 0) ≤ _
        simpa only [adaptiveCancellation, decide_eq_false h, Bool.false_or, hit, ite_eq_right h,
          Nat.zero_mul, Nat.zero_add] using ih (keyAt i :: hist)
    · rw [qsum_add, qsum_mul_right, qsum_const]
      have h : qsum N hit ≤ 1 := one_cancellation _
      calc qsum N hit * (N*N^m) + N*(m*N^m) ≤ 1*(N*N^m) + N*(m*N^m) :=
             Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _
           _ = (m+1) * N^(m+1) := by
             rw [Nat.one_mul, Nat.succ_mul, Nat.pow_succ N m]; simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

def lanesPerEvaluation := 12 * (poseidonRounds.length + 1)

theorem lanesPerEvaluation_eq : lanesPerEvaluation = 372 := by
  unfold lanesPerEvaluation
  rw [poseidonRounds.public_eq_1]
  simp only [List.length_append,List.length_map,poseidon2InitialExtConsts_length,
    poseidon2InternalConsts_length,poseidon2TerminalExtConsts_length]

theorem multi_eval_cancellation_bound (pick : List GoldilocksExt2 → GoldilocksExt2) (Q : Nat)
    (hist : List GoldilocksExt2) :
    goldilocksPrime * nsum MacBlind.goldilocksExt2Enum (Q * lanesPerEvaluation)
      (fun rs => if adaptiveCancellation pick hist rs then 1 else 0) ≤
      Q * (goldilocksPrime^2)^(Q * lanesPerEvaluation) := by
  have h := adaptive_cancellation_count pick (Q * lanesPerEvaluation) hist
  have hl : lanesPerEvaluation ≤ goldilocksPrime := by rw [lanesPerEvaluation_eq]; decide +kernel
  have hb := Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left Q hl))
  exact Nat.le_of_mul_le_mul_left (c := goldilocksPrime) (by
    simpa only [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hb) (by decide)

theorem tooth_after_open_cancellation :
    ∃ pick : GoldilocksExt2 → GoldilocksExt2, ∀ r : GoldilocksExt2,
      blindDegenerate (fun _ => pick r) 0 [r] = true := by
  exact ⟨neg, fun r => by simp [blindDegenerate, LawfulCommRing.add_right_neg]⟩

theorem committed_blindDegenerate_eq (c : Nat → GoldilocksExt2) (hist rs : List GoldilocksExt2) :
    adaptiveCancellation (fun h => c h.length) hist rs = blindDegenerate c hist.length rs := by
  induction rs generalizing hist with
  | nil => rfl
  | cons r rs ih => simp only [adaptiveCancellation, blindDegenerate, ih, List.length_cons]

#tooth_pair committed_blindDegenerate_eq vs tooth_after_open_cancellation

/-- Preprocessing uses one server family throughout the run. Its value plane is
    fixed across the possible MAC keys. Each entry is consumed exactly once. -/
structure SessionTapeEntry {n : Nat} (srv : GoldilocksExt2 → SpdzServers n) where
  atKey : GoldilocksExt2 → SpdzSession n
  valid : ∀ a, SessionValid (srv a) (atKey a)
  plane : ∀ a b, SameValuePlane (srv a) (srv b) (atKey a) (atKey b)

structure ServiceRequest where
  port : Spec.CredPort
  ticket : Spec.ToprfTicket
  input : Spec.Bytes
  tamper : EvalTamper

private theorem ok_of_outcome {S O : Type} {v : StepOutcome S O Unit} {s : S} {o : O}
    (h : outcomeStep v = some (s,o)) : v = .ok s o := by
  cases v with
  | err => rw [outcomeStep.public_eq_2] at h; cases h
  | ok s' o' =>
    rw [outcomeStep.public_eq_1] at h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl

section Service
variable {Attr : Type} [DecidableEq Attr] {n : Nat}

private theorem release_properties (cfg : Spec.IdealCredConfig Lane4) (P : RealSpdzParams Attr)
    (c c' : RealSpdzState Attr n) (req : ServiceRequest) (out : Spec.IdealCredOutput Lane4)
    (k : Lane4) (hs : ServersValid c.servers k) (hv : ∀ s ∈ c.sessions, SessionValid c.servers s)
    (ok : (piToprfRealSpdzMachine cfg P c.servers c.sessions).step c
      (req.port,.evalReal req.ticket req.input req.tamper) = some (c',out)) :
    ∃ s rest, c.sessions = s :: rest ∧ c'.sessions = rest ∧ c'.servers = c.servers ∧
      (spdzEval c.servers s (realEvalInput P req.ticket req.input) req.tamper).accept = true ∧
      out = .toprfEvaluated (spdzEval c.servers s (realEvalInput P req.ticket req.input) req.tamper).out := by
  obtain ⟨s,rest,queue,tail,output,_⟩ := piToprfRealSpdz_sound_or_mac_forgery cfg P
    c.servers c.sessions k hs hv ok
  have h : outcomeStep (evalOutcome cfg P c req.port req.ticket req.input req.tamper c.sessions) =
      some (c',out) := by
    simpa only [realSpdzMachine_eval_step] using ok
  rw [queue] at h
  rw [evalOutcome.public_eq_2] at h
  split at h
  · rename_i acc
    obtain ⟨_,_,_,next,_⟩ := evalFinish_ok (ok_of_outcome h)
    exact ⟨s,rest,queue,tail,next ▸ rfl,acc,output⟩
  · rw [outcomeStep.public_eq_2] at h
    cases h

/-- Run the ticket-gated machine. A rejection terminates the run. The adversary
    sees each released value before it chooses its next ticket, input and errors. -/
def serviceReleaseEvent (includeCancelled : Bool) (cfg : Spec.IdealCredConfig Lane4) (P : RealSpdzParams Attr)
    (k : Lane4) (choose : List Lane4 → ServiceRequest) :
    Nat → List Lane4 → RealSpdzState Attr n → Bool
  | 0, _, _ => false
  | q+1, hist, c =>
    let r := choose hist
    match (piToprfRealSpdzMachine cfg P c.servers c.sessions).step c
        (r.port,.evalReal r.ticket r.input r.tamper), c.sessions with
    | some (next,.toprfEvaluated y), s :: _ =>
      if y = evalAlgebraicOprf k (realEvalInput P r.ticket r.input) then
        serviceReleaseEvent includeCancelled cfg P k choose q (y :: hist) next
      else includeCancelled || !blindDegenerate r.tamper.rCorrupt 0 s.rHonest
    | _, _ => false

abbrev serviceFirstForgery (cfg : Spec.IdealCredConfig Lane4) (P : RealSpdzParams Attr)
    (k : Lane4) (choose : List Lane4 → ServiceRequest) (q : Nat) (hist : List Lane4) (c : RealSpdzState Attr n) :=
  serviceReleaseEvent false cfg P k choose q hist c

set_option maxRecDepth 4096 in
/-- At most Q of the p² persistent MAC keys release a first false value without
    cancellation. Ticket rejection can only remove keys from the winning set. -/
theorem piToprfRealSpdz_multi_eval_mac_bound (cfg : Spec.IdealCredConfig Lane4)
    (P : RealSpdzParams Attr) (k : Lane4) (choose : List Lane4 → ServiceRequest)
    (srv : GoldilocksExt2 → SpdzServers n) (key : ∀ a, (srv a).macKey = a)
    (valid : ∀ a, ServersValid (srv a) k) (tape : List (SessionTapeEntry srv)) :
    ∀ (hist : List Lane4) (svc : GoldilocksExt2 → PiToprfCredState Attr Lane4),
    qsum (goldilocksPrime^2) (fun i =>
      if serviceFirstForgery cfg P k choose tape.length hist
        ⟨svc (keyAt i),srv (keyAt i),tape.map (fun s => s.atKey (keyAt i))⟩ then 1 else 0)
      ≤ tape.length := by
  induction tape with
  | nil => intro hist svc; simp [serviceFirstForgery,serviceReleaseEvent,qsum_const]
  | cons row rest ih =>
    intro hist svc
    let r := choose hist
    let x := realEvalInput P r.ticket r.input
    let ideal := evalAlgebraicOprf k x
    let e : EvaluationWorlds n := ⟨fun a => (srv a,row.atKey a),k,x,r.tamper,key,valid,row.valid,row.plane⟩
    let curr := fun a => (⟨svc a,srv a,(row::rest).map (fun s => s.atKey a)⟩ : RealSpdzState Attr n)
    let step := fun a => (piToprfRealSpdzMachine cfg P (curr a).servers (curr a).sessions).step
      (curr a) (r.port,.evalReal r.ticket r.input r.tamper)
    let laterSvc := fun a => ((step a).map (fun z => z.1.svc)).getD (svc a)
    let later := fun i => serviceFirstForgery cfg P k choose rest.length (ideal :: hist)
      ⟨laterSvc (keyAt i),srv (keyAt i),rest.map (fun s => s.atKey (keyAt i))⟩
    apply Nat.le_trans (m := qsum _ (fun i => if e.fooled i || later i then 1 else 0))
    · apply qsum_le_qsum
      intro i
      let a := keyAt i
      change (if serviceFirstForgery cfg P k choose (rest.length+1) hist (curr a) then 1 else 0) ≤ _
      cases he : step a with
      | none =>
        change (if (match step a, (curr a).sessions with
          | some (next,.toprfEvaluated y), s :: _ =>
            if y = ideal then serviceFirstForgery cfg P k choose rest.length (y::hist) next
            else !blindDegenerate r.tamper.rCorrupt 0 s.rHonest
          | _, _ => false) then 1 else 0) ≤ _
        simp [he]
      | some pair =>
        obtain ⟨next,out⟩ := pair
        have hv : ∀ s ∈ (curr a).sessions, SessionValid (curr a).servers s := by
          intro s mem
          obtain ⟨z,_,rfl⟩ := List.mem_map.mp mem
          exact z.valid a
        obtain ⟨s,ls,hq,ht,hs,acc,ho⟩ := release_properties cfg P (curr a) next r out k (valid a) hv he
        obtain ⟨rfl,rfl⟩ := List.cons.inj hq
        subst out
        let v := spdzEval (srv a) (row.atKey a) x r.tamper
        change (if (match step a, (curr a).sessions with
          | some (next,.toprfEvaluated y), s :: _ =>
            if y = ideal then serviceFirstForgery cfg P k choose rest.length (y::hist) next
            else !blindDegenerate r.tamper.rCorrupt 0 s.rHonest
          | _, _ => false) then 1 else 0) ≤ _
        rw [he]
        change (if (if v.out = ideal then serviceFirstForgery cfg P k choose rest.length (v.out :: hist) next
          else !blindDegenerate r.tamper.rCorrupt 0 (row.atKey a).rHonest) then 1 else 0) ≤ _
        by_cases good : v.out = ideal
        · have nextEq : next = ⟨laterSvc a,srv a,rest.map (fun z => z.atKey a)⟩ := by
            simp only [laterSvc,he,Option.map_some,Option.getD_some]
            cases next
            simp_all only [curr]
          rw [ite_eq_left good,good,nextEq]
          change (if later i then 1 else 0) ≤ _
          cases e.fooled i <;> cases later i <;> decide
        · rw [ite_eq_right good]
          have fooled : e.fooled i = !blindDegenerate r.tamper.rCorrupt 0 (row.atKey a).rHonest := by
            unfold EvaluationWorlds.fooled
            rw [evalFooled.public_eq_1]
            change (v.accept && !decide (v.out = ideal) && _) = _
            simp only [good, decide_false, Bool.not_false, show v.accept = true from acc, Bool.true_and]
            rfl
          rw [← fooled]
          cases e.fooled i <;> cases later i <;> decide
    · exact Nat.le_trans (qsum_indicator_or_le _ _)
        (Nat.le_trans (Nat.add_le_add (one_fooled e) (ih (ideal::hist) laterSvc)) (by simp only [List.length_cons]; omega))

/-- Potential cancellations along the ideal-output prefix. Up to the first
    wrong release this prefix fixes every next request for every surviving key. -/
def potentialCancellation (P : RealSpdzParams Attr) (k : Lane4) (choose : List Lane4 → ServiceRequest) :
    List Lane4 → List (List GoldilocksExt2) → Bool
  | _, [] => false
  | hist, rs :: rest =>
    let r := choose hist
    blindDegenerate r.tamper.rCorrupt 0 rs ||
      potentialCancellation P k choose (evalAlgebraicOprf k (realEvalInput P r.ticket r.input)::hist) rest

private theorem wrong_release_charged (cfg : Spec.IdealCredConfig Lane4) (P : RealSpdzParams Attr)
    (k : Lane4) (choose : List Lane4 → ServiceRequest) (Q : Nat) :
    ∀ hist (c : RealSpdzState Attr n), ServersValid c.servers k →
      (∀ s ∈ c.sessions, SessionValid c.servers s) →
      serviceReleaseEvent true cfg P k choose Q hist c = true →
      serviceFirstForgery cfg P k choose Q hist c = true ∨
        potentialCancellation P k choose hist (c.sessions.map SpdzSession.rHonest) = true := by
  induction Q with
  | zero => intro hist c _ _ h; cases h
  | succ q ih =>
    intro hist c hs hv h
    let r := choose hist
    cases he : (piToprfRealSpdzMachine cfg P c.servers c.sessions).step c
        (r.port,.evalReal r.ticket r.input r.tamper) with
    | none => simp [serviceReleaseEvent,r] at he h; rw [he] at h; cases h
    | some pair =>
      obtain ⟨next,out⟩ := pair
      obtain ⟨s,rest,hq,ht,hs',_,ho⟩ := release_properties cfg P c next r out k hs hv he
      subst out
      let v := (spdzEval c.servers s (realEvalInput P r.ticket r.input) r.tamper).out
      let ideal := evalAlgebraicOprf k (realEvalInput P r.ticket r.input)
      change (piToprfRealSpdzMachine cfg P c.servers c.sessions).step c
        ((choose hist).port,.evalReal (choose hist).ticket (choose hist).input (choose hist).tamper) =
        some (next,.toprfEvaluated v) at he
      simp only [serviceFirstForgery,serviceReleaseEvent,he] at h ⊢
      simp only [hq,List.map_cons,potentialCancellation,Bool.false_or] at h ⊢
      by_cases good : v = ideal
      · have tailValid : ∀ t ∈ next.sessions, SessionValid next.servers t := by
          rw [hs',ht]
          exact fun t hm => hv t (hq ▸ List.Mem.tail s hm)
        obtain hf | hc := ih (v::hist) next (hs' ▸ hs) tailValid (by simpa only [good,↓reduceIte,ideal,r] using h)
        · exact Or.inl (by simpa only [good,↓reduceIte,ideal,r] using hf)
        · apply Or.inr
          apply Bool.or_eq_true_iff.mpr
          exact Or.inr (by simpa only [ht,good,ideal,r] using hc)
      · cases deg : blindDegenerate r.tamper.rCorrupt 0 s.rHonest with
        | false => exact Or.inl (by change (if v = ideal then _ else _) = true; rw [ite_eq_right good]; rfl)
        | true => exact Or.inr (Bool.or_eq_true_iff.mpr (Or.inl rfl))

/-- Iterate a finite weighted sum, drawing one independent block per round. -/
def repeatedSum {A : Type} (draw : (A → Nat) → Nat) : Nat → (List A → Nat) → Nat
  | 0, f => f []
  | q+1, f => draw fun r => repeatedSum draw q (fun rs => f (r::rs))

def sumMaskBlocks (m : Nat) := repeatedSum (nsum MacBlind.goldilocksExt2Enum m)

abbrev blockSum := sumMaskBlocks lanesPerEvaluation

private theorem repeated_linear {A : Type} (draw : (A → Nat) → Nat) (weight : Nat)
    (linear : ∀ f a b, draw (fun r => f r*a+b) = draw f*a+weight*b)
    (q : Nat) (f : List A → Nat) (a b : Nat) :
    repeatedSum draw q (fun rs => f rs * a + b) = repeatedSum draw q f * a + weight^q*b := by
  induction q generalizing f with
  | zero => simp only [repeatedSum,Nat.pow_zero,Nat.one_mul]
  | succ q ih =>
    let g := fun r => repeatedSum draw q (fun rs => f (r::rs))
    calc _ = draw (fun r => g r*a + weight^q*b) :=
           congrArg draw (funext (fun r => ih (fun rs => f (r::rs))))
         _ = draw g*a + weight*(weight^q*b) := linear _ _ _
         _ = _ := by rw [Nat.pow_succ weight q,Nat.mul_comm (weight^q) weight,Nat.mul_assoc]; rfl

set_option maxRecDepth 4096

private abbrev M := goldilocksPrime^2
private abbrev W := M^lanesPerEvaluation

private theorem mask_linear (m : Nat) (f : List GoldilocksExt2 → Nat) (a b : Nat) :
    nsum MacBlind.goldilocksExt2Enum m (fun rs => f rs * a + b) =
      nsum MacBlind.goldilocksExt2Enum m f * a + M^m*b := by
  induction m generalizing f with
  | zero => simp [nsum]
  | succ m ih =>
    rw [nsum,nsum]
    rw [qsum_congr (fun i => ih (fun rs => f (keyAt i :: rs)))]
    rw [qsum_add,qsum_mul_right,qsum_const,Nat.pow_succ M m]
    rw [Nat.mul_comm (M^m) M,Nat.mul_assoc M]

private theorem mask_le (m : Nat) (f g : List GoldilocksExt2 → Nat)
    (h : ∀ rs, f rs ≤ g rs) : nsum MacBlind.goldilocksExt2Enum m f ≤ nsum MacBlind.goldilocksExt2Enum m g := by
  induction m generalizing f g with
  | zero => exact h []
  | succ m ih =>
    rw [nsum,nsum]
    apply qsum_le_qsum
    intro i
    exact ih (fun rs => f (keyAt i::rs)) (fun rs => g (keyAt i::rs)) (fun rs => h _)

private theorem block_le (m q : Nat) (f g : List (List GoldilocksExt2) → Nat)
    (h : ∀ rs, rs.length = q → f rs ≤ g rs) : sumMaskBlocks m q f ≤ sumMaskBlocks m q g := by
  induction q generalizing f g with
  | zero => exact h [] rfl
  | succ q ih =>
    change nsum _ m (fun r => sumMaskBlocks m q (fun rs => f (r::rs))) ≤
      nsum _ m (fun r => sumMaskBlocks m q (fun rs => g (r::rs)))
    apply mask_le
    intro r
    exact ih (fun rs => f (r::rs)) (fun rs => g (r::rs)) (fun rs len => h (r::rs) (by simp [len]))

private theorem block_linear (m q : Nat) (f : List (List GoldilocksExt2) → Nat) (a b : Nat) :
    sumMaskBlocks m q (fun rs => f rs * a + b) = sumMaskBlocks m q f * a + (M^m)^q*b :=
  repeated_linear (nsum MacBlind.goldilocksExt2Enum m) (M^m)
    (mask_linear m) q f a b

private theorem one_block_cancel (m : Nat) (c : Nat → GoldilocksExt2) :
    nsum MacBlind.goldilocksExt2Enum m
      (fun rs => (if blindDegenerate c 0 rs then 1 else 0) * M) ≤ m*M^m := by
  have h := adaptive_cancellation_count (fun hist => c hist.length) m []
  simp only [committed_blindDegenerate_eq,List.length_nil] at h
  have e := mask_linear m (fun rs => if blindDegenerate c 0 rs then 1 else 0) M 0
  simp only [Nat.add_zero,Nat.mul_zero] at e
  rw [e,Nat.mul_comm _ M]
  exact h

omit [DecidableEq Attr] in
private theorem potential_charge (m : Nat) (P : RealSpdzParams Attr) (k : Lane4) (choose : List Lane4 → ServiceRequest)
    (q : Nat) : ∀ hist, sumMaskBlocks m q (fun rs => (if potentialCancellation P k choose hist rs then 1 else 0)*M)
      ≤ q * m * (M^m)^q := by
  induction q with
  | zero => intro hist; simp only [sumMaskBlocks,repeatedSum,potentialCancellation,Bool.false_eq_true,↓reduceIte,Nat.zero_mul,Nat.le_refl]
  | succ q ih =>
    intro hist
    let r := choose hist
    let next := evalAlgebraicOprf k (realEvalInput P r.ticket r.input)::hist
    let hit := fun rs => (if blindDegenerate r.tamper.rCorrupt 0 rs then 1 else 0)*M
    change nsum _ m (fun rs => sumMaskBlocks m q (fun tail =>
      (if potentialCancellation P k choose hist (rs::tail) then 1 else 0)*M)) ≤ _
    apply Nat.le_trans (m := nsum MacBlind.goldilocksExt2Enum m
      (fun rs => hit rs * (M^m)^q + q * m * (M^m)^q))
    · apply mask_le
      intro rs
      cases he : blindDegenerate r.tamper.rCorrupt 0 rs with
      | false => simpa only [potentialCancellation,show (choose hist) = r from rfl,he,Bool.false_or,
          hit,Bool.false_eq_true,↓reduceIte,Nat.zero_mul,Nat.zero_add] using ih next
      | true =>
        have eqv := block_linear m q (fun _ => 0) 0 M
        simp only [Nat.mul_zero,Nat.zero_add] at eqv
        simp only [potentialCancellation,show (choose hist) = r from rfl,he,Bool.true_or,↓reduceIte,
          Nat.one_mul,eqv,hit]
        rw [Nat.mul_comm M]
        omega
    · rw [mask_linear]
      apply Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (one_block_cancel m _)) _)
      rw [Nat.succ_mul,Nat.add_mul,Nat.pow_succ (M^m)]
      simp only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc,Nat.add_comm,Nat.le_refl]

def SessionTapeEntry.withMask {srv : GoldilocksExt2 → SpdzServers n}
    (s : SessionTapeEntry srv) (rs : List GoldilocksExt2) : SessionTapeEntry srv :=
  ⟨fun a => {(s.atKey a) with rHonest := rs},
    fun a => by simpa only [SessionValid.public_eq_1] using s.valid a,
    fun a b => ⟨(s.plane a b).lam, (s.plane a b).key, (s.plane a b).masks⟩⟩

def assignMasks {srv : GoldilocksExt2 → SpdzServers n} :
    List (SessionTapeEntry srv) → List (List GoldilocksExt2) → List (SessionTapeEntry srv)
  | [], _ => []
  | s::ss, rs => s.withMask (rs.headD []) :: assignMasks ss rs.tail

private theorem assigned_length {srv : GoldilocksExt2 → SpdzServers n}
    (ss : List (SessionTapeEntry srv)) (rs : List (List GoldilocksExt2)) :
    (assignMasks ss rs).length = ss.length := by
  induction ss generalizing rs with
  | nil => rfl
  | cons s ss ih => simp [assignMasks,ih]

private theorem assigned_masks {srv : GoldilocksExt2 → SpdzServers n}
    (ss : List (SessionTapeEntry srv)) (rs : List (List GoldilocksExt2)) (a : GoldilocksExt2)
    (h : rs.length = ss.length) :
    ((assignMasks ss rs).map (fun s => s.atKey a)).map SpdzSession.rHonest = rs := by
  induction ss generalizing rs with
  | nil => cases rs <;> first | rfl | cases h
  | cons s ss ih =>
    cases rs with
    | nil => cases h
    | cons r rs => exact congrArg (r :: ·) (ih rs (Nat.succ.inj h))

/-- Wrong release in one joint experiment. The denominator is W^Q times p²,
    where W counts all honest mask vectors of a session. The two terms in the
    numerator are Q*W^Q for MAC forgery and 372*Q*W^Q for cancellation. -/
theorem piToprfRealSpdz_joint_false_release_bound (cfg : Spec.IdealCredConfig Lane4)
    (P : RealSpdzParams Attr) (k : Lane4) (choose : List Lane4 → ServiceRequest)
    (srv : GoldilocksExt2 → SpdzServers n) (key : ∀ a, (srv a).macKey = a)
    (valid : ∀ a, ServersValid (srv a) k) (tape : List (SessionTapeEntry srv))
    (hist : List Lane4) (svc : GoldilocksExt2 → PiToprfCredState Attr Lane4) :
    blockSum tape.length (fun rs => qsum (goldilocksPrime^2) (fun i =>
      if serviceReleaseEvent true cfg P k choose tape.length hist
        ⟨svc (keyAt i),srv (keyAt i),(assignMasks tape rs).map (fun s => s.atKey (keyAt i))⟩ then 1 else 0)) ≤
      (tape.length * lanesPerEvaluation + tape.length) * ((goldilocksPrime^2)^lanesPerEvaluation)^tape.length := by
  let cancel := fun rs => (if potentialCancellation P k choose hist rs then 1 else 0)*M
  apply Nat.le_trans (m := blockSum tape.length (fun rs => cancel rs * 1 + tape.length))
  · apply block_le lanesPerEvaluation
    intro rs len
    let t := assignMasks tape rs
    have mac := piToprfRealSpdz_multi_eval_mac_bound cfg P k choose srv key valid t hist svc
    simp only [t,assigned_length] at mac
    cases hc : potentialCancellation P k choose hist rs with
    | true =>
      simp only [cancel,hc,↓reduceIte,Nat.one_mul,Nat.mul_one]
      apply Nat.le_trans (m := qsum M (fun _ => 1))
      · apply qsum_le_qsum
        intro i
        split <;> decide
      · rw [qsum_const,Nat.mul_one]; omega
    | false =>
      simp only [cancel,hc,Bool.false_eq_true,↓reduceIte,Nat.zero_mul,Nat.zero_add]
      apply Nat.le_trans _ mac
      apply qsum_le_qsum
      intro i
      split
      · rename_i hw
        have hv : ∀ s ∈ t.map (fun s => s.atKey (keyAt i)), SessionValid (srv (keyAt i)) s := by
          intro s hm
          obtain ⟨z,_,rfl⟩ := List.mem_map.mp hm
          exact z.valid _
        obtain good | bad := wrong_release_charged cfg P k choose tape.length hist _ (valid _) hv hw
        · rw [ite_eq_left good]; exact Nat.le_refl _
        · rw [assigned_masks tape rs _ len,hc] at bad
          cases bad
      · exact Nat.zero_le _
  · rw [blockSum,block_linear lanesPerEvaluation tape.length cancel 1 tape.length,Nat.mul_one]
    exact Nat.le_trans (Nat.add_le_add_right (potential_charge lanesPerEvaluation P k choose tape.length hist) _)
      (by rw [Nat.add_mul,Nat.mul_comm (W^tape.length)]; exact Nat.le_refl _)

end Service

end SpdzToprf
end Qsag
