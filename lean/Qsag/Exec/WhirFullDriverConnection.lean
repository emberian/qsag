module
public import Qsag.Exec.WhirKernels
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Oracle.Qrom
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Exec
open Qsag
local notation "F" => QuarticGoldilocks
local notation "B" => List UInt8
local notation "Z" => (CommRingOps.zero : F)
local notation "I" => (CommRingOps.one : F)
set_option autoImplicit false

/-- Keep this dictionary opaque to the compiler's specializer. Some warm
    dependency modules contain proof-only specializations of these generic checks. -/
structure RingChecks (T : Type) where
  bridge : T → T → T → T → T → T → T → T → T → T → T
  kernel : T → List T → List T
  witness : List T → Nat → Nat → (Nat → T) → List T → T → List T → Bool
  eval : List T → T → T
  cosets : List T → (Nat → T) → List T → List Nat → Bool
  dot : List T → List T → T
  cascade : List T → List T → List (T × T) → T
  oracleAt : List T → List (Nat → T) → List (T × T) → Nat → T

@[noinline, nospecialize] private def ringChecks (T : Type) [CommRingOps T] [DecidableEq T] :
    RingChecks T :=
  ⟨hemBridgeFoldClaim,hemKernelFold,polyWitnessValid,RoundPoly.evalCoeffs,checkQueriedCosets,
    ringDot,evalCascadeClaim,evalCascadeOracle⟩

/-- The host uses the same calls in concrete and oracle experiments. -/
structure WhirHash where
  digest : B → B
  squeeze : B → B → F

def concreteWhirHash : WhirHash :=
  ⟨Aggregation.pcsMerkleHash, Aggregation.squeezeExt4Challenge⟩

structure AffineStageWire where
  cross0 : F
  cross1 : F
  cross2 : F
  shift0 : F
  shift1 : F
  nextRoot : B
  ood0 : F
  ood1 : F
  nextWord : List F
  polynomial : List F
  logLeaves : Nat
  salts : List B
  siblings : List B

structure FullOpening where
  shifts : List F
  cascadePolynomial : List F
  stages : List AffineStageWire
  finalCoeffs : List F

structure DriverState where
  domain : List F
  oracleAt : Nat → F
  /-- Source columns packed in each parent leaf, before the affine combination. -/
  columns : List (Nat → F)
  kernel : List F
  claim : F
  degree : Nat
  agree : Nat
  commitment : B
  fs : B
  pins : List Nat

private def absorb (prior : B) (tag : String) (fields : List B) :=
  encodeMultiFrame (prior :: tag.toUTF8.toList :: fields)

private def squeeze (h : WhirHash) (prior : B) (tag : String) := h.squeeze tag.toUTF8.toList prior

private def cascadeWeights (h : WhirHash) (seed : B) : Nat → List (F × F)
  | 0 => []
  | 1 => [(I,Z)]
  | n+2 =>
    let t := squeeze h seed "PCS_BATCH_AFFINE_THETA"
    let a := squeeze h seed "PCS_BATCH_AFFINE_ALPHA"
    let b := squeeze h seed "PCS_BATCH_AFFINE_BETA"
    (a,b) :: (CommRingOps.add I (CommRingOps.mul t a),CommRingOps.mul t b) ::
      (List.range n).map fun i =>
        let s := absorb seed "PCS_BATCH_INDEX" [leb128 (i+2)]
        (squeeze h s "PCS_BATCH_AFFINE_ALPHA",squeeze h s "PCS_BATCH_AFFINE_BETA")

structure HostStage where
  phi : F
  theta : F
  alpha : F
  beta : F
  z0 : F
  z1 : F
  indices : List Nat
  next : DriverState

private def prepareStage (h : WhirHash) (s : DriverState) (st : HemWhirStageSpec F)
    (w : AffineStageWire) (final : Option (List F)) : HostStage :=
  let cross := absorb s.fs "WHIR_AFFINE_CROSS" [Aggregation.encodePolyExt4 [w.cross0,w.cross1,w.cross2]]
  let phi := squeeze h cross "WHIR_AFFINE_PHI"
  let shift := absorb cross "WHIR_AFFINE_SHIFT" [Aggregation.encodePolyExt4 [phi,w.shift0,w.shift1]]
  let theta := squeeze h shift "WHIR_AFFINE_THETA"
  let alpha := squeeze h shift "WHIR_AFFINE_ALPHA"
  let beta := squeeze h shift "WHIR_AFFINE_BETA"
  let committed := absorb shift "WHIR_NEXT" [w.nextRoot, Aggregation.encodePolyExt4 [theta,alpha,beta]]
  let z0 := Aggregation.GoldilocksExt4.embedBase (squeeze h committed "WHIR_OOD_0").c0.c0
  let z1 := Aggregation.GoldilocksExt4.embedBase (squeeze h committed "WHIR_OOD_1").c0.c0
  let querySeed := absorb committed "WHIR_QUERY"
    [Aggregation.encodePolyExt4 [z0,z1,w.ood0,w.ood1],
     encodeMultiFrame (final.toList.map Aggregation.encodePolyExt4)]
  let groups := st.domainPts.length
  let count := st.queriedCosets.length
  let drawn := Aggregation.sampleDistinctLoop
    (fun i => (squeeze h (absorb querySeed "WHIR_QUERY_INDEX" [leb128 i]) "INDEX").c0.c0.val % groups)
    count (2*count) 0 []
  let selected := Aggregation.scanFillDistinct count (List.range groups) drawn
  let indices := if count ≤ 1 then selected else selected.mergeSort
  let next := (ringChecks F).bridge s.claim w.cross0 w.cross1 w.cross2 w.shift0 w.shift1 phi theta alpha beta
  ⟨phi,theta,alpha,beta,z0,z1,indices,
    ⟨st.domainPts,fun i => w.nextWord.getD i Z,[fun i => w.nextWord.getD i Z],
     (ringChecks F).kernel phi s.kernel,next,st.degBound,st.minAgree,w.nextRoot,querySeed,indices⟩⟩

def canopyBatch (h : WhirHash) (s : DriverState) (w : AffineStageWire) (p : HostStage) : Bool :=
  let leaves := (p.indices.zip w.salts).map fun (i,salt) =>
    let width := p.next.domain.length
    let vals := s.columns.flatMap fun col => [col i,col (width+i)]
    (i,h.digest (encodeMultiFrame [[0],leb128 i,salt,Aggregation.encodePolyExt4 vals]))
  decide (w.logLeaves ≤ 28) && decide (2^w.logLeaves = p.next.domain.length) &&
    decide (w.salts.length = p.indices.length) &&
    verifyCanopyMultiproof (fun i a b => h.digest (encodeMultiFrame [[1],leb128 i,a,b]))
      (fun d root => h.digest (encodeMultiFrame [[2],leb128 d,root]))
      w.logLeaves s.commitment leaves w.siblings

/-- Verify both domain points, the squared target and the actual affine butterfly
    on the exact source-oracle entries covered by the Canopy batch. -/
def queriedButterflies (s : DriverState) (p : HostStage) : Bool :=
  let groups := p.next.domain.length
  decide (s.domain.length = 2 * groups) &&
    p.indices.all fun i =>
      let u := s.domain.getD i Z
      let x := u.c0.c0
      decide (i < groups ∧ u = Aggregation.GoldilocksExt4.embedBase x ∧ x ≠ Goldilocks.zero ∧
        s.domain.getD (i+groups) Z = CommRingOps.neg u ∧
        p.next.domain.getD i Z = CommRingOps.mul u u ∧
        p.next.oracleAt i = hemAffineDuetFold (s.oracleAt i) (s.oracleAt (i+groups))
          x p.theta p.alpha p.beta)

def hostChecks (h : WhirHash) (s : DriverState) (st : HemWhirStageSpec F)
    (w : AffineStageWire) (p : HostStage) :=
  decide (p.indices = st.queriedCosets ∧ p.indices ≠ [] ∧ w.nextWord.length = st.domainPts.length) &&
    canopyBatch h s w p && queriedButterflies s p

def stageRound (w : AffineStageWire) (p : HostStage) : HemTranscriptRound F :=
  .stageFold p.next.oracleAt w.cross0 w.cross1 w.cross2 w.shift0 w.shift1
    p.phi p.theta p.alpha p.beta p.z0 p.z1 w.ood0 w.ood1 [w.polynomial]

def stageChecks (st : HemWhirStageSpec F) (w : AffineStageWire) (p : HostStage) :=
  (ringChecks F).witness st.domainPts st.minAgree st.degBound p.next.oracleAt p.next.kernel p.next.claim w.polynomial &&
    decide ((ringChecks F).eval w.polynomial p.z0 = w.ood0) &&
    decide ((ringChecks F).eval w.polynomial p.z1 = w.ood1) &&
    (ringChecks F).cosets st.domainPts p.next.oracleAt w.polynomial st.queriedCosets

/-- Tail agreement includes every last-stage fold and the specification's terminal indices. -/
def checkTail (pin : Bool) (s : DriverState) (coeffs : List F) :=
  decide (coeffs.length ≤ s.degree+1) && decide ((ringChecks F).dot coeffs s.kernel = s.claim) &&
    (!pin || ((ringChecks F).cosets s.domain s.oracleAt coeffs (List.range (min s.agree s.domain.length)) &&
      (ringChecks F).cosets s.domain s.oracleAt coeffs s.pins))

structure DriverRun where
  accepted : Bool
  transcript : List (HemTranscriptRound F)
  /-- Retain the exact inputs for inspecting every checked Canopy batch and fold. -/
  batches : List (DriverState × HemWhirStageSpec F × AffineStageWire × HostStage)

def driveStages (h : WhirHash) (pin : Bool) (tail : List F) (s : DriverState) :
    List (HemWhirStageSpec F) → List AffineStageWire → DriverRun
  | [], [] => ⟨checkTail pin s tail,[.finalQuery tail],[]⟩
  | st :: sts, w :: ws =>
    let p := prepareStage h s st w (if sts.isEmpty then some tail else none)
    let later := driveStages h pin tail p.next sts ws
    ⟨hostChecks h s st w p && stageChecks st w p && later.accepted,
     stageRound w p :: later.transcript, (s,st,w,p) :: later.batches⟩
  | _, _ => ⟨false,[],[]⟩

private theorem driveStages_sound (h : WhirHash) (tail : List F) (s : DriverState)
    (sts : List (HemWhirStageSpec F)) (ws : List AffineStageWire) :
    let r := driveStages h true tail s sts ws
    r.accepted = true →
      verifyHemStages s.oracleAt s.domain s.degree s.agree s.kernel s.claim sts r.transcript = true ∧
      ∀ b ∈ r.batches, canopyBatch h b.1 b.2.2.1 b.2.2.2 = true ∧
        queriedButterflies b.1 b.2.2.2 = true := by
  induction sts generalizing s ws with
  | nil =>
    cases ws with
    | nil =>
      intro _ ok
      have ht : checkTail true s tail = true := ok
      simp only [checkTail, Bool.not_true, Bool.false_or, Bool.and_eq_true] at ht
      exact ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ht.1,ht.2.1⟩, fun _ hx => nomatch hx⟩
    | cons => intro _ he; cases he
  | cons st rest ih =>
    cases ws with
    | nil => intro _ he; cases he
    | cons w ws =>
      intro r ok
      let p := prepareStage h s st w (if rest.isEmpty then some tail else none)
      change (hostChecks h s st w p && stageChecks st w p &&
        (driveStages h true tail p.next rest ws).accepted) = true at ok
      obtain ⟨⟨hc,hs⟩,hr⟩ := (Bool.and_eq_true_iff.mp ok).imp_left Bool.and_eq_true_iff.mp
      obtain ⟨hv,ha⟩ := ih p.next ws hr
      refine ⟨?_, ?_⟩
      · change (_ && verifyHemStages _ _ _ _ _ _ rest _) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨?_,hv⟩
        simp only [List.any_cons,List.any_nil,Bool.or_false]
        exact hs
      · intro b hb
        rcases List.mem_cons.mp hb with he | he
        · subst b
          exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hc).1).2,(Bool.and_eq_true_iff.mp hc).2⟩
        · exact ha _ he

/-- Public stage dimensions enter the transcript before the first squeeze.
    Actual query indices are derived later from the committed opening. -/
private def instanceFrame (inst : HemWhirInstance F) : B :=
  encodeMultiFrame [leb128 inst.batchOracles.length, Aggregation.encodePolyExt4 inst.initDomainPts,
    leb128 inst.initDegBound, leb128 inst.initMinAgree, encodeMultiFrame (inst.stages.map fun st =>
      encodeMultiFrame [Aggregation.encodePolyExt4 st.domainPts,leb128 st.degBound,
        leb128 st.minAgree,leb128 st.listBound,leb128 st.queriedCosets.length])]

def runFullOpening (h : WhirHash) (pin : Bool) (inst : HemWhirInstance F)
    (root context : B) (w : FullOpening) : DriverRun :=
  let seed := absorb context "PCS_BATCH_SHIFT" [instanceFrame inst,root,Aggregation.encodePolyExt4 inst.batchClaims,
    Aggregation.encodePolyExt4 inst.initKernel,Aggregation.encodePolyExt4 w.shifts]
  let weights := cascadeWeights h seed inst.batchClaims.length
  let s : DriverState := ⟨inst.initDomainPts,(ringChecks F).oracleAt inst.initDomainPts inst.batchOracles weights,
    inst.batchOracles,inst.initKernel,(ringChecks F).cascade inst.batchClaims w.shifts weights,
    inst.initDegBound+1,hemNextMinAgree inst.initDomainPts.length inst.initMinAgree,root,seed,[]⟩
  let r := driveStages h pin w.finalCoeffs s inst.stages w.stages
  let good := decide (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length) &&
    decide (w.shifts.length = inst.batchClaims.length) &&
    decide (weights.length = inst.batchClaims.length) &&
    (ringChecks F).witness s.domain s.agree s.degree s.oracleAt s.kernel s.claim w.cascadePolynomial
  ⟨good && r.accepted,.cascade w.shifts weights [w.cascadePolynomial] :: r.transcript,r.batches⟩

def execWhirFullVerifier (h : WhirHash) (inst : HemWhirInstance F)
    (root context : B) (w : FullOpening) := (runFullOpening h true inst root context w).accepted

theorem execWhirFullVerifier_sound_for_verifyHemAffineWhir (h : WhirHash) (inst : HemWhirInstance F)
    (root context : B) (w : FullOpening) (ok : execWhirFullVerifier h inst root context w = true) :
    let r := runFullOpening h true inst root context w
    verifyHemAffineWhir inst r.transcript = true ∧
      ∀ b ∈ r.batches, canopyBatch h b.1 b.2.2.1 b.2.2.2 = true ∧
        queriedButterflies b.1 b.2.2.2 = true := by
  have ⟨good,rest⟩ := Bool.and_eq_true_iff.mp ok
  have ⟨hs,hb⟩ := driveStages_sound h _ _ _ _ rest
  refine ⟨?_,hb⟩
  unfold verifyHemAffineWhir
  dsimp only [runFullOpening]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  simp only [Bool.and_eq_true] at good ⊢
  exact ⟨good.1,good.2,hs⟩

/-- Event domination with the same oracle, adversarial state and decoded proof
    on both sides, including adversarial superpositions of proof addresses. -/
theorem execWhirFullVerifier_qrom_mass_le_spec {n width anc q : Nat}
    (A : QuantumAdv n width anc q) (fs : (Fin n → BitVec width) → WhirHash)
    (inst : HemWhirInstance F) (root context : B) (proof : Fin n → FullOpening) :
    uniformOracleSum width n (fun H => QVec.queryMassOn
      (fun i => execWhirFullVerifier (fs H) inst root context (proof i)) (runQuantumAdv A H)) ≤
    uniformOracleSum width n (fun H => QVec.queryMassOn
      (fun i => verifyHemAffineWhir inst (runFullOpening (fs H) true inst root context (proof i)).transcript)
      (runQuantumAdv A H)) := by
  apply uniformOracleSum_le
  intro H
  rw [QVec.queryMassOn_def,QVec.queryMassOn_def]
  apply qsum_le_qsum
  intro i
  cases he : execWhirFullVerifier (fs H) inst root context (proof i) with
  | false => exact Nat.zero_le _
  | true => rw [(execWhirFullVerifier_sound_for_verifyHemAffineWhir _ _ _ _ _ he).1]; exact Nat.le_refl _

/-- Zero coherent false-accept mass for the singleton zero-codeword/nonzero-claim
    family, with arbitrary stage count, quantum query count and oracle implementation. -/
theorem execWhirFullVerifier_qrom_soundness {n width anc q : Nat}
    (A : QuantumAdv n width anc q) (fs : (Fin n → BitVec width) → WhirHash)
    (dom : List F) (degree agree : Nat) (stages : List (HemWhirStageSpec F))
    (nd : dom.Nodup) (enough : degree+2 ≤ agree) (root context : B) (proof : Fin n → FullOpening) :
    let inst := hemZeroOracleClaimInstance dom degree agree stages
    ¬ HemStatementValid inst ∧ uniformOracleSum width n (fun H => QVec.queryMassOn
      (fun i => execWhirFullVerifier (fs H) inst root context (proof i)) (runQuantumAdv A H)) = 0 := by
  intro inst
  refine ⟨hemZeroOracleClaimInstance_invalid _ _ _ _ nd (by omega), ?_⟩
  have never (h : WhirHash) (w : FullOpening) : execWhirFullVerifier h inst root context w = false := by
    apply Bool.eq_false_iff.mpr
    intro ok
    have hv := (execWhirFullVerifier_sound_for_verifyHemAffineWhir _ _ _ _ _ ok).1
    have hs := (verifyHemAffineWhir_incremented_cascade_witness _ _ _ _ _ hv).2.1
    change w.shifts.length = 1 at hs
    obtain ⟨shift,he⟩ := List.length_eq_one_iff.mp hs
    generalize ht : (runFullOpening h true inst root context w).transcript = tr at hv
    have trForm : ∃ rest, tr = .cascade [shift] [(I,Z)] [w.cascadePolynomial] :: rest := by
      rw [← ht]
      simp only [runFullOpening,he,inst,hemZeroOracleClaimInstance,List.length_cons,
        List.length_nil,cascadeWeights]
      exact ⟨_,rfl⟩
    obtain ⟨rest,rfl⟩ := trForm
    have hz := verifyHemZeroOracle_implies_linear_collision dom degree agree stages shift I Z _ rest nd enough hv
    exact LawfulField.one_ne_zero (by simpa only [LawfulCommRing.zero_mul, LawfulCommRing.add_zero] using hz)
  rw [uniformOracleSum_congr width n _ (fun _ => 0) (fun H => by
    rw [QVec.queryMassOn_def]
    simp only [never,Bool.false_eq_true,↓reduceIte,qsum_const,Nat.mul_zero]),
    uniformOracleSum_const,Nat.mul_zero]

private def fixtureHash : WhirHash := ⟨fun _ => [],fun _ _ => Z⟩
private def fixtureStage : HemWhirStageSpec F := ⟨[I],0,1,1,[0]⟩
private def fixtureWire : AffineStageWire := ⟨Z,Z,Z,Z,Z,[],Z,Z,[Z],[],0,[[]],[]⟩

private theorem fixture_indices (s : DriverState) (tail : Option (List F)) :
    (prepareStage fixtureHash s fixtureStage fixtureWire tail).indices = [0] :=
  Aggregation.scanFill_sample_singleton _ (by rfl)

private theorem fixture_pins (s : DriverState) (tail : Option (List F)) :
    (prepareStage fixtureHash s fixtureStage fixtureWire tail).next.pins = [0] :=
  fixture_indices s tail

private theorem fixture_canopy (s : DriverState) (tail : Option (List F)) (root : s.commitment = []) :
    canopyBatch fixtureHash s fixtureWire (prepareStage fixtureHash s fixtureStage fixtureWire tail) =
      true := by
  unfold canopyBatch
  rw [fixture_indices, root]
  change verifyCanopyMultiproof (fun _ _ _ => ([] : B)) (fun _ _ => []) 0 [] [(0, [])] [] = true
  rw [verifyCanopyMultiproof_depth0_leaf0]
  rfl

/-- Change only the tail polynomial after a consistent zero fold. Its linear
    claim is still zero against a zero kernel, but its value at the pinned point is one. -/
theorem tooth_without_terminal_pin :
    ∃ (h : WhirHash) (inst : HemWhirInstance F) (root context : B) (w : FullOpening),
      w.stages.length = 1 ∧ (runFullOpening h false inst root context w).accepted = true ∧
      execWhirFullVerifier h inst root context w = false ∧
      execWhirFullVerifier h inst root context {w with finalCoeffs := []} = true := by
  let inst : HemWhirInstance F := ⟨[fun _ => Z],[Z],[I,CommRingOps.neg I],0,1,[],[fixtureStage]⟩
  refine ⟨fixtureHash,inst,[],[],⟨[Z],[],[fixtureWire],[I]⟩,?_⟩
  simp (disch := rfl) only [inst, execWhirFullVerifier, runFullOpening, driveStages, hostChecks,
    fixture_canopy, queriedButterflies, checkTail, fixture_indices, fixture_pins,
    hemAffineDuetFold, Aggregation.foldDuetExt4.public_eq_1]
  decide +kernel

/-- A deterministic zero squeeze discards the first coordinate of a two-word
    affine cascade. This separates acceptance transfer from a claim of soundness
    for arbitrary oracle instantiations. The example includes a Merkle opening
    and one checked fold before the terminal round. -/
theorem zero_squeeze_masks_false_batch_coordinate :
    ∃ (h : WhirHash) (inst : HemWhirInstance F) (w : FullOpening),
      ¬ HemStatementValid inst ∧ execWhirFullVerifier h inst [] [] w = true := by
  let inst : HemWhirInstance F := ⟨[fun _ => Z,fun _ => Z],[I,Z],[I,CommRingOps.neg I],0,1,[],[fixtureStage]⟩
  refine ⟨fixtureHash,inst,⟨[Z,Z],[],[fixtureWire],[]⟩,?_,?_⟩
  · intro valid
    have batch := ((HemStatementValid_iff _).mp valid).2
    obtain ⟨P,hP⟩ := ((HemBatchValid_cons_cons_iff _ _ _ _ _ _ _ _).mp batch).1
    have dot := of_decide_eq_true (Bool.and_eq_true_iff.mp hP).2
    change ringDot P ([] : List F) = I at dot
    rw [ringDot_nil_right] at dot
    exact LawfulField.one_ne_zero dot.symm
  · simp (disch := rfl) only [inst, execWhirFullVerifier, runFullOpening, driveStages, hostChecks,
    fixture_canopy, queriedButterflies, checkTail, fixture_indices, fixture_pins,
    hemAffineDuetFold, Aggregation.foldDuetExt4.public_eq_1]
    decide +kernel

#tooth_pair execWhirFullVerifier_sound_for_verifyHemAffineWhir vs tooth_without_terminal_pin
end Qsag.Exec
