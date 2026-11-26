module
public import Qsag.Protocol.Aggregation.MultiDepthRecursiveQromExtractor
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.ConcreteIvcDepth2Cert
import Qsag.Protocol.Signing.ExecEufCmaClosedGame
import Qsag.Tactic.AssuranceKit

/-!
The recursive R1CS argument has three different public sumchecks. Its row gate
contains a selected seventh power, multiplied by an equality weight. The column
check and the matrix accumulator both multiply two multilinear tables. At 23
variables the three checks take 23, 23 and 49 rounds respectively.

An internal proof exposes witness evaluations. Zero knowledge requires a ZK
outer layer. In the prefix-encoded quantum oracle game the public rounds cost
less than 2^-160 across trees of depth at most 20 at Q ≤ 2^64. The combined
whole-tree budget clears 128 bits at depths through 7 at Q ≤ 2^64, or through
20 at Q ≤ 2^57.

A target shard and a quorum overclaim each select a single authenticated path.
At depth at most 64 its combined public-round, WHIR and collision budget is
below 2^-130 at Q ≤ 2^64 and its public-round terms sum to less than 2^-160.
The finite-game reduction requires bounds on failure at the adaptively selected nodes. The quorum reduction yields a
verifying signature for an active, nonparticipating custody key. The recorded
extractor needs a framed node-witness query. Rust commits the assignment table
with WHIR, so applying the reduction to Rust requires a witness-recovery bridge.
For an alternative 23-variable schedule, depth16Schedule_tree_lt_128 bounds the sum over
all nodes through depth 16. recoverIvcAssignment checks a decoded assignment against the
public frame and matrix rows. Relating those wires to the child arguments still requires
the circuit-specific layout. Depth counts proof nodes visited. Computing an arbitrary capacity sum can also
require enumerating the shard interval. Rust's exclusive upper endpoint is u64.
-/

public section
namespace Qsag.RecursiveIvcPublicRowQrom
open Qsag.ClosedFs Qsag.MultiDepthQrom Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ZkHemV2Packed Qsag.SuccinctWhirAgg
attribute [-instance] Fin.instLinearOrderPackage
set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 512

local infixl:65 " +ₑ " => CommRingOps.add
local infixl:65 " -ₑ " => CommRingOps.sub
local infixl:70 " *ₑ " => CommRingOps.mul
open CommRingOps (zero one)

private theorem eval_eq (poly : List E) (r : E) :
    IvcAlgebra.evalCoeffs poly r = RoundPoly.evalCoeffs poly r := by
  induction poly with
  | nil => rfl
  | cons c cs ih =>
    change c +ₑ r *ₑ IvcAlgebra.evalCoeffs cs r = c +ₑ r *ₑ RoundPoly.evalCoeffs cs r
    rw [ih]

/-- The evaluator and endpoint check used by the recursive verifier. The pool
may be any duplicate-free set, and the coefficients may depend on public data. -/
theorem public_round_bad_challenges (degree : Nat) (honest sent pool : List E)
    (claim : E) (distinct : pool.Nodup) (hg : honest.length ≤ degree + 1)
    (hs : sent.length ≤ degree + 1)
    (check : IvcAlgebra.evalCoeffs sent zero +ₑ IvcAlgebra.evalCoeffs sent one = claim)
    (bad : claim ≠ IvcAlgebra.evalCoeffs honest zero +ₑ IvcAlgebra.evalCoeffs honest one) :
    (pool.filter fun r => decide (IvcAlgebra.evalCoeffs sent r = IvcAlgebra.evalCoeffs honest r)).length
      ≤ degree := by
  simp only [eval_eq] at check bad ⊢
  exact hemSumcheck_polynomial_collision_count degree honest sent pool claim distinct hg hs check bad

/-- A successful singleton round advances the concrete oracle state using the
serialized coefficients before drawing the challenge from that state. -/
theorem sumcheck_absorbs_before_challenge (H : IvcAlgebra.RO)
    (tag squeeze : Spec.Bytes) (poly : List E) (claim r : E) (record : Bool)
    (start absorbed finish : IvcAlgebra.FsTrace)
    (check : QuinticGoldilocks.add (IvcAlgebra.evalCoeffs poly .zero)
      (IvcAlgebra.evalCoeffs poly .one) = claim)
    (ha : IvcAlgebra.absorb H tag (NodeWire.words
      (poly.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])) record start = some ((), absorbed))
    (hr : IvcAlgebra.challenge H squeeze record absorbed = some (r, finish)) :
    IvcAlgebra.sumcheck H tag squeeze 1 poly.length claim [poly] record start =
      some ((IvcAlgebra.evalCoeffs poly r, [r]), finish) := by
  simp [IvcAlgebra.sumcheck, check, Bind.bind, StateT.bind, Pure.pure, StateT.pure, ha, hr]

/-- The ten-coefficient row wire admits X(X-2)(X-3), padded with zeros.
It has a false endpoint sum against zero and agrees at three distinct points. -/
theorem tooth_row_width_admits_three_agreements :
    ∃ (sent pool : List E), sent.length = 10 ∧ pool.Nodup ∧
      IvcAlgebra.evalCoeffs sent zero +ₑ IvcAlgebra.evalCoeffs sent one ≠ zero ∧
      (pool.filter fun r => decide (IvcAlgebra.evalCoeffs sent r = zero)).length > 2 := by
  let base (n : Nat) : E := .ofBase (Goldilocks.ofNat n)
  refine ⟨[zero, base 6, zero -ₑ base 5, one, zero, zero, zero, zero, zero, zero],
    [zero, base 2, base 3], ?_⟩
  decide +revert +kernel

/-- The full coefficient vector absorbed at a quadratic round. Its middle
coefficient is fixed by the incoming claim and the two free coefficients. -/
@[expose] def quadratic {F : Type} [CommRingOps F] (claim c0 c2 : F) : List F :=
  [c0, claim -ₑ (c0 +ₑ c0) -ₑ c2, c2]

private theorem quadratic_sum {F : Type} [LawfulCommRing F] (claim c0 c2 : F) :
    RoundPoly.evalCoeffs (quadratic claim c0 c2) zero +ₑ
      RoundPoly.evalCoeffs (quadratic claim c0 c2) one = claim := by
  simp only [quadratic, RoundPoly.evalCoeffs]
  constructive_ring

theorem quadratic_bad_challenges (honest pool : List E) (claim c0 c2 : E)
    (distinct : pool.Nodup) (degree : honest.length ≤ 3)
    (bad : claim ≠ IvcAlgebra.evalCoeffs honest zero +ₑ IvcAlgebra.evalCoeffs honest one) :
    (pool.filter fun r => decide (IvcAlgebra.evalCoeffs (quadratic claim c0 c2) r =
      IvcAlgebra.evalCoeffs honest r)).length ≤ 2 := by
  apply public_round_bad_challenges 2 honest (quadratic claim c0 c2) pool claim distinct degree (Nat.le_refl 3) _ bad
  simpa only [eval_eq] using quadratic_sum claim c0 c2

private theorem interpolate {F : Type} [LawfulField F] (r claim target : F)
    (hr : r *ₑ (r -ₑ one) ≠ zero) :
    ∃ c0 c2 : F, RoundPoly.evalCoeffs (quadratic claim c0 c2) r = target := by
  let delta := target -ₑ r *ₑ claim
  let denom := r *ₑ (r -ₑ one)
  let c2 := delta *ₑ LawfulField.inv denom
  refine ⟨zero, c2, ?_⟩
  calc
    RoundPoly.evalCoeffs (quadratic claim zero c2) r =
        r *ₑ claim +ₑ c2 *ₑ denom := by
          simp only [quadratic, RoundPoly.evalCoeffs, denom]
          constructive_ring
    _ = r *ₑ claim +ₑ delta *ₑ (denom *ₑ LawfulField.inv denom) := by
          dsimp only [c2]
          constructive_ring
    _ = target := by
          rw [LawfulField.mul_inv_cancel hr, LawfulCommRing.mul_one]
          dsimp only [delta]
          constructive_ring

/-- Quantifier reversal for the challenge-first mutant. For every eligible
challenge, a message passes both the verifier's endpoint and evaluation checks. -/
theorem tooth_unabsorbed_public_row_sumcheck_forges_claim (r falseClaim honestEval : E)
    (hr : r *ₑ (r -ₑ one) ≠ zero) :
    ∃ c0 c2 : E,
      IvcAlgebra.evalCoeffs (quadratic falseClaim c0 c2) zero +ₑ
        IvcAlgebra.evalCoeffs (quadratic falseClaim c0 c2) one = falseClaim ∧
      IvcAlgebra.evalCoeffs (quadratic falseClaim c0 c2) r = honestEval := by
  obtain ⟨c0, c2, h⟩ := interpolate r falseClaim honestEval hr
  exact ⟨c0, c2, by simpa only [eval_eq] using quadratic_sum falseClaim c0 c2,
    (eval_eq _ _).trans h⟩

/-- Charge all three sumchecks at every node, including the matrix fold at
leaves where it is unnecessary. The denominator is the uniform field size. -/
@[expose] def sumcheckBudget (Q : Nat) : RatBound :=
  dfmRoundScale Q ⟨23 * 9 + 23 * 2 + (2 * 23 + 3) * 2,
    quinticGoldilocksCard, quinticGoldilocksCard_pos⟩

/-- All quintic elements, with no assumption about a sampled subset. -/
@[expose] def fieldPool : List E :=
  (List.finRange quinticGoldilocksCard).map fun i => decodeQuinticNat i.val

theorem fieldPool_spec :
    fieldPool.Nodup ∧ fieldPool.length = quinticGoldilocksCard ∧
      (∀ z : E, z ∈ fieldPool) ∧ 2^319 < quinticGoldilocksCard := by
  refine ⟨?_, by simp only [fieldPool, List.length_map, List.length_finRange], ?_, by decide +kernel⟩
  · apply List.pairwise_map.mpr
    refine (List.nodup_finRange _).imp (fun {i j} hne he => hne (Fin.ext ?_))
    exact (encodeQuinticNat_decodeQuinticNat i.isLt).symm.trans
      ((congrArg encodeQuinticNat he).trans (encodeQuinticNat_decodeQuinticNat j.isLt))
  · intro z
    exact List.mem_map.mpr ⟨⟨encodeQuinticNat z, encodeQuinticNat_lt z⟩,
      List.mem_finRange _, decodeQuinticNat_encodeQuinticNat z⟩

/-- Canonical low-limb-first challenge word. The unused 320-bit encodings
cannot match a field element in the target list. -/
@[expose] def challengeWord (z : E) : BitVec 320 :=
  BitVec.ofNat 320 (z.c0.val + 2^64 * (z.c1.val + 2^64 *
    (z.c2.val + 2^64 * (z.c3.val + 2^64 * z.c4.val))))

abbrev PublicMessage := Spec.Bytes × List E
abbrev History := List (PublicMessage × Nat)

/-- The public bytes in the message may contain witness evaluations. Both
those bytes and the polynomial belong to the oracle address for the challenge. -/
structure RoundClaims where
  incoming : History → E
  honest : History → PublicMessage → List E

@[expose] def roundDegree (index : Nat) : Nat := if index < 23 then 9 else 2

@[expose] def agreementWords (claims : RoundClaims) (pre : History) (m : PublicMessage) :
    List (BitVec 320) :=
  let g := claims.honest pre m
  let p := m.2
  let sumAtEnds (poly : List E) :=
    IvcAlgebra.evalCoeffs poly zero +ₑ IvcAlgebra.evalCoeffs poly one
  if p.length = roundDegree pre.length + 1 ∧ sumAtEnds p = claims.incoming pre ∧
      claims.incoming pre ≠ sumAtEnds g then
    (fieldPool.filter fun r => decide
      (IvcAlgebra.evalCoeffs p r = IvcAlgebra.evalCoeffs g r)).map challengeWord
  else []

/-- Every canonical challenge that repairs a false checked claim is counted
by the quantum event, for every prefix and every set of public message bytes. -/
theorem checked_agreement_is_hit (claims : RoundClaims) (pre : History) (m : PublicMessage) (r : E)
    (width : m.2.length = roundDegree pre.length + 1)
    (check : IvcAlgebra.evalCoeffs m.2 zero +ₑ IvcAlgebra.evalCoeffs m.2 one = claims.incoming pre)
    (bad : claims.incoming pre ≠ IvcAlgebra.evalCoeffs (claims.honest pre m) zero +ₑ
      IvcAlgebra.evalCoeffs (claims.honest pre m) one)
    (hit : IvcAlgebra.evalCoeffs m.2 r = IvcAlgebra.evalCoeffs (claims.honest pre m) r) :
    listHasElem (challengeWord r) (agreementWords claims pre m) = true := by
  apply (listHasElem_eq_true_iff _ _).mpr
  dsimp only [agreementWords]
  split
  · exact List.mem_map_of_mem (f := challengeWord)
      (List.mem_filter.mpr ⟨fieldPool_spec.2.2.1 r, decide_eq_true hit⟩)
  · rename_i h
    exact False.elim (h ⟨width, check, bad⟩)

private theorem agreementWords_length (claims : RoundClaims) (pre : History) (m : PublicMessage)
    (degree : (claims.honest pre m).length ≤ roundDegree pre.length + 1) :
    (agreementWords claims pre m).length ≤ roundDegree pre.length := by
  dsimp only [agreementWords]
  split
  · rename_i ok
    rw [List.length_map]
    exact public_round_bad_challenges _ _ _ _ _ fieldPool_spec.1 degree
      (Nat.le_of_eq ok.1) ok.2.1 ok.2.2
  · exact Nat.zero_le _

/-- Scan for a false incoming claim that agrees with the honest polynomial
after a challenge. Previous challenges and all public bytes are available at each round. -/
@[expose] def hitInTranscript (claims : RoundClaims) (pre : History) : History → Bool
  | [] => false
  | (m, ch) :: rest =>
    listHasElem (BitVec.ofNat 320 ch) (agreementWords claims pre m) ||
      hitInTranscript claims (pre ++ [(m,ch)]) rest

private theorem hit_append (claims : RoundClaims) (pre xs : History) (m : PublicMessage) (ch : Nat) :
    hitInTranscript claims pre (xs ++ [(m,ch)]) = (hitInTranscript claims pre xs ||
      listHasElem (BitVec.ofNat 320 ch) (agreementWords claims (pre ++ xs) m)) := by
  induction xs generalizing pre with
  | nil => simp [hitInTranscript]
  | cons head tail ih =>
    rcases head with ⟨msg,word⟩
    simp [hitInTranscript, ih, List.append_assoc, Bool.or_assoc]

/-- Measure an adversary's full prefix-encoded public sumcheck transcript
under a uniform 320-bit random oracle. The event concerns the 23 row,
23 column and 49 matrix rounds. It makes no WHIR or extraction assumption. -/
@[expose] def publicFsHit {cardX : Nat} (claims : RoundClaims) (codec : FsCodec PublicMessage 95 cardX)
    (H : Fin cardX → BitVec 320) (o : Fin cardX) : Bool :=
  (codec.dec o).length == 95 && hitInTranscript claims [] (fsTranscript codec H (codec.dec o))

@[expose] def publicFsMass {cardX anc Q : Nat} (A : QuantumAdv cardX 320 anc Q)
    (codec : FsCodec PublicMessage 95 cardX) (claims : RoundClaims) : RatBound :=
  ⟨uniformOracleSum 320 cardX (fun H =>
          QVec.queryMassOn (publicFsHit claims codec H) (runQuantumAdv A H)),
        (2^320)^cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 320))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩

theorem public_sumchecks_qrom {cardX anc Q : Nat} (A : QuantumAdv cardX 320 anc Q)
    (codec : FsCodec PublicMessage 95 cardX) (claims : RoundClaims)
    (hg : ∀ pre m, pre.length < 95 →
      (claims.honest pre m).length ≤ roundDegree pre.length + 1) :
    RatBound.le
      (publicFsMass A codec claims)
      (sumcheckBudget Q) := by
  let bad (i : Fin 95) := roundDegree i.val
  refine RatBound.le_trans (fs_qrom_bool_rbr_soundness A codec (hitInTranscript claims [])
    bad rfl ?_ (publicFsHit claims codec) ?_) ?_
  · intro i pre m hlen dead
    simp only [hit_append, dead, Bool.false_or, List.nil_append]
    have word (j : Fin (2^320)) : BitVec.ofNat 320 j.val = BitVec.ofFin j := by
      apply BitVec.eq_of_toNat_eq
      exact Nat.mod_eq_of_lt j.isLt
    simp only [word]
    have n := agreementWords_length claims pre m (hg pre m (by rw [hlen]; exact i.isLt))
    rw [hlen] at n
    exact Nat.le_trans (qsum_ofFin_listHasElem_le_length _ _) n
  · intro H o h
    obtain ⟨len, live⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨eq_of_beq len, live⟩
  · have count : qsum 95 bad = 23 * 9 + 23 * 2 + (2 * 23 + 3) * 2 := by
      decide +revert +kernel
    change (2*Q+1)^2 * qsum 95 bad * quinticGoldilocksCard ≤
      (2*Q+1)^2 * _ * 2^320
    rw [count]
    exact Nat.mul_le_mul_left _ (by decide +kernel)

/-- Arithmetic for the named round and digest terms. A reduction from
accepted proofs with failed extraction to these events is a further obligation. -/
@[expose] def treeBudget (d Q : Nat) : RatBound :=
  RatBound.add (RatBound.scale (treeNodeCount d)
    (RatBound.add (sumcheckBudget Q) (scheduleQromError (zkHemV2ProdSched 23) Q)))
    (merkleProfileQromBound .poseidon2Gl24 Q)

private theorem scale_le {n m : Nat} {a b : RatBound}
    (hn : n ≤ m) (hab : a.le b) : (RatBound.scale n a).le (RatBound.scale m b) := by
  change n * a.num * b.den ≤ m * b.num * a.den
  rw [Nat.mul_assoc, Nat.mul_assoc]
  exact Nat.mul_le_mul hn hab

/-- Alternative depth-16 parameter set. Stage zero uses DKT multiplicity 54.
    All four shift sample counts account for the full tree union. -/
def depth16Schedule : WhirVerifierSchedule :=
  let stages := [
    ⟨6, 19, 2, 5, 284, 131073, 264574, 1, 2048, 2048, 23,
      905283979089⟩,
    ⟨4, 17, 4, 2, 141, 8194, 33029, 1, 512, 1024, 3, 12292⟩,
    ⟨3, 16, 6, 2, 94, 1026, 8265, 1, 1024, 4093, 3, 36840⟩,
    ⟨3, 15, 8, 2, 71, 130, 2081, 1, 2048, 16258, 3, 146325⟩]
  ⟨23, quinticGoldilocksCard, quinticGoldilocksCard_pos, stages⟩

theorem depth16Schedule_geometry :
    depth16Schedule.johnsonOk = true ∧ dkt26Covers 4 17 54 264574 = true ∧
    dkt26Covers 4 17 54 264573 = false ∧ dkt26MaskLineTotalBad 4 17 54 264574 = 905283979089 := by
  simp only [depth16Schedule, dkt26Covers.public_eqs, dkt26MaskLineTotalBad.public_eqs,
    dkt26Bcf.public_eqs, JohnsonBound.johnsonBound_eq]
  decide +kernel

private def depth16Rounds := packedStagesRoundBounds quinticGoldilocksCard quinticGoldilocksCard_pos
  depth16Schedule.stages

def depth16WhirError (Q : Nat) : RatBound :=
  RatBound.sumList (depth16Rounds.map (dfmRoundScale Q))

private theorem depth16RoundCap : depth16Rounds.all (fun b => decide (b.num * 2^280 ≤ b.den)) = true := by
  simp only [depth16Rounds, depth16Schedule, packedStagesRoundBounds, packedStageRoundBounds,
    singleOodSeedBound, WhirStage.foldBound_eq, WhirStage.shiftBound_eq, binom2_eq]
  decide +kernel

private theorem depth16WhirCap {Q : Nat} (hq : Q ≤ 2^64) :
    (depth16WhirError Q).le (RatBound.scale 24 (dfmRoundScale (2^64) (RatBound.invPow2 280))) := by
  have bounded := RatBound.sumList_le_length_mul
    (bound := dfmRoundScale (2^64) (RatBound.invPow2 280)) (depth16Rounds.map (dfmRoundScale Q))
    (fun _ hm => by
      obtain ⟨b,mem,rfl⟩ := List.mem_map.mp hm
      apply scale_le (Nat.pow_le_pow_left (by omega) 2)
      change b.num * 2^280 ≤ 1 * b.den
      rw [Nat.one_mul]
      exact of_decide_eq_true (List.all_eq_true.mp depth16RoundCap b mem))
  simpa only [depth16WhirError, List.length_map, show depth16Rounds.length = 24 by
    rw [depth16Rounds, packedStagesRoundBounds_length]; decide +kernel] using bounded

/-- Arithmetic budget for the alternative schedule, including all public sumchecks,
    all WHIR rounds of every node and the shared commitment collision term. -/
theorem depth16Schedule_tree_lt_128 {d Q : Nat} (hd : d ≤ 16) (hq : Q ≤ 2^64) :
    RatBound.lt (RatBound.add (RatBound.scale (treeNodeCount d)
      (RatBound.add (sumcheckBudget Q) (depth16WhirError Q)))
      (merkleProfileQromBound .poseidon2Gl24 Q)) (RatBound.invPow2 128) := by
  apply ratBound_lt_of_le_of_lt (b := RatBound.add (RatBound.scale (treeNodeCount 16)
    (RatBound.add (sumcheckBudget (2^64)) (RatBound.scale 24 (dfmRoundScale (2^64) (RatBound.invPow2 280)))))
    (merkleProfileQromBound .poseidon2Gl24 (2^64)))
  · apply RatBound.add_le_add _ (merkleProfileQromBound_mono _ hq)
    apply scale_le (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.succ_le_succ hd)) 1)
    apply RatBound.add_le_add _ (depth16WhirCap hq)
    apply scale_le _ (RatBound.le_refl _)
    exact Nat.pow_le_pow_left (by omega) 2
  · decide +kernel

#verify_constructive depth16Schedule_geometry depth16Schedule_tree_lt_128

/-- The public sumcheck terms alone clear 160 bits even at the full tree and query limits. -/
theorem tree_sumcheck_budget_lt_160 {d Q : Nat} (hd : d ≤ 20) (hq : Q ≤ 2^64) :
    RatBound.lt (RatBound.scale (treeNodeCount d) (sumcheckBudget Q)) (RatBound.invPow2 160) := by
  apply ratBound_lt_of_le_of_lt (b := RatBound.scale (treeNodeCount 20) (sumcheckBudget (2^64)))
  · apply scale_le (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.succ_le_succ hd)) 1)
    apply scale_le _ (RatBound.le_refl _)
    exact Nat.pow_le_pow_left (by omega) 2
  · decide +kernel

/-- Sum of the measured quantum public-round failure masses for all nodes.
Each prefix experiment can have different public data and adversary. -/
theorem tree_public_sumchecks_qrom {d cardX anc Q : Nat} (hd : d ≤ 20) (hq : Q ≤ 2^64)
    (A : Fin (treeNodeCount d) → QuantumAdv cardX 320 anc Q)
    (codec : Fin (treeNodeCount d) → FsCodec PublicMessage 95 cardX)
    (claims : Fin (treeNodeCount d) → RoundClaims)
    (hg : ∀ i pre m, pre.length < 95 →
      ((claims i).honest pre m).length ≤ roundDegree pre.length + 1) :
    RatBound.lt (RatBound.sumList ((List.finRange (treeNodeCount d)).map
      fun i => publicFsMass (A i) (codec i) (claims i))) (RatBound.invPow2 160) := by
  apply ratBound_lt_of_le_of_lt _ (tree_sumcheck_budget_lt_160 hd hq)
  have bound := RatBound.sumList_le_length_mul (bound := sumcheckBudget Q)
    ((List.finRange (treeNodeCount d)).map fun i => publicFsMass (A i) (codec i) (claims i))
    (fun mass hm => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hm
      exact public_sumchecks_qrom (A i) (codec i) (claims i) (hg i))
  simpa only [List.length_map, List.length_finRange] using bound

/-- The first WHIR fold already exhausts the requested tree budget on its own. -/
theorem first_fold_tree_budget_gt_2_neg_120 :
    match zkHemV2ProdStages 23 with
    | [] => False
    | first :: _ => RatBound.lt (RatBound.invPow2 120)
        (RatBound.scale (treeNodeCount 20) (dfmRoundScale (2^64)
          (first.foldBound quinticGoldilocksCard quinticGoldilocksCard_pos))) := by
  simp only [zkHemV2ProdStages.public_eq_8, WhirStage.foldBound_eq]
  decide +kernel

private theorem budget_mono {d e Q R : Nat} (hd : d ≤ e) (hq : Q ≤ R) :
    (treeBudget d Q).le (treeBudget e R) := by
  apply RatBound.add_le_add _ (merkleProfileQromBound_mono _ hq)
  apply scale_le (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.succ_le_succ hd)) 1)
  apply RatBound.add_le_add _ (scheduleQromError_mono _ hq)
  apply scale_le _ (RatBound.le_refl _)
  exact Nat.pow_le_pow_left (by omega) 2

private theorem budget_endpoints :
    RatBound.lt (treeBudget 7 (2^64)) (RatBound.invPow2 128) ∧
    RatBound.lt (treeBudget 20 (2^57)) (RatBound.invPow2 128) ∧
    ¬ RatBound.lt (treeBudget 8 (2^64)) (RatBound.invPow2 128) ∧
    RatBound.lt (RatBound.invPow2 116) (treeBudget 20 (2^64)) ∧
    RatBound.lt (treeBudget 20 (2^64)) (RatBound.invPow2 115) := by
  simp only [treeBudget, scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq,
    zkHemV2ProdSched.public_eq_1, zkHemV2ProdStages.public_eq_8,
    stagesRoundBounds_cons, stagesRoundBounds_nil, WhirStage.roundBounds_eq,
    WhirStage.foldBound_eq, WhirStage.oodBound_eq, WhirStage.shiftBound_eq, binom2_eq]
  decide +kernel

theorem treeBudget_lt_128 {d Q : Nat}
    (limits : (d ≤ 7 ∧ Q ≤ 2^64) ∨ (d ≤ 20 ∧ Q ≤ 2^57)) :
    RatBound.lt (treeBudget d Q) (RatBound.invPow2 128) := by
  rcases limits with ⟨hd,hq⟩ | ⟨hd,hq⟩
  · exact ratBound_lt_of_le_of_lt (budget_mono hd hq) budget_endpoints.1
  · exact ratBound_lt_of_le_of_lt (budget_mono hd hq) budget_endpoints.2.1

theorem tooth_dkt26_tree_budget_exceeds_target :
    ¬ RatBound.lt (treeBudget 20 (2^64)) (RatBound.invPow2 128) :=
  fun h => (by decide +kernel : ¬ RatBound.lt (RatBound.invPow2 116) (RatBound.invPow2 128))
    (ratBound_lt_of_le_of_lt (Nat.le_of_lt budget_endpoints.2.2.2.1) h)

theorem depth20_budget_interval :
    RatBound.lt (RatBound.invPow2 116) (treeBudget 20 (2^64)) ∧
      RatBound.lt (treeBudget 20 (2^64)) (RatBound.invPow2 115) :=
  budget_endpoints.2.2.2

/-- Successful extraction outside collisions and the actual indexed node
failure event. The argument reads the same recorded transcript at every depth. -/
theorem extract_outside_node_failures {n : Nat} (env : IvcExtractionContext n)
    (dep : IsDeployedAggProfile env.profile) (H : Spec.Bytes → Spec.Bytes)
    (T : QromQueryTranscript) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof env.cfg.params)
    (accept : verifyConcreteIvcRoot env.profile env.cfg H d stmt pi = true)
    (hc : hasQueryCollision T = false)
    (good : ∀ i < treeNodeCount d, ∀ level s p,
      treeNodeAt env H T d stmt pi i = some (level,s,p) →
      concreteIvcStepBad env H T level s p = false) :
    ∃ shards : List (ExtractedLeafShard n),
      extractMultiDepthQrom env H d T stmt pi = some shards ∧ shards.length = 2 ^ d ∧
      shards.map ExtractedLeafShard.shardId = List.range' stmt.lo (2 ^ d) ∧
      (shards.map ExtractedLeafShard.quorumCount).sum = stmt.totalQuorums ∧
      ∀ s ∈ shards, ValidQuorumSignatures env.profile H stmt.policyRegistryRoot stmt.message s := by
  rcases extractMultiDepthQrom_inductive_sound env dep H T hc d stmt pi accept with
    found | ⟨i, _, _, _, hi, _, node, bad⟩
  · exact found
  · rw [good i hi _ _ _ node] at bad
    cases bad

def rangeCap (cap : Nat → Nat) (lo len : Nat) : Nat :=
  ((List.range' lo len).map cap).sum

theorem rangeCap_double (cap : Nat → Nat) (lo m : Nat) :
    rangeCap cap lo (2^(m+1)) = rangeCap cap lo (2^m) + rangeCap cap (lo+2^m) (2^m) := by
  simp only [rangeCap, Nat.pow_succ, Nat.mul_two, ← List.range'_append_1, List.map_append,
    List.sum_append]

/-- A target is an absolute shard ID. The excess case uses an external capacity function. -/
inductive SpineSearch where
  | target (id : Nat)
  | excess (cap : Nat → Nat)

def SpineSearch.applies : SpineSearch → Nat → IvcTreeStatement → Prop
  | .target id, d, s => s.lo ≤ id ∧ id < s.lo + 2^d
  | .excess cap, d, s => rangeCap cap s.lo (2^d) < s.totalQuorums

def SpineSearch.left (q : SpineSearch) (m : Nat) (l : IvcTreeStatement) : Bool :=
  match q with
  | .target id => decide (id < l.lo + 2^m)
  | .excess cap => decide (rangeCap cap l.lo (2^m) < l.totalQuorums)

def SpineSearch.found {n : Nat} : SpineSearch → ExtractedLeafShard n → Prop
  | .target id, sh => sh.shardId = id
  | .excess cap, sh => cap sh.shardId < sh.quorumCount

section Spine
variable {n : Nat} (env : IvcExtractionContext n) (H : IvcAlgebra.RO) (T : QromQueryTranscript)
abbrev ProofAt {n : Nat} (env : IvcExtractionContext n) := FixedShapeWhirProof env.cfg.params
abbrev Child {n : Nat} (env : IvcExtractionContext n) := IvcTreeStatement × ProofAt env
abbrev Located {n : Nat} (env : IvcExtractionContext n) := Nat × Child env

def leafChecks (s : IvcTreeStatement) (sh : ExtractedLeafShard n) : Bool :=
  decide (sh.shardId = s.lo ∧ s.hi = s.lo + 1 ∧ sh.quorumCount = s.totalQuorums ∧
    0 < sh.quorumCount ∧ sh.threshold ≤ Composed.weight sh.stmt.bitmap ∧
    sh.stmt.message = s.message ∧ registryMember H s.policyRegistryRoot sh = true ∧
    0 < sh.threshold ∧ sh.quorumCount = Composed.weight sh.stmt.bitmap) &&
  (List.finRange n).all (fun i =>
    !sh.stmt.bitmap.getLsbD i.val || ((sh.stmt.roster i).profile == env.profile)) &&
  stepOp256TableOk env.profile (succinctCommitteeSlots sh.stmt) sh.rows

@[expose] def checkedLeaf (s : IvcTreeStatement) (p : ProofAt env) : Option (ExtractedLeafShard n) :=
  if verifyConcreteIvcRoot env.profile env.cfg H 0 s p then
    match extractIvcStepFromTranscript n env.profile H T 0 s p with
    | some (.leaf sh) => if leafChecks env H s sh then some sh else none
    | _ => none
  else none

@[expose] def checkedChildren (m : Nat) (s : IvcTreeStatement) (p : ProofAt env) :
    Option (Child env × Child env) :=
  if verifyConcreteIvcRoot env.profile env.cfg H (m+1) s p then
    match extractIvcStepFromTranscript n env.profile H T (m+1) s p with
    | some (.parent l r pl pr fold) =>
      if parentStitchCheck env H m s l r pl pr p fold then some ((l,pl),(r,pr)) else none
    | _ => none
  else none

/-- Each recursive call opens exactly one child witness from the recorded transcript.
The parent stitch verifies both child arguments. -/
def walk (q : SpineSearch) : (d : Nat) → IvcTreeStatement → ProofAt env →
    List (Located env) × Option (ExtractedLeafShard n)
  | 0, s, p => ([(0,s,p)], checkedLeaf env H T s p)
  | m+1, s, p =>
    match checkedChildren env H T m s p with
    | none => ([(m+1,s,p)], none)
    | some (l,r) =>
      let child := if q.left m l.1 then l else r
      let tail := walk q m child.1 child.2
      ((m+1,s,p) :: tail.1, tail.2)

def extractLeafAlongSpine (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (offset : Nat) :=
  (walk env H T (.target (s.lo + offset)) d s p).2

def spineNodeAt (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (offset k : Nat) :=
  (walk env H T (.target (s.lo + offset)) d s p).1[k]?

def extractOverclaimedSpine (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (cap : Nat → Nat) :=
  (walk env H T (.excess cap) d s p).2

def overclaimedSpineNodeAt (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (cap : Nat → Nat) (k : Nat) :=
  (walk env H T (.excess cap) d s p).1[k]?

def spineStepBad : Nat → IvcTreeStatement → ProofAt env → Bool
  | 0, s, p => verifyConcreteIvcRoot env.profile env.cfg H 0 s p && !hasQueryCollision T &&
      (checkedLeaf env H T s p).isNone
  | m+1, s, p => verifyConcreteIvcRoot env.profile env.cfg H (m+1) s p && !hasQueryCollision T &&
      (checkedChildren env H T m s p).isNone

def LocatedBad (d : Nat) (atNode : Nat → Option (Located env)) : Prop :=
  ∃ k < d+1, ∃ level s p, atNode k = some (level,s,p) ∧ spineStepBad env H T level s p = true

private theorem leaf_spec {s : IvcTreeStatement} {p : ProofAt env} {sh : ExtractedLeafShard n}
    (dep : IsDeployedAggProfile env.profile) (ok : checkedLeaf env H T s p = some sh) :
    sh.shardId = s.lo ∧ sh.quorumCount = s.totalQuorums ∧
    sh.quorumCount = Composed.weight sh.stmt.bitmap ∧
    ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh := by
  unfold checkedLeaf at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  rename_i hc
  cases ok
  obtain ⟨pair,table⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hd,prof⟩ := Bool.and_eq_true_iff.mp pair
  obtain ⟨id,_,count,pos,threshold,msg,reg,_,weight⟩ := of_decide_eq_true hd
  exact ⟨id,count,weight,pos,threshold,msg,prof,table,
    stepOp256TableOk_bothProfiles_extract env.profile dep _ _ prof table,reg⟩

private theorem children_spec {m : Nat} {s : IvcTreeStatement} {p : ProofAt env} {l r : Child env}
    (ok : checkedChildren env H T m s p = some (l,r)) :
    checkChildHeaders m s l.1 r.1 = true ∧ verifyConcreteIvcRoot env.profile env.cfg H m l.1 l.2 = true ∧
      verifyConcreteIvcRoot env.profile env.cfg H m r.1 r.2 = true := by
  unfold checkedChildren at ok
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  split at ok <;> try contradiction
  rename_i hs
  cases ok
  obtain ⟨h1,_⟩ := Bool.and_eq_true_iff.mp hs
  obtain ⟨h2,right⟩ := Bool.and_eq_true_iff.mp h1
  obtain ⟨headers,left⟩ := Bool.and_eq_true_iff.mp h2
  exact ⟨headers,left,right⟩

private theorem selected_spec (q : SpineSearch) {m : Nat} {s : IvcTreeStatement} {p : ProofAt env}
    {l r : Child env} (ok : checkedChildren env H T m s p = some (l,r)) (app : q.applies (m+1) s) :
    let c := if q.left m l.1 then l else r
    q.applies m c.1 ∧ verifyConcreteIvcRoot env.profile env.cfg H m c.1 c.2 = true ∧
      s.lo ≤ c.1.lo ∧ c.1.lo + 2^m ≤ s.lo + 2^(m+1) ∧
      c.1.policyRegistryRoot = s.policyRegistryRoot ∧ c.1.message = s.message := by
  obtain ⟨headers,vl,vr⟩ := children_spec env H T ok
  obtain ⟨rl,rr,_,_,ml,mr,ll,lh,mid,_,count⟩ := of_decide_eq_true headers
  have rightLo : r.1.lo = s.lo + 2^m := mid.symm.trans lh
  have pow : 2^(m+1) = 2^m + 2^m := by rw [Nat.pow_succ, Nat.mul_two]
  have endL : l.1.lo + 2^m ≤ s.lo + 2^(m+1) := by
    rw [ll,pow]
    exact Nat.add_le_add_left (Nat.le_add_right _ _) _
  have endR : r.1.lo + 2^m ≤ s.lo + 2^(m+1) := by
    rw [rightLo,pow,Nat.add_assoc]
    exact Nat.le_refl _
  cases q with
  | target id =>
    change s.lo ≤ id ∧ id < s.lo + 2^(m+1) at app
    simp only [SpineSearch.left, decide_eq_true_eq, SpineSearch.applies]
    split
    · exact ⟨⟨by omega, by omega⟩,vl,by omega,endL,rl,ml⟩
    · exact ⟨⟨by omega, by omega⟩,vr,by omega,endR,rr,mr⟩
  | excess cap =>
    change rangeCap cap s.lo (2^(m+1)) < s.totalQuorums at app
    rw [rangeCap_double, ← ll, count] at app
    simp only [SpineSearch.left, decide_eq_true_eq, SpineSearch.applies]
    split
    · exact ⟨by assumption,vl,by omega,endL,rl,ml⟩
    · have he : r.1.lo = l.1.lo + 2^m := by omega
      exact ⟨by rw [he]; omega,vr,by omega,endR,rr,mr⟩

theorem walk_length_le (q : SpineSearch) (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) :
    (walk env H T q d s p).1.length ≤ d+1 := by
  induction d generalizing s p with
  | zero => exact Nat.le_refl 1
  | succ m ih =>
    rw [walk]
    split
    · simp
    · exact Nat.succ_le_succ (ih _ _)

private theorem walk_sound (dep : IsDeployedAggProfile env.profile) (hc : hasQueryCollision T = false)
    (q : SpineSearch) (d : Nat) (s : IvcTreeStatement) (p : ProofAt env)
    (accept : verifyConcreteIvcRoot env.profile env.cfg H d s p = true) (app : q.applies d s) :
    (∃ sh, (walk env H T q d s p).2 = some sh ∧ q.found sh ∧ s.lo ≤ sh.shardId ∧
      sh.shardId < s.lo + 2^d ∧ sh.quorumCount = Composed.weight sh.stmt.bitmap ∧
      ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh) ∨
    LocatedBad env H T d (fun k => (walk env H T q d s p).1[k]?) := by
  induction d generalizing s p with
  | zero =>
    cases h : checkedLeaf env H T s p with
    | none => exact .inr ⟨0, by decide, 0,s,p,rfl,by simp [spineStepBad,accept,hc,h]⟩
    | some sh =>
      obtain ⟨id,count,weight,valid⟩ := leaf_spec env H T dep h
      refine .inl ⟨sh,h,?_,by omega,by simp [id],weight,valid⟩
      cases q with
      | target target =>
        change s.lo ≤ target ∧ target < s.lo + 1 at app
        change sh.shardId = target
        omega
      | excess cap =>
        change rangeCap cap s.lo 1 < s.totalQuorums at app
        simpa [SpineSearch.found,rangeCap,id,count,List.range'_succ] using app
  | succ m ih =>
    cases h : checkedChildren env H T m s p with
    | none =>
      exact .inr ⟨0,by omega,m+1,s,p,by simp [walk,h],by simp [spineStepBad,accept,hc,h]⟩
    | some lr =>
      obtain ⟨l,r⟩ := lr
      obtain ⟨childApp,v,lo,hi,reg,msg⟩ := selected_spec env H T q h app
      rcases ih _ _ v childApp with ⟨sh,ex,found,a,b,w,valid⟩ | ⟨k,hk,lv,t,pi,atK,bad⟩
      · exact .inl ⟨sh,by simpa only [walk,h] using ex,found,by omega,by omega,w,
          by rwa [reg,msg] at valid⟩
      · exact .inr ⟨k+1,by omega,lv,t,pi,by simpa only [walk,h,List.getElem?_cons_succ] using atK,bad⟩

theorem extractLeafAlongSpine_sound (dep : IsDeployedAggProfile env.profile) (hc : hasQueryCollision T = false)
    (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (offset : Nat) (ho : offset < 2^d)
    (accept : verifyConcreteIvcRoot env.profile env.cfg H d s p = true) :
    (∃ sh, extractLeafAlongSpine env H T d s p offset = some sh ∧ sh.shardId = s.lo + offset ∧
      0 < sh.quorumCount ∧ ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh) ∨
    LocatedBad env H T d (spineNodeAt env H T d s p offset) := by
  rcases walk_sound env H T dep hc (.target (s.lo+offset)) d s p accept
    ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ho _⟩ with
    ⟨sh,ex,id,_,_,_,v⟩ | bad
  · exact .inl ⟨sh,ex,id,v.1,v⟩
  · exact .inr bad

theorem extractOverclaimedSpine_sound (dep : IsDeployedAggProfile env.profile) (hc : hasQueryCollision T = false)
    (d : Nat) (s : IvcTreeStatement) (p : ProofAt env) (cap : Nat → Nat)
    (over : rangeCap cap s.lo (2^d) < s.totalQuorums)
    (accept : verifyConcreteIvcRoot env.profile env.cfg H d s p = true) :
    (∃ sh, extractOverclaimedSpine env H T d s p cap = some sh ∧ s.lo ≤ sh.shardId ∧
      sh.shardId < s.lo + 2^d ∧ cap sh.shardId < sh.quorumCount ∧
      sh.quorumCount = Composed.weight sh.stmt.bitmap ∧
      ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh) ∨
    LocatedBad env H T d (overclaimedSpineNodeAt env H T d s p cap) := by
  rcases walk_sound env H T dep hc (.excess cap) d s p accept over with
    ⟨sh,ex,h,a,b,w,v⟩ | bad
  · exact .inl ⟨sh,ex,a,b,h,w,v⟩
  · exact .inr bad

end Spine

def honestShardParticipated {n : Nat} (custody : Nat → Fin n → Composed.Custody)
    (msg : Spec.Bytes) (id : Nat) : Nat :=
  ((List.finRange n).filter fun v => Composed.quorumParticipated (custody id v) msg).length

private theorem count_participating {n : Nat} (part : Fin n → Bool) :
    ((List.finRange n).filter part).length = qsum n (fun i => if part i then 1 else 0) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.finRange_succ, List.filter_cons, List.filter_map]
    simp only [qsum_succ]
    cases h : part 0 <;> simp [ih, h, Function.comp_def, Nat.add_comm] <;> rfl

/-- An authenticated excess leaf identifies an active key with a verifying signature
and a missing quorum approval, when its roster agrees with the custody registry. -/
theorem overclaimed_spine_euf_cma_forgery {n : Nat} (env : IvcExtractionContext n)
    (H : IvcAlgebra.RO) (T : QromQueryTranscript) (dep : IsDeployedAggProfile env.profile)
    (hc : hasQueryCollision T = false) (d : Nat) (s : IvcTreeStatement) (p : ProofAt env)
    (custody : Nat → Fin n → Composed.Custody)
    (over : rangeCap (honestShardParticipated custody s.message) s.lo (2^d) < s.totalQuorums)
    (accept : verifyConcreteIvcRoot env.profile env.cfg H d s p = true) :
    let cap := honestShardParticipated custody s.message
    LocatedBad env H T d (overclaimedSpineNodeAt env H T d s p cap) ∨
      ∃ sh, extractOverclaimedSpine env H T d s p cap = some sh ∧
        s.lo ≤ sh.shardId ∧ sh.shardId < s.lo + 2^d ∧ cap sh.shardId < sh.quorumCount ∧
        ValidQuorumSignatures env.profile H s.policyRegistryRoot s.message sh ∧
        ((∀ v, sh.stmt.roster v = (custody sh.shardId v).state.pk) →
          ∃ v, sh.stmt.bitmap.getLsbD v.val = true ∧
            Composed.QuorumForgery (profileGeom env.profile) (custody sh.shardId v) s.message) := by
  intro cap
  rcases extractOverclaimedSpine_sound env H T dep hc d s p cap over accept with
    ⟨sh,ex,lo,hi,gt,weight,valid⟩ | bad
  · refine .inr ⟨sh,ex,lo,hi,gt,valid,fun keys => ?_⟩
    let active (v : Fin n) := sh.stmt.bitmap.getLsbD v.val
    let part (v : Fin n) := Composed.quorumParticipated (custody sh.shardId v) s.message
    cases h : (List.finRange n).find? (fun v => active v && !part v) with
    | some v =>
      have hv : (active v && !part v) = true :=
        List.find?_some (p := fun i => active i && !part i) h
      obtain ⟨act,no⟩ := Bool.and_eq_true_iff.mp hv
      obtain ⟨sig,_,ok⟩ := (Spec.ValidAggregateWitness_iff _ _ _).mp valid.2.2.2.2.2.1 v act
      rw [keys v, valid.2.2.1] at ok
      exact ⟨v,act,sig,ok,(by cases hp : part v <;> simp_all : part v = false)⟩
    | none =>
      have le : Composed.weight sh.stmt.bitmap ≤ cap sh.shardId := by
        change qsum n (fun i => if active i then 1 else 0) ≤ ((List.finRange n).filter part).length
        rw [count_participating]
        apply qsum_le_qsum
        intro v
        have no := List.find?_eq_none.mp h v (List.mem_finRange v)
        cases ha : active v <;> cases hp : part v <;> simp_all
      rw [← weight] at le
      exact False.elim (Nat.not_lt_of_ge le gt)
  · exact .inl bad

def spineBudget (d Q : Nat) : RatBound :=
  RatBound.add (RatBound.scale (d+1)
    (RatBound.add (sumcheckBudget Q) (scheduleQromError (zkHemV2ProdSched 23) Q)))
    (merkleProfileQromBound .poseidon2Gl24 Q)

theorem spineBudget_lt_130 {d Q : Nat} (hd : d ≤ 64) (hq : Q ≤ 2^64) :
    RatBound.lt (spineBudget d Q) (RatBound.invPow2 130) := by
  apply ratBound_lt_of_le_of_lt (b := spineBudget 64 (2^64))
  · apply RatBound.add_le_add _ (merkleProfileQromBound_mono _ hq)
    apply scale_le (Nat.succ_le_succ hd)
    apply RatBound.add_le_add _ (scheduleQromError_mono _ hq)
    apply scale_le _ (RatBound.le_refl _)
    exact Nat.pow_le_pow_left (by omega) 2
  · simp only [spineBudget, scheduleQromError_eq, WhirVerifierSchedule.roundBounds_eq,
      zkHemV2ProdSched.public_eq_1, zkHemV2ProdStages.public_eq_8, stagesRoundBounds_cons,
      stagesRoundBounds_nil, WhirStage.roundBounds_eq, WhirStage.foldBound_eq, WhirStage.oodBound_eq,
      WhirStage.shiftBound_eq, binom2_eq]
    decide +kernel

theorem spineBudget_lt_128 {d Q : Nat} (hd : d ≤ 64) (hq : Q ≤ 2^64) :
    RatBound.lt (spineBudget d Q) (RatBound.invPow2 128) :=
  ratBound_lt_of_le_of_lt (b := RatBound.invPow2 130) (Nat.le_of_lt (spineBudget_lt_130 hd hq))
    (by decide +kernel)

instance (q : SpineSearch) (d : Nat) (s : IvcTreeStatement) : Decidable (q.applies d s) := by
  cases q with
  | target id => exact inferInstanceAs (Decidable (s.lo ≤ id ∧ id < s.lo + 2^d))
  | excess cap => exact inferInstanceAs (Decidable (rangeCap cap s.lo (2^d) < s.totalQuorums))

def spineEvents {n nv : Nat} (env : IvcExtractionContext nv) (d : Nat) (select : IvcTreeStatement → SpineSearch)
    (H : Fin n → IvcAlgebra.RO) (run : Fin n → Child env × QromQueryTranscript) :
    (Fin (d+1) → Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool) :=
  let path := fun w => walk env (H w) (run w).2 (select (run w).1.1) d (run w).1.1 (run w).1.2
  let bad := fun (k : Fin (d+1)) (w : Fin n) => (path w).1[k.val]?.any fun (lv,s,p) =>
      spineStepBad env (H w) (run w).2 lv s p
  let collision := fun w => hasQueryCollision (run w).2
  let fail := fun w => decide ((select (run w).1.1).applies d (run w).1.1) &&
      verifyConcreteIvcRoot env.profile env.cfg (H w) d (run w).1.1 (run w).1.2 && (path w).2.isNone
  (bad,collision,fail)

/-- The games at position k inspect the node selected on that same sample.
Instantiating their bounds with the production schedule requires a reduction
for adaptive transcript extraction at the selected node. -/
theorem multidepth_spine_qrom_extractor_sound {n nc na nv : Nat}
    (env : IvcExtractionContext nv) (dep : IsDeployedAggProfile env.profile)
    (d Q : Nat) (hn : 0 < n) (coins : Spec.CoinSplit n nc na)
    (oracle : Fin nc → IvcAlgebra.RO) (prover : Fin na → OracleComp Spec.Bytes Spec.Bytes (Child env))
    (queries : ∀ i, QueryBounded Q (prover i)) (select : IvcTreeStatement → SpineSearch)
    (step coll : RatBound) :
    let H := fun w => oracle (coins.chal w)
    let run := fun w => recordedIvcRun (H w) (prover (coins.advc w))
    let ev := spineEvents env d select H run
    (∀ k, Spec.GameBound (Spec.FinGame.mk hn (ev.1 k)).winProb (toSpecRatBound step)) →
    Spec.GameBound (Spec.FinGame.mk hn ev.2.1).winProb (toSpecRatBound coll) →
    (∀ w, (run w).2.length ≤ Q) ∧ Spec.GameBound (Spec.FinGame.mk hn ev.2.2).winProb
      (toSpecRatBound (RatBound.add (RatBound.scale (d+1) step) coll)) := by
  intro H run ev each col
  let bad := ev.1
  let collision := ev.2.1
  let fail := ev.2.2
  let games := fun k => Spec.FinGame.mk hn (bad k)
  refine ⟨fun w => (recordedIvcRun_spec _ _ (queries (coins.advc w))).1, ?_⟩
  refine Spec.GameBound.trans (Spec.event_le_two_reductions (Spec.FinGame.mk hn fail)
    (Spec.FinGame.mk hn (anySlotWins (d+1) games)) (Spec.FinGame.mk hn collision) ?_)
    (Spec.RatBound.add_le_add (anySlotWins_bound hn _ games each) col)
  intro w loss
  cases hc : collision w with
  | true => exact .inr hc
  | false =>
    obtain ⟨eligible,miss⟩ := Bool.and_eq_true_iff.mp loss
    obtain ⟨app,accept⟩ := Bool.and_eq_true_iff.mp eligible
    rcases walk_sound env (H w) (run w).2 dep hc _ d _ _ accept (of_decide_eq_true app) with
      ⟨_,ok,_⟩ | ⟨k,hk,lv,s,p,atK,broken⟩
    · change (walk env (H w) (run w).2 _ d _ _).2.isNone = true at miss
      rw [ok] at miss
      cases miss
    · apply Or.inl (anySlotWins_of_win _ games w ⟨k,hk⟩ ?_)
      change ((walk env (H w) (run w).2 _ d _ _).1[k]?).any _ = true
      simp only [atK,Option.any_some,broken]

theorem selected_spine_failure_lt_128 {n nc na nv : Nat}
    (env : IvcExtractionContext nv) (dep : IsDeployedAggProfile env.profile)
    (d Q : Nat) (hn : 0 < n) (coins : Spec.CoinSplit n nc na)
    (oracle : Fin nc → IvcAlgebra.RO) (prover : Fin na → OracleComp Spec.Bytes Spec.Bytes (Child env))
    (queries : ∀ i, QueryBounded Q (prover i)) (select : IvcTreeStatement → SpineSearch)
    (hd : d ≤ 64) (hq : Q ≤ 2^64) :
    let H := fun w => oracle (coins.chal w)
    let run := fun w => recordedIvcRun (H w) (prover (coins.advc w))
    let step := RatBound.add (sumcheckBudget Q) (scheduleQromError (zkHemV2ProdSched 23) Q)
    let coll := merkleProfileQromBound .poseidon2Gl24 Q
    let ev := spineEvents env d select H run
    (∀ k, Spec.GameBound (Spec.FinGame.mk hn (ev.1 k)).winProb (toSpecRatBound step)) →
    Spec.GameBound (Spec.FinGame.mk hn ev.2.1).winProb (toSpecRatBound coll) →
    let win := (Spec.FinGame.mk hn ev.2.2).winProb
    RatBound.lt ⟨win.num,win.den,win.den_pos⟩ (RatBound.invPow2 128) := by
  intro H run step coll ev perPosition collision win
  have measured := (multidepth_spine_qrom_extractor_sound env dep d Q hn coins oracle prover
    queries select step coll perPosition collision).2
  exact ratBound_lt_of_le_of_lt (b := spineBudget d Q) measured (spineBudget_lt_128 hd hq)

#verify_constructive rangeCap_double walk_length_le extractLeafAlongSpine_sound
  extractOverclaimedSpine_sound overclaimed_spine_euf_cma_forgery spineBudget_lt_130 spineBudget_lt_128
  multidepth_spine_qrom_extractor_sound selected_spine_failure_lt_128
#print axioms extractLeafAlongSpine_sound
#print axioms overclaimed_spine_euf_cma_forgery
#print axioms spineBudget_lt_128
#print axioms multidepth_spine_qrom_extractor_sound

theorem spine_public_sumchecks_qrom {d cardX anc Q : Nat} (hd : d ≤ 64) (hq : Q ≤ 2^64)
    (A : Fin (d+1) → QuantumAdv cardX 320 anc Q)
    (codec : Fin (d+1) → FsCodec PublicMessage 95 cardX) (claims : Fin (d+1) → RoundClaims)
    (hg : ∀ i pre m, pre.length < 95 → ((claims i).honest pre m).length ≤ roundDegree pre.length + 1) :
    RatBound.lt (RatBound.sumList ((List.finRange (d+1)).map
      fun i => publicFsMass (A i) (codec i) (claims i))) (RatBound.invPow2 160) := by
  apply ratBound_lt_of_le_of_lt _ (tree_sumcheck_budget_lt_160 (d := 20) (Nat.le_refl _) hq)
  have each := RatBound.sumList_le_length_mul (bound := sumcheckBudget Q)
    ((List.finRange (d+1)).map fun i => publicFsMass (A i) (codec i) (claims i))
    (fun _ hm => by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
      exact public_sumchecks_qrom (A i) (codec i) (claims i) (hg i))
  rw [List.length_map,List.length_finRange] at each
  exact RatBound.le_trans each (scale_le (Nat.le_trans (Nat.succ_le_succ hd)
    (by decide : 65 ≤ treeNodeCount 20)) (RatBound.le_refl _))

theorem wire_interval_depth_lt_64 {d lo hi : Nat} (wire : hi < 2^64) (interval : hi = lo + 2^d) :
    d < 64 := by
  apply Nat.lt_of_not_ge
  intro h
  have pow := Nat.pow_le_pow_right (by decide : 0 < 2) h
  omega

#verify_constructive spine_public_sumchecks_qrom wire_interval_depth_lt_64

/-- A successful path requires the query for the complete encoded root witness.
A table commitment and bounded public-round agreement alone do not supply this record. -/
theorem successful_spine_requires_node_query {n : Nat} (env : IvcExtractionContext n)
    (H : IvcAlgebra.RO) (T : QromQueryTranscript) (q : SpineSearch) (d : Nat)
    (s : IvcTreeStatement) (p : ProofAt env) (sh : ExtractedLeafShard n)
    (found : (walk env H T q d s p).2 = some sh) :
    ∃ w : CommittedIvcNodeWitness env.cfg.params n,
      let input := nodeCommitmentInput env.profile d s p.stage0Nonce (NodeWire.node w)
      let output := encodeNatLeBytes 56 p.witnessCommitRoot.toNat
      (input,output) ∈ T ∧ H input = output := by
  cases h : extractIvcStepFromTranscript n env.profile H T d s p with
  | some w => exact ⟨w,extractIvcStepFromTranscript_recorded _ _ _ _ _ _ _ h⟩
  | none =>
    cases d with
    | zero =>
      cases v : verifyConcreteIvcRoot env.profile env.cfg H 0 s p <;>
        simp [walk,checkedLeaf,v,h] at found
    | succ m =>
      cases v : verifyConcreteIvcRoot env.profile env.cfg H (m+1) s p <;>
        simp [walk,checkedChildren,v,h] at found

open Depth2Cert in
/-- A fixed-oracle control for the recorded game. Replaying the certified
depth-two argument with an empty log makes the target extractor fail on the
only sample, even though the numerical budget at zero queries clears 128 bits. -/
theorem tooth_fixed_oracle_spine_replay :
    ¬ Spec.GameBound (Spec.FinGame.mk (n := 1) (by decide) (fun _ =>
      verifyConcreteIvcRoot fastEnv.profile fastEnv.cfg natXof56 2 rootStmt rootPi &&
      (extractLeafAlongSpine fastEnv natXof56 [] 2 rootStmt rootPi 0).isNone)).winProb
      (Spec.RatBound.invPow2 128) := by
  have empty : checkedChildren fastEnv natXof56 [] 1 rootStmt rootPi = none := by
    simp [checkedChildren,fast_root_accepts,extractIvcStepFromTranscript_nil]
  have miss : extractLeafAlongSpine fastEnv natXof56 [] 2 rootStmt rootPi 0 = none := by
    unfold extractLeafAlongSpine
    rw [walk,empty]
  rw [fast_root_accepts,miss]
  change ¬ (1 * 2^128 ≤ 1 * 1)
  decide

#tooth_pair selected_spine_failure_lt_128 vs tooth_fixed_oracle_spine_replay
#export_eqns rangeCap SpineSearch.applies SpineSearch.left SpineSearch.found
#export_eqns leafChecks walk spineStepBad LocatedBad
#export_eqns extractLeafAlongSpine spineNodeAt extractOverclaimedSpine overclaimedSpineNodeAt
#export_eqns spineBudget spineEvents honestShardParticipated
#verify_constructive successful_spine_requires_node_query

#verify_constructive tree_public_sumchecks_qrom first_fold_tree_budget_gt_2_neg_120
  checked_agreement_is_hit depth20_budget_interval tree_sumcheck_budget_lt_160
  fieldPool_spec public_sumchecks_qrom sumcheck_absorbs_before_challenge tooth_row_width_admits_three_agreements
  public_round_bad_challenges quadratic_bad_challenges
  tooth_unabsorbed_public_row_sumcheck_forges_claim treeBudget_lt_128
  tooth_dkt26_tree_budget_exceeds_target extract_outside_node_failures
#tooth_pair quadratic_bad_challenges vs tooth_unabsorbed_public_row_sumcheck_forges_claim
#tooth_pair treeBudget_lt_128 vs tooth_dkt26_tree_budget_exceeds_target
#print axioms tree_public_sumchecks_qrom
#print axioms first_fold_tree_budget_gt_2_neg_120
#print axioms public_sumchecks_qrom
#print axioms sumcheck_absorbs_before_challenge
#print axioms public_round_bad_challenges
#print axioms tooth_row_width_admits_three_agreements
#print axioms quadratic_bad_challenges
#print axioms tooth_unabsorbed_public_row_sumcheck_forges_claim
#print axioms treeBudget_lt_128
#print axioms tooth_dkt26_tree_budget_exceeds_target
#print axioms extract_outside_node_failures

end Qsag.RecursiveIvcPublicRowQrom
end
