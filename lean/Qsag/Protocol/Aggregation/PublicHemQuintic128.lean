module
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Aggregation.ZkHem
import Qsag.Protocol.Aggregation.HemRbrSoundness
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Aggregation
open Qsag.ClosedWhir Qsag.ZkHemV2Cert Qsag.ClosedFs
set_option autoImplicit false
set_option exponentiation.threshold 10000
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Wire choices for QSAGHQM2. Both use a 400-bit Fiat–Shamir chain.
    Seven canonical Goldilocks limbs have exactly p^7 possible values. -/
inductive PublicHemQuintic128 where
  | turboShake400 | poseidon2Gl24
  deriving DecidableEq

def publicHemDigestCard : PublicHemQuintic128 → Nat
  | .turboShake400 => 2^400
  | .poseidon2Gl24 => goldilocksPrime^7

theorem publicHemDigestCard_pos (p : PublicHemQuintic128) : 0 < publicHemDigestCard p := by
  cases p <;> decide +kernel

/-- Arithmetic throughout the round analysis publicHemRounds *up* to multiples of 2^-320. -/
private def units (num den : Nat) : Nat :=
  if den = 0 then 2^320 else (num * 2^320 + den - 1) / den

/-- Agreement on the fiber domain and CWYZ26 (multiplicity, Y-degree) witnesses
    for each successive virtual fold. Order and dimensions come from the deployed schedule. -/
structure PublicStageWitness where
  agree : Nat
  interpolation : List (Nat × Nat)
  deriving Repr

def publicAffineWitnesses : Nat → List PublicStageWitness
  | 16 => [
    ⟨8271, [(1024, 38869), (128, 7999), (64, 5547), (64, 5547)]⟩,
    ⟨2119, [(1024, 34833), (64, 3706), (32, 2987)]⟩,
    ⟨573, [(512, 14385), (16, 718), (8, 521)]⟩]
  | 17 => [
    ⟨8271, [(1024, 38869), (128, 7999), (64, 5547), (64, 5547), (64, 5547)]⟩,
    ⟨2119, [(1024, 34833), (64, 3706), (32, 2987)]⟩,
    ⟨302, [(1024, 21308), (8, 241), (8, 497), (4, 304)]⟩]
  | 18 => [
    ⟨16496, [(1024, 54747), (128, 10175), (128, 20415), (64, 5547), (64, 5547)]⟩,
    ⟨4194, [(1024, 48269), (64, 4671), (32, 3190)]⟩,
    ⟨573, [(512, 14385), (16, 718), (8, 521), (8, 1060)]⟩]
  | 19 => [
    ⟨32927, [(1024, 76750), (256, 32383), (128, 22016), (128, 22016), (128, 22017)]⟩,
    ⟨8329, [(1024, 67465), (128, 14325), (64, 11351)]⟩,
    ⟨1105, [(1024, 38980), (32, 2069), (16, 1669), (16, 3371)]⟩]
  | 20 => [
    ⟨65765, [(1024, 108511), (256, 42111), (256, 84351), (128, 22017), (128, 22017)]⟩,
    ⟨16577, [(1024, 94594), (128, 18431), (64, 12398)]⟩,
    ⟨2159, [(1024, 54088), (32, 2590), (16, 1755), (16, 3532)]⟩]
  | 21 => [
    ⟨65765, [(1024, 108511), (256, 42111), (256, 84351), (128, 22017), (128, 22017), (128, 22017)]⟩,
    ⟨16577, [(1024, 94594), (128, 18431), (64, 12398)]⟩,
    ⟨2159, [(1024, 54088), (32, 2590), (16, 1755), (16, 3532)]⟩]
  | 22 => [
    ⟨131403, [(1024, 152551), (512, 136447), (256, 87723), (256, 87723), (256, 87723), (256, 87723)]⟩,
    ⟨16577, [(1024, 94594), (128, 18431), (64, 12398), (64, 22187)]⟩,
    ⟨2159, [(1024, 54088), (32, 2590), (16, 1755), (16, 3532)]⟩]
  | 23 => [
    ⟨262630, [(1024, 215503), (512, 183039), (256, 87723), (256, 87723), (256, 87723), (256, 87723)]⟩,
    ⟨33042, [(1024, 132990), (256, 57579), (128, 45487), (128, 88063)]⟩,
    ⟨8403, [(1024, 103918), (64, 9790), (64, 19692)]⟩,
    ⟨2215, [(1024, 80453), (32, 4234), (16, 3370)]⟩]
  | 24 => [
    ⟨525011, [(1024, 304127), (512, 238975), (512, 350208), (512, 350208), (512, 350209), (512, 350209)]⟩,
    ⟨66053, [(256, 53611), (128, 41519), (128, 83166), (128, 88064)]⟩,
    ⟨16680, [(1024, 145642), (128, 30428), (64, 23450)]⟩,
    ⟨4324, [(1024, 111151), (32, 5239), (32, 10602)]⟩]
  | 25 => [
    ⟨1049672, [(1024, 429567), (1024, 859647), (512, 350208), (512, 350209), (512, 350209), (512, 350209)]⟩,
    ⟨132101, [(128, 41199), (128, 82526), (128, 88064), (64, 22188)]⟩,
    ⟨16680, [(1024, 145642), (128, 30428), (64, 23450), (64, 47029)]⟩,
    ⟨4324, [(1024, 111151), (32, 5239), (32, 10602)]⟩]
  | 26 => [
    ⟨2099203, [(1024, 787455), (512, 350208), (512, 350209), (512, 350209), (512, 350209), (512, 350209)]⟩,
    ⟨132101, [(128, 41199), (128, 82526), (128, 88064), (64, 22188), (64, 22188)]⟩,
    ⟨16680, [(1024, 145642), (128, 30428), (64, 23450), (64, 47029)]⟩,
    ⟨4324, [(1024, 111151), (32, 5239), (32, 10602)]⟩]
  | 27 => [
    ⟨4198403, [(512, 350208), (512, 350209), (512, 350209), (512, 350209), (512, 350209), (512, 350209)]⟩,
    ⟨264197, [(128, 82206), (128, 88064), (64, 22188), (64, 22188), (64, 22188)]⟩,
    ⟨33185, [(1024, 204003), (128, 38764), (128, 77786), (64, 49516)]⟩,
    ⟨4324, [(1024, 111151), (32, 5239), (32, 10602), (16, 6950)]⟩]
  | 28 => [
    ⟨8396803, [(512, 350209), (512, 350209), (512, 350209), (512, 350209), (512, 350209), (512, 350209)]⟩,
    ⟨264197, [(128, 82206), (128, 88064), (64, 22188), (64, 22188), (64, 22188), (64, 22188)]⟩,
    ⟨33185, [(1024, 204003), (128, 38764), (128, 77786), (64, 49516)]⟩,
    ⟨4324, [(1024, 111151), (32, 5239), (32, 10602), (16, 6950)]⟩]
  | _ => []

/-- Johnson bound for one fixed received word. A degenerate threshold fails the check. -/
private def johnsonList (n a d : Nat) : Nat :=
  n*(a-d)/(a*a-n*d)

private def wordList (s : WhirStage) (w : PublicStageWitness) : Nat :=
  let n := s.domainSize * 2^s.foldK
  johnsonList n (w.agree * 2^s.foldK) (n / 2^s.logInvRate + 2)

/-- Six times the interpolation count ∑_{j=0}^h (A-g*j)(B-j). Clearing
    denominators keeps the CWYZ26 (4.5) test in kernel natural arithmetic. -/
private def sixSum (A B g h : Nat) : Nat :=
  (h+1)*(6*A*B + g*h*(2*h+1) - 3*(A+g*B)*h)

private def foldWitnessOk (n d a m D : Nat) : Bool :=
  let M := min D ((m*a-D-1)/d)
  decide (0 < m ∧ 0 < D ∧ 0 < M ∧ D+d*M < m*a ∧
    n*(d+1) < (a-1)^2 ∧
    n*sixSum m (D+1) 1 (min M (m-1)) < sixSum (m*a-D) (D+1) d M ∧
    (D^2 + 4*d^2*M^2*D^3)*n^2 < quinticGoldilocksCard)

private def levels (s : WhirStage) (w : PublicStageWitness) :=
  (List.range s.foldK).map fun j =>
    let n := s.domainSize * 2^j
    (n, n/2^s.logInvRate+2, w.agree*2^j)

private def affineBad (s : WhirStage) (w : PublicStageWitness) : Nat :=
  (levels s w).foldl (fun b (n,d,a) =>
    max b (johnsonList n (a-1) (d+1) + 2*johnsonList n (a-1) d + 1)) 0

def publicStageWitnessOk (s : WhirStage) (w : PublicStageWitness) : Bool :=
  let n := s.domainSize * 2^s.foldK
  let a := w.agree * 2^s.foldK
  decide (w.interpolation.length = s.foldK ∧ w.agree+s.foldK ≤ s.domainSize ∧
    n/2^s.logInvRate+3 ≤ a ∧ s.agree ≤ w.agree ∧ s.queryCount ≤ s.domainSize ∧ n*(n/2^s.logInvRate+2) < a^2 ∧
    wordList s w ≤ 2^20 ∧ s.foldK*affineBad s w + 1 < 16384 ∧ s.logDomain+s.foldK ≤ 32) &&
  ((levels s w).zip w.interpolation).all fun ((n,d,a),(m,D)) => foldWitnessOk n d a m D

/-- Maximum of the OOD list collision, random batching, affine-fold and
    sampled fiber bounds. A missing or invalid interpolation witness costs one. -/
private def stageUnits (s : WhirStage) (w : PublicStageWitness) : Nat :=
  let q := quinticGoldilocksCard
  let L := wordList s w
  let d := s.domainSize * 2^s.foldK / 2^s.logInvRate + 2
  let ood := units ((L*(L-1)/2)*d^s.oodCount) (q^s.oodCount)
  -- Each binary affine fold also batches claims from pairs of decoder candidates.
  -- Three low-degree pairs and one high-degree pair suffice in the four-coin bridge.
  let Lfold := affineBad s w
  let fold := units (s.foldK*(Lfold + 4*Lfold^2) + 1) q
  let query := units (affineFallingFactorial (w.agree+s.foldK) s.queryCount) (affineFallingFactorial s.domainSize s.queryCount)
  let batch := units (2^20*(s.queryCount+s.oodCount)) q
  if publicStageWitnessOk s w then max ood (max fold (query + batch)) else 2^320

/-- The random row point, constraint-batching scalar, degree-eight row messages and
    column claim are fixed before their respective challenges. 2^20 bounds both the
    degree of batching the StepOp residuals and the number of candidate tables. -/
def publicHemRoundUnits (n : Nat) : Nat :=
  let stages := zkHemV2ProdStages n
  let ws := publicAffineWitnesses n
  if stages.length = ws.length then
    (stages.zip ws).foldl (fun worst (s,w) => max worst (stageUnits s w))
      (units (2^20 * 2^20) quinticGoldilocksCard)
  else 2^320

def publicHemRounds (n : Nat) : Nat :=
  let stages := zkHemV2ProdStages n
  6 + (n-8) + (stages.map (fun s => 2*s.foldK + 3)).sum

/-- Merkle verifier visits before sibling deduplication, plus the Rust transcript cap.
    All hash draws, including rejection-sampling retries, debit this cap. -/
private def visits (n : Nat) : Nat :=
  4096 + ((zkHemV2ProdStages n).map (fun s => (s.logDomain+1)*s.queryCount + 1)).sum

private theorem budgets (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    publicHemRoundUnits n ≤ 2^55 ∧ publicHemRounds n ≤ 100 ∧ visits n + publicHemRounds n ≤ 2^15 ∧
    (zkHemV2ProdStages n).length = (publicAffineWitnesses n).length ∧
    ((zkHemV2ProdStages n).zip (publicAffineWitnesses n)).all
      (fun (s,w) => publicStageWitnessOk s w) = true := by
  have h : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
      n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [publicHemRoundUnits, publicHemRounds, visits, zkHemV2ProdStages.public_eqs] <;> decide +kernel

/-- The deployed agreement thresholds bound the length of the mathematical decoder's
    entire list for every received word on every stage domain. -/
theorem publicHemQuintic_decoder_list_bound
    (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (s : WhirStage) (w : PublicStageWitness)
    (stage : (s,w) ∈ (zkHemV2ProdStages n).zip (publicAffineWitnesses n))
    (dom : List QuinticGoldilocks) (word : QuinticGoldilocks → QuinticGoldilocks)
    (distinct : dom.Nodup) (hlen : dom.length = s.domainSize * 2^s.foldK) :
    (gsDecodeList (dom.length/2^s.logInvRate+2) (w.agree*2^s.foldK) dom word).length ≤ 2^20 := by
  have ok := List.all_eq_true.mp (budgets n lo hi).2.2.2.2 (s,w) stage
  change publicStageWitnessOk s w = true at ok
  unfold publicStageWitnessOk at ok
  have hs := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).1
  have bound := gsDecodeList_length_le_johnson dom word (dom.length/2^s.logInvRate+2)
    (w.agree*2^s.foldK) distinct (by rw [hlen]; exact hs.2.2.1)
    (by rw [hlen]; simpa only [Nat.pow_two] using hs.2.2.2.2.2.1)
  rw [hlen, JohnsonBound.johnsonBound_eq] at bound
  rw [hlen]
  exact Nat.le_trans bound hs.2.2.2.2.2.2.1

/-- Reed–Solomon word domain for the Rust encoder at this stage, with coset shift 7. -/
def publicHemRsDomain (s : WhirStage) : List QuinticGoldilocks :=
  ZkHemV2.fiberRoots (s.logDomain+s.foldK) (QuinticGoldilocks.ofBase (Goldilocks.ofNat 7))

theorem publicHemQuintic_rs_decoder_list_bound (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28)
    (s : WhirStage) (w : PublicStageWitness)
    (stage : (s,w) ∈ (zkHemV2ProdStages n).zip (publicAffineWitnesses n))
    (word : QuinticGoldilocks → QuinticGoldilocks) :
    let dom := publicHemRsDomain s
    (gsDecodeList (dom.length/2^s.logInvRate+2) (w.agree*2^s.foldK) dom word).length ≤ 2^20 := by
  have ok := List.all_eq_true.mp (budgets n lo hi).2.2.2.2 (s,w) stage
  change publicStageWitnessOk s w = true at ok
  unfold publicStageWitnessOk at ok
  have hs := of_decide_eq_true (Bool.and_eq_true_iff.mp ok).1
  apply publicHemQuintic_decoder_list_bound n lo hi s w stage
  · apply ZkHemV2.fiberRoots_nodup _ hs.2.2.2.2.2.2.2.2
    decide +kernel
  · rw [publicHemRsDomain, ZkHemV2.fiberRoots_length, Nat.pow_add]
    rfl

/-- Stage zero meets the DKT26 threshold and uses the exact deployed profile query count. -/
theorem publicHemQuintic_stage0_dkt_queries (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) :
    (match (zkHemV2ProdStages n)[0]?, (publicAffineWitnesses n)[0]? with
    | some s, some w => dkt26Covers 4 (n-s.foldK) 512 w.agree &&
        decide (s.queryCount = (if n < 24 then 267 else 266))
    | _, _ => false) = true := by
  have h : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
      n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [zkHemV2ProdStages.public_eqs, dkt26Covers.public_eqs] <;> decide +kernel

/-- Count the accepted tuples in the actual without-replacement sample space.
    The supplied good set is the agreement set of a fixed received oracle. -/
theorem publicHemQuintic_deployed_query_count {α : Type} [DecidableEq α]
    (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (s : WhirStage) (w : PublicStageWitness)
    (stage : (s,w) ∈ (zkHemV2ProdStages n).zip (publicAffineWitnesses n))
    (U : List α) (good : α → Bool) (nodup : U.Nodup) (hlen : U.length = s.domainSize)
    (hGood : (U.filter good).length ≤ w.agree+s.foldK) :
    ((affineDistinctTuples s.queryCount U).filter (fun t => t.all good)).length * 2^265 <
      (affineDistinctTuples s.queryCount U).length := by
  have checks : ((zkHemV2ProdStages n).zip (publicAffineWitnesses n)).all (fun (s,w) =>
      decide (affineFallingFactorial (w.agree+s.foldK) s.queryCount * 2^265 <
        affineFallingFactorial s.domainSize s.queryCount)) = true := by
    have h : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
        n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [zkHemV2ProdStages.public_eqs] <;> decide +kernel
  have bound := of_decide_eq_true (List.all_eq_true.mp checks (s,w) stage)
  have hCount := affineDistinctTuples_all_good_le s.queryCount (w.agree+s.foldK) U good nodup hGood
  rw [affineDistinctTuples_length _ nodup, hlen]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hCount) bound

/-- CDHZ25 with the verifier offsets, commutativity and offline remainders retained.
    The verifier and proof-query caps dominate all thirteen public schedules. -/
def publicHemMerkleNumerator (t : Nat) : Nat :=
  1280*t*(2*t+1)^2 + 960*t*(t+1+2^15+100)^2 + 300*t^3 +
    480*(2^15)^2*(t+100+2^15+2) + 128*2^15*28

def publicHemError (p : PublicHemQuintic128) (n t : Nat) : RatBound :=
  let k := publicHemRounds n
  let r := publicHemRoundUnits n
  let merkle := publicHemMerkleNumerator t
  RatBound.add
    ⟨320*(t+k+1)*(t+k)*r + 8*(t+k+1)*k, 2^320, by decide⟩
    (RatBound.add ⟨merkle, publicHemDigestCard p, publicHemDigestCard_pos p⟩
      ⟨merkle, 2^400, by decide⟩)

/-- Strict bound on the public profile's total QROM knowledge-error budget under the
    CDHZ25 reduction and the ideal hash model. Includes a separate transcript hash term. -/
theorem publicHemQuintic_qrom_soundness_128 (profile : PublicHemQuintic128)
    (logCells qOracle : Nat) (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28)
    (hQ : qOracle ≤ 2^64) :
    RatBound.lt (publicHemError profile logCells qOracle) ⟨1, 2^128, by decide⟩ := by
  obtain ⟨hr,hk,_,_,_⟩ := budgets logCells hLo hHi
  let T := 2^64
  have h1 : qOracle + publicHemRounds logCells ≤ T + 100 := Nat.add_le_add hQ hk
  have h2 := Nat.add_le_add_right h1 1
  have hRound := Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 320 h2) h1) hr)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 8 h2) hk)
  have hm : publicHemMerkleNumerator qOracle ≤ publicHemMerkleNumerator T := by
    have h : qOracle ≤ T := hQ
    have a := Nat.mul_le_mul (Nat.mul_le_mul_left 1280 h)
      (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1) 2)
    have b := Nat.mul_le_mul (Nat.mul_le_mul_left 960 h)
      (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right h 1) (2^15)) 100) 2)
    have c := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left h 3)
    have d := Nat.mul_le_mul_left (480*(2^15)^2)
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right h 100) (2^15)) 2)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d) _
  cases profile <;>
    (unfold publicHemError RatBound.lt RatBound.add
     dsimp only
     apply Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.add_le_add
       (Nat.mul_le_mul_right _ hRound)
       (Nat.mul_le_mul_right _ (Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_right _ hm)))))
     decide +kernel)

/-- Even the digest term of the legacy Ext4 schedule's published upper bound
    exceeds the target. This is a statement about the guarantee in the reduction. -/
theorem tooth_legacy_publicHem_qrom_budget :
    RatBound.lt ⟨1, 2^128, by decide⟩
      (RatBound.add (scheduleQromError deployedSched (2^64))
        ⟨6380*(2^64)^3, 2^256, by decide⟩) := by
  let s := scheduleQromError deployedSched (2^64)
  have hs : 0 < s.den := s.h_pos
  have hd : 2^256 < (6380*(2^64)^3)*2^128 := by decide +kernel
  show 1*(s.den*2^256) < (s.num*2^256 + 6380*(2^64)^3*s.den)*2^128
  rw [Nat.one_mul, Nat.add_mul]
  apply Nat.lt_of_lt_of_le _ (Nat.le_add_left _ _)
  rw [Nat.mul_comm (6380*(2^64)^3) s.den, Nat.mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left hd hs

theorem tooth_legacy_publicHem_refutes_128 :
    ¬ RatBound.le (RatBound.add (scheduleQromError deployedSched (2^64))
        ⟨6380*(2^64)^3, 2^256, by decide⟩) ⟨1, 2^128, by decide⟩ :=
  Nat.not_le_of_lt tooth_legacy_publicHem_qrom_budget

/-- A checked false row polynomial can recover the honest running claim at
    most eight quintic challenges. This includes the degree-seven S-boxes and
    the extra equality-polynomial factor of the public row check. -/
theorem publicHemQuintic_row_collision_count (honest sent pool : List QuinticGoldilocks)
    (claim : QuinticGoldilocks) (distinct : pool.Nodup)
    (hg : honest.length ≤ 9) (hs : sent.length ≤ 9)
    (check : CommRingOps.add (RoundPoly.evalCoeffs sent CommRingOps.zero)
               (RoundPoly.evalCoeffs sent CommRingOps.one) = claim)
    (bad : claim ≠ CommRingOps.add (RoundPoly.evalCoeffs honest CommRingOps.zero)
               (RoundPoly.evalCoeffs honest CommRingOps.one)) :
    (pool.filter fun x => decide (RoundPoly.evalCoeffs sent x = RoundPoly.evalCoeffs honest x)).length ≤ 8 :=
  hemSumcheck_polynomial_collision_count 8 honest sent pool claim distinct hg hs check bad

/-- A false native StepOp constraint contributes a nonzero coefficient to the
    corresponding quintic batching polynomial. Count its bad batching scalars. -/
theorem publicHemQuintic_stepOp_gamma_roots (scheme : AggSigProfile) (slot : StepOpSlot)
    (t : Nat) (row : StepOpRow) (pool : List QuinticGoldilocks) (distinct : pool.Nodup)
    (bad : allZeroGoldilocks (stepOp256RowResiduals scheme slot t row) = false) :
    let res := stepOp256RowResiduals scheme slot t row
    (pool.filter fun x => decide (RoundPoly.evalCoeffs
      (res.map QuinticGoldilocks.ofBase) x = CommRingOps.zero)).length ≤ res.length - 1 := by
  let res := stepOp256RowResiduals scheme slot t row
  obtain ⟨c,mem,ne⟩ := exists_ne_zero_of_not_allZero res bad
  have len := List.length_pos_of_mem mem
  apply ZkHem.roots_le_of_exists_nonzero
  · rw [List.length_map]
    omega
  · refine ⟨QuinticGoldilocks.ofBase c, List.mem_map.mpr ⟨c, mem, rfl⟩, ?_⟩
    intro equal
    exact ne (QuinticGoldilocks.ofBase_injective (equal.trans QuinticGoldilocks.ofBase_zero.symm))
  · exact distinct

/-- Once the opening extractor supplies the committed satisfying table, each
    active slot yields a concrete native signature for that key and message. -/
theorem publicHemQuintic_extract_slot (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pk : AggValidatorPk) (msg : List UInt8)
    (slot : slots[k]? = some (some (pk, computeMessageMu pk msg)))
    (valid : stepOp256TableOk pk.profile slots rows = true) :
    ∃ sig, verifyAggNativeSig
      (match pk.profile with | .xmssPoseidon2 => xmssPoseidon2Geom | .corduroyPoseidon2 => corduroyPoseidon2Geom)
      pk msg sig = true := by
  cases hp : pk.profile with
  | xmssPoseidon2 =>
    exact ⟨_, stepOp256TableOk_xmss_extract slots rows k (pk, computeMessageMu pk msg) msg
      (hp ▸ valid) slot hp rfl⟩
  | corduroyPoseidon2 =>
    exact ⟨_, stepOp256TableOk_corduroy_extract slots rows k (pk, computeMessageMu pk msg) msg
      (hp ▸ valid) slot hp rfl⟩

/-- Hash operations on one of the two deployed digest alphabets. Leaf inputs are
    canonical fiber bytes. The node tweak is the heap index used by CanopyTree. -/
structure PublicCanopy (p : PublicHemQuintic128) where
  leaf : Nat → Nat → List UInt8 → Fin (publicHemDigestCard p)
  node : Nat → Fin (publicHemDigestCard p) → Fin (publicHemDigestCard p) → Fin (publicHemDigestCard p)
  wrap : Nat → Nat → Fin (publicHemDigestCard p) → Fin (publicHemDigestCard p)

def PublicCanopy.levelNode {p : PublicHemQuintic128} (M : PublicCanopy p) (depth lvl idx : Nat) :=
  M.node (2^(depth-(lvl+1)) + idx)

def PublicCanopy.openRoot {p : PublicHemQuintic128} (M : PublicCanopy p)
    (stage depth pos : Nat) (fiber : List UInt8) (path : List (Fin (publicHemDigestCard p))) :=
  M.wrap stage depth (Qsag.ClosedFs.merklePathRoot (M.levelNode depth) 0 pos (M.leaf stage pos fiber) path)

inductive PublicCanopy.Collision {p : PublicHemQuintic128} (M : PublicCanopy p) (stage depth pos : Nat) where
  | leaf (x y : List UInt8) (distinct : x ≠ y) (collide : M.leaf stage pos x = M.leaf stage pos y)
  | node (w : MerkleCollisionWitness (M.levelNode depth))
  | wrap (x y : Fin (publicHemDigestCard p)) (distinct : x ≠ y)
      (collide : M.wrap stage depth x = M.wrap stage depth y)

/-- Extract a concrete collision from two different fibers opened at the same
    position of the same public commitment, including a collision in the root wrapper. -/
def publicHemQuintic_extract_canopy_collision {p : PublicHemQuintic128} (M : PublicCanopy p)
    (stage depth pos : Nat) (x y : List UInt8) (px py : List (Fin (publicHemDigestCard p)))
    (hx : px.length = depth) (hy : py.length = depth) (different : x ≠ y)
    (accepted : M.openRoot stage depth pos x px = M.openRoot stage depth pos y py) :
    M.Collision stage depth pos := by
  let a := Qsag.ClosedFs.merklePathRoot (M.levelNode depth) 0 pos (M.leaf stage pos x) px
  let b := Qsag.ClosedFs.merklePathRoot (M.levelNode depth) 0 pos (M.leaf stage pos y) py
  if equal : a = b then
    cases extractMerkleCollision (M.levelNode depth) px py 0 pos (M.leaf stage pos x)
      (M.leaf stage pos y) (hx.trans hy.symm) equal with
    | inl h => exact .leaf x y different h.1
    | inr collision => exact .node collision
  else exact .wrap a b equal accepted

/-- One Stage-0 symbol and its complete fiber, after expanding the deduplicated path.
    The fiber position and offset determine its Reed–Solomon evaluation point. -/
structure PublicStage0Sample (p : PublicHemQuintic128) where
  pos : Nat
  offset : Nat
  fiber : List UInt8
  path : List (Fin (publicHemDigestCard p))

def PublicStage0Sample.point {p : PublicHemQuintic128} (s : WhirStage) (a : PublicStage0Sample p) :
    QuinticGoldilocks :=
  QuinticGoldilocks.ofBase (CommRingOps.mul (Goldilocks.ofNat 7)
    (ZkHemV2.fpow (ZkHemV2.twoAdicElem (s.logDomain+s.foldK)) (a.pos+a.offset*s.domainSize)))

def PublicStage0Sample.read {p : PublicHemQuintic128} (M : PublicCanopy p)
    (s : WhirStage) (root : Fin (publicHemDigestCard p)) (a : PublicStage0Sample p) :
    Option QuinticGoldilocks := do
  guard (a.pos < s.domainSize && a.offset < 2^s.foldK && a.fiber.length == 8*2^s.foldK &&
    a.path.length == s.logDomain && (M.openRoot 0 s.logDomain a.pos a.fiber a.path).val == root.val)
  let (v,_) ← decodeGoldilocksLe8 (a.fiber.drop (8*a.offset))
  return QuinticGoldilocks.ofBase v

/-- Reconstruct the committed coefficient vector from enough authenticated samples. -/
def publicHemQuintic_interpolate {p : PublicHemQuintic128} (M : PublicCanopy p)
    (s : WhirStage) (root : Fin (publicHemDigestCard p)) (samples : List (PublicStage0Sample p)) :
    Option (List QuinticGoldilocks) := do
  let xs := samples.map (PublicStage0Sample.point s)
  guard xs.Nodup
  let ys ← samples.mapM (PublicStage0Sample.read M s root)
  return ZkHem.interp xs ys

theorem publicHemQuintic_stage0_recover {p : PublicHemQuintic128} (M : PublicCanopy p)
    (s : WhirStage) (root : Fin (publicHemDigestCard p)) (samples : List (PublicStage0Sample p))
    (coeffs : List QuinticGoldilocks) (size : coeffs.length = samples.length)
    (distinct : (samples.map (PublicStage0Sample.point s)).Nodup)
    (opened : ∀ a ∈ samples, a.read M s root =
      some (RoundPoly.evalCoeffs coeffs (a.point s))) :
    publicHemQuintic_interpolate M s root samples = some coeffs := by
  have collect : ∀ as : List (PublicStage0Sample p),
      (∀ a ∈ as, a.read M s root = some (RoundPoly.evalCoeffs coeffs (a.point s))) →
      as.mapM (PublicStage0Sample.read M s root) =
        some (as.map (fun a => RoundPoly.evalCoeffs coeffs (a.point s))) := by
    intro as
    induction as with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro h
      rw [List.mapM_cons, h x List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
      rfl
  have recovered := ZkHem.interp_evalAll (samples.map (PublicStage0Sample.point s)) coeffs
    distinct (by simpa only [List.length_map] using size)
  rw [ZkHem.evalAll.public_eqs] at recovered
  rw [List.map_map] at recovered
  unfold publicHemQuintic_interpolate
  simp only [distinct, guard, pure, ↓reduceIte, bind, Option.bind, collect samples opened]
  exact congrArg some recovered

/-- False-acceptance mass for the succinct Merkle-opening verifier. The explicit
    hypotheses specify the required protocol certificate, root consistency and collision
    game. A satisfying committed table yields the missing native signature at the slot. -/
theorem publicHemQuintic_succinct_false_acceptance {Stmt Msg Pub : Type} {cardX cardAnc Q : Nat}
    (p : PublicHemQuintic128) (n : Nat) (lo : 16 ≤ n) (hi : n ≤ 28) (hq : Q ≤ 2^64)
    (iop : OracleIop Stmt (List StepOpSlot) Msg Pub QuinticGoldilocks (publicHemRounds n))
    (width : iop.w = 400) (B : SuccinctIopBridge iop (Fin (publicHemDigestCard p)))
    (M : MerkleSetup (Fin (publicHemDigestCard p)) QuinticGoldilocks) (cert : BoolRbrCert iop)
    (badCount : ∀ j, cert.bad j ≤ publicHemRoundUnits n * 2^80)
    (sc : FsCodec (SuccinctRoundMsg (Fin (publicHemDigestCard p)) Pub) (publicHemRounds n) cardX)
    (aux : Fin cardX → List (QuinticGoldilocks × List (Fin (publicHemDigestCard p))))
    (ps : List StepOpSlot) (initRoots : Nat → Fin (publicHemDigestCard p))
    (tblOf : Nat → Fin (publicHemDigestCard p) → Nat → QuinticGoldilocks)
    (k : Nat) (pk : AggValidatorPk) (msg : List UInt8)
    (slot : ps[k]? = some (some (pk, computeMessageMu pk msg)))
    (relation : iop.inLang (B.liftStmt ps initRoots tblOf) →
      ∃ rows, stepOp256TableOk pk.profile ps rows = true)
    (absent : ∀ sig, verifyAggNativeSig
      (match pk.profile with | .xmssPoseidon2 => xmssPoseidon2Geom | .corduroyPoseidon2 => corduroyPoseidon2Geom)
      pk msg sig ≠ true)
    (hRoots : ∀ (H : Fin cardX → BitVec iop.w) (o : Fin cardX),
      succinctFsAccept iop B M sc aux ps initRoots H o = true →
      let str := fsTranscript sc H (sc.dec o)
      ∀ q ∈ iop.queries ps (str.map (fun sc' => (sc'.1.pub, sc'.2))),
        M.root q.1 (iop.depth q.1) (tblOf q.1 (B.rootsOf initRoots (str.map Prod.fst) q.1)) =
          B.rootsOf initRoots (str.map Prod.fst) q.1)
    (A : QuantumAdv cardX iop.w cardAnc Q)
    (hMerkle : RatBound.le
      ⟨uniformOracleSum iop.w cardX (fun H =>
          QVec.queryMassOn (succinctFsCollisionEvent iop B M sc aux ps initRoots tblOf H)
            (runQuantumAdv A H)),
        (2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos iop.w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩ ⟨publicHemMerkleNumerator (2^64), publicHemDigestCard p, publicHemDigestCard_pos p⟩) :
    RatBound.lt
      ⟨uniformOracleSum iop.w cardX (fun H =>
          QVec.queryMassOn (succinctFsAccept iop B M sc aux ps initRoots H) (runQuantumAdv A H)),
        (2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos iop.w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨1, 2^128, by decide⟩ := by
  obtain ⟨hr,hk,_,_,_⟩ := budgets n lo hi
  have hx : ¬ iop.inLang (B.liftStmt ps initRoots tblOf) := by
    intro h
    obtain ⟨rows,ok⟩ := relation h
    obtain ⟨sig,hSig⟩ := publicHemQuintic_extract_slot ps rows k pk msg slot ok
    exact absent sig hSig
  have hsum := qsum_le_qsum badCount
  rw [qsum_const] at hsum
  have hsum' := Nat.le_trans hsum (Nat.mul_le_mul hk (Nat.mul_le_mul_right _ hr))
  let cap : RatBound := ⟨(2*(2^64)+1)^2*(100*(2^55*2^80)),2^400,by decide⟩
  have hRbr : RatBound.le
      ⟨(2*Q+1)^2 * qsum (publicHemRounds n) cert.bad, 2^iop.w, Nat.two_pow_pos _⟩ cap := by
    unfold RatBound.le
    dsimp [cap]
    rw [width]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
      (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hq) 1) 2) hsum')
  have total := succinct_fs_qrom_total_error_budget iop B M cert sc aux ps initRoots tblOf
    hx hRoots A cap _ hRbr hMerkle
  apply ratBound_lt_of_le_of_lt total
  cases p <;> decide +kernel

#print axioms publicHemQuintic_stage0_recover
#print axioms publicHemQuintic_stepOp_gamma_roots
#print axioms publicHemQuintic_extract_canopy_collision
#print axioms publicHemQuintic_stage0_dkt_queries
#print axioms publicHemQuintic_rs_decoder_list_bound
#print axioms publicHemQuintic_decoder_list_bound
#print axioms publicHemQuintic_deployed_query_count
#print axioms publicHemQuintic_succinct_false_acceptance
#verify_constructive publicHemQuintic_succinct_false_acceptance publicHemQuintic_deployed_query_count
#verify_constructive publicHemQuintic_stage0_recover publicHemQuintic_stepOp_gamma_roots
#print axioms publicHemQuintic_extract_slot
#print axioms publicHemQuintic_row_collision_count
#print axioms publicHemQuintic_qrom_soundness_128
#print axioms tooth_legacy_publicHem_qrom_budget
#verify_constructive publicHemQuintic_qrom_soundness_128 tooth_legacy_publicHem_qrom_budget
#tooth_pair publicHemQuintic_qrom_soundness_128 vs tooth_legacy_publicHem_refutes_128
end Qsag.Aggregation
end
