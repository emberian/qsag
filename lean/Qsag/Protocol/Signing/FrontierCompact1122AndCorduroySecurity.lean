module
/-
# Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity — `Compact1122` (`FrontierSumFts`), Forward-Secure `RotatedEpochVote`, & `Corduroy` Stateless `Poseidon2` Threshold EUF-CMA

Constructive Lean 4.35 security reductions and real-parameter certifications (zero custom
axioms, purely constructive extractors):
1. **`Compact1122` (`h = 8, w = 96, L = 34, S = 1615, n = 32`) & `Full256Bit` Rank Domain & 1-Time EUF-CMA**:
   - Certifies `compact1122_rank_domain_gt_2pow256` (`2^263 < M(8, 96, 34, 1615) < 2^264`, wire size
     `1122` B, `RotatedEpochVote` `1194` B, plus `Full256Bit` `2^256 < M(8, 5, 72, 144)` and `2338` B),
     root-singleton exclusion (`frontierRootSubCount`), bijectivity of `unrankFrontierFts` /
     `rankFrontierFts`, stack-to-tree equivalence (`runFrontierStackLoop`), `cSHAKE256` domain
     disjointness across all seven `QSAG.FTS.*.V1` customization tags (`fts_cshake_domains_disjoint`),
     and constructive `Type`-valued 1-time EUF-CMA extraction (`extractCompact1122ForgeryBreak` /
     `compact1122_one_time_euf_cma_reduction`), paired with `tooth_drop_target_sum_allows_one_sig_forgery`.
2. **`RotatedEpochVote` Forward-Secure Key-Chain Induction (`rotatedEpochVote_forward_secure_chain`)**:
   - Models `EpochKeyLink` / `RotatedEpochVote` (`crates/qsag-fts/src/frontier.rs`) with injective
     104-byte big-endian framing (`encodeEpochVoteInput_injective`) under `cSHAKE256("QSAG.FTS.EPOCH.VOTE.V1")`
     (`cshakeEpochVoteHasher`), proving by induction across historical epochs that an accepted
     divergent chain yields an explicit `cSHAKE256` framing collision on distinct 104-byte inputs or
     a historical-key primitive break (`rotatedEpochVote_cshake_chain_reduction`), contrasted with
     `tooth_static_key_compromise_forges_historical_epoch`.
3. **`Corduroy` Width-12 `Poseidon2` Stateless Hypertree + `(t, n)` Shamir Power-7 EUF-CMA
   (`corduroy_threshold_stateless_euf_cma`)**:
   - Covers both real Rust profiles: `corduroyCustody128Params` (`d = 7, h' = 4, k = 33, a = 6,
     Q_max = 2^12`, `productionWellFormed = true`) and `corduroyPoseidon2AggParams` (`d = 16, h' = 4,
     k = 32, a = 8, Q_max = 2^20`, `76,896` B wire signature, explicitly documenting the `16 * 4 = 64 > 62`
     leaf-index check in `corduroy_real_profiles_audit`), composing stateless `poseidon2Suite` EUF-CMA
     extraction, `mkShamirProductionPqHashMpcOracles`, `< t` corrupted-custodian Shamir privacy
     (`shamir_single_share_privacy_bijection`), and SPDZ `GoldilocksExt2` MAC pin bounds
     (`spdzGateStream_pin_count_le`).
-/

public import Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.SpongeFramingAndDomainSep
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Math.Goldilocks
import all Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Keccak
import all Qsag.Oracle.SpongeFramingAndDomainSep
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. `Compact1122` (`FrontierSumFts`) Rank Bijection, `cSHAKE256` Framing & 1-Time EUF-CMA -/

structure FrontierFtsParams where
  nodeBytes : Nat
  treeHeight : Nat
  winternitzW : Nat
  frontierLen : Nat
  targetSum : Nat
  indexBits : Nat
  counterBits : Nat
  maxSafeUses : Nat
  deriving DecidableEq, Repr

/-- Exact `FrontierFtsProfile::Compact1122` parameters (`crates/qsag-fts/src/frontier.rs:108-117`). -/
@[expose] def compact1122Params : FrontierFtsParams := ⟨32, 8, 96, 34, 1615, 256, 16, 1⟩

/-- Exact `FrontierFtsProfile::Full256Bit` parameters (`crates/qsag-fts/src/frontier.rs:118-127`). -/
@[expose] def full256BitParams : FrontierFtsParams := ⟨32, 8, 5, 72, 144, 256, 16, 1⟩

@[expose] def FrontierFtsParams.signatureBytes (p : FrontierFtsParams) : Nat :=
  (p.frontierLen + 1) * p.nodeBytes + (p.counterBits + 7) / 8

@[expose] def FrontierFtsParams.rotatedEpochVoteBytes (p : FrontierFtsParams) : Nat :=
  72 + p.signatureBytes

def splitConvFrom (f : Nat → Nat) (ell cur : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => f cur * f (ell - cur) + splitConvFrom f ell (cur + 1) rem

/-- Non-root subtree antichain count `N_sub(t, ell)` (`0 ≤ t < h`, where `ell = 1` stops at subtree root). -/
def frontierSubCount : Nat → Nat → Nat
  | 0, ell => if ell = 1 then 1 else 0
  | t + 1, ell =>
    if ell = 0 then 0 else if ell = 1 then 1 else splitConvFrom (frontierSubCount t) ell 1 (ell - 1)

/-- Root antichain count `N_root(h, ell)` matching `crates/qsag-fts/src/frontier.rs:212-215`
    (`t = h` excludes singleton `ell = 1`; agrees with `frontierSubCount h ell` for all `ell ≥ 2`). -/
def frontierRootSubCount (h ell : Nat) : Nat :=
  if ell = 1 then 0 else frontierSubCount h ell

theorem frontierRootSubCount_eq_of_two_le {h ell : Nat} (hL : 2 ≤ ell) :
    frontierRootSubCount h ell = frontierSubCount h ell := by
  unfold frontierRootSubCount
  simp [show ell ≠ 1 by omega]

def windowConv (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | remW + 1, u => f u + (if u = 0 then 0 else windowConv f remW (u - 1))

def frontierDecCount (w : Nat) : Nat → Nat → Nat
  | 0, u => if u = 0 then 1 else 0
  | k + 1, u => windowConv (frontierDecCount w k) w u

/-- Horner base-`B` polynomial evaluation (Kronecker substitution) for `O(1)` GMP `decide +kernel`
    evaluation of `frontierSubCount` and `frontierDecCount` without `let`-duplication blowup. -/
def polyEvalB (B : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + B * polyEvalB B cs

private theorem mem_le_sum : ∀ {xs : List Nat} {c : Nat}, c ∈ xs → c ≤ xs.sum
  | _ :: _, _, .head _ => by simp [List.sum_cons]
  | a :: xs, c, .tail _ h => by
    have ih := mem_le_sum h
    simp only [List.sum_cons]; omega

private theorem polyEvalB_div_mod (B : Nat) (hB : 0 < B) :
    ∀ (cs : List Nat) (i : Nat), (∀ c ∈ cs, c < B) →
      (polyEvalB B cs / B ^ i) % B = cs.getD i 0
  | [], i, _ => by simp [polyEvalB]
  | c :: cs, 0, hLt => by
    have hc : c < B := hLt c (.head cs)
    dsimp only [polyEvalB, List.getD, List.getElem?_cons_zero, Option.getD_some]
    rw [Nat.pow_zero, Nat.div_one, Nat.mul_comm B, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  | c :: cs, i + 1, hLt => by
    have hc : c < B := hLt c (.head cs)
    dsimp only [polyEvalB, List.getD, List.getElem?_cons_succ]
    have hPow : B ^ (i + 1) = B * B ^ i := by rw [Nat.pow_succ, Nat.mul_comm]
    have hDivB : (c + B * polyEvalB B cs) / B = polyEvalB B cs := by
      rw [Nat.mul_comm B, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hc, Nat.zero_add]
    rw [hPow, ← Nat.div_div_eq_div_mul, hDivB]
    exact polyEvalB_div_mod B hB cs i (fun x hx => hLt x (.tail c hx))

def addListNat : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addListNat xs ys

private theorem polyEvalB_addListNat (B : Nat) :
    ∀ (xs ys : List Nat), polyEvalB B (addListNat xs ys) = polyEvalB B xs + polyEvalB B ys
  | [], ys => by unfold addListNat polyEvalB; rw [Nat.zero_add]
  | _ :: _, [] => (Nat.add_zero _).symm
  | x :: xs, y :: ys => by
    simp only [addListNat, polyEvalB, polyEvalB_addListNat B xs ys, Nat.mul_add]; omega

private theorem getD_addListNat :
    ∀ (xs ys : List Nat) (i : Nat), (addListNat xs ys).getD i 0 = xs.getD i 0 + ys.getD i 0
  | [], ys, i => by
    have h0 : ([] : List Nat).getD i 0 = 0 := rfl
    unfold addListNat; rw [h0, Nat.zero_add]
  | _ :: _, [], _ => (Nat.add_zero _).symm
  | x :: xs, y :: ys, 0 => rfl
  | x :: xs, y :: ys, i + 1 => getD_addListNat xs ys i

private theorem sum_addListNat :
    ∀ (xs ys : List Nat), (addListNat xs ys).sum = xs.sum + ys.sum
  | [], ys => by unfold addListNat; exact (Nat.zero_add _).symm
  | _ :: _, [] => (Nat.add_zero _).symm
  | x :: xs, y :: ys => by simp only [addListNat, List.sum_cons, sum_addListNat xs ys]; omega

def mulOnesList : Nat → List Nat → List Nat
  | 0, _ => []
  | m + 1, cs => addListNat cs (0 :: mulOnesList m cs)

private theorem polyEvalB_mulOnesList (B : Nat) :
    ∀ (w : Nat) (cs : List Nat),
      polyEvalB B (mulOnesList w cs) = polyEvalB B (List.replicate w 1) * polyEvalB B cs
  | 0, _ => by simp [mulOnesList, polyEvalB]
  | m + 1, cs => by
    simp only [mulOnesList, List.replicate_succ, polyEvalB_addListNat, polyEvalB,
      polyEvalB_mulOnesList B m cs, Nat.zero_add]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

private theorem onesPoly_geom (B : Nat) (hB1 : 1 ≤ B) :
    ∀ w : Nat, (B - 1) * polyEvalB B (List.replicate w 1) + 1 = B ^ w
  | 0 => by show (B - 1) * 0 + 1 = 1; rw [Nat.mul_zero, Nat.zero_add]
  | m + 1 => by
    have ih := onesPoly_geom B hB1 m
    simp only [List.replicate_succ, polyEvalB, Nat.mul_add, Nat.mul_one]
    have hSub : B - 1 + 1 = B := by omega
    have hRearr : (B - 1) + (B - 1) * (B * polyEvalB B (List.replicate m 1)) + 1 =
        (B - 1 + 1) + B * ((B - 1) * polyEvalB B (List.replicate m 1)) := by
      rw [Nat.mul_left_comm (B - 1) B]; omega
    rw [hRearr, hSub]
    have hMul := congrArg (B * ·) ih
    simp only [Nat.mul_add, Nat.mul_one] at hMul
    rw [Nat.pow_succ, Nat.mul_comm (B ^ m) B]; omega

private theorem onesPoly_eq_div (B w : Nat) (hB2 : 2 ≤ B) :
    polyEvalB B (List.replicate w 1) = (B ^ w - 1) / (B - 1) := by
  have hG := onesPoly_geom B (by omega) w
  have hSub : B ^ w - 1 = polyEvalB B (List.replicate w 1) * (B - 1) := by
    rw [Nat.mul_comm]; omega
  rw [hSub, Nat.mul_div_cancel _ (by omega)]

private theorem getD_mulOnesList (cs : List Nat) :
    ∀ (w u : Nat), (mulOnesList w cs).getD u 0 = windowConv (cs.getD · 0) w u
  | 0, _ => rfl
  | m + 1, 0 => by rw [mulOnesList, getD_addListNat]; exact Nat.add_zero _
  | m + 1, u + 1 => by
    rw [mulOnesList, getD_addListNat]
    simp only [windowConv, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact congrArg (cs.getD (u + 1) 0 + ·) (getD_mulOnesList cs m u)

private theorem windowConv_congr (f g : Nat → Nat) :
    (∀ x, f x = g x) → ∀ (w u : Nat), windowConv f w u = windowConv g w u
  | _, 0, _ => rfl
  | hfg, m + 1, u => by
    unfold windowConv
    rw [hfg u]
    if hu : u = 0 then
      rw [hu]; rfl
    else
      simp only [hu, ↓reduceIte, windowConv_congr f g hfg m (u - 1)]

private theorem sum_mulOnesList (cs : List Nat) :
    ∀ w : Nat, (mulOnesList w cs).sum = w * cs.sum
  | 0 => (Nat.zero_mul _).symm
  | m + 1 => by
    simp only [mulOnesList, sum_addListNat, List.sum_cons, Nat.zero_add, sum_mulOnesList cs m, Nat.succ_mul]
    omega

def decList (w : Nat) : Nat → List Nat
  | 0 => [1]
  | k + 1 => mulOnesList w (decList w k)

private theorem decList_spec (B w : Nat) (hB2 : 2 ≤ B) :
    ∀ k : Nat,
      polyEvalB B (decList w k) = ((B ^ w - 1) / (B - 1)) ^ k ∧
      (decList w k).sum = w ^ k ∧
      (∀ u, (decList w k).getD u 0 = frontierDecCount w k u)
  | 0 => ⟨by show 1 + B * 0 = 1; rw [Nat.mul_zero, Nat.add_zero], rfl, fun u => by cases u <;> rfl⟩
  | k + 1 => by
    obtain ⟨hEv, hSm, hGet⟩ := decList_spec B w hB2 k
    refine ⟨?_, ?_, ?_⟩
    · rw [decList, polyEvalB_mulOnesList, onesPoly_eq_div B w hB2, hEv, Nat.pow_succ, Nat.mul_comm]
    · rw [decList, sum_mulOnesList, hSm, Nat.pow_succ, Nat.mul_comm]
    · intro u
      rw [decList, getD_mulOnesList, frontierDecCount]
      exact windowConv_congr _ _ hGet w u

def convListNat : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, bs => addListNat (bs.map (a * ·)) (0 :: convListNat as bs)

private theorem polyEvalB_map_mul (B a : Nat) :
    ∀ bs : List Nat, polyEvalB B (bs.map (a * ·)) = a * polyEvalB B bs
  | [] => by simp [polyEvalB]
  | b :: bs => by
    simp only [List.map_cons, polyEvalB, polyEvalB_map_mul B a bs, Nat.mul_add]
    rw [Nat.mul_left_comm a B]

private theorem polyEvalB_convListNat (B : Nat) :
    ∀ (xs ys : List Nat), polyEvalB B (convListNat xs ys) = polyEvalB B xs * polyEvalB B ys
  | [], _ => by simp [convListNat, polyEvalB]
  | a :: as, ys => by
    simp only [convListNat, polyEvalB_addListNat, polyEvalB_map_mul, polyEvalB,
      polyEvalB_convListNat B as ys, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc]

private theorem sum_map_mul (a : Nat) :
    ∀ bs : List Nat, (bs.map (a * ·)).sum = a * bs.sum
  | [] => by simp
  | b :: bs => by simp only [List.map_cons, List.sum_cons, sum_map_mul a bs, Nat.mul_add]

private theorem sum_convListNat :
    ∀ (xs ys : List Nat), (convListNat xs ys).sum = xs.sum * ys.sum
  | [], _ => by simp [convListNat]
  | a :: as, ys => by
    simp only [convListNat, sum_addListNat, sum_map_mul, List.sum_cons, Nat.zero_add,
      sum_convListNat as ys, Nat.add_mul]

def fullConvAt : List Nat → (Nat → Nat) → Nat → Nat
  | [], _, _ => 0
  | a :: _, g, 0 => a * g 0
  | a :: as, g, n + 1 => a * g (n + 1) + fullConvAt as g n

private theorem getD_map_mul (a : Nat) :
    ∀ (bs : List Nat) (n : Nat), (bs.map (a * ·)).getD n 0 = a * bs.getD n 0
  | [], _ => (Nat.mul_zero a).symm
  | _ :: _, 0 => rfl
  | _ :: bs, n + 1 => getD_map_mul a bs n

private theorem getD_convListNat :
    ∀ (xs ys : List Nat) (n : Nat), (convListNat xs ys).getD n 0 = fullConvAt xs (ys.getD · 0) n
  | [], _, _ => rfl
  | a :: _, ys, 0 => by rw [convListNat, getD_addListNat, getD_map_mul]; exact Nat.add_zero _
  | a :: as, ys, n + 1 => by
    rw [convListNat, getD_addListNat, getD_map_mul]
    exact congrArg (a * ys.getD (n + 1) 0 + ·) (getD_convListNat as ys n)

private theorem fullConvAt_eq_splitConvFrom (f : Nat → Nat) (hf0 : f 0 = 0) (ell : Nat) :
    ∀ (rem : Nat) (zs : List Nat) (cur : Nat),
      cur + rem = ell → (∀ i, zs.getD i 0 = f (cur + i)) →
      fullConvAt zs f rem = splitConvFrom f ell cur rem
  | 0, zs, _, _, _ => by
    cases zs with
    | nil => rfl
    | cons z _ => unfold fullConvAt splitConvFrom; rw [hf0, Nat.mul_zero]
  | r + 1, [], cur, hEq, hZ => by
    have hfCur : f cur = 0 := by simpa using (hZ 0).symm
    have ih := fullConvAt_eq_splitConvFrom f hf0 ell r [] (cur + 1) (by omega)
      (fun i => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hZ (i + 1))
    unfold fullConvAt splitConvFrom
    rw [hfCur, Nat.zero_mul, Nat.zero_add, ← ih]; rfl
  | r + 1, z :: zs, cur, hEq, hZ => by
    have hz : z = f cur := by simpa [List.getD] using hZ 0
    have hSub : r + 1 = ell - cur := by omega
    have ih := fullConvAt_eq_splitConvFrom f hf0 ell r zs (cur + 1) (by omega)
      (fun i => by simpa [List.getD, Nat.add_assoc, Nat.add_comm 1 i] using hZ (i + 1))
    unfold fullConvAt splitConvFrom
    rw [hz, hSub, ih]

def subList : Nat → List Nat
  | 0 => [0, 1]
  | t + 1 => addListNat [0, 1] (convListNat (subList t) (subList t))

def kronSubEval (B : Nat) : Nat → Nat
  | 0 => B
  | t + 1 => B + (kronSubEval B t) ^ 2

def subTotalSum : Nat → Nat
  | 0 => 1
  | t + 1 => 1 + (subTotalSum t) ^ 2

private theorem subList_spec (B : Nat) :
    ∀ t : Nat,
      polyEvalB B (subList t) = kronSubEval B t ∧
      (subList t).sum = subTotalSum t ∧
      (∀ ell, (subList t).getD ell 0 = frontierSubCount t ell)
  | 0 => ⟨by show 0 + B * (1 + B * 0) = B; rw [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.zero_add],
      rfl, fun ell => by
        cases ell with
        | zero => rfl
        | succ m => cases m <;> rfl⟩
  | t + 1 => by
    obtain ⟨hEv, hSm, hGet⟩ := subList_spec B t
    have hf0 : frontierSubCount t 0 = 0 := by cases t <;> rfl
    refine ⟨?_, ?_, ?_⟩
    · simp only [subList, kronSubEval, polyEvalB_addListNat, polyEvalB_convListNat, hEv, polyEvalB,
        Nat.zero_add, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.pow_two]
    · simp only [subList, subTotalSum, sum_addListNat, sum_convListNat, hSm, List.sum_cons,
        List.sum_nil, Nat.zero_add, Nat.add_zero, Nat.pow_two]
    · intro ell
      rw [subList, getD_addListNat, getD_convListNat]
      have hSubHd : ∃ as, subList t = 0 :: as ∧ ∀ i, as.getD i 0 = frontierSubCount t (1 + i) := by
        cases hSL : subList t with
        | nil =>
          have h1 := hGet 1
          rw [hSL] at h1
          cases t <;> simp [frontierSubCount] at h1
        | cons a0 as =>
          have ha0 : a0 = 0 := by
            have h0 := hGet 0; rw [hSL] at h0; simpa [List.getD, hf0] using h0
          subst ha0
          exact ⟨as, rfl, fun i => by
            have hi := hGet (1 + i); rw [hSL] at hi; simpa [List.getD, Nat.add_comm 1 i] using hi⟩
      obtain ⟨as, hEqSL, hAs⟩ := hSubHd
      have hFullCongr : ∀ zs m, fullConvAt zs (fun i => (subList t).getD i 0) m = fullConvAt zs (frontierSubCount t) m := by
        intro zs m; induction zs generalizing m with
        | nil => rfl
        | cons z zs ih => cases m with
          | zero => unfold fullConvAt; dsimp only; rw [hGet 0]
          | succ r => unfold fullConvAt; dsimp only; rw [hGet (r + 1), ih r]
      rw [hFullCongr, hEqSL]
      cases ell with
      | zero =>
        change 0 + 0 * frontierSubCount t 0 = 0
        rw [Nat.zero_mul]
      | succ m =>
        cases m with
        | zero =>
          have ha0 : fullConvAt as (frontierSubCount t) 0 = 0 := by
            cases as with
            | nil => rfl
            | cons a _ => unfold fullConvAt; rw [hf0, Nat.mul_zero]
          have hL01 : ([0, 1] : List Nat).getD 1 0 = 1 := rfl
          have hFC1 : fullConvAt (0 :: as) (frontierSubCount t) 1 = 0 := by
            unfold fullConvAt; rw [Nat.zero_mul, Nat.zero_add, ha0]
          rw [hL01, hFC1]; rfl
        | succ r =>
          have hSp := fullConvAt_eq_splitConvFrom (frontierSubCount t) hf0 (r + 2) (r + 1) as 1 (by omega) hAs
          have h01 : ([0, 1] : List Nat).getD (r + 2) 0 = 0 := rfl
          rw [h01, Nat.zero_add]
          unfold fullConvAt frontierSubCount
          rw [Nat.zero_mul, Nat.zero_add]
          simp only [Nat.succ_ne_zero, ↓reduceIte, show r + 2 ≠ 1 by omega, Nat.add_sub_cancel]
          exact hSp

@[expose] def frontierTotalCardFast (p : FrontierFtsParams) : Nat :=
  let B := 2 ^ 256
  (if p.frontierLen = 1 then 0 else (kronSubEval B p.treeHeight / B ^ p.frontierLen) % B) *
  ((((B ^ p.winternitzW - 1) / (B - 1)) ^ p.frontierLen / B ^ p.targetSum) % B)

theorem frontierTotalCardFast_eq_spec
    (p : FrontierFtsParams)
    (hSubBnd : subTotalSum p.treeHeight < 2 ^ 256)
    (hDecBnd : p.winternitzW ^ p.frontierLen < 2 ^ 256) :
    frontierTotalCardFast p =
      frontierRootSubCount p.treeHeight p.frontierLen *
        frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
  let B := 2 ^ 256
  have hB0 : 0 < B := by decide +kernel
  have hB2 : 2 ≤ B := by decide +kernel
  obtain ⟨hSubEv, hSubSm, hSubGet⟩ := subList_spec B p.treeHeight
  obtain ⟨hDecEv, hDecSm, hDecGet⟩ := decList_spec B p.winternitzW hB2 p.frontierLen
  have hSubDig : (kronSubEval B p.treeHeight / B ^ p.frontierLen) % B = frontierSubCount p.treeHeight p.frontierLen := by
    rw [← hSubEv, polyEvalB_div_mod B hB0 _ p.frontierLen
      (fun c hc => Nat.lt_of_le_of_lt (mem_le_sum hc) (hSubSm ▸ hSubBnd)), hSubGet]
  have hDecDig : (((B ^ p.winternitzW - 1) / (B - 1)) ^ p.frontierLen / B ^ p.targetSum) % B =
      frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
    rw [← hDecEv, polyEvalB_div_mod B hB0 _ p.targetSum
      (fun c hc => Nat.lt_of_le_of_lt (mem_le_sum hc) (hDecSm ▸ hDecBnd)), hDecGet]
  change (if p.frontierLen = 1 then 0 else (kronSubEval B p.treeHeight / B ^ p.frontierLen) % B) *
    ((((B ^ p.winternitzW - 1) / (B - 1)) ^ p.frontierLen / B ^ p.targetSum) % B) =
    (if p.frontierLen = 1 then 0 else frontierSubCount p.treeHeight p.frontierLen) *
      frontierDecCount p.winternitzW p.frontierLen p.targetSum
  rw [hSubDig, hDecDig]

theorem compact1122_rank_domain_gt_2pow256 :
    compact1122Params.signatureBytes = 1122 ∧
    compact1122Params.signatureBytes + 96 ≤ 1232 ∧
    compact1122Params.rotatedEpochVoteBytes = 1194 ∧
    full256BitParams.signatureBytes = 2338 ∧
    2 ^ 263 < frontierRootSubCount compact1122Params.treeHeight compact1122Params.frontierLen *
                frontierDecCount compact1122Params.winternitzW compact1122Params.frontierLen compact1122Params.targetSum ∧
    frontierRootSubCount compact1122Params.treeHeight compact1122Params.frontierLen *
      frontierDecCount compact1122Params.winternitzW compact1122Params.frontierLen compact1122Params.targetSum < 2 ^ 264 ∧
    2 ^ 256 < frontierRootSubCount compact1122Params.treeHeight compact1122Params.frontierLen *
                frontierDecCount compact1122Params.winternitzW compact1122Params.frontierLen compact1122Params.targetSum ∧
    2 ^ 256 < frontierRootSubCount full256BitParams.treeHeight full256BitParams.frontierLen *
                frontierDecCount full256BitParams.winternitzW full256BitParams.frontierLen full256BitParams.targetSum ∧
    (∀ d₁ d₂ : BitVec 256,
      d₁.toNat < frontierRootSubCount compact1122Params.treeHeight compact1122Params.frontierLen *
                   frontierDecCount compact1122Params.winternitzW compact1122Params.frontierLen compact1122Params.targetSum ∧
      (d₁.toNat = d₂.toNat → d₁ = d₂)) := by
  have hBounds :
      2 ^ 263 < frontierTotalCardFast compact1122Params ∧
      frontierTotalCardFast compact1122Params < 2 ^ 264 ∧
      2 ^ 256 < frontierTotalCardFast full256BitParams := by decide +kernel
  have hSubC : subTotalSum compact1122Params.treeHeight < 2 ^ 256 := by decide +kernel
  have hDecC : compact1122Params.winternitzW ^ compact1122Params.frontierLen < 2 ^ 256 := by decide +kernel
  have hSubF : subTotalSum full256BitParams.treeHeight < 2 ^ 256 := by decide +kernel
  have hDecF : full256BitParams.winternitzW ^ full256BitParams.frontierLen < 2 ^ 256 := by decide +kernel
  have hEqC := frontierTotalCardFast_eq_spec compact1122Params hSubC hDecC
  have hEqF := frontierTotalCardFast_eq_spec full256BitParams hSubF hDecF
  have hLoC := Nat.lt_of_lt_of_eq hBounds.1 hEqC
  have hHiC := hEqC ▸ hBounds.2.1
  have hLoF := Nat.lt_of_lt_of_eq hBounds.2.2 hEqF
  have h256 := Nat.lt_trans (by decide +kernel : 2 ^ 256 < 2 ^ 263) hLoC
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    hLoC, hHiC, h256, hLoF,
    fun d₁ _ => ⟨Nat.lt_trans d₁.isLt h256, BitVec.eq_of_toNat_eq⟩⟩

/-! ### Prefix-Free Binary-Tree Antichain & Bijective Unrank / Rank -/

inductive AntichainTree : Type where
  | leaf : AntichainTree
  | split : AntichainTree → AntichainTree → AntichainTree
  deriving DecidableEq, Repr

def AntichainTree.size : AntichainTree → Nat
  | .leaf => 1
  | .split l r => l.size + r.size

theorem AntichainTree.size_pos : ∀ tr : AntichainTree, 1 ≤ tr.size
  | .leaf => Nat.le_refl 1
  | .split l r => by
    have hl := l.size_pos
    have hr := r.size_pos
    unfold AntichainTree.size; omega

def AntichainTree.Valid : Nat → AntichainTree → Bool
  | 0, .leaf => true
  | 0, .split _ _ => false
  | _ + 1, .leaf => true
  | t + 1, .split l r => l.Valid t && r.Valid t

def AntichainTree.frontierNodes (v : Nat) : AntichainTree → List Nat
  | .leaf => [v]
  | .split l r => l.frontierNodes (2 * v) ++ r.frontierNodes (2 * v + 1)

theorem AntichainTree.frontierNodes_length :
    ∀ (tr : AntichainTree) (v : Nat), (tr.frontierNodes v).length = tr.size
  | .leaf, _ => rfl
  | .split l r, v => by
    simp [AntichainTree.frontierNodes, AntichainTree.size,
      l.frontierNodes_length (2 * v), r.frontierNodes_length (2 * v + 1)]

def collapseTreeStack (v : Nat) (tr : AntichainTree) : List (Nat × AntichainTree) → List (Nat × AntichainTree)
  | [] => [(v, tr)]
  | (lv, ltr) :: rest =>
    if lv % 2 = 0 ∧ v = lv + 1 then collapseTreeStack (lv / 2) (.split ltr tr) rest else (v, tr) :: (lv, ltr) :: rest

def parseFrontierNodes : List Nat → List (Nat × AntichainTree) → List (Nat × AntichainTree)
  | [], st => st
  | v :: vs, st => parseFrontierNodes vs (collapseTreeStack v .leaf st)

private theorem parseFrontierNodes_append :
    ∀ (tr : AntichainTree) (v : Nat) (rest : List Nat) (st : List (Nat × AntichainTree)),
      0 < v → parseFrontierNodes (tr.frontierNodes v ++ rest) st = parseFrontierNodes rest (collapseTreeStack v tr st)
  | .leaf, _, _, _, _ => rfl
  | .split l r, v, rest, st, hv => by
    simp only [AntichainTree.frontierNodes, List.append_assoc, parseFrontierNodes_append l (2 * v) _ st (by omega)]
    have hL : collapseTreeStack (2 * v) l st = (2 * v, l) :: st := by
      cases st with
      | nil => rfl
      | cons hd _ => unfold collapseTreeStack; simp [show ¬ (hd.1 % 2 = 0 ∧ 2 * v = hd.1 + 1) by rintro ⟨_, _⟩; omega]
    have hR : collapseTreeStack (2 * v + 1) r ((2 * v, l) :: st) = collapseTreeStack v (.split l r) st := by
      conv => lhs; unfold collapseTreeStack
      simp [show (2 * v) % 2 = 0 ∧ 2 * v + 1 = 2 * v + 1 from ⟨by omega, rfl⟩, show (2 * v) / 2 = v by omega]
    rw [hL, parseFrontierNodes_append r (2 * v + 1) rest _ (by omega), hR]

theorem frontierNodes_injective_root (tr₁ tr₂ : AntichainTree)
    (hEq : tr₁.frontierNodes 1 = tr₂.frontierNodes 1) : tr₁ = tr₂ := by
  have h := congrArg (fun ns => parseFrontierNodes ns [])
    (by simpa using hEq : tr₁.frontierNodes 1 ++ [] = tr₂.frontierNodes 1 ++ [])
  rw [parseFrontierNodes_append tr₁ 1 [] [] (by decide), parseFrontierNodes_append tr₂ 1 [] [] (by decide)] at h
  simpa [parseFrontierNodes, collapseTreeStack] using h

def unrankSplitChoice (t ell cur : Nat) : (rem r : Nat) → Option (Nat × Nat × Nat)
  | 0, _ => none
  | rem + 1, r =>
    let rCnt := frontierSubCount t (ell - cur)
    let bkt := frontierSubCount t cur * rCnt
    if r < bkt then some (cur, r / rCnt, r % rCnt) else unrankSplitChoice t ell (cur + 1) rem (r - bkt)

def unrankSubtree : (t ell r : Nat) → Option AntichainTree
  | 0, ell, r => if ell = 1 ∧ r = 0 then some .leaf else none
  | t + 1, ell, r =>
    if ell = 0 then none else if ell = 1 then (if r = 0 then some .leaf else none)
    else match unrankSplitChoice t ell 1 (ell - 1) r with
      | none => none
      | some (leftSz, rL, rR) =>
        match unrankSubtree t leftSz rL, unrankSubtree t (ell - leftSz) rR with
        | some l, some rt => some (.split l rt) | _, _ => none

def rankSplitPrefix (t ell cur target : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => if cur < target then frontierSubCount t cur * frontierSubCount t (ell - cur) +
      rankSplitPrefix t ell (cur + 1) target rem else 0

def rankSubtree : Nat → AntichainTree → Nat
  | 0, _ => 0
  | _ + 1, .leaf => 0
  | t + 1, .split l rt =>
    let ell := l.size + rt.size
    rankSplitPrefix t ell 1 l.size (ell - 1) + rankSubtree t l * frontierSubCount t rt.size + rankSubtree t rt

private theorem ite_true_eq {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem ite_false_eq {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  cases ‹Decidable c› with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem unrankSplitChoice_spec (t ell : Nat) :
    ∀ (cur rem r : Nat), r < splitConvFrom (frontierSubCount t) ell cur rem →
      ∃ leftSz rL rR, unrankSplitChoice t ell cur rem r = some (leftSz, rL, rR) ∧
        cur ≤ leftSz ∧ leftSz < cur + rem ∧ rL < frontierSubCount t leftSz ∧
        rR < frontierSubCount t (ell - leftSz) ∧
        rankSplitPrefix t ell cur leftSz rem + rL * frontierSubCount t (ell - leftSz) + rR = r
  | _, 0, _, hLt => nomatch hLt
  | cur, rem + 1, r, hLt => by
    unfold splitConvFrom at hLt
    if hB : r < frontierSubCount t cur * frontierSubCount t (ell - cur) then
      have hrPos : 0 < frontierSubCount t (ell - cur) := by
        cases hRC : frontierSubCount t (ell - cur) with
        | zero => rw [hRC, Nat.mul_zero] at hB; nomatch hB
        | succ m => exact Nat.zero_lt_succ m
      have hDM : (r / frontierSubCount t (ell - cur)) * frontierSubCount t (ell - cur) +
          r % frontierSubCount t (ell - cur) = r := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod r _
      refine ⟨cur, r / frontierSubCount t (ell - cur), r % frontierSubCount t (ell - cur),
        by unfold unrankSplitChoice; dsimp only; rw [ite_true_eq hB], Nat.le_refl _, by omega,
        (Nat.div_lt_iff_lt_mul hrPos).mpr hB, Nat.mod_lt r hrPos, ?_⟩
      unfold rankSplitPrefix
      rw [ite_false_eq (Nat.lt_irrefl cur), Nat.zero_add]
      exact hDM
    else
      obtain ⟨lsz, rL, rR, hRec, hGe, hUp, hrL, hrR, hRk⟩ :=
        unrankSplitChoice_spec t ell (cur + 1) rem
          (r - frontierSubCount t cur * frontierSubCount t (ell - cur)) (by omega)
      refine ⟨lsz, rL, rR,
        by unfold unrankSplitChoice; dsimp only; rw [ite_false_eq hB]; exact hRec,
        by omega, by omega, hrL, hrR, ?_⟩
      unfold rankSplitPrefix
      rw [ite_true_eq (show cur < lsz by omega)]
      omega

theorem rankSubtree_unrankSubtree :
    ∀ (t ell r : Nat), r < frontierSubCount t ell →
      ∃ tr : AntichainTree, unrankSubtree t ell r = some tr ∧ tr.Valid t = true ∧ tr.size = ell ∧ rankSubtree t tr = r
  | 0, ell, r, hLt => by
    unfold frontierSubCount at hLt
    if h1 : ell = 1 then
      subst h1; rw [ite_true_eq rfl] at hLt; have hr0 : r = 0 := by omega
      subst hr0; exact ⟨.leaf, rfl, rfl, rfl, rfl⟩
    else
      rw [ite_false_eq h1] at hLt; nomatch hLt
  | t + 1, ell, r, hLt => by
    unfold frontierSubCount at hLt
    if h0 : ell = 0 then
      rw [ite_true_eq h0] at hLt; nomatch hLt
    else if h1 : ell = 1 then
      subst h1; rw [ite_false_eq h0, ite_true_eq rfl] at hLt; have hr0 : r = 0 := by omega
      subst hr0; exact ⟨.leaf, rfl, rfl, rfl, rfl⟩
    else
      rw [ite_false_eq h0, ite_false_eq h1] at hLt
      obtain ⟨lsz, rL, rR, hSp, _, _, hrL, hrR, hRk⟩ := unrankSplitChoice_spec t ell 1 (ell - 1) r hLt
      obtain ⟨l, hUl, hVl, hSl, hRl⟩ := rankSubtree_unrankSubtree t lsz rL hrL
      obtain ⟨rt, hUr, hVr, hSr, hRr⟩ := rankSubtree_unrankSubtree t (ell - lsz) rR hrR
      have hEll : l.size + rt.size = ell := by rw [hSl, hSr]; omega
      refine ⟨.split l rt, ?_, ?_, hEll, ?_⟩
      · unfold unrankSubtree; rw [ite_false_eq h0, ite_false_eq h1, hSp]; dsimp only; rw [hUl, hUr]
      · unfold AntichainTree.Valid; rw [hVl, hVr]; rfl
      · unfold rankSubtree; dsimp only; rw [hEll, hSl, hSr, hRl, hRr]; exact hRk

def unrankWindowDigit (w k : Nat) : (remW u baseA r : Nat) → Option (Nat × Nat)
  | 0, _, _, _ => none
  | remW + 1, u, baseA, r =>
    let bkt := frontierDecCount w k u
    if r < bkt then some (baseA, r) else if u = 0 then none
    else unrankWindowDigit w k remW (u - 1) (baseA + 1) (r - bkt)

def unrankDecorations (w : Nat) : (k u r : Nat) → Option (List Nat)
  | 0, u, r => if u = 0 ∧ r = 0 then some [] else none
  | k + 1, u, r =>
    match unrankWindowDigit w k w u 0 r with
    | none => none
    | some (a, rSub) => (unrankDecorations w k (u - a) rSub).map (a :: ·)

def rankWindowPrefix (w k : Nat) : (remW u target : Nat) → Nat
  | 0, _, _ => 0
  | _ + 1, _, 0 => 0
  | remW + 1, u, target + 1 =>
    frontierDecCount w k u + (if u = 0 then 0 else rankWindowPrefix w k remW (u - 1) target)

def rankDecorations (w : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | a :: rest, u => rankWindowPrefix w rest.length w u a + rankDecorations w rest (u - a)

private theorem unrankWindowDigit_spec (w k : Nat) :
    ∀ (remW u baseA r : Nat), r < windowConv (frontierDecCount w k) remW u →
      ∃ aOff rSub, unrankWindowDigit w k remW u baseA r = some (baseA + aOff, rSub) ∧
        aOff < remW ∧ aOff ≤ u ∧ rSub < frontierDecCount w k (u - aOff) ∧ rankWindowPrefix w k remW u aOff + rSub = r
  | 0, _, _, _, hLt => nomatch hLt
  | remW + 1, u, baseA, r, hLt => by
    unfold windowConv at hLt
    if hB : r < frontierDecCount w k u then
      exact ⟨0, r,
        by unfold unrankWindowDigit; dsimp only; rw [ite_true_eq hB, Nat.add_zero],
        Nat.zero_lt_succ _, Nat.zero_le _, by rw [Nat.sub_zero]; exact hB,
        by unfold rankWindowPrefix; exact Nat.zero_add r⟩
    else if hu0 : u = 0 then
      rw [ite_true_eq hu0, Nat.add_zero] at hLt; exact False.elim (hB hLt)
    else
      rw [ite_false_eq hu0] at hLt
      obtain ⟨aOff, rSub, hRec, hLtW, hLeU, hrS, hRk⟩ :=
        unrankWindowDigit_spec w k remW (u - 1) (baseA + 1) (r - frontierDecCount w k u) (by omega)
      refine ⟨aOff + 1, rSub, ?_, Nat.succ_lt_succ hLtW, by omega,
        (show u - 1 - aOff = u - (aOff + 1) by omega) ▸ hrS, ?_⟩
      · unfold unrankWindowDigit; dsimp only; rw [ite_false_eq hB, ite_false_eq hu0]
        exact (show baseA + 1 + aOff = baseA + (aOff + 1) by omega) ▸ hRec
      · unfold rankWindowPrefix; rw [ite_false_eq hu0]; omega

theorem rankDecorations_unrankDecorations (w : Nat) :
    ∀ (k u r : Nat), r < frontierDecCount w k u →
      ∃ offs : List Nat, unrankDecorations w k u r = some offs ∧
        offs.length = k ∧ offs.sum = u ∧ (∀ a ∈ offs, a < w) ∧ rankDecorations w offs u = r
  | 0, u, r, hLt => by
    unfold frontierDecCount at hLt
    if hu0 : u = 0 then
      subst hu0; rw [ite_true_eq rfl] at hLt; have hr0 : r = 0 := by omega
      subst hr0
      refine ⟨[], rfl, rfl, rfl, ?_, rfl⟩
      intro _ h; cases h
    else
      rw [ite_false_eq hu0] at hLt; nomatch hLt
  | k + 1, u, r, hLt => by
    unfold frontierDecCount at hLt
    obtain ⟨a, rSub, hDig, haW, haU, hrSub, hRkW⟩ := unrankWindowDigit_spec w k w u 0 r hLt
    rw [Nat.zero_add] at hDig
    obtain ⟨rest, hRest, hLen, hSum, hBnd, hRkRest⟩ := rankDecorations_unrankDecorations w k (u - a) rSub hrSub
    refine ⟨a :: rest,
      by unfold unrankDecorations; rw [hDig]; dsimp only; rw [hRest]; rfl,
      congrArg Nat.succ hLen,
      by rw [List.sum_cons, hSum]; omega,
      ?_,
      by unfold rankDecorations; rw [hLen, hRkRest]; omega⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | htl
    · exact haW
    · exact hBnd x htl

def unrankFrontierFts (p : FrontierFtsParams) (rank : Nat) : Option (AntichainTree × List Nat × List Nat) :=
  let dCard := frontierDecCount p.winternitzW p.frontierLen p.targetSum
  let fCard := frontierRootSubCount p.treeHeight p.frontierLen
  if rank < fCard * dCard then
    match unrankSubtree p.treeHeight p.frontierLen (rank / dCard),
          unrankDecorations p.winternitzW p.frontierLen p.targetSum (rank % dCard) with
    | some tr, some offs => some (tr, tr.frontierNodes 1, offs)
    | _, _ => none
  else none

def rankFrontierFts (p : FrontierFtsParams) (tr : AntichainTree) (offs : List Nat) : Nat :=
  rankSubtree p.treeHeight tr * frontierDecCount p.winternitzW p.frontierLen p.targetSum +
  rankDecorations p.winternitzW offs p.targetSum

private theorem unrankFrontierFts_rank_lt {p : FrontierFtsParams} {r : Nat}
    {tr : AntichainTree} {paths offs : List Nat}
    (h : unrankFrontierFts p r = some (tr, paths, offs)) :
    r < frontierRootSubCount p.treeHeight p.frontierLen *
        frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
  unfold unrankFrontierFts at h
  dsimp only at h
  if hLt : r < frontierRootSubCount p.treeHeight p.frontierLen *
      frontierDecCount p.winternitzW p.frontierLen p.targetSum then
    exact hLt
  else
    rw [ite_false_eq hLt] at h; cases h

theorem unrankFrontierFts_bijective (p : FrontierFtsParams) (rank : Nat)
    (hLt : rank < frontierRootSubCount p.treeHeight p.frontierLen *
                  frontierDecCount p.winternitzW p.frontierLen p.targetSum) :
    ∃ tr paths offs, unrankFrontierFts p rank = some (tr, paths, offs) ∧
      paths = tr.frontierNodes 1 ∧ tr.Valid p.treeHeight = true ∧ tr.size = p.frontierLen ∧
      2 ≤ p.frontierLen ∧
      offs.length = p.frontierLen ∧ offs.sum = p.targetSum ∧
      (∀ a ∈ offs, a < p.winternitzW) ∧ rankFrontierFts p tr offs = rank := by
  have hdPos : 0 < frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
    cases hD : frontierDecCount p.winternitzW p.frontierLen p.targetSum with
    | zero => rw [hD, Nat.mul_zero] at hLt; nomatch hLt
    | succ m => exact Nat.zero_lt_succ m
  have hfPos : 0 < frontierRootSubCount p.treeHeight p.frontierLen := by
    cases hF : frontierRootSubCount p.treeHeight p.frontierLen with
    | zero => rw [hF, Nat.zero_mul] at hLt; nomatch hLt
    | succ m => exact Nat.zero_lt_succ m
  have hTwoLe : 2 ≤ p.frontierLen := by
    unfold frontierRootSubCount at hfPos
    if h1 : p.frontierLen = 1 then
      rw [ite_true_eq h1] at hfPos; nomatch hfPos
    else if h0 : p.frontierLen = 0 then
      rw [ite_false_eq h1, h0] at hfPos
      cases hTH : p.treeHeight <;> rw [hTH] at hfPos <;> nomatch hfPos
    else
      omega
  have hfSubLt : rank / frontierDecCount p.winternitzW p.frontierLen p.targetSum <
      frontierSubCount p.treeHeight p.frontierLen := by
    rw [← frontierRootSubCount_eq_of_two_le hTwoLe]
    exact (Nat.div_lt_iff_lt_mul hdPos).mpr hLt
  obtain ⟨tr, hTr, hVal, hSz, hRkTr⟩ := rankSubtree_unrankSubtree p.treeHeight p.frontierLen _ hfSubLt
  obtain ⟨offs, hOffs, hLen, hSum, hBnd, hRkOff⟩ :=
    rankDecorations_unrankDecorations p.winternitzW p.frontierLen p.targetSum _ (Nat.mod_lt rank hdPos)
  exact ⟨tr, tr.frontierNodes 1, offs,
    by unfold unrankFrontierFts; dsimp only; rw [ite_true_eq hLt, hTr, hOffs],
    rfl, hVal, hSz, hTwoLe, hLen, hSum, hBnd,
    by unfold rankFrontierFts; rw [hRkTr, hRkOff, Nat.mul_comm (rank / _) _]; exact Nat.div_add_mod rank _⟩

theorem unrankFrontierFts_injective (p : FrontierFtsParams) {r₁ r₂ : Nat}
    {tr₁ tr₂ : AntichainTree} {paths₁ paths₂ offs₁ offs₂ : List Nat}
    (h₁ : unrankFrontierFts p r₁ = some (tr₁, paths₁, offs₁))
    (h₂ : unrankFrontierFts p r₂ = some (tr₂, paths₂, offs₂))
    (hSame : paths₁ = paths₂ ∧ offs₁ = offs₂) : r₁ = r₂ := by
  have hLt₁ := unrankFrontierFts_rank_lt h₁
  have hLt₂ := unrankFrontierFts_rank_lt h₂
  obtain ⟨_, _, _, hu₁, hp₁, _, _, _, _, _, _, hrk₁⟩ := unrankFrontierFts_bijective p r₁ hLt₁
  obtain ⟨_, _, _, hu₂, hp₂, _, _, _, _, _, _, hrk₂⟩ := unrankFrontierFts_bijective p r₂ hLt₂
  rw [h₁] at hu₁; injection hu₁ with e₁; obtain ⟨rfl, e₁'⟩ := Prod.mk.inj e₁; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₁'
  rw [h₂] at hu₂; injection hu₂ with e₂; obtain ⟨rfl, e₂'⟩ := Prod.mk.inj e₂; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₂'
  rw [← hrk₁, ← hrk₂, frontierNodes_injective_root tr₁ tr₂ (hp₁.symm.trans (hSame.1.trans hp₂)), hSame.2]

attribute [local irreducible] frontierSubCount frontierDecCount

/-! ### Constructive Equal-Sum Pigeonhole & `FrontierSumFts` 1-Time EUF-CMA Reduction -/

def findSmallerOffsetIdx :
    (ys xs : List Nat) → (hLen : ys.length = xs.length) → ys.sum ≤ xs.sum → ys ≠ xs →
    { idx : Fin ys.length // ys.get idx < xs.get ⟨idx.1, Nat.lt_of_lt_of_eq idx.2 hLen⟩ }
  | [], [], _, _, hNe => False.elim (hNe rfl)
  | y :: ys, x :: xs, hLen, hSum, hNe =>
    if hLt : y < x then ⟨⟨0, Nat.zero_lt_succ _⟩, hLt⟩
    else if hEq : y = x then
      let sub := findSmallerOffsetIdx ys xs (Nat.succ.inj hLen)
        (by simp [List.sum_cons, hEq] at hSum; omega) (fun hTl => hNe (by rw [hEq, hTl]))
      ⟨⟨sub.1.1 + 1, Nat.succ_lt_succ sub.1.2⟩, sub.2⟩
    else
      let sub := findSmallerOffsetIdx ys xs (Nat.succ.inj hLen)
        (by simp [List.sum_cons] at hSum; omega) (fun hTl => by simp [List.sum_cons, hTl] at hSum; omega)
      ⟨⟨sub.1.1 + 1, Nat.succ_lt_succ sub.1.2⟩, sub.2⟩

structure FrontierHashSuite where
  prehashMsg  : BitVec 256 → BitVec 256 → List UInt8 → BitVec 256
  squeezeRank : BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256 → UInt16 → BitVec 256
  prfRand     : BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256 → BitVec 256
  leafStart   : BitVec 256 → BitVec 256 → Nat → BitVec 256
  chainStep   : BitVec 256 → Nat → Nat → BitVec 256 → BitVec 256
  mergeNode   : BitVec 256 → Nat → BitVec 256 → BitVec 256 → BitVec 256

/-! ### Real `cSHAKE256` Framing & Customization-Tag Domain Separation (`crates/qsag-fts/src/frontier.rs`) -/

def fixedBytesLE : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: fixedBytesLE k (n / 256)

def decodeBytesLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeBytesLE bs

theorem fixedBytesLE_length : ∀ (k n : Nat), (fixedBytesLE k n).length = k
  | 0, _ => rfl
  | k + 1, n => congrArg Nat.succ (fixedBytesLE_length k (n / 256))

theorem decodeBytesLE_fixedBytesLE : ∀ (k n : Nat), n < 256 ^ k → decodeBytesLE (fixedBytesLE k n) = n
  | 0, n, hLt => by simp at hLt; subst hLt; rfl
  | k + 1, n, hLt => by
    have hPow : 256 ^ (k + 1) = 256 ^ k * 256 := Nat.pow_succ 256 k
    have hDivLt : n / 256 < 256 ^ k := (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr (hPow ▸ hLt)
    unfold fixedBytesLE decodeBytesLE
    rw [decodeBytesLE_fixedBytesLE k (n / 256) hDivLt, UInt8.toNat_ofNat']
    have h28 : (2 : Nat) ^ 8 = 256 := rfl
    rw [h28]; omega

def fixedBytesBE (k n : Nat) : List UInt8 := (fixedBytesLE k n).reverse
def decodeBytesBE (bs : List UInt8) : Nat := decodeBytesLE bs.reverse

theorem fixedBytesBE_length (k n : Nat) : (fixedBytesBE k n).length = k := by
  rw [fixedBytesBE, List.length_reverse, fixedBytesLE_length]

theorem fixedBytesBE_injective {k n₁ n₂ : Nat} (h₁ : n₁ < 256 ^ k) (h₂ : n₂ < 256 ^ k)
    (hEq : fixedBytesBE k n₁ = fixedBytesBE k n₂) : n₁ = n₂ := by
  have hDec := congrArg decodeBytesBE hEq
  unfold decodeBytesBE fixedBytesBE at hDec
  rw [List.reverse_reverse, List.reverse_reverse,
      decodeBytesLE_fixedBytesLE k n₁ h₁, decodeBytesLE_fixedBytesLE k n₂ h₂] at hDec
  exact hDec

def bv256BytesBE (x : BitVec 256) : List UInt8 := fixedBytesBE 32 x.toNat
def u64BytesBE (x : UInt64) : List UInt8 := fixedBytesBE 8 x.toNat
def u16BytesBE (x : UInt16) : List UInt8 := fixedBytesBE 2 x.toNat
def bytes32ToBv256BE (bs : List UInt8) : BitVec 256 := BitVec.ofNat 256 (decodeBytesBE (bs.take 32))

theorem bv256BytesBE_injective {x y : BitVec 256} (hEq : bv256BytesBE x = bv256BytesBE y) : x = y := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide +kernel
  exact BitVec.eq_of_toNat_eq (fixedBytesBE_injective (h256 ▸ x.isLt) (h256 ▸ y.isLt) hEq)

/-- Exact ASCII customization tags from `crates/qsag-fts/src/frontier.rs:28-33, 689`. -/
def ftsTagLeaf : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 76, 69, 65, 70, 46, 86, 49] -- "QSAG.FTS.LEAF.V1"
def ftsTagMerge : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 77, 69, 82, 71, 69, 46, 86, 49] -- "QSAG.FTS.MERGE.V1"
def ftsTagChain : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 67, 72, 65, 73, 78, 46, 86, 49] -- "QSAG.FTS.CHAIN.V1"
def ftsTagRand : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 82, 65, 78, 68, 46, 86, 49] -- "QSAG.FTS.RAND.V1"
def ftsTagMsgPre : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 77, 83, 71, 50, 53, 54, 46, 86, 49] -- "QSAG.FTS.MSG256.V1"
def ftsTagHmsg : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 72, 77, 83, 71, 46, 86, 49] -- "QSAG.FTS.HMSG.V1"
def ftsTagEpochVote : List UInt8 :=
  [81, 83, 65, 71, 46, 70, 84, 83, 46, 69, 80, 79, 67, 72, 46, 86, 79, 84, 69, 46, 86, 49] -- "QSAG.FTS.EPOCH.VOTE.V1"

inductive FtsDomainRole : Type where
  | leaf | merge | chain | rand | msgPre | hmsg | epochVote
  deriving DecidableEq, Repr

def FtsDomainRole.tag : FtsDomainRole → List UInt8
  | .leaf => ftsTagLeaf
  | .merge => ftsTagMerge
  | .chain => ftsTagChain
  | .rand => ftsTagRand
  | .msgPre => ftsTagMsgPre
  | .hmsg => ftsTagHmsg
  | .epochVote => ftsTagEpochVote

/-- Every pair of distinct `FrontierSumFts` / `RotatedEpochVote` customization tags maps to strictly
    disjoint 136-byte padded `cSHAKE256` sponge block sequences for all payloads `m₁, m₂`. -/
theorem fts_cshake_domains_disjoint (r₁ r₂ : FtsDomainRole) (hNe : r₁ ≠ r₂) (m₁ m₂ : List UInt8) :
    absorbPayload 136 domCshake256 (cshakePrefix [] r₁.tag ++ m₁) ≠
      absorbPayload 136 domCshake256 (cshakePrefix [] r₂.tag ++ m₂) := by
  have hTagNe : r₁.tag ≠ r₂.tag := by
    cases r₁ <;> cases r₂ <;> first | exact False.elim (hNe rfl) | decide +kernel
  have hN : 8 * ([] : List UInt8).length < 256 ^ 255 := bitlen_lt_sp800_bound (s := []) (by decide)
  have hS₁ : 8 * r₁.tag.length < 256 ^ 255 := by
    cases r₁ <;> exact bitlen_lt_sp800_bound (by decide)
  have hS₂ : 8 * r₂.tag.length < 256 ^ 255 := by
    cases r₂ <;> exact bitlen_lt_sp800_bound (by decide)
  have hTagNeNil₁ : r₁.tag ≠ [] := by
    cases r₁ <;> decide
  have hTagNeNil₂ : r₂.tag ≠ [] := by
    cases r₂ <;> decide
  have hDisj := cshake256_domains_disjoint m₁ m₂ hN hS₁ hN hS₂ (fun hPair => hTagNe (Prod.mk.inj hPair).2)
  simpa [hTagNeNil₁, hTagNeNil₂] using hDisj

def evalFtsCshake256_32 (tag payload : List UInt8) : BitVec 256 :=
  bytes32ToBv256BE (evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes [] tag payload 32)

def encodeFrontierPid (p : FrontierFtsParams) : List UInt8 :=
  fixedBytesBE 8 p.nodeBytes ++ fixedBytesBE 8 p.treeHeight ++ fixedBytesBE 8 p.winternitzW ++
  fixedBytesBE 8 p.frontierLen ++ fixedBytesBE 8 p.targetSum ++ fixedBytesBE 8 p.indexBits ++
  fixedBytesBE 8 p.counterBits

/-- Real `cSHAKE256` (`Keccak-f[1600]`) instantiation of `FrontierHashSuite` matching `frontier.rs`. -/
def cshakeFrontierHashSuite (p : FrontierFtsParams) : FrontierHashSuite :=
  let pid := encodeFrontierPid p
  { prehashMsg  := fun pkSeed pkRoot msg =>
      evalFtsCshake256_32 ftsTagMsgPre (pid ++ bv256BytesBE pkSeed ++ bv256BytesBE pkRoot ++ msg)
    squeezeRank := fun pkSeed pkRoot rand d ctr =>
      evalFtsCshake256_32 ftsTagHmsg (pid ++ bv256BytesBE pkSeed ++ bv256BytesBE pkRoot ++
        bv256BytesBE rand ++ bv256BytesBE d ++ u16BytesBE ctr)
    prfRand     := fun skPrf pkSeed pkRoot hedge d =>
      evalFtsCshake256_32 ftsTagRand (pid ++ bv256BytesBE skPrf ++ bv256BytesBE pkSeed ++
        bv256BytesBE pkRoot ++ bv256BytesBE hedge ++ bv256BytesBE d)
    leafStart   := fun pkSeed skSeed v =>
      evalFtsCshake256_32 ftsTagLeaf (pid ++ bv256BytesBE pkSeed ++ fixedBytesBE 8 v ++ bv256BytesBE skSeed)
    chainStep   := fun pkSeed v step cur =>
      evalFtsCshake256_32 ftsTagChain (pid ++ bv256BytesBE pkSeed ++ fixedBytesBE 8 v ++
        fixedBytesBE 8 step ++ bv256BytesBE cur)
    mergeNode   := fun pkSeed v l r =>
      evalFtsCshake256_32 ftsTagMerge (pid ++ bv256BytesBE pkSeed ++ fixedBytesBE 8 v ++
        bv256BytesBE l ++ bv256BytesBE r) }

structure FrontierPublicKey where
  pkSeed : BitVec 256
  root : BitVec 256
  deriving DecidableEq, Repr

structure FrontierSecretKey where
  skSeed : BitVec 256
  skPrf : BitVec 256
  pkSeed : BitVec 256
  deriving DecidableEq, Repr

structure FrontierSignature where
  randomizer : BitVec 256
  grindCounter : UInt16
  chainValues : List (BitVec 256)
  deriving DecidableEq, Repr

private theorem band_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h <;> exact ⟨rfl, rfl⟩

private theorem eq_of_bne_false {α : Type} [DecidableEq α] {a b : α} (h : ¬ (a != b) = true) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso; exact h (by simp [bne, BEq.beq, hab])

def chainAdvance (H : FrontierHashSuite) (pkSeed : BitVec 256) (v : Nat) : Nat → Nat → BitVec 256 → BitVec 256
  | _, 0, cur => cur
  | step, rem + 1, cur => chainAdvance H pkSeed v (step + 1) rem (H.chainStep pkSeed v step cur)

theorem chainAdvance_add (H : FrontierHashSuite) (pkSeed : BitVec 256) (v : Nat) :
    ∀ (s k₁ k₂ : Nat) (x : BitVec 256),
      chainAdvance H pkSeed v s (k₁ + k₂) x = chainAdvance H pkSeed v (s + k₁) k₂ (chainAdvance H pkSeed v s k₁ x)
  | _, 0, _, _ => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | s, k₁ + 1, k₂, x => by
    have h1 : k₁ + 1 + k₂ = (k₁ + k₂) + 1 := by omega
    have h2 : s + 1 + k₁ = s + (k₁ + 1) := by omega
    have ih := chainAdvance_add H pkSeed v (s + 1) k₁ k₂ (H.chainStep pkSeed v s x)
    rw [h1]
    show chainAdvance H pkSeed v (s + 1) (k₁ + k₂) (H.chainStep pkSeed v s x) =
      chainAdvance H pkSeed v (s + (k₁ + 1)) k₂ (chainAdvance H pkSeed v (s + 1) k₁ (H.chainStep pkSeed v s x))
    rw [ih, h2]

def honestNodeBase (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) : Nat → Nat → BitVec 256
  | 0, v => H.leafStart pkSeed skSeed v
  | t + 1, v =>
    H.mergeNode pkSeed v
      (chainAdvance H pkSeed (2 * v) 0 (w - 1) (honestNodeBase H pkSeed skSeed w t (2 * v)))
      (chainAdvance H pkSeed (2 * v + 1) 0 (w - 1) (honestNodeBase H pkSeed skSeed w t (2 * v + 1)))

def honestNodeOut (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w t v : Nat) : BitVec 256 :=
  let base := honestNodeBase H pkSeed skSeed w t v
  if v > 1 then chainAdvance H pkSeed v 0 (w - 1) base else base

def deriveFrontierPk (H : FrontierHashSuite) (p : FrontierFtsParams) (sk : FrontierSecretKey) : FrontierPublicKey :=
  ⟨sk.pkSeed, honestNodeOut H sk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1⟩

def honestSignSubtree (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat)
    (t v : Nat) : AntichainTree → List Nat → List (BitVec 256)
  | .leaf, offs => [chainAdvance H pkSeed v 0 (offs.headD 0) (honestNodeBase H pkSeed skSeed w t v)]
  | .split l r, offs =>
    match t with
    | 0 => []
    | t' + 1 =>
      honestSignSubtree H pkSeed skSeed w t' (2 * v) l (offs.take l.size) ++
      honestSignSubtree H pkSeed skSeed w t' (2 * v + 1) r (offs.drop l.size)

def evalAntichainTree (H : FrontierHashSuite) (pkSeed : BitVec 256) (w v : Nat) :
    AntichainTree → List Nat → List (BitVec 256) → BitVec 256
  | .leaf, offs, vals => chainAdvance H pkSeed v (offs.headD 0) (w - 1 - offs.headD 0) (vals.headD 0#256)
  | .split l r, offs, vals =>
    let m := H.mergeNode pkSeed v
      (evalAntichainTree H pkSeed w (2 * v) l (offs.take l.size) (vals.take l.size))
      (evalAntichainTree H pkSeed w (2 * v + 1) r (offs.drop l.size) (vals.drop l.size))
    if v > 1 then chainAdvance H pkSeed v 0 (w - 1) m else m

def collapseFrontierStack (H : FrontierHashSuite) (pkSeed : BitVec 256) (w v : Nat)
    (cur : BitVec 256) : List (Nat × BitVec 256) → List (Nat × BitVec 256)
  | [] => [(v, cur)]
  | (leftV, lEnd) :: rest =>
    if leftV % 2 = 0 ∧ v = leftV + 1 then
      let pv := leftV / 2; let m := H.mergeNode pkSeed pv lEnd cur
      collapseFrontierStack H pkSeed w pv (if pv > 1 then chainAdvance H pkSeed pv 0 (w - 1) m else m) rest
    else (v, cur) :: (leftV, lEnd) :: rest

def runFrontierStackLoop (H : FrontierHashSuite) (pkSeed : BitVec 256) (w : Nat) :
    List Nat → List Nat → List (BitVec 256) → List (Nat × BitVec 256) → List (Nat × BitVec 256)
  | [], _, _, st => st
  | v :: vs, offs, vals, st =>
    let a := offs.headD 0
    runFrontierStackLoop H pkSeed w vs offs.tail vals.tail
      (collapseFrontierStack H pkSeed w v (chainAdvance H pkSeed v a (w - 1 - a) (vals.headD 0#256)) st)

private theorem length_take_eq {α : Type} :
    ∀ (xs : List α) (n : Nat), n ≤ xs.length → (xs.take n).length = n
  | _, 0, _ => rfl
  | [], _ + 1, h => nomatch h
  | _ :: xs, n + 1, h => congrArg Nat.succ (length_take_eq xs n (Nat.le_of_succ_le_succ h))

private theorem runFrontierStackLoop_tree_eq (H : FrontierHashSuite) (pkSeed : BitVec 256) (w : Nat) :
    ∀ (tr : AntichainTree) (v : Nat) (offs : List Nat) (vals : List (BitVec 256))
      (restVs restOffs : List Nat) (restVals : List (BitVec 256)) (st : List (Nat × BitVec 256)),
      0 < v → offs.length = tr.size → vals.length = tr.size →
      runFrontierStackLoop H pkSeed w (tr.frontierNodes v ++ restVs) (offs ++ restOffs) (vals ++ restVals) st =
      runFrontierStackLoop H pkSeed w restVs restOffs restVals
        (collapseFrontierStack H pkSeed w v (evalAntichainTree H pkSeed w v tr offs vals) st)
  | .leaf, _, offs, vals, _, _, _, _, _, hOL, hVL => by
    cases offs with
    | nil => cases hOL
    | cons a os =>
      cases vals with
      | nil => cases hVL
      | cons x xs =>
        cases os with
        | nil =>
          cases xs with
          | nil => rfl
          | cons _ _ => cases Nat.succ.inj hVL
        | cons _ _ => cases Nat.succ.inj hOL
  | .split l r, v, offs, vals, restVs, restOffs, restVals, st, hv, hOL, hVL => by
    conv => lhs; rw [AntichainTree.frontierNodes, List.append_assoc,
      (List.take_append_drop l.size offs).symm, List.append_assoc,
      (List.take_append_drop l.size vals).symm, List.append_assoc]
    rw [runFrontierStackLoop_tree_eq H pkSeed w l (2 * v) (offs.take l.size) (vals.take l.size)
          (r.frontierNodes (2 * v + 1) ++ restVs) (offs.drop l.size ++ restOffs) (vals.drop l.size ++ restVals)
          st (by omega)
          (length_take_eq offs l.size (by unfold AntichainTree.size at hOL; omega))
          (length_take_eq vals l.size (by unfold AntichainTree.size at hVL; omega))]
    have hL : collapseFrontierStack H pkSeed w (2 * v)
        (evalAntichainTree H pkSeed w (2 * v) l (offs.take l.size) (vals.take l.size)) st =
        (2 * v, evalAntichainTree H pkSeed w (2 * v) l (offs.take l.size) (vals.take l.size)) :: st := by
      cases st with
      | nil => rfl
      | cons hd _ => unfold collapseFrontierStack; simp [show ¬ (hd.1 % 2 = 0 ∧ 2 * v = hd.1 + 1) by rintro ⟨_, _⟩; omega]
    rw [hL, runFrontierStackLoop_tree_eq H pkSeed w r (2 * v + 1) (offs.drop l.size) (vals.drop l.size)
          restVs restOffs restVals _ (by omega)
          (by rw [List.length_drop]; unfold AntichainTree.size at hOL; omega)
          (by rw [List.length_drop]; unfold AntichainTree.size at hVL; omega)]
    congr 1
    conv => lhs; unfold collapseFrontierStack
    simp [show (2 * v) % 2 = 0 ∧ 2 * v + 1 = 2 * v + 1 from ⟨by omega, rfl⟩, show (2 * v) / 2 = v by omega, evalAntichainTree]

def verifyFrontierFts (H : FrontierHashSuite) (p : FrontierFtsParams)
    (pk : FrontierPublicKey) (msg : List UInt8) (sig : FrontierSignature) : Bool :=
  if sig.chainValues.length != p.frontierLen then false
  else if sig.grindCounter.toNat >= 2 ^ p.counterBits then false
  else
    let d := H.prehashMsg pk.pkSeed pk.root msg
    match unrankFrontierFts p (H.squeezeRank pk.pkSeed pk.root sig.randomizer d sig.grindCounter).toNat with
    | none => false
    | some (_, frontier, offsets) =>
      match runFrontierStackLoop H pk.pkSeed p.winternitzW frontier offsets sig.chainValues [] with
      | [(1, rootOut)] => decide (rootOut = pk.root)
      | _ => false

