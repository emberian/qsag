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
     `cshake256_framed_xof` framing (`encodeEpochVoteInput_injective`) under `cSHAKE256("QSAG.FTS.EPOCH.VOTE.V1")`
     (`cshakeEpochVoteHasher`), proving by induction across historical epochs that an accepted
     divergent chain yields an explicit `cSHAKE256` framing collision on distinct framed inputs or
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

public import Qsag.Tactic.Prelude
public import Qsag.Spec.GameBound
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Sponge
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Threshold.ThresholdMpc
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

/-- Inequality of full `cSHAKE256` padded 136-byte block sequences (`cshake256_encodings_ne` form)
    for any distinct `FrontierSumFts` / `RotatedEpochVote` customization tags `r₁ ≠ r₂`. -/
theorem fts_cshake_encodings_ne (r₁ r₂ : FtsDomainRole) (hNe : r₁ ≠ r₂) (m₁ m₂ : List UInt8) :
    (if ([] : List UInt8) = [] ∧ r₁.tag = [] then absorbPayload 136 domShake256 m₁
     else absorbPayload 136 domCshake256 (cshakePrefix [] r₁.tag ++ m₁)) ≠
    (if ([] : List UInt8) = [] ∧ r₂.tag = [] then absorbPayload 136 domShake256 m₂
     else absorbPayload 136 domCshake256 (cshakePrefix [] r₂.tag ++ m₂)) := by
  have hTagNe : r₁.tag ≠ r₂.tag := by
    cases r₁ <;> cases r₂ <;> first | exact False.elim (hNe rfl) | decide +kernel
  have hN : 8 * ([] : List UInt8).length < 256 ^ 255 := bitlen_lt_sp800_bound (s := []) (by decide)
  have hS₁ : 8 * r₁.tag.length < 256 ^ 255 := by
    cases r₁ <;> exact bitlen_lt_sp800_bound (by decide)
  have hS₂ : 8 * r₂.tag.length < 256 ^ 255 := by
    cases r₂ <;> exact bitlen_lt_sp800_bound (by decide)
  exact cshake256_encodings_ne m₁ m₂ hN hS₁ hN hS₂ (fun hPair => hTagNe (Prod.mk.inj hPair).2)

/-- Every pair of distinct `FrontierSumFts` / `RotatedEpochVote` customization tags maps to
    unequal 136-byte padded `cSHAKE256` sponge block sequences for all payloads `m₁, m₂`. -/
theorem fts_cshake_domains_disjoint (r₁ r₂ : FtsDomainRole) (hNe : r₁ ≠ r₂) (m₁ m₂ : List UInt8) :
    absorbPayload 136 domCshake256 (cshakePrefix [] r₁.tag ++ m₁) ≠
      absorbPayload 136 domCshake256 (cshakePrefix [] r₂.tag ++ m₂) := by
  have hTagNeNil₁ : r₁.tag ≠ [] := by cases r₁ <;> decide
  have hTagNeNil₂ : r₂.tag ≠ [] := by cases r₂ <;> decide
  simpa [hTagNeNil₁, hTagNeNil₂] using fts_cshake_encodings_ne r₁ r₂ hNe m₁ m₂

def evalFtsCshake256_32 (tag payload : List UInt8) : BitVec 256 :=
  bytes32ToBv256BE (evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes [] tag payload 32)

def encodeFrontierPid (p : FrontierFtsParams) : List UInt8 :=
  fixedBytesBE 8 p.nodeBytes ++ fixedBytesBE 8 p.treeHeight ++ fixedBytesBE 8 p.winternitzW ++
  fixedBytesBE 8 p.frontierLen ++ fixedBytesBE 8 p.targetSum ++ fixedBytesBE 8 p.indexBits ++
  fixedBytesBE 8 p.counterBits

theorem encodeFrontierPid_length (p : FrontierFtsParams) : (encodeFrontierPid p).length = 56 := by
  simp [encodeFrontierPid, fixedBytesBE_length]

/-- Length-framed `cshake256_framed_xof` body `(u64_le(f.len()) || f)*`
    (`crates/qsag-accel/src/keccak.rs:274-284`). -/
def encodeCshakeFramesBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => fixedBytesLE 8 f.length ++ f ++ encodeCshakeFramesBody fs

/-- Exact preimage framing absorbed by `cshake256_framed_xof(tag, frames)`
    (`crates/qsag-accel/src/keccak.rs:274-284`):
    `u64_le(frames.len()) || (u64_le(f.len()) || f)*`. -/
def encodeCshakeFrames (frames : List (List UInt8)) : List UInt8 :=
  fixedBytesLE 8 frames.length ++ encodeCshakeFramesBody frames

theorem encodeCshakeFramesBody_eq_flatMap :
    ∀ frames : List (List UInt8),
      encodeCshakeFramesBody frames = frames.flatMap (fun f => fixedBytesLE 8 f.length ++ f)
  | [] => rfl
  | f :: fs => by
    simp only [encodeCshakeFramesBody, List.flatMap_cons, List.append_assoc,
      encodeCshakeFramesBody_eq_flatMap fs]

theorem encodeCshakeFrames_eq_flatMap (frames : List (List UInt8)) :
    encodeCshakeFrames frames =
      fixedBytesLE 8 frames.length ++ frames.flatMap (fun f => fixedBytesLE 8 f.length ++ f) := by
  rw [encodeCshakeFrames, encodeCshakeFramesBody_eq_flatMap]

theorem fixedBytesLE_injective {k n₁ n₂ : Nat} (h₁ : n₁ < 256 ^ k) (h₂ : n₂ < 256 ^ k)
    (hEq : fixedBytesLE k n₁ = fixedBytesLE k n₂) : n₁ = n₂ := by
  have hDec := congrArg decodeBytesLE hEq
  rw [decodeBytesLE_fixedBytesLE k n₁ h₁, decodeBytesLE_fixedBytesLE k n₂ h₂] at hDec
  exact hDec

private theorem append_inj_left_len {α : Type} :
    ∀ {xs₁ xs₂ ys₁ ys₂ : List α}, xs₁.length = xs₂.length →
      xs₁ ++ ys₁ = xs₂ ++ ys₂ → xs₁ = xs₂ ∧ ys₁ = ys₂
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | _ :: _, [], _, _, hL, _ => nomatch hL
  | [], _ :: _, _, _, hL, _ => nomatch hL
  | a₁ :: xs₁, a₂ :: xs₂, ys₁, ys₂, hL, hEq => by
    obtain ⟨rfl, hTl⟩ := List.cons.inj hEq
    obtain ⟨hX, hY⟩ := append_inj_left_len (Nat.succ.inj hL) hTl
    exact ⟨congrArg (a₁ :: ·) hX, hY⟩

theorem encodeCshakeFramesBody_injective :
    ∀ {fs₁ fs₂ : List (List UInt8)},
      (∀ f ∈ fs₁, f.length < 256 ^ 8) →
      (∀ f ∈ fs₂, f.length < 256 ^ 8) →
      encodeCshakeFramesBody fs₁ = encodeCshakeFramesBody fs₂ →
      fs₁ = fs₂
  | [], [], _, _, _ => rfl
  | [], f₂ :: fs₂, _, _, hEq => by
    have hL := congrArg List.length hEq
    simp [encodeCshakeFramesBody, fixedBytesLE_length] at hL <;> omega
  | f₁ :: fs₁, [], _, _, hEq => by
    have hL := congrArg List.length hEq
    simp [encodeCshakeFramesBody, fixedBytesLE_length] at hL <;> omega
  | f₁ :: fs₁, f₂ :: fs₂, hB₁, hB₂, hEq => by
    simp only [encodeCshakeFramesBody, List.append_assoc] at hEq
    obtain ⟨hLenBytes, hRest⟩ := append_inj_left_len
      ((fixedBytesLE_length 8 f₁.length).trans (fixedBytesLE_length 8 f₂.length).symm) hEq
    have hFLen : f₁.length = f₂.length :=
      fixedBytesLE_injective (hB₁ f₁ (.head fs₁)) (hB₂ f₂ (.head fs₂)) hLenBytes
    obtain ⟨hF, hTail⟩ := append_inj_left_len hFLen hRest
    rw [hF, encodeCshakeFramesBody_injective
      (fun f hf => hB₁ f (.tail f₁ hf)) (fun f hf => hB₂ f (.tail f₂ hf)) hTail]

/-- **Tuple-Level Frame Injectivity of `cshake256_framed_xof` (`encodeCshakeFrames_injective`)**:
    Distinct lists of `< 2^64`-byte frames never collide prior to sponge absorption. -/
theorem encodeCshakeFrames_injective {fs₁ fs₂ : List (List UInt8)}
    (hB₁ : ∀ f ∈ fs₁, f.length < 256 ^ 8)
    (hB₂ : ∀ f ∈ fs₂, f.length < 256 ^ 8)
    (hEq : encodeCshakeFrames fs₁ = encodeCshakeFrames fs₂) :
    fs₁ = fs₂ := by
  unfold encodeCshakeFrames at hEq
  obtain ⟨_, hBody⟩ := append_inj_left_len
    ((fixedBytesLE_length 8 fs₁.length).trans (fixedBytesLE_length 8 fs₂.length).symm) hEq
  exact encodeCshakeFramesBody_injective hB₁ hB₂ hBody

theorem u16BytesBE_injective {c₁ c₂ : UInt16} (hEq : u16BytesBE c₁ = u16BytesBE c₂) : c₁ = c₂ := by
  have h16 : (2 : Nat) ^ 16 = 256 ^ 2 := by decide +kernel
  exact UInt16.eq_of_toBitVec_eq
    (BitVec.eq_of_toNat_eq (fixedBytesBE_injective (h16 ▸ c₁.toBitVec.isLt) (h16 ▸ c₂.toBitVec.isLt) hEq))

/-- Exact framed `cSHAKE256` preimage builders for the six `FrontierSumFts` roles
    (`crates/qsag-fts/src/frontier.rs:748-812, 1077-1089`). -/
def ftsPrehashFrames (p : FrontierFtsParams) (pkSeed pkRoot : BitVec 256) (msg : List UInt8) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE pkSeed, bv256BytesBE pkRoot, msg]

def ftsSqueezeRankFrames (p : FrontierFtsParams) (pkSeed pkRoot rand d : BitVec 256) (ctr : UInt16) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, u16BytesBE ctr, bv256BytesBE pkSeed, bv256BytesBE pkRoot,
    bv256BytesBE rand, bv256BytesBE d]

def ftsPrfRandFrames (p : FrontierFtsParams) (skPrf pkSeed pkRoot hedge d : BitVec 256) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE skPrf, bv256BytesBE pkSeed, bv256BytesBE pkRoot,
    bv256BytesBE hedge, [0], bv256BytesBE d]

def ftsLeafStartFrames (p : FrontierFtsParams) (pkSeed skSeed : BitVec 256) (v : Nat) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE pkSeed, fixedBytesBE 8 v, bv256BytesBE skSeed]

def ftsChainStepFrames (p : FrontierFtsParams) (pkSeed : BitVec 256) (v step : Nat) (cur : BitVec 256) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE pkSeed, fixedBytesBE 8 v, fixedBytesBE 8 step,
    bv256BytesBE cur]

def ftsMergeNodeFrames (p : FrontierFtsParams) (pkSeed : BitVec 256) (v : Nat) (l r : BitVec 256) : List UInt8 :=
  encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE pkSeed, fixedBytesBE 8 v,
    bv256BytesBE l, bv256BytesBE r]

theorem ftsSqueezeRankFrames_eq (p : FrontierFtsParams) (pkSeed pkRoot rand d : BitVec 256) (ctr : UInt16) :
    ftsSqueezeRankFrames p pkSeed pkRoot rand d ctr =
      encodeCshakeFrames [encodeFrontierPid p, u16BytesBE ctr, bv256BytesBE pkSeed, bv256BytesBE pkRoot,
        bv256BytesBE rand, bv256BytesBE d] := by unfold ftsSqueezeRankFrames; rfl

theorem ftsPrfRandFrames_eq (p : FrontierFtsParams) (skPrf pkSeed pkRoot hedge d : BitVec 256) :
    ftsPrfRandFrames p skPrf pkSeed pkRoot hedge d =
      encodeCshakeFrames [encodeFrontierPid p, bv256BytesBE skPrf, bv256BytesBE pkSeed, bv256BytesBE pkRoot,
        bv256BytesBE hedge, [0], bv256BytesBE d] := by unfold ftsPrfRandFrames; rfl

/-- Real `cSHAKE256` (`Keccak-f[1600]`, `cshake256_framed_xof`) instantiation of `FrontierHashSuite`
    matching `crates/qsag-fts/src/frontier.rs:748-812, 1077-1089` bit-for-bit. -/
def cshakeFrontierHashSuite (p : FrontierFtsParams) : FrontierHashSuite where
  prehashMsg  pkSeed pkRoot msg := evalFtsCshake256_32 ftsTagMsgPre (ftsPrehashFrames p pkSeed pkRoot msg)
  squeezeRank pkSeed pkRoot rand d ctr := evalFtsCshake256_32 ftsTagHmsg (ftsSqueezeRankFrames p pkSeed pkRoot rand d ctr)
  prfRand     skPrf pkSeed pkRoot hedge d := evalFtsCshake256_32 ftsTagRand (ftsPrfRandFrames p skPrf pkSeed pkRoot hedge d)
  leafStart   pkSeed skSeed v := evalFtsCshake256_32 ftsTagLeaf (ftsLeafStartFrames p pkSeed skSeed v)
  chainStep   pkSeed v step cur := evalFtsCshake256_32 ftsTagChain (ftsChainStepFrames p pkSeed v step cur)
  mergeNode   pkSeed v l r := evalFtsCshake256_32 ftsTagMerge (ftsMergeNodeFrames p pkSeed v l r)

private theorem len_pid_lt_u64 (p : FrontierFtsParams) : (encodeFrontierPid p).length < 256 ^ 8 := by
  rw [encodeFrontierPid_length]; decide +kernel

private theorem len_bv256_lt_u64 (x : BitVec 256) : (bv256BytesBE x).length < 256 ^ 8 := by
  rw [bv256BytesBE, fixedBytesBE_length]; decide +kernel

private theorem len_be8_lt_u64 (n : Nat) : (fixedBytesBE 8 n).length < 256 ^ 8 := by
  rw [fixedBytesBE_length]; decide +kernel

private theorem len_u16_lt_u64 (c : UInt16) : (u16BytesBE c).length < 256 ^ 8 := by
  rw [u16BytesBE, fixedBytesBE_length]; decide +kernel

theorem ftsPrehashFrames_injective (p : FrontierFtsParams)
    {pkS₁ pkR₁ pkS₂ pkR₂ : BitVec 256} {m₁ m₂ : List UInt8}
    (hm₁ : m₁.length < 256 ^ 8) (hm₂ : m₂.length < 256 ^ 8)
    (hEq : ftsPrehashFrames p pkS₁ pkR₁ m₁ = ftsPrehashFrames p pkS₂ pkR₂ m₂) :
    pkS₁ = pkS₂ ∧ pkR₁ = pkR₂ ∧ m₁ = m₂ := by
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₁
        · exact len_bv256_lt_u64 pkR₁
        · exact hm₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₂
        · exact len_bv256_lt_u64 pkR₂
        · exact hm₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  exact ⟨bv256BytesBE_injective hL.2.1, bv256BytesBE_injective hL.2.2.1, hL.2.2.2⟩

theorem ftsSqueezeRankFrames_injective (p : FrontierFtsParams)
    {pkS₁ pkR₁ r₁ d₁ pkS₂ pkR₂ r₂ d₂ : BitVec 256} {c₁ c₂ : UInt16}
    (hEq : ftsSqueezeRankFrames p pkS₁ pkR₁ r₁ d₁ c₁ = ftsSqueezeRankFrames p pkS₂ pkR₂ r₂ d₂ c₂) :
    c₁ = c₂ ∧ pkS₁ = pkS₂ ∧ pkR₁ = pkR₂ ∧ r₁ = r₂ ∧ d₁ = d₂ := by
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_u16_lt_u64 c₁
        · exact len_bv256_lt_u64 pkS₁
        · exact len_bv256_lt_u64 pkR₁
        · exact len_bv256_lt_u64 r₁
        · exact len_bv256_lt_u64 d₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_u16_lt_u64 c₂
        · exact len_bv256_lt_u64 pkS₂
        · exact len_bv256_lt_u64 pkR₂
        · exact len_bv256_lt_u64 r₂
        · exact len_bv256_lt_u64 d₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  exact ⟨u16BytesBE_injective hL.2.1, bv256BytesBE_injective hL.2.2.1,
    bv256BytesBE_injective hL.2.2.2.1, bv256BytesBE_injective hL.2.2.2.2.1,
    bv256BytesBE_injective hL.2.2.2.2.2⟩

theorem ftsPrfRandFrames_injective (p : FrontierFtsParams)
    {skP₁ pkS₁ pkR₁ h₁ d₁ skP₂ pkS₂ pkR₂ h₂ d₂ : BitVec 256}
    (hEq : ftsPrfRandFrames p skP₁ pkS₁ pkR₁ h₁ d₁ = ftsPrfRandFrames p skP₂ pkS₂ pkR₂ h₂ d₂) :
    skP₁ = skP₂ ∧ pkS₁ = pkS₂ ∧ pkR₁ = pkR₂ ∧ h₁ = h₂ ∧ d₁ = d₂ := by
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 skP₁
        · exact len_bv256_lt_u64 pkS₁
        · exact len_bv256_lt_u64 pkR₁
        · exact len_bv256_lt_u64 h₁
        · decide +kernel
        · exact len_bv256_lt_u64 d₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 skP₂
        · exact len_bv256_lt_u64 pkS₂
        · exact len_bv256_lt_u64 pkR₂
        · exact len_bv256_lt_u64 h₂
        · decide +kernel
        · exact len_bv256_lt_u64 d₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  exact ⟨bv256BytesBE_injective hL.2.1, bv256BytesBE_injective hL.2.2.1,
    bv256BytesBE_injective hL.2.2.2.1, bv256BytesBE_injective hL.2.2.2.2.1,
    bv256BytesBE_injective hL.2.2.2.2.2.2⟩

theorem ftsChainStepFrames_injective (p : FrontierFtsParams)
    {pkS₁ pkS₂ cur₁ cur₂ : BitVec 256} {v₁ s₁ v₂ s₂ : Nat}
    (hv₁ : v₁ < 256 ^ 8) (hs₁ : s₁ < 256 ^ 8) (hv₂ : v₂ < 256 ^ 8) (hs₂ : s₂ < 256 ^ 8)
    (hEq : ftsChainStepFrames p pkS₁ v₁ s₁ cur₁ = ftsChainStepFrames p pkS₂ v₂ s₂ cur₂) :
    pkS₁ = pkS₂ ∧ v₁ = v₂ ∧ s₁ = s₂ ∧ cur₁ = cur₂ := by
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₁
        · exact len_be8_lt_u64 v₁
        · exact len_be8_lt_u64 s₁
        · exact len_bv256_lt_u64 cur₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₂
        · exact len_be8_lt_u64 v₂
        · exact len_be8_lt_u64 s₂
        · exact len_bv256_lt_u64 cur₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  exact ⟨bv256BytesBE_injective hL.2.1, fixedBytesBE_injective hv₁ hv₂ hL.2.2.1,
    fixedBytesBE_injective hs₁ hs₂ hL.2.2.2.1, bv256BytesBE_injective hL.2.2.2.2⟩

theorem ftsMergeNodeFrames_injective (p : FrontierFtsParams)
    {pkS₁ pkS₂ l₁ r₁ l₂ r₂ : BitVec 256} {v₁ v₂ : Nat}
    (hv₁ : v₁ < 256 ^ 8) (hv₂ : v₂ < 256 ^ 8)
    (hEq : ftsMergeNodeFrames p pkS₁ v₁ l₁ r₁ = ftsMergeNodeFrames p pkS₂ v₂ l₂ r₂) :
    pkS₁ = pkS₂ ∧ v₁ = v₂ ∧ l₁ = l₂ ∧ r₁ = r₂ := by
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₁
        · exact len_be8_lt_u64 v₁
        · exact len_bv256_lt_u64 l₁
        · exact len_bv256_lt_u64 r₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl
        · exact len_pid_lt_u64 p
        · exact len_bv256_lt_u64 pkS₂
        · exact len_be8_lt_u64 v₂
        · exact len_bv256_lt_u64 l₂
        · exact len_bv256_lt_u64 r₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  exact ⟨bv256BytesBE_injective hL.2.1, fixedBytesBE_injective hv₁ hv₂ hL.2.2.1,
    bv256BytesBE_injective hL.2.2.2.1, bv256BytesBE_injective hL.2.2.2.2⟩

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

def signFrontierFts (H : FrontierHashSuite) (p : FrontierFtsParams)
    (sk : FrontierSecretKey) (hedge : BitVec 256) (ctr : UInt16) (msg : List UInt8) : Option FrontierSignature :=
  if ctr.toNat >= 2 ^ p.counterBits then none
  else
    let pk := deriveFrontierPk H p sk
    let d := H.prehashMsg pk.pkSeed pk.root msg
    let rand := H.prfRand sk.skPrf pk.pkSeed pk.root hedge d
    match unrankFrontierFts p (H.squeezeRank pk.pkSeed pk.root rand d ctr).toNat with
    | none => none
    | some (tr, _, offs) =>
      some ⟨rand, ctr, honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs⟩

private theorem honestSignSubtree_length (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) :
    ∀ (t v : Nat) (tr : AntichainTree) (offs : List Nat),
      tr.Valid t = true → (honestSignSubtree H pkSeed skSeed w t v tr offs).length = tr.size
  | _, _, .leaf, _, _ => by unfold honestSignSubtree; rfl
  | 0, _, .split _ _, _, hV => by simp [AntichainTree.Valid] at hV
  | t + 1, v, .split l r, offs, hV => by
    obtain ⟨hl, hr⟩ := band_eq_true hV
    unfold honestSignSubtree
    dsimp only
    rw [List.length_append,
      honestSignSubtree_length H pkSeed skSeed w t (2 * v) l _ hl,
      honestSignSubtree_length H pkSeed skSeed w t (2 * v + 1) r _ hr]
    rfl

private theorem take_append_eq {α : Type} :
    ∀ (xs ys : List α) (n : Nat), xs.length = n → (xs ++ ys).take n = xs
  | [], _, 0, _ => rfl
  | _ :: _, _, 0, h => nomatch h
  | [], _, _ + 1, h => nomatch h
  | x :: xs, ys, n + 1, h => congrArg (x :: ·) (take_append_eq xs ys n (Nat.succ.inj h))

private theorem drop_append_eq {α : Type} :
    ∀ (xs ys : List α) (n : Nat), xs.length = n → (xs ++ ys).drop n = ys
  | [], _ys, 0, _ => rfl
  | _ :: _, _, 0, h => nomatch h
  | [], _, _ + 1, h => nomatch h
  | _ :: xs, ys, n + 1, h => drop_append_eq xs ys n (Nat.succ.inj h)

private theorem evalAntichainTree_honest (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) (hw : 1 ≤ w) :
    ∀ (t v : Nat) (tr : AntichainTree) (offs : List Nat),
      0 < v → tr.Valid t = true → offs.length = tr.size → (∀ a ∈ offs, a < w) → (tr = .leaf → 1 < v) →
      evalAntichainTree H pkSeed w v tr offs (honestSignSubtree H pkSeed skSeed w t v tr offs) =
        honestNodeOut H pkSeed skSeed w t v
  | t, v, .leaf, offs, _, _, hOL, hBnd, hvGt => by
    cases offs with
    | nil => cases hOL
    | cons a os =>
      have := hBnd a (.head os)
      unfold honestSignSubtree evalAntichainTree honestNodeOut
      simp only [List.headD_cons, hvGt rfl, ↓reduceIte]
      have hAdd := chainAdvance_add H pkSeed v 0 a (w - 1 - a) (honestNodeBase H pkSeed skSeed w t v)
      rw [Nat.zero_add, show a + (w - 1 - a) = w - 1 by omega] at hAdd
      exact hAdd.symm
  | 0, _, .split _ _, _, _, hV, _, _, _ => by simp [AntichainTree.Valid] at hV
  | t + 1, v, .split l r, offs, hv, hV, hOL, hBnd, _ => by
    obtain ⟨hl, hr⟩ := band_eq_true hV
    have hHSL := honestSignSubtree_length H pkSeed skSeed w t (2 * v) l (offs.take l.size) hl
    have hTkL : (offs.take l.size).length = l.size :=
      length_take_eq offs l.size (by unfold AntichainTree.size at hOL; omega)
    have hDpL : (offs.drop l.size).length = r.size := by
      rw [List.length_drop]; unfold AntichainTree.size at hOL; omega
    have hTakeH :
        ((honestSignSubtree H pkSeed skSeed w t (2 * v) l (offs.take l.size)) ++
         (honestSignSubtree H pkSeed skSeed w t (2 * v + 1) r (offs.drop l.size))).take l.size =
          honestSignSubtree H pkSeed skSeed w t (2 * v) l (offs.take l.size) :=
      take_append_eq _ _ l.size hHSL
    have hDropH :
        ((honestSignSubtree H pkSeed skSeed w t (2 * v) l (offs.take l.size)) ++
         (honestSignSubtree H pkSeed skSeed w t (2 * v + 1) r (offs.drop l.size))).drop l.size =
          honestSignSubtree H pkSeed skSeed w t (2 * v + 1) r (offs.drop l.size) :=
      drop_append_eq _ _ l.size hHSL
    unfold honestSignSubtree evalAntichainTree
    dsimp only
    rw [hTakeH, hDropH,
        evalAntichainTree_honest H pkSeed skSeed w hw t (2 * v) l (offs.take l.size) (by omega) hl
          hTkL (fun a ha => hBnd a (List.mem_of_mem_take ha)) (fun _ => by omega),
        evalAntichainTree_honest H pkSeed skSeed w hw t (2 * v + 1) r (offs.drop l.size) (by omega) hr
          hDpL (fun a ha => hBnd a (List.mem_of_mem_drop ha)) (fun _ => by omega)]
    have hLOut : honestNodeOut H pkSeed skSeed w t (2 * v) =
        chainAdvance H pkSeed (2 * v) 0 (w - 1) (honestNodeBase H pkSeed skSeed w t (2 * v)) := by
      unfold honestNodeOut; simp [show 2 * v > 1 by omega]
    have hROut : honestNodeOut H pkSeed skSeed w t (2 * v + 1) =
        chainAdvance H pkSeed (2 * v + 1) 0 (w - 1) (honestNodeBase H pkSeed skSeed w t (2 * v + 1)) := by
      unfold honestNodeOut; simp [show 2 * v + 1 > 1 by omega]
    have hMergeEq : H.mergeNode pkSeed v
        (honestNodeOut H pkSeed skSeed w t (2 * v))
        (honestNodeOut H pkSeed skSeed w t (2 * v + 1)) =
        honestNodeBase H pkSeed skSeed w (t + 1) v := by
      rw [hLOut, hROut]; rfl
    rw [hMergeEq]; rfl

theorem verifyFrontierFts_signFrontierFts (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hw : 1 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen)
    (sk : FrontierSecretKey) (hedge : BitVec 256) (ctr : UInt16) (msg : List UInt8)
    (sig : FrontierSignature) (hSign : signFrontierFts H p sk hedge ctr msg = some sig) :
    verifyFrontierFts H p (deriveFrontierPk H p sk) msg sig = true := by
  unfold signFrontierFts at hSign
  by_cases hCtr : ctr.toNat >= 2 ^ p.counterBits; · simp [hCtr] at hSign
  simp only [hCtr, ↓reduceIte] at hSign
  let pk := deriveFrontierPk H p sk; let d := H.prehashMsg pk.pkSeed pk.root msg
  let rand := H.prfRand sk.skPrf pk.pkSeed pk.root hedge d
  let rk := (H.squeezeRank pk.pkSeed pk.root rand d ctr).toNat
  cases hUnr : unrankFrontierFts p rk with
  | none => simp [pk, d, rand, rk, hUnr] at hSign
  | some tp =>
    obtain ⟨tr, paths, offs⟩ := tp; simp only [pk, d, rand, rk, hUnr, Option.some.injEq] at hSign; subst hSign
    have hLt := unrankFrontierFts_rank_lt hUnr
    obtain ⟨_, _, _, hu', hp', hVal, hSz, _, hOLen, _, hBnd, _⟩ := unrankFrontierFts_bijective p rk hLt
    rw [hUnr] at hu'; injection hu' with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    have hSigLen := (honestSignSubtree_length H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs hVal).trans hSz
    change verifyFrontierFts H p pk msg
      ⟨rand, ctr, honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs⟩ = true
    unfold verifyFrontierFts
    have hLenChk : ((honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs).length != p.frontierLen) = false := by
      rw [hSigLen]; simp
    rw [hLenChk]
    simp only [Bool.false_eq_true, ↓reduceIte, hCtr]
    change (match unrankFrontierFts p rk with
            | none => false
            | some (_, frontier, offsets) =>
              match runFrontierStackLoop H pk.pkSeed p.winternitzW frontier offsets
                  (honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs) [] with
              | [(1, rootOut)] => decide (rootOut = pk.root)
              | _ => false) = true
    rw [hUnr]; dsimp only
    have hLp := runFrontierStackLoop_tree_eq H pk.pkSeed p.winternitzW tr 1 offs
      (honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs) [] [] [] []
      (by decide) (hOLen.trans hSz.symm) (hSigLen.trans hSz.symm)
    simp only [List.append_nil] at hLp; rw [hp', hLp]
    unfold runFrontierStackLoop collapseFrontierStack
    rw [evalAntichainTree_honest H pk.pkSeed sk.skSeed p.winternitzW hw p.treeHeight 1 tr offs
      (by decide) hVal (hOLen.trans hSz.symm) hBnd (fun hLf => by subst hLf; unfold AntichainTree.size at hSz; omega)]
    simp [pk, deriveFrontierPk]

inductive FrontierForgeryBreak (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) : Type where
  | prehashTcrCollision (pkRoot : BitVec 256) (m₁ m₂ : List UInt8) :
      m₂ ≠ m₁ → H.prehashMsg pkSeed pkRoot m₂ = H.prehashMsg pkSeed pkRoot m₁ → FrontierForgeryBreak H pkSeed skSeed w
  | targetIndexCollision (pkRoot r₁ d₁ : BitVec 256) (c₁ : UInt16) (r₂ d₂ : BitVec 256) (c₂ : UInt16) :
      (r₂ ≠ r₁ ∨ d₂ ≠ d₁ ∨ c₂ ≠ c₁) →
      (H.squeezeRank pkSeed pkRoot r₂ d₂ c₂).toNat = (H.squeezeRank pkSeed pkRoot r₁ d₁ c₁).toNat →
      FrontierForgeryBreak H pkSeed skSeed w
  | merkleCollision (v : Nat) (l₁ r₁ l₂ r₂ : BitVec 256) :
      (l₁ ≠ l₂ ∨ r₁ ≠ r₂) → H.mergeNode pkSeed v l₁ r₁ = H.mergeNode pkSeed v l₂ r₂ → FrontierForgeryBreak H pkSeed skSeed w
  | chainStepCollision (v step : Nat) (x₁ x₂ : BitVec 256) :
      x₁ ≠ x₂ → H.chainStep pkSeed v step x₁ = H.chainStep pkSeed v step x₂ → FrontierForgeryBreak H pkSeed skSeed w
  | unrevealedSubtreeMergePreimage (t v : Nat) (lEnd rEnd : BitVec 256) :
      0 < t → 1 < v → H.mergeNode pkSeed v lEnd rEnd = honestNodeBase H pkSeed skSeed w t v →
      FrontierForgeryBreak H pkSeed skSeed w
  | chainPreimageInversion (t v revStep : Nat) (pre : BitVec 256) :
      0 < revStep → revStep < w →
      H.chainStep pkSeed v (revStep - 1) pre = chainAdvance H pkSeed v 0 revStep (honestNodeBase H pkSeed skSeed w t v) →
      FrontierForgeryBreak H pkSeed skSeed w

def findChainStepCollision (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w v : Nat) :
    (step rem : Nat) → (x₁ x₂ : BitVec 256) → x₁ ≠ x₂ →
    chainAdvance H pkSeed v step rem x₁ = chainAdvance H pkSeed v step rem x₂ →
    FrontierForgeryBreak H pkSeed skSeed w
  | _, 0, _, _, hNe, hAdv => False.elim (hNe hAdv)
  | step, rem + 1, x₁, x₂, hNe, hAdv =>
    let y₁ := H.chainStep pkSeed v step x₁; let y₂ := H.chainStep pkSeed v step x₂
    if hEq : y₁ = y₂ then .chainStepCollision v step x₁ x₂ hNe hEq
    else findChainStepCollision H pkSeed skSeed w v (step + 1) rem y₁ y₂ hEq hAdv

def inspectSplitNode (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w t v : Nat)
    (hv : 0 < v) (lEnd₂ rEnd₂ : BitVec 256)
    (hOut : (let m := H.mergeNode pkSeed v lEnd₂ rEnd₂
             if v > 1 then chainAdvance H pkSeed v 0 (w - 1) m else m) = honestNodeOut H pkSeed skSeed w (t + 1) v) :
    PSum (FrontierForgeryBreak H pkSeed skSeed w)
      (lEnd₂ = honestNodeOut H pkSeed skSeed w t (2 * v) ∧
       rEnd₂ = honestNodeOut H pkSeed skSeed w t (2 * v + 1) ∧
       H.mergeNode pkSeed v lEnd₂ rEnd₂ = honestNodeBase H pkSeed skSeed w (t + 1) v) :=
  let hL := honestNodeOut H pkSeed skSeed w t (2 * v)
  let hR := honestNodeOut H pkSeed skSeed w t (2 * v + 1)
  let m₂ := H.mergeNode pkSeed v lEnd₂ rEnd₂; let m₁ := honestNodeBase H pkSeed skSeed w (t + 1) v
  have hm₁Eq : m₁ = H.mergeNode pkSeed v hL hR := by
    unfold m₁ hL hR honestNodeBase honestNodeOut; simp [show 2 * v > 1 by omega, show 2 * v + 1 > 1 by omega]
  if hmNe : m₂ ≠ m₁ then
    if hvGt : v > 1 then
      .inl (findChainStepCollision H pkSeed skSeed w v 0 (w - 1) m₂ m₁ hmNe
        (by unfold honestNodeOut at hOut; dsimp only [m₂, m₁] at *; simp [hvGt] at hOut; exact hOut))
    else False.elim (hmNe (by unfold honestNodeOut at hOut; dsimp only [m₂, m₁] at *; simp [hvGt] at hOut; exact hOut))
  else
    have hmEq := Decidable.of_not_not hmNe
    if hlNe : lEnd₂ ≠ hL then .inl (.merkleCollision v lEnd₂ rEnd₂ hL hR (.inl hlNe) (hmEq.trans hm₁Eq))
    else if hrNe : rEnd₂ ≠ hR then .inl (.merkleCollision v lEnd₂ rEnd₂ hL hR (.inr hrNe) (hmEq.trans hm₁Eq))
    else .inr ⟨Decidable.of_not_not hlNe, Decidable.of_not_not hrNe, hmEq⟩

def extractAntichainDiffBreak (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) :
    (t v : Nat) → (tr₁ tr₂ : AntichainTree) → (offs₂ : List Nat) → (vals₂ : List (BitVec 256)) →
    0 < v → (tr₁ = .leaf → 1 < v) → tr₂.Valid t = true → tr₁.size ≤ tr₂.size → tr₁ ≠ tr₂ →
    evalAntichainTree H pkSeed w v tr₂ offs₂ vals₂ = honestNodeOut H pkSeed skSeed w t v →
    FrontierForgeryBreak H pkSeed skSeed w
  | _, _, .leaf, .leaf, _, _, _, _, _, _, hNe, _ => False.elim (hNe rfl)
  | _, _, .split l₁ r₁, .leaf, _, _, _, _, _, hSz, _, _ =>
    False.elim (by have := l₁.size_pos; have := r₁.size_pos; unfold AntichainTree.size at hSz; omega)
  | 0, _, _, .split _ _, _, _, _, _, hV, _, _, _ => False.elim (by simp [AntichainTree.Valid] at hV)
  | t + 1, v, .leaf, .split l₂ r₂, offs₂, vals₂, hv, hvGt, _, _, _, hEv =>
    let lEnd₂ := evalAntichainTree H pkSeed w (2 * v) l₂ (offs₂.take l₂.size) (vals₂.take l₂.size)
    let rEnd₂ := evalAntichainTree H pkSeed w (2 * v + 1) r₂ (offs₂.drop l₂.size) (vals₂.drop l₂.size)
    match inspectSplitNode H pkSeed skSeed w t v hv lEnd₂ rEnd₂ hEv with
    | .inl brk => brk
    | .inr ⟨_, _, hmEq⟩ => .unrevealedSubtreeMergePreimage (t + 1) v lEnd₂ rEnd₂ (Nat.zero_lt_succ t) (hvGt rfl) hmEq
  | t + 1, v, .split l₁ r₁, .split l₂ r₂, offs₂, vals₂, hv, _, hV, hSz, hNe, hEv =>
    have hVSub := band_eq_true hV
    let lEnd₂ := evalAntichainTree H pkSeed w (2 * v) l₂ (offs₂.take l₂.size) (vals₂.take l₂.size)
    let rEnd₂ := evalAntichainTree H pkSeed w (2 * v + 1) r₂ (offs₂.drop l₂.size) (vals₂.drop l₂.size)
    match inspectSplitNode H pkSeed skSeed w t v hv lEnd₂ rEnd₂ hEv with
    | .inl brk => brk
    | .inr ⟨hLEq, hREq, _⟩ =>
      if hlLt : l₁.size < l₂.size then
        extractAntichainDiffBreak H pkSeed skSeed w t (2 * v) l₁ l₂ (offs₂.take l₂.size) (vals₂.take l₂.size)
          (by omega) (fun _ => by omega) hVSub.1 (Nat.le_of_lt hlLt) (fun e => by rw [e] at hlLt; omega) hLEq
      else if hrLt : r₁.size < r₂.size then
        extractAntichainDiffBreak H pkSeed skSeed w t (2 * v + 1) r₁ r₂ (offs₂.drop l₂.size) (vals₂.drop l₂.size)
          (by omega) (fun _ => by omega) hVSub.2 (Nat.le_of_lt hrLt) (fun e => by rw [e] at hrLt; omega) hREq
      else if hlNe : l₁ ≠ l₂ then
        extractAntichainDiffBreak H pkSeed skSeed w t (2 * v) l₁ l₂ (offs₂.take l₂.size) (vals₂.take l₂.size)
          (by omega) (fun _ => by omega) hVSub.1 (by unfold AntichainTree.size at hSz; omega) hlNe hLEq
      else
        extractAntichainDiffBreak H pkSeed skSeed w t (2 * v + 1) r₁ r₂ (offs₂.drop l₂.size) (vals₂.drop l₂.size)
          (by omega) (fun _ => by omega) hVSub.2 (by unfold AntichainTree.size at hSz; omega)
          (fun hrEq => hNe (by rw [Decidable.of_not_not hlNe, hrEq])) hREq

def extractOffsetDiffBreak (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) :
    (t v : Nat) → (tr : AntichainTree) → (offs₁ offs₂ : List Nat) → (vals₂ : List (BitVec 256)) →
    0 < v → (tr = .leaf → 1 < v) → tr.Valid t = true →
    (hOL₁ : offs₁.length = tr.size) → (hOL₂ : offs₂.length = tr.size) → vals₂.length = tr.size →
    (∀ a ∈ offs₁, a < w) → (idx : Fin offs₂.length) →
    offs₂.get idx < offs₁.get ⟨idx.1, Nat.lt_of_lt_of_eq idx.2 (hOL₂.trans hOL₁.symm)⟩ →
    evalAntichainTree H pkSeed w v tr offs₂ vals₂ = honestNodeOut H pkSeed skSeed w t v →
    FrontierForgeryBreak H pkSeed skSeed w
  | t, v, .leaf, offs₁, offs₂, vals₂, _, hvGt, _, hOL₁, hOL₂, hVL₂, hBnd₁, idx, hLtIdx, hEval =>
    match offs₁, offs₂, vals₂, hOL₁, hOL₂, hVL₂, idx, hLtIdx, hEval with
    | d₁ :: os₁, d₂ :: _, y :: _, _, _, _, ⟨0, _⟩, hLt0, hEv =>
      have hd₁W : d₁ < w := hBnd₁ d₁ (.head os₁); have hd₂Lt : d₂ < d₁ := hLt0; have hv1 : v > 1 := hvGt rfl
      let pre := chainAdvance H pkSeed v d₂ (d₁ - 1 - d₂) y
      let yAtD1 := H.chainStep pkSeed v (d₁ - 1) pre
      let honestD1 := chainAdvance H pkSeed v 0 d₁ (honestNodeBase H pkSeed skSeed w t v)
      have hyStep : chainAdvance H pkSeed v d₂ (d₁ - d₂) y = yAtD1 := by
        rw [show d₁ - d₂ = (d₁ - 1 - d₂) + 1 by omega, chainAdvance_add]
        simp [chainAdvance, show d₂ + (d₁ - 1 - d₂) = d₁ - 1 by omega, pre, yAtD1]
      if hHit : yAtD1 = honestD1 then .chainPreimageInversion t v d₁ pre (by omega) hd₁W hHit
      else
        findChainStepCollision H pkSeed skSeed w v d₁ (w - 1 - d₁) yAtD1 honestD1 hHit (by
          unfold evalAntichainTree honestNodeOut at hEv; simp only [List.headD_cons, hv1, ↓reduceIte] at hEv
          have hAdd₂ := chainAdvance_add H pkSeed v d₂ (d₁ - d₂) (w - 1 - d₁) y
          have hAdd₁ := chainAdvance_add H pkSeed v 0 d₁ (w - 1 - d₁) (honestNodeBase H pkSeed skSeed w t v)
          rw [show (d₁ - d₂) + (w - 1 - d₁) = w - 1 - d₂ by omega, show d₂ + (d₁ - d₂) = d₁ by omega, hyStep] at hAdd₂
          rw [show d₁ + (w - 1 - d₁) = w - 1 by omega, Nat.zero_add] at hAdd₁
          exact hAdd₂.symm.trans (hEv.trans hAdd₁))
    | _ :: _, _ :: os₂, _, _, hOL₂, _, ⟨_ + 1, hk⟩, _, _ =>
      False.elim (by have h0 : os₂.length = 0 := Nat.succ.inj hOL₂; rw [List.length_cons, h0] at hk; omega)
  | 0, _, .split _ _, _, _, _, _, _, hV, _, _, _, _, _, _, _ => False.elim (by simp [AntichainTree.Valid] at hV)
  | t + 1, v, .split l r, offs₁, offs₂, vals₂, hv, _, hV, hOL₁, hOL₂, hVL₂, hBnd₁, idx, hLtIdx, hEv =>
    have hVSub := band_eq_true hV
    let lEnd₂ := evalAntichainTree H pkSeed w (2 * v) l (offs₂.take l.size) (vals₂.take l.size)
    let rEnd₂ := evalAntichainTree H pkSeed w (2 * v + 1) r (offs₂.drop l.size) (vals₂.drop l.size)
    match inspectSplitNode H pkSeed skSeed w t v hv lEnd₂ rEnd₂ hEv with
    | .inl brk => brk
    | .inr ⟨hLEq, hREq, _⟩ =>
      if hInL : idx.1 < l.size then
        have hTk2 : (offs₂.take l.size).length = l.size :=
          length_take_eq offs₂ l.size (by unfold AntichainTree.size at hOL₂; omega)
        extractOffsetDiffBreak H pkSeed skSeed w t (2 * v) l (offs₁.take l.size) (offs₂.take l.size) (vals₂.take l.size)
          (by omega) (fun _ => by omega) hVSub.1
          (length_take_eq offs₁ l.size (by unfold AntichainTree.size at hOL₁; omega))
          hTk2
          (length_take_eq vals₂ l.size (by unfold AntichainTree.size at hVL₂; omega))
          (fun a ha => hBnd₁ a (List.mem_of_mem_take ha))
          ⟨idx.1, hTk2.symm ▸ hInL⟩
          (by simp only [List.get_eq_getElem, List.getElem_take]; exact hLtIdx) hLEq
      else
        have hDp2 : (offs₂.drop l.size).length = r.size := by
          rw [List.length_drop]; unfold AntichainTree.size at hOL₂; omega
        extractOffsetDiffBreak H pkSeed skSeed w t (2 * v + 1) r (offs₁.drop l.size) (offs₂.drop l.size) (vals₂.drop l.size)
          (by omega) (fun _ => by omega) hVSub.2
          (by rw [List.length_drop]; unfold AntichainTree.size at hOL₁; omega)
          hDp2
          (by rw [List.length_drop]; unfold AntichainTree.size at hVL₂; omega)
          (fun a ha => hBnd₁ a (List.mem_of_mem_drop ha))
          ⟨idx.1 - l.size, by rw [hDp2]; unfold AntichainTree.size at hOL₂; omega⟩
          (by simp only [List.get_eq_getElem, List.getElem_drop]
              simpa [show l.size + (idx.1 - l.size) = idx.1 by omega] using hLtIdx) hREq

def extractCompact1122ForgeryBreak (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (sk : FrontierSecretKey)
    (hedge₁ : BitVec 256) (ctr₁ : UInt16) (m₁ : List UInt8) (sig₁ : FrontierSignature)
    (hHonest : signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁)
    (m₂ : List UInt8) (sig₂ : FrontierSignature) (hFresh : m₂ ≠ m₁)
    (hForged : verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true) :
    FrontierForgeryBreak H sk.pkSeed sk.skSeed p.winternitzW :=
  let pk := deriveFrontierPk H p sk
  let d₁ := H.prehashMsg pk.pkSeed pk.root m₁; let d₂ := H.prehashMsg pk.pkSeed pk.root m₂
  let rk₁ := (H.squeezeRank pk.pkSeed pk.root sig₁.randomizer d₁ sig₁.grindCounter).toNat
  let rk₂ := (H.squeezeRank pk.pkSeed pk.root sig₂.randomizer d₂ sig₂.grindCounter).toNat
  if hRkEq : rk₂ = rk₁ then
    if hdEq : d₂ = d₁ then .prehashTcrCollision pk.root m₁ m₂ hFresh hdEq
    else .targetIndexCollision pk.root sig₁.randomizer d₁ sig₁.grindCounter sig₂.randomizer d₂ sig₂.grindCounter (.inr (.inl hdEq)) hRkEq
  else
    have hUnr₁Some : ∃ tr₁ paths₁ offs₁, unrankFrontierFts p rk₁ = some (tr₁, paths₁, offs₁) := by
      unfold signFrontierFts at hHonest
      if hC₁ : ctr₁.toNat >= 2 ^ p.counterBits then
        simp [hC₁] at hHonest
      else
        simp only [hC₁, ↓reduceIte] at hHonest
        cases hU : unrankFrontierFts p (H.squeezeRank pk.pkSeed pk.root (H.prfRand sk.skPrf pk.pkSeed pk.root hedge₁ d₁) d₁ ctr₁).toNat with
        | none => simp [pk, d₁, hU] at hHonest
        | some tp => simp only [pk, d₁, hU, Option.some.injEq] at hHonest; subst hHonest; exact ⟨tp.1, tp.2.1, tp.2.2, hU⟩
    match hU₁ : unrankFrontierFts p rk₁, hU₂ : unrankFrontierFts p rk₂ with
    | none, _ => False.elim (by obtain ⟨_, _, _, h⟩ := hUnr₁Some; rw [h] at hU₁; cases hU₁)
    | _, none => False.elim (by
        unfold verifyFrontierFts at hForged
        if hCL : (sig₂.chainValues.length != p.frontierLen) = true then
          simp [hCL] at hForged
        else
          have hCLF : (sig₂.chainValues.length != p.frontierLen) = false := Bool.eq_false_iff.mpr hCL
          if hC₂ : sig₂.grindCounter.toNat >= 2 ^ p.counterBits then
            simp [hCLF, hC₂] at hForged
          else
            simp [hCLF, hC₂, pk, d₂, rk₂, hU₂] at hForged)
    | some (tr₁, paths₁, offs₁), some (tr₂, paths₂, offs₂) =>
      have hLt₁ := unrankFrontierFts_rank_lt hU₁
      have hLt₂ := unrankFrontierFts_rank_lt hU₂
      have hP₁ : paths₁ = tr₁.frontierNodes 1 ∧ tr₁.Valid p.treeHeight = true ∧ tr₁.size = p.frontierLen ∧
          offs₁.length = p.frontierLen ∧ offs₁.sum = p.targetSum ∧ (∀ a ∈ offs₁, a < p.winternitzW) := by
        obtain ⟨_, _, _, hu, hp, hv, hs, _, hl, hsm, hb, _⟩ := unrankFrontierFts_bijective p rk₁ hLt₁
        rw [hU₁] at hu; injection hu with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
        exact ⟨hp, hv, hs, hl, hsm, hb⟩
      have hP₂ : paths₂ = tr₂.frontierNodes 1 ∧ tr₂.Valid p.treeHeight = true ∧ tr₂.size = p.frontierLen ∧
          offs₂.length = p.frontierLen ∧ offs₂.sum = p.targetSum ∧ (∀ a ∈ offs₂, a < p.winternitzW) := by
        obtain ⟨_, _, _, hu, hp, hv, hs, _, hl, hsm, hb, _⟩ := unrankFrontierFts_bijective p rk₂ hLt₂
        rw [hU₂] at hu; injection hu with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
        exact ⟨hp, hv, hs, hl, hsm, hb⟩
      have hVer : sig₂.chainValues.length = p.frontierLen ∧
          evalAntichainTree H sk.pkSeed p.winternitzW 1 tr₂ offs₂ sig₂.chainValues = pk.root := by
        unfold verifyFrontierFts at hForged
        by_cases hCL : sig₂.chainValues.length != p.frontierLen; · simp [hCL] at hForged
        have hCLEq : sig₂.chainValues.length = p.frontierLen := eq_of_bne_false hCL
        by_cases hC₂ : sig₂.grindCounter.toNat >= 2 ^ p.counterBits; · simp [hCL, hC₂] at hForged
        simp only [hCL, Bool.false_eq_true, ↓reduceIte, hC₂, pk, d₂, rk₂, hU₂] at hForged
        have hLp := runFrontierStackLoop_tree_eq H sk.pkSeed p.winternitzW tr₂ 1 offs₂ sig₂.chainValues
          [] [] [] [] (by decide) (hP₂.2.2.2.1.trans hP₂.2.2.1.symm) (hCLEq.trans hP₂.2.2.1.symm)
        simp only [List.append_nil] at hLp
        have hPkSeedEq : pk.pkSeed = sk.pkSeed := rfl
        rw [hPkSeedEq, hP₂.1, hLp] at hForged
        unfold runFrontierStackLoop collapseFrontierStack at hForged
        exact ⟨hCLEq, of_decide_eq_true hForged⟩
      if hTrNe : tr₁ ≠ tr₂ then
        extractAntichainDiffBreak H sk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr₁ tr₂ offs₂ sig₂.chainValues
          (by decide) (fun hLf => by subst hLf; have := hP₁.2.2.1; unfold AntichainTree.size at this; omega)
          hP₂.2.1 (by omega) hTrNe hVer.2
      else
        have hTrEq := Decidable.of_not_not hTrNe
        have hOffNe : offs₂ ≠ offs₁ := fun hOffEq => hRkEq (unrankFrontierFts_injective p hU₂ hU₁
          ⟨hP₂.1.trans ((congrArg (AntichainTree.frontierNodes 1) hTrEq.symm).trans hP₁.1.symm), hOffEq⟩)
        let idxWit := findSmallerOffsetIdx offs₂ offs₁ (hP₂.2.2.2.1.trans hP₁.2.2.2.1.symm) (by omega) hOffNe
        extractOffsetDiffBreak H sk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr₂ offs₁ offs₂ sig₂.chainValues
          (by decide) (fun hLf => by subst hLf; have := hP₂.2.2.1; unfold AntichainTree.size at this; omega)
          hP₂.2.1 (hP₁.2.2.2.1.trans hP₂.2.2.1.symm) (hP₂.2.2.2.1.trans hP₂.2.2.1.symm)
          (hVer.1.trans hP₂.2.2.1.symm) hP₁.2.2.2.2.2 idxWit.1 idxWit.2 hVer.2

theorem compact1122_one_time_euf_cma_reduction (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (sk : FrontierSecretKey)
    (hedge₁ : BitVec 256) (ctr₁ : UInt16) (m₁ : List UInt8) (sig₁ : FrontierSignature)
    (hHonest : signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁)
    (m₂ : List UInt8) (sig₂ : FrontierSignature) (hFresh : m₂ ≠ m₁)
    (hForged : verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true) :
    Nonempty (FrontierForgeryBreak H sk.pkSeed sk.skSeed p.winternitzW) :=
  ⟨extractCompact1122ForgeryBreak H p hL sk hedge₁ ctr₁ m₁ sig₁ hHonest m₂ sig₂ hFresh hForged⟩

/-! ### §1b. Mechanized `Compact1122` (`w = 96, L = 34, S = 1615`) Target-Sum Antichain & `≤ 1`-Query ROM/QROM EUF-CMA Reduction -/

private theorem sum_replicate_eq : ∀ (n c : Nat), (List.replicate n c).sum = n * c
  | 0, _ => by simp
  | n + 1, c => by
    simp only [List.replicate_succ, List.sum_cons, sum_replicate_eq n c, Nat.succ_mul]
    omega

/-- **Explicit `Compact1122` (`w = 96, L = 34, S = 1615`) Bidirectional Target-Sum Antichain
    (`compact1122_target_sum_antichain`)**:
    1. Any two distinct length-`34` digit vectors `d, d'` in `[0, 96)` with target sum `1615` are
       incomparable (`∃ i < 34, d'[i] < d[i]` and `∃ j < 34, d[j] < d'[j]`), constructively
       forcing at least one strictly backward hash-chain step in every same-antichain forgery, and
    2. Any single length-`34` digit vector `d'` with target sum `1615` satisfies `∃ i < 34, d'[i] < 95`
       (`1615 < 34 * 95 = 3230`), forcing a strictly backward hash-chain step in any 0-query forgery! -/
theorem compact1122_target_sum_antichain :
    (∀ (d d' : List Nat),
      ∀ (hLen : d.length = 34) (hLen' : d'.length = 34),
      (∀ x ∈ d, x < 96) → (∀ x ∈ d', x < 96) →
      d.sum = 1615 → d'.sum = 1615 → d' ≠ d →
      (∃ i : Fin d'.length,
        d'.get i < d.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (by omega)⟩ ∧
        d.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (by omega)⟩ < 96) ∧
      (∃ j : Fin d.length,
        d.get j < d'.get ⟨j.1, Nat.lt_of_lt_of_eq j.2 (by omega)⟩ ∧
        d'.get ⟨j.1, Nat.lt_of_lt_of_eq j.2 (by omega)⟩ < 96)) ∧
    (∀ (d' : List Nat),
      d'.length = 34 → d'.sum = 1615 →
      ∃ i : Fin d'.length, d'.get i < 95) := by
  refine ⟨fun d d' hL hL' hBd hBd' hS hS' hNe => ?_, fun d' hL' hS' => ?_⟩
  · let w₁ := findSmallerOffsetIdx d' d (hL'.trans hL.symm) (by omega) hNe
    let w₂ := findSmallerOffsetIdx d d' (hL.trans hL'.symm) (by omega) (fun e => hNe e.symm)
    exact ⟨⟨w₁.1, w₁.2, hBd _ (List.get_mem _ _)⟩,
           ⟨w₂.1, w₂.2, hBd' _ (List.get_mem _ _)⟩⟩
  · let maxVec := List.replicate 34 95
    have hMaxLen : maxVec.length = 34 := List.length_replicate
    have hMaxSum : maxVec.sum = 3230 := (sum_replicate_eq 34 95).trans (by decide)
    have hNeMax : d' ≠ maxVec := fun hEq => by rw [hEq, hMaxSum] at hS'; cases hS'
    let w := findSmallerOffsetIdx d' maxVec (hL'.trans hMaxLen.symm) (by omega) hNeMax
    refine ⟨w.1, ?_⟩
    have hMem : maxVec.get ⟨w.1.1, Nat.lt_of_lt_of_eq w.1.2 (hL'.trans hMaxLen.symm)⟩ ∈ maxVec :=
      List.get_mem _ _
    have hw := w.2
    rw [(List.mem_replicate.mp hMem).2] at hw
    exact hw

/-- Constructive 0-query (`EUF-NMA`) forgery break extractor for `FrontierSumFts` whenever
    `p.targetSum < p.frontierLen * (p.winternitzW - 1)` (satisfied by both `Compact1122` and `Full256Bit`). -/
def extractCompact1122ZeroQueryBreak (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hSlack : p.targetSum < p.frontierLen * (p.winternitzW - 1))
    (sk : FrontierSecretKey) (m₂ : List UInt8) (sig₂ : FrontierSignature)
    (hForged : verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true) :
    FrontierForgeryBreak H sk.pkSeed sk.skSeed p.winternitzW :=
  let pk := deriveFrontierPk H p sk
  let d₂ := H.prehashMsg pk.pkSeed pk.root m₂
  let rk₂ := (H.squeezeRank pk.pkSeed pk.root sig₂.randomizer d₂ sig₂.grindCounter).toNat
  match hU₂ : unrankFrontierFts p rk₂ with
  | none => False.elim (by
      unfold verifyFrontierFts at hForged
      if hCL : (sig₂.chainValues.length != p.frontierLen) = true then
        simp [hCL] at hForged
      else
        have hCLF : (sig₂.chainValues.length != p.frontierLen) = false := Bool.eq_false_iff.mpr hCL
        if hC₂ : sig₂.grindCounter.toNat >= 2 ^ p.counterBits then
          simp [hCLF, hC₂] at hForged
        else
          simp [hCLF, hC₂, pk, d₂, rk₂, hU₂] at hForged)
  | some (tr₂, paths₂, offs₂) =>
    have hLt₂ := unrankFrontierFts_rank_lt hU₂
    have hP₂ : paths₂ = tr₂.frontierNodes 1 ∧ tr₂.Valid p.treeHeight = true ∧
        tr₂.size = p.frontierLen ∧ 2 ≤ p.frontierLen ∧
        offs₂.length = p.frontierLen ∧ offs₂.sum = p.targetSum ∧
        (∀ a ∈ offs₂, a < p.winternitzW) := by
      obtain ⟨_, _, _, hu, hp, hv, hs, h2L, hl, hsm, hb, _⟩ := unrankFrontierFts_bijective p rk₂ hLt₂
      rw [hU₂] at hu; injection hu with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
      exact ⟨hp, hv, hs, h2L, hl, hsm, hb⟩
    have hVer : sig₂.chainValues.length = p.frontierLen ∧
        evalAntichainTree H sk.pkSeed p.winternitzW 1 tr₂ offs₂ sig₂.chainValues = pk.root := by
      unfold verifyFrontierFts at hForged
      by_cases hCL : sig₂.chainValues.length != p.frontierLen; · simp [hCL] at hForged
      have hCLEq : sig₂.chainValues.length = p.frontierLen := eq_of_bne_false hCL
      by_cases hC₂ : sig₂.grindCounter.toNat >= 2 ^ p.counterBits; · simp [hCL, hC₂] at hForged
      simp only [hCL, Bool.false_eq_true, ↓reduceIte, hC₂, pk, d₂, rk₂, hU₂] at hForged
      have hLp := runFrontierStackLoop_tree_eq H sk.pkSeed p.winternitzW tr₂ 1 offs₂ sig₂.chainValues
        [] [] [] [] (by decide) (hP₂.2.2.2.2.1.trans hP₂.2.2.1.symm) (hCLEq.trans hP₂.2.2.1.symm)
      simp only [List.append_nil] at hLp
      have hPkSeedEq : pk.pkSeed = sk.pkSeed := rfl
      rw [hPkSeedEq, hP₂.1, hLp] at hForged
      unfold runFrontierStackLoop collapseFrontierStack at hForged
      exact ⟨hCLEq, of_decide_eq_true hForged⟩
    let endVec := List.replicate p.frontierLen (p.winternitzW - 1)
    have hEndLen : endVec.length = p.frontierLen := List.length_replicate
    have hEndSum : endVec.sum = p.frontierLen * (p.winternitzW - 1) :=
      sum_replicate_eq p.frontierLen (p.winternitzW - 1)
    have hW2 : 2 ≤ p.winternitzW := by
      cases hw : p.winternitzW with
      | zero => simp [hw] at hSlack
      | succ w' => cases w' with
        | zero => simp [hw] at hSlack
        | succ _ => omega
    have hEndBnd : ∀ a ∈ endVec, a < p.winternitzW := fun a ha => by
      rw [(List.mem_replicate.mp ha).2]; omega
    have hNeEnd : offs₂ ≠ endVec := fun hEq => by
      have hS := hP₂.2.2.2.2.2.1
      rw [hEq, hEndSum] at hS; omega
    let idxWit := findSmallerOffsetIdx offs₂ endVec
      (hP₂.2.2.2.2.1.trans hEndLen.symm) (by rw [hP₂.2.2.2.2.2.1, hEndSum]; exact Nat.le_of_lt hSlack) hNeEnd
    extractOffsetDiffBreak H sk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr₂ endVec offs₂ sig₂.chainValues
      (by decide) (fun hLf => by subst hLf; have := hP₂.2.2.1; unfold AntichainTree.size at this; omega)
      hP₂.2.1 (hEndLen.trans hP₂.2.2.1.symm) (hP₂.2.2.2.2.1.trans hP₂.2.2.1.symm)
      (hVer.1.trans hP₂.2.2.1.symm) hEndBnd idxWit.1 idxWit.2 hVer.2

/-- Unified `≤ 1`-query (`0` or `1` signing query) constructive `FrontierSumFts` EUF-CMA extractor. -/
def extractCompact1122AtMostOneQueryBreak (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (hSlack : p.targetSum < p.frontierLen * (p.winternitzW - 1))
    (sk : FrontierSecretKey)
    (priorQuery : Option (BitVec 256 × UInt16 × List UInt8 × FrontierSignature))
    (hPriorHonest : match priorQuery with
      | none => True
      | some (hedge₁, ctr₁, m₁, sig₁) => signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁)
    (mStar : List UInt8) (sigStar : FrontierSignature)
    (hFresh : match priorQuery with
      | none => True
      | some (_, _, m₁, _) => mStar ≠ m₁)
    (hForged : verifyFrontierFts H p (deriveFrontierPk H p sk) mStar sigStar = true) :
    FrontierForgeryBreak H sk.pkSeed sk.skSeed p.winternitzW :=
  match priorQuery, hPriorHonest, hFresh with
  | none, _, _ => extractCompact1122ZeroQueryBreak H p hSlack sk mStar sigStar hForged
  | some (hedge₁, ctr₁, m₁, sig₁), hHon, hFr =>
    extractCompact1122ForgeryBreak H p hL sk hedge₁ ctr₁ m₁ sig₁ hHon mStar sigStar hFr hForged

/-- Classification of `FrontierForgeryBreak` into its three ROM/QROM reduction events:
    1. `isMsgOrRankTcr`: `TAG_MSG_PRE` TCR collision or `TAG_HMSG` target-rank collision,
    2. `isTreeOrChainCollision`: `TAG_MERGE` Merkle node collision or `TAG_CHAIN` step second-preimage/collision,
    3. `isOneWayPreimage`: `TAG_CHAIN` chain-step inversion at a strictly smaller digit `d'_i < d_i`
       or `TAG_MERGE` unrevealed-subtree preimage. -/
def FrontierForgeryBreak.isMsgOrRankTcr {H : FrontierHashSuite} {pkS skS : BitVec 256} {w : Nat} :
    FrontierForgeryBreak H pkS skS w → Bool
  | .prehashTcrCollision .. | .targetIndexCollision .. => true
  | _ => false

def FrontierForgeryBreak.isTreeOrChainCollision {H : FrontierHashSuite} {pkS skS : BitVec 256} {w : Nat} :
    FrontierForgeryBreak H pkS skS w → Bool
  | .merkleCollision .. | .chainStepCollision .. => true
  | _ => false

def FrontierForgeryBreak.isOneWayPreimage {H : FrontierHashSuite} {pkS skS : BitVec 256} {w : Nat} :
    FrontierForgeryBreak H pkS skS w → Bool
  | .unrevealedSubtreeMergePreimage .. | .chainPreimageInversion .. => true
  | _ => false

theorem FrontierForgeryBreak.exhausts_three_events {H : FrontierHashSuite}
    {pkS skS : BitVec 256} {w : Nat} (b : FrontierForgeryBreak H pkS skS w) :
    b.isMsgOrRankTcr = true ∨ b.isTreeOrChainCollision = true ∨ b.isOneWayPreimage = true := by
  cases b <;> simp [FrontierForgeryBreak.isMsgOrRankTcr,
    FrontierForgeryBreak.isTreeOrChainCollision, FrontierForgeryBreak.isOneWayPreimage]

/-- Closed `≤ 1`-query `FrontierSumFts` (`Compact1122` / `Full256Bit`) EUF-CMA outcome record. -/
structure FrontierOneUseEufCmaOutcome where
  sk : FrontierSecretKey
  prior : Option (BitVec 256 × UInt16 × List UInt8)
  msgStar : List UInt8
  sigStar : FrontierSignature

def frontierOneUseEufCmaWin (H : FrontierHashSuite) (p : FrontierFtsParams)
    (o : FrontierOneUseEufCmaOutcome) : Bool :=
  let fresh := match o.prior with
    | none => true
    | some (hg, ctr, m₁) =>
      match signFrontierFts H p o.sk hg ctr m₁ with
      | none => true
      | some _ => decide (o.msgStar ≠ m₁)
  fresh && verifyFrontierFts H p (deriveFrontierPk H p o.sk) o.msgStar o.sigStar

theorem frontierOneUseEufCmaWin_none (H : FrontierHashSuite) (p : FrontierFtsParams)
    (sk : FrontierSecretKey) (msgStar : List UInt8) (sigStar : FrontierSignature) :
    frontierOneUseEufCmaWin H p ⟨sk, none, msgStar, sigStar⟩ =
      verifyFrontierFts H p (deriveFrontierPk H p sk) msgStar sigStar := by
  unfold frontierOneUseEufCmaWin
  exact Bool.true_and _

/-- **Closed `Spec.GameBound` `Compact1122` Target-Sum EUF-CMA Reduction (`compact1122_closed_euf_cma_gameBound`)**:
    Over any finite coin space `Fin n` (supporting both classical ROM and QROM measurement
    distributions), the `≤ 1`-query `Compact1122` EUF-CMA winning probability is bounded by the
    sum `εTcr + εCol + εPre` of:
    - `TAG_MSG_PRE` / `TAG_HMSG` target-collision probability (`εTcr`),
    - `TAG_MERGE` / `TAG_CHAIN` second-preimage / collision probability (`εCol`), and
    - `TAG_CHAIN` / `TAG_MERGE` one-way chain-inversion / unrevealed-node preimage probability (`εPre`). -/
theorem compact1122_closed_euf_cma_gameBound {n : Nat} (hPos : 0 < n)
    (H : FrontierHashSuite) (game : Fin n → FrontierOneUseEufCmaOutcome)
    (isTcr isCol isPre : Fin n → Bool)
    {εTcr εCol εPre : Spec.RatBound}
    (hClassify : ∀ (ω : Fin n) (brk : FrontierForgeryBreak H (game ω).sk.pkSeed (game ω).sk.skSeed 96),
      (brk.isMsgOrRankTcr = true → isTcr ω = true) ∧
      (brk.isTreeOrChainCollision = true → isCol ω = true) ∧
      (brk.isOneWayPreimage = true → isPre ω = true))
    (hBTcr : Spec.GameBound (Spec.FinGame.mk hPos isTcr).winProb εTcr)
    (hBCol : Spec.GameBound (Spec.FinGame.mk hPos isCol).winProb εCol)
    (hBPre : Spec.GameBound (Spec.FinGame.mk hPos isPre).winProb εPre) :
    Spec.GameBound
      (Spec.FinGame.mk hPos (fun ω => frontierOneUseEufCmaWin H compact1122Params (game ω))).winProb
      ((εTcr.add εCol).add εPre) := by
  refine Spec.event_le_three_reductions
    (Spec.FinGame.mk hPos (fun ω => frontierOneUseEufCmaWin H compact1122Params (game ω)))
    (Spec.FinGame.mk hPos isTcr) (Spec.FinGame.mk hPos isCol) (Spec.FinGame.mk hPos isPre)
    (fun ω hWin => ?_) hBTcr hBCol hBPre
  have hWinU : frontierOneUseEufCmaWin H compact1122Params (game ω) = true := hWin
  unfold frontierOneUseEufCmaWin at hWinU
  obtain ⟨hFrBool, hVer⟩ := band_eq_true hWinU
  have hL : 2 ≤ compact1122Params.frontierLen := by decide
  have hSl : compact1122Params.targetSum <
      compact1122Params.frontierLen * (compact1122Params.winternitzW - 1) := by decide
  have hBrk : Nonempty (FrontierForgeryBreak H (game ω).sk.pkSeed (game ω).sk.skSeed 96) := by
    cases hPr : (game ω).prior with
    | none =>
      exact ⟨extractCompact1122ZeroQueryBreak H compact1122Params hSl (game ω).sk
        (game ω).msgStar (game ω).sigStar hVer⟩
    | some q =>
      obtain ⟨hg, ctr, m₁⟩ := q
      cases hSign : signFrontierFts H compact1122Params (game ω).sk hg ctr m₁ with
      | none =>
        exact ⟨extractCompact1122ZeroQueryBreak H compact1122Params hSl (game ω).sk
          (game ω).msgStar (game ω).sigStar hVer⟩
      | some sig₁ =>
        simp only [hPr, hSign] at hFrBool
        exact ⟨extractCompact1122ForgeryBreak H compact1122Params hL (game ω).sk hg ctr m₁ sig₁
          hSign (game ω).msgStar (game ω).sigStar (of_decide_eq_true hFrBool) hVer⟩
  obtain ⟨brk⟩ := hBrk
  obtain ⟨c1, c2, c3⟩ := hClassify ω brk
  rcases brk.exhausts_three_events with e1 | e2 | e3
  · exact .inl (c1 e1)
  · exact .inr (.inl (c2 e2))
  · exact .inr (.inr (c3 e3))

/-- Concrete `Keccak-f[1600]` `cshake256_framed_xof` lifting of `FrontierForgeryBreak` under
    `cshakeFrontierHashSuite p`: every collision case yields distinct length-framed `cSHAKE256`
    preimages with equal 256-bit sponge digests (under `v, step < 2^64`, `msg.length < 2^64`). -/
theorem compact1122_cshake256_concrete_break_lift (p : FrontierFtsParams) (pkSeed skSeed : BitVec 256)
    (brk : FrontierForgeryBreak (cshakeFrontierHashSuite p) pkSeed skSeed p.winternitzW) :
    (match brk with
     | .prehashTcrCollision pkR m₁ m₂ _ _ =>
       m₁.length < 256 ^ 8 → m₂.length < 256 ^ 8 →
         ftsPrehashFrames p pkSeed pkR m₂ ≠ ftsPrehashFrames p pkSeed pkR m₁ ∧
         evalFtsCshake256_32 ftsTagMsgPre (ftsPrehashFrames p pkSeed pkR m₂) =
           evalFtsCshake256_32 ftsTagMsgPre (ftsPrehashFrames p pkSeed pkR m₁)
     | .targetIndexCollision pkR r₁ d₁ c₁ r₂ d₂ c₂ _ _ =>
       ftsSqueezeRankFrames p pkSeed pkR r₂ d₂ c₂ ≠ ftsSqueezeRankFrames p pkSeed pkR r₁ d₁ c₁ ∧
       evalFtsCshake256_32 ftsTagHmsg (ftsSqueezeRankFrames p pkSeed pkR r₂ d₂ c₂) =
         evalFtsCshake256_32 ftsTagHmsg (ftsSqueezeRankFrames p pkSeed pkR r₁ d₁ c₁)
     | .merkleCollision v l₁ r₁ l₂ r₂ _ _ =>
       v < 256 ^ 8 →
         ftsMergeNodeFrames p pkSeed v l₁ r₁ ≠ ftsMergeNodeFrames p pkSeed v l₂ r₂ ∧
         evalFtsCshake256_32 ftsTagMerge (ftsMergeNodeFrames p pkSeed v l₁ r₁) =
           evalFtsCshake256_32 ftsTagMerge (ftsMergeNodeFrames p pkSeed v l₂ r₂)
     | .chainStepCollision v step x₁ x₂ _ _ =>
       v < 256 ^ 8 → step < 256 ^ 8 →
         ftsChainStepFrames p pkSeed v step x₁ ≠ ftsChainStepFrames p pkSeed v step x₂ ∧
         evalFtsCshake256_32 ftsTagChain (ftsChainStepFrames p pkSeed v step x₁) =
           evalFtsCshake256_32 ftsTagChain (ftsChainStepFrames p pkSeed v step x₂)
     | .unrevealedSubtreeMergePreimage t v lEnd rEnd _ _ _ =>
       evalFtsCshake256_32 ftsTagMerge (ftsMergeNodeFrames p pkSeed v lEnd rEnd) =
         honestNodeBase (cshakeFrontierHashSuite p) pkSeed skSeed p.winternitzW t v
     | .chainPreimageInversion t v revStep pre _ _ _ =>
       evalFtsCshake256_32 ftsTagChain (ftsChainStepFrames p pkSeed v (revStep - 1) pre) =
         chainAdvance (cshakeFrontierHashSuite p) pkSeed v 0 revStep
           (honestNodeBase (cshakeFrontierHashSuite p) pkSeed skSeed p.winternitzW t v)) := by
  cases brk with
  | prehashTcrCollision pkR m₁ m₂ hNe hEq =>
    intro hm₁ hm₂
    exact ⟨fun hF => hNe (ftsPrehashFrames_injective p hm₂ hm₁ hF).2.2, hEq⟩
  | targetIndexCollision pkR r₁ d₁ c₁ r₂ d₂ c₂ hDiff hToNat =>
    refine ⟨fun hF => ?_, BitVec.eq_of_toNat_eq hToNat⟩
    obtain ⟨hc, _, _, hr, hd⟩ := ftsSqueezeRankFrames_injective p hF
    rcases hDiff with h | h | h
    · exact h hr
    · exact h hd
    · exact h hc
  | merkleCollision v l₁ r₁ l₂ r₂ hDiff hEq =>
    intro hv
    refine ⟨fun hF => ?_, hEq⟩
    obtain ⟨_, _, hl, hr⟩ := ftsMergeNodeFrames_injective p hv hv hF
    rcases hDiff with h | h
    · exact h hl
    · exact h hr
  | chainStepCollision v step x₁ x₂ hNe hEq =>
    intro hv hs
    exact ⟨fun hF => hNe (ftsChainStepFrames_injective p hv hs hv hs hF).2.2.2, hEq⟩
  | unrevealedSubtreeMergePreimage _ _ _ _ _ _ hEq => exact hEq
  | chainPreimageInversion _ _ _ _ _ _ hEq => exact hEq

/-! ## §2. `RotatedEpochVote` Forward-Secure Key-Chain Induction (`rotatedEpochVote_forward_secure_chain`) -/

structure EpochKeyLink where
  epoch : UInt64
  nextEpochPkRoot : BitVec 256
  deriving DecidableEq, Repr

structure RotatedEpochVote where
  link : EpochKeyLink
  voteDigest : BitVec 256
  signature : FrontierSignature
  deriving DecidableEq, Repr
abbrev EpochVoteHasher := BitVec 256 → UInt64 → BitVec 256 → BitVec 256 → List UInt8

/-- Exact length-framed `EpochKeyLink::message` preimage (`crates/qsag-fts/src/frontier.rs:649-661`):
    `cshake256_framed_xof("QSAG.FTS.EPOCH.VOTE.V1", &[chain_id, &epoch.to_be_bytes(), vote_digest, &next_epoch_pk_root])`. -/
def encodeEpochVoteInput (chainId : BitVec 256) (ep : UInt64) (voteDigest nextPkRoot : BitVec 256) : List UInt8 :=
  encodeCshakeFrames [bv256BytesBE chainId, u64BytesBE ep, bv256BytesBE voteDigest, bv256BytesBE nextPkRoot]

theorem encodeEpochVoteInput_injective {c₁ c₂ : BitVec 256} {ep₁ ep₂ : UInt64}
    {d₁ d₂ r₁ r₂ : BitVec 256}
    (hEq : encodeEpochVoteInput c₁ ep₁ d₁ r₁ = encodeEpochVoteInput c₂ ep₂ d₂ r₂) :
    c₁ = c₂ ∧ ep₁ = ep₂ ∧ d₁ = d₂ ∧ r₁ = r₂ := by
  have hLen8 : ∀ x : UInt64, (u64BytesBE x).length < 256 ^ 8 := fun x => by
    rw [u64BytesBE, fixedBytesBE_length]; decide +kernel
  have hL := encodeCshakeFrames_injective
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact len_bv256_lt_u64 c₁
        · exact hLen8 ep₁
        · exact len_bv256_lt_u64 d₁
        · exact len_bv256_lt_u64 r₁)
    (by intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact len_bv256_lt_u64 c₂
        · exact hLen8 ep₂
        · exact len_bv256_lt_u64 d₂
        · exact len_bv256_lt_u64 r₂) hEq
  simp only [List.cons.injEq, and_true] at hL
  have h64 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide +kernel
  have hepNat := fixedBytesBE_injective (h64 ▸ ep₁.toBitVec.isLt) (h64 ▸ ep₂.toBitVec.isLt) hL.2.1
  exact ⟨bv256BytesBE_injective hL.1, UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hepNat),
    bv256BytesBE_injective hL.2.2.1, bv256BytesBE_injective hL.2.2.2⟩

/-- Real `cSHAKE256("QSAG.FTS.EPOCH.VOTE.V1")` 32-byte vote message hasher matching `EpochKeyLink::message`. -/
def cshakeEpochVoteHasher : EpochVoteHasher := fun chainId ep voteDigest nextPkRoot =>
  evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes
    [] ftsTagEpochVote (encodeEpochVoteInput chainId ep voteDigest nextPkRoot) 32

def verifyRotatedEpochVote (H : FrontierHashSuite) (p : FrontierFtsParams)
    (voteHash : EpochVoteHasher) (chainId : BitVec 256)
    (currentPk : FrontierPublicKey) (expectedEpoch : UInt64)
    (expectedDigest : BitVec 256) (vote : RotatedEpochVote) : Option FrontierPublicKey :=
  if p.nodeBytes != 32 || p.maxSafeUses != 1 then none
  else if vote.link.epoch != expectedEpoch || expectedEpoch.toNat + 1 >= 2 ^ 64 then none
  else if vote.voteDigest != expectedDigest then none
  else if verifyFrontierFts H p currentPk
            (voteHash chainId vote.link.epoch vote.voteDigest vote.link.nextEpochPkRoot) vote.signature then
    some ⟨currentPk.pkSeed, vote.link.nextEpochPkRoot⟩
  else none

def verifyRotatedEpochChain (H : FrontierHashSuite) (p : FrontierFtsParams)
    (voteHash : EpochVoteHasher) (chainId : BitVec 256) :
    FrontierPublicKey → Nat → List (BitVec 256) → List RotatedEpochVote → Option FrontierPublicKey
  | curPk, _, [], [] => some curPk
  | curPk, ep, d :: ds, v :: vs =>
    if ep >= 2 ^ 64 then none
    else match verifyRotatedEpochVote H p voteHash chainId curPk (UInt64.ofNat ep) d v with
      | none => none
      | some nextPk => verifyRotatedEpochChain H p voteHash chainId nextPk (ep + 1) ds vs
  | _, _, _, _ => none

inductive EpochChainHistoricalBreak (H : FrontierHashSuite) (voteHash : EpochVoteHasher)
    (pkSeed : BitVec 256) (w : Nat) : Type where
  | voteFramingCollision (chainId : BitVec 256) (ep : UInt64) (d₁ r₁ d₂ r₂ : BitVec 256) :
      (d₂ ≠ d₁ ∨ r₂ ≠ r₁) → voteHash chainId ep d₂ r₂ = voteHash chainId ep d₁ r₁ →
      EpochChainHistoricalBreak H voteHash pkSeed w
  | epochKeyBreak (histEpoch : Nat) (skSeedAtEpoch : BitVec 256) :
      FrontierForgeryBreak H pkSeed skSeedAtEpoch w → EpochChainHistoricalBreak H voteHash pkSeed w

structure HonestEpochRecord where
  sk : FrontierSecretKey
  hedge : BitVec 256
  ctr : UInt16
  voteDigest : BitVec 256
  nextPkRoot : BitVec 256
  vote : RotatedEpochVote

def HonestEpochRecord.ValidAt (H : FrontierHashSuite) (p : FrontierFtsParams)
    (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) (ep : Nat) (rec_ : HonestEpochRecord) : Prop :=
  rec_.sk.pkSeed = pkSeed ∧ rec_.vote.link = ⟨UInt64.ofNat ep, rec_.nextPkRoot⟩ ∧
  rec_.vote.voteDigest = rec_.voteDigest ∧
  signFrontierFts H p rec_.sk rec_.hedge rec_.ctr
    (voteHash chainId (UInt64.ofNat ep) rec_.voteDigest rec_.nextPkRoot) = some rec_.vote.signature

private theorem verifyRotatedEpochVote_eq_some
    {H : FrontierHashSuite} {p : FrontierFtsParams} {voteHash : EpochVoteHasher}
    {chainId : BitVec 256} {curPk npk : FrontierPublicKey}
    {ep : UInt64} {d : BitVec 256} {v : RotatedEpochVote}
    (hV : verifyRotatedEpochVote H p voteHash chainId curPk ep d v = some npk) :
    v.link.epoch = ep ∧ v.voteDigest = d ∧
    verifyFrontierFts H p curPk (voteHash chainId ep d v.link.nextEpochPkRoot) v.signature = true ∧
    npk = ⟨curPk.pkSeed, v.link.nextEpochPkRoot⟩ := by
  unfold verifyRotatedEpochVote at hV
  cases c1 : (p.nodeBytes != 32 || p.maxSafeUses != 1)
  · simp only [c1, Bool.false_eq_true, ↓reduceIte] at hV
    cases c2 : (v.link.epoch != ep || decide (ep.toNat + 1 >= 2 ^ 64))
    · simp only [c2, Bool.false_eq_true, ↓reduceIte] at hV
      cases c3 : (v.voteDigest != d)
      · simp only [c3, Bool.false_eq_true, ↓reduceIte] at hV
        have hEp : v.link.epoch = ep := eq_of_bne_false (fun hT => by rw [hT] at c2; cases c2)
        have hDig : v.voteDigest = d := eq_of_bne_false (fun hT => by rw [hT] at c3; cases c3)
        cases c4 : verifyFrontierFts H p curPk (voteHash chainId v.link.epoch v.voteDigest v.link.nextEpochPkRoot) v.signature
        · rw [c4] at hV; cases hV
        · simp only [c4, ↓reduceIte] at hV
          injection hV with hNpk
          rw [hEp, hDig] at c4
          exact ⟨hEp, hDig, c4, hNpk.symm⟩
      · rw [c3] at hV; cases hV
    · rw [c2] at hV; cases hV
  · rw [c1] at hV; cases hV

def extractRotatedEpochVoteChainBreak (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) :
    (startEp : Nat) → (histRecords : List HonestEpochRecord) →
    (advDigests : List (BitVec 256)) → (advVotes : List RotatedEpochVote) →
    (anchorPk finalPk : FrontierPublicKey) →
    (hLen1 : histRecords.length = advDigests.length) → (hLen2 : advDigests.length = advVotes.length) →
    (∀ idx : Fin histRecords.length, (histRecords.get idx).ValidAt H p voteHash chainId pkSeed (startEp + idx.1)) →
    (∀ r₀, histRecords.head? = some r₀ → anchorPk = deriveFrontierPk H p r₀.sk) →
    (∀ i : Fin histRecords.length, ∀ rNext, histRecords[i.1 + 1]? = some rNext →
      (histRecords.get i).nextPkRoot = (deriveFrontierPk H p rNext.sk).root) →
    verifyRotatedEpochChain H p voteHash chainId anchorPk startEp advDigests advVotes = some finalPk →
    (∃ i : Fin histRecords.length,
      advDigests.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
      (advVotes.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠
        (histRecords.get i).nextPkRoot) →
    EpochChainHistoricalBreak H voteHash pkSeed p.winternitzW
  | _, [], _, _, _, _, _, _, _, _, _, _, hDev => False.elim (by obtain ⟨⟨_, hi⟩, _⟩ := hDev; exact nomatch hi)
  | startEp, r₀ :: rs, dAdv :: dsAdv, vAdv :: vsAdv, anchorPk, finalPk,
    hLen1, hLen2, hVal, hAnchor, hLink, hChainAcc, hDev =>
    have hr₀Val : r₀.ValidAt H p voteHash chainId pkSeed startEp := by simpa using hVal ⟨0, Nat.zero_lt_succ _⟩
    have hAncEq : anchorPk = deriveFrontierPk H p r₀.sk := hAnchor r₀ rfl
    have hStepAcc : ∃ npk, verifyRotatedEpochVote H p voteHash chainId anchorPk (UInt64.ofNat startEp) dAdv vAdv = some npk ∧
        verifyRotatedEpochChain H p voteHash chainId npk (startEp + 1) dsAdv vsAdv = some finalPk := by
      unfold verifyRotatedEpochChain at hChainAcc
      if hEpB : startEp >= 2 ^ 64 then
        simp [hEpB] at hChainAcc
      else
        simp only [hEpB, ↓reduceIte] at hChainAcc
        match hV : verifyRotatedEpochVote H p voteHash chainId anchorPk (UInt64.ofNat startEp) dAdv vAdv with
        | none => rw [hV] at hChainAcc; cases hChainAcc
        | some npk => rw [hV] at hChainAcc; exact ⟨npk, rfl, hChainAcc⟩
    if hHeadDiff : dAdv ≠ r₀.voteDigest ∨ vAdv.link.nextEpochPkRoot ≠ r₀.nextPkRoot then
      have hVerStep : verifyFrontierFts H p (deriveFrontierPk H p r₀.sk)
          (voteHash chainId (UInt64.ofNat startEp) dAdv vAdv.link.nextEpochPkRoot) vAdv.signature = true := by
        obtain ⟨_, hV, _⟩ := hStepAcc
        rw [hAncEq] at hV
        exact (verifyRotatedEpochVote_eq_some hV).2.2.1
      let m₁ := voteHash chainId (UInt64.ofNat startEp) r₀.voteDigest r₀.nextPkRoot
      let m₂ := voteHash chainId (UInt64.ofNat startEp) dAdv vAdv.link.nextEpochPkRoot
      if hMEq : m₂ = m₁ then
        .voteFramingCollision chainId (UInt64.ofNat startEp) r₀.voteDigest r₀.nextPkRoot dAdv vAdv.link.nextEpochPkRoot hHeadDiff hMEq
      else
        .epochKeyBreak startEp r₀.sk.skSeed (hr₀Val.1 ▸ extractCompact1122ForgeryBreak H p hL r₀.sk r₀.hedge r₀.ctr
          m₁ r₀.vote.signature hr₀Val.2.2.2 m₂ vAdv.signature hMEq hVerStep)
    else
      have hSame0 : dAdv = r₀.voteDigest ∧ vAdv.link.nextEpochPkRoot = r₀.nextPkRoot :=
        ⟨Decidable.of_not_not (fun h1 => hHeadDiff (.inl h1)), Decidable.of_not_not (fun h2 => hHeadDiff (.inr h2))⟩
      have hNextPkEq : ∀ npk, verifyRotatedEpochVote H p voteHash chainId anchorPk (UInt64.ofNat startEp) dAdv vAdv = some npk →
          npk = ⟨pkSeed, r₀.nextPkRoot⟩ := by
        intro npk hV
        have hEqNpk := (verifyRotatedEpochVote_eq_some hV).2.2.2
        rw [hEqNpk, hAncEq, hSame0.2]
        unfold deriveFrontierPk
        rw [hr₀Val.1]
      extractRotatedEpochVoteChainBreak H p hL voteHash chainId pkSeed (startEp + 1) rs dsAdv vsAdv
        ⟨pkSeed, r₀.nextPkRoot⟩ finalPk (Nat.succ.inj hLen1) (Nat.succ.inj hLen2)
        (fun j => by simpa [Nat.add_assoc, Nat.add_comm 1 j.1] using hVal ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun r₁ hr₁ => by
          cases rs with
          | nil => cases hr₁
          | cons hd tl =>
            injection hr₁ with hE; rw [← hE]
            have hL0 := hLink ⟨0, Nat.zero_lt_succ _⟩ hd rfl
            have hV1 : hd.ValidAt H p voteHash chainId pkSeed (startEp + 1) := by
              simpa using hVal ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
            unfold deriveFrontierPk at hL0 ⊢
            rw [FrontierPublicKey.mk.injEq]
            exact ⟨hV1.1.symm, hL0⟩)
        (fun j rNext hNxt => hLink ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ rNext hNxt)
        (by obtain ⟨npk, hV, hRest⟩ := hStepAcc; rw [hNextPkEq npk hV] at hRest; exact hRest)
        (by obtain ⟨⟨idx, hIdx⟩, hD⟩ := hDev
            cases idx with
            | zero => exact False.elim (hHeadDiff hD)
            | succ j => exact ⟨⟨j, Nat.lt_of_succ_lt_succ hIdx⟩, hD⟩)

theorem rotatedEpochVote_forward_secure_chain (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256)
    (startEp : Nat) (histRecords : List HonestEpochRecord)
    (advDigests : List (BitVec 256)) (advVotes : List RotatedEpochVote)
    (anchorPk finalPk : FrontierPublicKey)
    (hLen1 : histRecords.length = advDigests.length) (hLen2 : advDigests.length = advVotes.length)
    (hVal : ∀ idx : Fin histRecords.length, (histRecords.get idx).ValidAt H p voteHash chainId pkSeed (startEp + idx.1))
    (hAnchor : ∀ r₀, histRecords.head? = some r₀ → anchorPk = deriveFrontierPk H p r₀.sk)
    (hLink : ∀ i : Fin histRecords.length, ∀ rNext, histRecords[i.1 + 1]? = some rNext →
      (histRecords.get i).nextPkRoot = (deriveFrontierPk H p rNext.sk).root)
    (hAcc : verifyRotatedEpochChain H p voteHash chainId anchorPk startEp advDigests advVotes = some finalPk)
    (hDev : ∃ i : Fin histRecords.length,
      advDigests.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
      (advVotes.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠ (histRecords.get i).nextPkRoot) :
    Nonempty (EpochChainHistoricalBreak H voteHash pkSeed p.winternitzW) :=
  ⟨extractRotatedEpochVoteChainBreak H p hL voteHash chainId pkSeed startEp histRecords advDigests advVotes
    anchorPk finalPk hLen1 hLen2 hVal hAnchor hLink hAcc hDev⟩

/-- Under the real `cshakeEpochVoteHasher` (`cSHAKE256("QSAG.FTS.EPOCH.VOTE.V1")`), any
    `voteFramingCollision` is an explicit `Keccak-f[1600]` `cSHAKE256` collision on two distinct
    104-byte vote payloads; otherwise a historical-epoch `FrontierForgeryBreak` is extracted. -/
theorem rotatedEpochVote_cshake_chain_reduction (H : FrontierHashSuite) (p : FrontierFtsParams)
    (_chainId pkSeed : BitVec 256)
    (brk : EpochChainHistoricalBreak H cshakeEpochVoteHasher pkSeed p.winternitzW) :
    (∃ m₁ m₂ : List UInt8, m₂ ≠ m₁ ∧
      evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes [] ftsTagEpochVote m₂ 32 =
      evalCshake256Sponge keccakF1600 zeroKState xorRate136 rateBlockBytes [] ftsTagEpochVote m₁ 32) ∨
    (∃ (_histEpoch : Nat) (skSeedAtEpoch : BitVec 256),
      Nonempty (FrontierForgeryBreak H pkSeed skSeedAtEpoch p.winternitzW)) := by
  cases brk with
  | voteFramingCollision c ep d₁ r₁ d₂ r₂ hDiff hCol =>
    refine .inl ⟨encodeEpochVoteInput c ep d₁ r₁, encodeEpochVoteInput c ep d₂ r₂, ?_, hCol⟩
    intro hInEq
    obtain ⟨_, _, hdEq, hrEq⟩ := encodeEpochVoteInput_injective hInEq
    rcases hDiff with hdNe | hrNe
    · exact hdNe hdEq
    · exact hrNe hrEq
  | epochKeyBreak histEp skEp fBrk =>
    exact .inr ⟨histEp, skEp, ⟨fBrk⟩⟩

/-! ## §3. `Corduroy` Width-12 `Poseidon2` Stateless Hypertree + `(t, n)` Shamir Power-7 Composition -/

/-- Exact `AggSigProfile::CorduroyPoseidon2` parameters (`crates/qsag-agg/src/sig.rs:31-67`):
    `d = 16` layers, `h' = 4` subtree height (`64`-bit leaf space), `k = 32` FORS trees of height `a = 8`,
    `w = 4, ell1 = 128`, `Q_max = 2^20`, raw signature size `76,896` B. -/
@[expose] def corduroyPoseidon2AggParams : PqHashParams :=
  { w := 4, ell1 := 128, subtreeHeight := 4, numLayers := 16,
    forsTrees := 32, forsHeight := 8, maxSigsLog2 := 20, statefulJorts := false }

/-- Exact wire-byte formula of `AggSigProfile::CorduroyPoseidon2::raw_signature_bytes`
    (`crates/qsag-agg/src/sig.rs:86-90`). -/
@[expose] def corduroyPoseidon2RawSigBytes (p : PqHashParams) : Nat :=
  32 + p.forsTrees * (1 + p.forsHeight) * 32 + p.numLayers * (4 + p.ell1 * 32 + p.subtreeHeight * 32)

/-- Cross-crate audit of both real Rust `Corduroy` parameter profiles:
    1. `corduroyCustody128Params` (`d = 7, h' = 4, h = 28, k = 33, a = 6, Q_max = 2^12`, `tsw_baggy.rs:730`)
       satisfies `productionWellFormed = true`.
    2. `corduroyPoseidon2AggParams` (`d = 16, h' = 4, h = 64, k = 32, a = 8, Q_max = 2^20`, `sig.rs:31-67`)
       has exact wire size `76,896` B and `64`-bit XOF-indexed leaf space, which exceeds the `≤ 62`-bit
       `u64` leaf-index guard in `PqHashParams.productionWellFormed`. -/
theorem corduroy_real_profiles_audit :
    corduroyCustody128Params.numLayers = 7 ∧
    corduroyCustody128Params.subtreeHeight = 4 ∧
    corduroyCustody128Params.productionWellFormed = true ∧
    corduroyPoseidon2AggParams.numLayers = 16 ∧
    corduroyPoseidon2AggParams.subtreeHeight = 4 ∧
    corduroyPoseidon2AggParams.numLayers * corduroyPoseidon2AggParams.subtreeHeight = 64 ∧
    corduroyPoseidon2RawSigBytes corduroyPoseidon2AggParams = 76896 ∧
    corduroyPoseidon2AggParams.productionWellFormed = false :=
  by
    simp only [corduroyCustody128Params_eq, PqHashParams.productionWellFormed_eq,
      corduroyPoseidon2AggParams, corduroyPoseidon2RawSigBytes] <;> decide +kernel

def mkShamirProductionPqHashMpcOracles
    (lambdas : List Goldilocks) (skSeedSh skPrfSh : List (List Goldilocks))
    (pkSeed : List UInt8) (decomp8 : List Goldilocks → List (List Goldilocks))
    (callPrep : Nat → Nat → Poseidon2CallPrep) : ProductionPqHashMpcOracles where
  toPqHashMpcOracles := mkShamirPoseidon2MpcOracles lambdas skSeedSh skPrfSh pkSeed decomp8 callPrep
  evalIndexedForsReveal tree0 kp0 j u :=
    mpcPoseidon2Hash32Shared lambdas
      (shamirFrameSingleSecretCall lambdas.length tagPrf pkSeed ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ skSeedSh)
      (callPrep 0)
  evalIndexedForsLeafHash tree0 kp0 j u :=
    match mpcPoseidon2SqueezeSecret32 lambdas decomp8
            (shamirFrameSingleSecretCall lambdas.length tagPrf pkSeed ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ skSeedSh)
            (callPrep 0) with
    | none => []
    | some secSh =>
      mpcPoseidon2Hash32Shared lambdas
        (shamirFrameSingleSecretCall lambdas.length tagThF pkSeed ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ secSh)
        (callPrep 1)

theorem mkShamirProductionPqHashMpcOracles_matchesKey
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one)
    {skSeedSh skPrfSh : List (List Goldilocks)} {skSeed skPrf : List UInt8}
    (hSeed : ShamirByteSharesValid lambdas skSeedSh skSeed)
    (hPrf  : ShamirByteSharesValid lambdas skPrfSh skPrf) (pkSeed : List UInt8)
    {decomp8 : List Goldilocks → List (List Goldilocks)} (hDecomp : ValidShamirLimbDecomp8 lambdas decomp8)
    (callPrep : Nat → Nat → Poseidon2CallPrep) (hPrep : ∀ step blk, (callPrep step blk).validAt lambdas) :
    (mkShamirProductionPqHashMpcOracles lambdas skSeedSh skPrfSh pkSeed decomp8 callPrep).MatchesKey
      poseidon2Suite ⟨skSeed, skPrf, pkSeed⟩ := by
  rw [ProductionPqHashMpcOracles.MatchesKey_iff]
  refine ⟨mkShamirPoseidon2MpcOracles_matchesKey lambdas hSumOne hSeed hPrf pkSeed hDecomp callPrep hPrep, ?_, ?_⟩
  · intro tree0 kp0 j u; dsimp only [mkShamirProductionPqHashMpcOracles]
    have hF := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSeed
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hF (callPrep 0) (hPrep 0)).2,
        forsIndexedSecretLeaf_eq, thSecretPrf_eq, thCall_eq]; rfl
  · intro tree0 kp0 j u; dsimp only [mkShamirProductionPqHashMpcOracles]
    have hF1 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSeed
    obtain ⟨secSh, hSq, hSecV⟩ := mpcPoseidon2SqueezeSecret32_valid lambdas hSumOne hDecomp hF1 (callPrep 0) (hPrep 0)
    have hF2 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagThF pkSeed
      ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSecV
    rw [hSq]; dsimp only
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hF2 (callPrep 1) (hPrep 1)).2,
        forsIndexedLeafFn_eq, forsIndexedLeafHash_eq, forsIndexedSecretLeaf_eq, thChainF_eq, thSecretPrf_eq, thCall_eq, thCall_eq]; rfl

theorem corduroy_threshold_stateless_euf_cma
    (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16)
    (hStateless : params.statefulJorts = false) :
    -- (1) Subthreshold `< t` corrupted custodians reveal zero information about the Shamir secret at `0`:
    (∀ (t : Nat) (corruptPts : List Goldilocks) (s₁ s₂ : Goldilocks)
       (hCard : corruptPts.length + 1 ≤ t) (P : ShamirPadPoly Goldilocks t),
      (∀ c ∈ corruptPts, c ≠ Goldilocks.zero) →
      RoundPoly.evalCoeffs P.1 Goldilocks.zero = s₁ →
      let eqv := shamir_rebalanceEquiv Goldilocks.inv t corruptPts (Goldilocks.sub s₂ s₁) hCard
      let Q := eqv.toFun P
      eqv.invFun Q = P ∧ RoundPoly.evalCoeffs Q.1 Goldilocks.zero = s₂ ∧
      (∀ xc ∈ corruptPts, RoundPoly.evalCoeffs Q.1 xc = RoundPoly.evalCoeffs P.1 xc)) ∧
    -- (2) Threshold `(t, n)` Shamir Power-7 cut matches `evalProductionStatelessSign` + SPDZ MAC `1/p^2` bound:
    (∀ (lambdas : List Goldilocks) (skSeedSh skPrfSh : List (List Goldilocks))
       (skSeed skPrf pkSeed msg optRand : List UInt8) (maxGrind : Nat)
       (decomp8 : List Goldilocks → List (List Goldilocks)) (callPrep : Nat → Nat → Poseidon2CallPrep),
      ringListSum lambdas = Goldilocks.one →
      ShamirByteSharesValid lambdas skSeedSh skSeed → ShamirByteSharesValid lambdas skPrfSh skPrf →
      ValidShamirLimbDecomp8 lambdas decomp8 → (∀ step blk, (callPrep step blk).validAt lambdas) →
      mpcEvalProductionStatelessSign poseidon2Suite params
        (mkShamirProductionPqHashMpcOracles lambdas skSeedSh skPrfSh pkSeed decomp8 callPrep)
        pkSeed msg optRand maxGrind =
      evalProductionStatelessSign poseidon2Suite params ⟨skSeed, skPrf, pkSeed⟩ msg optRand maxGrind) ∧
    (∀ gates : List (Goldilocks × GoldilocksExt2),
      qsum goldilocksExt2Card
        (fun idx => if anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) gates then 1 else 0) ≤ gates.length) ∧
    -- (3) Combined stateless width-12 `poseidon2Suite` + SPDZ MAC EUF-CMA advantage union bound:
    (∀ {Ω : Type} (coins : List Ω) (game : Ω → ProdEufCmaOutcome)
       (isSpdzMacForge isItsr isTcr isPre : Ω → Bool),
      (∀ ω, isSpdzMacForge ω = false →
        (ProdForsItsrBreak poseidon2Suite params (derivePublicKey poseidon2Suite params (game ω).sk)
          (productionSigningLog poseidon2Suite params (game ω).sk (game ω).queries)
          (game ω).msgStar (game ω).sigStar → isItsr ω = true) ∧
        (ProdSmTcrBreak poseidon2Suite params (game ω).sk
          (productionSigningLog poseidon2Suite params (game ω).sk (game ω).queries) → isTcr ω = true) ∧
        (ProdPreimageBreak poseidon2Suite params (game ω).sk
          (productionSigningLog poseidon2Suite params (game ω).sk (game ω).queries)
          (game ω).msgStar (game ω).sigStar → isPre ω = true)) →
      params.statefulJorts = false ∧
      hitCount (fun ω => prodEufCmaWin poseidon2Suite params (game ω)) coins ≤
        hitCount isSpdzMacForge coins + hitCount isItsr coins + hitCount isTcr coins + hitCount isPre coins) := by
  refine ⟨fun t cPts s₁ s₂ hC P hNz hS => shamir_single_share_privacy_bijection t cPts s₁ s₂ hC hNz P hS,
    fun ls sSh pSh sS sP pkS m opt mg dec cp h1 hSd hPf hDc hPr =>
      thresholdProductionStatelessSign_eq_evalProductionStatelessSign poseidon2Suite params _ _
        (mkShamirProductionPqHashMpcOracles_matchesKey ls h1 hSd hPf pkS hDc cp hPr) m opt mg,
    spdzGateStream_pin_count_le, ?_⟩
  intro Ω coins game isSpdz isItsr isTcr isPre hCases
  refine ⟨hStateless, ?_⟩
  induction coins with
  | nil => simp [hitCount]
  | cons ω rest ih =>
    unfold hitCount
    by_cases hWin : prodEufCmaWin poseidon2Suite params (game ω) = true
    · by_cases hSp : isSpdz ω = true
      · simp [hWin, hSp]; omega
      · have hSpF := Bool.eq_false_iff.mpr hSp
        obtain ⟨cItsr, cTcr, cPre⟩ := hCases ω hSpF
        have hWinU := hWin
        unfold prodEufCmaWin at hWinU
        obtain ⟨hVer, hNotIn⟩ := band_eq_true hWinU
        have hFresh : ∀ e ∈ productionSigningLog poseidon2Suite params (game ω).sk (game ω).queries, e.1 ≠ (game ω).msgStar :=
          fun e he hEq => of_decide_eq_true hNotIn (List.mem_map.mpr ⟨e, he, hEq⟩)
        rcases production_stateless_forgery_break poseidon2Suite params (game ω).sk (game ω).queries
            (game ω).msgStar (game ω).sigStar hw hStateless hFresh hVer with b1 | b2 | b3
        · have := cItsr b1; simp [hWin, hSpF, this]; omega
        · have := cTcr b2; simp [hWin, hSpF, this]; omega
        · have := cPre b3; simp [hWin, hSpF, this]; omega
    · simp [Bool.eq_false_iff.mpr hWin]; omega

/-- Specialization of `corduroy_threshold_stateless_euf_cma` to both real Rust `Corduroy` profiles:
    `corduroyCustody128Params` (`d = 7, h' = 4, k = 33, a = 6`) and `corduroyPoseidon2AggParams`
    (`d = 16, h' = 4, k = 32, a = 8`). -/
theorem corduroy_both_real_profiles_euf_cma
    {Ω : Type} (coins : List Ω)
    (gameCustody gameAgg : Ω → ProdEufCmaOutcome)
    (isSpdzC isItsrC isTcrC isPreC isSpdzA isItsrA isTcrA isPreA : Ω → Bool)
    (hCustody : ∀ ω, isSpdzC ω = false →
      (ProdForsItsrBreak poseidon2Suite corduroyCustody128Params
        (derivePublicKey poseidon2Suite corduroyCustody128Params (gameCustody ω).sk)
        (productionSigningLog poseidon2Suite corduroyCustody128Params (gameCustody ω).sk (gameCustody ω).queries)
        (gameCustody ω).msgStar (gameCustody ω).sigStar → isItsrC ω = true) ∧
      (ProdSmTcrBreak poseidon2Suite corduroyCustody128Params (gameCustody ω).sk
        (productionSigningLog poseidon2Suite corduroyCustody128Params (gameCustody ω).sk (gameCustody ω).queries) → isTcrC ω = true) ∧
      (ProdPreimageBreak poseidon2Suite corduroyCustody128Params (gameCustody ω).sk
        (productionSigningLog poseidon2Suite corduroyCustody128Params (gameCustody ω).sk (gameCustody ω).queries)
        (gameCustody ω).msgStar (gameCustody ω).sigStar → isPreC ω = true))
    (hAgg : ∀ ω, isSpdzA ω = false →
      (ProdForsItsrBreak poseidon2Suite corduroyPoseidon2AggParams
        (derivePublicKey poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk)
        (productionSigningLog poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk (gameAgg ω).queries)
        (gameAgg ω).msgStar (gameAgg ω).sigStar → isItsrA ω = true) ∧
      (ProdSmTcrBreak poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk
        (productionSigningLog poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk (gameAgg ω).queries) → isTcrA ω = true) ∧
      (ProdPreimageBreak poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk
        (productionSigningLog poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω).sk (gameAgg ω).queries)
        (gameAgg ω).msgStar (gameAgg ω).sigStar → isPreA ω = true)) :
    hitCount (fun ω => prodEufCmaWin poseidon2Suite corduroyCustody128Params (gameCustody ω)) coins ≤
      hitCount isSpdzC coins + hitCount isItsrC coins + hitCount isTcrC coins + hitCount isPreC coins ∧
    hitCount (fun ω => prodEufCmaWin poseidon2Suite corduroyPoseidon2AggParams (gameAgg ω)) coins ≤
      hitCount isSpdzA coins + hitCount isItsrA coins + hitCount isTcrA coins + hitCount isPreA coins := by
  exact ⟨((corduroy_threshold_stateless_euf_cma corduroyCustody128Params (.inl (by simp only [corduroyCustody128Params_eq])) (by simp only [corduroyCustody128Params_eq])).2.2.2
            coins gameCustody isSpdzC isItsrC isTcrC isPreC hCustody).2,
         ((corduroy_threshold_stateless_euf_cma corduroyPoseidon2AggParams (.inl rfl) rfl).2.2.2
            coins gameAgg isSpdzA isItsrA isTcrA isPreA hAgg).2⟩

/-! ### Real-Parameter Inhabitedness & `#tooth_pair` / `#verify_inhabited` / `#verify_constructive` Gates -/

/-- Surgical prehash-collision fault around `cshakeFrontierHashSuite` at two chosen messages `m₁, m₂`,
    used solely to witness non-vacuity of the forgery reduction premise at the exact `compact1122Params`
    (`w = 96, h = 8, L = 34, S = 1615`) without placeholder parameters or identity chains. -/
def prehashFaultSuite (base : FrontierHashSuite) (m₁ m₂ : List UInt8) : FrontierHashSuite :=
  { base with
    prehashMsg := fun pkSeed pkRoot m =>
      if m = m₂ then base.prehashMsg pkSeed pkRoot m₁ else base.prehashMsg pkSeed pkRoot m }

private theorem ite_self_eq {α : Type} {c : Prop} [Decidable c] (a : α) :
    (if c then a else a) = a := by
  cases ‹Decidable c› <;> rfl

attribute [local irreducible] evalFtsCshake256_32 cshakeEpochVoteHasher

private def witCompact1122H : FrontierHashSuite :=
  prehashFaultSuite (cshakeFrontierHashSuite compact1122Params) [1] [2]

private def witCompact1122Sk : FrontierSecretKey := ⟨1#256, 2#256, 3#256⟩

private def witCompact1122Sig : FrontierSignature :=
  (signFrontierFts witCompact1122H compact1122Params witCompact1122Sk 0#256 0 [1]).getD ⟨0#256, 0, []⟩

private theorem witSignGetD_of_dom (H : FrontierHashSuite) (p : FrontierFtsParams)
    (sk : FrontierSecretKey) (m : List UInt8)
    (hDom : 2 ^ 256 < frontierRootSubCount p.treeHeight p.frontierLen *
                      frontierDecCount p.winternitzW p.frontierLen p.targetSum) :
    signFrontierFts H p sk 0#256 0 m = some ((signFrontierFts H p sk 0#256 0 m).getD ⟨0#256, 0, []⟩) := by
  let pk := deriveFrontierPk H p sk
  let d₁ := H.prehashMsg pk.pkSeed pk.root m
  let rand := H.prfRand sk.skPrf pk.pkSeed pk.root 0#256 d₁
  let rk := (H.squeezeRank pk.pkSeed pk.root rand d₁ 0).toNat
  have hLt := Nat.lt_trans (H.squeezeRank pk.pkSeed pk.root rand d₁ 0).isLt hDom
  obtain ⟨tr, _, offs, hUnr, _, _, _, _, _, _, _, _⟩ := unrankFrontierFts_bijective p rk hLt
  have hCtr0 : ¬ ((0 : UInt16).toNat >= 2 ^ p.counterBits) := by
    have hPow : 0 < 2 ^ p.counterBits := Nat.pow_pos (by decide : 0 < 2)
    change ¬ (0 >= 2 ^ p.counterBits); omega
  have hSome : signFrontierFts H p sk 0#256 0 m =
      some ⟨rand, 0, honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs⟩ := by
    unfold signFrontierFts
    rw [ite_false_eq hCtr0]
    simp [pk, d₁, rand, rk, hUnr]
  rw [hSome]; rfl

private theorem witCompact1122_hSign :
    signFrontierFts witCompact1122H compact1122Params witCompact1122Sk 0#256 0 [1] = some witCompact1122Sig :=
  witSignGetD_of_dom witCompact1122H compact1122Params witCompact1122Sk [1]
    compact1122_rank_domain_gt_2pow256.2.2.2.2.2.2.1

private theorem witVer2_of_fault (base : FrontierHashSuite) (p : FrontierFtsParams)
    (hw : 1 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen)
    (sk : FrontierSecretKey) (m₁ m₂ : List UInt8) (sig : FrontierSignature)
    (hSign : signFrontierFts (prehashFaultSuite base m₁ m₂) p sk 0#256 0 m₁ = some sig) :
    verifyFrontierFts (prehashFaultSuite base m₁ m₂) p
      (deriveFrontierPk (prehashFaultSuite base m₁ m₂) p sk) m₂ sig = true := by
  let H := prehashFaultSuite base m₁ m₂
  have hVer₁ := verifyFrontierFts_signFrontierFts H p hw hL sk 0#256 0 m₁ sig hSign
  have hPreEq : H.prehashMsg (deriveFrontierPk H p sk).pkSeed (deriveFrontierPk H p sk).root m₂ =
      H.prehashMsg (deriveFrontierPk H p sk).pkSeed (deriveFrontierPk H p sk).root m₁ := by
    dsimp only [H, prehashFaultSuite]
    rw [ite_true_eq rfl, ite_self_eq]
  unfold verifyFrontierFts at hVer₁ ⊢; rw [hPreEq]; exact hVer₁

private theorem witCompact1122_hVer :
    verifyFrontierFts witCompact1122H compact1122Params
      (deriveFrontierPk witCompact1122H compact1122Params witCompact1122Sk) [2] witCompact1122Sig = true :=
  witVer2_of_fault (cshakeFrontierHashSuite compact1122Params) compact1122Params
    (by decide) (by decide) witCompact1122Sk [1] [2] witCompact1122Sig witCompact1122_hSign

private theorem witCompact1122_hL : 2 ≤ compact1122Params.frontierLen := by decide
private theorem witCompact1122_hNe : ([2] : List UInt8) ≠ [1] := by decide

private def witEpochM1 : List UInt8 := cshakeEpochVoteHasher 0#256 0 0#256 0#256
private def witEpochM2 : List UInt8 := cshakeEpochVoteHasher 0#256 0 1#256 0#256

private def witEpochH : FrontierHashSuite :=
  prehashFaultSuite (cshakeFrontierHashSuite compact1122Params) witEpochM1 witEpochM2

private def witEpochPk : FrontierPublicKey :=
  deriveFrontierPk witEpochH compact1122Params witCompact1122Sk

private def witEpochSig : FrontierSignature :=
  (signFrontierFts witEpochH compact1122Params witCompact1122Sk 0#256 0 witEpochM1).getD ⟨0#256, 0, []⟩

private def witEpochRec0 : HonestEpochRecord :=
  ⟨witCompact1122Sk, 0#256, 0, 0#256, 0#256, ⟨⟨0, 0#256⟩, 0#256, witEpochSig⟩⟩

private def witEpochAdvV : RotatedEpochVote := ⟨⟨0, 0#256⟩, 1#256, witEpochSig⟩

private theorem witEpoch_hSign :
    signFrontierFts witEpochH compact1122Params witCompact1122Sk 0#256 0 witEpochM1 = some witEpochSig :=
  witSignGetD_of_dom witEpochH compact1122Params witCompact1122Sk witEpochM1
    compact1122_rank_domain_gt_2pow256.2.2.2.2.2.2.1

private theorem witEpoch_hVer2 :
    verifyFrontierFts witEpochH compact1122Params witEpochPk witEpochM2 witEpochSig = true :=
  witVer2_of_fault (cshakeFrontierHashSuite compact1122Params) compact1122Params
    (by decide) (by decide) witCompact1122Sk witEpochM1 witEpochM2 witEpochSig witEpoch_hSign

private theorem witEpoch_hVal :
    ∀ idx : Fin [witEpochRec0].length,
      ([witEpochRec0].get idx).ValidAt witEpochH compact1122Params cshakeEpochVoteHasher 0#256 3#256 (0 + idx.1) := by
  rintro ⟨_ | k, hi⟩
  · exact ⟨rfl, rfl, rfl, witEpoch_hSign⟩
  · cases Nat.lt_of_succ_lt_succ hi

private theorem witEpoch_hAnc :
    ∀ r₀, [witEpochRec0].head? = some r₀ →
      witEpochPk = deriveFrontierPk witEpochH compact1122Params r₀.sk := by
  intro r₀ hr; injection hr with hE; rw [← hE]; rfl

private theorem witEpoch_hLink :
    ∀ i : Fin [witEpochRec0].length, ∀ rNext, [witEpochRec0][i.1 + 1]? = some rNext →
      ([witEpochRec0].get i).nextPkRoot = (deriveFrontierPk witEpochH compact1122Params rNext.sk).root := by
  rintro ⟨_ | k, hi⟩ _ hNxt
  · cases hNxt
  · cases Nat.lt_of_succ_lt_succ hi

private theorem witEpochAcc_of_ver (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hBytes : p.nodeBytes = 32) (hUses : p.maxSafeUses = 1)
    (voteHash : EpochVoteHasher) (sk : FrontierSecretKey) (sig : FrontierSignature)
    (hSeed : sk.pkSeed = 3#256)
    (hVer2 : verifyFrontierFts H p (deriveFrontierPk H p sk) (voteHash 0#256 0 1#256 0#256) sig = true) :
    verifyRotatedEpochChain H p voteHash 0#256 (deriveFrontierPk H p sk) 0 [1#256]
      [⟨⟨0, 0#256⟩, 1#256, sig⟩] = some ⟨3#256, 0#256⟩ := by
  unfold verifyRotatedEpochChain verifyRotatedEpochVote
  have hEp0 : ¬ (0 >= 2 ^ 64) := by decide +kernel
  have hC1 : (p.nodeBytes != 32 || p.maxSafeUses != 1) = false := by rw [hBytes, hUses]; rfl
  have hC2 : ((0 : UInt64) != UInt64.ofNat 0 || decide ((UInt64.ofNat 0).toNat + 1 >= 2 ^ 64)) = false := rfl
  have hC3 : ((1#256 : BitVec 256) != 1#256) = false := rfl
  simp only [hEp0, hC1, hC2, hC3, Bool.false_eq_true, ↓reduceIte]
  rw [hVer2]
  simp only [↓reduceIte]
  unfold verifyRotatedEpochChain deriveFrontierPk
  rw [hSeed]

private theorem witEpoch_hAcc :
    verifyRotatedEpochChain witEpochH compact1122Params cshakeEpochVoteHasher 0#256
      witEpochPk 0 [1#256] [witEpochAdvV] = some ⟨3#256, 0#256⟩ :=
  witEpochAcc_of_ver witEpochH compact1122Params rfl rfl cshakeEpochVoteHasher
    witCompact1122Sk witEpochSig rfl witEpoch_hVer2

private theorem witEpoch_hDev :
    ∃ i : Fin [witEpochRec0].length,
      ([1#256] : List (BitVec 256)).get ⟨i.1, i.2⟩ ≠ ([witEpochRec0].get i).voteDigest ∨
      ([witEpochAdvV].get ⟨i.1, i.2⟩).link.nextEpochPkRoot ≠ ([witEpochRec0].get i).nextPkRoot :=
  ⟨⟨0, Nat.zero_lt_succ 0⟩, .inl (by show (1#256 : BitVec 256) ≠ 0#256; decide)⟩

attribute [local irreducible]
  cshakeFrontierHashSuite prehashFaultSuite
  deriveFrontierPk signFrontierFts verifyFrontierFts verifyRotatedEpochChain
  witCompact1122H witCompact1122Sig witEpochM1 witEpochM2 witEpochH witEpochPk witEpochSig

set_option maxRecDepth 32768

#verify_constructive Qsag.compact1122_rank_domain_gt_2pow256
  Qsag.fts_cshake_encodings_ne
  Qsag.fts_cshake_domains_disjoint
  Qsag.encodeCshakeFrames_injective
  Qsag.ftsPrehashFrames_injective
  Qsag.ftsSqueezeRankFrames_injective
  Qsag.ftsPrfRandFrames_injective
  Qsag.ftsChainStepFrames_injective
  Qsag.ftsMergeNodeFrames_injective
  Qsag.encodeEpochVoteInput_injective
  Qsag.unrankFrontierFts_bijective
  Qsag.unrankFrontierFts_injective
  Qsag.verifyFrontierFts_signFrontierFts
  Qsag.compact1122_target_sum_antichain
  Qsag.compact1122_one_time_euf_cma_reduction
  Qsag.compact1122_closed_euf_cma_gameBound
  Qsag.compact1122_cshake256_concrete_break_lift
  Qsag.rotatedEpochVote_forward_secure_chain
  Qsag.rotatedEpochVote_cshake_chain_reduction
  Qsag.corduroy_real_profiles_audit
  Qsag.corduroy_threshold_stateless_euf_cma
  Qsag.corduroy_both_real_profiles_euf_cma
end Qsag
end

/-! ### Exports for lane sig -/
public section
namespace Qsag

#export_eqns chainAdvance collapseFrontierStack runFrontierStackLoop deriveFrontierPk
  signFrontierFts verifyRotatedEpochVote

theorem AntichainTree.size_leaf : AntichainTree.leaf.size = 1 := by rfl

theorem honestSignSubtree_length_eq_size (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256)
    (w : Nat) :
    ∀ (t v : Nat) (tr : AntichainTree) (offs : List Nat),
      tr.Valid t = true → (honestSignSubtree H pkSeed skSeed w t v tr offs).length = tr.size :=
  honestSignSubtree_length H pkSeed skSeed w

theorem runFrontierStackLoop_frontierNodes (H : FrontierHashSuite) (pkSeed : BitVec 256) (w : Nat) :
    ∀ (tr : AntichainTree) (v : Nat) (offs : List Nat) (vals : List (BitVec 256))
      (restVs restOffs : List Nat) (restVals : List (BitVec 256)) (st : List (Nat × BitVec 256)),
      0 < v → offs.length = tr.size → vals.length = tr.size →
      runFrontierStackLoop H pkSeed w (tr.frontierNodes v ++ restVs) (offs ++ restOffs) (vals ++ restVals) st =
      runFrontierStackLoop H pkSeed w restVs restOffs restVals
        (collapseFrontierStack H pkSeed w v (evalAntichainTree H pkSeed w v tr offs vals) st) :=
  runFrontierStackLoop_tree_eq H pkSeed w

theorem evalAntichainTree_honestSignSubtree (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256)
    (w : Nat) (hw : 1 ≤ w) :
    ∀ (t v : Nat) (tr : AntichainTree) (offs : List Nat),
      0 < v → tr.Valid t = true → offs.length = tr.size → (∀ a ∈ offs, a < w) → (tr = .leaf → 1 < v) →
      evalAntichainTree H pkSeed w v tr offs (honestSignSubtree H pkSeed skSeed w t v tr offs) =
        honestNodeOut H pkSeed skSeed w t v :=
  evalAntichainTree_honest H pkSeed skSeed w hw

attribute [local irreducible] evalFtsCshake256_32 cshakeEpochVoteHasher
  cshakeFrontierHashSuite prehashFaultSuite
  deriveFrontierPk signFrontierFts verifyFrontierFts verifyRotatedEpochChain
  witCompact1122H witCompact1122Sig witEpochM1 witEpochM2 witEpochH witEpochPk witEpochSig

/-- The premises of `compact1122_one_time_euf_cma_reduction` hold on the deployed
    `compact1122Params` under a pre-hash-faulted cSHAKE suite. -/
theorem compact1122_forgery_witness :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (sk : FrontierSecretKey) (hedge₁ : BitVec 256) (ctr₁ : UInt16)
      (m₁ : List UInt8) (sig₁ : FrontierSignature),
      signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁ ∧
      ∃ (m₂ : List UInt8) (sig₂ : FrontierSignature),
        m₂ ≠ m₁ ∧ verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true :=
  ⟨witCompact1122H, compact1122Params, witCompact1122_hL, witCompact1122Sk, 0#256, 0, [1], witCompact1122Sig,
    witCompact1122_hSign, [2], witCompact1122Sig, witCompact1122_hNe, witCompact1122_hVer⟩

/-- The premises of `rotatedEpochVote_forward_secure_chain` hold on a one-epoch chain. -/
theorem rotatedEpochVote_chain_witness :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) (startEp : Nat)
      (histRecords : List HonestEpochRecord) (advDigests : List (BitVec 256))
      (advVotes : List RotatedEpochVote) (anchorPk finalPk : FrontierPublicKey)
      (hLen1 : histRecords.length = advDigests.length) (hLen2 : advDigests.length = advVotes.length),
      (∀ idx : Fin histRecords.length, (histRecords.get idx).ValidAt H p voteHash chainId pkSeed (startEp + idx.1)) ∧
      (∀ r₀, histRecords.head? = some r₀ → anchorPk = deriveFrontierPk H p r₀.sk) ∧
      (∀ i : Fin histRecords.length, ∀ rNext, histRecords[i.1 + 1]? = some rNext →
        (histRecords.get i).nextPkRoot = (deriveFrontierPk H p rNext.sk).root) ∧
      verifyRotatedEpochChain H p voteHash chainId anchorPk startEp advDigests advVotes = some finalPk ∧
      (∃ i : Fin histRecords.length,
        advDigests.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
        (advVotes.get ⟨i.1, Nat.lt_of_lt_of_eq i.2 (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠ (histRecords.get i).nextPkRoot) :=
  ⟨witEpochH, compact1122Params, witCompact1122_hL, cshakeEpochVoteHasher, 0#256, 3#256, 0,
    [witEpochRec0], [1#256], [witEpochAdvV], witEpochPk, ⟨3#256, 0#256⟩, rfl, rfl,
    witEpoch_hVal, witEpoch_hAnc, witEpoch_hLink, witEpoch_hAcc, witEpoch_hDev⟩

set_option maxRecDepth 32768 in
#verify_inhabited Qsag.compact1122_one_time_euf_cma_reduction Qsag.compact1122_forgery_witness

set_option maxRecDepth 32768 in
#verify_inhabited Qsag.rotatedEpochVote_forward_secure_chain Qsag.rotatedEpochVote_chain_witness

end Qsag
end
