module
/-
# Qsag.FrontierCompact1122AndCorduroySecurity — `Compact1122` (`FrontierSumFts`), Forward-Secure `RotatedEpochVote`, & `Corduroy` 16-Layer Threshold EUF-CMA

Constructive Lean 4.35 security reductions (`0 sorry`, `0` custom axioms, `0 Classical.choice`):
1. **`Compact1122` (`h = 8, w = 96, L = 34, S = 1615, n = 32`) Rank Domain & 1-Time EUF-CMA**:
   - Certifies `compact1122_rank_domain_gt_2pow256` (`M(8, 96, 34, 1615) > 2^263 > 2^256`, wire size
     `1122` B, `RotatedEpochVote` `1194` B), bijectivity of `unrankFrontierFts` / `rankFrontierFts`,
     stack-to-tree equivalence (`runFrontierStackLoop`), and constructive `Type`-valued 1-time
     EUF-CMA extraction (`extractCompact1122ForgeryBreak` / `compact1122_one_time_euf_cma_reduction`),
     paired with `tooth_drop_target_sum_allows_one_sig_forgery`.
2. **`RotatedEpochVote` Forward-Secure Key-Chain Induction (`rotatedEpochVote_forward_secure_chain`)**:
   - Models `EpochKeyLink` / `RotatedEpochVote` (`crates/qsag-fts/src/frontier.rs`) and proves by
     induction across historical epochs that an accepted divergent chain yields a vote-framing
     collision or a historical-key primitive break. No adaptive compromise experiment,
     erasure implementation, or probability bound for those primitive breaks is established here,
     contrasted with `tooth_static_key_compromise_forges_historical_epoch`.
3. **`Corduroy` 16-Layer Stateless `Poseidon2` Hypertree + `(t, n)` Shamir Power-7 EUF-CMA
   (`corduroy_threshold_stateless_euf_cma`)**:
   - Composes 16-layer stateless `poseidon2Suite` EUF-CMA extraction, `mkShamirProductionPqHashMpcOracles`,
     `< t` corrupted-custodian Shamir secret-independence (`shamir_single_share_privacy_bijection`),
     and SPDZ `GoldilocksExt2` MAC pin bounds (`spdzGateStream_pin_count_le`).
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
public import Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.HashSigs
public import Qsag.HypertreeEufCma
public import Qsag.ThresholdMpc
import all Qsag.Goldilocks
import all Qsag.Poseidon2
import all Qsag.HashSigs
import all Qsag.HypertreeEufCma
import all Qsag.ThresholdMpc
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. `Compact1122` (`FrontierSumFts`) Rank Bijection & 1-Time EUF-CMA Reduction -/

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

@[expose] def compact1122Params : FrontierFtsParams := ⟨32, 8, 96, 34, 1615, 256, 16, 1⟩
@[expose] def FrontierFtsParams.signatureBytes (p : FrontierFtsParams) : Nat :=
  (p.frontierLen + 1) * p.nodeBytes + (p.counterBits + 7) / 8
@[expose] def FrontierFtsParams.rotatedEpochVoteBytes (p : FrontierFtsParams) : Nat :=
  72 + p.signatureBytes

def splitConvFrom (f : Nat → Nat) (ell cur : Nat) : Nat → Nat
  | 0 => 0
  | rem + 1 => f cur * f (ell - cur) + splitConvFrom f ell (cur + 1) rem

def frontierSubCount : Nat → Nat → Nat
  | 0, ell => if ell = 1 then 1 else 0
  | t + 1, ell =>
    if ell = 0 then 0 else if ell = 1 then 1 else splitConvFrom (frontierSubCount t) ell 1 (ell - 1)

def windowConv (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | remW + 1, u => f u + (if u = 0 then 0 else windowConv f remW (u - 1))

def frontierDecCount (w : Nat) : Nat → Nat → Nat
  | 0, u => if u = 0 then 1 else 0
  | k + 1, u => windowConv (frontierDecCount w k) w u

private theorem windowConv_step (f : Nat → Nat) :
    ∀ (w u : Nat), windowConv f w (u + 1) + (if w ≤ u + 1 then f (u + 1 - w) else 0) =
      f (u + 1) + windowConv f w u
  | 0, _ => by simp [windowConv]
  | 1, 0 => by simp [windowConv]
  | m + 2, 0 => by simp [windowConv, show ¬ (m + 2 ≤ 1) by omega]
  | m + 1, v + 1 => by
    have ih := windowConv_step f m v
    have hCond : (m + 1 ≤ v + 2) ↔ (m ≤ v + 1) := by omega
    have hSub : v + 2 - (m + 1) = v + 1 - m := by omega
    unfold windowConv; simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hm : m ≤ v + 1
    · simp only [hm, hCond.mpr hm, ↓reduceIte, hSub] at ih ⊢; omega
    · simp only [hm, show ¬ (m + 1 ≤ v + 2) from fun hc => hm (hCond.mp hc), ↓reduceIte] at ih ⊢; omega

def slideWindowAux : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, [], acc =>
    match acc + x with | 0 => 0 :: slideWindowAux xs [] 0 | m + 1 => (m + 1) :: slideWindowAux xs [] (m + 1)
  | x :: xs, y :: ys, acc =>
    match acc + x - y with | 0 => 0 :: slideWindowAux xs ys 0 | m + 1 => (m + 1) :: slideWindowAux xs ys (m + 1)

private theorem match_cons_nat (n : Nat) (f : Nat → List Nat) :
    (match n with | 0 => 0 :: f 0 | m + 1 => (m + 1) :: f (m + 1)) = n :: f n := by
  cases n <;> rfl

def decTableRow (w maxS : Nat) : Nat → List Nat
  | 0 => 1 :: List.replicate maxS 0
  | k + 1 => let prev := decTableRow w maxS k; slideWindowAux prev (List.replicate w 0 ++ prev) 0

private theorem slideWindowAux_spec (f : Nat → Nat) (w : Nat) :
    ∀ (rem start : Nat) (xs ys : List Nat) (acc : Nat), xs.length = rem →
      (∀ i < rem, xs.getD i 0 = f (start + i)) →
      (∀ i < rem, ys.getD i 0 = (if w ≤ start + i then f (start + i - w) else 0)) →
      (start = 0 → acc = 0) →
      (∀ p, start = p + 1 → acc = windowConv f w p ∧
        (if w ≤ p + 1 then f (p + 1 - w) else 0) ≤ acc + f (p + 1)) →
      slideWindowAux xs ys acc = List.ofFn (fun i : Fin rem => windowConv f w (start + i.1))
  | 0, _, [], _, _, _, _, _, _, _ => rfl
  | rem + 1, start, x :: xs, ys, acc, hLen, hXs, hYs, h0, hSucc => by
    have hx0 : x = f start := by simpa using hXs 0 (Nat.zero_lt_succ rem)
    have hy0 : ys.headD 0 = (if w ≤ start then f (start - w) else 0) := by
      cases ys <;> [simpa using (hYs 0 (Nat.zero_lt_succ rem)).symm; simpa using hYs 0 (Nat.zero_lt_succ rem)]
    have hWinLe : ∀ (m u : Nat), (if m ≤ u + 1 then f (u + 1 - m) else 0) ≤ windowConv f m u + f (u + 1) := by
      intro m u; have := windowConv_step f m u; omega
    have hAccNext : acc + x - ys.headD 0 = windowConv f w start := by
      cases start with
      | zero => rw [h0 rfl, hx0, hy0]; cases w <;> simp [windowConv]
      | succ p => obtain ⟨hA, _⟩ := hSucc p rfl; rw [hx0, hy0]; have hE := windowConv_step f w p; rw [← hA] at hE; omega
    cases ys with
    | nil =>
      have hNoDrop : ∀ i < rem + 1, (if w ≤ start + i then f (start + i - w) else 0) = 0 := fun i hi => (hYs i hi).symm
      unfold slideWindowAux; rw [match_cons_nat, show acc + x = windowConv f w start by simpa [List.headD] using hAccNext]
      simp only [List.ofFn_succ, Fin.val_zero, Nat.add_zero]; congr 1
      exact slideWindowAux_spec f w rem (start + 1) xs [] (windowConv f w start) (Nat.succ.inj hLen)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hXs (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using (hNoDrop (i + 1) (Nat.succ_lt_succ hi)).symm)
        (fun h => nomatch h) (fun p hp => ⟨by rw [Nat.succ.inj hp], by rw [Nat.succ.inj hp]; exact hWinLe w p⟩)
    | cons y ys' =>
      unfold slideWindowAux; rw [match_cons_nat, show acc + x - y = windowConv f w start from hAccNext]
      simp only [List.ofFn_succ, Fin.val_zero, Nat.add_zero]; congr 1
      exact slideWindowAux_spec f w rem (start + 1) xs ys' (windowConv f w start) (Nat.succ.inj hLen)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hXs (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hYs (i + 1) (Nat.succ_lt_succ hi))
        (fun h => nomatch h) (fun p hp => ⟨by rw [Nat.succ.inj hp], by rw [Nat.succ.inj hp]; exact hWinLe w p⟩)

private theorem getD_ofFn_nat {n : Nat} (g : Fin n → Nat) (i : Nat) (hi : i < n) :
    (List.ofFn g).getD i 0 = g ⟨i, hi⟩ := by simp [List.getD, List.getElem?_ofFn, hi]

private theorem getD_replicate_append_nat (w : Nat) (xs : List Nat) :
    ∀ i, (List.replicate w 0 ++ xs).getD i 0 = (if w ≤ i then xs.getD (i - w) 0 else 0) := by
  induction w with
  | zero => intro i; simp
  | succ m ih =>
    intro i; cases i with
    | zero => simp [List.replicate]
    | succ j =>
      simp only [List.replicate_succ, List.cons_append, List.getD_cons_succ, ih j]
      by_cases hm : m ≤ j
      · simp [hm, show m + 1 ≤ j + 1 by omega, show j - m = j + 1 - (m + 1) by omega]
      · simp [hm, show ¬ (m + 1 ≤ j + 1) by omega]

private theorem decTableRow_eq_ofFn (w maxS : Nat) :
    ∀ k : Nat, decTableRow w maxS k = List.ofFn (fun i : Fin (maxS + 1) => frontierDecCount w k i.1)
  | 0 => by
    apply List.ext_getElem?; intro i; cases i with
    | zero => simp [decTableRow, frontierDecCount]
    | succ j =>
      simp only [decTableRow, List.getElem?_cons_succ, List.getElem?_replicate, List.getElem?_ofFn]
      by_cases hj : j < maxS <;> simp [hj, show (j + 1 < maxS + 1) ↔ j < maxS by omega, frontierDecCount]
  | k + 1 => by
    unfold decTableRow; rw [decTableRow_eq_ofFn w maxS k]
    exact slideWindowAux_spec (frontierDecCount w k) w (maxS + 1) 0 _ _ 0 List.length_ofFn
      (fun i hi => by simpa using getD_ofFn_nat (fun j : Fin (maxS + 1) => frontierDecCount w k j.1) i hi)
      (fun i hi => by
        rw [getD_replicate_append_nat]
        by_cases hw : w ≤ i <;> [simp [hw, getD_ofFn_nat _ (i - w) (by omega)]; simp [hw]])
      (fun _ => rfl) (fun _ hp => nomatch hp)

def subTableRow (maxL : Nat) : Nat → List Nat
  | 0 => List.ofFn (fun i : Fin (maxL + 1) => if i.1 = 1 then 1 else 0)
  | t + 1 =>
    let prev := subTableRow maxL t
    List.ofFn (fun i : Fin (maxL + 1) =>
      if i.1 = 0 then 0 else if i.1 = 1 then 1 else splitConvFrom (prev.getD · 0) i.1 1 (i.1 - 1))

private theorem splitConvFrom_congr (f g : Nat → Nat) (ell : Nat) :
    ∀ (cur rem : Nat), (∀ j, j ≤ ell → f j = g j) → cur + rem ≤ ell →
      splitConvFrom f ell cur rem = splitConvFrom g ell cur rem
  | _, 0, _, _ => rfl
  | cur, rem + 1, hEq, hBnd => by
    unfold splitConvFrom
    rw [hEq cur (by omega), hEq (ell - cur) (by omega), splitConvFrom_congr f g ell (cur + 1) rem hEq (by omega)]

private theorem subTableRow_eq_ofFn (maxL : Nat) :
    ∀ t : Nat, subTableRow maxL t = List.ofFn (fun i : Fin (maxL + 1) => frontierSubCount t i.1)
  | 0 => by apply List.ext_getElem?; intro i; simp [subTableRow, frontierSubCount]
  | t + 1 => by
    unfold subTableRow; rw [subTableRow_eq_ofFn maxL t]; apply List.ext_getElem?; intro ell; simp only [List.getElem?_ofFn]
    by_cases hLt : ell < maxL + 1
    · simp only [hLt, ↓reduceDIte, Option.some.injEq]; unfold frontierSubCount
      by_cases h0 : ell = 0; · simp [h0]
      by_cases h1 : ell = 1; · simp [h1]
      simp only [h0, h1, ↓reduceIte]
      exact splitConvFrom_congr _ _ ell 1 (ell - 1) (fun j _ => getD_ofFn_nat _ j (by omega)) (by omega)
    · simp [hLt]

@[expose] def frontierTotalCardFast (p : FrontierFtsParams) : Nat :=
  (subTableRow p.frontierLen p.treeHeight).getD p.frontierLen 0 *
  (decTableRow p.winternitzW p.targetSum p.frontierLen).getD p.targetSum 0

theorem frontierTotalCardFast_eq_spec (p : FrontierFtsParams) :
    frontierTotalCardFast p =
      frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
  unfold frontierTotalCardFast
  rw [subTableRow_eq_ofFn, decTableRow_eq_ofFn,
      getD_ofFn_nat _ p.frontierLen (Nat.lt_succ_self _), getD_ofFn_nat _ p.targetSum (Nat.lt_succ_self _)]

set_option maxRecDepth 32768 in
theorem compact1122_rank_domain_gt_2pow256 :
    compact1122Params.signatureBytes = 1122 ∧
    compact1122Params.signatureBytes + 96 ≤ 1232 ∧
    compact1122Params.rotatedEpochVoteBytes = 1194 ∧
    2 ^ 263 < frontierSubCount 8 34 * frontierDecCount 96 34 1615 ∧
    2 ^ 256 < frontierSubCount 8 34 * frontierDecCount 96 34 1615 ∧
    (∀ d₁ d₂ : BitVec 256,
      d₁.toNat < frontierSubCount 8 34 * frontierDecCount 96 34 1615 ∧
      (d₁.toNat = d₂.toNat → d₁ = d₂)) := by
  have hFast : 2 ^ 263 < frontierTotalCardFast compact1122Params := by decide
  rw [frontierTotalCardFast_eq_spec] at hFast; dsimp only [compact1122Params] at hFast
  have h256 := Nat.lt_trans (by decide : 2 ^ 256 < 2 ^ 263) hFast
  exact ⟨by decide, by decide, by decide, hFast, h256,
    fun d₁ _ => ⟨Nat.lt_trans d₁.isLt h256, BitVec.eq_of_toNat_eq⟩⟩

/-! ### Prefix-Free Binary-Tree Antichain & Bijective Unrank / Rank -/

inductive AntichainTree : Type where
  | leaf : AntichainTree
  | split : AntichainTree → AntichainTree → AntichainTree
  deriving DecidableEq, Repr

def AntichainTree.size : AntichainTree → Nat | .leaf => 1 | .split l r => l.size + r.size
theorem AntichainTree.size_pos : ∀ tr : AntichainTree, 1 ≤ tr.size
  | .leaf => Nat.le_refl 1
  | .split l r => by have := l.size_pos; have := r.size_pos; unfold AntichainTree.size; omega

def AntichainTree.Valid : Nat → AntichainTree → Bool
  | 0, .leaf => true | 0, .split _ _ => false
  | _ + 1, .leaf => true | t + 1, .split l r => l.Valid t && r.Valid t

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
      | cons hd _ => unfold collapseTreeStack; simp [show ¬ (hd.1 % 2 = 0 ∧ 2 * v = hd.1 + 1) by omega]
    have hR : collapseTreeStack (2 * v + 1) r ((2 * v, l) :: st) = collapseTreeStack v (.split l r) st := by
      unfold collapseTreeStack
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
  | 0, _ => 0 | _ + 1, .leaf => 0
  | t + 1, .split l rt =>
    let ell := l.size + rt.size
    rankSplitPrefix t ell 1 l.size (ell - 1) + rankSubtree t l * frontierSubCount t rt.size + rankSubtree t rt

private theorem unrankSplitChoice_spec (t ell : Nat) :
    ∀ (cur rem r : Nat), r < splitConvFrom (frontierSubCount t) ell cur rem →
      ∃ leftSz rL rR, unrankSplitChoice t ell cur rem r = some (leftSz, rL, rR) ∧
        cur ≤ leftSz ∧ leftSz < cur + rem ∧ rL < frontierSubCount t leftSz ∧
        rR < frontierSubCount t (ell - leftSz) ∧
        rankSplitPrefix t ell cur leftSz rem + rL * frontierSubCount t (ell - leftSz) + rR = r
  | _, 0, _, hLt => by simp [splitConvFrom] at hLt
  | cur, rem + 1, r, hLt => by
    unfold splitConvFrom at hLt
    let lCnt := frontierSubCount t cur; let rCnt := frontierSubCount t (ell - cur)
    by_cases hB : r < lCnt * rCnt
    · have hrPos : 0 < rCnt := by cases rCnt with | zero => simp [rCnt] at hB | succ m => exact Nat.zero_lt_succ m
      have hDM : (r / rCnt) * rCnt + r % rCnt = r := by rw [Nat.mul_comm (r / rCnt) rCnt]; exact Nat.div_add_mod r rCnt
      exact ⟨cur, r / rCnt, r % rCnt, by unfold unrankSplitChoice; simp [lCnt, rCnt, hB], Nat.le_refl _, by omega,
        (Nat.div_lt_iff_lt_mul hrPos).mpr hB, Nat.mod_lt r hrPos, by unfold rankSplitPrefix; simp [hDM]⟩
    · obtain ⟨lsz, rL, rR, hRec, hGe, hUp, hrL, hrR, hRk⟩ := unrankSplitChoice_spec t ell (cur + 1) rem (r - lCnt * rCnt) (by omega)
      refine ⟨lsz, rL, rR, by unfold unrankSplitChoice; simp [lCnt, rCnt, hB, hRec], by omega, by omega, hrL, hrR, ?_⟩
      unfold rankSplitPrefix; simp only [show cur < lsz by omega, ↓reduceIte]
      change lCnt * rCnt + rankSplitPrefix t ell (cur + 1) lsz rem + rL * frontierSubCount t (ell - lsz) + rR = r; omega

theorem rankSubtree_unrankSubtree :
    ∀ (t ell r : Nat), r < frontierSubCount t ell →
      ∃ tr : AntichainTree, unrankSubtree t ell r = some tr ∧ tr.Valid t = true ∧ tr.size = ell ∧ rankSubtree t tr = r
  | 0, ell, r, hLt => by
    unfold frontierSubCount at hLt; by_cases h1 : ell = 1
    · subst h1; simp only [↓reduceIte] at hLt; have hr0 : r = 0 := by omega
      subst hr0; exact ⟨.leaf, by simp [unrankSubtree], rfl, rfl, rfl⟩
    · simp [h1] at hLt
  | t + 1, ell, r, hLt => by
    unfold frontierSubCount at hLt
    by_cases h0 : ell = 0; · simp [h0] at hLt
    by_cases h1 : ell = 1
    · subst h1; simp only [Nat.one_ne_zero, ↓reduceIte] at hLt; have hr0 : r = 0 := by omega
      subst hr0; exact ⟨.leaf, by simp [unrankSubtree], rfl, rfl, rfl⟩
    · simp only [h0, h1, ↓reduceIte] at hLt
      obtain ⟨lsz, rL, rR, hSp, _, _, hrL, hrR, hRk⟩ := unrankSplitChoice_spec t ell 1 (ell - 1) r hLt
      obtain ⟨l, hUl, hVl, hSl, hRl⟩ := rankSubtree_unrankSubtree t lsz rL hrL
      obtain ⟨rt, hUr, hVr, hSr, hRr⟩ := rankSubtree_unrankSubtree t (ell - lsz) rR hrR
      have hEll : l.size + rt.size = ell := by rw [hSl, hSr]; omega
      exact ⟨.split l rt, by unfold unrankSubtree; simp [h0, h1, hSp, hUl, hUr],
        by simp [AntichainTree.Valid, hVl, hVr], hEll, by unfold rankSubtree; rw [hEll, hSl, hSr, hRl, hRr]; exact hRk⟩

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
    | none => none | some (a, rSub) => (unrankDecorations w k (u - a) rSub).map (a :: ·)

def rankWindowPrefix (w k : Nat) : (remW u target : Nat) → Nat
  | 0, _, _ => 0 | _ + 1, _, 0 => 0
  | remW + 1, u, target + 1 =>
    frontierDecCount w k u + (if u = 0 then 0 else rankWindowPrefix w k remW (u - 1) target)

def rankDecorations (w : Nat) : List Nat → Nat → Nat
  | [], _ => 0 | a :: rest, u => rankWindowPrefix w rest.length w u a + rankDecorations w rest (u - a)

private theorem unrankWindowDigit_spec (w k : Nat) :
    ∀ (remW u baseA r : Nat), r < windowConv (frontierDecCount w k) remW u →
      ∃ aOff rSub, unrankWindowDigit w k remW u baseA r = some (baseA + aOff, rSub) ∧
        aOff < remW ∧ aOff ≤ u ∧ rSub < frontierDecCount w k (u - aOff) ∧ rankWindowPrefix w k remW u aOff + rSub = r
  | 0, _, _, _, hLt => by simp [windowConv] at hLt
  | remW + 1, u, baseA, r, hLt => by
    unfold windowConv at hLt; let bkt := frontierDecCount w k u
    by_cases hB : r < bkt
    · exact ⟨0, r, by unfold unrankWindowDigit; simp [bkt, hB], Nat.zero_lt_succ _, Nat.zero_le _, hB, by simp [rankWindowPrefix]⟩
    · by_cases hu0 : u = 0; · simp [bkt, hu0] at hLt; omega
      simp only [hu0, ↓reduceIte] at hLt
      obtain ⟨aOff, rSub, hRec, hLtW, hLeU, hrS, hRk⟩ := unrankWindowDigit_spec w k remW (u - 1) (baseA + 1) (r - bkt) (by omega)
      refine ⟨aOff + 1, rSub, ?_, Nat.succ_lt_succ hLtW, by omega, (show u - 1 - aOff = u - (aOff + 1) by omega) ▸ hrS, ?_⟩
      · unfold unrankWindowDigit; simp [bkt, hB, hu0, (show baseA + 1 + aOff = baseA + (aOff + 1) by omega) ▸ hRec]
      · unfold rankWindowPrefix; simp only [hu0, ↓reduceIte]
        change bkt + rankWindowPrefix w k remW (u - 1) aOff + rSub = r; omega

theorem rankDecorations_unrankDecorations (w : Nat) :
    ∀ (k u r : Nat), r < frontierDecCount w k u →
      ∃ offs : List Nat, unrankDecorations w k u r = some offs ∧
        offs.length = k ∧ offs.sum = u ∧ (∀ a ∈ offs, a < w) ∧ rankDecorations w offs u = r
  | 0, u, r, hLt => by
    unfold frontierDecCount at hLt; by_cases hu0 : u = 0
    · subst hu0; simp only [↓reduceIte] at hLt; have hr0 : r = 0 := by omega
      subst hr0; exact ⟨[], by simp [unrankDecorations], rfl, rfl, fun _ h => nomatch h, rfl⟩
    · simp [hu0] at hLt
  | k + 1, u, r, hLt => by
    unfold frontierDecCount at hLt
    obtain ⟨a, rSub, hDig, haW, haU, hrSub, hRkW⟩ := unrankWindowDigit_spec w k w u 0 r hLt
    simp only [Nat.zero_add] at hDig
    obtain ⟨rest, hRest, hLen, hSum, hBnd, hRkRest⟩ := rankDecorations_unrankDecorations w k (u - a) rSub hrSub
    refine ⟨a :: rest, by unfold unrankDecorations; simp [hDig, hRest], congrArg Nat.succ hLen,
      by simp [List.sum_cons, hSum]; omega, ?_, by unfold rankDecorations; rw [hLen, hRkRest]; omega⟩
    intro x hx; rcases List.mem_cons.mp hx with rfl | htl <;> [exact haW; exact hBnd x htl]

def unrankFrontierFts (p : FrontierFtsParams) (rank : Nat) : Option (AntichainTree × List Nat × List Nat) :=
  let dCard := frontierDecCount p.winternitzW p.frontierLen p.targetSum
  let fCard := frontierSubCount p.treeHeight p.frontierLen
  if rank < fCard * dCard then
    match unrankSubtree p.treeHeight p.frontierLen (rank / dCard),
          unrankDecorations p.winternitzW p.frontierLen p.targetSum (rank % dCard) with
    | some tr, some offs => some (tr, tr.frontierNodes 1, offs) | _, _ => none
  else none

def rankFrontierFts (p : FrontierFtsParams) (tr : AntichainTree) (offs : List Nat) : Nat :=
  rankSubtree p.treeHeight tr * frontierDecCount p.winternitzW p.frontierLen p.targetSum +
  rankDecorations p.winternitzW offs p.targetSum

theorem unrankFrontierFts_bijective (p : FrontierFtsParams) (rank : Nat)
    (hLt : rank < frontierSubCount p.treeHeight p.frontierLen *
                  frontierDecCount p.winternitzW p.frontierLen p.targetSum) :
    ∃ tr paths offs, unrankFrontierFts p rank = some (tr, paths, offs) ∧
      paths = tr.frontierNodes 1 ∧ tr.Valid p.treeHeight = true ∧ tr.size = p.frontierLen ∧
      offs.length = p.frontierLen ∧ offs.sum = p.targetSum ∧
      (∀ a ∈ offs, a < p.winternitzW) ∧ rankFrontierFts p tr offs = rank := by
  let dCard := frontierDecCount p.winternitzW p.frontierLen p.targetSum
  let fCard := frontierSubCount p.treeHeight p.frontierLen
  have hdPos : 0 < dCard := by cases hD : dCard with | zero => rw [hD, Nat.mul_zero] at hLt; omega | succ m => exact Nat.zero_lt_succ m
  obtain ⟨tr, hTr, hVal, hSz, hRkTr⟩ := rankSubtree_unrankSubtree p.treeHeight p.frontierLen _ ((Nat.div_lt_iff_lt_mul hdPos).mpr hLt)
  obtain ⟨offs, hOffs, hLen, hSum, hBnd, hRkOff⟩ := rankDecorations_unrankDecorations p.winternitzW p.frontierLen p.targetSum _ (Nat.mod_lt rank hdPos)
  exact ⟨tr, tr.frontierNodes 1, offs, by unfold unrankFrontierFts; simp [dCard, fCard, hLt, hTr, hOffs],
    rfl, hVal, hSz, hLen, hSum, hBnd,
    by unfold rankFrontierFts; rw [hRkTr, hRkOff, Nat.mul_comm (rank / dCard) dCard]; exact Nat.div_add_mod rank dCard⟩

theorem unrankFrontierFts_injective (p : FrontierFtsParams) {r₁ r₂ : Nat}
    {tr₁ tr₂ : AntichainTree} {paths₁ paths₂ offs₁ offs₂ : List Nat}
    (h₁ : unrankFrontierFts p r₁ = some (tr₁, paths₁, offs₁))
    (h₂ : unrankFrontierFts p r₂ = some (tr₂, paths₂, offs₂))
    (hSame : paths₁ = paths₂ ∧ offs₁ = offs₂) : r₁ = r₂ := by
  have hLt₁ : r₁ < frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
    unfold unrankFrontierFts at h₁; split at h₁ <;> [assumption; cases h₁]
  have hLt₂ : r₂ < frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
    unfold unrankFrontierFts at h₂; split at h₂ <;> [assumption; cases h₂]
  obtain ⟨_, _, _, hu₁, hp₁, _, _, _, _, _, hrk₁⟩ := unrankFrontierFts_bijective p r₁ hLt₁
  obtain ⟨_, _, _, hu₂, hp₂, _, _, _, _, _, hrk₂⟩ := unrankFrontierFts_bijective p r₂ hLt₂
  rw [h₁] at hu₁; injection hu₁ with e₁; obtain ⟨rfl, e₁'⟩ := Prod.mk.inj e₁; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₁'
  rw [h₂] at hu₂; injection hu₂ with e₂; obtain ⟨rfl, e₂'⟩ := Prod.mk.inj e₂; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e₂'
  rw [← hrk₁, ← hrk₂, frontierNodes_injective_root tr₁ tr₂ (hp₁.symm.trans (hSame.1.trans hp₂)), hSame.2]

/-! ### Constructive Equal-Sum Pigeonhole & `FrontierSumFts` 1-Time EUF-CMA Reduction -/

def findSmallerOffsetIdx :
    (ys xs : List Nat) → (hLen : ys.length = xs.length) → ys.sum ≤ xs.sum → ys ≠ xs →
    { idx : Fin ys.length // ys.get idx < xs.get ⟨idx.1, idx.2.trans_eq hLen⟩ }
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

structure FrontierPublicKey where pkSeed : BitVec 256; root : BitVec 256 deriving DecidableEq, Repr
structure FrontierSecretKey where skSeed : BitVec 256; skPrf : BitVec 256; pkSeed : BitVec 256 deriving DecidableEq, Repr
structure FrontierSignature where
  randomizer : BitVec 256
  grindCounter : UInt16
  chainValues : List (BitVec 256)
  deriving DecidableEq, Repr

def chainAdvance (H : FrontierHashSuite) (pkSeed : BitVec 256) (v : Nat) : Nat → Nat → BitVec 256 → BitVec 256
  | _, 0, cur => cur
  | step, rem + 1, cur => chainAdvance H pkSeed v (step + 1) rem (H.chainStep pkSeed v step cur)

theorem chainAdvance_add (H : FrontierHashSuite) (pkSeed : BitVec 256) (v : Nat) :
    ∀ (s k₁ k₂ : Nat) (x : BitVec 256),
      chainAdvance H pkSeed v s (k₁ + k₂) x = chainAdvance H pkSeed v (s + k₁) k₂ (chainAdvance H pkSeed v s k₁ x)
  | _, 0, _, _ => rfl
  | s, k₁ + 1, k₂, x => by
    simp only [Nat.succ_add, chainAdvance, chainAdvance_add H pkSeed v (s + 1) k₁ k₂]
    rw [show s + 1 + k₁ = s + (k₁ + 1) by omega]

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

def honestSignSubtree (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) :
    Nat → Nat → AntichainTree → List Nat → List (BitVec 256)
  | t, v, .leaf, offs => [chainAdvance H pkSeed v 0 (offs.headD 0) (honestNodeBase H pkSeed skSeed w t v)]
  | t + 1, v, .split l r, offs =>
    honestSignSubtree H pkSeed skSeed w t (2 * v) l (offs.take l.size) ++
    honestSignSubtree H pkSeed skSeed w t (2 * v + 1) r (offs.drop l.size)
  | 0, _, .split _ _, _ => []

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

private theorem runFrontierStackLoop_tree_eq (H : FrontierHashSuite) (pkSeed : BitVec 256) (w : Nat) :
    ∀ (tr : AntichainTree) (v : Nat) (offs : List Nat) (vals : List (BitVec 256))
      (restVs restOffs : List Nat) (restVals : List (BitVec 256)) (st : List (Nat × BitVec 256)),
      0 < v → offs.length = tr.size → vals.length = tr.size →
      runFrontierStackLoop H pkSeed w (tr.frontierNodes v ++ restVs) (offs ++ restOffs) (vals ++ restVals) st =
      runFrontierStackLoop H pkSeed w restVs restOffs restVals
        (collapseFrontierStack H pkSeed w v (evalAntichainTree H pkSeed w v tr offs vals) st)
  | .leaf, _, offs, vals, _, _, _, _, _, hOL, hVL => by
    cases offs with | nil => cases hOL | cons a os =>
      cases vals with | nil => cases hVL | cons x xs =>
        rw [List.eq_nil_of_length_eq_zero (Nat.succ.inj hOL), List.eq_nil_of_length_eq_zero (Nat.succ.inj hVL)]; rfl
  | .split l r, v, offs, vals, restVs, restOffs, restVals, st, hv, hOL, hVL => by
    conv => lhs; rw [AntichainTree.frontierNodes, List.append_assoc,
      (List.take_append_drop l.size offs).symm, List.append_assoc,
      (List.take_append_drop l.size vals).symm, List.append_assoc]
    rw [runFrontierStackLoop_tree_eq H pkSeed w l (2 * v) (offs.take l.size) (vals.take l.size)
          (r.frontierNodes (2 * v + 1) ++ restVs) (offs.drop l.size ++ restOffs) (vals.drop l.size ++ restVals)
          st (by omega) (by simp [hOL, AntichainTree.size]) (by simp [hVL, AntichainTree.size])]
    have hL : collapseFrontierStack H pkSeed w (2 * v)
        (evalAntichainTree H pkSeed w (2 * v) l (offs.take l.size) (vals.take l.size)) st =
        (2 * v, evalAntichainTree H pkSeed w (2 * v) l (offs.take l.size) (vals.take l.size)) :: st := by
      cases st with | nil => rfl | cons hd _ => unfold collapseFrontierStack; simp [show ¬ (hd.1 % 2 = 0 ∧ 2 * v = hd.1 + 1) by omega]
    rw [hL, runFrontierStackLoop_tree_eq H pkSeed w r (2 * v + 1) (offs.drop l.size) (vals.drop l.size)
          restVs restOffs restVals _ (by omega) (by simp [hOL, AntichainTree.size]) (by simp [hVL, AntichainTree.size])]
    unfold collapseFrontierStack
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
      | [(1, rootOut)] => decide (rootOut = pk.root) | _ => false

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
  | _, _, .leaf, _, _ => rfl
  | 0, _, .split _ _, _, hV => by simp [AntichainTree.Valid] at hV
  | t + 1, v, .split l r, offs, hV => by
    obtain ⟨hl, hr⟩ := Bool.and_eq_true.mp hV
    simp [honestSignSubtree, AntichainTree.size,
      honestSignSubtree_length H pkSeed skSeed w t (2 * v) l _ hl,
      honestSignSubtree_length H pkSeed skSeed w t (2 * v + 1) r _ hr]

private theorem evalAntichainTree_honest (H : FrontierHashSuite) (pkSeed skSeed : BitVec 256) (w : Nat) (hw : 1 ≤ w) :
    ∀ (t v : Nat) (tr : AntichainTree) (offs : List Nat),
      0 < v → tr.Valid t = true → offs.length = tr.size → (∀ a ∈ offs, a < w) → (tr = .leaf → 1 < v) →
      evalAntichainTree H pkSeed w v tr offs (honestSignSubtree H pkSeed skSeed w t v tr offs) =
        honestNodeOut H pkSeed skSeed w t v
  | t, v, .leaf, offs, _, _, hOL, hBnd, hvGt => by
    cases offs with | nil => cases hOL | cons a os =>
      have := hBnd a (.head os)
      unfold honestSignSubtree evalAntichainTree honestNodeOut
      simp only [List.headD_cons, hvGt rfl, ↓reduceIte, ← chainAdvance_add]
      rw [show a + (w - 1 - a) = w - 1 by omega, Nat.zero_add]
  | 0, _, .split _ _, _, _, hV, _, _, _ => by simp [AntichainTree.Valid] at hV
  | t + 1, v, .split l r, offs, hv, hV, hOL, hBnd, _ => by
    obtain ⟨hl, hr⟩ := Bool.and_eq_true.mp hV
    have hHSL := honestSignSubtree_length H pkSeed skSeed w t (2 * v) l (offs.take l.size) hl
    unfold honestSignSubtree evalAntichainTree
    rw [List.take_append_of_le_length (by omega), hHSL, List.take_length,
        List.drop_append_of_le_length (by omega), hHSL, List.drop_length, List.nil_append,
        evalAntichainTree_honest H pkSeed skSeed w hw t (2 * v) l (offs.take l.size) (by omega) hl
          (by simp [hOL, AntichainTree.size]) (fun a ha => hBnd a (List.mem_of_mem_take ha)) (fun _ => by omega),
        evalAntichainTree_honest H pkSeed skSeed w hw t (2 * v + 1) r (offs.drop l.size) (by omega) hr
          (by simp [hOL, AntichainTree.size]) (fun a ha => hBnd a (List.mem_of_mem_drop ha)) (fun _ => by omega)]
    unfold honestNodeOut honestNodeBase; simp [show 2 * v > 1 by omega, show 2 * v + 1 > 1 by omega]

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
    have hLt : rk < frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
      unfold unrankFrontierFts at hUnr; split at hUnr <;> [assumption; cases hUnr]
    obtain ⟨_, _, _, hu', hp', hVal, hSz, hOLen, _, hBnd, _⟩ := unrankFrontierFts_bijective p rk hLt
    rw [hUnr] at hu'; injection hu' with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    have hSigLen := (honestSignSubtree_length H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs hVal).trans hSz
    unfold verifyFrontierFts; simp only [hSigLen, bne_self_eq_false, ↓reduceIte, hCtr, hUnr]
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
        (by unfold honestNodeOut at hOut; simp [m₂, m₁, hvGt] at hOut; exact hOut))
    else False.elim (hmNe (by unfold honestNodeOut at hOut; simp [m₂, m₁, hvGt] at hOut; exact hOut))
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
    have hVSub := Bool.and_eq_true.mp hV
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
    offs₁.length = tr.size → offs₂.length = tr.size → vals₂.length = tr.size →
    (∀ a ∈ offs₁, a < w) → (idx : Fin offs₂.length) →
    offs₂.get idx < offs₁.get ⟨idx.1, idx.2.trans_eq (‹offs₂.length = tr.size›.trans ‹offs₁.length = tr.size›.symm)⟩ →
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
    | _ :: _, _ :: _, _, _, hOL₂, _, ⟨_ + 1, hk⟩, _, _ =>
      False.elim (by unfold AntichainTree.size at hOL₂; simp at hOL₂; subst hOL₂; omega)
  | 0, _, .split _ _, _, _, _, _, _, hV, _, _, _, _, _, _, _ => False.elim (by simp [AntichainTree.Valid] at hV)
  | t + 1, v, .split l r, offs₁, offs₂, vals₂, hv, _, hV, hOL₁, hOL₂, hVL₂, hBnd₁, idx, hLtIdx, hEv =>
    have hVSub := Bool.and_eq_true.mp hV
    let lEnd₂ := evalAntichainTree H pkSeed w (2 * v) l (offs₂.take l.size) (vals₂.take l.size)
    let rEnd₂ := evalAntichainTree H pkSeed w (2 * v + 1) r (offs₂.drop l.size) (vals₂.drop l.size)
    match inspectSplitNode H pkSeed skSeed w t v hv lEnd₂ rEnd₂ hEv with
    | .inl brk => brk
    | .inr ⟨hLEq, hREq, _⟩ =>
      if hInL : idx.1 < l.size then
        extractOffsetDiffBreak H pkSeed skSeed w t (2 * v) l (offs₁.take l.size) (offs₂.take l.size) (vals₂.take l.size)
          (by omega) (fun _ => by omega) hVSub.1 (by simp [hOL₁, AntichainTree.size])
          (by simp [hOL₂, AntichainTree.size]) (by simp [hVL₂, AntichainTree.size])
          (fun a ha => hBnd₁ a (List.mem_of_mem_take ha)) ⟨idx.1, by simp [hOL₂, AntichainTree.size, hInL]⟩
          (by simp [List.get_eq_getElem, List.getElem_take]; exact hLtIdx) hLEq
      else
        extractOffsetDiffBreak H pkSeed skSeed w t (2 * v + 1) r (offs₁.drop l.size) (offs₂.drop l.size) (vals₂.drop l.size)
          (by omega) (fun _ => by omega) hVSub.2 (by simp [hOL₁, AntichainTree.size])
          (by simp [hOL₂, AntichainTree.size]) (by simp [hVL₂, AntichainTree.size])
          (fun a ha => hBnd₁ a (List.mem_of_mem_drop ha))
          ⟨idx.1 - l.size, by simp [hOL₂, AntichainTree.size]; unfold AntichainTree.size at hOL₂; omega⟩
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
      unfold signFrontierFts at hHonest; split at hHonest; · cases hHonest
      dsimp only at hHonest
      cases hU : unrankFrontierFts p (H.squeezeRank pk.pkSeed pk.root (H.prfRand sk.skPrf pk.pkSeed pk.root hedge₁ d₁) d₁ ctr₁).toNat with
      | none => simp [pk, d₁, hU] at hHonest
      | some tp => simp only [pk, d₁, hU, Option.some.injEq] at hHonest; subst hHonest; exact ⟨tp.1, tp.2.1, tp.2.2, hU⟩
    match hU₁ : unrankFrontierFts p rk₁, hU₂ : unrankFrontierFts p rk₂ with
    | none, _ => False.elim (by obtain ⟨_, _, _, h⟩ := hUnr₁Some; rw [h] at hU₁; cases hU₁)
    | _, none => False.elim (by
        unfold verifyFrontierFts at hForged; split at hForged; · cases hForged
        split at hForged <;> [cases hForged; simp [pk, d₂, rk₂, hU₂] at hForged])
    | some (tr₁, paths₁, offs₁), some (tr₂, paths₂, offs₂) =>
      have hLt₁ : rk₁ < frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
        unfold unrankFrontierFts at hU₁; split at hU₁ <;> [assumption; cases hU₁]
      have hLt₂ : rk₂ < frontierSubCount p.treeHeight p.frontierLen * frontierDecCount p.winternitzW p.frontierLen p.targetSum := by
        unfold unrankFrontierFts at hU₂; split at hU₂ <;> [assumption; cases hU₂]
      have hP₁ : paths₁ = tr₁.frontierNodes 1 ∧ tr₁.Valid p.treeHeight = true ∧ tr₁.size = p.frontierLen ∧
          offs₁.length = p.frontierLen ∧ offs₁.sum = p.targetSum ∧ (∀ a ∈ offs₁, a < p.winternitzW) := by
        obtain ⟨_, _, _, hu, hp, hv, hs, hl, hsm, hb, _⟩ := unrankFrontierFts_bijective p rk₁ hLt₁
        rw [hU₁] at hu; injection hu with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
        exact ⟨hp, hv, hs, hl, hsm, hb⟩
      have hP₂ : paths₂ = tr₂.frontierNodes 1 ∧ tr₂.Valid p.treeHeight = true ∧ tr₂.size = p.frontierLen ∧
          offs₂.length = p.frontierLen ∧ offs₂.sum = p.targetSum ∧ (∀ a ∈ offs₂, a < p.winternitzW) := by
        obtain ⟨_, _, _, hu, hp, hv, hs, hl, hsm, hb, _⟩ := unrankFrontierFts_bijective p rk₂ hLt₂
        rw [hU₂] at hu; injection hu with e; obtain ⟨rfl, e'⟩ := Prod.mk.inj e; obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
        exact ⟨hp, hv, hs, hl, hsm, hb⟩
      have hVer : sig₂.chainValues.length = p.frontierLen ∧
          evalAntichainTree H sk.pkSeed p.winternitzW 1 tr₂ offs₂ sig₂.chainValues = pk.root := by
        unfold verifyFrontierFts at hForged
        by_cases hCL : sig₂.chainValues.length != p.frontierLen; · simp [hCL] at hForged
        have hCLEq : sig₂.chainValues.length = p.frontierLen := Decidable.of_not_not (by simpa using hCL)
        by_cases hC₂ : sig₂.grindCounter.toNat >= 2 ^ p.counterBits; · simp [hCL, hC₂] at hForged
        simp only [hCL, ↓reduceIte, hC₂, pk, d₂, rk₂, hU₂] at hForged
        have hLp := runFrontierStackLoop_tree_eq H sk.pkSeed p.winternitzW tr₂ 1 offs₂ sig₂.chainValues
          [] [] [] [] (by decide) (hP₂.2.2.2.1.trans hP₂.2.2.1.symm) (hCLEq.trans hP₂.2.2.1.symm)
        simp only [List.append_nil] at hLp; rw [hP₂.1, hLp] at hForged
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

def verifyFrontierFtsNoTargetSum (H : FrontierHashSuite) (p : FrontierFtsParams)
    (pk : FrontierPublicKey) (frontier offs : List Nat) (chainVals : List (BitVec 256)) : Bool :=
  if chainVals.length != p.frontierLen || offs.length != p.frontierLen then false
  else if offs.any (fun a => decide (p.winternitzW ≤ a)) then false
  else match runFrontierStackLoop H pk.pkSeed p.winternitzW frontier offs chainVals [] with
    | [(1, rootOut)] => decide (rootOut = pk.root) | _ => false

theorem tooth_drop_target_sum_allows_one_sig_forgery
    (H : FrontierHashSuite) (p : FrontierFtsParams) (hw : 2 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen)
    (sk : FrontierSecretKey) (tr : AntichainTree) (hVal : tr.Valid p.treeHeight = true) (hSz : tr.size = p.frontierLen) :
    let pk := deriveFrontierPk H p sk
    let offs₁ := List.replicate p.frontierLen 0
    let honestVals := honestSignSubtree H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs₁
    let v₀ := (tr.frontierNodes 1).headD 2
    let forgedVals := (H.chainStep pk.pkSeed v₀ 0 (honestVals.headD 0#256)) :: honestVals.tail
    let offs₂ := 1 :: List.replicate (p.frontierLen - 1) 0
    offs₂ ≠ offs₁ ∧ verifyFrontierFtsNoTargetSum H p pk (tr.frontierNodes 1) offs₂ forgedVals = true := by
  intro pk offs₁ honestVals v₀ forgedVals offs₂
  have hNe : offs₂ ≠ offs₁ := by dsimp only [offs₁, offs₂]; cases hFL : p.frontierLen <;> [omega; simp [List.replicate_succ]]
  refine ⟨hNe, ?_⟩
  have hHLen := (honestSignSubtree_length H pk.pkSeed sk.skSeed p.winternitzW p.treeHeight 1 tr offs₁ hVal).trans hSz
  have hNLen := (tr.frontierNodes_length 1).trans hSz
  have hOLen₁ : offs₁.length = p.frontierLen := List.length_replicate
  have hOLen₂ : offs₂.length = p.frontierLen := by dsimp only [offs₂]; rw [List.length_cons, List.length_replicate]; omega
  cases hFN : tr.frontierNodes 1 with | nil => rw [hFN] at hNLen; simp at hNLen; omega | cons u us =>
    cases hHV : honestVals with | nil => rw [hHV] at hHLen; simp at hHLen; omega | cons x xs =>
      have hFLS : p.frontierLen = us.length + 1 := by rw [hFN] at hNLen; simpa using hNLen.symm
      have hO₁ : offs₁ = 0 :: List.replicate us.length 0 := by dsimp only [offs₁]; rw [hFLS, List.replicate_succ]
      have hO₂ : offs₂ = 1 :: List.replicate us.length 0 := by dsimp only [offs₂]; rw [hFLS]; simp
      have hFLen : forgedVals.length = p.frontierLen := by dsimp only [forgedVals]; rw [hHV] at hHLen ⊢; simpa using hHLen
      have hNoBig : offs₂.any (fun a => decide (p.winternitzW ≤ a)) = false := by
        rw [hO₂, List.any_cons, decide_eq_false (by omega : ¬ p.winternitzW ≤ 1)]
        suffices (List.replicate us.length 0).any (fun a => decide (p.winternitzW ≤ a)) = false by rw [this]; rfl
        apply List.any_eq_false.mpr; intro a ha; rw [List.mem_replicate] at ha; rw [ha.2]; exact decide_eq_false (by omega)
      unfold verifyFrontierFtsNoTargetSum
      simp only [hFLen, hOLen₂, bne_self_eq_false, Bool.or_self, ↓reduceIte, hNoBig]
      have hStepEq : runFrontierStackLoop H pk.pkSeed p.winternitzW (tr.frontierNodes 1) offs₂ forgedVals [] =
          runFrontierStackLoop H pk.pkSeed p.winternitzW (tr.frontierNodes 1) offs₁ honestVals [] := by
        dsimp only [forgedVals, v₀]; rw [hFN, hHV, hO₁, hO₂]; unfold runFrontierStackLoop
        simp only [List.headD_cons, List.tail_cons, Nat.sub_zero]
        have hAdv : chainAdvance H pk.pkSeed u 0 (p.winternitzW - 1) x =
            chainAdvance H pk.pkSeed u 1 (p.winternitzW - 1 - 1) (H.chainStep pk.pkSeed u 0 x) := by
          conv => lhs; rw [show p.winternitzW - 1 = 1 + (p.winternitzW - 1 - 1) by omega]
          rfl
        rw [hAdv]
      rw [hStepEq]
      have hLp := runFrontierStackLoop_tree_eq H pk.pkSeed p.winternitzW tr 1 offs₁ honestVals
        [] [] [] [] (by decide) (hOLen₁.trans hSz.symm) (hHLen.trans hSz.symm)
      simp only [List.append_nil] at hLp; rw [hLp]; unfold runFrontierStackLoop collapseFrontierStack
      rw [evalAntichainTree_honest H pk.pkSeed sk.skSeed p.winternitzW (by omega) p.treeHeight 1 tr offs₁
        (by decide) hVal (hOLen₁.trans hSz.symm)
        (fun a ha => by rw [List.mem_replicate] at ha; rw [ha.2]; omega)
        (fun hLf => by subst hLf; unfold AntichainTree.size at hSz; omega)]
      simp [pk, deriveFrontierPk]

/-! ## §2. `RotatedEpochVote` Forward-Secure Key-Chain Induction (`rotatedEpochVote_forward_secure_chain`) -/

structure EpochKeyLink where epoch : UInt64; nextEpochPkRoot : BitVec 256 deriving DecidableEq, Repr
structure RotatedEpochVote where
  link : EpochKeyLink; voteDigest : BitVec 256; signature : FrontierSignature
  deriving DecidableEq, Repr
abbrev EpochVoteHasher := BitVec 256 → UInt64 → BitVec 256 → BitVec 256 → List UInt8

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
      | none => none | some nextPk => verifyRotatedEpochChain H p voteHash chainId nextPk (ep + 1) ds vs
  | _, _, _, _ => none

inductive EpochChainHistoricalBreak (H : FrontierHashSuite) (voteHash : EpochVoteHasher)
    (pkSeed : BitVec 256) (w : Nat) : Type where
  | voteFramingCollision (chainId : BitVec 256) (ep : UInt64) (d₁ r₁ d₂ r₂ : BitVec 256) :
      (d₂ ≠ d₁ ∨ r₂ ≠ r₁) → voteHash chainId ep d₂ r₂ = voteHash chainId ep d₁ r₁ →
      EpochChainHistoricalBreak H voteHash pkSeed w
  | epochKeyBreak (histEpoch : Nat) (skSeedAtEpoch : BitVec 256) :
      FrontierForgeryBreak H pkSeed skSeedAtEpoch w → EpochChainHistoricalBreak H voteHash pkSeed w

structure HonestEpochRecord where
  sk : FrontierSecretKey; hedge : BitVec 256; ctr : UInt16
  voteDigest : BitVec 256; nextPkRoot : BitVec 256; vote : RotatedEpochVote

def HonestEpochRecord.ValidAt (H : FrontierHashSuite) (p : FrontierFtsParams)
    (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) (ep : Nat) (rec_ : HonestEpochRecord) : Prop :=
  rec_.sk.pkSeed = pkSeed ∧ rec_.vote.link = ⟨UInt64.ofNat ep, rec_.nextPkRoot⟩ ∧
  rec_.vote.voteDigest = rec_.voteDigest ∧
  signFrontierFts H p rec_.sk rec_.hedge rec_.ctr
    (voteHash chainId (UInt64.ofNat ep) rec_.voteDigest rec_.nextPkRoot) = some rec_.vote.signature

def extractRotatedEpochVoteChainBreak (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hL : 2 ≤ p.frontierLen) (voteHash : EpochVoteHasher) (chainId pkSeed : BitVec 256) :
    (startEp : Nat) → (histRecords : List HonestEpochRecord) →
    (advDigests : List (BitVec 256)) → (advVotes : List RotatedEpochVote) →
    (anchorPk finalPk : FrontierPublicKey) →
    histRecords.length = advDigests.length → advDigests.length = advVotes.length →
    (∀ idx : Fin histRecords.length, (histRecords.get idx).ValidAt H p voteHash chainId pkSeed (startEp + idx.1)) →
    (∀ r₀, histRecords.head? = some r₀ → anchorPk = deriveFrontierPk H p r₀.sk) →
    (∀ i : Fin histRecords.length, ∀ rNext, histRecords[i.1 + 1]? = some rNext →
      (histRecords.get i).nextPkRoot = (deriveFrontierPk H p rNext.sk).root) →
    verifyRotatedEpochChain H p voteHash chainId anchorPk startEp advDigests advVotes = some finalPk →
    (∃ i : Fin histRecords.length,
      advDigests.get ⟨i.1, i.2.trans_eq ‹histRecords.length = advDigests.length›⟩ ≠ (histRecords.get i).voteDigest ∨
      (advVotes.get ⟨i.1, i.2.trans_eq (‹histRecords.length = advDigests.length›.trans ‹advDigests.length = advVotes.length›)⟩).link.nextEpochPkRoot ≠
        (histRecords.get i).nextPkRoot) →
    EpochChainHistoricalBreak H voteHash pkSeed p.winternitzW
  | _, [], _, _, _, _, _, _, _, _, _, _, hDev => False.elim (by obtain ⟨⟨_, hi⟩, _⟩ := hDev; omega)
  | startEp, r₀ :: rs, dAdv :: dsAdv, vAdv :: vsAdv, anchorPk, finalPk,
    hLen1, hLen2, hVal, hAnchor, hLink, hChainAcc, hDev =>
    have hr₀Val : r₀.ValidAt H p voteHash chainId pkSeed startEp := by simpa using hVal ⟨0, Nat.zero_lt_succ _⟩
    have hAncEq : anchorPk = deriveFrontierPk H p r₀.sk := hAnchor r₀ rfl
    have hStepAcc : ∃ npk, verifyRotatedEpochVote H p voteHash chainId anchorPk (UInt64.ofNat startEp) dAdv vAdv = some npk ∧
        verifyRotatedEpochChain H p voteHash chainId npk (startEp + 1) dsAdv vsAdv = some finalPk := by
      unfold verifyRotatedEpochChain at hChainAcc
      by_cases hEpB : startEp >= 2 ^ 64; · simp [hEpB] at hChainAcc
      simp only [hEpB, ↓reduceIte] at hChainAcc
      cases hV : verifyRotatedEpochVote H p voteHash chainId anchorPk (UInt64.ofNat startEp) dAdv vAdv with
      | none => simp [hV] at hChainAcc | some npk => exact ⟨npk, hV, by simpa [hV] using hChainAcc⟩
    if hHeadDiff : dAdv ≠ r₀.voteDigest ∨ vAdv.link.nextEpochPkRoot ≠ r₀.nextPkRoot then
      have hVerStep : verifyFrontierFts H p (deriveFrontierPk H p r₀.sk)
          (voteHash chainId (UInt64.ofNat startEp) dAdv vAdv.link.nextEpochPkRoot) vAdv.signature = true := by
        obtain ⟨_, hV, _⟩ := hStepAcc; rw [hAncEq] at hV; unfold verifyRotatedEpochVote at hV
        by_cases c1 : p.nodeBytes != 32 || p.maxSafeUses != 1; · simp [c1] at hV
        by_cases c2 : vAdv.link.epoch != UInt64.ofNat startEp || (UInt64.ofNat startEp).toNat + 1 >= 2 ^ 64; · simp [c1, c2] at hV
        by_cases c3 : vAdv.voteDigest != dAdv; · simp [c1, c2, c3] at hV
        simp only [c1, c2, c3, ↓reduceIte] at hV
        have hEpEq : vAdv.link.epoch = UInt64.ofNat startEp := by
          cases h : (vAdv.link.epoch != UInt64.ofNat startEp) <;> [exact of_decide_eq_false h; simp [h] at c2]
        have hDigEq : vAdv.voteDigest = dAdv := by
          cases h : (vAdv.voteDigest != dAdv) <;> [exact of_decide_eq_false h; simp [h] at c3]
        by_cases hOk : verifyFrontierFts H p (deriveFrontierPk H p r₀.sk)
            (voteHash chainId vAdv.link.epoch vAdv.voteDigest vAdv.link.nextEpochPkRoot) vAdv.signature = true
        · rw [hEpEq, hDigEq] at hOk; exact hOk
        · simp [hOk] at hV
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
        intro npk hV; unfold verifyRotatedEpochVote at hV
        by_cases c1 : p.nodeBytes != 32 || p.maxSafeUses != 1; · simp [c1] at hV
        by_cases c2 : vAdv.link.epoch != UInt64.ofNat startEp || (UInt64.ofNat startEp).toNat + 1 >= 2 ^ 64; · simp [c1, c2] at hV
        by_cases c3 : vAdv.voteDigest != dAdv; · simp [c1, c2, c3] at hV
        simp only [c1, c2, c3, ↓reduceIte] at hV; split at hV
        · injection hV with hE; rw [← hE, hAncEq, hSame0.2]; simp [deriveFrontierPk, hr₀Val.1]
        · cases hV
      extractRotatedEpochVoteChainBreak H p hL voteHash chainId pkSeed (startEp + 1) rs dsAdv vsAdv
        ⟨pkSeed, r₀.nextPkRoot⟩ finalPk (Nat.succ.inj hLen1) (Nat.succ.inj hLen2)
        (fun j => by simpa [Nat.add_assoc, Nat.add_comm 1 j.1] using hVal ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
        (fun r₁ hr₁ => by
          have hL0 := hLink ⟨0, Nat.zero_lt_succ _⟩ r₁ (by simpa using hr₁)
          have hV1 : r₁.ValidAt H p voteHash chainId pkSeed (startEp + 1) := by
            cases rs with | nil => cases hr₁ | cons hd _ =>
              injection hr₁ with hE; subst hE; simpa using hVal ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
          simp [deriveFrontierPk] at hL0 ⊢; exact ⟨hV1.1.symm, hL0⟩)
        (fun j rNext hNxt => hLink ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ rNext hNxt)
        (by obtain ⟨npk, hV, hRest⟩ := hStepAcc; rw [hNextPkEq npk hV] at hRest; exact hRest)
        (by obtain ⟨⟨idx, hIdx⟩, hD⟩ := hDev
            cases idx with | zero => exact False.elim (hHeadDiff hD) | succ j => exact ⟨⟨j, Nat.lt_of_succ_lt_succ hIdx⟩, hD⟩)

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
      advDigests.get ⟨i.1, i.2.trans_eq hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
      (advVotes.get ⟨i.1, i.2.trans_eq (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠ (histRecords.get i).nextPkRoot) :
    Nonempty (EpochChainHistoricalBreak H voteHash pkSeed p.winternitzW) :=
  ⟨extractRotatedEpochVoteChainBreak H p hL voteHash chainId pkSeed startEp histRecords advDigests advVotes
    anchorPk finalPk hLen1 hLen2 hVal hAnchor hLink hAcc hDev⟩

theorem tooth_static_key_compromise_forges_historical_epoch
    (H : FrontierHashSuite) (p : FrontierFtsParams)
    (hBytes : p.nodeBytes = 32) (hUses : p.maxSafeUses = 1)
    (hw : 1 ≤ p.winternitzW) (hL : 2 ≤ p.frontierLen) (hCtrBits : 1 ≤ p.counterBits)
    (hDom : 2 ^ 256 ≤ frontierSubCount p.treeHeight p.frontierLen *
                      frontierDecCount p.winternitzW p.frontierLen p.targetSum)
    (voteHash : EpochVoteHasher) (chainId : BitVec 256)
    (skStatic : FrontierSecretKey) (hedge : BitVec 256)
    (honestDigest forgedDigest : BitVec 256) (hDiff : forgedDigest ≠ honestDigest) :
    let pk₀ := deriveFrontierPk H p skStatic
    ∃ forgedVote : RotatedEpochVote,
      forgedVote.voteDigest = forgedDigest ∧ forgedVote.voteDigest ≠ honestDigest ∧
      verifyRotatedEpochVote H p voteHash chainId pk₀ 0 forgedDigest forgedVote = some pk₀ := by
  intro pk₀
  let msg := voteHash chainId 0 forgedDigest pk₀.root
  let d := H.prehashMsg pk₀.pkSeed pk₀.root msg
  let rand := H.prfRand skStatic.skPrf pk₀.pkSeed pk₀.root hedge d
  let rk := (H.squeezeRank pk₀.pkSeed pk₀.root rand d 0).toNat
  obtain ⟨tr, _, offs, hUnr, _, _, _, _, _, _, _⟩ :=
    unrankFrontierFts_bijective p rk (Nat.lt_of_lt_of_le (H.squeezeRank pk₀.pkSeed pk₀.root rand d 0).isLt hDom)
  have hCtr0 : ¬ ((0 : UInt16).toNat >= 2 ^ p.counterBits) := by
    have := Nat.two_pow_pos p.counterBits; simp; omega
  let sig : FrontierSignature := ⟨rand, 0, honestSignSubtree H pk₀.pkSeed skStatic.skSeed p.winternitzW p.treeHeight 1 tr offs⟩
  have hSign : signFrontierFts H p skStatic hedge 0 msg = some sig := by
    unfold signFrontierFts; simp [hCtr0, pk₀, msg, d, rand, rk, hUnr, sig]
  refine ⟨⟨⟨0, pk₀.root⟩, forgedDigest, sig⟩, rfl, hDiff, ?_⟩
  unfold verifyRotatedEpochVote
  simp [hBytes, hUses, verifyFrontierFts_signFrontierFts H p hw hL skStatic hedge 0 msg sig hSign, msg, pk₀]

/-! ## §3. `Corduroy` 16-Layer Stateless `Poseidon2` Hypertree + `(t, n)` Shamir Power-7 Composition -/

@[expose] def corduroy16LayerPoseidon2Params : PqHashParams :=
  { w := 4, ell1 := 128, subtreeHeight := 3, numLayers := 16,
    forsTrees := 32, forsHeight := 8, maxSigsLog2 := 20, statefulJorts := false }

theorem corduroy16LayerPoseidon2Params_wellFormed :
    corduroy16LayerPoseidon2Params.numLayers = 16 ∧
    corduroy16LayerPoseidon2Params.statefulJorts = false ∧
    corduroy16LayerPoseidon2Params.productionWellFormed = true :=
  ⟨rfl, rfl, by decide +kernel⟩

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
  refine ⟨mkShamirPoseidon2MpcOracles_matchesKey lambdas hSumOne hSeed hPrf pkSeed hDecomp callPrep hPrep, ?_, ?_⟩
  · intro tree0 kp0 j u; dsimp only [mkShamirProductionPqHashMpcOracles]
    have hF := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSeed
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hF (callPrep 0) (hPrep 0)).2,
        forsIndexedSecretLeaf, thSecretPrf_eq, thCall_eq]; rfl
  · intro tree0 kp0 j u; dsimp only [mkShamirProductionPqHashMpcOracles]
    have hF1 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagPrf pkSeed
      ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSeed
    obtain ⟨secSh, hSq, hSecV⟩ := mpcPoseidon2SqueezeSecret32_valid lambdas hSumOne hDecomp hF1 (callPrep 0) (hPrep 0)
    have hF2 := shamirFrameSingleSecretCall_valid lambdas hSumOne tagThF pkSeed
      ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩ hSecV
    rw [hSq]; dsimp only
    rw [(mpcPoseidon2SpongeShared_simulates lambdas hSumOne hF2 (callPrep 1) (hPrep 1)).2,
        forsIndexedLeafFn, forsIndexedLeafHash, forsIndexedSecretLeaf, thChainF_eq, thSecretPrf_eq, thCall_eq, thCall_eq]; rfl

theorem corduroy_threshold_stateless_euf_cma
    (params : PqHashParams)
    (hLayers : params.numLayers = 16)
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
      finSum goldilocksExt2Card
        (fun idx => if anyGatePinsAlpha (enumGoldilocksExt2.toFun idx) gates then 1 else 0) ≤ gates.length) ∧
    -- (3) Combined 16-layer stateless `poseidon2Suite` + SPDZ MAC EUF-CMA advantage union bound:
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
      params.numLayers = 16 ∧
      hitCount (fun ω => prodEufCmaWin poseidon2Suite params (game ω)) coins ≤
        hitCount isSpdzMacForge coins + hitCount isItsr coins + hitCount isTcr coins + hitCount isPre coins) := by
  refine ⟨fun t cPts s₁ s₂ hC P hNz hS => shamir_single_share_privacy_bijection t cPts s₁ s₂ hC hNz P hS,
    fun ls sSh pSh sS sP pkS m opt mg dec cp h1 hSd hPf hDc hPr =>
      thresholdProductionStatelessSign_eq_evalProductionStatelessSign poseidon2Suite params _ _
        (mkShamirProductionPqHashMpcOracles_matchesKey ls h1 hSd hPf pkS hDc cp hPr) m opt mg,
    spdzGateStream_pin_count_le, ?_⟩
  intro Ω coins game isSpdz isItsr isTcr isPre hCases
  refine ⟨hLayers, ?_⟩
  induction coins with
  | nil => simp [hitCount]
  | cons ω rest ih =>
    unfold hitCount
    by_cases hWin : prodEufCmaWin poseidon2Suite params (game ω) = true
    · by_cases hSp : isSpdz ω = true
      · simp [hWin, hSp]; omega
      · have hSpF := Bool.eq_false_iff.mpr hSp
        obtain ⟨cItsr, cTcr, cPre⟩ := hCases ω hSpF
        obtain ⟨hVer, hNotIn⟩ := Bool.and_eq_true.mp hWin
        have hFresh : ∀ e ∈ productionSigningLog poseidon2Suite params (game ω).sk (game ω).queries, e.1 ≠ (game ω).msgStar :=
          fun e he hEq => of_decide_eq_true hNotIn (List.mem_map.mpr ⟨e, he, hEq⟩)
        rcases production_stateless_forgery_break poseidon2Suite params (game ω).sk (game ω).queries
            (game ω).msgStar (game ω).sigStar hw hStateless hFresh hVer with b1 | b2 | b3
        · have := cItsr b1; simp [hWin, hSpF, this]; omega
        · have := cTcr b2; simp [hWin, hSpF, this]; omega
        · have := cPre b3; simp [hWin, hSpF, this]; omega
    · simp [Bool.eq_false_iff.mpr hWin]; omega

theorem tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret
    (P Q : List Goldilocks)
    (hP : verifyShamirPolyConsistent 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true)
    (hQ : verifyShamirPolyConsistent 2 Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true) :
    RoundPoly.evalCoeffs P Goldilocks.zero = RoundPoly.evalCoeffs Q Goldilocks.zero ∧
    RoundPoly.evalCoeffs P Goldilocks.zero ≠ Goldilocks.zero := by
  have hRef : verifyShamirPolyConsistent 2 [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
      [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] = true := by decide +kernel
  have hEqQ := shamirPolyConsistent_unique_at_zero 2 P Q [Goldilocks.ofNat 1, Goldilocks.ofNat 2]
    [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hQ
  have hEqRef := shamirPolyConsistent_unique_at_zero 2 P [Goldilocks.ofNat 1, Goldilocks.ofNat 4]
    [Goldilocks.ofNat 1, Goldilocks.ofNat 2] [Goldilocks.ofNat 5, Goldilocks.ofNat 9] (by decide +kernel) (by decide) hP hRef
  exact ⟨hEqQ, by rw [hEqRef]; decide +kernel⟩

/-! ### Inhabitedness & `#tooth_pair` / `#verify_inhabited` / `#verify_constructive` Gates -/

def toyFrontierHash : FrontierHashSuite where
  prehashMsg := fun _ _ _ => 0#256
  squeezeRank := fun _ _ _ _ _ => 0#256
  prfRand := fun _ _ _ _ _ => 0#256
  leafStart := fun _ _ _ => 0#256
  chainStep := fun _ _ _ x => x
  mergeNode := fun _ _ l _ => l

theorem witness_compact1122_forgery :
    ∃ (H : FrontierHashSuite) (p : FrontierFtsParams) (_ : 2 ≤ p.frontierLen)
      (sk : FrontierSecretKey) (hedge₁ : BitVec 256) (ctr₁ : UInt16)
      (m₁ : List UInt8) (sig₁ : FrontierSignature),
      signFrontierFts H p sk hedge₁ ctr₁ m₁ = some sig₁ ∧
      ∃ (m₂ : List UInt8) (sig₂ : FrontierSignature),
        m₂ ≠ m₁ ∧ verifyFrontierFts H p (deriveFrontierPk H p sk) m₂ sig₂ = true := by
  let p : FrontierFtsParams := ⟨32, 1, 2, 2, 1, 256, 8, 1⟩
  let sk : FrontierSecretKey := ⟨0#256, 0#256, 0#256⟩
  have hUnr0 : unrankFrontierFts p 0 = some (.split .leaf .leaf, [2, 3], [0, 1]) := by decide +kernel
  let sig : FrontierSignature := ⟨0#256, 0, [0#256, 0#256]⟩
  refine ⟨toyFrontierHash, p, by decide, sk, 0#256, 0, [1], sig, ?_, [2], sig, by decide, ?_⟩
  · unfold signFrontierFts toyFrontierHash; simp [p, sk, hUnr0, sig, honestSignSubtree, chainAdvance, honestNodeBase]
  · unfold verifyFrontierFts toyFrontierHash deriveFrontierPk
    simp [p, sk, hUnr0, sig, runFrontierStackLoop, collapseFrontierStack, chainAdvance, honestNodeOut, honestNodeBase]

theorem witness_rotatedEpochVote_chain :
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
        advDigests.get ⟨i.1, i.2.trans_eq hLen1⟩ ≠ (histRecords.get i).voteDigest ∨
        (advVotes.get ⟨i.1, i.2.trans_eq (hLen1.trans hLen2)⟩).link.nextEpochPkRoot ≠ (histRecords.get i).nextPkRoot) := by
  let p : FrontierFtsParams := ⟨32, 1, 2, 2, 1, 256, 8, 1⟩
  let sk : FrontierSecretKey := ⟨0#256, 0#256, 0#256⟩
  have hUnr0 : unrankFrontierFts p 0 = some (.split .leaf .leaf, [2, 3], [0, 1]) := by decide +kernel
  let sig : FrontierSignature := ⟨0#256, 0, [0#256, 0#256]⟩
  let vh : EpochVoteHasher := fun _ _ _ _ => [0]
  let rec₀ : HonestEpochRecord := ⟨sk, 0#256, 0, 0#256, 0#256, ⟨⟨0, 0#256⟩, 0#256, sig⟩⟩
  let advV : RotatedEpochVote := ⟨⟨0, 0#256⟩, 1#256, sig⟩
  have hSign : signFrontierFts toyFrontierHash p sk 0#256 0 [0] = some sig := by
    unfold signFrontierFts toyFrontierHash; simp [p, sk, hUnr0, sig, honestSignSubtree, chainAdvance, honestNodeBase]
  have hVer : verifyFrontierFts toyFrontierHash p (deriveFrontierPk toyFrontierHash p sk) [0] sig = true := by
    unfold verifyFrontierFts toyFrontierHash deriveFrontierPk
    simp [p, sk, hUnr0, sig, runFrontierStackLoop, collapseFrontierStack, chainAdvance, honestNodeOut, honestNodeBase]
  refine ⟨toyFrontierHash, p, by decide, vh, 0#256, 0#256, 0, [rec₀], [1#256], [advV],
    deriveFrontierPk toyFrontierHash p sk, ⟨0#256, 0#256⟩, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨i, hi⟩; have hi0 : i = 0 := by omega
    subst hi0; exact ⟨rfl, rfl, rfl, hSign⟩
  · intro r₀ hr; injection hr with hE; rw [← hE]
  · intro ⟨i, hi⟩ _ hNxt; have hi0 : i = 0 := by omega
    subst hi0; cases hNxt
  · unfold verifyRotatedEpochChain verifyRotatedEpochVote
    simp [p, sk, advV, vh, hVer, deriveFrontierPk]
  · exact ⟨⟨0, by decide⟩, .inl (by decide)⟩

theorem witness_corduroy_16layer_params :
    ∃ params : PqHashParams,
      params.numLayers = 16 ∧ (params.w = 4 ∨ params.w = 16) ∧ params.statefulJorts = false :=
  ⟨corduroy16LayerPoseidon2Params, rfl, .inl rfl, rfl⟩

end Qsag
end

#tooth_pair Qsag.compact1122_one_time_euf_cma_reduction vs Qsag.tooth_drop_target_sum_allows_one_sig_forgery
#tooth_pair Qsag.rotatedEpochVote_forward_secure_chain vs Qsag.tooth_static_key_compromise_forges_historical_epoch
#tooth_pair Qsag.corduroy_threshold_stateless_euf_cma vs Qsag.tooth_corduroy_t_corrupted_custodians_uniquely_pin_secret
#verify_inhabited Qsag.compact1122_one_time_euf_cma_reduction Qsag.witness_compact1122_forgery
#verify_inhabited Qsag.rotatedEpochVote_forward_secure_chain Qsag.witness_rotatedEpochVote_chain
#verify_inhabited Qsag.corduroy_threshold_stateless_euf_cma Qsag.witness_corduroy_16layer_params
#verify_constructive
  Qsag.compact1122_rank_domain_gt_2pow256
  Qsag.unrankFrontierFts_bijective
  Qsag.unrankFrontierFts_injective
  Qsag.verifyFrontierFts_signFrontierFts
  Qsag.compact1122_one_time_euf_cma_reduction
  Qsag.tooth_drop_target_sum_allows_one_sig_forgery
  Qsag.rotatedEpochVote_forward_secure_chain
  Qsag.tooth_static_key_compromise_forges_historical_epoch
  Qsag.corduroy_threshold_stateless_euf_cma
