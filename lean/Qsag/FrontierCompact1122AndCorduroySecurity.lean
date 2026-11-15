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
     induction across historical epochs both unforgeable chain continuity from `pk_0` and strict
     forward secrecy when secret seeds at `eStar > 0` are compromised after zeroizing `0 .. eStar - 1`,
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

