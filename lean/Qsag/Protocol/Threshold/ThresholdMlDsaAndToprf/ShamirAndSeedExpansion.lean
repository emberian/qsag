module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.CheckedSigning
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ## Authenticated replicated shares and a masked rejection observation

This local view model includes both held components and their MAC shares.
It describes a uniform sharing experiment; seed expansion and a distributed
implementation refinement remain separate obligations.
-/

structure RssAuthShare204 where
  value : Fq204
  mac : Fq204
  deriving DecidableEq

abbrev RssAuthCoins204 := RssAuthShare204 × RssAuthShare204

def rssNextParty204 (p : Fin 3) : Fin 3 := ⟨(p.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def rssLastParty204 (p : Fin 3) : Fin 3 := ⟨(p.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

private theorem rssPartyIndices204 (p : Fin 3) :
    rssNextParty204 p ≠ p ∧ rssLastParty204 p ≠ p ∧ rssLastParty204 p ≠ rssNextParty204 p := by
  revert p
  decide

/-- Party `p` holds the two components other than `p`. Both the value and MAC
sum are completed at the missing component. -/
def rssAuthSharing204 (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    Fin 3 → RssAuthShare204 := fun i =>
  if i = p then
    ⟨Fq204.sub (Fq204.sub secret r.1.value) r.2.value,
     Fq204.sub (Fq204.sub (Fq204.mul key secret) r.1.mac) r.2.mac⟩
  else if i = rssNextParty204 p then r.1 else r.2

def rssAuthPartyView204 (p : Fin 3) (shares : Fin 3 → RssAuthShare204) : RssAuthCoins204 :=
  (shares (rssNextParty204 p), shares (rssLastParty204 p))

theorem rssAuthPartyView204_simulated (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    rssAuthPartyView204 p (rssAuthSharing204 p key secret r) = r := by
  obtain ⟨h1, h2, h3⟩ := rssPartyIndices204 p
  simp only [rssAuthPartyView204, rssAuthSharing204, ite_false_of h1, ite_false_of h2,
    ite_false_of h3, ite_true]

private theorem fq_sub_sub_add_add204 (s a b : Fq204) :
    Fq204.add (Fq204.add (Fq204.sub (Fq204.sub s a) b) a) b = s := by
  rw [← Fq204.ofInt_nat s, ← Fq204.ofInt_nat a, ← Fq204.ofInt_nat b]
  simp only [Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1
  omega

/-- Reconstruction of both channels establishes the global MAC invariant. -/
theorem rssAuthSharing204_reconstruct (p : Fin 3) (key secret : Fq204) (r : RssAuthCoins204) :
    let sh := rssAuthSharing204 p key secret r
    Fq204.add (Fq204.add (sh p).value (sh (rssNextParty204 p)).value)
      (sh (rssLastParty204 p)).value = secret ∧
    Fq204.add (Fq204.add (sh p).mac (sh (rssNextParty204 p)).mac)
      (sh (rssLastParty204 p)).mac = Fq204.mul key secret := by
  obtain ⟨h1, h2, h3⟩ := rssPartyIndices204 p
  simp only [rssAuthSharing204, ite_false_of h1, ite_false_of h2, ite_false_of h3,
    ite_true, fq_sub_sub_add_add204, and_self]

/-- The observation before unmasking the rejection bit. Revealing the bit
itself is deliberately not claimed private. -/
def rssMaskedRejectView204 (p : Fin 3) (key secret : Fq204) (reject : Bool)
    (coins : RssAuthCoins204 × Bool) : RssAuthCoins204 × Bool :=
  (rssAuthPartyView204 p (rssAuthSharing204 p key secret coins.1), reject.xor coins.2)

def rssRejectCoinBijection204 (a b : Bool) :
    SimpleEquiv (RssAuthCoins204 × Bool) (RssAuthCoins204 × Bool) where
  toFun c := (c.1, b.xor (a.xor c.2))
  invFun c := (c.1, a.xor (b.xor c.2))
  left_inv c := by rcases c with ⟨r, m⟩; cases a <;> cases b <;> cases m <;> rfl
  right_inv c := by rcases c with ⟨r, m⟩; cases a <;> cases b <;> cases m <;> rfl

/-- One coin bijection preserves the joint per-party share/MAC view and the
masked rejection bit, even when rejection depends arbitrarily on the secret. -/
theorem rssMaskedRejectView204_private (p : Fin 3) (key s t : Fq204)
    (reject : Fq204 → Bool) (c : RssAuthCoins204 × Bool) :
    rssMaskedRejectView204 p key s (reject s) c =
      rssMaskedRejectView204 p key t (reject t)
        ((rssRejectCoinBijection204 (reject s) (reject t)).toFun c) := by
  simp only [rssMaskedRejectView204, rssAuthPartyView204_simulated, rssRejectCoinBijection204]
  rcases c with ⟨r, m⟩
  cases reject s <;> cases reject t <;> cases m <;> rfl

/-! ## Seed expansion: the multi-key hybrid

In `rss_mpc.rs` every replicated component draws its masks from a tape expanded from
that component's own subset key (`Prss::elements`). The theorems above are stated for
independent uniform tapes. This section is the reduction between the two experiments.

Both tape samplers read one coin from a common space `Fin N`: `real r` is the tape
expanded from the key encoded by `r`, `ideal r` an independently sampled tape. A
distinguisher sees the list of all `m` tapes. Hybrid `j` replaces the first `j` tapes.
Neighbouring hybrids differ in one tape, and for every fixing of the other tapes the
distinguisher restricted to that position is a single-key adversary; `hPRF` bounds
exactly these adversaries. All hit counts share the denominator `N^m`, so dividing the
conclusion by `N^m` gives `m` times the single-key advantage `ε / N`.
-/

def prssGap (a b : Nat) : Nat := (a - b) + (b - a)

theorem prssGap_triangle (a b c : Nat) : prssGap a c ≤ prssGap a b + prssGap b c := by
  unfold prssGap
  omega

private theorem prssGap_self (a : Nat) : prssGap a a = 0 := by
  unfold prssGap
  omega

private theorem prssGap_add_le (a b c d : Nat) :
    prssGap (a + c) (b + d) ≤ prssGap a b + prssGap c d := by
  unfold prssGap
  omega

private theorem prssGap_qsum_le {n : Nat} (f g : Fin n → Nat) :
    prssGap (qsum n f) (qsum n g) ≤ qsum n (fun i => prssGap (f i) (g i)) := by
  have h1 : qsum n f ≤ qsum n g + qsum n (fun i => prssGap (f i) (g i)) := by
    rw [← qsum_add]
    exact qsum_le_qsum (fun i => by unfold prssGap; omega)
  have h2 : qsum n g ≤ qsum n f + qsum n (fun i => prssGap (f i) (g i)) := by
    rw [← qsum_add]
    exact qsum_le_qsum (fun i => by unfold prssGap; omega)
  unfold prssGap at *
  omega

/-- Sum over all coin vectors for `m` keys. -/
def prssCoinSum (N : Nat) : (m : Nat) → (List (Fin N) → Nat) → Nat
  | 0, f => f []
  | m + 1, f => qsum N (fun r => prssCoinSum N m (fun rs => f (r :: rs)))

private theorem prssCoinSum_succ (N m : Nat) (f : List (Fin N) → Nat) :
    prssCoinSum N (m + 1) f = qsum N (fun r => prssCoinSum N m (fun rs => f (r :: rs))) := by
  rfl

private theorem prssCoinSum_const (N : Nat) (c : Nat) :
    ∀ m : Nat, prssCoinSum N m (fun _ => c) = N ^ m * c := by
  intro m
  induction m with
  | zero => simp only [prssCoinSum, Nat.pow_zero, Nat.one_mul]
  | succ m ih =>
    rw [prssCoinSum_succ, qsum_congr (fun _ => ih), qsum_const, Nat.pow_succ,
      Nat.mul_comm (N ^ m) N, Nat.mul_assoc]

private theorem prssCoinSum_le (N : Nat) (m : Nat) :
    ∀ (f g : List (Fin N) → Nat), (∀ rs, f rs ≤ g rs) →
      prssCoinSum N m f ≤ prssCoinSum N m g := by
  induction m with
  | zero => intro f g h; exact h []
  | succ m ih =>
    intro f g h
    rw [prssCoinSum_succ, prssCoinSum_succ]
    exact qsum_le_qsum (fun r => ih _ _ (fun rs => h (r :: rs)))

private theorem prssGap_coinSum_le (N : Nat) (m : Nat) :
    ∀ (f g : List (Fin N) → Nat),
      prssGap (prssCoinSum N m f) (prssCoinSum N m g) ≤
        prssCoinSum N m (fun rs => prssGap (f rs) (g rs)) := by
  induction m with
  | zero => intro f g; exact Nat.le_refl _
  | succ m ih =>
    intro f g
    rw [prssCoinSum_succ, prssCoinSum_succ, prssCoinSum_succ]
    exact Nat.le_trans (prssGap_qsum_le _ _) (qsum_le_qsum (fun r => ih _ _))

private theorem prssCoinSum_qsum_comm (N : Nat) (m : Nat) :
    ∀ (F : Fin N → List (Fin N) → Nat),
      qsum N (fun r => prssCoinSum N m (fun rs => F r rs)) =
        prssCoinSum N m (fun rs => qsum N (fun r => F r rs)) := by
  induction m with
  | zero => intro F; rfl
  | succ m ih =>
    intro F
    rw [prssCoinSum_succ]
    have h1 : qsum N (fun r => prssCoinSum N (m + 1) (fun rs => F r rs)) =
        qsum N (fun r => qsum N (fun r' =>
          prssCoinSum N m (fun rs => F r (r' :: rs)))) :=
      qsum_congr (fun r => prssCoinSum_succ N m _)
    rw [h1, qsum_comm]
    exact qsum_congr (fun r' => ih (fun r rs => F r (r' :: rs)))

/-- Hybrid `j`: the first `j` tapes are ideal, the remaining ones are expanded from keys. -/
def prssHybridTapes {O : Type} {N : Nat} (real ideal : Fin N → O) :
    Nat → List (Fin N) → List O
  | _, [] => []
  | 0, r :: rs => real r :: prssHybridTapes real ideal 0 rs
  | j + 1, r :: rs => ideal r :: prssHybridTapes real ideal j rs

def prssHybridHits {O : Type} {N : Nat} (real ideal : Fin N → O) (m j : Nat)
    (D : List O → Bool) : Nat :=
  prssCoinSum N m (fun rs => (D (prssHybridTapes real ideal j rs)).toNat)

/-- Every tape expanded from its own key. -/
def prssRealHits {O : Type} {N : Nat} (real : Fin N → O) (m : Nat) (D : List O → Bool) : Nat :=
  prssCoinSum N m (fun rs => (D (rs.map real)).toNat)

/-- Every tape sampled independently. -/
def prssIdealHits {O : Type} {N : Nat} (ideal : Fin N → O) (m : Nat) (D : List O → Bool) :
    Nat :=
  prssCoinSum N m (fun rs => (D (rs.map ideal)).toNat)

private theorem prssHybridHits_zero_succ {O : Type} {N : Nat} (real ideal : Fin N → O)
    (m : Nat) (D : List O → Bool) :
    prssHybridHits real ideal (m + 1) 0 D =
      qsum N (fun r => prssHybridHits real ideal m 0 (fun t => D (real r :: t))) := by
  rfl

private theorem prssHybridHits_succ_succ {O : Type} {N : Nat} (real ideal : Fin N → O)
    (m j : Nat) (D : List O → Bool) :
    prssHybridHits real ideal (m + 1) (j + 1) D =
      qsum N (fun r => prssHybridHits real ideal m j (fun t => D (ideal r :: t))) := by
  rfl

theorem prssHybridHits_zero {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat) :
    ∀ D : List O → Bool, prssHybridHits real ideal m 0 D = prssRealHits real m D := by
  induction m with
  | zero => intro D; rfl
  | succ m ih =>
    intro D
    rw [prssHybridHits_zero_succ, qsum_congr (fun r => ih _)]
    rfl

theorem prssHybridHits_all {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat) :
    ∀ D : List O → Bool, prssHybridHits real ideal m m D = prssIdealHits ideal m D := by
  induction m with
  | zero => intro D; rfl
  | succ m ih =>
    intro D
    rw [prssHybridHits_succ_succ, qsum_congr (fun r => ih _)]
    rfl

/-- The single-key assumption, for the adversaries the hybrid produces: the
distinguisher with every other tape fixed. -/
def PrssSingleKeyBound {O : Type} {N : Nat} (real ideal : Fin N → O) (D : List O → Bool)
    (ε : Nat) : Prop :=
  ∀ pre post : List O,
    prssGap (qsum N (fun r => (D (pre ++ real r :: post)).toNat))
      (qsum N (fun r => (D (pre ++ ideal r :: post)).toNat)) ≤ ε

private theorem prssSingleKeyBound_cons {O : Type} {N : Nat} {real ideal : Fin N → O}
    {D : List O → Bool} {ε : Nat} (h : PrssSingleKeyBound real ideal D ε) (o : O) :
    PrssSingleKeyBound real ideal (fun t => D (o :: t)) ε :=
  fun pre post => h (o :: pre) post

/-- Neighbouring hybrids differ by the single-key bound, summed over the other coins. -/
theorem prssHybrid_step {O : Type} {N : Nat} (real ideal : Fin N → O) (ε : Nat) :
    ∀ (j m : Nat) (D : List O → Bool), j < m → PrssSingleKeyBound real ideal D ε →
      prssGap (prssHybridHits real ideal m j D) (prssHybridHits real ideal m (j + 1) D) ≤
        N ^ (m - 1) * ε := by
  intro j
  induction j with
  | zero =>
    intro m D hm hPRF
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hL : prssHybridHits real ideal (m' + 1) 0 D =
        prssCoinSum N m' (fun rs => qsum N (fun r =>
          (D (real r :: prssHybridTapes real ideal 0 rs)).toNat)) :=
      prssCoinSum_qsum_comm N m' _
    have hR : prssHybridHits real ideal (m' + 1) 1 D =
        prssCoinSum N m' (fun rs => qsum N (fun r =>
          (D (ideal r :: prssHybridTapes real ideal 0 rs)).toNat)) :=
      prssCoinSum_qsum_comm N m' _
    rw [hL, hR, Nat.add_sub_cancel, ← prssCoinSum_const N ε m']
    exact Nat.le_trans (prssGap_coinSum_le N m' _ _)
      (prssCoinSum_le N m' _ _ (fun rs => hPRF [] _))
  | succ j ih =>
    intro m D hm hPRF
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, m' = k + 1 := ⟨m' - 1, by omega⟩
    rw [prssHybridHits_succ_succ, prssHybridHits_succ_succ]
    refine Nat.le_trans (prssGap_qsum_le _ _) ?_
    have hEach : ∀ r : Fin N,
        prssGap (prssHybridHits real ideal (k + 1) j (fun t => D (ideal r :: t)))
          (prssHybridHits real ideal (k + 1) (j + 1) (fun t => D (ideal r :: t))) ≤
          N ^ k * ε := fun r =>
      ih (k + 1) _ (by omega) (prssSingleKeyBound_cons hPRF (ideal r))
    refine Nat.le_trans (qsum_le_qsum hEach) ?_
    rw [qsum_const, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm (N ^ k) N, Nat.mul_assoc]
    exact Nat.le_refl _

/-- **Multi-key seed-expansion hybrid.** Replacing all `m` key-expanded tapes by
independent tapes changes any distinguisher's hit count by at most `m N^(m-1) ε`, that
is, its acceptance probability by at most `m (ε / N)`. -/
theorem prss_multi_key_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O) (m : Nat)
    (D : List O → Bool) (ε : Nat) (hPRF : PrssSingleKeyBound real ideal D ε) :
    prssGap (prssRealHits real m D) (prssIdealHits ideal m D) ≤ m * (N ^ (m - 1) * ε) := by
  have hAll : ∀ k : Nat, k ≤ m →
      prssGap (prssHybridHits real ideal m 0 D) (prssHybridHits real ideal m k D) ≤
        k * (N ^ (m - 1) * ε) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [prssGap_self]
      exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := prssHybrid_step real ideal ε k m D (by omega) hPRF
      have h3 := prssGap_triangle (prssHybridHits real ideal m 0 D)
        (prssHybridHits real ideal m k D) (prssHybridHits real ideal m (k + 1) D)
      rw [Nat.succ_mul]
      omega
  have h := hAll m (Nat.le_refl m)
  rwa [prssHybridHits_zero, prssHybridHits_all] at h

/-- The three subset keys of the two-of-three replicated sharing. -/
theorem prss_three_key_hybrid {O : Type} {N : Nat} (real ideal : Fin N → O)
    (D : List O → Bool) (ε : Nat) (hPRF : PrssSingleKeyBound real ideal D ε) :
    prssGap (prssRealHits real 3 D) (prssIdealHits ideal 3 D) ≤ 3 * (N ^ 2 * ε) :=
  prss_multi_key_hybrid real ideal 3 D ε hPRF

/-- The single-key bound is needed: an expansion whose tape differs from every ideal
tape is told apart by reading one entry. -/
theorem tooth_prss_constant_expansion_distinguished :
    ∃ D : List Bool → Bool,
      prssGap (prssRealHits (N := 1) (fun _ => false) 1 D)
        (prssIdealHits (N := 1) (fun _ => true) 1 D) ≠ 0 := by
  refine ⟨fun t => t.headD false, ?_⟩
  show prssGap (qsum 1 (fun _ => 0)) (qsum 1 (fun _ => 1)) ≠ 0
  rw [qsum_const, qsum_const]
  decide

private def prssSwap2 (r : Fin 2) : Fin 2 := ⟨1 - r.val, by omega⟩

/-- A two-coin instance in which the two samplers are different functions with the same
distribution; the bound holds with `ε = 0` for a distinguisher that reads a tape. -/
theorem prss_multi_key_hybrid_inhabited :
    ∃ (D : List Bool → Bool) (ε : Nat),
      PrssSingleKeyBound (N := 2) (fun r => decide (r.val = 1)) (fun r => decide (r.val = 0)) D ε ∧
      prssGap (prssRealHits (N := 2) (fun r => decide (r.val = 1)) 3 D)
        (prssIdealHits (N := 2) (fun r => decide (r.val = 0)) 3 D) ≤ 3 * (2 ^ 2 * ε) := by
  have hBound : PrssSingleKeyBound (N := 2) (fun r => decide (r.val = 1))
      (fun r => decide (r.val = 0)) (fun t => t.headD false) 0 := by
    intro pre post
    have hSwap : ∀ r : Fin 2, prssSwap2 (prssSwap2 r) = r := by decide
    have hId : ∀ r : Fin 2, decide (r.val = 0) = decide ((prssSwap2 r).val = 1) := by decide
    have hEq : qsum 2 (fun r => ((pre ++ decide (r.val = 0) :: post).headD false).toNat) =
        qsum 2 (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat) := by
      rw [qsum_congr (fun r => by rw [hId r])]
      exact qsum_perm_invariant prssSwap2 prssSwap2 hSwap hSwap
        (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat)
    show prssGap (qsum 2 (fun r => ((pre ++ decide (r.val = 1) :: post).headD false).toNat))
      (qsum 2 (fun r => ((pre ++ decide (r.val = 0) :: post).headD false).toNat)) ≤ 0
    rw [hEq, prssGap_self]
    exact Nat.le_refl 0
  exact ⟨fun t => t.headD false, 0, hBound, prss_multi_key_hybrid _ _ 3 _ 0 hBound⟩

#tooth_pair prss_multi_key_hybrid vs tooth_prss_constant_expansion_distinguished
#verify_inhabited prss_multi_key_hybrid prss_multi_key_hybrid_inhabited

/-! ## Shamir Threshold ML-DSA (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`) Conversion & Byzantine Soundness -/

/-- Maximum custodian count for Shamir threshold ML-DSA (`MAX_THRESHOLD_MLDSA_PARTIES = 64`). -/
def shamirMldsaMaxCustodians : Nat := 64

/-- Maximum RSS signing-engine quorum size (`MAX_MPC_PARTIES = 16`). -/
def shamirMldsaMaxQuorum : Nat := 16

/-- Parameter validation matching `ThresholdMlDsaDkgConfig::validate_shamir` and
    `threshold_sign_mldsa_party` (`threshold_mldsa_shamir.rs:77-88`, `threshold_mldsa.rs:2117-2125`):
    `2 ≤ t`, `n ≤ 64`, `2t - 1 ≤ n`, and `2t - 1 ≤ m ≤ 16` (hence `t ≤ 8`). -/
def shamirMldsaParamsValid (t n m : Nat) : Bool :=
  decide (2 ≤ t) &&
  decide (n ≤ shamirMldsaMaxCustodians) &&
  decide (2 * t - 1 ≤ n) &&
  decide (2 * t - 1 ≤ m) &&
  decide (m ≤ shamirMldsaMaxQuorum)

theorem shamirMldsaParamsValid_bounds {t n m : Nat}
    (h : shamirMldsaParamsValid t n m = true) :
    2 ≤ t ∧ t ≤ 8 ∧ n ≤ 64 ∧ 2 * t - 1 ≤ n ∧ 2 * t - 1 ≤ m ∧ m ≤ 16 := by
  unfold shamirMldsaParamsValid shamirMldsaMaxCustodians shamirMldsaMaxQuorum at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1.1.1, by omega, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private def polyAddCoeffs204 : List Fq204 → List Fq204 → List Fq204
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => Fq204.add c d :: polyAddCoeffs204 cs ds

private theorem polyAddCoeffs204_length :
    ∀ (cs ds : List Fq204), (polyAddCoeffs204 cs ds).length = Nat.max cs.length ds.length
  | [], ds => by simp [polyAddCoeffs204]
  | c :: cs, [] => by simp [polyAddCoeffs204]
  | c :: cs, d :: ds => by
    simp [polyAddCoeffs204, polyAddCoeffs204_length cs ds, Nat.succ_max_succ]

private theorem evalCoeffs_polyAddCoeffs204 :
    ∀ (cs ds : List Fq204) (x : Fq204),
      RoundPoly.evalCoeffs (polyAddCoeffs204 cs ds) x =
        Fq204.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], ds, x => by
    change RoundPoly.evalCoeffs ds x = Fq204.add Fq204.zero (RoundPoly.evalCoeffs ds x)
    exact (Fq204.zero_add _).symm
  | c :: cs, [], x => by
    change RoundPoly.evalCoeffs (c :: cs) x = Fq204.add (RoundPoly.evalCoeffs (c :: cs) x) Fq204.zero
    exact (Fq204.add_zero _).symm
  | c :: cs, d :: ds, x => by
    simp only [polyAddCoeffs204, RoundPoly.evalCoeffs_cons, evalCoeffs_polyAddCoeffs204 cs ds x]
    change Fq204.add (Fq204.add c d)
        (Fq204.mul x (Fq204.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x))) =
      Fq204.add (Fq204.add c (Fq204.mul x (RoundPoly.evalCoeffs cs x)))
        (Fq204.add d (Fq204.mul x (RoundPoly.evalCoeffs ds x)))
    rw [Fq204.left_distrib,
        Fq204.add_assoc c d _,
        ← Fq204.add_assoc d _ _,
        Fq204.add_comm d (Fq204.mul x (RoundPoly.evalCoeffs cs x)),
        Fq204.add_assoc (Fq204.mul x (RoundPoly.evalCoeffs cs x)) d _,
        ← Fq204.add_assoc c _ _]

def eraseFirstFq204 (x : Fq204) : List Fq204 → List Fq204
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstFq204 x ys

private theorem eraseFirstFq204_length_of_mem {x : Fq204} :
    ∀ {xs : List Fq204}, x ∈ xs → (eraseFirstFq204 x xs).length + 1 = xs.length
  | [], h => nomatch h
  | y :: ys, h => by
    unfold eraseFirstFq204
    if hxy : x = y then
      simp [hxy]
    else
      rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hxy
      · simp only [hxy, ↓reduceIte, List.length_cons]
        have ih := eraseFirstFq204_length_of_mem hm
        omega

private theorem mem_eraseFirstFq204_of_ne {y x : Fq204} (hne : y ≠ x) :
    ∀ {xs : List Fq204}, y ∈ xs → y ∈ eraseFirstFq204 x xs
  | [], h => nomatch h
  | z :: zs, h => by
    unfold eraseFirstFq204
    if hxz : x = z then
      subst hxz
      rcases List.mem_cons.mp h with rfl | hm
      · exact absurd rfl hne
      · simp [hm]
    else
      simp only [hxz, ↓reduceIte, List.mem_cons]
      rcases List.mem_cons.mp h with rfl | hm
      · exact Or.inl rfl
      · exact Or.inr (mem_eraseFirstFq204_of_ne hne hm)

private theorem not_mem_eraseFirstFq204_of_nodup {x : Fq204} :
    ∀ {xs : List Fq204}, xs.Nodup → x ∉ eraseFirstFq204 x xs
  | [], _ => by simp [eraseFirstFq204]
  | y :: ys, .cons hnot hnd => by
    unfold eraseFirstFq204
    if hxy : x = y then
      subst hxy
      simp only [↓reduceIte]
      exact fun hm => hnot x hm rfl
    else
      simp only [hxy, ↓reduceIte, List.mem_cons]
      rintro (hFalse | hm)
      · exact hFalse.elim
      · exact not_mem_eraseFirstFq204_of_nodup hnd hm

/-- Lagrange basis polynomial `L_{pt}(X) = (∏_{o ∈ nodes \ {pt}} (X - o)) · (∏_{o ∈ nodes \ {pt}} (pt - o))⁻¹`
    over `Fq204` (`lagrange_weights`, `threshold_mldsa.rs:2027-2042`). -/
def lagrangeBasisCoeffs204 (nodes : List Fq204) (pt : Fq204) : List Fq204 :=
  let others := eraseFirstFq204 pt nodes
  let denom := RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs others) pt
  (RoundPoly.vanishingCoeffs others).map (Fq204.mul (Fq204.inv denom))

def lagrangeWeightAt204 (nodes : List Fq204) (pt target : Fq204) : Fq204 :=
  RoundPoly.evalCoeffs (lagrangeBasisCoeffs204 nodes pt) target

/-- Lagrange weights mapping degree-`< nodes.length` evaluations at `nodes` to the evaluation at `target`
    (`threshold_mldsa.rs:2027-2042`). -/
def lagrangeWeightsFq204 (nodes : List Fq204) (target : Fq204) : List Fq204 :=
  nodes.map (fun pt => lagrangeWeightAt204 nodes pt target)

private theorem lagrangeWeightAt204_kron {nodes : List Fq204} (hNd : nodes.Nodup)
    {pt y : Fq204} (_hPt : pt ∈ nodes) (hY : y ∈ nodes) :
    lagrangeWeightAt204 nodes pt y = if y = pt then Fq204.one else Fq204.zero := by
  unfold lagrangeWeightAt204 lagrangeBasisCoeffs204
  dsimp only
  have hMap : ∀ (s : Fq204) (cs : List Fq204) (z : Fq204),
      RoundPoly.evalCoeffs (cs.map (Fq204.mul s)) z = Fq204.mul s (RoundPoly.evalCoeffs cs z) :=
    fun s cs z => RoundPoly.evalCoeffs_map_mul s cs z
  rw [hMap]
  if hyEq : y = pt then
    subst hyEq
    simp only [↓reduceIte]
    have hNotMem : y ∉ eraseFirstFq204 y nodes := not_mem_eraseFirstFq204_of_nodup hNd
    have hDenNz : RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs (eraseFirstFq204 y nodes)) y ≠
        CommRingOps.zero :=
      RoundPoly.evalCoeffs_vanishingCoeffs_ne_zero (by decide) _ y hNotMem
    rw [Fq204.mul_comm, Fq204.mul_inv_cancel hDenNz]
  else
    simp only [hyEq, ↓reduceIte]
    have hIn : y ∈ eraseFirstFq204 pt nodes := mem_eraseFirstFq204_of_ne hyEq hY
    have hVan : RoundPoly.evalCoeffs (RoundPoly.vanishingCoeffs (eraseFirstFq204 pt nodes)) y =
        CommRingOps.zero :=
      RoundPoly.evalCoeffs_vanishingCoeffs_of_mem _ y hIn
    rw [hVan]
    exact Fq204.mul_zero _

private def lagrangeInterpLoop204 (allNodes : List Fq204) : List Fq204 → List Fq204 → List Fq204
  | [], _ => []
  | _, [] => []
  | pt :: ptsRest, sh :: shRest =>
    polyAddCoeffs204 ((lagrangeBasisCoeffs204 allNodes pt).map (Fq204.mul sh))
      (lagrangeInterpLoop204 allNodes ptsRest shRest)

/-- Explicit degree-`< nodes.length` Lagrange interpolant over `Fq204`. -/
def lagrangeInterpCoeffs204 (nodes shares : List Fq204) : List Fq204 :=
  lagrangeInterpLoop204 nodes nodes shares

private theorem lagrangeInterpLoop204_length_le (allNodes : List Fq204) :
    ∀ (curNodes curShares : List Fq204),
      (∀ pt ∈ curNodes, pt ∈ allNodes) →
      (lagrangeInterpLoop204 allNodes curNodes curShares).length ≤ allNodes.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], _ => Nat.zero_le _
  | pt :: ptsRest, sh :: shRest, hSub => by
    simp only [lagrangeInterpLoop204, polyAddCoeffs204_length, List.length_map]
    have hBasisLen : (lagrangeBasisCoeffs204 allNodes pt).length = allNodes.length := by
      unfold lagrangeBasisCoeffs204
      simp only [List.length_map, RoundPoly.vanishingCoeffs_length]
      exact eraseFirstFq204_length_of_mem (hSub pt (.head _))
    have ih := lagrangeInterpLoop204_length_le allNodes ptsRest shRest
      (fun z hz => hSub z (.tail _ hz))
    rw [hBasisLen]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, ih⟩

private theorem lagrangeInterpLoop204_eval_eq_dot (allNodes : List Fq204) (target : Fq204) :
    ∀ (curNodes curShares : List Fq204),
      RoundPoly.evalCoeffs (lagrangeInterpLoop204 allNodes curNodes curShares) target =
        ringDot (curNodes.map (fun pt => lagrangeWeightAt204 allNodes pt target)) curShares
  | [], _ => by simp [lagrangeInterpLoop204, ringDot]
  | _ :: _, [] => by simp [lagrangeInterpLoop204, ringDot]
  | pt :: ptsRest, sh :: shRest => by
    simp only [lagrangeInterpLoop204, List.map_cons, evalCoeffs_polyAddCoeffs204,
      lagrangeInterpLoop204_eval_eq_dot allNodes target ptsRest shRest]
    have hTerm : RoundPoly.evalCoeffs ((lagrangeBasisCoeffs204 allNodes pt).map (Fq204.mul sh)) target =
        Fq204.mul (lagrangeWeightAt204 allNodes pt target) sh := by
      have hMap := RoundPoly.evalCoeffs_map_mul sh (lagrangeBasisCoeffs204 allNodes pt) target
      exact hMap.trans (Fq204.mul_comm sh _)
    rw [hTerm]
    rfl

private theorem ringDot_kron_mem {allNodes : List Fq204} (hNd : allNodes.Nodup) :
    ∀ {curNodes curShares : List Fq204},
      curNodes.Nodup →
      (∀ pt ∈ curNodes, pt ∈ allNodes) →
      ∀ {p : Fq204 × Fq204},
        p ∈ List.zip curNodes curShares →
        ringDot (curNodes.map (fun pt => lagrangeWeightAt204 allNodes pt p.1)) curShares = p.2
  | [], _, _, _, _, hp => nomatch hp
  | _ :: _, [], _, _, _, hp => nomatch hp
  | pt :: ptsRest, sh :: shRest, .cons hnot hndRest, hSub, ⟨x, y⟩, hp => by
    have hZeroNotIn : ∀ {ns ss : List Fq204} {z : Fq204},
        z ∈ allNodes →
        (∀ q ∈ ns, q ∈ allNodes) →
        (∀ q ∈ ns, z ≠ q) →
        ringDot (ns.map (fun q => lagrangeWeightAt204 allNodes q z)) ss = Fq204.zero := by
      intro ns
      induction ns with
      | nil => intro _ _ _ _ _; rfl
      | cons q qs ihq =>
        intro ss z hzIn hSubQ hNeQ
        cases ss with
        | nil => rfl
        | cons s ss' =>
          simp only [List.map_cons, ringDot, dotVec]
          have hw0 : lagrangeWeightAt204 allNodes q z = Fq204.zero := by
            rw [lagrangeWeightAt204_kron hNd (hSubQ q (.head _)) hzIn]
            have hne : z ≠ q := hNeQ q (.head _)
            simp [hne]
          rw [hw0]
          change Fq204.add (Fq204.mul Fq204.zero s)
              (ringDot (qs.map (fun q' => lagrangeWeightAt204 allNodes q' z)) ss') = Fq204.zero
          rw [Fq204.zero_mul, Fq204.zero_add]
          exact ihq hzIn (fun q' hq' => hSubQ q' (.tail _ hq'))
            (fun q' hq' => hNeQ q' (.tail _ hq'))
    rcases List.mem_cons.mp hp with hHead | hTail
    · cases hHead
      dsimp only
      simp only [List.map_cons, ringDot, dotVec]
      have hw1 : lagrangeWeightAt204 allNodes pt pt = Fq204.one := by
        rw [lagrangeWeightAt204_kron hNd (hSub pt (.head _)) (hSub pt (.head _))]
        simp
      rw [hw1]
      change Fq204.add (Fq204.mul Fq204.one sh)
          (ringDot (ptsRest.map (fun q => lagrangeWeightAt204 allNodes q pt)) shRest) = sh
      rw [Fq204.one_mul,
          hZeroNotIn (hSub pt (.head _)) (fun q hq => hSub q (.tail _ hq))
            (fun q hq heq => hnot q hq heq),
          Fq204.add_zero]
    · dsimp only
      simp only [List.map_cons, ringDot, dotVec]
      have hxInRest : x ∈ ptsRest := by
        have hFst := List.of_mem_zip hTail
        exact hFst.1
      have hxNePt : x ≠ pt := fun heq => hnot x hxInRest heq.symm
      have hw0 : lagrangeWeightAt204 allNodes pt x = Fq204.zero := by
        rw [lagrangeWeightAt204_kron hNd (hSub pt (.head _)) (hSub x (.tail _ hxInRest))]
        simp [hxNePt]
      rw [hw0]
      change Fq204.add (Fq204.mul Fq204.zero sh)
          (ringDot (ptsRest.map (fun q => lagrangeWeightAt204 allNodes q x)) shRest) = y
      rw [Fq204.zero_mul, Fq204.zero_add]
      exact ringDot_kron_mem hNd hndRest (fun q hq => hSub q (.tail _ hq)) hTail

private theorem poly204_eq_of_agree_ge_t {t : Nat} (ht : 1 ≤ t)
    {Q P S : List Fq204}
    (hQLen : Q.length ≤ t) (hPLen : P.length ≤ t)
    (hSNd : S.Nodup) (hSCard : t ≤ S.length)
    (hAgree : ∀ x ∈ S, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs P x)
    (target : Fq204) :
    RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs P target := by
  if hEq : RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs P target then
    exact hEq
  else
    exfalso
    let diff := RoundPoly.subCoeffs Q P
    have hDiffLen : diff.length ≤ (t - 1) + 1 := by
      dsimp only [diff]
      rw [RoundPoly.subCoeffs_length]
      have hMax : Nat.max Q.length P.length ≤ t := Nat.max_le.mpr ⟨hQLen, hPLen⟩
      omega
    have hDiffTargetNz : RoundPoly.evalCoeffs diff target ≠ CommRingOps.zero := by
      dsimp only [diff]
      rw [RoundPoly.evalCoeffs_sub]
      exact fun hz => hEq (LawfulCommRing.sub_eq_zero_iff.mp hz)
    have hFiltGen : ∀ (U : List Fq204),
        (∀ x ∈ U, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs P x) →
        U.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) = U := by
      intro U
      induction U with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro hAg
        have hx0 : RoundPoly.evalCoeffs diff x = CommRingOps.zero := by
          dsimp only [diff]
          rw [RoundPoly.evalCoeffs_sub, hAg x (.head _), LawfulCommRing.sub_self]
        simp only [List.filter_cons, decide_eq_true hx0, ↓reduceIte]
        exact congrArg (x :: ·) (ih (fun y hy => hAg y (.tail _ hy)))
    have hFiltEq := hFiltGen S hAgree
    have hRootsLe := RoundPoly.roots_nodup_length_le (t - 1) diff S hSNd hDiffLen ⟨target, hDiffTargetNz⟩
    rw [hFiltEq] at hRootsLe
    omega

/-- Exact Shamir-to-additive signing session key conversion (`shamir_session_key`,
    `threshold_mldsa.rs:2055-2085`): uses the first `t` quorum shares to define the degree-`< t`
    interpolant, checks that all remaining `m - t` quorum shares vanish against their Lagrange
    predictions (`KeyShareInconsistent` otherwise), and returns the `t` additive shares
    `λ_i(0) · share_i` summing to `P(0)`. -/
def shamirSessionKeyConvert (t : Nat) (pts shares : List Fq204) : Option (List Fq204) :=
  if decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) then
    let ptsBase := pts.take t
    let sharesBase := shares.take t
    let extraPairs := (List.zip pts shares).drop t
    let checksOk := extraPairs.all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero))
    if checksOk then
      some (List.zipWith Fq204.mul (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase)
    else
      none
  else
    none

private theorem sum_zipWith_mul_eq_ringDot :
    ∀ (ws ss : List Fq204),
      (List.zipWith Fq204.mul ws ss).foldr Fq204.add Fq204.zero = ringDot ws ss
  | [], _ => rfl
  | _ :: _, [] => rfl
  | w :: ws, s :: ss => by
    simp only [List.zipWith_cons_cons, List.foldr_cons, ringDot, dotVec]
    exact congrArg (Fq204.add (Fq204.mul w s)) (sum_zipWith_mul_eq_ringDot ws ss)

private theorem nodup_take_of_nodup {α : Type} :
    ∀ (k : Nat) {xs : List α}, xs.Nodup → (xs.take k).Nodup
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | k + 1, _ :: _xs, .cons hnot hnd =>
    .cons (fun z hz => hnot z (List.mem_of_mem_take hz)) (nodup_take_of_nodup k hnd)

private theorem take_map_fq204 {α β : Type} (f : α → β) :
    ∀ (k : Nat) (xs : List α), (xs.map f).take k = (xs.take k).map f
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => congrArg (f x :: ·) (take_map_fq204 f k xs)

private theorem mem_zip_map_self {α β : Type} (f : α → β) :
    ∀ {xs : List α} {x : α}, x ∈ xs → (x, f x) ∈ List.zip xs (xs.map f)
  | [], _, hx => nomatch hx
  | a :: as, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hTl
    · exact .head _
    · exact .tail _ (mem_zip_map_self f hTl)

/-- **Shamir Threshold ML-DSA Conversion Completeness (`shamirSessionKey_complete`)**:
    For any valid parameter tuple `(t, n, m)` (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`), distinct quorum
    evaluation points `pts` of size `m`, and degree-`< t` secret polynomial `coeffs`,
    honest Shamir shares `pts.map (RoundPoly.evalCoeffs coeffs)` pass all `m - t` syndrome checks
    and convert into additive shares whose sum equals the exact secret `RoundPoly.evalCoeffs coeffs 0`. -/
theorem shamirSessionKey_complete {t n m : Nat}
    (hParams : shamirMldsaParamsValid t n m = true)
    (pts coeffs : List Fq204)
    (hPtsNd : pts.Nodup) (hPtsLen : pts.length = m)
    (hDeg : coeffs.length ≤ t) :
    let shares := pts.map (RoundPoly.evalCoeffs coeffs)
    ∃ additiveShares : List Fq204,
      shamirSessionKeyConvert t pts shares = some additiveShares ∧
      additiveShares.length = t ∧
      additiveShares.foldr Fq204.add Fq204.zero = RoundPoly.evalCoeffs coeffs Fq204.zero := by
  obtain ⟨ht2, _, _, _, hmLo, _⟩ := shamirMldsaParamsValid_bounds hParams
  have ht1 : 1 ≤ t := by omega
  have htLe : t ≤ pts.length := by omega
  let shares := pts.map (RoundPoly.evalCoeffs coeffs)
  have hShLen : pts.length = shares.length := (List.length_map _).symm
  let ptsBase := pts.take t
  let sharesBase := shares.take t
  have hBaseNd : ptsBase.Nodup := nodup_take_of_nodup t hPtsNd
  have hBaseLen : ptsBase.length = t := List.length_take_of_le htLe
  have hShBaseEq : sharesBase = ptsBase.map (RoundPoly.evalCoeffs coeffs) := by
    dsimp only [sharesBase, shares, ptsBase]
    exact take_map_fq204 _ t pts
  let Q := lagrangeInterpCoeffs204 ptsBase sharesBase
  have hQLen : Q.length ≤ t := by
    have hL := lagrangeInterpLoop204_length_le ptsBase ptsBase sharesBase (fun _ h => h)
    rwa [hBaseLen] at hL
  have hQAgreeBase : ∀ x ∈ ptsBase, RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs coeffs x := by
    intro x hx
    have hPairMem : (x, RoundPoly.evalCoeffs coeffs x) ∈ List.zip ptsBase sharesBase := by
      rw [hShBaseEq]
      exact mem_zip_map_self _ hx
    have hEvalDot := lagrangeInterpLoop204_eval_eq_dot ptsBase x ptsBase sharesBase
    have hKron := ringDot_kron_mem hBaseNd hBaseNd (fun _ h => h) hPairMem
    exact hEvalDot.trans hKron
  have hQEqAll : ∀ target : Fq204, RoundPoly.evalCoeffs Q target = RoundPoly.evalCoeffs coeffs target :=
    poly204_eq_of_agree_ge_t ht1 hQLen hDeg hBaseNd (Nat.le_of_eq hBaseLen.symm) hQAgreeBase
  have hChecksOk : ((List.zip pts shares).drop t).all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero)) = true := by
    apply List.all_eq_true.mpr
    intro ps hps
    have hInZip : ps ∈ List.zip pts shares := List.mem_of_mem_drop hps
    have hPs2 : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 := by
      dsimp only [shares] at hInZip
      have hZipMap : ∀ xs : List Fq204, ∀ p ∈ List.zip xs (xs.map (RoundPoly.evalCoeffs coeffs)),
          p.2 = RoundPoly.evalCoeffs coeffs p.1 := by
        intro xs
        induction xs with
        | nil => intro _ hp; nomatch hp
        | cons a as iha =>
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hTl
          · rfl
          · exact iha p hTl
      exact hZipMap pts ps hInZip
    apply decide_eq_true
    have hDot : ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase = RoundPoly.evalCoeffs Q ps.1 :=
      (lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase).symm
    rw [hDot, hQEqAll ps.1, hPs2, fq204_sub_self]
  let out := List.zipWith Fq204.mul (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase
  refine ⟨out, ?_, ?_, ?_⟩
  · unfold shamirSessionKeyConvert
    have hGuard : decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) = true :=
      decide_eq_true ⟨ht1, htLe, hShLen⟩
    rw [hGuard]
    dsimp only
    rw [hChecksOk]
    rfl
  · dsimp only [out, lagrangeWeightsFq204, sharesBase]
    rw [List.length_zipWith, List.length_map, hBaseLen, List.length_take_of_le (by omega), Nat.min_self]
  · dsimp only [out]
    rw [sum_zipWith_mul_eq_ringDot]
    have hDot0 : ringDot (lagrangeWeightsFq204 ptsBase Fq204.zero) sharesBase =
        RoundPoly.evalCoeffs Q Fq204.zero :=
      (lagrangeInterpLoop204_eval_eq_dot ptsBase Fq204.zero ptsBase sharesBase).symm
    rw [hDot0, hQEqAll Fq204.zero]

private theorem filter_partition_length {α : Type} (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length
  | [] => rfl
  | x :: xs => by
    have ih := filter_partition_length p xs
    cases hpx : p x <;> simp [hpx] <;> omega

private theorem zip_take_eq {α β : Type} :
    ∀ (k : Nat) (xs : List α) (ys : List β),
      (List.zip xs ys).take k = List.zip (xs.take k) (ys.take k)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | _ + 1, _ :: _, [] => rfl
  | k + 1, x :: xs, y :: ys => congrArg ((x, y) :: ·) (zip_take_eq k xs ys)

private theorem nodup_map_fst_of_sublist {α β : Type} (p : α × β → Bool) :
    ∀ {xs : List α} {ys : List β},
      xs.Nodup → (((List.zip xs ys).filter p).map Prod.fst).Nodup
  | [], _, _ => .nil
  | _ :: _, [], _ => .nil
  | x :: xs, y :: ys, .cons hnot hnd => by
    simp only [List.zip_cons_cons, List.filter_cons]
    cases p (x, y) with
    | false => exact nodup_map_fst_of_sublist p hnd
    | true =>
      simp only [↓reduceIte, List.map_cons]
      refine .cons ?_ (nodup_map_fst_of_sublist p hnd)
      intro z hz
      obtain ⟨pair, hMemFilt, rfl⟩ := List.mem_map.mp hz
      have hInZip := (List.mem_filter.mp hMemFilt).1
      exact hnot pair.1 (List.of_mem_zip hInZip).1

/-- **Shamir Threshold ML-DSA Byzantine Conversion Soundness (`shamirSessionKey_byzantine_sound`)**:
    For any valid `(t, n, m)` (`n ≤ 64`, `2t - 1 ≤ m ≤ 16`), distinct quorum points `pts` of size `m`,
    degree-`< t` secret polynomial `coeffs`, and submitted quorum shares `shares` with **at most `t - 1`
    corrupt shares**, if `shamirSessionKeyConvert t pts shares = some additiveShares`, then the
    converted additive shares sum to the **exact** secret `RoundPoly.evalCoeffs coeffs 0`! -/
theorem shamirSessionKey_byzantine_sound {t n m : Nat}
    (hParams : shamirMldsaParamsValid t n m = true)
    {pts coeffs shares additiveShares : List Fq204}
    (hPtsNd : pts.Nodup) (hLens : (pts.length, shares.length) = (m, m))
    (hDeg : coeffs.length ≤ t)
    (hCorruptLe :
      ((List.zip pts shares).filter
        (fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1))).length ≤ t - 1)
    (hConv : shamirSessionKeyConvert t pts shares = some additiveShares) :
    additiveShares.foldr Fq204.add Fq204.zero = RoundPoly.evalCoeffs coeffs Fq204.zero := by
  have hPtsLen : pts.length = m := (Prod.mk.injEq _ _ _ _).mp hLens |>.1
  have hShLen : shares.length = m := (Prod.mk.injEq _ _ _ _).mp hLens |>.2
  obtain ⟨ht2, _, _, _, hmLo, _⟩ := shamirMldsaParamsValid_bounds hParams
  have ht1 : 1 ≤ t := by omega
  have htLe : t ≤ pts.length := by omega
  unfold shamirSessionKeyConvert at hConv
  have hGuard : decide (1 ≤ t ∧ t ≤ pts.length ∧ pts.length = shares.length) = true :=
    decide_eq_true ⟨ht1, htLe, hPtsLen.trans hShLen.symm⟩
  rw [hGuard] at hConv
  dsimp only at hConv
  let ptsBase := pts.take t
  let sharesBase := shares.take t
  let extraPairs := (List.zip pts shares).drop t
  cases hChecks : extraPairs.all (fun ps =>
      decide (Fq204.sub ps.2 (ringDot (lagrangeWeightsFq204 ptsBase ps.1) sharesBase) = Fq204.zero)) with
  | false => rw [hChecks] at hConv; cases hConv
  | true =>
    rw [hChecks] at hConv
    simp only [↓reduceIte, Option.some.injEq] at hConv
    subst hConv
    have hBaseNd : ptsBase.Nodup := nodup_take_of_nodup t hPtsNd
    have hBaseLen : ptsBase.length = t := List.length_take_of_le htLe
    let Q := lagrangeInterpCoeffs204 ptsBase sharesBase
    have hQLen : Q.length ≤ t := by
      have hL := lagrangeInterpLoop204_length_le ptsBase ptsBase sharesBase (fun _ h => h)
      rwa [hBaseLen] at hL
    have hPairOnQ : ∀ ps ∈ List.zip pts shares, RoundPoly.evalCoeffs Q ps.1 = ps.2 := by
      intro ps hMem
      rw [← List.take_append_drop t (List.zip pts shares)] at hMem
      rcases List.mem_append.mp hMem with hInTake | hInDrop
      · rw [zip_take_eq t pts shares] at hInTake
        have hEval := lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase
        have hKron := ringDot_kron_mem hBaseNd hBaseNd (fun _ h => h) hInTake
        exact hEval.trans hKron
      · have hChk := of_decide_eq_true (List.all_eq_true.mp hChecks ps hInDrop)
        have hEqDot := fq204_eq_of_sub_eq_zero hChk
        have hEval := lagrangeInterpLoop204_eval_eq_dot ptsBase ps.1 ptsBase sharesBase
        exact hEval.trans hEqDot.symm
    let isBad : Fq204 × Fq204 → Bool := fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1)
    let honestPairs := (List.zip pts shares).filter (fun ps => !isBad ps)
    have hZipLen : (List.zip pts shares).length = m := by
      rw [List.length_zip, hPtsLen, hShLen, Nat.min_self]
    have hPart := filter_partition_length isBad (List.zip pts shares)
    have hHonestLen : t ≤ honestPairs.length := by
      dsimp only [honestPairs, isBad] at hPart ⊢
      omega
    let honestPts := honestPairs.map Prod.fst
    have hHonestPtsNd : honestPts.Nodup := nodup_map_fst_of_sublist (fun ps => !isBad ps) hPtsNd
    have hHonestPtsLen : t ≤ honestPts.length := by
      dsimp only [honestPts]; rwa [List.length_map]
    have hAgreeHonest : ∀ x ∈ honestPts,
        RoundPoly.evalCoeffs Q x = RoundPoly.evalCoeffs coeffs x := by
      intro x hx
      obtain ⟨ps, hpsMem, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hInZip, hNotBad⟩ := List.mem_filter.mp hpsMem
      have hGood : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 := by
        dsimp only [isBad] at hNotBad
        if hEq : ps.2 = RoundPoly.evalCoeffs coeffs ps.1 then
          exact hEq
        else
          simp [hEq] at hNotBad
      exact (hPairOnQ ps hInZip).trans hGood
    have hAt0 := poly204_eq_of_agree_ge_t ht1 hQLen hDeg hHonestPtsNd hHonestPtsLen hAgreeHonest Fq204.zero
    rw [sum_zipWith_mul_eq_ringDot]
    exact (lagrangeInterpLoop204_eval_eq_dot ptsBase Fq204.zero ptsBase sharesBase).symm.trans hAt0

/-- **`#tooth` (`tooth_shamirSessionKey_corrupt_threshold_forges`)**:
    When `t` custodians are corrupt (violating `≤ t - 1`, or when `m = t` omits the `m - t`
    syndrome checks), a forged degree-`< t` share vector passes `shamirSessionKeyConvert` while
    reconstructing a forged secret `≠ RoundPoly.evalCoeffs coeffs 0`! -/
theorem tooth_shamirSessionKey_corrupt_threshold_forges :
    ∃ (pts coeffs forgedShares out : List Fq204),
      shamirMldsaParamsValid 2 64 3 = true ∧
      pts.Nodup ∧ pts.length = 3 ∧ forgedShares.length = 3 ∧ coeffs.length ≤ 2 ∧
      shamirSessionKeyConvert 2 pts forgedShares = some out ∧
      out.foldr Fq204.add Fq204.zero ≠ RoundPoly.evalCoeffs coeffs Fq204.zero := by
  let pts : List Fq204 := [Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3]
  let coeffs : List Fq204 := [Fq204.zero, Fq204.zero]
  -- Forged linear polynomial `f(X) = 3 - X` agrees with `coeffs = 0` at `X = 3` (`1` honest party,
  -- `2 = t` corrupt parties at `X = 1, 2`) and reconstructs `f(0) = 3 ≠ 0`!
  let forgedPoly : List Fq204 := [Fq204.ofNat 3, Fq204.neg Fq204.one]
  let forgedShares : List Fq204 := pts.map (RoundPoly.evalCoeffs forgedPoly)
  obtain ⟨out, hConv, _, hSum⟩ :=
    shamirSessionKey_complete (t := 2) (n := 64) (m := 3) (by decide) pts forgedPoly
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun x hx heq => by subst heq; revert hx; decide)
          (.cons (fun _ h => nomatch h) .nil)))
      rfl (by decide)
  refine ⟨pts, coeffs, forgedShares, out, by decide,
    .cons (fun x hx heq => by subst heq; revert hx; decide)
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun _ h => nomatch h) .nil)),
    rfl, rfl, by decide, hConv, ?_⟩
  rw [hSum]
  decide

theorem inhabited_shamirSessionKey_byzantine_sound :
    ∃ (t n m : Nat) (pts coeffs shares additiveShares : List Fq204),
      shamirMldsaParamsValid t n m = true ∧
      pts.Nodup ∧ (pts.length, shares.length) = (m, m) ∧ coeffs.length ≤ t ∧
      ((List.zip pts shares).filter
        (fun ps => decide (ps.2 ≠ RoundPoly.evalCoeffs coeffs ps.1))).length ≤ t - 1 ∧
      shamirSessionKeyConvert t pts shares = some additiveShares := by
  have hNd : ([Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3] : List Fq204).Nodup :=
    .cons (fun x hx heq => by subst heq; revert hx; decide)
      (.cons (fun x hx heq => by subst heq; revert hx; decide)
        (.cons (fun _ h => nomatch h) .nil))
  exact ⟨2, 64, 3,
    [Fq204.ofNat 1, Fq204.ofNat 2, Fq204.ofNat 3],
    [],
    [Fq204.zero, Fq204.zero, Fq204.zero],
    [Fq204.zero, Fq204.zero],
    by decide, hNd, rfl, by decide, by decide, by decide⟩

#tooth_pair shamirSessionKey_byzantine_sound vs tooth_shamirSessionKey_corrupt_threshold_forges
#verify_inhabited shamirSessionKey_byzantine_sound inhabited_shamirSessionKey_byzantine_sound

#verify_constructive shamirSessionKey_complete shamirSessionKey_byzantine_sound

end Qsag
end
