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

