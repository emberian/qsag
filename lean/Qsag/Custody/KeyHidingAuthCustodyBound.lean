module
/-
# Qsag.Custody.KeyHidingAuthCustodyBound — key-hiding PRF custody tags and their forgery bound

A custodian tag that is a PRF value of the permit, the adaptive tag-forgery experiment for it,
and the reduction of that experiment to `Spec.PrfHard`.

**Scope.**

1. `refinesOfEq`: a `Spec.Refines` witness (identity relation) for two equal machines over one
   state type, with its relation and initial map characterised
   (`refinesOfEq_rel`, `refinesOfEq_absInit`, `refinesOfEq_runStep`).
2. `encodePermit`: an injective byte encoding of `Spec.CustodyApproval`
   (`encodePermit_injective`), and `prfCustodyTag prf dg key permit = prf key (dg (encodePermit
   permit))`. `dg` is a digest to the fixed input length of the PRF; `Spec.PrfHard` speaks about
   one input length only.
3. The tag experiment. An adversary is a `Spec.Code` program over `tagIface M` (query a message,
   receive its tag); the challenger answers the first `q` queries and logs them. Three events of
   one run: `encFreshTagGame` (a correct tag on an input of the keyed function that was never
   queried), `eufCmaTagGame` (a correct tag on a message that was never queried) and
   `encCollisionGame` (the output message has the encoding of a different queried message).
4. Proved, for every coin split, every uniform sampler on `Spec.PrfSampleOk` and every randomized
   adversary:
   * `tagForge_prf_hop`: the real and the random-function forgery experiments differ by at most
     `ε` under `Spec.PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε`. The reduction is
     `tagForgeDistinguisher` (`q + 1` oracle calls on every path,
     `tagForgeDistinguisher_within`); its membership in `𝒜` is a hypothesis.
   * `encFreshTagGame_random_function_bound`: against a function sampled uniformly from a set
     that is closed under changing one in-domain value (`SupportShiftClosed`), the forgery
     probability is at most `256 ^ (-outLen)`. An exact count, by a fixed-point-free XOR shift of
     the value at the forged input.
   * `prfTag_forgery_bound`, `eufCmaTag_forgery_bound`, `prfCustodyTag_unforgeable`: the two
     combined, `ε + 256 ^ (-outLen)`, plus the probability of `encCollisionGame` for message
     freshness. A collision of permit encodings is a collision of `dg`
     (`permitCollision_yields_digest_collision`).
   * `custodianKeys_forgery_union_bound`: an event that implies a forgery under one of `k`
     custodian keys has probability at most `k * (ε + 256 ^ (-outLen))`.
   * `prfTag_view_key_hiding`: any Boolean function of `q` adaptively requested tags is within
     `ε` of the same function computed from a random function, which does not read the key.
5. Negative results: a tag that equals the key is forged with probability one after one query
   (`tooth_toyCustodyTag_one_query_forgery`, `tooth_toyPermitTag_one_query_forgery`), and the
   closure hypothesis of the counting bound cannot be dropped
   (`tooth_singleFunction_support_forged`).

The full PRF sample space satisfies shift closure by `prfSampleOk_shiftClosed`. The probability of `encCollisionGame`
is left as a term. Nothing here mentions the authenticated custodian network; the composition
with it is in `Qsag.Top.CustodyKeyHidingBound`.
-/

public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCustody
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Encoding
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.KeyHidingCustody

open Qsag.Spec

set_option autoImplicit false

/-! ## 0. Finite sums -/

private theorem ifPos.{u} {α : Sort u} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem ifNeg.{u} {α : Sort u} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem ssum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    sampleSum n f = sampleSum n g :=
  congrArg (sampleSum n) (funext h)

private theorem ssum_le :
    ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i ≤ g i) → sampleSum n f ≤ sampleSum n g
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h => by
    rw [sampleSum_succ, sampleSum_succ]
    exact Nat.add_le_add (h _) (ssum_le n _ _ (fun i => h _))

private theorem ssum_const : ∀ (n k : Nat), sampleSum n (fun _ => k) = n * k
  | 0, k => by rw [sampleSum_zero, Nat.zero_mul]
  | n + 1, k => by
    rw [sampleSum_succ, ssum_const n k, Nat.succ_mul]
    exact Nat.add_comm _ _

private theorem ssum_add :
    ∀ (n : Nat) (f g : Fin n → Nat),
      sampleSum n (fun i => f i + g i) = sampleSum n f + sampleSum n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
    rw [sampleSum_succ, sampleSum_succ n f, sampleSum_succ n g, ssum_add n]
    omega

private theorem ssum_mul_right :
    ∀ (n : Nat) (f : Fin n → Nat) (k : Nat),
      sampleSum n (fun i => f i * k) = sampleSum n f * k
  | 0, _, k => by rw [sampleSum_zero, sampleSum_zero, Nat.zero_mul]
  | n + 1, f, k => by
    rw [sampleSum_succ, sampleSum_succ n f, ssum_mul_right n, Nat.add_mul]

private theorem ssum_exchange :
    ∀ (a b : Nat) (g : Fin a → Fin b → Nat),
      sampleSum a (fun i => sampleSum b (g i)) =
        sampleSum b (fun j => sampleSum a (fun i => g i j))
  | 0, b, g => by
    rw [sampleSum_zero]
    have h : (fun j : Fin b => sampleSum 0 (fun i => g i j)) = fun _ => 0 :=
      funext (fun _ => sampleSum_zero _)
    rw [h, ssum_const, Nat.mul_zero]
  | a + 1, b, g => by
    rw [sampleSum_succ, ssum_exchange a b (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩),
      ← ssum_add]
    exact ssum_congr (fun j => (sampleSum_succ a (fun i => g i j)).symm)

private theorem ssum_single_le :
    ∀ (k : Nat) (f : Fin k → Nat) (p : Fin k), f p ≤ sampleSum k f
  | 0, _, p => nomatch p
  | k + 1, f, ⟨0, _⟩ => by
    rw [sampleSum_succ]
    exact Nat.le_add_right _ _
  | k + 1, f, ⟨p + 1, hp⟩ => by
    rw [sampleSum_succ]
    exact Nat.le_trans
      (ssum_single_le k (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        ⟨p, Nat.lt_of_succ_lt_succ hp⟩)
      (Nat.le_add_left _ _)

private theorem ssum_indicator_le_one :
    ∀ (k : Nat) (b : Fin k → Bool),
      (∀ i j, b i = true → b j = true → i = j) →
      sampleSum k (fun i => if b i then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | k + 1, b, h => by
    rw [sampleSum_succ]
    cases h0 : b ⟨0, Nat.zero_lt_succ k⟩ with
    | false =>
      exact Nat.le_trans (Nat.le_of_eq (Nat.zero_add _))
        (ssum_indicator_le_one k (fun i => b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
          (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (h _ _ hi hj)))))
    | true =>
      have hz : ∀ i : Fin k, b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = false := by
        intro i
        cases hb : b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ with
        | false => rfl
        | true => exact absurd (congrArg Fin.val (h _ _ h0 hb)) (Nat.succ_ne_zero i.1).symm
      have hTail : sampleSum k
          (fun i : Fin k => if b ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = true then 1 else 0) = 0 := by
        rw [ssum_congr (g := fun _ => 0) (fun i => by rw [hz i]; rfl), ssum_const, Nat.mul_zero]
      rw [hTail]
      exact Nat.le_refl 1

/-- Reindexing a finite sum by an involution. -/
private theorem ssum_invol {n : Nat} (s : Fin n → Fin n) (hs : ∀ c, s (s c) = c)
    (w : Fin n → Nat) : sampleSum n (fun c => w (s c)) = sampleSum n w := by
  let π : CoinSplit n n 1 :=
    { chal := s
      advc := fun _ => ⟨0, Nat.one_pos⟩
      pair := fun c _ => s c
      chal_pair := fun c _ => hs c
      advc_pair := fun _ a => Fin.ext (by have := a.2; omega)
      pair_eta := fun ω => hs ω }
  have h := CoinSplit.sampleSum_eq π w
  rw [h]
  exact ssum_congr (fun c => by
    show w (s c) = sampleSum 1 (fun _ => w (s c))
    rw [sampleSum_succ, sampleSum_zero]
    exact (Nat.add_zero _).symm)

private theorem fin_choice :
    ∀ (n : Nat) {m : Nat} (P : Fin n → Fin m → Prop),
      (∀ i, ∃ j, P i j) → ∃ s : Fin n → Fin m, ∀ i, P i (s i)
  | 0, _, _, _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
  | n + 1, m, P, h => by
    obtain ⟨j0, hj0⟩ := h ⟨0, Nat.zero_lt_succ n⟩
    obtain ⟨s, hs⟩ := fin_choice n (fun i j => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)
      (fun i => h _)
    refine ⟨fun i =>
      match i with
      | ⟨0, _⟩ => j0
      | ⟨v + 1, hv⟩ => s ⟨v, Nat.lt_of_succ_lt_succ hv⟩, ?_⟩
    intro i
    match i with
    | ⟨0, _⟩ => exact hj0
    | ⟨v + 1, hv⟩ => exact hs ⟨v, Nat.lt_of_succ_lt_succ hv⟩

/-- **Counting by a free family of involutions.** If for each of `m` indices `p` the indicator
    `W' p` is `W` reindexed by an involution, and at most one `p` makes `W' p c` true at each
    `c`, then `W` holds on at most a `1 / m` fraction of the `nC` points. -/
private theorem shift_count {nC m : Nat} (W : Fin nC → Bool) (W' : Fin m → Fin nC → Bool)
    (hPerm : ∀ p, ∃ s : Fin nC → Fin nC, (∀ c, s (s c) = c) ∧ ∀ c, W' p c = W (s c))
    (hOne : ∀ c p p', W' p c = true → W' p' c = true → p = p') :
    sampleSum nC (fun c => if W c then 1 else 0) * m ≤ nC := by
  have hEach : ∀ p : Fin m,
      sampleSum nC (fun c => if W' p c then 1 else 0) =
        sampleSum nC (fun c => if W c then 1 else 0) := by
    intro p
    obtain ⟨s, hs, hW⟩ := hPerm p
    rw [ssum_congr (g := fun c => (fun c => if W c then 1 else 0) (s c))
      (fun c => by rw [hW c])]
    exact ssum_invol s hs (fun c => if W c then 1 else 0)
  have hSum : sampleSum m (fun p => sampleSum nC (fun c => if W' p c then 1 else 0)) =
      m * sampleSum nC (fun c => if W c then 1 else 0) := by
    rw [ssum_congr (g := fun _ => sampleSum nC (fun c => if W c then 1 else 0)) hEach,
      ssum_const]
  have hLe : sampleSum m (fun p => sampleSum nC (fun c => if W' p c then 1 else 0)) ≤ nC := by
    rw [ssum_exchange m nC (fun p c => if W' p c then 1 else 0)]
    have h1 : sampleSum nC (fun c => sampleSum m (fun p => if W' p c then 1 else 0)) ≤
        sampleSum nC (fun _ => 1) :=
      ssum_le nC _ _ (fun c => ssum_indicator_le_one m (fun p => W' p c) (hOne c))
    rw [ssum_const, Nat.mul_one] at h1
    exact h1
  rw [Nat.mul_comm, ← hSum]
  exact hLe

/-- A game's winning probability is at most its distinguishing advantage from another game plus
    the other game's winning probability. -/
private theorem winProb_le_advDist_add {n : Nat} (G₁ G₀ : FinGame n) :
    GameBound G₁.winProb ((AdvDist G₁ G₀).add G₀.winProb) := by
  show G₁.winCount * (n * n) ≤ (natAbsDiff G₁.winCount G₀.winCount * n + G₀.winCount * n) * n
  have h : G₁.winCount ≤ natAbsDiff G₁.winCount G₀.winCount + G₀.winCount := by
    unfold natAbsDiff
    by_cases hab : G₁.winCount ≤ G₀.winCount
    · rw [ifPos hab]; omega
    · rw [ifNeg hab]; omega
  rw [← Nat.add_mul, Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ h

/-- **Union bound over a finite family of reductions.** If every winning coin of `G₀` is a
    winning coin of one of the `k` games `R p`, and each `R p` has probability at most `δ`, then
    `G₀` has probability at most `k * δ`. -/
theorem event_le_family_reductions {n k : Nat} (G₀ : FinGame n) (R : Fin k → FinGame n)
    (hExtract : ∀ ω : Fin n, G₀.win ω = true → ∃ p : Fin k, (R p).win ω = true)
    {δ : Spec.RatBound} (hBound : ∀ p : Fin k, GameBound (R p).winProb δ) :
    GameBound G₀.winProb (δ.scale k) := by
  show G₀.winCount * δ.den ≤ (k * δ.num) * n
  have hPoint : ∀ ω : Fin n, (if G₀.win ω then 1 else 0) ≤
      sampleSum k (fun p => if (R p).win ω then 1 else 0) := by
    intro ω
    cases hg : G₀.win ω with
    | false => exact Nat.zero_le _
    | true =>
      obtain ⟨p, hp⟩ := hExtract ω hg
      have h1 := ssum_single_le k (fun p => if (R p).win ω then 1 else 0) p
      have h2 : (if (R p).win ω = true then 1 else 0) = 1 := by rw [hp]; rfl
      rw [h2] at h1
      exact h1
  have hCount : G₀.winCount ≤ sampleSum k (fun p => (R p).winCount) := by
    rw [FinGame.winCount_eq]
    have h1 := ssum_le n _ _ hPoint
    rw [ssum_exchange n k (fun ω p => if (R p).win ω then 1 else 0)] at h1
    exact Nat.le_trans h1 (Nat.le_of_eq (ssum_congr (fun p => (FinGame.winCount_eq (R p)).symm)))
  have hEach : ∀ p : Fin k, (R p).winCount * δ.den ≤ δ.num * n := fun p => hBound p
  have h2 : sampleSum k (fun p => (R p).winCount) * δ.den ≤ k * (δ.num * n) := by
    rw [← ssum_mul_right, ← ssum_const k (δ.num * n)]
    exact ssum_le k _ _ hEach
  rw [Nat.mul_assoc]
  exact Nat.le_trans (Nat.mul_le_mul_right _ hCount) h2

/-! ## 1. A `Spec.Refines` witness for equal machines -/

/-- Two equal machines over one state type refine each other through the identity relation. -/
def refinesOfEq {S In Out : Type} {M₁ M₂ : Machine S In Out} (h : M₁ = M₂) : Refines M₁ M₂ where
  Rel := Eq
  absInit s := s
  init_ok hInit := ⟨h ▸ hInit, rfl⟩
  sim_ok hRel hStep := by
    subst hRel
    subst h
    rw [hStep]
    exact ⟨rfl, rfl⟩
  sim_err hRel hNone := by
    subst hRel
    subst h
    exact ⟨hNone, rfl⟩

theorem refinesOfEq_rel {S In Out : Type} {M₁ M₂ : Machine S In Out} (h : M₁ = M₂) (c a : S) :
    (refinesOfEq h).Rel c a ↔ c = a :=
  Iff.rfl

theorem refinesOfEq_absInit {S In Out : Type} {M₁ M₂ : Machine S In Out} (h : M₁ = M₂)
    (c : S) : (refinesOfEq h).absInit c = c := by
  rfl

/-- The witness of `refinesOfEq`, read through `Spec.Refines.preserve_runStep`: from one state
    the two machines produce the same output and the same next state on every input. -/
theorem refinesOfEq_runStep {S In Out : Type} {M₁ M₂ : Machine S In Out} (h : M₁ = M₂)
    (s : S) (inp : In) :
    (M₁.runStep s inp).2 = (M₂.runStep s inp).2 ∧ (M₁.runStep s inp).1 = (M₂.runStep s inp).1 :=
  (refinesOfEq h).preserve_runStep inp (rfl : (refinesOfEq h).Rel s s)

/-! ## 2. Permit encoding -/

/-- Byte encoding of an approval permit: the five numeric fields in the self-delimiting unary
    framing of `Qsag.frameLength`, then the payload. It needs no size bound on any field. -/
def encodePermit (a : CustodyApproval) : Bytes :=
  frameLength a.party (frameLength a.deploymentId (frameLength a.intent.sessionId
    (frameLength a.intent.round (frameLength a.intent.epoch
      (frameLength a.intent.spend a.intent.payload)))))

/-- The permit encoding determines the permit. -/
theorem encodePermit_injective {a b : CustodyApproval} (h : encodePermit a = encodePermit b) :
    a = b := by
  unfold encodePermit at h
  obtain ⟨h1, h⟩ := frameLength_inj _ _ _ _ h
  obtain ⟨h2, h⟩ := frameLength_inj _ _ _ _ h
  obtain ⟨h3, h⟩ := frameLength_inj _ _ _ _ h
  obtain ⟨h4, h⟩ := frameLength_inj _ _ _ _ h
  obtain ⟨h5, h⟩ := frameLength_inj _ _ _ _ h
  obtain ⟨h6, h7⟩ := frameLength_inj _ _ _ _ h
  exact CustodyApproval.eq_of_fields h1 h2 (CustodyIntent.eq_of_fields h3 h4 h5 h6 h7)

/-- The key-hiding custody tag: the PRF under the custodian's key of the digest of the encoded
    permit. -/
def prfCustodyTag (prf : Bytes → Bytes → Bytes) (dg : Bytes → Bytes) (key : Bytes)
    (permit : CustodyApproval) : Bytes :=
  prf key (dg (encodePermit permit))

/-- The input of the keyed function for a permit. -/
def permitInput (dg : Bytes → Bytes) (permit : CustodyApproval) : Bytes :=
  dg (encodePermit permit)

theorem prfCustodyTag_eq (prf : Bytes → Bytes → Bytes) (dg : Bytes → Bytes) (key : Bytes)
    (permit : CustodyApproval) :
    prfCustodyTag prf dg key permit = prf key (permitInput dg permit) := by
  rfl

/-! ## 3. The tag experiment -/

/-- Tag-oracle interface: a message is queried, its tag is returned. -/
@[expose, reducible] def tagIface (M : Type) : Iface where
  Query := M
  Resp _ := Bytes

/-- The challenger of the tag experiment for the keyed function `f` on encoded messages: the
    first `q` queries are answered and logged, later ones are answered `[]`. -/
def tagOracle {M : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat) (log : List M) :
    (m : (tagIface M).Query) → (tagIface M).Resp m × List M :=
  fun m => if log.length < q then (f (enc m), log ++ [m]) else ([], log)

theorem tagOracle_pos {M : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    {log : List M} (h : log.length < q) (m : M) :
    tagOracle enc f q log m = (f (enc m), log ++ [m]) :=
  ifPos h _ _

theorem tagOracle_neg {M : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    {log : List M} (h : ¬ log.length < q) (m : M) :
    tagOracle enc f q log m = ([], log) :=
  ifNeg h _ _

/-- One run of the tag experiment: the adversary's output and the log of answered queries. -/
def tagRun {M R : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    (A : Code (tagIface M) R) : R × List M :=
  Code.play (tagOracle enc f q) A []

/-- The output message has an encoding of length `inLen` that no answered query has. -/
def freshPointOk {M : Type} (enc : M → Bytes) (inLen : Nat) (r : (M × Bytes) × List M) : Bool :=
  decide (enc r.1.1 ∉ r.2.map enc) && decide ((enc r.1.1).length = inLen)

/-- Forgery on a fresh input of the keyed function: `freshPointOk` and the output tag is the
    value of `f` there. -/
def encFreshWin {M : Type} (enc : M → Bytes) (inLen : Nat) (f : Bytes → Bytes)
    (r : (M × Bytes) × List M) : Bool :=
  freshPointOk enc inLen r && decide (r.1.2 = f (enc r.1.1))

/-- Forgery on a fresh message: the output message was not queried and carries its tag. -/
def msgFreshWin {M : Type} [DecidableEq M] (enc : M → Bytes) (f : Bytes → Bytes)
    (r : (M × Bytes) × List M) : Bool :=
  decide (r.1.1 ∉ r.2) && decide (r.1.2 = f (enc r.1.1))

/-- Some answered query is a different message with the encoding of the output message. -/
def encCollision {M : Type} [DecidableEq M] (enc : M → Bytes) (r : (M × Bytes) × List M) :
    Bool :=
  r.2.any (fun m => decide (m ≠ r.1.1) && decide (enc m = enc r.1.1))

/-- **Fresh-input forgery game** for the coin-indexed keyed function `fn`, query budget `q` and
    adversary `adv`. -/
def encFreshTagGame {n : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (fn : Fin n → Bytes → Bytes) (adv : Fin n → Code (tagIface M) (M × Bytes)) : FinGame n :=
  ⟨hPos, fun ω => encFreshWin enc inLen (fn ω) (tagRun enc (fn ω) q (adv ω))⟩

/-- **Existential-forgery game under adaptive chosen-message attack** (fresh message). -/
def eufCmaTagGame {n : Nat} (hPos : 0 < n) {M : Type} [DecidableEq M] (enc : M → Bytes)
    (q : Nat) (fn : Fin n → Bytes → Bytes) (adv : Fin n → Code (tagIface M) (M × Bytes)) :
    FinGame n :=
  ⟨hPos, fun ω => msgFreshWin enc (fn ω) (tagRun enc (fn ω) q (adv ω))⟩

/-- The event that the run exhibits two different messages with one encoding. -/
def encCollisionGame {n : Nat} (hPos : 0 < n) {M : Type} [DecidableEq M] (enc : M → Bytes)
    (q : Nat) (fn : Fin n → Bytes → Bytes) (adv : Fin n → Code (tagIface M) (M × Bytes)) :
    FinGame n :=
  ⟨hPos, fun ω => encCollision enc (tagRun enc (fn ω) q (adv ω))⟩

/-- The view game: the adversary outputs one bit after its queries. -/
def tagViewGame {n : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes) (q : Nat)
    (fn : Fin n → Bytes → Bytes) (adv : Fin n → Code (tagIface M) Bool) : FinGame n :=
  ⟨hPos, fun ω => (tagRun enc (fn ω) q (adv ω)).1⟩

/-- The challenger answers at most `q` queries. -/
theorem tagRun_log_length_le {M R : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    (A : Code (tagIface M) R) : (tagRun enc f q A).2.length ≤ q :=
  Code.play_invariant (tagOracle enc f q) (fun log => log.length ≤ q)
    (fun log m h => by
      by_cases hc : log.length < q
      · rw [tagOracle_pos enc f q hc]
        show (log ++ [m]).length ≤ q
        rw [List.length_append]
        exact hc
      · rw [tagOracle_neg enc f q hc]
        exact h)
    A [] (Nat.zero_le q)

/-- A winning coin of the fresh-message game: the output message is not in the log and its tag
    is the value of the keyed function. -/
theorem eufCmaTagGame_win_sound {n : Nat} (hPos : 0 < n) {M : Type} [DecidableEq M]
    (enc : M → Bytes) (q : Nat) (fn : Fin n → Bytes → Bytes)
    (adv : Fin n → Code (tagIface M) (M × Bytes)) (ω : Fin n)
    (hWin : (eufCmaTagGame hPos enc q fn adv).win ω = true) :
    (tagRun enc (fn ω) q (adv ω)).1.1 ∉ (tagRun enc (fn ω) q (adv ω)).2 ∧
    (tagRun enc (fn ω) q (adv ω)).1.2 = fn ω (enc (tagRun enc (fn ω) q (adv ω)).1.1) := by
  have hG : (eufCmaTagGame hPos enc q fn adv).win ω = true := hWin
  have hW : msgFreshWin enc (fn ω) (tagRun enc (fn ω) q (adv ω)) = true := hG
  unfold msgFreshWin at hW
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hW
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- A fresh-message forgery is a fresh-input forgery or exhibits an encoding collision, when
    every encoding has the input length of the keyed function. -/
theorem msgFreshWin_encFresh_or_collision {M : Type} [DecidableEq M] (enc : M → Bytes)
    (inLen : Nat) (hLen : ∀ m : M, (enc m).length = inLen) (f : Bytes → Bytes)
    (r : (M × Bytes) × List M) (h : msgFreshWin enc f r = true) :
    encFreshWin enc inLen f r = true ∨ encCollision enc r = true := by
  unfold msgFreshWin at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  have hFresh : r.1.1 ∉ r.2 := of_decide_eq_true h1
  by_cases hx : enc r.1.1 ∈ r.2.map enc
  · obtain ⟨m, hm, he⟩ := List.mem_map.mp hx
    refine .inr (List.any_eq_true.mpr ⟨m, hm, Bool.and_eq_true_iff.mpr ⟨?_, decide_eq_true he⟩⟩)
    exact decide_eq_true (fun hEq => hFresh (hEq ▸ hm))
  · refine .inl ?_
    unfold encFreshWin freshPointOk
    rw [decide_eq_true hx, decide_eq_true (hLen r.1.1), h2]
    rfl

/-! ## 4. The reduction to the PRF experiment -/

theorem play_bind {E : Iface} {A B σ : Type} (oracle : σ → (q : E.Query) → E.Resp q × σ) :
    ∀ (c : Code E A) (g : A → Code E B) (st : σ),
      Code.play oracle (Code.bind c g) st =
        Code.play oracle (g (Code.play oracle c st).1) (Code.play oracle c st).2
  | .ret a, g, st => by rw [Code.ret_bind, Code.play_ret]
  | .call qr k, g, st => by
    rw [Code.call_bind, Code.play_call, Code.play_call]
    exact play_bind oracle (k _) g _

/-- Translation of a tag-experiment adversary into a program over the byte oracle: queries are
    encoded and forwarded while fewer than `q` were answered, and answered `[]` afterwards
    without a call. The log of answered queries is returned with the output. -/
def relay {M R : Type} (enc : M → Bytes) (q : Nat) :
    Code (tagIface M) R → List M → Code byteOracleIface (R × List M)
  | .ret r, log => .ret (r, log)
  | .call m k, log =>
    if log.length < q then
      .call (E := byteOracleIface) (enc m) (fun resp => relay enc q (k resp) (log ++ [m]))
    else relay enc q (k []) log

theorem relay_ret {M R : Type} (enc : M → Bytes) (q : Nat) (r : R) (log : List M) :
    relay enc q (Code.ret (E := tagIface M) r) log = Code.ret (r, log) := by
  rfl

theorem relay_call {M R : Type} (enc : M → Bytes) (q : Nat) (m : M)
    (k : Bytes → Code (tagIface M) R) (log : List M) :
    relay enc q (Code.call (E := tagIface M) m k) log =
      if log.length < q then
        Code.call (E := byteOracleIface) (enc m) (fun resp => relay enc q (k resp) (log ++ [m]))
      else relay enc q (k []) log := by
  rfl

/-- The translated program makes at most `q - log.length` oracle calls on every path. -/
theorem relay_within {M R : Type} (enc : M → Bytes) (q : Nat) :
    ∀ (c : Code (tagIface M) R) (log : List M), Within (q - log.length) (relay enc q c log)
  | .ret r, log => .ret _ (r, log)
  | .call m k, log => by
    rw [relay_call]
    by_cases h : log.length < q
    · rw [ifPos h]
      have hEq : q - log.length = (q - (log ++ [m]).length) + 1 := by
        rw [List.length_append, List.length_singleton]
        omega
      rw [hEq]
      exact .call (E := byteOracleIface) _ _ (fun resp => relay_within enc q (k resp) (log ++ [m]))
    · rw [ifNeg h]
      exact relay_within enc q (k []) log

/-- Against the byte oracle of `f` with budget `Q ≥ q`, started with as many used queries as the
    log is long, the translated program computes the run of the tag experiment. -/
theorem relay_play {M R : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q Q : Nat) (hQ : q ≤ Q) :
    ∀ (c : Code (tagIface M) R) (log : List M),
      Code.play (budgetedFunOracle f Q) (relay enc q c log) log.length =
        (Code.play (tagOracle enc f q) c log, (Code.play (tagOracle enc f q) c log).2.length)
  | .ret r, log => by
    rw [relay_ret, Code.play_ret, Code.play_ret]
  | .call m k, log => by
    rw [relay_call, Code.play_call (tagOracle enc f q)]
    by_cases h : log.length < q
    · rw [ifPos h, Code.play_call, budgetedFunOracle.public_eqs, ifPos (Nat.lt_of_lt_of_le h hQ),
        tagOracle_pos enc f q h]
      have ih := relay_play enc f q Q hQ (k (f (enc m))) (log ++ [m])
      rw [List.length_append, List.length_singleton] at ih
      exact ih
    · rw [ifNeg h, tagOracle_neg enc f q h]
      exact relay_play enc f q Q hQ (k []) log

/-- The final check of the forgery distinguisher: on a fresh in-domain output it asks the oracle
    for the value at the output's encoding and compares it with the output tag. -/
def forgeCheck {M : Type} (enc : M → Bytes) (inLen : Nat) (r : (M × Bytes) × List M) :
    Code byteOracleIface Bool :=
  if freshPointOk enc inLen r then
    .call (E := byteOracleIface) (enc r.1.1) (fun t => .ret (decide (r.1.2 = t)))
  else .ret false

/-- **The PRF distinguisher of the forgery experiment**: run the adversary through `relay`, then
    `forgeCheck`. -/
def tagForgeDistinguisher {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) : Code byteOracleIface Bool :=
  Code.bind (relay enc q A []) (forgeCheck enc inLen)

/-- The PRF distinguisher of the view experiment: the adversary's own bit. -/
def tagViewDistinguisher {M : Type} (enc : M → Bytes) (q : Nat) (A : Code (tagIface M) Bool) :
    Code byteOracleIface Bool :=
  Code.bind (relay enc q A []) (fun r => .ret r.1)

/-- The forgery distinguisher makes at most `q + 1` oracle calls, whatever the adversary. -/
theorem tagForgeDistinguisher_within {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) : Within (q + 1) (tagForgeDistinguisher enc q inLen A) := by
  unfold tagForgeDistinguisher
  refine Within.bind (relay_within enc q A []) (fun r => ?_)
  unfold forgeCheck
  cases freshPointOk enc inLen r with
  | true => exact .call (E := byteOracleIface) _ _ (fun _ => .ret 0 _)
  | false => exact .ret 1 false

/-- The view distinguisher makes at most `q` oracle calls, whatever the adversary. -/
theorem tagViewDistinguisher_within {M : Type} (enc : M → Bytes) (q : Nat)
    (A : Code (tagIface M) Bool) : Within q (tagViewDistinguisher enc q A) := by
  unfold tagViewDistinguisher
  exact Within.bind (b₂ := 0) (relay_within enc q A []) (fun r => .ret 0 r.1)

/-- With oracle `f` and budget `q + 1`, the forgery distinguisher outputs the verdict of the
    fresh-input forgery experiment for `f`. -/
theorem tagForgeDistinguisher_play {M : Type} (enc : M → Bytes) (f : Bytes → Bytes)
    (q inLen : Nat) (A : Code (tagIface M) (M × Bytes)) :
    (Code.play (budgetedFunOracle f (q + 1)) (tagForgeDistinguisher enc q inLen A) 0).1 =
      encFreshWin enc inLen f (tagRun enc f q A) := by
  have hRelay := relay_play enc f q (q + 1) (Nat.le_succ q) A []
  have hLen := tagRun_log_length_le enc f q A
  unfold tagForgeDistinguisher
  rw [play_bind]
  have hRelay' : Code.play (budgetedFunOracle f (q + 1)) (relay enc q A []) 0 =
      (tagRun enc f q A, (tagRun enc f q A).2.length) := hRelay
  rw [hRelay']
  show (Code.play (budgetedFunOracle f (q + 1)) (forgeCheck enc inLen (tagRun enc f q A))
    (tagRun enc f q A).2.length).1 = encFreshWin enc inLen f (tagRun enc f q A)
  unfold forgeCheck encFreshWin
  cases freshPointOk enc inLen (tagRun enc f q A) with
  | false =>
    show (Code.play (budgetedFunOracle f (q + 1)) (Code.ret false)
      (tagRun enc f q A).2.length).1 = false
    rw [Code.play_ret]
  | true =>
    show (Code.play (budgetedFunOracle f (q + 1))
      (Code.call (E := byteOracleIface) (enc (tagRun enc f q A).1.1)
        (fun t => Code.ret (decide ((tagRun enc f q A).1.2 = t))))
      (tagRun enc f q A).2.length).1 = (true && decide ((tagRun enc f q A).1.2 =
        f (enc (tagRun enc f q A).1.1)))
    rw [Code.play_call, budgetedFunOracle.public_eqs, ifPos (Nat.lt_succ_of_le hLen),
      Code.play_ret]
    rfl

/-- With oracle `f` and budget `q`, the view distinguisher outputs the adversary's bit. -/
theorem tagViewDistinguisher_play {M : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    (A : Code (tagIface M) Bool) :
    (Code.play (budgetedFunOracle f q) (tagViewDistinguisher enc q A) 0).1 =
      (tagRun enc f q A).1 := by
  have hRelay : Code.play (budgetedFunOracle f q) (relay enc q A []) 0 =
      (tagRun enc f q A, (tagRun enc f q A).2.length) := relay_play enc f q q (Nat.le_refl q) A []
  unfold tagViewDistinguisher
  rw [play_bind, hRelay, Code.play_ret]

/-- **The forgery experiment under the PRF is within `ε` of the forgery experiment under a
    random function.** The left game keys `prf` with the sampled key; the right game uses the
    sampled function and does not read the key. -/
theorem tagForge_prf_hop {n nC nA : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes)
    (q inLen : Nat) (prf : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (adv : Fin nA → Code (tagIface M) (M × Bytes))
    (hD : ∀ a : Fin nA, 𝒜 (tagForgeDistinguisher enc q inLen (adv a))) :
    GameBound
      (AdvDist
        (encFreshTagGame hPos enc q inLen (fun ω => prf (sample (π.chal ω)).1)
          (fun ω => adv (π.advc ω)))
        (encFreshTagGame hPos enc q inLen (fun ω => (sample (π.chal ω)).2)
          (fun ω => adv (π.advc ω)))) ε := by
  have hReal : encFreshTagGame hPos enc q inLen (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω)) =
      prfRealGame hPos prf (q + 1) (fun ω => (sample (π.chal ω)).1)
        (fun ω => tagForgeDistinguisher enc q inLen (adv (π.advc ω))) :=
    FinGame.ext_win (fun ω => by
      rw [prfRealGame.public_eqs]
      exact (tagForgeDistinguisher_play enc (prf (sample (π.chal ω)).1) q inLen
        (adv (π.advc ω))).symm)
  have hIdeal : encFreshTagGame hPos enc q inLen (fun ω => (sample (π.chal ω)).2)
        (fun ω => adv (π.advc ω)) =
      prfIdealGame hPos (q + 1) (fun ω => (sample (π.chal ω)).2)
        (fun ω => tagForgeDistinguisher enc q inLen (adv (π.advc ω))) :=
    FinGame.ext_win (fun ω => by
      rw [prfIdealGame.public_eqs]
      exact (tagForgeDistinguisher_play enc (sample (π.chal ω)).2 q inLen
        (adv (π.advc ω))).symm)
  rw [hReal, hIdeal]
  exact hPrf n nC nA hPos π sample hU
    (fun a => tagForgeDistinguisher enc q inLen (adv a)) hD

/-- **Tags hide the key.** Any bit computed by an adaptive adversary from `q` tags under the
    sampled key has, up to `ε`, the distribution of the same bit computed from the sampled
    random function, in which the key does not occur. -/
theorem prfTag_view_key_hiding {n nC nA : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes)
    (q : Nat) (prf : Bytes → Bytes → Bytes) (keyLen inLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen q ε)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (adv : Fin nA → Code (tagIface M) Bool)
    (hD : ∀ a : Fin nA, 𝒜 (tagViewDistinguisher enc q (adv a))) :
    GameBound
      (AdvDist
        (tagViewGame hPos enc q (fun ω => prf (sample (π.chal ω)).1) (fun ω => adv (π.advc ω)))
        (tagViewGame hPos enc q (fun ω => (sample (π.chal ω)).2) (fun ω => adv (π.advc ω))))
      ε := by
  have hReal : tagViewGame hPos enc q (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω)) =
      prfRealGame hPos prf q (fun ω => (sample (π.chal ω)).1)
        (fun ω => tagViewDistinguisher enc q (adv (π.advc ω))) :=
    FinGame.ext_win (fun ω => by
      rw [prfRealGame.public_eqs]
      exact (tagViewDistinguisher_play enc (prf (sample (π.chal ω)).1) q (adv (π.advc ω))).symm)
  have hIdeal : tagViewGame hPos enc q (fun ω => (sample (π.chal ω)).2)
        (fun ω => adv (π.advc ω)) =
      prfIdealGame hPos q (fun ω => (sample (π.chal ω)).2)
        (fun ω => tagViewDistinguisher enc q (adv (π.advc ω))) :=
    FinGame.ext_win (fun ω => by
      rw [prfIdealGame.public_eqs]
      exact (tagViewDistinguisher_play enc (sample (π.chal ω)).2 q (adv (π.advc ω))).symm)
  rw [hReal, hIdeal]
  exact hPrf n nC nA hPos π sample hU (fun a => tagViewDistinguisher enc q (adv a)) hD

/-! ## 5. Forgery against a uniformly sampled function: an exact count -/

/-- Bytewise XOR, truncated to the shorter argument. -/
@[expose] def xorBytes (a b : Bytes) : Bytes :=
  List.zipWith (fun x y => x ^^^ y) a b

theorem xorBytes_length : ∀ (a b : Bytes), a.length = b.length → (xorBytes a b).length = a.length
  | [], _, _ => by rfl
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | _ :: a, _ :: b, h => congrArg Nat.succ (xorBytes_length a b (Nat.succ.inj h))

theorem xorBytes_cancel : ∀ (a p : Bytes), a.length = p.length → xorBytes (xorBytes a p) p = a
  | [], [], _ => by rfl
  | [], _ :: _, h => absurd h.symm (Nat.succ_ne_zero _)
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)
  | x :: a, y :: p, h => by
    show ((x ^^^ y) ^^^ y) :: xorBytes (xorBytes a p) p = x :: a
    rw [u8_xor_cancel_right, xorBytes_cancel a p (Nat.succ.inj h)]

theorem xorBytes_right_inj :
    ∀ (a p p' : Bytes), a.length = p.length → a.length = p'.length →
      xorBytes a p = xorBytes a p' → p = p'
  | [], [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _, _ => absurd h.symm (Nat.succ_ne_zero _)
  | [], [], _ :: _, _, h, _ => absurd h.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, h, _, _ => absurd h (Nat.succ_ne_zero _)
  | _ :: _, _ :: _, [], _, h, _ => absurd h (Nat.succ_ne_zero _)
  | x :: a, y :: p, y' :: p', h, h', hx => by
    have hx' : (x ^^^ y) :: xorBytes a p = (x ^^^ y') :: xorBytes a p' := hx
    obtain ⟨h1, h2⟩ := List.cons.inj hx'
    have hy : y = y' :=
      calc y = x ^^^ (x ^^^ y) := (u8_xor_cancel_left x y).symm
        _ = x ^^^ (x ^^^ y') := by rw [h1]
        _ = y' := u8_xor_cancel_left x y'
    rw [hy, xorBytes_right_inj a p p' (Nat.succ.inj h) (Nat.succ.inj h') h2]

/-- `f` with its value at `x` XOR-shifted by `pad`. -/
@[expose] def shiftAt (x pad : Bytes) (f : Bytes → Bytes) : Bytes → Bytes :=
  fun y => if y = x then xorBytes (f y) pad else f y

theorem shiftAt_self (x pad : Bytes) (f : Bytes → Bytes) :
    shiftAt x pad f x = xorBytes (f x) pad :=
  ifPos rfl _ _

theorem shiftAt_ne (x pad : Bytes) (f : Bytes → Bytes) {y : Bytes} (h : y ≠ x) :
    shiftAt x pad f y = f y :=
  ifNeg h _ _

/-- The sample set of keyed-function experiments is closed under resampling one in-domain value:
    members map `inLen`-byte inputs to `outLen`-byte outputs, and shifting the value at one
    `inLen`-byte input by an `outLen`-byte pad gives a member with the same key. -/
@[expose] def SupportShiftClosed (inLen outLen : Nat)
    (support : Bytes × (Bytes → Bytes) → Prop) : Prop :=
  (∀ (k : Bytes) (f : Bytes → Bytes), support (k, f) →
    ∀ x : Bytes, x.length = inLen → (f x).length = outLen) ∧
  (∀ (k : Bytes) (f : Bytes → Bytes), support (k, f) →
    ∀ x pad : Bytes, x.length = inLen → pad.length = outLen → support (k, shiftAt x pad f))

/-- The full PRF sample space admits every length-preserving shift at an in-domain input. -/
theorem prfSampleOk_shiftClosed (keyLen inLen outLen : Nat) :
    SupportShiftClosed inLen outLen (PrfSampleOk keyLen inLen outLen) := by
  constructor
  · intro k f h x hx
    exact ((prfSampleOk_iff _ _ _ _).mp h).2 x |>.1 hx
  · intro k f h x pad hx hp
    obtain ⟨hk, hf⟩ := (prfSampleOk_iff _ _ _ _).mp h
    refine (prfSampleOk_iff _ _ _ _).mpr ⟨hk, fun y => ?_⟩
    dsimp only [Prod.snd]
    by_cases hxy : y = x
    · subst y
      have hl := (hf x).1 hx
      rw [shiftAt_self]
      exact ⟨fun _ => (xorBytes_length _ _ (hl.trans hp.symm)).trans hl, fun hn => (hn hx).elim⟩
    · rw [shiftAt_ne _ _ _ hxy]
      exact hf y

theorem pow256_pos : ∀ k : Nat, 0 < 256 ^ k
  | 0 => Nat.one_pos
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow256_pos k) (by decide)

/-- The probability `256 ^ (-outLen)` of guessing one uniform `outLen`-byte value. -/
@[expose] def tagGuessBound (outLen : Nat) : Spec.RatBound :=
  ⟨1, 256 ^ outLen, pow256_pos outLen⟩

private theorem tagPlay_log_mono {M R : Type} (enc : M → Bytes) (f : Bytes → Bytes) (q : Nat)
    (c : Code (tagIface M) R) (log : List M) (m : M) (hm : m ∈ log) :
    m ∈ (Code.play (tagOracle enc f q) c log).2 :=
  Code.play_invariant (tagOracle enc f q) (fun st => m ∈ st)
    (fun st qr h => by
      by_cases hc : st.length < q
      · rw [tagOracle_pos enc f q hc]
        exact List.mem_append_left _ h
      · rw [tagOracle_neg enc f q hc]
        exact h)
    c log hm

/-- A run reads the keyed function only at the encodings of the answered queries. -/
private theorem tagPlay_congr {M R : Type} (enc : M → Bytes) (f g : Bytes → Bytes) (q : Nat) :
    ∀ (c : Code (tagIface M) R) (log : List M),
      (∀ m ∈ (Code.play (tagOracle enc f q) c log).2, f (enc m) = g (enc m)) →
      Code.play (tagOracle enc g q) c log = Code.play (tagOracle enc f q) c log
  | .ret r, log, _ => by rw [Code.play_ret, Code.play_ret]
  | .call m k, log, h => by
    rw [Code.play_call] at h
    rw [Code.play_call, Code.play_call (tagOracle enc f q)]
    by_cases hc : log.length < q
    · rw [tagOracle_pos enc f q hc] at h
      rw [tagOracle_pos enc f q hc, tagOracle_pos enc g q hc]
      have hm : f (enc m) = g (enc m) :=
        h m (tagPlay_log_mono enc f q _ _ m
          (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
      rw [← hm]
      exact tagPlay_congr enc f g q (k (f (enc m))) (log ++ [m]) h
    · rw [tagOracle_neg enc f q hc] at h
      rw [tagOracle_neg enc f q hc, tagOracle_neg enc g q hc]
      exact tagPlay_congr enc f g q (k []) log h

private theorem freshPointOk_spec {M : Type} (enc : M → Bytes) (inLen : Nat)
    (r : (M × Bytes) × List M) (h : freshPointOk enc inLen r = true) :
    enc r.1.1 ∉ r.2.map enc ∧ (enc r.1.1).length = inLen := by
  unfold freshPointOk at h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- Shifting the value at a fresh output point does not change the run. -/
private theorem shift_run_eq {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes)
    (hC : freshPointOk enc inLen (tagRun enc f q A) = true) :
    tagRun enc (shiftAt (enc (tagRun enc f q A).1.1) pad f) q A = tagRun enc f q A := by
  have hFresh := (freshPointOk_spec enc inLen _ hC).1
  unfold tagRun at hFresh ⊢
  exact tagPlay_congr enc f _ q A [] (fun m hm =>
    (shiftAt_ne _ pad f (fun he => hFresh (List.mem_map.mpr ⟨m, hm, he⟩))).symm)

/-- The shift used by the count: at a run with a fresh in-domain output point, XOR `pad` into the
    value there; otherwise leave the function alone. -/
private def forgeShift {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes) : Bytes → Bytes :=
  if freshPointOk enc inLen (tagRun enc f q A) then
    shiftAt (enc (tagRun enc f q A).1.1) pad f
  else f

private def idealWin {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (f : Bytes → Bytes) : Bool :=
  encFreshWin enc inLen f (tagRun enc f q A)

private theorem forgeShift_false {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes)
    (hC : freshPointOk enc inLen (tagRun enc f q A) = false) :
    forgeShift enc q inLen A pad f = f := by
  unfold forgeShift
  rw [hC]
  rfl

private theorem forgeShift_true {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes)
    (hC : freshPointOk enc inLen (tagRun enc f q A) = true) :
    forgeShift enc q inLen A pad f = shiftAt (enc (tagRun enc f q A).1.1) pad f := by
  unfold forgeShift
  rw [hC]
  rfl

private theorem forgeShift_invol {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes)
    (hLen : freshPointOk enc inLen (tagRun enc f q A) = true →
      (f (enc (tagRun enc f q A).1.1)).length = pad.length) :
    forgeShift enc q inLen A pad (forgeShift enc q inLen A pad f) = f := by
  cases hC : freshPointOk enc inLen (tagRun enc f q A) with
  | false =>
    have h1 := forgeShift_false enc q inLen A pad f hC
    rw [h1, h1]
  | true =>
    have hRun := shift_run_eq enc q inLen A pad f hC
    have hC' : freshPointOk enc inLen
        (tagRun enc (shiftAt (enc (tagRun enc f q A).1.1) pad f) q A) = true := by
      rw [hRun]; exact hC
    rw [forgeShift_true enc q inLen A pad f hC, forgeShift_true enc q inLen A pad _ hC', hRun]
    funext y
    by_cases hy : y = enc (tagRun enc f q A).1.1
    · rw [hy, shiftAt_self, shiftAt_self]
      exact xorBytes_cancel _ _ (hLen hC)
    · rw [shiftAt_ne _ _ _ hy, shiftAt_ne _ _ _ hy]

/-- If the shifted function is forged against, the unshifted run has a fresh in-domain output
    point and its output tag is the shifted value there. -/
private theorem shift_win {M : Type} (enc : M → Bytes) (q inLen : Nat)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (f : Bytes → Bytes)
    (hW : idealWin enc q inLen A (forgeShift enc q inLen A pad f) = true) :
    freshPointOk enc inLen (tagRun enc f q A) = true ∧
      (tagRun enc f q A).1.2 = xorBytes (f (enc (tagRun enc f q A).1.1)) pad := by
  cases hC : freshPointOk enc inLen (tagRun enc f q A) with
  | false =>
    rw [forgeShift_false enc q inLen A pad f hC] at hW
    unfold idealWin encFreshWin at hW
    rw [hC] at hW
    exact absurd hW Bool.false_ne_true
  | true =>
    rw [forgeShift_true enc q inLen A pad f hC] at hW
    unfold idealWin encFreshWin at hW
    rw [shift_run_eq enc q inLen A pad f hC] at hW
    have h3 := of_decide_eq_true (Bool.and_eq_true_iff.mp hW).2
    rw [shiftAt_self] at h3
    exact ⟨rfl, h3⟩

private theorem forgeShift_support {M : Type} (enc : M → Bytes) (q inLen outLen : Nat)
    {support : Bytes × (Bytes → Bytes) → Prop} (hClosed : SupportShiftClosed inLen outLen support)
    (A : Code (tagIface M) (M × Bytes)) (pad : Bytes) (hPad : pad.length = outLen)
    (k : Bytes) (f : Bytes → Bytes) (hS : support (k, f)) :
    support (k, forgeShift enc q inLen A pad f) := by
  cases hC : freshPointOk enc inLen (tagRun enc f q A) with
  | false => rw [forgeShift_false enc q inLen A pad f hC]; exact hS
  | true =>
    rw [forgeShift_true enc q inLen A pad f hC]
    exact hClosed.2 k f hS _ pad (freshPointOk_spec enc inLen _ hC).2 hPad

/-- The `outLen`-byte pad with index `p`. -/
private def padOf (outLen : Nat) (p : Fin (256 ^ outLen)) : Bytes :=
  encodeNatLeBytes outLen p.val

private theorem padOf_injective (outLen : Nat) (p p' : Fin (256 ^ outLen))
    (h : padOf outLen p = padOf outLen p') : p = p' := by
  apply Fin.ext
  have h1 := decodeNatLeBytes_encodeNatLeBytes outLen p.val p.2
  have h2 := decodeNatLeBytes_encodeNatLeBytes outLen p'.val p'.2
  unfold padOf at h
  rw [h] at h1
  exact h1.symm.trans h2

/-- For one adversary program: among the coins of a uniform sampler on a shift-closed set, the
    forging ones are at most a `256 ^ (-outLen)` fraction. -/
private theorem idealWin_count {nC : Nat} {M : Type} (enc : M → Bytes) (q inLen outLen : Nat)
    {support : Bytes × (Bytes → Bytes) → Prop} (hClosed : SupportShiftClosed inLen outLen support)
    (sample : Fin nC → Bytes × (Bytes → Bytes)) (hU : UniformOn support sample)
    (A : Code (tagIface M) (M × Bytes)) :
    sampleSum nC (fun c => if idealWin enc q inLen A (sample c).2 then 1 else 0) * 256 ^ outLen ≤
      nC := by
  refine shift_count (fun c => idealWin enc q inLen A (sample c).2)
    (fun p c => idealWin enc q inLen A (forgeShift enc q inLen A (padOf outLen p) (sample c).2))
    (fun p => ?_) (fun c p p' hp hp' => ?_)
  · have hPadLen : (padOf outLen p).length = outLen := encodeNatLeBytes_length outLen p.val
    obtain ⟨s, hs⟩ := fin_choice nC
      (fun c c' => sample c' =
        ((sample c).1, forgeShift enc q inLen A (padOf outLen p) (sample c).2))
      (fun c => hU.surjective _
        (forgeShift_support enc q inLen outLen hClosed A _ hPadLen _ _ (hU.mem c)))
    refine ⟨s, fun c => hU.injective _ _ ?_, fun c => by rw [hs c]⟩
    have hInv := forgeShift_invol enc q inLen A (padOf outLen p) (sample c).2 (fun hC =>
      (hClosed.1 _ _ (hU.mem c) _ (freshPointOk_spec enc inLen _ hC).2).trans hPadLen.symm)
    rw [hs (s c), hs c]
    show ((sample c).1, forgeShift enc q inLen A (padOf outLen p)
      (forgeShift enc q inLen A (padOf outLen p) (sample c).2)) = sample c
    rw [hInv]
  · obtain ⟨hC, h1⟩ := shift_win enc q inLen A (padOf outLen p) (sample c).2 hp
    obtain ⟨_, h2⟩ := shift_win enc q inLen A (padOf outLen p') (sample c).2 hp'
    have hLen := hClosed.1 _ _ (hU.mem c) _ (freshPointOk_spec enc inLen _ hC).2
    exact padOf_injective outLen p p'
      (xorBytes_right_inj _ _ _
        (hLen.trans (encodeNatLeBytes_length outLen p.val).symm)
        (hLen.trans (encodeNatLeBytes_length outLen p'.val).symm) (h1.symm.trans h2))

/-- **Forgery against a uniformly sampled function has probability at most `256 ^ (-outLen)`.**
    The function is the second component of a sample that is uniform on a set closed under
    resampling one in-domain value (`SupportShiftClosed`); the adversary is randomized, adaptive
    and unbounded, and the challenger answers `q` queries. The count pairs every forging coin
    with the `256 ^ outLen` coins whose function differs from it by an XOR pad at the forged
    input: the adversary's run is the same on all of them, and at most one carries the tag it
    outputs. -/
theorem encFreshTagGame_random_function_bound {n nC nA : Nat} (hPos : 0 < n) {M : Type}
    (enc : M → Bytes) (q inLen outLen : Nat)
    {support : Bytes × (Bytes → Bytes) → Prop} (hClosed : SupportShiftClosed inLen outLen support)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn support sample)
    (adv : Fin nA → Code (tagIface M) (M × Bytes)) :
    GameBound
      (encFreshTagGame hPos enc q inLen (fun ω => (sample (π.chal ω)).2)
        (fun ω => adv (π.advc ω))).winProb
      (tagGuessBound outLen) := by
  show (encFreshTagGame hPos enc q inLen (fun ω => (sample (π.chal ω)).2)
    (fun ω => adv (π.advc ω))).winCount * 256 ^ outLen ≤ 1 * n
  rw [Nat.one_mul, FinGame.winCount_eq]
  let π' : CoinSplit n nA nC :=
    { chal := π.advc
      advc := π.chal
      pair := fun a c => π.pair c a
      chal_pair := fun a c => π.advc_pair c a
      advc_pair := fun a c => π.chal_pair c a
      pair_eta := π.pair_eta }
  rw [CoinSplit.sampleSum_eq π']
  have hRe : ∀ a : Fin nA,
      sampleSum nC (fun c => if (encFreshTagGame hPos enc q inLen
        (fun ω => (sample (π.chal ω)).2) (fun ω => adv (π.advc ω))).win (π'.pair a c)
        then 1 else 0) =
      sampleSum nC (fun c => if idealWin enc q inLen (adv a) (sample c).2 then 1 else 0) :=
    fun a => ssum_congr (fun c => by
      show (if encFreshWin enc inLen (sample (π.chal (π.pair c a))).2
        (tagRun enc (sample (π.chal (π.pair c a))).2 q (adv (π.advc (π.pair c a)))) = true
        then 1 else 0) = _
      rw [π.chal_pair, π.advc_pair]
      rfl)
  rw [ssum_congr hRe, ← ssum_mul_right]
  have h1 := ssum_le nA _ _
    (fun a => idealWin_count enc q inLen outLen hClosed sample hU (adv a))
  rw [ssum_const] at h1
  rw [CoinSplit.card_eq π, Nat.mul_comm nC nA]
  exact h1

/-! ## 6. Forgery bounds under `Spec.PrfHard` -/

/-- **A PRF is an unforgeable tag.** Under `Spec.PrfHard` with `q + 1` queries, an adaptive
    adversary that sees `q` tags under a uniform key outputs a correct tag on a fresh `inLen`-byte
    input with probability at most `ε + 256 ^ (-outLen)`. The reduction is
    `tagForgeDistinguisher`; `hD` places it in the class the hardness is assumed for. -/
theorem prfTag_forgery_bound {n nC nA : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes)
    (q inLen : Nat) (prf : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (adv : Fin nA → Code (tagIface M) (M × Bytes))
    (hD : ∀ a : Fin nA, 𝒜 (tagForgeDistinguisher enc q inLen (adv a))) :
    GameBound
      (encFreshTagGame hPos enc q inLen (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω))).winProb
      (ε.add (tagGuessBound outLen)) :=
  GameBound.trans
    (winProb_le_advDist_add _
      (encFreshTagGame hPos enc q inLen (fun ω => (sample (π.chal ω)).2)
        (fun ω => adv (π.advc ω))))
    (Spec.RatBound.add_le_add
      (tagForge_prf_hop hPos enc q inLen prf keyLen outLen hPrf π sample hU adv hD)
      (encFreshTagGame_random_function_bound hPos enc q inLen outLen (prfSampleOk_shiftClosed keyLen inLen outLen) π sample hU adv))

/-- **Existential unforgeability under adaptive chosen-message attack**, for messages encoded to
    the input length of the PRF. A forgery on a message that was not queried has probability at
    most `ε + 256 ^ (-outLen)` plus the probability that the run exhibits two different messages
    with one encoding. -/
theorem eufCmaTag_forgery_bound {n nC nA : Nat} (hPos : 0 < n) {M : Type} [DecidableEq M]
    (enc : M → Bytes) (q inLen : Nat) (hLen : ∀ m : M, (enc m).length = inLen)
    (prf : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (adv : Fin nA → Code (tagIface M) (M × Bytes))
    (hD : ∀ a : Fin nA, 𝒜 (tagForgeDistinguisher enc q inLen (adv a))) :
    GameBound
      (eufCmaTagGame hPos enc q (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω))).winProb
      ((ε.add (tagGuessBound outLen)).add
        (encCollisionGame hPos enc q (fun ω => prf (sample (π.chal ω)).1)
          (fun ω => adv (π.advc ω))).winProb) :=
  GameBound.trans
    (event_le_two_reductions _
      (encFreshTagGame hPos enc q inLen (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω)))
      (encCollisionGame hPos enc q (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω)))
      (fun _ h => msgFreshWin_encFresh_or_collision enc inLen hLen _ _ h))
    (Spec.RatBound.add_le_add
      (prfTag_forgery_bound hPos enc q inLen prf keyLen outLen hPrf π sample hU adv hD)
      (Spec.RatBound.le_refl _))

/-- In the permit experiment the challenger's answer to an admitted query is `prfCustodyTag`. -/
theorem tagOracle_answers_prfCustodyTag (prf : Bytes → Bytes → Bytes) (dg : Bytes → Bytes)
    (key : Bytes) (q : Nat) {log : List CustodyApproval} (h : log.length < q)
    (permit : CustodyApproval) :
    (tagOracle (permitInput dg) (prf key) q log permit).1 = prfCustodyTag prf dg key permit := by
  rw [tagOracle_pos _ _ _ h, prfCustodyTag_eq]

/-- A collision of permit inputs between two different permits is a collision of the digest. -/
theorem permitCollision_yields_digest_collision (dg : Bytes → Bytes)
    (r : (CustodyApproval × Bytes) × List CustodyApproval)
    (h : encCollision (permitInput dg) r = true) : Nonempty (HashCollision dg) := by
  unfold encCollision at h
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp h
  obtain ⟨hNe, hEq⟩ := Bool.and_eq_true_iff.mp hm
  exact ⟨⟨encodePermit m, encodePermit r.1.1,
    fun hEnc => (of_decide_eq_true hNe) (encodePermit_injective hEnc), of_decide_eq_true hEq⟩⟩

/-- **`prfCustodyTag` is unforgeable after `q` adaptive honest tags.** The adversary asks for the
    tags of `q` permits of its choice under a uniform custodian key and outputs a permit it did
    not ask for together with a tag. With a digest `dg` to `inLen` bytes, the output tag is
    `prfCustodyTag prf dg key` of that permit with probability at most `ε + 256 ^ (-outLen)` plus
    the probability that two different permits of the run have one digest. -/
theorem prfCustodyTag_unforgeable {n nC nA : Nat} (hPos : 0 < n)
    (dg : Bytes → Bytes) (q inLen : Nat) (hLen : ∀ x : Bytes, (dg x).length = inLen)
    (prf : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε)
    (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (adv : Fin nA → Code (tagIface CustodyApproval) (CustodyApproval × Bytes))
    (hD : ∀ a : Fin nA, 𝒜 (tagForgeDistinguisher (permitInput dg) q inLen (adv a))) :
    GameBound
      (eufCmaTagGame hPos (permitInput dg) q (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω))).winProb
      ((ε.add (tagGuessBound outLen)).add
        (encCollisionGame hPos (permitInput dg) q (fun ω => prf (sample (π.chal ω)).1)
          (fun ω => adv (π.advc ω))).winProb) ∧
    (∀ ω : Fin n,
      (eufCmaTagGame hPos (permitInput dg) q (fun ω => prf (sample (π.chal ω)).1)
        (fun ω => adv (π.advc ω))).win ω = true →
      (tagRun (permitInput dg) (prf (sample (π.chal ω)).1) q (adv (π.advc ω))).1.1 ∉
        (tagRun (permitInput dg) (prf (sample (π.chal ω)).1) q (adv (π.advc ω))).2 ∧
      (tagRun (permitInput dg) (prf (sample (π.chal ω)).1) q (adv (π.advc ω))).1.2 =
        prfCustodyTag prf dg (sample (π.chal ω)).1
          (tagRun (permitInput dg) (prf (sample (π.chal ω)).1) q (adv (π.advc ω))).1.1) := by
  refine ⟨eufCmaTag_forgery_bound hPos (permitInput dg) q inLen
    (fun m => hLen (encodePermit m)) prf keyLen outLen hPrf π sample hU adv hD, ?_⟩
  intro ω hWin
  obtain ⟨h1, h2⟩ := eufCmaTagGame_win_sound hPos (permitInput dg) q _ _ ω hWin
  exact ⟨h1, h2.trans (prfCustodyTag_eq prf dg _ _).symm⟩

/-- **Union over `k` custodian keys.** `G₀` is any event of the coin space such that each of its
    coins is a fresh-input forgery under the key of one of `k` custodians; custodian `p`'s key is
    the challenger coordinate of its own split `π p`, and its forger `adv p` reads the other
    coordinate. Under `Spec.PrfHard`, `G₀` has probability at most
    `k * (ε + 256 ^ (-outLen))`. -/
theorem custodianKeys_forgery_union_bound {n k : Nat} (hPos : 0 < n) {M : Type}
    (enc : M → Bytes) (q inLen : Nat) (prf : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    {𝒜 : Code byteOracleIface Bool → Prop} {ε : Spec.RatBound}
    (hPrf : PrfHard 𝒜 prf keyLen inLen outLen (q + 1) ε)
    (nC nA : Fin k → Nat) (π : (p : Fin k) → CoinSplit n (nC p) (nA p))
    (sample : (p : Fin k) → Fin (nC p) → Bytes × (Bytes → Bytes))
    (hU : ∀ p : Fin k, UniformOn (PrfSampleOk keyLen inLen outLen) (sample p))
    (adv : (p : Fin k) → Fin (nA p) → Code (tagIface M) (M × Bytes))
    (hD : ∀ (p : Fin k) (a : Fin (nA p)), 𝒜 (tagForgeDistinguisher enc q inLen (adv p a)))
    (G₀ : FinGame n)
    (hExtract : ∀ ω : Fin n, G₀.win ω = true → ∃ p : Fin k,
      (encFreshTagGame hPos enc q inLen (fun ω => prf (sample p ((π p).chal ω)).1)
        (fun ω => adv p ((π p).advc ω))).win ω = true) :
    GameBound G₀.winProb ((ε.add (tagGuessBound outLen)).scale k) :=
  event_le_family_reductions G₀
    (fun p => encFreshTagGame hPos enc q inLen (fun ω => prf (sample p ((π p).chal ω)).1)
      (fun ω => adv p ((π p).advc ω)))
    hExtract
    (fun p => prfTag_forgery_bound hPos enc q inLen prf keyLen outLen hPrf (π p)
      (sample p) (hU p) (adv p) (hD p))

/-! ## 7. Negative results -/

/-- The toy tag of a MAC-style layer whose certificate carries the key: the tag is the key. -/
def toyCustodyTag (key : Bytes) : Bytes → Bytes :=
  fun _ => key

/-- One honest tag on `m₀`, then the same tag on `m₁`. -/
def toyKeyRecoveryAdv {M : Type} (m₀ m₁ : M) : Code (tagIface M) (M × Bytes) :=
  .call (E := tagIface M) m₀ (fun t => .ret (m₁, t))

/-- The key-recovery adversary forges against the toy tag on every coin. -/
theorem toyKeyRecoveryAdv_wins {n : Nat} (hPos : 0 < n) {M : Type} (enc : M → Bytes)
    (key : Fin n → Bytes) (m₀ m₁ : M) (hNe : enc m₀ ≠ enc m₁) {q : Nat} (hq : 0 < q)
    (ω : Fin n) :
    (encFreshTagGame hPos enc q (enc m₁).length (fun ω => toyCustodyTag (key ω))
      (fun _ => toyKeyRecoveryAdv m₀ m₁)).win ω = true := by
  have hRun : tagRun enc (toyCustodyTag (key ω)) q (toyKeyRecoveryAdv m₀ m₁) =
      ((m₁, key ω), [m₀]) := by
    unfold tagRun toyKeyRecoveryAdv
    have h0 : ([] : List M).length < q := hq
    rw [Code.play_call, tagOracle_pos enc _ q h0, Code.play_ret]
    rfl
  have hWin : encFreshWin enc (enc m₁).length (toyCustodyTag (key ω))
      (tagRun enc (toyCustodyTag (key ω)) q (toyKeyRecoveryAdv m₀ m₁)) = true := by
    rw [hRun]
    have h1 : enc m₁ ∉ [m₀].map enc := fun h => hNe (List.mem_singleton.mp h).symm
    have h3 : key ω = toyCustodyTag (key ω) (enc m₁) := by rfl
    show (decide (enc m₁ ∉ [m₀].map enc) && decide ((enc m₁).length = (enc m₁).length) &&
      decide (key ω = toyCustodyTag (key ω) (enc m₁))) = true
    rw [decide_eq_true h1, decide_eq_true (rfl : (enc m₁).length = (enc m₁).length),
      decide_eq_true h3]
    rfl
  have hGame : (encFreshTagGame hPos enc q (enc m₁).length (fun ω => toyCustodyTag (key ω))
      (fun _ => toyKeyRecoveryAdv m₀ m₁)).win ω = true := hWin
  exact hGame

/-- **A tag that reveals the key is forged after one honest tag.** In the experiment in which
    `prfTag_forgery_bound` holds for a PRF, the toy tag is forged with probability one by an
    adversary that makes a single query: no bound below `1` holds for it. -/
theorem tooth_toyCustodyTag_one_query_forgery {n : Nat} (hPos : 0 < n) {M : Type}
    (enc : M → Bytes) (key : Fin n → Bytes) (m₀ m₁ : M) (hNe : enc m₀ ≠ enc m₁)
    {q : Nat} (hq : 0 < q) {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound
      (encFreshTagGame hPos enc q (enc m₁).length (fun ω => toyCustodyTag (key ω))
        (fun _ => toyKeyRecoveryAdv m₀ m₁)).winProb ε :=
  FinGame.not_bound_of_forall_win _
    (fun ω => toyKeyRecoveryAdv_wins hPos enc key m₀ m₁ hNe hq ω) hε

/-- The same for approval permits under `encodePermit`: after one honest toy tag on a permit, a
    different permit is certified with probability one. -/
theorem tooth_toyPermitTag_one_query_forgery {n : Nat} (hPos : 0 < n) (key : Fin n → Bytes)
    (p₀ p₁ : CustodyApproval) (hNe : p₀ ≠ p₁) {q : Nat} (hq : 0 < q)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound
      (encFreshTagGame hPos encodePermit q (encodePermit p₁).length
        (fun ω => toyCustodyTag (key ω)) (fun _ => toyKeyRecoveryAdv p₀ p₁)).winProb ε :=
  tooth_toyCustodyTag_one_query_forgery hPos encodePermit key p₀ p₁
    (fun h => hNe (encodePermit_injective h)) hq hε

/-- **The closure hypothesis of the count is necessary.** A sampler that is uniform on a
    one-element set (`Spec.uniformOn_unique`) fixes the function; an adversary that outputs the
    value of that function without any query forges on every coin, so the bound
    `256 ^ (-(outLen + 1))` of `encFreshTagGame_random_function_bound` fails. -/
theorem tooth_singleFunction_support_forged {M : Type} (enc : M → Bytes) (m : M)
    (f₀ : Bytes → Bytes) (q outLen : Nat) :
    ¬ GameBound
      (encFreshTagGame Nat.one_pos enc q (enc m).length (fun _ : Fin 1 => f₀)
        (fun _ => Code.ret (m, f₀ (enc m)))).winProb
      (tagGuessBound (outLen + 1)) := by
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) ?_
  · have hRun : tagRun enc f₀ q (Code.ret (E := tagIface M) (m, f₀ (enc m))) =
        ((m, f₀ (enc m)), []) := by
      unfold tagRun
      rw [Code.play_ret]
    show encFreshWin enc (enc m).length f₀
      (tagRun enc f₀ q (Code.ret (E := tagIface M) (m, f₀ (enc m)))) = true
    rw [hRun]
    have h1 : enc m ∉ ([] : List M).map enc := fun h => nomatch h
    show (decide (enc m ∉ ([] : List M).map enc) && decide ((enc m).length = (enc m).length) &&
      decide (f₀ (enc m) = f₀ (enc m))) = true
    rw [decide_eq_true h1, decide_eq_true (rfl : (enc m).length = (enc m).length),
      decide_eq_true (rfl : f₀ (enc m) = f₀ (enc m))]
    rfl
  · show 1 < 256 ^ (outLen + 1)
    rw [Nat.pow_succ]
    have := pow256_pos outLen
    omega

/-! ## 8. A non-degenerate instance of the count -/

/-- The keyed-function sample set with empty key, the single input `[]` and one-byte values. -/
def oneByteSupport (x : Bytes × (Bytes → Bytes)) : Prop :=
  x.1 = [] ∧ (x.2 []).length = 1 ∧ ∀ y : Bytes, y ≠ [] → x.2 y = []

/-- Its sampler: coin `i` gives the function with value `[i]` at `[]`. -/
def oneByteSample (i : Fin 256) : Bytes × (Bytes → Bytes) :=
  ([], fun y => if y = [] then [UInt8.ofNat i.val] else [])

theorem oneByteSample_uniform : UniformOn oneByteSupport oneByteSample where
  mem i := ⟨rfl, by
    show (if ([] : Bytes) = [] then [UInt8.ofNat i.val] else []).length = 1
    rw [ifPos rfl]
    rfl, fun y hy => ifNeg hy _ _⟩
  injective c c' h := by
    have h1 : (oneByteSample c).2 [] = (oneByteSample c').2 [] := by rw [h]
    have h2 : [UInt8.ofNat c.val] = [UInt8.ofNat c'.val] := by
      have e1 : (oneByteSample c).2 [] = [UInt8.ofNat c.val] := by
        show (if ([] : Bytes) = [] then [UInt8.ofNat c.val] else []) = [UInt8.ofNat c.val]
        rw [ifPos rfl]
      have e2 : (oneByteSample c').2 [] = [UInt8.ofNat c'.val] := by
        show (if ([] : Bytes) = [] then [UInt8.ofNat c'.val] else []) = [UInt8.ofNat c'.val]
        rw [ifPos rfl]
      rw [← e1, ← e2]
      exact h1
    have h3 := congrArg UInt8.toNat (List.cons.inj h2).1
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat', Nat.mod_eq_of_lt c.2, Nat.mod_eq_of_lt c'.2] at h3
    exact Fin.ext h3
  surjective x hx := by
    obtain ⟨k, f⟩ := x
    obtain ⟨hk, hLen, hOff⟩ := hx
    have hk' : k = [] := hk
    have hLen' : (f []).length = 1 := hLen
    have hOff' : ∀ y : Bytes, y ≠ [] → f y = [] := hOff
    cases hv : f [] with
    | nil => rw [hv] at hLen'; exact absurd hLen' (by decide)
    | cons b rest =>
      rw [hv] at hLen'
      have hRest : rest = [] := List.length_eq_zero_iff.mp (Nat.succ.inj hLen')
      refine ⟨⟨b.toNat, b.toBitVec.isLt⟩, ?_⟩
      rw [hk']
      show (([] : Bytes), fun y => if y = [] then [UInt8.ofNat b.toNat] else []) = ([], f)
      have hf : (fun y : Bytes => if y = [] then [UInt8.ofNat b.toNat] else []) = f := by
        funext y
        by_cases hy : y = []
        · rw [ifPos hy, hy, hv, hRest, UInt8.ofNat_toNat]
        · rw [ifNeg hy, hOff' y hy]
      rw [hf]

theorem oneByteSupport_shiftClosed : SupportShiftClosed 0 1 oneByteSupport := by
  refine ⟨fun k f hS x hx => ?_, fun k f hS x pad hx hPad => ?_⟩
  · rw [List.length_eq_zero_iff.mp hx]
    exact hS.2.1
  · have hx' : x = [] := List.length_eq_zero_iff.mp hx
    obtain ⟨hk, hLen, hOff⟩ := hS
    have hLen' : (f []).length = 1 := hLen
    refine ⟨hk, ?_, fun y hy => ?_⟩
    · show (shiftAt x pad f []).length = 1
      rw [hx', shiftAt_self, xorBytes_length _ _ (hLen'.trans hPad.symm)]
      exact hLen'
    · show shiftAt x pad f y = []
      rw [hx', shiftAt_ne _ _ _ hy]
      exact hOff y hy

/-- **The count on a 256-element sample set.** Against a uniform one-byte value, every adaptive
    adversary with any query budget forges on a fresh input with probability at most `1 / 256`:
    `encFreshTagGame_random_function_bound` at a sampler and a closure proof constructed here. -/
theorem witness_oneByte_random_function_bound {n nA : Nat} (hPos : 0 < n) {M : Type}
    (enc : M → Bytes) (q : Nat) (π : CoinSplit n 256 nA)
    (adv : Fin nA → Code (tagIface M) (M × Bytes)) :
    GameBound
      (encFreshTagGame hPos enc q 0 (fun ω => (oneByteSample (π.chal ω)).2)
        (fun ω => adv (π.advc ω))).winProb
      (tagGuessBound 1) :=
  encFreshTagGame_random_function_bound hPos enc q 0 1 oneByteSupport_shiftClosed π
    oneByteSample oneByteSample_uniform adv

#verify_constructive
  Qsag.KeyHidingCustody.event_le_family_reductions
  Qsag.KeyHidingCustody.refinesOfEq_rel
  Qsag.KeyHidingCustody.refinesOfEq_absInit
  Qsag.KeyHidingCustody.refinesOfEq_runStep
  Qsag.KeyHidingCustody.encodePermit_injective
  Qsag.KeyHidingCustody.prfCustodyTag_eq
  Qsag.KeyHidingCustody.tagOracle_pos
  Qsag.KeyHidingCustody.tagOracle_neg
  Qsag.KeyHidingCustody.tagRun_log_length_le
  Qsag.KeyHidingCustody.eufCmaTagGame_win_sound
  Qsag.KeyHidingCustody.msgFreshWin_encFresh_or_collision
  Qsag.KeyHidingCustody.play_bind
  Qsag.KeyHidingCustody.relay_ret
  Qsag.KeyHidingCustody.relay_call
  Qsag.KeyHidingCustody.relay_within
  Qsag.KeyHidingCustody.relay_play
  Qsag.KeyHidingCustody.tagForgeDistinguisher_within
  Qsag.KeyHidingCustody.tagViewDistinguisher_within
  Qsag.KeyHidingCustody.tagForgeDistinguisher_play
  Qsag.KeyHidingCustody.tagViewDistinguisher_play
  Qsag.KeyHidingCustody.tagForge_prf_hop
  Qsag.KeyHidingCustody.prfTag_view_key_hiding
  Qsag.KeyHidingCustody.xorBytes_length
  Qsag.KeyHidingCustody.xorBytes_cancel
  Qsag.KeyHidingCustody.xorBytes_right_inj
  Qsag.KeyHidingCustody.shiftAt_self
  Qsag.KeyHidingCustody.shiftAt_ne
  Qsag.KeyHidingCustody.pow256_pos
  Qsag.KeyHidingCustody.encFreshTagGame_random_function_bound
  Qsag.KeyHidingCustody.prfTag_forgery_bound
  Qsag.KeyHidingCustody.eufCmaTag_forgery_bound
  Qsag.KeyHidingCustody.tagOracle_answers_prfCustodyTag
  Qsag.KeyHidingCustody.permitCollision_yields_digest_collision
  Qsag.KeyHidingCustody.prfCustodyTag_unforgeable
  Qsag.KeyHidingCustody.custodianKeys_forgery_union_bound
  Qsag.KeyHidingCustody.toyKeyRecoveryAdv_wins
  Qsag.KeyHidingCustody.tooth_toyCustodyTag_one_query_forgery
  Qsag.KeyHidingCustody.tooth_toyPermitTag_one_query_forgery
  Qsag.KeyHidingCustody.tooth_singleFunction_support_forged
  Qsag.KeyHidingCustody.oneByteSample_uniform
  Qsag.KeyHidingCustody.oneByteSupport_shiftClosed
  Qsag.KeyHidingCustody.witness_oneByte_random_function_bound

#tooth_pair Qsag.KeyHidingCustody.prfTag_forgery_bound vs
  Qsag.KeyHidingCustody.tooth_toyCustodyTag_one_query_forgery
#tooth_pair Qsag.KeyHidingCustody.prfCustodyTag_unforgeable vs
  Qsag.KeyHidingCustody.tooth_toyPermitTag_one_query_forgery
#tooth_pair Qsag.KeyHidingCustody.encFreshTagGame_random_function_bound vs
  Qsag.KeyHidingCustody.tooth_singleFunction_support_forged

/-! Kernel-checked defining equations of the tag experiments, for importers that build new
    adversaries against them (`Qsag.Top.CertCustodyAdaptiveBound`). No body is exposed. -/
#export_eqns tagRun encFreshWin msgFreshWin encCollision encFreshTagGame eufCmaTagGame
  encCollisionGame permitInput prfCustodyTag

/-- Projection lemma for `freshPointOk` (its compiler equation mentions a private proof term). -/
theorem freshPointOk_eq_true_iff {M : Type} (enc : M → Bytes) (inLen : Nat)
    (r : (M × Bytes) × List M) :
    freshPointOk enc inLen r = true ↔
      enc r.1.1 ∉ r.2.map enc ∧ (enc r.1.1).length = inLen := by
  unfold freshPointOk
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

#verify_constructive Qsag.KeyHidingCustody.freshPointOk_eq_true_iff

end Qsag.KeyHidingCustody
end
