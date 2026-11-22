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
