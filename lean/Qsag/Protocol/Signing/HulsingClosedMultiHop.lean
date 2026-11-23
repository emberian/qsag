module

public import Qsag.Protocol.Signing.HulsingMultiHopReduction
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-- The stateless signing experiment admits queries in arbitrary epoch order. -/
abbrev ExecStatelessEufCmaGame {n qHash qSign : Nat} :=
  @execEufCmaGameWith n qHash qSign false

private theorem pair_ext {a b : Nat} (sp : Spec.CoinSplit (a * b) a b) {i j : Fin (a * b)}
    (hc : sp.chal i = sp.chal j) (ha : sp.advc i = sp.advc j) : i = j := by
  calc
    i = sp.pair (sp.chal i) (sp.advc i) := (sp.pair_eta i).symm
    _ = sp.pair (sp.chal j) (sp.advc j) := by rw [hc, ha]
    _ = j := sp.pair_eta j

/-- Cardinality of a tape of independent fixed-width byte strings. -/
def powItsr (width : Nat) : Nat → Nat
  | 0 => 1
  | q + 1 => pow256 width * powItsr width q

/-- The ITSR tape has one fixed-width randomizer per oracle call. -/
def itsrVecSampler (width : Nat) : (q : Nat) → Fin (powItsr width q) → List Spec.Bytes
  | 0, _ => []
  | q + 1, z =>
    let sp := Spec.CoinSplit.prod (pow256 width) (powItsr width q)
    byteVecSampler width (sp.chal z) :: itsrVecSampler width q (sp.advc z)

theorem uniformOn_itsrVecSampler (width : Nat) : ∀ q,
    Spec.UniformOn (Spec.ItsrSampleOk width q) (itsrVecSampler width q)
  | 0 => {
    mem := fun _ => (Spec.ItsrSampleOk_eq ..).mpr ⟨rfl, fun _ h => nomatch h⟩
    injective := fun i j _ => Fin.ext ((Nat.lt_one_iff.mp i.isLt).trans (Nat.lt_one_iff.mp j.isLt).symm)
    surjective := fun xs h => ⟨⟨0, Nat.one_pos⟩, (List.eq_nil_of_length_eq_zero
      ((Spec.ItsrSampleOk_eq ..).mp h).1).symm⟩ }
  | q + 1 => by
    let sp := Spec.CoinSplit.prod (pow256 width) (powItsr width q)
    have ht := uniformOn_itsrVecSampler width q
    have hb := uniformOn_byteVecSampler width
    constructor
    · intro z
      have h := (Spec.ItsrSampleOk_eq ..).mp (ht.mem (sp.advc z))
      apply (Spec.ItsrSampleOk_eq ..).mpr
      exact ⟨congrArg Nat.succ h.1, List.forall_mem_cons.mpr ⟨hb.mem _, h.2⟩⟩
    · intro i j eq
      have ⟨e, f⟩ := List.cons.inj eq
      exact pair_ext sp (hb.injective _ _ e) (ht.injective _ _ f)
    · intro xs h
      obtain ⟨len, mem⟩ := (Spec.ItsrSampleOk_eq ..).mp h
      cases xs with
      | nil => cases len
      | cons x xs =>
        obtain ⟨hx, hxs⟩ := List.forall_mem_cons.mp mem
        obtain ⟨i, ei⟩ := hb.surjective x hx
        obtain ⟨j, ej⟩ := ht.surjective xs ((Spec.ItsrSampleOk_eq ..).mpr ⟨Nat.succ.inj len, hxs⟩)
        refine ⟨sp.pair i j, ?_⟩
        change byteVecSampler width (sp.chal _) :: itsrVecSampler width q (sp.advc _) = _
        rw [sp.chal_pair, sp.advc_pair, ei, ej]

@[expose] def samplePair {n m : Nat} {α β : Type} (s : Fin n → α) (v : Fin m → β)
    (z : Fin (n * m)) : α × β :=
  let sp := Spec.CoinSplit.prod n m
  (s (sp.chal z), v (sp.advc z))

theorem uniformOn_samplePair {n m : Nat} {α β : Type} {s : Fin n → α} {v : Fin m → β}
    {S : α → Prop} {V : β → Prop} (hs : Spec.UniformOn S s) (hv : Spec.UniformOn V v) :
    Spec.UniformOn (fun x => S x.1 ∧ V x.2) (samplePair s v) := by
  let sp := Spec.CoinSplit.prod n m
  constructor
  · intro z
    exact ⟨hs.mem _, hv.mem _⟩
  · intro i j e
    exact pair_ext sp (hs.injective _ _ (congrArg Prod.fst e)) (hv.injective _ _ (congrArg Prod.snd e))
  · intro (x, y) ⟨hx, hy⟩
    obtain ⟨i, hi⟩ := hs.surjective x hx
    obtain ⟨j, hj⟩ := hv.surjective y hy
    refine ⟨sp.pair i j, ?_⟩
    change (s (sp.chal _), v (sp.advc _)) = _
    rw [sp.chal_pair, sp.advc_pair, hi, hj]

private def singleHidden (z : Fin (pow256 32)) : List Spec.Bytes := [byteVecSampler 32 z]

private theorem uniform_singleHidden : Spec.UniformOn (Spec.ItsrSampleOk 32 1) singleHidden where
  mem z := (Spec.ItsrSampleOk_eq ..).mpr ⟨rfl, List.forall_mem_singleton.mpr (byteVecSampler_length ..)⟩
  injective i j e := (uniformOn_byteVecSampler 32).injective _ _ (List.cons.inj e).1
  surjective xs h := by
    obtain ⟨hl, hm⟩ := (Spec.ItsrSampleOk_eq ..).mp h
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨i, hi⟩ := (uniformOn_byteVecSampler 32).surjective x (hm x (.head _))
    exact ⟨i, congrArg (fun b => [b]) hi⟩

def mkPreSampler {n : Nat} (seedS : Fin n → Spec.Bytes) :=
  samplePair seedS singleHidden

theorem uniformOn_mkPreSampler {n seedLen : Nat} {seedS : Fin n → Spec.Bytes}
    (hs : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS) :
    Spec.UniformOn (Spec.SmDtPreSampleOk seedLen 32 1) (mkPreSampler seedS) := by
  have h := uniformOn_samplePair hs uniform_singleHidden
  have he : Spec.SmDtPreSampleOk seedLen 32 1 =
      (fun x => x.1.length = seedLen ∧ Spec.ItsrSampleOk 32 1 x.2) := by
    funext x
    rw [Spec.SmDtPreSampleOk_eq, Spec.ItsrSampleOk_eq]
  rwa [he]

def mkUdSampler {n : Nat} (seedS : Fin n → Spec.Bytes) :=
  samplePair seedS (samplePair singleHidden singleHidden)

theorem uniformOn_mkUdSampler {n seedLen : Nat} {seedS : Fin n → Spec.Bytes}
    (hs : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS) :
    Spec.UniformOn (SmDtUdSampleOk seedLen 32 32 1) (mkUdSampler seedS) := by
  have hv := uniformOn_samplePair uniform_singleHidden uniform_singleHidden
  have he : SmDtUdSampleOk seedLen 32 32 1 = (fun x => x.1.length = seedLen ∧
      Spec.ItsrSampleOk 32 1 x.2.1 ∧ Spec.ItsrSampleOk 32 1 x.2.2) := by
    funext x
    rw [SmDtUdSampleOk.public_eqs, Spec.ItsrSampleOk_eq, Spec.ItsrSampleOk_eq]
  rw [he]
  exact uniformOn_samplePair hs hv

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

/-- Exchange the random-function output at one input with an independent output coin. -/
def exchangePrfEntry (x : Spec.Bytes)
    (z : (Spec.Bytes × (Spec.Bytes → Spec.Bytes)) × Spec.Bytes) :=
  ((z.1.1, fun y => if y = x then z.2 else z.1.2 y), z.1.2 x)

private theorem exchangePrfEntry_invol (x : Spec.Bytes)
    (z : (Spec.Bytes × (Spec.Bytes → Spec.Bytes)) × Spec.Bytes) :
    exchangePrfEntry x (exchangePrfEntry x z) = z := by
  obtain ⟨⟨k, f⟩, b⟩ := z
  unfold exchangePrfEntry
  simp only [↓reduceIte, Prod.mk.injEq, true_and, and_true]
  funext y
  by_cases h : y = x <;> simp only [h, ↓reduceIte]

private theorem exchangePrfEntry_mem {keyLen inLen outLen : Nat} {x : Spec.Bytes}
    (hx : x.length = inLen) {z : (Spec.Bytes × (Spec.Bytes → Spec.Bytes)) × Spec.Bytes}
    (hz : Spec.PrfSampleOk keyLen inLen outLen z.1 ∧ z.2.length = outLen) :
    Spec.PrfSampleOk keyLen inLen outLen (exchangePrfEntry x z).1 ∧
      (exchangePrfEntry x z).2.length = outLen := by
  obtain ⟨hk, hf⟩ := (Spec.PrfSampleOk_eq ..).mp hz.1
  refine ⟨(Spec.PrfSampleOk_eq ..).mpr ⟨hk, fun y => ?_⟩, (hf x).1 hx⟩
  by_cases hy : y = x
  · subst y
    exact ⟨fun _ => by simpa only [exchangePrfEntry, ↓reduceIte] using hz.2,
      fun hn => (hn hx).elim⟩
  · simpa only [exchangePrfEntry, hy, ↓reduceIte] using hf y

/-- Every joint observation of the table and the spare coin has the same count after
    exchanging them at a fixed, in-domain input. The rest of the table is available
    to the observation. The key and all other table entries retain their values. -/
theorem prf_entry_exchange_sum {n keyLen inLen outLen : Nat}
    {sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)}
    (hSample : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen outLen) sample)
    (x : Spec.Bytes) (hx : x.length = inLen)
    (w : (Spec.Bytes × (Spec.Bytes → Spec.Bytes)) × Spec.Bytes → Nat) :
    let draw := samplePair sample (byteVecSampler outLen)
    Spec.sampleSum (n * pow256 outLen) (fun i => w (exchangePrfEntry x (draw i))) =
      Spec.sampleSum (n * pow256 outLen) (fun i => w (draw i)) := by
  intro draw
  have hu := uniformOn_samplePair hSample (uniformOn_byteVecSampler outLen)
  obtain ⟨f, hf⟩ := fin_choice (n * pow256 outLen)
    (fun i j => draw j = exchangePrfEntry x (draw i))
    (fun i => hu.surjective _ (exchangePrfEntry_mem hx (hu.mem i)))
  have hInv : ∀ i, f (f i) = i := fun i => hu.injective _ _ (by
    change draw (f (f i)) = draw i
    rw [hf, hf, exchangePrfEntry_invol])
  let sp : Spec.CoinSplit (n * pow256 outLen) (n * pow256 outLen) 1 :=
    { chal := f, advc := fun _ => 0, pair := fun j _ => f j
      chal_pair := fun i _ => hInv i
      advc_pair := fun _ j => Fin.ext (Nat.lt_one_iff.mp j.isLt).symm
      pair_eta := hInv }
  have h := sp.sampleSum_eq (fun i => w (draw i))
  rw [h]
  apply congrArg (Spec.sampleSum _)
  funext i
  rw [Spec.sampleSum_succ, Spec.sampleSum_zero, Nat.add_zero]
  exact congrArg w (hf i).symm

/-- Mask the challenged entry before giving a table to a simulator. -/
def puncturePrf (x : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (y : Spec.Bytes) :=
  if y = x then [] else f y

private theorem samplePair_sum {n m : Nat} {α β : Type} (s : Fin n → α) (v : Fin m → β)
    (w : α × β → Nat) :
    Spec.sampleSum (n * m) (fun i => w (samplePair s v i)) =
    Spec.sampleSum n (fun i => Spec.sampleSum m (fun j => w (s i, v j))) := by
  let sp := Spec.CoinSplit.prod n m
  rw [sp.sampleSum_eq]
  apply Spec.sampleSum_ext
  intro i
  apply Spec.sampleSum_ext
  intro j
  change w (s (sp.chal (sp.pair i j)), v (sp.advc (sp.pair i j))) = _
  rw [sp.chal_pair, sp.advc_pair]

/-- Conditional on the full punctured table, the deleted entry is an independent
    fixed-width draw. Both sides are exact counts with the same normalization. -/
theorem puncturedPrf_draw_sum {n keyLen inLen outLen : Nat}
    {sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)}
    (hSample : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen outLen) sample)
    (x : Spec.Bytes) (hx : x.length = inLen)
    (w : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Nat) :
    Spec.sampleSum n (fun c => w (puncturePrf x (sample c).2) ((sample c).2 x)) * pow256 outLen =
      Spec.sampleSum (pow256 outLen) (fun b => Spec.sampleSum n (fun c =>
        w (puncturePrf x (sample c).2) (byteVecSampler outLen b))) := by
  let obs := fun (z : (Spec.Bytes × (Spec.Bytes → Spec.Bytes)) × Spec.Bytes) =>
    w (puncturePrf x z.1.2) (z.1.2 x)
  have swap := prf_entry_exchange_sum hSample x hx obs
  change Spec.sampleSum _ (fun i => (fun z => obs (exchangePrfEntry x z))
    (samplePair sample (byteVecSampler outLen) i)) = _ at swap
  rw [samplePair_sum sample (byteVecSampler outLen) (fun z => obs (exchangePrfEntry x z)),
    samplePair_sum sample (byteVecSampler outLen) obs] at swap
  have erase (f : Spec.Bytes → Spec.Bytes) (b : Spec.Bytes) :
      puncturePrf x (fun y => if y = x then b else f y) = puncturePrf x f := by
    funext y
    by_cases h : y = x <;> simp only [puncturePrf, h, ↓reduceIte]
  simp only [obs, exchangePrfEntry, erase, ↓reduceIte, Spec.sampleSum_const] at swap
  rw [← Spec.sampleSum_mul_right]
  calc
    _ = Spec.sampleSum n (fun c => pow256 outLen *
        w (puncturePrf x (sample c).2) ((sample c).2 x)) :=
      Spec.sampleSum_ext fun _ => Nat.mul_comm _ _
    _ = _ := swap.symm.trans (Spec.sampleSum_comm ..)

/-- Evaluate an adaptive program against a fixed random-function table. -/
def evalPrfTable {R : Type} (f : Spec.Bytes → Spec.Bytes) : Spec.Code Spec.byteOracleIface R → R
  | .ret r => r
  | .call x k => evalPrfTable f (k (f x))

private abbrev PrfCache := Spec.Bytes → Option Spec.Bytes

private def remember (cache : PrfCache) (x b : Spec.Bytes) : PrfCache :=
  fun y => if y = x then some b else cache y

private def cachedTable (cache : PrfCache) (f : Spec.Bytes → Spec.Bytes) :=
  fun x => (cache x).getD (f x)

/-- A fresh valid input consumes the next tape entry. A repeated input receives
    its recorded answer. Out-of-domain inputs receive the empty byte string. -/
def evalMemoPrf {R : Type} (inLen : Nat) (cache : Spec.Bytes → Option Spec.Bytes)
    (tape : List Spec.Bytes) : Spec.Code Spec.byteOracleIface R → R
  | .ret r => r
  | .call x k =>
    match cache x with
    | some b => evalMemoPrf inLen cache tape (k b)
    | none =>
      if x.length = inLen then
        let b := tape.headD []
        evalMemoPrf inLen (remember cache x b) tape.tail (k b)
      else evalMemoPrf inLen cache tape (k [])

private theorem tape_cons_sum (width q : Nat) (w : List Spec.Bytes → Nat) :
    Spec.sampleSum (powItsr width (q + 1)) (fun z => w (itsrVecSampler width (q + 1) z)) =
      Spec.sampleSum (pow256 width) (fun b => Spec.sampleSum (powItsr width q) (fun t =>
        w (byteVecSampler width b :: itsrVecSampler width q t))) :=
  samplePair_sum (byteVecSampler width) (itsrVecSampler width q) (fun p => w (p.1 :: p.2))

private theorem sampleSum_bool_le_one_of_subsingleton {m : Nat} (p : Fin m → Bool)
    (hSub : ∀ i j : Fin m, p i = true → p j = true → i = j) :
    Spec.sampleSum m (fun i => if p i then 1 else 0) ≤ 1 := by
  suffices ∀ (k : Nat) (q : Fin k → Bool),
      (∀ i j : Fin k, q i = true → q j = true → i = j) →
      Spec.sampleSum k (fun i => if q i then 1 else 0) ≤ 1 from this m p hSub
  intro k
  induction k with
  | zero => intro _ _; exact Nat.zero_le 1
  | succ k ih =>
    intro q hq
    rw [Spec.sampleSum_succ]
    cases h0 : q ⟨0, Nat.zero_lt_succ k⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih (fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) (fun i j hi hj =>
        Fin.ext (Nat.succ.inj (congrArg Fin.val (hq _ _ hi hj))))
    · simp only [↓reduceIte]
      have hRest : Spec.sampleSum k (fun i => if q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) = 0 := by
        have hZ : (fun i : Fin k => if q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) =
            (fun _ => 0) := by
          funext i
          cases hi : q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
          · rfl
          · exact False.elim (Nat.succ_ne_zero i.1 (congrArg Fin.val (hq _ _ hi h0)))
        rw [hZ, Spec.sampleSum_const, Nat.mul_zero]
      rw [hRest]
      exact Nat.le_refl 1

#verify_constructive sampleSum_bool_le_one_of_subsingleton

/-- Once one coordinate is erased, even a prediction depending on every remaining
    tape entry matches that coordinate with probability at most one over its alphabet. -/
theorem itsr_erased_coordinate_count (width : Nat) : ∀ (q i : Nat), i < q →
    ∀ predict : List Spec.Bytes → Spec.Bytes,
      Spec.sampleSum (powItsr width q) (fun z =>
        let tape := itsrVecSampler width q z
        if tape.getD i [] = predict (tape.set i []) then 1 else 0) * pow256 width ≤ powItsr width q
  | 0, i, hi, _ => (Nat.not_lt_zero i hi).elim
  | q+1, 0, _, predict => by
    let T := powItsr width q
    let B := pow256 width
    let hit := fun (b : Fin B) (z : Fin T) =>
      if byteVecSampler width b = predict ([] :: itsrVecSampler width q z) then 1 else 0
    have one (z : Fin T) : Spec.sampleSum B (fun b => hit b z) ≤ 1 := by
      let ok := fun b => decide (byteVecSampler width b = predict ([] :: itsrVecSampler width q z))
      have h := sampleSum_bool_le_one_of_subsingleton ok (fun i j hi hj =>
        (uniformOn_byteVecSampler width).injective _ _ ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm))
      simpa only [ok, hit, decide_eq_true_eq] using h
    rw [tape_cons_sum width q (fun tape => if tape.getD 0 [] = predict (tape.set 0 []) then 1 else 0)]
    change Spec.sampleSum B (fun b => Spec.sampleSum T (hit b)) * B ≤ B * T
    rw [Spec.sampleSum_comm B T hit, Nat.mul_comm B T]
    apply Nat.mul_le_mul_right
    have h := Spec.sampleSum_le T _ (fun _ => 1) one
    simpa only [Spec.sampleSum_const, Nat.mul_one] using h
  | q+1, i+1, hi, predict => by
    let T := powItsr width q
    let B := pow256 width
    let hit := fun (b : Fin B) (z : Fin T) =>
      let tape := itsrVecSampler width q z
      if tape.getD i [] = predict (byteVecSampler width b :: tape.set i []) then 1 else 0
    have ih (b : Fin B) : Spec.sampleSum T (hit b) * B ≤ T :=
      itsr_erased_coordinate_count width q i (Nat.lt_of_succ_lt_succ hi)
        (fun tape => predict (byteVecSampler width b :: tape))
    rw [tape_cons_sum width q (fun tape => if tape.getD (i+1) [] = predict (tape.set (i+1) []) then 1 else 0)]
    change Spec.sampleSum B (fun b => Spec.sampleSum T (hit b)) * B ≤ B * T
    rw [← Spec.sampleSum_mul_right]
    simpa only [Spec.sampleSum_const] using Spec.sampleSum_le B _ (fun _ => T) ih

private theorem cachedTable_fill (cache : PrfCache) (x : Spec.Bytes) (hx : cache x = none)
    (f : Spec.Bytes → Spec.Bytes) :
    cachedTable (remember cache x (f x)) (puncturePrf x f) = cachedTable cache f := by
  funext y
  by_cases he : y = x
  · subst y
    simp only [cachedTable, remember, ↓reduceIte, hx, Option.getD]
  · simp only [cachedTable, remember, he, ↓reduceIte, puncturePrf]

private theorem cachedTable_puncture (cache : PrfCache) (x b : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) :
    cachedTable (remember cache x b) (puncturePrf x f) = cachedTable (remember cache x b) f := by
  funext y
  by_cases he : y = x <;> simp only [cachedTable, remember, puncturePrf, he, ↓reduceIte, Option.getD]

private theorem evalMemoPrf_sum {R : Type} {n keyLen inLen width : Nat}
    {sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)}
    (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen width) sample)
    (w : R → Nat) (c : Spec.Code Spec.byteOracleIface R) :
    ∀ q, Spec.Within q c → ∀ cache : PrfCache,
    Spec.sampleSum n (fun j => w (evalPrfTable (cachedTable cache (sample j).2) c)) * powItsr width q =
    n * Spec.sampleSum (powItsr width q) (fun t => w (evalMemoPrf inLen cache (itsrVecSampler width q t) c)) := by
  induction c with
  | ret v =>
    intro q _ cache
    simp only [evalPrfTable, evalMemoPrf, Spec.sampleSum_const]
    exact (Nat.mul_right_comm n (w v) _).trans (Nat.mul_assoc _ _ _)
  | call x k ih =>
    intro _ hb cache
    cases hb with
    | @call q _ _ hk =>
      cases hit : cache x with
      | some b =>
        simpa only [evalPrfTable, evalMemoPrf, cachedTable, hit, Option.getD] using
          ih b (q + 1) (Spec.Within.mono (Nat.le_succ _) (hk b)) cache
      | none =>
        by_cases len : x.length = inLen
        · let B := pow256 width
          let T := powItsr width q
          let obs := fun f b => w (evalPrfTable (cachedTable (remember cache x b) f) (k b))
          have swap := puncturedPrf_draw_sum hu x len obs
          simp only [obs, cachedTable_fill _ _ hit, cachedTable_puncture] at swap
          let branch := fun b => Spec.sampleSum n (fun j =>
            obs (sample j).2 (byteVecSampler width b))
          let lazyBranch := fun b => Spec.sampleSum T (fun t =>
            w (evalMemoPrf inLen (remember cache x (byteVecSampler width b))
              (itsrVecSampler width q t) (k (byteVecSampler width b))))
          have ihb : ∀ b, branch b * T = n * lazyBranch b := fun b =>
            ih _ q (hk _) (remember cache x (byteVecSampler width b))
          rw [tape_cons_sum width q (fun tape => w (evalMemoPrf inLen cache tape (.call x k)))]
          simp only [evalMemoPrf, evalPrfTable, hit, len, ↓reduceIte, List.headD_cons, List.tail_cons]
          change Spec.sampleSum n (fun j =>
            w (evalPrfTable (cachedTable cache (sample j).2) (k ((cache x).getD ((sample j).2 x))))) *
            (B * T) = n * Spec.sampleSum B lazyBranch
          rw [hit, ← Nat.mul_assoc]
          change Spec.sampleSum n (fun j =>
            w (evalPrfTable (cachedTable cache (sample j).2) (k ((sample j).2 x)))) * B * T = _
          rw [swap]
          change Spec.sampleSum B branch * T = _
          rw [← Spec.sampleSum_mul_right]
          calc
            _ = Spec.sampleSum B (fun b => lazyBranch b * n) :=
              Spec.sampleSum_ext fun b => (ihb b).trans (Nat.mul_comm _ _)
            _ = _ := (Spec.sampleSum_mul_right ..).trans (Nat.mul_comm _ _)
        · have invalid : ∀ j, (sample j).2 x = [] := fun j =>
            (((Spec.PrfSampleOk_eq ..).mp (hu.mem j)).2 x).2 len
          simpa only [evalPrfTable, evalMemoPrf, cachedTable, hit, Option.getD, invalid, len, ↓reduceIte] using
            ih [] (q + 1) (Spec.Within.mono (Nat.le_succ _) (hk [])) cache

/-- Exact adaptive lazy sampling for the PRF challenger, including repeated and
    malformed inputs. The continuation can retain the whole query transcript. -/
theorem prf_table_eq_memoized_tape {R : Type} {n keyLen inLen width q : Nat}
    {sample : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)}
    (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen inLen width) sample)
    (c : Spec.Code Spec.byteOracleIface R) (hb : Spec.Within q c) (w : R → Nat) :
    Spec.sampleSum n (fun j => w (evalPrfTable (sample j).2 c)) * powItsr width q =
    n * Spec.sampleSum (powItsr width q) (fun t =>
      w (evalMemoPrf inLen (fun _ => none) (itsrVecSampler width q t) c)) :=
  evalMemoPrf_sum hu w c q hb (fun _ => none)

/-- PRF_msg input derived by the ideal-secret signer. -/
def signingPrfInput (suite : TweakableHashSuite) (pk : PqPublicKey) (q : ProdSigningQuery) :=
  encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)

theorem signingPrfInput_prehash_eq (suite : TweakableHashSuite) (pk : PqPublicKey)
    (q₁ q₂ : ProdSigningQuery) (eq : signingPrfInput suite pk q₁ = signingPrfInput suite pk q₂) :
    thPreHash suite pk.pkSeed pk.pkRoot q₁.message = thPreHash suite pk.pkSeed pk.pkRoot q₂.message := by
  have len (m : Spec.Bytes) : (thPreHash suite pk.pkSeed pk.pkRoot m).length = 32 := by
    rw [thPreHash_eq]
    exact thCall_length ..
  simp only [signingPrfInput, encodePrfMsg65.public_eqs, padBytes32_of_len32 (len _)] at eq
  exact (List.append_inj (List.cons.inj eq).2
    ((padBytes32_length _).trans (padBytes32_length _).symm)).2

private def prehashWitness (suite : TweakableHashSuite) (pk : PqPublicKey) (m₁ m₂ : Spec.Bytes)
    (hne : m₁ ≠ m₂) (he : thPreHash suite pk.pkSeed pk.pkRoot m₁ = thPreHash suite pk.pkSeed pk.pkRoot m₂) :
    ExplicitTcrWitness suite pk.pkSeed := by
  refine ⟨⟨encodeMultiRoleTweak tagHPre zeroAdrs, encodeMultiFrame [pk.pkRoot, m₂],
      encodeMultiFrame [pk.pkRoot, m₁]⟩, ?_, ?_⟩
  · intro hh
    exact hne (List.cons.inj (List.cons.inj (encodeMultiFrame_injective hh)).2).1
  · rw [suiteTweakHash_multiRole, suiteTweakHash_multiRole]
    simpa only [thPreHash_eq, thCall_eq] using he

/-- Reusing a PRF_msg input for distinct messages supplies a concrete prehash collision. -/
def reusedSigningInputTcr (suite : TweakableHashSuite) (pk : PqPublicKey)
    (q₁ q₂ : ProdSigningQuery) (hne : q₁.message ≠ q₂.message)
    (eq : signingPrfInput suite pk q₁ = signingPrfInput suite pk q₂) :
    ExplicitTcrWitness suite pk.pkSeed :=
  prehashWitness suite pk q₁.message q₂.message hne (signingPrfInput_prehash_eq suite pk q₁ q₂ eq)

private theorem idealSigner_at_prfInput (suite : TweakableHashSuite) (params : PqHashParams)
    (seed : Spec.Bytes) (f sec : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery) :
    let ov := secOverlaySuite suite seed sec
    let pk := derivePublicKeyIdealPrf suite params seed sec
    signQueryIdealPrf suite params seed (fun _ => f (signingPrfInput ov pk q)) sec q =
      signQueryIdealPrf suite params seed f sec q := by
  simp only [signQueryIdealPrf.public_eqs, signQueryWithRandFn.public_eqs,
    derivePublicKeyIdealPrf.public_eqs, signingPrfInput]

/-- Compile the signing tree to queries at its actual 65-byte PRF inputs.
    The result retains successful signatures in chronological order. Failed requests
    determine the continuation with the same none response as the executable signer. -/
def signingTranscriptCode (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes) {R : Type} :
    ProdAdaptiveTree R → Nat → List (Spec.Bytes × PqHashSig) →
      Spec.Code Spec.byteOracleIface (R × List (Spec.Bytes × PqHashSig))
  | .pure r, _, log => .ret (r, log)
  | .hashQuery x k, lo, log => signingTranscriptCode latchOn suite params seed sec (k (suite.rawHash x)) lo log
  | .signQuery q k, lo, log =>
    if latchOn = false ∨ lo ≤ q.epoch then
      let pk := derivePublicKeyIdealPrf suite params seed sec
      .call (signingPrfInput (secOverlaySuite suite seed sec) pk q) fun b =>
        let sig := signQueryIdealPrf suite params seed (fun _ => b) sec q
        let entries := match sig with | none => [] | some s => [(q.message, s)]
        signingTranscriptCode latchOn suite params seed sec (k sig) (q.epoch + 1) (log ++ entries)
    else signingTranscriptCode latchOn suite params seed sec (k none) lo log

private theorem signingTranscriptCode_within {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes) :
    ∀ {qH qS} (t : ProdAdaptiveTree R) (lo : Nat) (log : List (Spec.Bytes × PqHashSig)),
      ProdDualBounded qH qS t → Spec.Within qS (signingTranscriptCode latchOn suite params seed sec t lo log)
  | _, qS, .pure _, _, _, _ => .ret qS _
  | 0, _, .hashQuery _ _, _, _, h => False.elim h
  | _ + 1, _, .hashQuery x k, lo, log, h =>
    signingTranscriptCode_within latchOn suite params seed sec (k (suite.rawHash x)) lo log (h _)
  | _, 0, .signQuery _ _, _, _, h => False.elim h
  | _, qS + 1, .signQuery q k, lo, log, h => by
    unfold signingTranscriptCode
    split
    · exact .call _ _ (fun _ => signingTranscriptCode_within latchOn suite params seed sec _ _ _ (h _))
    · exact Spec.Within.mono (Nat.le_succ qS)
        (signingTranscriptCode_within latchOn suite params seed sec _ _ _ (h none))

private theorem signingTranscriptCode_eval {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (seed : Spec.Bytes) (f sec : Spec.Bytes → Spec.Bytes)
    (t : ProdAdaptiveTree R) (lo : Nat) (log : List (Spec.Bytes × PqHashSig)) :
    let sign := signQueryIdealPrf suite params seed f sec
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash sign t lo
    evalPrfTable f (signingTranscriptCode latchOn suite params seed sec t lo log) =
      (run.1, log ++ signLogFromOracle sign run.2) := by
  induction t generalizing lo log with
  | pure r => simp only [signingTranscriptCode, evalPrfTable, evalLatchedAdaptiveTree.public_eq_1,
      signLogFromOracle.public_eqs, List.append_nil]
  | hashQuery x k ih => exact ih (suite.rawHash x) _ _
  | signQuery q k ih =>
    simp only [evalLatchedAdaptiveTree_sign, signingTranscriptCode]
    split
    · simp only [evalPrfTable, idealSigner_at_prfInput, signLogFromOracle_cons, ← List.append_assoc]
      exact ih _ _ _
    · exact ih none _ _

/-- The actual ideal-PRF signing transcript has exactly the distribution of the
    memoized ITSR tape simulation, for either epoch policy and any transcript test. -/
theorem signing_transcript_eq_memoized_tape {n keyLen qHash qSign : Nat}
    (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes)
    (sampleMsg : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (A : SeedWithheldEufCmaAdv qHash qSign)
    (w : (Spec.Bytes × PqHashSig) × List (Spec.Bytes × PqHashSig) → Nat) :
    let t := (canonicalizeAdvOptRand A).run (derivePublicKeyIdealPrf suite params seed sec)
    Spec.sampleSum n (fun c =>
      let sign := signQueryIdealPrf suite params seed (sampleMsg c).2 sec
      let run := evalLatchedAdaptiveTree latchOn suite.rawHash sign t 0
      w (run.1, signLogFromOracle sign run.2)) * powItsr 32 qSign =
    n * Spec.sampleSum (powItsr 32 qSign) (fun j => w (evalMemoPrf 65 (fun _ => none)
      (itsrVecSampler 32 qSign j) (signingTranscriptCode latchOn suite params seed sec t 0 []))) := by
  intro t
  have hb := signingTranscriptCode_within latchOn suite params seed sec t 0 [] ((canonicalizeAdvOptRand A).bounded _)
  simpa only [signingTranscriptCode_eval, List.nil_append] using prf_table_eq_memoized_tape hu _ hb w

/-- Each fresh PRF input commits its first original message to the ITSR oracle.
    The cache keeps the first request alongside the randomizer, including on a
    signing failure. Repeated inputs use that same randomizer. -/
def memoItsrTranscriptCode {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes) :
    ProdAdaptiveTree R → Nat → List (Spec.Bytes × PqHashSig) →
      (Spec.Bytes → Option (Spec.Bytes × ProdSigningQuery)) →
      Spec.Code Spec.byteOracleIface (R × List (Spec.Bytes × PqHashSig))
  | .pure r, _, log, _ => .ret (r, log)
  | .hashQuery x k, lo, log, cache =>
    memoItsrTranscriptCode latchOn suite params seed sec (k (suite.rawHash x)) lo log cache
  | .signQuery q k, lo, log, cache =>
    if latchOn = false ∨ lo ≤ q.epoch then
      let pk := derivePublicKeyIdealPrf suite params seed sec
      let x := signingPrfInput (secOverlaySuite suite seed sec) pk q
      let resume := fun b nextCache =>
        let sig := signQueryIdealPrf suite params seed (fun _ => b) sec q
        let entries := match sig with | none => [] | some s => [(q.message, s)]
        memoItsrTranscriptCode latchOn suite params seed sec (k sig) (q.epoch + 1) (log ++ entries) nextCache
      match cache x with
      | some (b, _) => resume b cache
      | none => .call q.message fun b => resume b (fun y => if y = x then some (b, q) else cache y)
    else memoItsrTranscriptCode latchOn suite params seed sec (k none) lo log cache

private theorem headD_drop_getD (tape : List Spec.Bytes) (i : Nat) :
    (tape.drop i).headD [] = tape.getD i [] := by
  induction i generalizing tape with
  | zero => cases tape <;> rfl
  | succ i ih => cases tape with
    | nil => rfl
    | cons _ t => exact ih t

private theorem tail_drop_succ (tape : List Spec.Bytes) (i : Nat) :
    (tape.drop i).tail = tape.drop (i+1) := by
  induction i generalizing tape with
  | zero => cases tape <;> rfl
  | succ i ih => cases tape with
    | nil => rfl
    | cons _ t => exact ih t

private theorem memoItsrTranscriptCode_play {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes)
    (tape : List Spec.Bytes) (cap : Nat) :
    ∀ {qH qS} (t : ProdAdaptiveTree R) (lo : Nat) (log : List (Spec.Bytes × PqHashSig))
      (cache : Spec.Bytes → Option (Spec.Bytes × ProdSigningQuery)) (commits : List (Spec.Bytes × Spec.Bytes)),
      ProdDualBounded qH qS t → commits.length + qS ≤ cap →
      (Spec.Code.play (Spec.itsrOracle cap (fun i => tape.getD i []))
        (memoItsrTranscriptCode latchOn suite params seed sec t lo log cache) commits).1 =
      evalMemoPrf 65 (fun z => (cache z).map Prod.fst) (tape.drop commits.length)
        (signingTranscriptCode latchOn suite params seed sec t lo log)
  | _, _, .pure r, _, _, _, _, _, _ => by
    simp only [memoItsrTranscriptCode, Spec.Code.play_ret, signingTranscriptCode, evalMemoPrf]
  | 0, _, .hashQuery _ _, _, _, _, _, h, _ => h.elim
  | _+1, _, .hashQuery x k, lo, log, cache, commits, h, capOK =>
    memoItsrTranscriptCode_play latchOn suite params seed sec tape cap
      (k (suite.rawHash x)) lo log cache commits (h _) capOK
  | _, 0, .signQuery _ _, _, _, _, _, h, _ => h.elim
  | _, qS+1, .signQuery q k, lo, log, cache, commits, h, capOK => by
    let pk := derivePublicKeyIdealPrf suite params seed sec
    let x := signingPrfInput (secOverlaySuite suite seed sec) pk q
    rw [memoItsrTranscriptCode, signingTranscriptCode]
    by_cases admit : latchOn = false ∨ lo ≤ q.epoch
    · simp only [admit, ↓reduceIte, evalMemoPrf]
      cases hit : cache x with
      | some entry =>
        rcases entry with ⟨b, first⟩
        simp only [Option.map_some]
        exact memoItsrTranscriptCode_play latchOn suite params seed sec tape cap _ _ _ cache commits (h _) (by omega)
      | none =>
        have head := headD_drop_getD tape commits.length
        have tail := tail_drop_succ tape commits.length
        have room : commits.length < cap := by omega
        simp only [Option.map_none, ↓reduceIte, head, tail,
          Spec.Code.play_call, Spec.itsrOracle_eq, room]
        let b := tape.getD commits.length []
        let nextCache := fun y => if y = x then some (b,q) else cache y
        have eq : (fun z => (nextCache z).map Prod.fst) = remember (fun z => (cache z).map Prod.fst) x b := by
          funext z
          by_cases hz : z = x <;> simp [nextCache, remember, hz]
        let sig := signQueryIdealPrf suite params seed (fun _ => b) sec q
        let entries := match sig with | none => [] | some v => [(q.message,v)]
        have ih := memoItsrTranscriptCode_play latchOn suite params seed sec tape cap
          (k sig) (q.epoch+1) (log ++ entries) nextCache
          (commits ++ [(b,q.message)]) (h _) (by simp only [List.length_append, List.length_singleton]; omega)
        have valid : (signingPrfInput (secOverlaySuite suite seed sec)
            (derivePublicKeyIdealPrf suite params seed sec) q).length = 65 := encodePrfMsg65_length _ _
        rw [ite_eq_left valid]
        simpa only [List.length_append, List.length_singleton, eq] using ih
    · simp only [admit, ↓reduceIte]
      exact memoItsrTranscriptCode_play latchOn suite params seed sec tape cap (k none) lo log cache
        commits (h none) (by omega)

/-- Replace the actual message-PRF table by an interactive ITSR challenger on
    original messages, preserving the distribution of the forger output and
    successful signing transcript. -/
theorem signing_transcript_eq_interactive_itsr {n keyLen qHash qSign : Nat}
    (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (seed : Spec.Bytes) (sec : Spec.Bytes → Spec.Bytes)
    (sampleMsg : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (A : SeedWithheldEufCmaAdv qHash qSign)
    (w : (Spec.Bytes × PqHashSig) × List (Spec.Bytes × PqHashSig) → Nat) :
    let t := (canonicalizeAdvOptRand A).run (derivePublicKeyIdealPrf suite params seed sec)
    Spec.sampleSum n (fun c =>
      let sign := signQueryIdealPrf suite params seed (sampleMsg c).2 sec
      let run := evalLatchedAdaptiveTree latchOn suite.rawHash sign t 0
      w (run.1, signLogFromOracle sign run.2)) * powItsr 32 qSign =
    n * Spec.sampleSum (powItsr 32 qSign) (fun j => w (Spec.Code.play
      (Spec.itsrOracle qSign (fun i => (itsrVecSampler 32 qSign j).getD i []))
      (memoItsrTranscriptCode latchOn suite params seed sec t 0 [] (fun _ => none)) []).1) := by
  intro t
  rw [signing_transcript_eq_memoized_tape latchOn suite params seed sec sampleMsg hu A w]
  exact congrArg (n * ·) (Spec.sampleSum_ext fun j => congrArg w
    (memoItsrTranscriptCode_play latchOn suite params seed sec (itsrVecSampler 32 qSign j) qSign
      t 0 [] (fun _ => none) [] ((canonicalizeAdvOptRand A).bounded _) (by simp)).symm)

private abbrev RepresentedLog (suite : TweakableHashSuite) (p : PqHashParams) (pk : PqPublicKey)
    (log : List (Spec.Bytes × PqHashSig)) (commits : List (Spec.Bytes × Spec.Bytes)) :=
  ∀ e ∈ log, verifyProductionPqHashSig suite p pk e.1 e.2 = true ∧
    ∃ first, (e.2.rRand, first) ∈ commits ∧
      thPreHash suite pk.pkSeed pk.pkRoot e.1 = thPreHash suite pk.pkSeed pk.pkRoot first

private theorem representedLog_resume (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (q first : ProdSigningQuery) (b : Spec.Bytes)
    (log : List (Spec.Bytes × PqHashSig)) (commits : List (Spec.Bytes × Spec.Bytes)) :
    let pk := derivePublicKeyIdealPrf suite p s f
    let ov := secOverlaySuite suite s f
    let sig := signQueryIdealPrf suite p s (fun _ => b) f q
    let entries := match sig with | none => [] | some v => [(q.message, v)]
    RepresentedLog suite p pk log commits → (b, first.message) ∈ commits →
    signingPrfInput ov pk q = signingPrfInput ov pk first →
    RepresentedLog suite p pk (log ++ entries) commits := by
  intro pk ov sig entries inv hm he e mem
  rcases List.mem_append.mp mem with old | new
  · exact inv e old
  · cases hs : signQueryIdealPrf suite p s (fun _ => b) f q with
    | none => simp [entries, sig, hs] at new
    | some v =>
      simp only [entries, sig, hs, List.mem_singleton] at new
      subst e
      obtain ⟨r, hv⟩ := idealSigner_const_sound suite p s b f q v hs
      have hh := signingPrfInput_prehash_eq ov pk q first he
      simp only [ov, thPreHash_eq, secOverlaySuite_thCall_cons2] at hh
      exact ⟨hv, first.message, r ▸ hm, by simpa only [thPreHash_eq] using hh⟩

private theorem memoItsr_represented {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (cap : Nat) (rand : Nat → Spec.Bytes) :
    ∀ {qH qS} (t : ProdAdaptiveTree R) (lo : Nat) (log : List (Spec.Bytes × PqHashSig))
      (cache : Spec.Bytes → Option (Spec.Bytes × ProdSigningQuery)) (commits : List (Spec.Bytes × Spec.Bytes)),
      let pk := derivePublicKeyIdealPrf suite p s f
      let key := signingPrfInput (secOverlaySuite suite s f) pk
      let run := Spec.Code.play (Spec.itsrOracle cap rand)
        (memoItsrTranscriptCode latchOn suite p s f t lo log cache) commits
      ProdDualBounded qH qS t → commits.length + qS ≤ cap →
      (∀ x b first, cache x = some (b, first) → x = key first ∧ (b, first.message) ∈ commits) →
      RepresentedLog suite p pk log commits → RepresentedLog suite p pk run.1.2 run.2
  | _, _, .pure _, _, _, _, _, _, _, _, h => by simpa only [memoItsrTranscriptCode, Spec.Code.play_ret] using h
  | 0, _, .hashQuery _ _, _, _, _, _, h, _, _, _ => h.elim
  | _+1, _, .hashQuery x k, lo, log, cache, cs, h, hcap, hc, hl =>
    memoItsr_represented latchOn suite p s f cap rand (k (suite.rawHash x)) lo log cache cs (h _) hcap hc hl
  | _, 0, .signQuery _ _, _, _, _, _, h, _, _, _ => h.elim
  | _, qS+1, .signQuery q k, lo, log, cache, cs, h, hcap, hc, hl => by
    let pk := derivePublicKeyIdealPrf suite p s f
    let key := signingPrfInput (secOverlaySuite suite s f) pk
    simp only [memoItsrTranscriptCode]
    by_cases admit : latchOn = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left admit]
      cases hit : cache (key q) with
      | some entry =>
        obtain ⟨b, first⟩ := entry
        obtain ⟨he, hm⟩ := hc _ _ _ hit
        exact memoItsr_represented latchOn suite p s f cap rand _ _ _ cache cs (h _) (by omega) hc
          (representedLog_resume suite p s f q first b log cs hl hm he)
      | none =>
        have room : cs.length < cap := by omega
        rw [Spec.Code.play_call, Spec.itsrOracle_eq, ite_eq_left room]
        let b := rand cs.length
        let cs' := cs ++ [(b, q.message)]
        have last : (b, q.message) ∈ cs' := List.mem_append_right _ (.head _)
        apply memoItsr_represented latchOn suite p s f cap rand _ _ _ _ cs' (h _)
        · simp only [cs', List.length_append, List.length_singleton]; omega
        · intro x v first eq
          split at eq
          · cases eq; exact ⟨‹_›, last⟩
          · obtain ⟨he, hm⟩ := hc _ _ _ eq
            exact ⟨he, List.mem_append_left _ hm⟩
        · apply representedLog_resume suite p s f q q b log cs' _ last rfl
          intro e he
          obtain ⟨hv, first, hm, hp⟩ := hl e he
          exact ⟨hv, first, List.mem_append_left _ hm, hp⟩
    · rw [ite_eq_right admit]
      exact memoItsr_represented latchOn suite p s f cap rand _ lo log cache cs (h none) (by omega) hc hl

/-- Project the actual forgery from the memoized signing simulation into the ITSR game. -/
def memoItsrAdv {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) :=
  let pk := derivePublicKeyIdealPrf suite p s f
  Spec.Code.bind (memoItsrTranscriptCode latchOn suite p s f ((canonicalizeAdvOptRand A).run pk)
    0 [] (fun _ => none)) (fun out => .ret (out.1.2.rRand, out.1.1))

theorem memoItsrAdv_fresh_cover_wins {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) (rand : Nat → Spec.Bytes) :
    let pk := derivePublicKeyIdealPrf suite p s f
    let t := (canonicalizeAdvOptRand A).run pk
    let run := Spec.Code.play (Spec.itsrOracle qSign rand)
      (memoItsrTranscriptCode latchOn suite p s f t 0 [] (fun _ => none)) []
    ExplicitItsrCover suite p pk run.1.2 run.1.1.1 run.1.1.2 →
    (run.1.1.2.rRand, run.1.1.1) ∉ run.2 →
    let attack := Spec.Code.play (Spec.itsrOracle qSign rand) (memoItsrAdv latchOn suite p s f A) []
    Spec.itsrWin (forsGlobalSubsetSelector suite p pk) attack.2 attack.1 = true := by
  intro pk t run cover fresh attack
  have rep := memoItsr_represented latchOn suite p s f qSign rand t 0 [] (fun _ => none) []
    ((canonicalizeAdvOptRand A).bounded pk) (by simp) (fun _ _ _ eq => nomatch eq) (fun _ hm => nomatch hm)
  simp only [attack, memoItsrAdv, code_play_bind, Spec.Code.play_ret]
  exact explicitItsrCover_cached_win suite p pk _ _ _ _ cover
    (fun e he => (rep e he).1) (fun e he => (rep e he).2) fresh

private abbrev SlotCache := Spec.Bytes → Option (Nat × ProdSigningQuery)

private def valuedCache (rand : Nat → Spec.Bytes) (slots : SlotCache) (x : Spec.Bytes) :=
  (slots x).map fun entry => (rand entry.1, entry.2)

private def addSlot (slots : SlotCache) (key : Spec.Bytes) (i : Nat) (q : ProdSigningQuery) : SlotCache :=
  fun x => if x = key then some (i, q) else slots x

private theorem valuedCache_add (rand : Nat → Spec.Bytes) (slots : SlotCache)
    (key : Spec.Bytes) (i : Nat) (q : ProdSigningQuery) :
    valuedCache rand (addSlot slots key i q) =
      fun x => if x = key then some (rand i, q) else valuedCache rand slots x := by
  funext x
  by_cases h : x = key <;> simp [valuedCache, addSlot, h]

/-- Replay the signing program with one cache slot permanently answering failure.
    The replay consults its tape only at the other slot indices. -/
private def replayFailedSlot {R : Type} (latchOn : Bool) (raw : Spec.Bytes → Spec.Bytes)
    (key : ProdSigningQuery → Spec.Bytes) (sign : ProdSigningQuery → Spec.Bytes → Option PqHashSig)
    (hidden : Nat) (rand : Nat → Spec.Bytes) :
    ProdAdaptiveTree R → Nat → SlotCache → Nat → R
  | .pure out, _, _, _ => out
  | .hashQuery x k, lo, slots, n => replayFailedSlot latchOn raw key sign hidden rand (k (raw x)) lo slots n
  | .signQuery q k, lo, slots, n =>
    if latchOn = false ∨ lo ≤ q.epoch then
      let x := key q
      let resume := fun i cache count =>
        let reply := if i = hidden then none else sign q (rand i)
        replayFailedSlot latchOn raw key sign hidden rand (k reply) (q.epoch+1) cache count
      match slots x with
      | some (i, _) => resume i slots n
      | none => resume n (addSlot slots x n q) (n+1)
    else replayFailedSlot latchOn raw key sign hidden rand (k none) lo slots n

private abbrev signingEntries (q : ProdSigningQuery) (sig : Option PqHashSig) : List (Spec.Bytes × PqHashSig) :=
  match sig with | none => [] | some v => [(q.message, v)]

private theorem memoItsr_log_extends {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (cap : Nat) (rand : Nat → Spec.Bytes) :
    ∀ {qh qs} (t : ProdAdaptiveTree R) lo log cache cs,
      let run := Spec.Code.play (Spec.itsrOracle cap rand)
        (memoItsrTranscriptCode latchOn suite p s f t lo log cache) cs
      ProdDualBounded qh qs t → cs.length + qs ≤ cap →
      cs <+: run.2 ∧ log <+: run.1.2
  | _, _, .pure _, _, _, _, _, _, _ => by simp [memoItsrTranscriptCode, Spec.Code.play_ret]
  | 0, _, .hashQuery _ _, _, _, _, _, h, _ => h.elim
  | _+1, _, .hashQuery x k, lo, log, cache, cs, h, room =>
    memoItsr_log_extends latchOn suite p s f cap rand (k (suite.rawHash x)) lo log cache cs (h _) room
  | _, 0, .signQuery _ _, _, _, _, _, h, _ => h.elim
  | _, qs+1, .signQuery q k, lo, log, cache, cs, h, room => by
    simp only [memoItsrTranscriptCode]
    split
    · split
      · obtain ⟨hcs, hlog⟩ := memoItsr_log_extends latchOn suite p s f cap rand (k _) (q.epoch+1)
          (log ++ signingEntries q _) cache cs (h _) (by omega)
        exact ⟨hcs, (List.prefix_append ..).trans hlog⟩
      · rw [Spec.Code.play_call, Spec.itsrOracle_eq, ite_eq_left (show cs.length < cap by omega)]
        obtain ⟨hcs, hlog⟩ := memoItsr_log_extends latchOn suite p s f cap rand (k _) (q.epoch+1)
          (log ++ signingEntries q _) _ (cs ++ [(_, q.message)]) (h _) (by simp; omega)
        exact ⟨(List.prefix_append ..).trans hcs, (List.prefix_append ..).trans hlog⟩
    · exact memoItsr_log_extends latchOn suite p s f cap rand (k none) lo log cache cs (h _) (by omega)

private theorem prefix_index {α : Type} {xs ys : List α} {i : Nat} {a : α}
    (hp : xs <+: ys) (entry : xs[i]? = some a) : ys[i]? = some a := by
  obtain ⟨rest, rfl⟩ := hp
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp entry
  rwa [List.getElem?_append_left hi]

private abbrev SlotsAgree (key : ProdSigningQuery → Spec.Bytes) (rand : Nat → Spec.Bytes)
    (slots : SlotCache) (cs : List (Spec.Bytes × Spec.Bytes)) :=
  ∀ x i first, slots x = some (i, first) →
    x = key first ∧ cs[i]? = some (rand i, first.message)

private theorem slotsAgree_add {key : ProdSigningQuery → Spec.Bytes} {rand : Nat → Spec.Bytes}
    {slots : SlotCache} {cs : List (Spec.Bytes × Spec.Bytes)} (ok : SlotsAgree key rand slots cs)
    (q : ProdSigningQuery) :
    SlotsAgree key rand (addSlot slots (key q) cs.length q) (cs ++ [(rand cs.length, q.message)]) := by
  intro x i first eq
  simp only [addSlot] at eq
  split at eq
  · cases eq
    exact ⟨‹_›, by simp⟩
  · obtain ⟨he, hi⟩ := ok _ _ _ eq
    exact ⟨he, prefix_index (List.prefix_append ..) hi⟩

private theorem memoItsr_failed_replay {R : Type} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (cap target : Nat)
    (rand masked : Nat → Spec.Bytes) (agree : ∀ i, i ≠ target → masked i = rand i)
    (m b : Spec.Bytes) :
    ∀ {qh qs} (t : ProdAdaptiveTree R) lo log (slots : SlotCache) cs,
      let pk := derivePublicKeyIdealPrf suite p s f
      let ov := secOverlaySuite suite s f
      let key := signingPrfInput ov pk
      let sign := fun q z => signQueryIdealPrf suite p s (fun _ => z) f q
      let run := Spec.Code.play (Spec.itsrOracle cap rand)
        (memoItsrTranscriptCode latchOn suite p s f t lo log (valuedCache rand slots)) cs
      ProdDualBounded qh qs t → cs.length + qs ≤ cap → SlotsAgree key rand slots cs →
      run.2[target]? = some (b, m) →
      (∀ e ∈ run.1.2, thPreHash ov pk.pkSeed pk.pkRoot e.1 ≠ thPreHash ov pk.pkSeed pk.pkRoot m) →
      run.1.1 = replayFailedSlot latchOn suite.rawHash key sign target masked t lo slots cs.length
  | _, _, .pure _, _, _, _, _, _, _, _, _, _ => by simp only [memoItsrTranscriptCode, Spec.Code.play_ret, replayFailedSlot]
  | 0, _, .hashQuery _ _, _, _, _, _, h, _, _, _, _ => h.elim
  | _+1, _, .hashQuery x k, lo, log, slots, cs, h, room, hs, atSlot, clean =>
    memoItsr_failed_replay latchOn suite p s f cap target rand masked agree m b
      (k (suite.rawHash x)) lo log slots cs (h _) room hs atSlot clean
  | _, 0, .signQuery _ _, _, _, _, _, h, _, _, _, _ => h.elim
  | _, qs+1, .signQuery q k, lo, log, slots, cs, h, room, hs, atSlot, clean => by
    let pk := derivePublicKeyIdealPrf suite p s f
    let ov := secOverlaySuite suite s f
    let key := signingPrfInput ov pk
    let sign := fun q z => signQueryIdealPrf suite p s (fun _ => z) f q
    have resume (i : Nat) (first : ProdSigningQuery) (cache : SlotCache) (commits : List (Spec.Bytes × Spec.Bytes))
        (keyEq : key q = key first) (indexEq : commits[i]? = some (rand i, first.message))
        (room' : commits.length + qs ≤ cap) (ok : SlotsAgree key rand cache commits) :
        let sig := sign q (rand i)
        let log' := log ++ signingEntries q sig
        let after := Spec.Code.play (Spec.itsrOracle cap rand)
          (memoItsrTranscriptCode latchOn suite p s f (k sig) (q.epoch+1) log' (valuedCache rand cache)) commits
        after.2[target]? = some (b, m) →
        (∀ e ∈ after.1.2, thPreHash ov pk.pkSeed pk.pkRoot e.1 ≠ thPreHash ov pk.pkSeed pk.pkRoot m) →
        after.1.1 = replayFailedSlot latchOn suite.rawHash key sign target masked
          (k (if i = target then none else sign q (masked i))) (q.epoch+1) cache commits.length := by
      intro sig log' after idx clean'
      have eq : (if i = target then none else sign q (masked i)) = sig := by
        by_cases hidden : i = target
        · rw [ite_eq_left hidden]
          have ⟨hcs, hlog⟩ := memoItsr_log_extends latchOn suite p s f cap rand (k sig) (q.epoch+1)
            log' (valuedCache rand cache) commits (h _) room'
          subst i
          have same := (prefix_index hcs indexEq).symm.trans idx
          have msgEq : first.message = m := congrArg Prod.snd (Option.some.inj same)
          cases success : sig with
          | none => rfl
          | some v =>
            have hm : (q.message, v) ∈ log' := by
              simp only [log', success, signingEntries]
              exact List.mem_append_right _ (.head _)
            exact False.elim (clean' _ (hlog.mem hm) (msgEq ▸ signingPrfInput_prehash_eq ov pk q first keyEq))
        · rw [ite_eq_right hidden, agree i hidden]
      rw [eq]
      exact memoItsr_failed_replay latchOn suite p s f cap target rand masked agree m b
        (k sig) (q.epoch+1) log' cache commits (h _) room' ok idx clean'
    simp only [memoItsrTranscriptCode, replayFailedSlot] at atSlot clean ⊢
    by_cases admit : latchOn = false ∨ lo ≤ q.epoch
    · simp only [admit, ↓reduceIte] at atSlot clean ⊢
      cases hit : slots (key q) with
      | some entry =>
        obtain ⟨i, first⟩ := entry
        have vhit : valuedCache rand slots (key q) = some (rand i, first) := by simp [valuedCache, hit]
        dsimp only [key, ov, pk] at vhit hit
        simp only [vhit] at atSlot clean ⊢
        obtain ⟨he, hi⟩ := hs _ _ _ hit
        exact resume i first slots cs he hi (by omega) hs atSlot clean
      | none =>
        have vhit : valuedCache rand slots (key q) = none := by simp [valuedCache, hit]
        have hroom : cs.length < cap := by omega
        dsimp only [key, ov, pk] at vhit hit
        simp only [vhit, Spec.Code.play_call, Spec.itsrOracle_eq, hroom, ↓reduceIte] at atSlot clean ⊢
        let cs' := cs ++ [(rand cs.length, q.message)]
        let cache := addSlot slots (key q) cs.length q
        have eq := valuedCache_add rand slots (key q) cs.length q
        dsimp only [key, ov, pk] at eq
        rw [← eq] at atSlot clean ⊢
        have cap' : cs'.length + qs ≤ cap := by
          simp only [cs', List.length_append, List.length_singleton]; omega
        simpa only [cs', List.length_append, List.length_singleton] using
          resume cs.length q cache cs' rfl (by simp [cs']) cap' (slotsAgree_add hs q) atSlot clean
    · simp only [admit, ↓reduceIte] at atSlot clean ⊢
      exact memoItsr_failed_replay latchOn suite p s f cap target rand masked agree m b
        (k none) lo log slots cs (h none) (by omega) hs atSlot clean

theorem powItsr_pos (w : Nat) : ∀ q, 0 < powItsr w q
  | 0 => Nat.one_pos
  | q + 1 => Nat.mul_pos (pow256_pos w) (powItsr_pos w q)

/-- The encoded secret slot is in the sampled PRF domain, for every sampled seed. -/
theorem secretPrfSlot_input_length {n seedLen : Nat} {seedS : Fin n → Spec.Bytes}
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (i : Fin n) (addr : HashAdrs) :
    (seedS i ++ encodeAdrs addr).length = seedLen + 32 := by
  rw [List.length_append, hSeed.mem, encodeAdrs_length]

/-- Commit to the leaf tweak before revealing the seed. The recovery algorithm sees
    the punctured table, the seed, and the challenged leaf digest. -/
def puncturedTablePreAdv (addr : HashAdrs) (tweak : Spec.Bytes)
    (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) : Spec.Code Spec.targetIface Spec.TargetBreak :=
  .call (.target tweak []) fun digest =>
    .call .reveal fun seed =>
      let s := seed.getD []
      .ret ⟨tweak, [], recover (puncturePrf (s ++ encodeAdrs addr) f) s (digest.getD [])⟩

private theorem puncturedTablePreAdv_win (suite : TweakableHashSuite) (addr : HashAdrs)
    (tweak seed : Spec.Bytes) (hidden : Nat → Spec.Bytes) (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) :
    let th := suiteTweakHash suite
    let run := Spec.Code.play (Spec.smDtPreOracle th 1 hidden)
      (puncturedTablePreAdv addr tweak recover f) ⟨seed, [], false⟩
    let y := th seed tweak (hidden 0)
    Spec.smDtPreWin th run.2 run.1 =
      decide (th seed tweak (recover (puncturePrf (seed ++ encodeAdrs addr) f) seed y) = y) := by
  intro th run y
  have ok : false = false ∧ ([] : List (Spec.Bytes × Spec.Bytes)).length < 1 ∧
      tweak ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst := ⟨rfl, Nat.one_pos, fun h => nomatch h⟩
  dsimp only [run, puncturedTablePreAdv, y]
  rw [Spec.Code.play_call, Spec.smDtPreOracle_target, ite_eq_left ok]
  dsimp only [List.length_nil, List.nil_append, Option.getD]
  rw [Spec.Code.play_call, Spec.smDtPreOracle_reveal, Spec.Code.play_ret, Spec.smDtPreWin_eq]
  simp only [List.any, decide_true, Bool.true_and, Bool.or_false]

/-- Exact single-slot reduction from a punctured ideal secret PRF to SM-DT-PRE.
    The seed determines the challenged table index after the adversary commits its
    hash tweak. Every other PRF entry is available to the recovery algorithm. -/
theorem hulsing_punctured_prf_slot_pre_bound {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (sampleSec : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (addr : HashAdrs) (tweak : Spec.Bytes)
    (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (hClass : ∀ c, 𝒜 (puncturedTablePreAdv addr tweak recover (sampleSec c).2))
    {ε : Spec.RatBound}
    (hard : Spec.SmDtPreHard 𝒜 (suiteTweakHash suite) seedLen 32 1 ε) :
    let game := Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let pair := samplePair seedS sampleSec z
      let seed := pair.1
      let table := pair.2
      let x := seed ++ encodeAdrs addr
      let y := suiteTweakHash suite seed tweak (table.2 x)
      decide (suiteTweakHash suite seed tweak (recover (puncturePrf x table.2) seed y) = y)
    Spec.GameBound game.winProb ε := by
  intro game
  let B := pow256 32
  let A := fun c : Fin nSec => puncturedTablePreAdv addr tweak recover (sampleSec c).2
  let π := Spec.CoinSplit.prod (nSeed * B) nSec
  have pos := Nat.mul_pos (Nat.mul_pos hs (pow256_pos 32)) hc
  have hardB := hard _ _ _ pos π (mkPreSampler seedS) (uniformOn_mkPreSampler hSeed) A hClass
  let pre := Spec.smDtPreGame pos (suiteTweakHash suite) 1
    (fun z => (mkPreSampler seedS (π.chal z)).1)
    (fun z j => (mkPreSampler seedS (π.chal z)).2.getD j [])
    (fun z => A (π.advc z))
  let obs := fun (seed : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (hidden : Spec.Bytes) =>
    let y := suiteTweakHash suite seed tweak hidden
    if decide (suiteTweakHash suite seed tweak (recover f seed y) = y) then 1 else 0
  let w := fun (seed : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) =>
    obs seed (puncturePrf (seed ++ encodeAdrs addr) f) (f (seed ++ encodeAdrs addr))
  have countReal : game.winCount = Spec.sampleSum nSeed (fun i =>
      Spec.sampleSum nSec (fun c => w (seedS i) (sampleSec c).2)) := by
    unfold Spec.FinGame.winCount
    apply samplePair_sum seedS sampleSec (fun z => w z.1 z.2.2)
  have countPre : pre.winCount = Spec.sampleSum nSeed (fun i => Spec.sampleSum B
      (fun b => Spec.sampleSum nSec (fun c => obs (seedS i)
        (puncturePrf (seedS i ++ encodeAdrs addr) (sampleSec c).2) (byteVecSampler 32 b)))) := by
    unfold Spec.FinGame.winCount
    rw [π.sampleSum_eq]
    let sp := Spec.CoinSplit.prod nSeed B
    rw [sp.sampleSum_eq]
    refine Spec.sampleSum_ext (fun i => Spec.sampleSum_ext (fun b => Spec.sampleSum_ext (fun c => ?_)))
    simp only [pre, A, Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs,
      mkPreSampler, samplePair, sp, B, Spec.CoinSplit.chal_pair, Spec.CoinSplit.advc_pair, singleHidden]
    simpa only [obs, List.getD_cons_zero] using
      congrArg (fun flag : Bool => if flag then 1 else 0)
        (puncturedTablePreAdv_win suite addr tweak (seedS i)
          (fun j => [byteVecSampler 32 b].getD j []) recover (sampleSec c).2)
  have counts : game.winCount * B = pre.winCount := by
    rw [countReal, countPre, ← Spec.sampleSum_mul_right]
    exact Spec.sampleSum_ext (fun i => puncturedPrf_draw_sum hSec (seedS i ++ encodeAdrs addr)
      (secretPrfSlot_input_length hSeed i addr) (obs (seedS i)))
  change pre.winCount * ε.den ≤ ε.num * (nSeed * B * nSec) at hardB
  change game.winCount * ε.den ≤ ε.num * (nSeed * nSec)
  apply Nat.le_of_mul_le_mul_right (c := B) _ (pow256_pos 32)
  rw [Nat.mul_right_comm game.winCount, counts, Nat.mul_assoc ε.num]
  exact Nat.le_trans hardB (Nat.le_of_eq (congrArg (ε.num * ·) (Nat.mul_right_comm nSeed B nSec)))

/-- Invert the actual indexed FORS leaf from its digest and the rest of the
    ideal secret table. The hash input is uniform without a UD hop. -/
theorem hulsing_punctured_fors_leaf_pre_bound {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) table)
    (tree : UInt64) (kp j u : Nat)
    (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜 : Spec.Code Spec.targetIface Spec.TargetBreak → Prop} {ε : Spec.RatBound}
    (hard : Spec.SmDtPreHard 𝒜 (suiteTweakHash suite) seedLen 32 1 ε) :
    let addr : HashAdrs := ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
    let target := encodeChainFTweak (forsLeafHashAdrs tree kp j u)
    (∀ c, 𝒜 (puncturedTablePreAdv addr target recover (table c).2)) →
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let pair := samplePair seedS table z
      let s := pair.1
      let f := pair.2.2
      let y := forsIndexedLeafFn (secOverlaySuite suite s f) ⟨[], [], s⟩ tree kp j u
      decide (forsIndexedLeafHash suite s tree kp j u (recover (puncturePrf (s ++ encodeAdrs addr) f) s y) = y)
      ).winProb ε := by
  intro addr target hClass
  have base := hulsing_punctured_prf_slot_pre_bound hs hc suite seedS hSeed table hSec
    addr target recover hClass hard
  let sp := Spec.CoinSplit.prod nSeed nSec
  have hleaf (i : Fin nSeed) (c : Fin nSec) :
      forsIndexedLeafFn (secOverlaySuite suite (seedS i) (table c).2) ⟨[], [], seedS i⟩ tree kp j u =
        suiteTweakHash suite (seedS i) target ((table c).2 (seedS i ++ encodeAdrs addr)) := by
    rw [forsIndexedLeafFn_eq, forsIndexedSecretLeaf_eq, secOverlaySuite_tagPrf_empty]
    have len := ((Spec.PrfSampleOk_eq ..).mp (hSec.mem c)).2 (seedS i ++ encodeAdrs addr)
    rw [padBytes32_of_len32 (len.1 (secretPrfSlot_input_length hSeed i addr))]
    rw [suiteTweakHash_chainF, forsIndexedLeafHash_eq_chainF_adrs, thChainF_eq, thChainF_eq,
      secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
  simpa only [samplePair, hleaf, target, suiteTweakHash_chainF, forsIndexedLeafHash_eq_chainF_adrs] using base

/-- Observe one PRF cell while retaining access to the disjoint cells. -/
def puncturedDigestGame {nSeed nSec : Nat} (hs : 0 < nSeed) (hc : 0 < nSec)
    (seedS : Fin nSeed → Spec.Bytes) (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (addr : HashAdrs) (test : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Bool) :
    Spec.FinGame (nSeed * nSec) :=
  ⟨Nat.mul_pos hs hc, fun z =>
    let pair := samplePair seedS table z
    let x := pair.1 ++ encodeAdrs addr
    test (puncturePrf x pair.2.2) pair.1 (pair.2.2 x)⟩

private def udCoordinateGame {nSeed nSec : Nat} (hs : 0 < nSeed) (hc : 0 < nSec)
    (seedS : Fin nSeed → Spec.Bytes) (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (addr : HashAdrs) (second : Bool)
    (test : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Bool) :
    Spec.FinGame ((nSeed * (pow256 32 * pow256 32)) * nSec) :=
  ⟨Nat.mul_pos (Nat.mul_pos hs (Nat.mul_pos (pow256_pos _) (pow256_pos _))) hc, fun z =>
    let data := samplePair (samplePair seedS (samplePair (byteVecSampler 32) (byteVecSampler 32))) table z
    let seed := data.1.1
    test (puncturePrf (seed ++ encodeAdrs addr) data.2.2) seed
      (if second then data.1.2.2 else data.1.2.1)⟩

private theorem doubleDraw_sum {b : Nat} (second : Bool) (f : Fin b → Nat) :
    Spec.sampleSum b (fun i => Spec.sampleSum b (fun j => f (if second then j else i))) =
      Spec.sampleSum b f * b := by
  cases second with
  | true => simp only [↓reduceIte, Spec.sampleSum_const, Nat.mul_comm b]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Spec.sampleSum_const]
    simpa only [Nat.mul_comm b] using Spec.sampleSum_mul_right b f b

private theorem udCoordinateGame_normalize {nSeed nSec keyLen seedLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) table)
    (addr : HashAdrs) (second : Bool)
    (test : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Bool) :
    let small := (puncturedDigestGame hs hc seedS table addr test).winProb
    let big := (udCoordinateGame hs hc seedS table addr second test).winProb
    small.le big ∧ big.le small := by
  let B := pow256 32
  let obs := fun (seed : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (v : Spec.Bytes) =>
    if test f seed v then 1 else 0
  let w := fun (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (v : Spec.Bytes) =>
    obs s (puncturePrf (s ++ encodeAdrs addr) f) v
  let small := puncturedDigestGame hs hc seedS table addr test
  let big := udCoordinateGame hs hc seedS table addr second test
  have counts : small.winCount * (B * B) = big.winCount := by
    have r := samplePair_sum seedS table (fun z => w z.1 z.2.2 (z.2.2 (z.1 ++ encodeAdrs addr)))
    have l := samplePair_sum (samplePair seedS (samplePair (byteVecSampler 32) (byteVecSampler 32))) table
      (fun z => w z.1.1 z.2.2 (if second then z.1.2.2 else z.1.2.1))
    change small.winCount = _ at r
    change big.winCount = _ at l
    rw [l, r, ← Spec.sampleSum_mul_right, samplePair_sum seedS (samplePair (byteVecSampler 32) (byteVecSampler 32)) (fun z => Spec.sampleSum nSec
      (fun c => w z.1 (table c).2 (if second then z.2.2 else z.2.1)))]
    apply Spec.sampleSum_ext
    intro i
    rw [samplePair_sum (byteVecSampler 32) (byteVecSampler 32) (fun z =>
      Spec.sampleSum nSec (fun c => w (seedS i) (table c).2 (if second then z.2 else z.1)))]
    have each := puncturedPrf_draw_sum hSec (seedS i ++ encodeAdrs addr)
      (secretPrfSlot_input_length hSeed i addr) (obs (seedS i))
    rw [← Nat.mul_assoc, each]
    let weights := fun b => Spec.sampleSum nSec (fun c => w (seedS i) (table c).2 (byteVecSampler 32 b))
    exact (doubleDraw_sum second weights).symm.trans (Spec.sampleSum_ext fun b =>
      Spec.sampleSum_ext fun d => by cases second <;> rfl)
  have size : nSeed * nSec * (B * B) = nSeed * (B * B) * nSec := Nat.mul_right_comm ..
  have eq : small.winCount * (nSeed * (B * B) * nSec) = big.winCount * (nSeed * nSec) :=
    (congrArg (small.winCount * ·) size.symm).trans (by
      rw [← Nat.mul_assoc, Nat.mul_right_comm small.winCount, counts])
  exact ⟨Nat.le_of_eq eq, Nat.le_of_eq eq.symm⟩

/-- A single UD hop at a fixed chain tweak for an arbitrary observation of the
    digest, seed, and off-slot PRF table. The two games use the original coins. -/
theorem hulsing_punctured_prf_slot_ud_bound {nSeed nSec keyLen seedLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) table)
    (addr : HashAdrs) (tweak : Spec.Bytes)
    (test : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Bool)
    {𝒜 : Spec.Code Spec.targetIface Bool → Prop}
    (hClass : ∀ c, 𝒜 (udDigestTest tweak (fun s => test (puncturePrf (s ++ encodeAdrs addr) (table c).2) s)))
    {ε : Spec.RatBound}
    (hard : SmDtUdHard 𝒜 (suiteTweakHash suite) seedLen 32 32 1 ε) :
    let real := puncturedDigestGame hs hc seedS table addr
      (fun f s v => test f s (suiteTweakHash suite s tweak v))
    let ideal := puncturedDigestGame hs hc seedS table addr test
    Spec.GameBound real.winProb (ideal.winProb.add ε) := by
  let obs := fun f s v => test f s (suiteTweakHash suite s tweak v)
  let D := fun c : Fin nSec => udDigestTest tweak (fun s => test (puncturePrf (s ++ encodeAdrs addr) (table c).2) s)
  let π := Spec.CoinSplit.prod (nSeed * (pow256 32 * pow256 32)) nSec
  have hop := hulsing_hop3_ud_chain_simulation
    (Nat.mul_pos (Nat.mul_pos hs (Nat.mul_pos (pow256_pos 32) (pow256_pos 32))) hc)
    (udCoordinateGame hs hc seedS table addr false obs) (udCoordinateGame hs hc seedS table addr true test)
    (suiteTweakHash suite) seedLen 32 32 1 π (mkUdSampler seedS) (uniformOn_mkUdSampler hSeed)
    D hClass hard (fun z => ?_) (fun z => ?_)
  · exact Spec.RatBound.le_trans (udCoordinateGame_normalize hs hc seedS hSeed table hSec addr false obs).1
      (Spec.RatBound.le_trans hop (Spec.RatBound.add_le_add
        (udCoordinateGame_normalize hs hc seedS hSeed table hSec addr true test).2 (Spec.RatBound.le_refl _)))
  · exact (udDigestTest_real_win _ (suiteTweakHash suite)
      (fun z => (mkUdSampler seedS (π.chal z)).1)
      (fun z i => (mkUdSampler seedS (π.chal z)).2.1.getD i []) tweak
      (fun z s => test (puncturePrf (s ++ encodeAdrs addr) (table (π.advc z)).2) s) z).symm
  · exact (udDigestTest_ideal_win _ (fun z => (mkUdSampler seedS (π.chal z)).1)
      (fun z i => (mkUdSampler seedS (π.chal z)).2.2.getD i []) tweak
      (fun z s => test (puncturePrf (s ++ encodeAdrs addr) (table (π.advc z)).2) s) z).symm

/-- One PRE challenge and one UD challenge for each step preceding the target. -/
def wotsSlotLoss (εPre εUd : Spec.RatBound) : Nat → Spec.RatBound
  | 0 => εPre
  | k + 1 => (wotsSlotLoss εPre εUd k).add εUd

/-- Check the recovered preimage against the target at the end of a WOTS suffix. -/
def wotsSlotTest (suite : TweakableHashSuite) (layer : UInt32) (tree : UInt64)
    (kp chain start count : Nat) (target : Spec.Bytes)
    (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (seed v : Spec.Bytes) : Bool :=
  let node := wotsChainSteps suite seed layer tree kp chain start count v
  let y := suiteTweakHash suite seed target node
  decide (suiteTweakHash suite seed target (recover f seed y) = y)

/-- Inverting a fixed WOTS node with its PRF cell hidden costs one PRE
    challenge and one UD hop for each preceding executable chain step. -/
theorem hulsing_wots_slot_chain_bound {nSeed nSec keyLen seedLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) table)
    (layer : UInt32) (tree : UInt64) (kp chain step : Nat)
    (recover : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop} {εPre εUd : Spec.RatBound}
    (hardPre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 εPre)
    (hardUd : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 εUd) :
    let addr : HashAdrs := ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩
    let hashAddr := fun (i : Nat) => HashAdrs.mk layer tree .wotsHash (UInt32.ofNat kp)
      (UInt32.ofNat chain) (UInt32.ofNat i)
    let target := encodeChainFTweak (hashAddr step)
    let test := fun i k => wotsSlotTest suite layer tree kp chain i k target recover
    (∀ c, 𝒜Pre (puncturedTablePreAdv addr target recover (table c).2)) →
    (∀ i k, i + 1 + k = step → ∀ c, 𝒜Ud (udDigestTest (encodeChainFTweak (hashAddr i)) (fun s =>
      test (i+1) k (puncturePrf (s ++ encodeAdrs addr) (table c).2) s))) →
    Spec.GameBound (puncturedDigestGame hs hc seedS table addr (test 0 step)).winProb
      (wotsSlotLoss εPre εUd step) := by
  intro addr hashAddr target test hPre hUd
  suffices aux : ∀ k i, i + k = step → Spec.GameBound
      (puncturedDigestGame hs hc seedS table addr (test i k)).winProb (wotsSlotLoss εPre εUd k) from
    aux step 0 (Nat.zero_add step)
  intro k
  induction k with
  | zero =>
    intro i _
    have base := hulsing_punctured_prf_slot_pre_bound hs hc suite seedS hSeed table hSec
      addr target recover hPre hardPre
    simpa only [test, wotsSlotTest, wotsChainSteps_zero, puncturedDigestGame, wotsSlotLoss] using base
  | succ k ih =>
    intro i hi
    have hi' : i + 1 + k = step := by omega
    have hop := hulsing_punctured_prf_slot_ud_bound hs hc suite seedS hSeed table hSec addr
      (encodeChainFTweak (hashAddr i)) (test (i+1) k) (hUd i k hi') hardUd
    have he : test i (k+1) = (fun f s v => test (i+1) k f s
        (suiteTweakHash suite s (encodeChainFTweak (hashAddr i)) v)) := by
      funext f s v
      simp only [test, wotsSlotTest, wotsChainSteps_succ, suiteTweakHash_chainF, hashAddr]
    rw [he]
    exact Spec.RatBound.le_trans hop (Spec.RatBound.add_le_add (ih (i+1) hi') (Spec.RatBound.le_refl _))

/-- WOTS chains are indexed by the address words actually consumed by the hash. -/
def wotsPrfCell (layer : UInt32) (tree : UInt64) (kp r : Nat) : HashAdrs :=
  ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat r, 0⟩

private theorem chainSteps_at_words (suite : TweakableHashSuite) (s : Spec.Bytes) (l : UInt32) (t : UInt64)
    (k r : Nat) : ∀ n i v,
      wotsChainSteps suite s l t (UInt32.ofNat k).toNat (UInt32.ofNat r).toNat i n v =
        wotsChainSteps suite s l t k r i n v
  | 0, _, _ => by rw [wotsChainSteps_zero, wotsChainSteps_zero]
  | n+1, i, v => by
    simp only [wotsChainSteps_succ, UInt32.ofNat_toNat]
    exact chainSteps_at_words suite s l t k r n (i+1) _

private theorem chainSteps_secOverlay (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (k r : Nat) : ∀ n i v,
    wotsChainSteps (secOverlaySuite suite s f) s l t k r i n v = wotsChainSteps suite s l t k r i n v
  | 0, _, _ => by rw [wotsChainSteps_zero, wotsChainSteps_zero]
  | n+1, i, v => by
    simp only [wotsChainSteps_succ, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
    exact chainSteps_secOverlay suite s f l t k r n (i+1) _

/-- Compute the real node from a physical WOTS secret-PRF cell. -/
def cellWotsNode (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (cell : HashAdrs) (n : Nat) : Spec.Bytes :=
  wotsChainSteps suite s cell.layer cell.tree cell.keyPair.toNat cell.chainIdx.toNat 0 n
    (padBytes32 (f (s ++ encodeAdrs cell)))

theorem ideal_wots_cell (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (l : UInt32) (t : UInt64) (k r n : Nat) :
    honestChainNode (secOverlaySuite suite s f) ⟨[], [], s⟩ l t k r n =
      cellWotsNode suite s f (wotsPrfCell l t k r) n := by
  rw [honestChainNode_eq, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty, chainSteps_secOverlay]
  exact (chainSteps_at_words suite s l t k r n 0 _).symm

/-- Evaluate an ordinary cell from the off-slot table or advance the pinned
    chain from its public challenge node. -/
def pinnedWotsNode (suite : TweakableHashSuite) (s : Spec.Bytes) (off : Spec.Bytes → Spec.Bytes)
    (pin : HashAdrs) (cut : Nat) (digest : Spec.Bytes) (cell : HashAdrs) (n : Nat) :=
  if cell = pin then
    wotsChainSteps suite s cell.layer cell.tree cell.keyPair.toNat cell.chainIdx.toNat cut (n-cut) digest
  else cellWotsNode suite s off cell n

theorem pinnedWotsNode_eq (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (pin cell : HashAdrs) (cut n : Nat) (available : cell = pin → cut ≤ n) :
    pinnedWotsNode suite s (puncturePrf (s ++ encodeAdrs pin) f) pin cut (cellWotsNode suite s f pin cut)
      cell n = cellWotsNode suite s f cell n := by
  unfold pinnedWotsNode
  by_cases he : cell = pin
  · subst cell
    have hn : cut + (n-cut) = n := Nat.add_sub_of_le (available rfl)
    simp only [↓reduceIte, cellWotsNode]
    simpa only [Nat.zero_add, hn] using wotsChainSteps_add suite s pin.layer pin.tree pin.keyPair.toNat
      pin.chainIdx.toNat cut (n-cut) 0 (padBytes32 (f (s ++ encodeAdrs pin)))
  · have ne : s ++ encodeAdrs cell ≠ s ++ encodeAdrs pin :=
      fun h => he (encodeAdrs_injective (List.append_cancel_left h))
    simp only [he, ↓reduceIte, cellWotsNode, puncturePrf, ne]

/-- Reconstruct the XMSS leaf for every key pair from public chain endpoints. -/
def pinnedWotsPk (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes) (off : Spec.Bytes → Spec.Bytes)
    (pin : HashAdrs) (cut : Nat) (digest : Spec.Bytes) (l : UInt32) (t : UInt64) (k : Nat) :=
  thTweakTl suite s ⟨l, t, .wotsPk, UInt32.ofNat k, 0, 0⟩ ((List.range p.ell1).map fun r =>
    pinnedWotsNode suite s off pin cut digest (wotsPrfCell l t k r) (p.w-1))

theorem pinnedWotsPk_eq (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : HashAdrs) (cut : Nat) (hcut : cut ≤ p.w-1)
    (l : UInt32) (t : UInt64) (k : Nat) :
    computeWotsPk (secOverlaySuite suite s f) p ⟨[], [], s⟩ l t k =
      pinnedWotsPk suite p s (puncturePrf (s ++ encodeAdrs pin) f) pin cut
        (cellWotsNode suite s f pin cut) l t k := by
  rw [pinnedWotsPk, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
  congr 1
  apply List.map_congr_left
  intro r _
  exact (ideal_wots_cell suite s f l t k r _).trans
    (pinnedWotsNode_eq suite s f pin _ cut _ (fun _ => hcut)).symm

/-- Full top-layer public key supplied to a public-key-dependent adaptive adversary
    by a one-cell WOTS simulator. -/
def pinnedWotsPublicKey (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (off : Spec.Bytes → Spec.Bytes) (pin : HashAdrs) (cut : Nat) (digest : Spec.Bytes) : PqPublicKey :=
  let top := UInt32.ofNat (p.numLayers-1)
  ⟨s, computeMerkleNode suite s top 0 .tree (pinnedWotsPk suite p s off pin cut digest top 0) p.subtreeHeight 0⟩

theorem pinnedWotsPublicKey_eq (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : HashAdrs) (cut : Nat) (hcut : cut ≤ p.w-1) :
    derivePublicKeyIdealPrf suite p s f = pinnedWotsPublicKey suite p s (puncturePrf (s ++ encodeAdrs pin) f)
      pin cut (cellWotsNode suite s f pin cut) := by
  rw [derivePublicKeyIdealPrf.public_eqs, derivePublicKey, pinnedWotsPublicKey]
  dsimp only
  rw [computeXmssSubtreeRoot_eq, ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
  congr 1
  exact secOverlaySuite_real_merkleNodeKp suite s f _ _ _ _ _ _
    (pinnedWotsPk_eq suite p s f pin cut hcut _ _) _ _ _

/-- A public-key-dependent candidate for an actual WOTS node in the ideal
    secret-PRF game. The public key is derived from the same table as the target. -/
theorem hulsing_wots_pk_dependent_slot_bound {nSeed nSec keyLen seedLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seedS : Fin nSeed → Spec.Bytes)
    (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) table)
    (l : UInt32) (t : UInt64) (kp r step : Nat) (hStep : step < p.w-1)
    (candidate : PqPublicKey → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop} {εPre εUd : Spec.RatBound}
    (hardPre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 εPre)
    (hardUd : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 εUd) :
    let addr := wotsPrfCell l t kp r
    let ha := fun (i : Nat) => HashAdrs.mk l t .wotsHash (UInt32.ofNat kp) (UInt32.ofNat r) (UInt32.ofNat i)
    let target := encodeChainFTweak (ha step)
    let recover := fun off s y => candidate (pinnedWotsPublicKey suite p s off addr (step+1) y)
    (∀ c, 𝒜Pre (puncturedTablePreAdv addr target recover (table c).2)) →
    (∀ i k, i+1+k = step → ∀ c, 𝒜Ud (udDigestTest (encodeChainFTweak (ha i)) (fun s =>
      wotsSlotTest suite l t kp r (i+1) k target recover
        (puncturePrf (s ++ encodeAdrs addr) (table c).2) s))) →
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let pair := samplePair seedS table z
      let s := pair.1
      let f := pair.2.2
      decide (thChainF suite s (ha step) (candidate (derivePublicKeyIdealPrf suite p s f)) =
        honestChainNode (secOverlaySuite suite s f) ⟨[],[],s⟩ l t kp r (step+1))).winProb
      (wotsSlotLoss εPre εUd step) := by
  intro addr ha target recover hPre hUd
  have bound := hulsing_wots_slot_chain_bound hs hc suite seedS hSeed table hSec l t kp r step recover
    hardPre hardUd hPre hUd
  let sp := Spec.CoinSplit.prod nSeed nSec
  have point (i : Fin nSeed) (c : Fin nSec) :
      let s := seedS i
      let f := (table c).2
      let ov := secOverlaySuite suite s f
      suiteTweakHash suite s target (wotsChainSteps suite s l t kp r 0 step (f (s ++ encodeAdrs addr))) =
        honestChainNode ov ⟨[],[],s⟩ l t kp r (step+1) := by
    intro s f ov
    have len := (((Spec.PrfSampleOk_eq ..).mp (hSec.mem c)).2 (s ++ encodeAdrs addr)).1
      (secretPrfSlot_input_length hSeed i addr)
    rw [← honestChainNode_succ, honestChainNode_eq, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty]
    change _ = thChainF (secOverlaySuite suite s f) s (ha step) (wotsChainSteps (secOverlaySuite suite s f)
      s l t kp r 0 step (padBytes32 ((table c).2 (s ++ encodeAdrs addr))))
    rw [padBytes32_of_len32 len, chainSteps_secOverlay, suiteTweakHash_chainF]
    rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
  have pk (i : Fin nSeed) (c : Fin nSec) :
      let s := seedS i
      let f := (table c).2
      derivePublicKeyIdealPrf suite p s f = pinnedWotsPublicKey suite p s (puncturePrf (s ++ encodeAdrs addr) f)
        addr (step+1) (honestChainNode (secOverlaySuite suite s f) ⟨[],[],s⟩ l t kp r (step+1)) :=
    (pinnedWotsPublicKey_eq suite p _ _ addr (step+1) hStep).trans
      (congrArg _ (ideal_wots_cell suite _ _ l t kp r (step+1)).symm)
  let actual := fun z : Fin (nSeed * nSec) =>
    let s := seedS (sp.chal z)
    let f := (table (sp.advc z)).2
    decide (thChainF suite s (ha step) (candidate (derivePublicKeyIdealPrf suite p s f)) =
      honestChainNode (secOverlaySuite suite s f) ⟨[],[],s⟩ l t kp r (step+1))
  have eq : (puncturedDigestGame hs hc seedS table addr (wotsSlotTest suite l t kp r 0 step target recover)).win =
      actual := by
    funext z
    let s := seedS (sp.chal z)
    let f := (table (sp.advc z)).2
    let ov := secOverlaySuite suite s f
    let node := honestChainNode ov ⟨[],[],s⟩ l t kp r (step+1)
    let y := suiteTweakHash suite s target (wotsChainSteps suite s l t kp r 0 step (f (s ++ encodeAdrs addr)))
    change decide (suiteTweakHash suite s target
      (candidate (pinnedWotsPublicKey suite p s (puncturePrf (s ++ encodeAdrs addr) f) addr (step+1) y)) = y) =
      decide (thChainF suite s (ha step) (candidate (derivePublicKeyIdealPrf suite p s f)) = node)
    have hy : y = node := point _ _
    rw [hy, pk (sp.chal z) (sp.advc z), suiteTweakHash_chainF]
  change Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) actual).winProb _
  rw [← eq]
  exact bound

/-- Decide subset cover by searching the finite signing transcript. -/
instance decidableExplicitItsrCover (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8)
    (sigStar : PqHashSig) : Decidable (ExplicitItsrCover suite params pk log msgStar sigStar) :=
  decidable_of_iff (verifyProductionPqHashSig suite params pk msgStar sigStar = true ∧
    params.statefulJorts = false ∧ 0 < params.forsTrees ∧
    (∀ e ∈ log, e.1 ≠ msgStar) ∧ ∀ pos ∈ prodSigForsLeaves suite params pk msgStar sigStar,
      ∃ e ∈ log, pos ∈ prodSigForsLeaves suite params pk e.1 e.2)
    ⟨fun ⟨ha, hst, ht, hf, hc⟩ => ⟨ha, hst, ht, hf, hc⟩,
     fun h => ⟨h.accepted, h.stateless, h.trees_pos, h.fresh, h.covered⟩⟩

/-- ITSR loss on memoized transcripts whose forged pair is absent from the
    challenger log. This game runs the same cache on successes and failures. -/
theorem memoItsr_fresh_cover_bound {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign)
    {𝒜 : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop} {ε : Spec.RatBound}
    (member : 𝒜 (memoItsrAdv latchOn suite p s f A))
    (hard : Spec.ItsrHard 𝒜 (forsGlobalSubsetSelector suite p (derivePublicKeyIdealPrf suite p s f))
      32 qSign ε) :
    let pk := derivePublicKeyIdealPrf suite p s f
    let t := (canonicalizeAdvOptRand A).run pk
    let pos := powItsr_pos 32 qSign
    Spec.GameBound (Spec.FinGame.mk pos fun z =>
      let rand := fun i => (itsrVecSampler 32 qSign z).getD i []
      let run := Spec.Code.play (Spec.itsrOracle qSign rand)
        (memoItsrTranscriptCode latchOn suite p s f t 0 [] (fun _ => none)) []
      decide (ExplicitItsrCover suite p pk run.1.2 run.1.1.1 run.1.1.2 ∧
        (run.1.1.2.rRand, run.1.1.1) ∉ run.2)).winProb ε := by
  intro pk t pos
  have bound := hard _ _ 1 pos (Spec.CoinSplit.challengerOnly _)
    (itsrVecSampler 32 qSign) (uniformOn_itsrVecSampler ..)
    (fun _ => memoItsrAdv latchOn suite p s f A) (fun _ => member)
  apply Spec.GameBound.trans (Spec.event_le_reduction_win _ _ _) bound
  intro z win
  obtain ⟨hc, hf⟩ := of_decide_eq_true win
  rw [Spec.itsrGame_win, Spec.itsrRun_eq, Spec.CoinSplit.challengerOnly_chal]
  exact memoItsrAdv_fresh_cover_wins latchOn suite p s f A _ hc hf

private theorem itsr_commit_at_index {R : Type} (cap : Nat) (rand : Nat → Spec.Bytes)
    (c : Spec.Code Spec.byteOracleIface R) :
    let cs := (Spec.Code.play (Spec.itsrOracle cap rand) c []).2
    cs.length ≤ cap ∧ ∀ i b m, cs[i]? = some (b, m) → rand i = b := by
  let inv := fun cs : List (Spec.Bytes × Spec.Bytes) =>
    cs.length ≤ cap ∧ ∀ i b m, cs[i]? = some (b, m) → rand i = b
  apply Spec.Code.play_invariant (Spec.itsrOracle cap rand) inv
  · intro cs m ok
    rw [Spec.itsrOracle_eq]
    split
    · rename_i room
      refine ⟨by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      intro i b msg he
      by_cases old : i < cs.length
      · rw [List.getElem?_append_left old] at he
        exact ok.2 i b msg he
      · rw [List.getElem?_append_right (by omega)] at he
        obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp he
        have eq : i = cs.length := by simp only [List.length_singleton] at hi; omega
        subst i
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at he
        exact he.1
    · exact ok
  · exact ⟨Nat.zero_le cap, fun _ _ _ he => nomatch he⟩

private theorem sampleSum_term_le : ∀ {n : Nat} (w : Fin n → Nat) (i : Fin n), w i ≤ Spec.sampleSum n w
  | 0, _, i => i.elim0
  | _+1, _, ⟨0, _⟩ => Nat.le_add_right _ _
  | n+1, w, ⟨i+1, hi⟩ => by
    rw [Spec.sampleSum_succ]
    exact Nat.le_trans (sampleSum_term_le (fun j : Fin n => w ⟨j.val+1, Nat.succ_lt_succ j.isLt⟩)
      ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (Nat.le_add_left _ _)

/-- Union over the possible cache allocation indices of an adaptive forgery. -/
theorem itsr_tape_guess_bound (width q : Nat) (predict : Fin q → List Spec.Bytes → Spec.Bytes) :
    Spec.GameBound (Spec.FinGame.mk (powItsr_pos width q) fun z =>
      let tape := itsrVecSampler width q z
      decide (∃ i : Fin q, tape.getD i [] = predict i (tape.set i []))).winProb
      ⟨q, pow256 width, pow256_pos width⟩ := by
  let T := powItsr width q
  let B := pow256 width
  let hits := fun (z : Fin T) (i : Fin q) =>
    let tape := itsrVecSampler width q z
    tape.getD i [] = predict i (tape.set i [])
  let w := fun z i => if hits z i then 1 else 0
  change Spec.sampleSum T (fun z => if decide (∃ i, hits z i) then 1 else 0) * B ≤ q * T
  have h := Spec.sampleSum_le T (fun z => if decide (∃ i, hits z i) then 1 else 0) (fun z => Spec.sampleSum q (w z)) (fun z => by
    split
    · rename_i he
      obtain ⟨i, hi⟩ := of_decide_eq_true he
      simpa only [w, hi, ↓reduceIte] using sampleSum_term_le (w z) i
    · exact Nat.zero_le _)
  apply Nat.le_trans (Nat.mul_le_mul_right B h)
  rw [Spec.sampleSum_comm T q w, ← Spec.sampleSum_mul_right]
  simpa only [Spec.sampleSum_const] using Spec.sampleSum_le q _ (fun _ => T)
    (fun i => itsr_erased_coordinate_count width q i i.isLt (predict i))

abbrev cleanSigningPrehash (suite : TweakableHashSuite) (pk : PqPublicKey)
    (log : List (Spec.Bytes × PqHashSig)) (m : Spec.Bytes) : Prop :=
  ∀ e ∈ log, thPreHash suite pk.pkSeed pk.pkRoot e.1 ≠ thPreHash suite pk.pkSeed pk.pkRoot m

/-- When the forged message's prehash was never successfully signed, guessing a
    previously committed pair costs at most one 32-byte guess per cache allocation. -/
theorem memoItsr_committed_guess_bound {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    let pk := derivePublicKeyIdealPrf suite p s f
    let t := (canonicalizeAdvOptRand A).run pk
    Spec.GameBound (Spec.FinGame.mk (powItsr_pos 32 qSign) fun z =>
      let rand := fun i => (itsrVecSampler 32 qSign z).getD i []
      let run := Spec.Code.play (Spec.itsrOracle qSign rand)
        (memoItsrTranscriptCode latchOn suite p s f t 0 [] (fun _ => none)) []
      decide ((run.1.1.2.rRand, run.1.1.1) ∈ run.2 ∧ cleanSigningPrehash suite pk run.1.2 run.1.1.1)).winProb
      ⟨qSign, 2 ^ 256, by decide⟩ := by
  intro pk t
  let ov := secOverlaySuite suite s f
  let key := signingPrfInput ov pk
  let sign := fun q z => signQueryIdealPrf suite p s (fun _ => z) f q
  let slots : SlotCache := fun _ => none
  let predict := fun (i : Fin qSign) (tape : List Spec.Bytes) =>
    (replayFailedSlot latchOn suite.rawHash key sign i (fun j => tape.getD j []) t 0 slots 0).2.rRand
  have bound := itsr_tape_guess_bound 32 qSign predict
  have size : (⟨qSign, pow256 32, pow256_pos 32⟩ : Spec.RatBound) = ⟨qSign, 2 ^ 256, by decide⟩ :=
    Spec.RatBound.ext rfl (by change pow256 32 = 2 ^ 256; rw [pow256_eq_pow])
  rw [size] at bound
  apply Spec.GameBound.trans (Spec.event_le_reduction_win _ _ _) bound
  intro z he
  let tape := itsrVecSampler 32 qSign z
  let rand := fun i => tape.getD i []
  let c := memoItsrTranscriptCode latchOn suite p s f t 0 [] (fun _ => none)
  let run := Spec.Code.play (Spec.itsrOracle qSign rand) c []
  obtain ⟨mem, clean⟩ := of_decide_eq_true he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp mem
  have ⟨len, draws⟩ := itsr_commit_at_index qSign rand c
  have lt : i < qSign := by
    obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hi
    exact Nat.lt_of_lt_of_le h len
  let masked := fun j => (tape.set i []).getD j []
  have agree (j : Nat) (ne : j ≠ i) : masked j = rand j := by
    simp only [masked, rand, List.getD_eq_getElem?_getD, List.getElem?_set_ne ne.symm]
  have eq := memoItsr_failed_replay latchOn suite p s f qSign i rand masked agree
    run.1.1.1 run.1.1.2.rRand t 0 [] slots [] ((canonicalizeAdvOptRand A).bounded pk)
    (by simp) (fun _ _ _ h => nomatch h) hi (by
      intro e hm
      simpa only [thPreHash_eq, secOverlaySuite_thCall_cons2] using clean e hm)
  apply decide_eq_true
  exact ⟨⟨i, lt⟩, (draws i _ _ hi).trans (congrArg (fun x => x.2.rRand) eq)⟩

private def logPrehashCollision (suite : TweakableHashSuite) (pk : PqPublicKey) (m : Spec.Bytes) :
    List (Spec.Bytes × PqHashSig) → Option (ExplicitTcrWitness suite pk.pkSeed)
  | [] => none
  | (msg, _) :: rest =>
    if h : msg ≠ m ∧ thPreHash suite pk.pkSeed pk.pkRoot msg = thPreHash suite pk.pkSeed pk.pkRoot m then
      some (prehashWitness suite pk msg m h.1 h.2)
    else logPrehashCollision suite pk m rest

private theorem logPrehashCollision_none (suite : TweakableHashSuite) (pk : PqPublicKey) (m : Spec.Bytes) :
    ∀ log, logPrehashCollision suite pk m log = none → (∀ e ∈ log, e.1 ≠ m) → cleanSigningPrehash suite pk log m
  | [], _, _ => fun _ h => nomatch h
  | (msg, sig) :: rest, hn, fresh => by
    rw [logPrehashCollision] at hn
    split at hn
    · cases hn
    · rename_i no
      exact List.forall_mem_cons.mpr ⟨fun he => no ⟨fresh _ (.head _), he⟩,
        logPrehashCollision_none suite pk m rest hn (fun e he => fresh e (.tail _ he))⟩

private abbrev SigningObservation := (Spec.Bytes × PqHashSig) × List (Spec.Bytes × PqHashSig)

private def idealSigningObservation {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (s : Spec.Bytes) (msg sec : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) : SigningObservation :=
  let sign := signQueryIdealPrf suite p s msg sec
  let pk := derivePublicKeyIdealPrf suite p s sec
  let run := evalLatchedAdaptiveTree latchOn suite.rawHash sign ((canonicalizeAdvOptRand A).run pk) 0
  (run.1, signLogFromOracle sign run.2)

/-- Extract a prehash collision between the forgery and a successful signing reply. -/
def signingPrehashTcr {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (msg sec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) (s : Spec.Bytes) :
    Option (ExplicitTcrWitness suite s) :=
  let pk := derivePublicKeyIdealPrf suite p s sec
  let obs := idealSigningObservation latchOn suite p s msg sec A
  have he : pk.pkSeed = s := by simp only [pk, derivePublicKeyIdealPrf.public_eqs, derivePublicKey]
  he ▸ logPrehashCollision suite pk obs.1.1 obs.2

private def cleanCover (suite : TweakableHashSuite) (p : PqHashParams) (pk : PqPublicKey)
    (obs : SigningObservation) : Bool :=
  decide (ExplicitItsrCover suite p pk obs.2 obs.1.1 obs.1.2 ∧ cleanSigningPrehash suite pk obs.2 obs.1.1)

private theorem cleanCover_ideal_bound {n keyLen qHash qSign : Nat} (pos : 0 < n)
    (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (sec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign)
    (msg : Fin n → Spec.Bytes × (Spec.Bytes → Spec.Bytes)) (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) msg)
    {𝒜 : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop} {ε : Spec.RatBound}
    (member : 𝒜 (memoItsrAdv latchOn suite p s sec A))
    (hard : Spec.ItsrHard 𝒜 (forsGlobalSubsetSelector suite p (derivePublicKeyIdealPrf suite p s sec)) 32 qSign ε) :
    let pk := derivePublicKeyIdealPrf suite p s sec
    Spec.GameBound (Spec.FinGame.mk pos fun i => cleanCover suite p pk
      (idealSigningObservation latchOn suite p s (msg i).2 sec A)).winProb (ε.add ⟨qSign, 2^256, by decide⟩) := by
  intro pk
  let t := (canonicalizeAdvOptRand A).run pk
  let eval := fun z => Spec.Code.play (Spec.itsrOracle qSign (fun i => (itsrVecSampler 32 qSign z).getD i []))
    (memoItsrTranscriptCode latchOn suite p s sec t 0 [] (fun _ => none)) []
  let tapeGame := Spec.FinGame.mk (powItsr_pos 32 qSign) fun z => cleanCover suite p pk (eval z).1
  have h1 := memoItsr_fresh_cover_bound latchOn suite p s sec A member hard
  have h2 := memoItsr_committed_guess_bound latchOn suite p s sec A
  have hb : Spec.GameBound tapeGame.winProb (ε.add ⟨qSign, 2^256, by decide⟩) := by
    apply Spec.GameBound.trans (Spec.event_le_two_reductions _ _ _ _) (Spec.RatBound.add_le_add h1 h2)
    intro z won
    obtain ⟨hc, clean⟩ := of_decide_eq_true won
    by_cases mem : ((eval z).1.1.2.rRand, (eval z).1.1.1) ∈ (eval z).2
    · exact .inr (decide_eq_true ⟨mem, clean⟩)
    · exact .inl (decide_eq_true ⟨hc, mem⟩)
  apply Spec.GameBound.trans _ hb
  have norm := signing_transcript_eq_interactive_itsr latchOn suite p s sec msg hu A
    (fun obs => if cleanCover suite p pk obs then 1 else 0)
  exact Nat.le_of_eq (norm.trans (Nat.mul_comm ..))

private theorem average_challenger_bound {n nc na : Nat} (pos : 0 < n) (π : Spec.CoinSplit n nc na)
    (w : Fin nc → Fin na → Bool) (ε : Spec.RatBound)
    (h : ∀ a, Spec.sampleSum nc (fun i => if w i a then 1 else 0) * ε.den ≤ ε.num * nc) :
    Spec.GameBound (Spec.FinGame.mk pos fun z => w (π.chal z) (π.advc z)).winProb ε := by
  change Spec.sampleSum n _ * ε.den ≤ ε.num * n
  rw [π.sampleSum_eq]
  simp only [π.chal_pair, π.advc_pair]
  rw [Spec.sampleSum_comm nc na, ← Spec.sampleSum_mul_right]
  have hs := Spec.sampleSum_le na _ _ h
  rw [Spec.sampleSum_const] at hs
  rw [π.card_eq]
  simpa only [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using hs

/-- A preimage witness ranges over the FORS trees and WOTS positions in the forgery. -/
instance decidableExplicitPreBreak (suite secOv : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig))
    (msgStar : List UInt8) (sigStar : PqHashSig) :
    Decidable (ExplicitPreBreak suite secOv params sk log msgStar sigStar) := by
  let leaf := sigStar.leafGlobalIdx
  let height := params.subtreeHeight
  let pk := derivePublicKey secOv params sk
  let indices := prodSigForsIdxs suite params pk msgStar sigStar
  let tree := fun (pos : Nat) => UInt64.ofNat (pos / 2 ^ height)
  let kp := fun (pos : Nat) => pos % 2 ^ height
  let pos := fun (i : Nat) => leaf / 2 ^ (i * height)
  apply decidable_of_iff
    ((∃ j : Fin params.forsTrees,
      let u := indices.getD j 0
      params.statefulJorts = false ∧ leaf < 2 ^ (params.numLayers * height) ∧
      u < 2 ^ params.forsHeight ∧
      (∀ e ∈ log, (leaf, j.val, u) ∉ prodSigForsLeaves suite params pk e.1 e.2) ∧
      forsIndexedLeafHash suite sk.pkSeed (tree leaf) (kp leaf) j u
        (sigStar.forsOpenings.getD j ⟨[], []⟩).secretVal =
        forsIndexedLeafFn secOv sk (tree leaf) (kp leaf) j u) ∨
     (∃ (i : Fin params.numLayers) (r : Fin params.ell1) (step : Fin (params.w - 1)),
      let p := pos i
      let layer := UInt32.ofNat i
      leaf < 2 ^ (params.numLayers * height) ∧
      thChainF suite sk.pkSeed
        ⟨layer, tree p, .wotsHash, UInt32.ofNat (kp p), UInt32.ofNat r, UInt32.ofNat step⟩
        ((sigStar.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []) =
        honestChainNode secOv sk layer (tree p) (kp p) r (step.val + 1) ∧
      (∀ e ∈ log, e.2.leafGlobalIdx / 2 ^ (i * height) = p →
        step < (prodLogLayerDigits secOv params sk e i).getD r 0)))
  constructor
  · rintro (⟨j, hs, hl, hu, hn, hi⟩ | ⟨i, r, step, hl, hi, hn⟩)
    · exact .fors j j.isLt hs hl hu hn hi
    · exact .wots i i.isLt r r.isLt step step.isLt hl hi hn
  · intro h
    cases h with
    | fors j hj hs hl hu hn hi => exact .inl ⟨⟨j, hj⟩, hs, hl, hu, hn, hi⟩
    | wots i hi r hr step hstep hl he hn =>
      exact .inr ⟨⟨i, hi⟩, ⟨r, hr⟩, ⟨step, hstep⟩, hl, he, hn⟩

/-- Subset cover and preimage predicates on the actual ideal-PRF signing transcript. -/
def idealPrfBreakEvents {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Spec.Bytes) (rfMsg rfSec : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) : Bool × Bool :=
  let pk := derivePublicKeyIdealPrf suite params pkSeed rfSec
  let signFn := signQueryIdealPrf suite params pkSeed rfMsg rfSec
  let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
    ((canonicalizeAdvOptRand A).run pk) 0
  let log := signLogFromOracle signFn run.2
  (decide (ExplicitItsrCover suite params pk log run.1.1 run.1.2),
   decide (ExplicitPreBreak suite (secOverlaySuite suite pkSeed rfSec) params ⟨[], [], pkSeed⟩
     log run.1.1 run.1.2))

private theorem idealPrfBreakEvents_fst_of {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Spec.Bytes)
    (rfMsg rfSec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) :
    let pk := derivePublicKeyIdealPrf suite params pkSeed rfSec
    let signFn := signQueryIdealPrf suite params pkSeed rfMsg rfSec
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand A).run pk) 0
    ExplicitItsrCover suite params pk (signLogFromOracle signFn run.2) run.1.1 run.1.2 →
    (idealPrfBreakEvents latchOn suite params pkSeed rfMsg rfSec A).1 = true :=
  decide_eq_true

private theorem idealPrfBreakEvents_snd_of {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Spec.Bytes)
    (rfMsg rfSec : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) :
    let pk := derivePublicKeyIdealPrf suite params pkSeed rfSec
    let signFn := signQueryIdealPrf suite params pkSeed rfMsg rfSec
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
      ((canonicalizeAdvOptRand A).run pk) 0
    ExplicitPreBreak suite (secOverlaySuite suite pkSeed rfSec) params ⟨[], [], pkSeed⟩
      (signLogFromOracle signFn run.2) run.1.1 run.1.2 →
    (idealPrfBreakEvents latchOn suite params pkSeed rfMsg rfSec A).2 = true :=
  decide_eq_true

theorem idealPrfBreakEvents_noFors {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (hNoFors : params.statefulJorts = true ∨ params.forsTrees = 0)
    (pkSeed : Spec.Bytes) (rfMsg rfSec : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) :
    (idealPrfBreakEvents latchOn suite params pkSeed rfMsg rfSec A).1 = false := by
  apply decide_eq_false
  intro h
  rcases hNoFors with hs | hz
  · exact Bool.noConfusion (h.stateless.symm.trans hs)
  · exact (Nat.ne_of_gt h.trees_pos) hz

/-- Close subset cover on the ideal-PRF signing game. The independent message table
    supplies the ITSR tape. A successful prehash reuse costs one open-seed commitment. -/
theorem hulsing_idealPrf_cover_bound {n nm nr nc nz ns na qHash qSign keyLen seedLen qTcr : Nat}
    (pos : 0 < n) (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (π₁ : Spec.CoinSplit n nm nr) (π₂ : Spec.CoinSplit nr nc nz) (π₃ : Spec.CoinSplit nz ns na)
    (msg : Fin nm → Spec.Bytes × (Spec.Bytes → Spec.Bytes)) (hu : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) msg)
    (sec : Fin nc → Spec.Bytes → Spec.Bytes) (seed : Fin ns → Spec.Bytes)
    (hs : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (adv : Fin na → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜I : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop}
    {𝒜T : Spec.Code Spec.targetIface Spec.TargetBreak → Prop} {εI εT : Spec.RatBound}
    (mi : ∀ s c a, 𝒜I (memoItsrAdv latchOn suite p (seed s) (sec c) (adv a)))
    (mt : ∀ m c a, 𝒜T (openSeedWitnessAdv suite (signingPrehashTcr latchOn suite p (msg m).2 (sec c) (adv a))))
    (hi : ¬ (p.statefulJorts = true ∨ p.forsTrees = 0) → ∀ s c, Spec.ItsrHard 𝒜I (forsGlobalSubsetSelector suite p (derivePublicKeyIdealPrf suite p (seed s) (sec c)))
      32 qSign εI)
    (ht : SmDtOpenSeedTcrHard 𝒜T (suiteTweakHash suite) seedLen qTcr εT) (room : 0 < qTcr) :
    Spec.GameBound (Spec.FinGame.mk pos fun z => (idealPrfBreakEvents latchOn suite p
      (seed (π₃.chal (π₂.advc (π₁.advc z)))) (msg (π₁.chal z)).2
      (sec (π₂.chal (π₁.advc z))) (adv (π₃.advc (π₂.advc (π₁.advc z))))).1).winProb
      (if p.statefulJorts = true ∨ p.forsTrees = 0 then Spec.RatBound.zero
       else (εI.add ⟨qSign, 2^256, by decide⟩).add εT) := by
  split
  · rename_i absent
    exact Spec.FinGame.bound_zero_of_forall_lose _ fun _ => idealPrfBreakEvents_noFors _ _ _ absent _ _ _ _
  · rename_i present
    let seedR := fun r => seed (π₃.chal (π₂.advc r))
    let secR := fun r => sec (π₂.chal r)
    let advR := fun r => adv (π₃.advc (π₂.advc r))
    let pk := fun r => derivePublicKeyIdealPrf suite p (seedR r) (secR r)
    let obs := fun m r => idealSigningObservation latchOn suite p (seedR r) (msg m).2 (secR r) (advR r)
    let eps := εI.add ⟨qSign, 2^256, by decide⟩
    have posM : 0 < nm := (π₁.chal ⟨0, pos⟩).isLt |> Nat.lt_of_le_of_lt (Nat.zero_le _)
    have clean := average_challenger_bound pos π₁ (fun m r => cleanCover suite p (pk r) (obs m r)) eps
      (fun r => cleanCover_ideal_bound posM latchOn suite p (seedR r) (secR r) (advR r)
        msg hu (mi _ _ _) (hi present _ _))
    let O := Spec.CoinSplit.prod nm (nc * na)
    let I := Spec.CoinSplit.prod nc na
    let extract := fun d => signingPrehashTcr latchOn suite p (msg (O.chal d)).2
      (sec (I.chal (O.advc d))) (adv (I.advc (O.advc d)))
    let π := reassocHop4SeedSplit π₁ π₂ π₃
    have collision := openSeedWitness_bound pos room suite π seed hs extract (fun _ => mt _ _ _) ht
    apply Spec.GameBound.trans (Spec.event_le_two_reductions _ _ _ _) (Spec.RatBound.add_le_add clean collision)
    intro z win
    let m := π₁.chal z
    let r := π₁.advc z
    have cover : ExplicitItsrCover suite p (pk r) (obs m r).2 (obs m r).1.1 (obs m r).1.2 :=
      of_decide_eq_true win
    cases found : logPrehashCollision suite (pk r) (obs m r).1.1 (obs m r).2 with
    | none => exact .inl (decide_eq_true ⟨cover, logPrehashCollision_none _ _ _ _ found cover.fresh⟩)
    | some w =>
      right
      change (extract (π.advc z) (seed (π.chal z))).isSome = true
      have chal : π.chal z = π₃.chal (π₂.advc r) := (reassocHop4SeedSplit_coords π₁ π₂ π₃ z).1
      have rest : π.advc z = O.pair m (I.pair (π₂.chal r) (π₃.advc (π₂.advc r))) :=
        (reassocHop4SeedSplit_coords π₁ π₂ π₃ z).2
      rw [rest, chal]
      simp only [extract, O.chal_pair, O.advc_pair, I.chal_pair, I.advc_pair]
      have flag : ∀ {u v : Spec.Bytes} (eq : u = v) (opt : Option (ExplicitTcrWitness suite u)),
          (eq ▸ opt : Option (ExplicitTcrWitness suite v)).isSome = opt.isSome := by
        intro u v eq opt; cases eq; rfl
      simp only [signingPrehashTcr, flag]
      change (logPrehashCollision suite (pk r) (obs m r).1.1 (obs m r).2).isSome = true
      rw [found]; rfl

/-- Executable EUF-CMA bound after the two PRF hops and the adaptive open-seed
    collision reduction. The remaining probabilities measure subset cover and
    secret-slot inversion on the same ideal-PRF run. -/
abbrev PrfTcrReductionFor (latchOn : Bool) (params : PqHashParams)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (hw : params.w = 4 ∨ params.w = 16) : Prop :=
  ∀ {n nC1 nR1 nC2 nR2 nSeed nA qHash qSign : Nat} (hPos : 0 < n) (suite : TweakableHashSuite)
    (seedLen keyLen qPrfMsg qPrfSec qTcr : Nat)
    (_ : qSign ≤ qPrfMsg) (_ : prfSecQueryBudget params qSign ≤ qPrfSec)
    (_ : 0 < qTcr) (π1 : Spec.CoinSplit n nC1 nR1) (π2 : Spec.CoinSplit nR1 nC2 nR2)
    (π3 : Spec.CoinSplit nR2 nSeed nA)
    (sampleMsg : Fin nC1 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) sampleMsg)
    (sampleSec : Fin nC2 → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (_ : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (seedS : Fin nSeed → Spec.Bytes)
    (_ : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seedS)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Msg 𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (_ : ∀ r1 : Fin nR1, 𝒜Msg (prfMsgHopDistinguisher latchOn suite params
      (seedS (π3.chal (π2.advc r1))) (sampleSec (π2.chal r1)).1 (adv (π3.advc (π2.advc r1)))))
    (_ : ∀ b : Fin (nC1 * nR2),
      let sp := Spec.CoinSplit.prod nC1 nR2
      𝒜Sec (prfSecHopDistinguisher latchOn suite params (seedS (π3.chal (sp.advc b)))
        (sampleMsg (sp.chal b)).2 (adv (π3.advc (sp.advc b)))))
    {𝒜Tcr : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    (_ : ∀ r4 : Fin (nC1 * (nC2 * nA)),
      let spO := Spec.CoinSplit.prod nC1 (nC2 * nA); let spI := Spec.CoinSplit.prod nC2 nA
      let c1 := spO.chal r4; let c2 := spI.chal (spO.advc r4); let a := spI.advc (spO.advc r4)
      𝒜Tcr (openSeedTcrHopAdv latchOn suite params hw (sampleMsg c1).2 (sampleSec c2).2
        (fun x hx => ((Spec.PrfSampleOk_eq keyLen 65 32 _).mp (hSampleMsg.mem c1)).2 x |>.1 hx)
        hOneTimeIfSt (adv a)))
    {εPrfMsg εPrfSec εTcr : Spec.RatBound}
    (_ : Spec.PrfHard 𝒜Msg (suitePrfMsg65 suite) keyLen 65 32 qPrfMsg εPrfMsg)
    (_ : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrfSec εPrfSec)
    (_ : SmDtOpenSeedTcrHard 𝒜Tcr (suiteTweakHash suite) seedLen qTcr εTcr),
    let events := fun ω => idealPrfBreakEvents latchOn suite params
      (seedS (π3.chal (π2.advc (π1.advc ω)))) (sampleMsg (π1.chal ω)).2
      (sampleSec (π2.chal (π1.advc ω))).2 (adv (π3.advc (π2.advc (π1.advc ω))))
    let cover := Spec.FinGame.mk hPos (fun ω => (events ω).1)
    let pre := Spec.FinGame.mk hPos (fun ω => (events ω).2)
    let coverBound := if params.statefulJorts = true ∨ params.forsTrees = 0 then Spec.RatBound.zero else cover.winProb
    Spec.GameBound (execEufCmaGameWith latchOn hPos suite params
      (multiHopFullKeygen π1 π2 π3 sampleMsg sampleSec seedS) (multiHopFullAdv π1 π2 π3 adv)).winProb
      ((((coverBound.add εTcr).add pre.winProb).add εPrfSec).add εPrfMsg)

