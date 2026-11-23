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

