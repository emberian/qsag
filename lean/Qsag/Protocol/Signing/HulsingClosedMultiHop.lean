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

theorem hulsing_prf_tcr_residual_bound (latchOn : Bool) (params : PqHashParams)
    (hOneTimeIfSt : params.statefulJorts = true → latchOn = true)
    (hw : params.w = 4 ∨ params.w = 16) :
    PrfTcrReductionFor latchOn params hOneTimeIfSt hw := by
  intro n nC1 nR1 nC2 nR2 nSeed nA qHash qSign hPos suite seedLen keyLen qPrfMsg qPrfSec qTcr
    hqPrfMsg hqPrfSec hqTcr π1 π2 π3 sampleMsg hSampleMsg sampleSec hSampleSec seedS hSeed adv
    𝒜Msg 𝒜Sec hClassMsg hClassSec 𝒜Tcr hClassTcr εPrfMsg εPrfSec εTcr hPrfMsg hPrfSec hTcr
  intro events cover pre coverBound
  have coverLe : Spec.GameBound cover.winProb coverBound := by
    dsimp only [coverBound]
    split
    · rename_i absent
      exact Spec.FinGame.bound_zero_of_forall_lose cover fun _ => idealPrfBreakEvents_noFors _ _ _ absent _ _ _ _
    · exact Spec.RatBound.le_refl _
  exact hulsing_full_multihop_euf_cma_bound_with latchOn hPos suite params hOneTimeIfSt hw
    seedLen keyLen qPrfMsg qPrfSec qTcr hqPrfMsg hqPrfSec hqTcr π1 π2 π3 sampleMsg hSampleMsg
    sampleSec hSampleSec seedS hSeed adv hClassMsg hClassSec hClassTcr cover.win pre.win
    (fun _ => idealPrfBreakEvents_fst_of _ _ _ _ _ _ _) (fun _ => idealPrfBreakEvents_snd_of _ _ _ _ _ _ _)
    hPrfMsg hPrfSec coverLe hTcr (Spec.RatBound.le_refl _)

#verify_constructive hulsing_idealPrf_cover_bound logPrehashCollision_none cleanCover_ideal_bound average_challenger_bound

#export_eqns puncturePrf wotsPrfCell cellWotsNode pinnedWotsNode wotsSlotLoss puncturedDigestGame

#verify_constructive itsr_commit_at_index sampleSum_term_le itsr_tape_guess_bound memoItsr_committed_guess_bound

#verify_constructive valuedCache_add memoItsr_log_extends prefix_index slotsAgree_add memoItsr_failed_replay

#verify_constructive itsr_erased_coordinate_count powItsr_pos memoItsr_fresh_cover_bound signingPrfInput_prehash_eq representedLog_resume memoItsr_represented memoItsrAdv_fresh_cover_wins

#verify_constructive pair_ext uniformOn_itsrVecSampler uniformOn_samplePair uniform_singleHidden
  uniformOn_mkPreSampler uniformOn_mkUdSampler idealPrfBreakEvents_noFors
  hulsing_prf_tcr_residual_bound fin_choice exchangePrfEntry_invol exchangePrfEntry_mem
  hulsing_wots_pk_dependent_slot_bound chainSteps_at_words chainSteps_secOverlay ideal_wots_cell pinnedWotsNode_eq pinnedWotsPk_eq pinnedWotsPublicKey_eq
  headD_drop_getD tail_drop_succ memoItsrTranscriptCode_play signing_transcript_eq_interactive_itsr
  hulsing_punctured_fors_leaf_pre_bound hulsing_wots_slot_chain_bound doubleDraw_sum udCoordinateGame_normalize hulsing_punctured_prf_slot_ud_bound
  prf_entry_exchange_sum samplePair_sum puncturedPrf_draw_sum secretPrfSlot_input_length
  tape_cons_sum cachedTable_fill cachedTable_puncture evalMemoPrf_sum prf_table_eq_memoized_tape
  idealSigner_at_prfInput signingTranscriptCode_within signingTranscriptCode_eval
  signing_transcript_eq_memoized_tape puncturedTablePreAdv_win hulsing_punctured_prf_slot_pre_bound


/-- Secret-dependent values used when assembling a production signature. -/
structure SigningMaterial where
  wots : UInt32 → UInt64 → Nat → Nat → Nat → Spec.Bytes
  forsSecret : UInt64 → Nat → Nat → Nat → Spec.Bytes
  forsLeaf : UInt64 → Nat → Nat → Nat → Spec.Bytes

def SigningMaterial.ideal (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) :
    SigningMaterial :=
  let ov := secOverlaySuite suite s f
  let sk : PqSecretKey := ⟨[], [], s⟩
  ⟨honestChainNode ov sk, forsIndexedSecretLeaf ov sk, forsIndexedLeafFn ov sk⟩

def forsPrfCell (tree : UInt64) (kp j u : Nat) : HashAdrs :=
  ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩

inductive SigningPin where
  | fors (tree : UInt64) (kp treeIdx leafIdx : Nat)
  | wots (layer : UInt32) (tree : UInt64) (kp chain step : Nat)

def SigningPin.cell : SigningPin → HashAdrs
  | .fors t k j u => forsPrfCell t k j u
  | .wots l t k r _ => wotsPrfCell l t k r

def SigningPin.cut : SigningPin → Nat
  | .fors .. => 0
  | .wots _ _ _ _ step => step + 1

def SigningPin.digest (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) :
    SigningPin → Spec.Bytes
  | .fors t k j u => (SigningMaterial.ideal suite s f).forsLeaf t k j u
  | .wots l t k r step => cellWotsNode suite s f (wotsPrfCell l t k r) (step + 1)

/-- Supply the challenged digest at its physical address. Every unchallenged
    secret comes from the punctured table. -/
def SigningMaterial.pinned (suite : TweakableHashSuite) (s : Spec.Bytes) (off : Spec.Bytes → Spec.Bytes)
    (pin : SigningPin) (y : Spec.Bytes) : SigningMaterial :=
  let view := SigningMaterial.ideal suite s off
  { wots := fun l t k r => pinnedWotsNode suite s off pin.cell pin.cut y (wotsPrfCell l t k r)
    forsSecret := view.forsSecret
    forsLeaf := fun t k j u => if forsPrfCell t k j u = pin.cell then y else view.forsLeaf t k j u }

private theorem off_cell {pin addr : HashAdrs} (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (ne : addr ≠ pin) :
    puncturePrf (s ++ encodeAdrs pin) f (s ++ encodeAdrs addr) = f (s ++ encodeAdrs addr) := by
  rw [puncturePrf.public_eqs, ite_eq_right (fun e => ne (encodeAdrs_injective (List.append_cancel_left e)))]

theorem pinned_fors_secret (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (pin : SigningPin) (t : UInt64) (k j u : Nat) (hne : forsPrfCell t k j u ≠ pin.cell) :
    (SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)).forsSecret t k j u =
      (SigningMaterial.ideal suite s f).forsSecret t k j u := by
  simp only [SigningMaterial.pinned, SigningMaterial.ideal, forsIndexedSecretLeaf_eq, secOverlaySuite_tagPrf_empty]
  exact congrArg padBytes32 (off_cell s f hne)

private theorem forsLeaf_same_cell (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    {t t' : UInt64} {k j u k' j' u' : Nat} (he : forsPrfCell t k j u = forsPrfCell t' k' j' u') :
    (SigningMaterial.ideal suite s f).forsLeaf t k j u = (SigningMaterial.ideal suite s f).forsLeaf t' k' j' u' := by
  simp only [forsPrfCell, HashAdrs.mk.injEq, true_and] at he
  obtain ⟨rfl, hk, hj, hu⟩ := he
  simp only [SigningMaterial.ideal, forsIndexedLeafFn_eq, forsIndexedSecretLeaf_eq, forsIndexedLeafHash_eq,
    thChainF_eq, hk, hj, hu]

theorem pinned_fors_leaf (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (pin : SigningPin) (t : UInt64) (k j u : Nat) :
    (SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)).forsLeaf t k j u =
      (SigningMaterial.ideal suite s f).forsLeaf t k j u := by
  dsimp only [SigningMaterial.pinned]
  split
  · rename_i eq
    cases pin with
    | fors => exact (forsLeaf_same_cell suite s f eq).symm
    | wots => simp [SigningPin.cell, forsPrfCell, wotsPrfCell.public_eqs] at eq
  · rename_i ne
    have hs := pinned_fors_secret suite s f pin t k j u ne
    dsimp only [SigningMaterial.ideal, SigningMaterial.pinned] at hs ⊢
    rw [forsIndexedLeafFn_eq, forsIndexedLeafFn_eq, hs]
    simp only [forsIndexedLeafHash_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]

theorem pinned_wots_node (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (pin : SigningPin) (l : UInt32) (t : UInt64) (k r n : Nat) (available : wotsPrfCell l t k r = pin.cell → pin.cut ≤ n) :
    (SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)).wots l t k r n =
      (SigningMaterial.ideal suite s f).wots l t k r n := by
  simp only [SigningMaterial.pinned, SigningMaterial.ideal, ideal_wots_cell]
  cases pin with
  | fors t' k' j u =>
    have ne : wotsPrfCell l t k r ≠ forsPrfCell t' k' j u := by
      simp [wotsPrfCell.public_eqs, forsPrfCell]
    rw [pinnedWotsNode.public_eqs, SigningPin.cell, ite_eq_right ne]
    simp only [cellWotsNode.public_eqs, off_cell s f ne]
  | wots => exact pinnedWotsNode_eq suite s f _ _ _ n available

/-- The endpoint compression and the Merkle paths use public WOTS nodes only. -/
def SigningMaterial.wotsPk (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (l : UInt32) (t : UInt64) (k : Nat) :=
  thTweakTl suite s ⟨l, t, .wotsPk, UInt32.ofNat k, 0, 0⟩
    ((List.range p.ell1).map fun r => v.wots l t k r (p.w-1))

def SigningMaterial.xmssRoot (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (l : UInt32) (t : UInt64) :=
  computeMerkleNode suite s l t .tree (v.wotsPk suite p s l t) p.subtreeHeight 0

def SigningMaterial.forsRoot (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (t : UInt64) (k : Nat) :=
  thTweakTl suite s ⟨0, t, .forsRoots, UInt32.ofNat k, 0, 0⟩
    ((List.range p.forsTrees).map fun j => computeMerkleNodeKp suite s 0 t .forsTree (UInt32.ofNat k)
      (v.forsLeaf t k j) p.forsHeight j 0)

def SigningMaterial.openings (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (t : UInt64) (k : Nat) (idxs : List Nat) :=
  (List.range p.forsTrees).map fun j =>
    let u := idxs.getD j 0
    (⟨v.forsSecret t k j u, buildMerkleAuthPathKp suite s 0 t .forsTree (UInt32.ofNat k)
      (v.forsLeaf t k j) p.forsHeight j 0 u⟩ : ForsTreeOpening)

theorem ideal_material_wotsPk (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (k : Nat) :
    computeWotsPk (secOverlaySuite suite s f) p ⟨[], [], s⟩ l t k =
      (SigningMaterial.ideal suite s f).wotsPk suite p s l t k := by
  rw [computeWotsPk_eq, SigningMaterial.wotsPk, thTweakTl_eq, thTweakTl_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
  rfl

theorem ideal_material_xmssRoot (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) :
    computeXmssSubtreeRoot (secOverlaySuite suite s f) p ⟨[], [], s⟩ l t =
      (SigningMaterial.ideal suite s f).xmssRoot suite p s l t := by
  rw [computeXmssSubtreeRoot_eq, SigningMaterial.xmssRoot, ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq]
  exact secOverlaySuite_real_merkleNodeKp suite s f _ _ _ _ _ _ (ideal_material_wotsPk suite p s f l t) _ _ _

theorem ideal_material_forsRoot (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (t : UInt64) (k : Nat) :
    computeProductionForsPk (secOverlaySuite suite s f) p ⟨[], [], s⟩ t k =
      (SigningMaterial.ideal suite s f).forsRoot suite p s t k := by
  rw [computeProductionForsPk_eq, SigningMaterial.forsRoot, thTweakTl_eq, thTweakTl_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
  congr 1
  apply List.map_congr_left
  intro j _
  exact secOverlaySuite_real_merkleNodeKp suite s f _ _ _ _ _ _ (fun _ => rfl) _ _ _

theorem ideal_material_openings (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (t : UInt64) (k : Nat) (idxs : List Nat) :
    buildProductionForsOpenings (secOverlaySuite suite s f) p ⟨[], [], s⟩ t k idxs =
      (SigningMaterial.ideal suite s f).openings suite p s t k idxs := by
  rw [buildProductionForsOpenings_def, SigningMaterial.openings]
  apply List.map_congr_left
  intro j _
  dsimp only [SigningMaterial.ideal]
  congr 1
  exact secOverlaySuite_real_authPathKp suite s f _ _ _ _ _ _ (fun _ => rfl) _ _ _ _

def SigningMaterial.publicKey (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) : PqPublicKey := ⟨s, v.xmssRoot suite p s (UInt32.ofNat (p.numLayers-1)) 0⟩

theorem ideal_material_publicKey (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) :
    derivePublicKeyIdealPrf suite p s f = (SigningMaterial.ideal suite s f).publicKey suite p s := by
  simp only [derivePublicKeyIdealPrf.public_eqs, derivePublicKey, SigningMaterial.publicKey, ideal_material_xmssRoot]

private theorem pinned_wotsPk (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) (hcut : pin.cut ≤ p.w-1) (l : UInt32) (t : UInt64) :
    let v := SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)
    v.wotsPk suite p s l t = (SigningMaterial.ideal suite s f).wotsPk suite p s l t := by
  intro v
  funext k
  unfold SigningMaterial.wotsPk
  congr 1
  apply List.map_congr_left
  exact fun r _ => pinned_wots_node suite s f pin l t k r _ (fun _ => hcut)

private theorem pinned_xmssRoot (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) (hcut : pin.cut ≤ p.w-1) :
    let v := SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)
    v.xmssRoot suite p s = (SigningMaterial.ideal suite s f).xmssRoot suite p s := by
  funext l t
  unfold SigningMaterial.xmssRoot
  rw [pinned_wotsPk suite p s f pin hcut]

private theorem pinned_forsRoot (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) :
    let v := SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin (pin.digest suite s f)
    v.forsRoot suite p s = (SigningMaterial.ideal suite s f).forsRoot suite p s := by
  intro v
  have leaves : v.forsLeaf = (SigningMaterial.ideal suite s f).forsLeaf :=
    funext fun t => funext fun k => funext fun j => funext (pinned_fors_leaf suite s f pin t k j)
  funext t k
  unfold SigningMaterial.forsRoot
  rw [leaves]

/-- Address and digest inputs for a layer are determined before any WOTS value is disclosed. -/
def signingPosition (p : PqHashParams) (leaf i : Nat) := leaf / 2 ^ (i * p.subtreeHeight)

private theorem signingPosition_next (p : PqHashParams) (leaf i : Nat) :
    signingPosition p leaf (i+1) = signingPosition p leaf i / 2 ^ p.subtreeHeight := by
  rw [signingPosition, signingPosition, Nat.succ_mul, Nat.pow_add, Nat.div_div_eq_div_mul]

def signingLayerMsg (p : PqHashParams) (root : UInt32 → UInt64 → Spec.Bytes)
    (initial : Spec.Bytes) (leaf i : Nat) :=
  if i = 0 then initial else root (UInt32.ofNat (i-1)) (UInt64.ofNat (signingPosition p leaf i))

def signingLayerGrind (suite : TweakableHashSuite) (p : PqHashParams) (pk : PqPublicKey)
    (rand : Spec.Bytes) (root : UInt32 → UInt64 → Spec.Bytes) (initial : Spec.Bytes) (leaf fuel i : Nat) :=
  let pos := signingPosition p leaf i
  prodGrind suite p rand pk.pkSeed pk.pkRoot (signingLayerMsg p root initial leaf i) i
    (UInt64.ofNat (pos / 2 ^ p.subtreeHeight)) (UInt32.ofNat (pos % 2 ^ p.subtreeHeight)) fuel

private def collectLayers (one : Nat → Option LayerXmssSig) : Nat → Nat → Option (List LayerXmssSig)
  | _, 0 => some []
  | i, n+1 => do
    let layer ← one i
    let rest ← collectLayers one (i+1) n
    return layer :: rest

private def renderLayer (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (leaf i ctr : Nat) (digits : List Nat) : LayerXmssSig :=
  let pos := signingPosition p leaf i
  let l := UInt32.ofNat i
  let t := UInt64.ofNat (pos / 2 ^ p.subtreeHeight)
  let k := pos % 2 ^ p.subtreeHeight
  ⟨ctr, (List.range p.ell1).map (fun r => v.wots l t k r (digits.getD r 0)),
   buildMerkleAuthPathKp suite s l t .tree 0 (v.wotsPk suite p s l t) p.subtreeHeight 0 0 k⟩

private def renderAt (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (leaf : Nat) (counters : Nat → Option (Nat × List Nat × Spec.Bytes)) (i : Nat) :=
  (counters i).map fun (ctr, digits, _) => renderLayer v suite p s leaf i ctr digits

private theorem prodGrind_overlay (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (rand root msg : Spec.Bytes) (i : Nat) (t : UInt64) (k : UInt32)
    (fuel : Nat) : prodGrind (secOverlaySuite suite s f) p rand s root msg i t k fuel =
      prodGrind suite p rand s root msg i t k fuel := by
  simp only [prodGrind.public_eqs]
  split
  · generalize 0 = ctr
    induction fuel generalizing ctr with
    | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
    | succ n ih => rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ,
        thHashLeafMsg_eq, thHashLeafMsg_eq, secOverlaySuite_thCall_cons2, ih]
  · generalize 0 = ctr
    induction fuel generalizing ctr with
    | zero => rw [grindTswInternalCounterAux_zero, grindTswInternalCounterAux_zero]
    | succ n ih => rw [grindTswInternalCounterAux_succ, grindTswInternalCounterAux_succ,
        thHashInternalNode_eq, thHashInternalNode_eq, secOverlaySuite_thCall_cons2, ih]

private theorem ideal_layers (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pkRoot rand initial : Spec.Bytes) (leaf fuel : Nat) :
    let v := SigningMaterial.ideal suite s f
    let root := v.xmssRoot suite p s
    let counters := signingLayerGrind suite p ⟨s, pkRoot⟩ rand root initial leaf fuel
    ∀ rem i, signProductionHypertreeLayers (secOverlaySuite suite s f) p ⟨[], [], s⟩ pkRoot rand fuel
      i (signingPosition p leaf i) (signingLayerMsg p root initial leaf i) rem =
      collectLayers (renderAt v suite p s leaf counters) i rem := by
  intro v root counters rem
  induction rem with
  | zero => intro i; rw [signProductionHypertreeLayers_zero, collectLayers]
  | succ n ih =>
    intro i
    let ov := secOverlaySuite suite s f
    let pos := signingPosition p leaf i
    let t := UInt64.ofNat (pos / 2^p.subtreeHeight)
    let k := pos % 2^p.subtreeHeight
    let M := signingLayerMsg p root initial leaf i
    rw [signProductionHypertreeLayers_succ, collectLayers]
    simp only [renderAt]
    have gr : prodGrind ov p rand s pkRoot M i t (UInt32.ofNat k) fuel = counters i :=
      prodGrind_overlay suite p s f rand pkRoot M i t (UInt32.ofNat k) fuel
    rw [prodGrind.public_eqs] at gr
    rw [gr]
    cases g : counters i with
    | none => rfl
    | some triple =>
      obtain ⟨ctr, digits, hm⟩ := triple
      have msg : computeXmssSubtreeRoot ov p ⟨[], [], s⟩ (UInt32.ofNat i) t =
          signingLayerMsg p root initial leaf (i+1) := by
        simp only [signingLayerMsg, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
          signingPosition_next, root, v, ideal_material_xmssRoot, ov, t, pos]
      rw [msg, ← signingPosition_next, ih]
      cases rest : collectLayers (renderAt v suite p s leaf counters) (i+1) n with
      | none => rfl
      | some tail =>
        apply congrArg (fun x => some (x :: tail))
        unfold renderLayer
        dsimp only
        simp only [signingPosition_next]
        congr 1
        exact secOverlaySuite_real_authPathKp suite s f _ _ _ _ _ _
          (ideal_material_wotsPk suite p s f _ _) _ _ _ _

private abbrev GrindTable := Nat → Option (Nat × List Nat × Spec.Bytes)

private def treeOf (p : PqHashParams) (pos : Nat) := UInt64.ofNat (pos / 2^p.subtreeHeight)
private def kpOf (p : PqHashParams) (pos : Nat) := pos % 2^p.subtreeHeight

private abbrev AllowedOpen (p : PqHashParams) (pin : SigningPin) (leaf : Nat) (idxs : List Nat) :=
  p.statefulJorts = true ∨ ∀ j : Fin p.forsTrees,
    forsPrfCell (treeOf p leaf) (kpOf p leaf) j (idxs.getD j 0) ≠ pin.cell

private abbrev AllowedWots (p : PqHashParams) (pin : SigningPin) (leaf : Nat) (counters : GrindTable) :=
  ∀ (i : Fin p.numLayers) (r : Fin p.ell1),
    let pos := signingPosition p leaf i
    wotsPrfCell (UInt32.ofNat i) (treeOf p pos) (kpOf p pos) r = pin.cell →
      pin.cut ≤ (((counters i).map (fun v => v.2.1)).getD []).getD r 0

private def bottomMsg (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s mu : Spec.Bytes) (leaf : Nat) :=
  if p.statefulJorts then mu else v.forsRoot suite p s (treeOf p leaf) (kpOf p leaf)

private def materialCore (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (pk : PqPublicKey) (q : ProdSigningQuery) (rand mu : Spec.Bytes) (leaf : Nat) (idxs : List Nat)
    (pin : Option SigningPin) : Option PqHashSig :=
  let s := pk.pkSeed
  let counters := signingLayerGrind suite p pk rand (v.xmssRoot suite p s) (bottomMsg v suite p s mu leaf)
    leaf q.grindLimit
  let allowed := match pin with
    | none => true
    | some target => decide (AllowedOpen p target leaf idxs ∧ AllowedWots p target leaf counters)
  if allowed then do
    let layers ← collectLayers (renderAt v suite p s leaf counters) 0 p.numLayers
    let ops := if p.statefulJorts then [] else v.openings suite p s (treeOf p leaf) (kpOf p leaf) idxs
    let sig : PqHashSig := ⟨rand, 0, leaf, ops, layers⟩
    if verifyProductionPqHashSig suite p pk q.message sig then some sig else none
  else none

private def signLocation (suite : TweakableHashSuite) (p : PqHashParams) (pk : PqPublicKey)
    (q : ProdSigningQuery) (rand mu : Spec.Bytes) : Option (Nat × List Nat) :=
  if p.statefulJorts then
    if p.productionLeafIdxInRange q.epoch then some (q.epoch, []) else none
  else deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu

def materialSignQuery (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (msg : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery) (pin : Option SigningPin) :
    Option PqHashSig :=
  let pk := v.publicKey suite p s
  let mu := thPreHash suite s pk.pkRoot q.message
  let rand := msg (encodePrfMsg65 q.randomness mu)
  if p.productionWellFormed then do
    let (leaf, idxs) ← signLocation suite p pk q rand mu
    materialCore v suite p pk q rand mu leaf idxs pin
  else none

private theorem overlay_inputs (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (rand seed root mu : Spec.Bytes) :
    deriveProductionStatelessInputs (secOverlaySuite suite s f) p rand seed root mu =
      deriveProductionStatelessInputs suite p rand seed root mu := by
  have blocks : ∀ i n, thXofMsgBlocks (secOverlaySuite suite s f) rand seed root mu i n =
      thXofMsgBlocks suite rand seed root mu i n := by
    intro i n; induction n generalizing i with
    | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
    | succ n ih => rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ, secOverlaySuite_thCall_cons2, ih]
  simp only [deriveProductionStatelessInputs_eq, thXofMsg_eq, blocks]

private theorem ideal_material_core (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (root : Spec.Bytes) (q : ProdSigningQuery) (rand mu : Spec.Bytes)
    (leaf : Nat) (idxs : List Nat) :
    let ov := secOverlaySuite suite s f
    let pk : PqPublicKey := ⟨s, root⟩
    signProductionHypertreeCore ov p ⟨[], [], s⟩ pk q.message mu rand leaf
      (if p.statefulJorts then none else some idxs) q.grindLimit =
      materialCore (SigningMaterial.ideal suite s f) suite p pk q rand mu leaf idxs none := by
  intro ov pk
  let v := SigningMaterial.ideal suite s f
  let cur := bottomMsg v suite p s mu leaf
  let counters := signingLayerGrind suite p pk rand (v.xmssRoot suite p s) cur leaf q.grindLimit
  have layers : signProductionHypertreeLayers ov p ⟨[], [], s⟩ root rand q.grindLimit 0 leaf cur p.numLayers =
      collectLayers (renderAt v suite p s leaf counters) 0 p.numLayers := by
    simpa only [signingPosition, Nat.zero_mul, Nat.pow_zero, Nat.div_one, signingLayerMsg,
      ↓reduceIte] using ideal_layers suite p s f root rand cur leaf q.grindLimit p.numLayers 0
  rw [signProductionHypertreeCore_def, materialCore]
  by_cases mode : p.statefulJorts = true <;>
    simp only [mode, Bool.false_eq_true, ↓reduceIte, ov, ideal_material_openings, ideal_material_forsRoot, pk]
  all_goals
    simp only [cur, bottomMsg, mode, Bool.false_eq_true, ↓reduceIte, treeOf, kpOf, ov, v] at layers
    rw [layers]
    change (match collectLayers _ _ _ with | none => none | some ls => _) = _
    cases hl : collectLayers (renderAt v suite p s leaf counters) 0 p.numLayers with
    | none => rfl
    | some ls => simp only [secOverlaySuite_verify_eq]; rfl

theorem ideal_material_signQuery (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f msg : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery) :
    signQueryIdealPrf suite p s msg f q = materialSignQuery (SigningMaterial.ideal suite s f) suite p s msg q none := by
  let ov := secOverlaySuite suite s f
  let sk : PqSecretKey := ⟨[], [], s⟩
  let pk := derivePublicKey ov p sk
  let mu := thPreHash suite s pk.pkRoot q.message
  let rand := msg (encodePrfMsg65 q.randomness mu)
  have pkEq : (SigningMaterial.ideal suite s f).publicKey suite p s = pk := by
    rw [← ideal_material_publicKey, derivePublicKeyIdealPrf.public_eqs]
  have mh : thPreHash ov pk.pkSeed pk.pkRoot q.message = mu := by
    simp only [ov, mu, thPreHash_eq, secOverlaySuite_thCall_cons2]; rfl
  have se : pk.pkSeed = s := rfl
  simp only [signQueryIdealPrf.public_eqs, signQueryWithRandFn.public_eqs, signCoreWithRand.public_eqs,
    materialSignQuery, pkEq, signLocation]
  have mh' : thPreHash (secOverlaySuite suite s f)
      (derivePublicKey (secOverlaySuite suite s f) p ⟨[], [], s⟩).pkSeed
      (derivePublicKey (secOverlaySuite suite s f) p ⟨[], [], s⟩).pkRoot q.message = mu := mh
  simp only [mh', overlay_inputs]
  cases wf : p.productionWellFormed <;> cases st : p.statefulJorts <;> simp <;> try rfl
  · change Option.rec _ _ (deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu) =
      (deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu).bind _
    cases hi : deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu with
    | none => rfl
    | some li =>
      obtain ⟨l, js⟩ := li
      simpa only [Option.bind, st, Bool.false_eq_true, ↓reduceIte, pk, sk, ov, derivePublicKey, rand, mu] using ideal_material_core suite p s f pk.pkRoot q rand mu l js
  · cases ok : p.productionLeafIdxInRange q.epoch <;> simp <;> try rfl
    simpa only [st, ↓reduceIte, pk, sk, ov, derivePublicKey, rand, mu] using ideal_material_core suite p s f pk.pkRoot q rand mu q.epoch []

private theorem collectLayers_congr {a b : Nat → Option LayerXmssSig} :
    ∀ n i, (∀ k, i ≤ k → k < i+n → a k = b k) → collectLayers a i n = collectLayers b i n := by
  intro n; induction n with
  | zero => intro i _; rfl
  | succ n ih =>
    intro i h
    rw [collectLayers, collectLayers, h i (Nat.le_refl _) (by omega), ih (i+1) (fun k lo hi => h k (by omega) (by omega))]

private abbrev pinnedView (suite : TweakableHashSuite) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (pin : SigningPin) := SigningMaterial.pinned suite s (puncturePrf (s ++ encodeAdrs pin.cell) f) pin
      (pin.digest suite s f)

private theorem pinned_openings (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) (leaf : Nat) (idxs : List Nat)
    (allowed : AllowedOpen p pin leaf idxs) (st : p.statefulJorts = false) :
    let v := pinnedView suite s f pin
    v.openings suite p s (treeOf p leaf) (kpOf p leaf) idxs =
      (SigningMaterial.ideal suite s f).openings suite p s (treeOf p leaf) (kpOf p leaf) idxs := by
  intro v
  rcases allowed with bad | all
  · simp [st] at bad
  · unfold SigningMaterial.openings
    apply List.map_congr_left
    intro j hj
    let u := idxs.getD j 0
    dsimp only [v, pinnedView]
    rw [pinned_fors_secret suite s f pin _ _ j u (all ⟨j, List.mem_range.mp hj⟩),
      funext (pinned_fors_leaf suite s f pin (treeOf p leaf) (kpOf p leaf) j)]

private theorem pinned_layers (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) (cut : pin.cut ≤ p.w-1)
    (leaf : Nat) (counters : GrindTable) (allowed : AllowedWots p pin leaf counters) :
    collectLayers (renderAt (pinnedView suite s f pin) suite p s leaf counters) 0 p.numLayers =
      collectLayers (renderAt (SigningMaterial.ideal suite s f) suite p s leaf counters) 0 p.numLayers := by
  apply collectLayers_congr
  intro i _ hi
  simp only [Nat.zero_add] at hi
  unfold renderAt
  cases g : counters i with
  | none => rfl
  | some tuple =>
    obtain ⟨ctr, digits, hm⟩ := tuple
    simp only [Option.map_some]
    unfold renderLayer
    simp only [pinned_wotsPk suite p s f pin cut]
    congr 2
    apply List.map_congr_left
    intro r hr
    apply pinned_wots_node
    simpa only [g, Option.map_some, Option.getD_some, treeOf, kpOf] using allowed ⟨i, hi⟩ ⟨r, List.mem_range.mp hr⟩

private def planGrind (v : SigningMaterial) (suite : TweakableHashSuite) (p : PqHashParams)
    (pk : PqPublicKey) (q : ProdSigningQuery) (rand mu : Spec.Bytes) (leaf : Nat) :=
  signingLayerGrind suite p pk rand (v.xmssRoot suite p pk.pkSeed) (bottomMsg v suite p pk.pkSeed mu leaf)
    leaf q.grindLimit

private theorem pinned_core_eq (suite : TweakableHashSuite) (p : PqHashParams) (s root : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (pin : SigningPin) (cut : pin.cut ≤ p.w-1)
    (q : ProdSigningQuery) (rand mu : Spec.Bytes) (leaf : Nat) (idxs : List Nat) :
    let pk : PqPublicKey := ⟨s, root⟩
    let v := SigningMaterial.ideal suite s f
    let counters := planGrind v suite p pk q rand mu leaf
    materialCore (pinnedView suite s f pin) suite p pk q rand mu leaf idxs (some pin) =
      if AllowedOpen p pin leaf idxs ∧ AllowedWots p pin leaf counters then
        materialCore v suite p pk q rand mu leaf idxs none else none := by
  intro pk v counters
  have gr : planGrind (pinnedView suite s f pin) suite p pk q rand mu leaf = counters := by
    simp only [counters, planGrind, bottomMsg, pk, pinned_forsRoot suite p s f pin, pinned_xmssRoot suite p s f pin cut, v]
  unfold planGrind at gr
  simp only [materialCore, gr, decide_eq_true_eq, ↓reduceIte]
  split
  · rename_i h
    rw [pinned_layers suite p s f pin cut leaf counters h.2]
    have ops : (if p.statefulJorts then [] else (pinnedView suite s f pin).openings suite p s (treeOf p leaf) (kpOf p leaf) idxs) =
        (if p.statefulJorts then [] else v.openings suite p s (treeOf p leaf) (kpOf p leaf) idxs) := by
      by_cases st : p.statefulJorts = true
      · simp [st]
      · have no := Bool.eq_false_iff.mpr st
        simpa only [no, Bool.false_eq_true, ↓reduceIte] using pinned_openings suite p s f pin leaf idxs h.1 no
    rw [ops]
    rfl
  · rfl

#verify_constructive collectLayers_congr pinned_openings pinned_layers pinned_core_eq

private theorem collectLayers_get {one : Nat → Option LayerXmssSig} :
    ∀ n i ls, collectLayers one i n = some ls → ∀ k, k < n →
      one (i+k) = some (ls.getD k ⟨0, [], []⟩) := by
  intro n; induction n with
  | zero => intro i ls h k hk; omega
  | succ n ih =>
    intro i ls h k hk
    rw [collectLayers] at h
    cases g : one i with
    | none => simp [g] at h
    | some l =>
      cases hTail : collectLayers one (i+1) n with
      | none => simp [g, hTail] at h
      | some tail =>
        simp [g, hTail] at h
        subst ls
        cases k with
        | zero => simpa using g
        | succ k =>
          simpa only [List.getD_cons_succ, Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1 k] using
            ih (i+1) tail hTail k (by omega)

private theorem material_core_success (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (q : ProdSigningQuery) (rand : Spec.Bytes) (leaf : Nat) (idxs : List Nat)
    (sig : PqHashSig) :
    let v := SigningMaterial.ideal suite s f
    let pk := v.publicKey suite p s
    let mu := thPreHash suite s pk.pkRoot q.message
    let counters := planGrind v suite p pk q rand mu leaf
    materialCore v suite p pk q rand mu leaf idxs none = some sig →
    sig.leafGlobalIdx = leaf ∧ sig.rRand = rand ∧ ∀ i, i < p.numLayers →
      ((counters i).map (fun x => x.2.1)).getD [] =
        prodLogLayerDigits (secOverlaySuite suite s f) p ⟨[], [], s⟩ (q.message, sig) i := by
  intro v pk mu counters h
  let one := renderAt v suite p s leaf counters
  change (do
    let ls ← collectLayers one 0 p.numLayers
    let ops := if p.statefulJorts then [] else v.openings suite p s (treeOf p leaf) (kpOf p leaf) idxs
    let sign : PqHashSig := ⟨rand, 0, leaf, ops, ls⟩
    if verifyProductionPqHashSig suite p pk q.message sign then some sign else none) = some sig at h
  cases hs : collectLayers one 0 p.numLayers with
  | none => simp [hs] at h
  | some ls =>
    let ops := if p.statefulJorts then [] else v.openings suite p s (treeOf p leaf) (kpOf p leaf) idxs
    let built : PqHashSig := ⟨rand, 0, leaf, ops, ls⟩
    rw [hs] at h
    change (if verifyProductionPqHashSig suite p pk q.message built then some built else none) = some sig at h
    split at h
    · rw [← Option.some.inj h]
      dsimp only [built]
      refine ⟨rfl, rfl, fun i hi => ?_⟩
      have layer := collectLayers_get _ _ _ hs i hi
      simp only [Nat.zero_add, one, renderAt] at layer
      cases hg : counters i with
      | none => simp [hg] at layer
      | some triple =>
        obtain ⟨ctr, digits, hm⟩ := triple
        simp only [hg, Option.map_some, Option.some.injEq] at layer
        have ctrEq := congrArg LayerXmssSig.tswCtr layer
        dsimp only [renderLayer] at ctrEq
        let pos := signingPosition p leaf i
        let root := v.xmssRoot suite p s
        let initial := bottomMsg v suite p s mu leaf
        have honest : prodGrind (secOverlaySuite suite s f) p rand s pk.pkRoot
            (signingLayerMsg p root initial leaf i) i (treeOf p pos) (UInt32.ofNat (kpOf p pos)) q.grindLimit =
            some (ctr, digits, hm) := (prodGrind_overlay suite p s f _ _ _ _ _ _ _).trans hg
        have pkEq : derivePublicKey (secOverlaySuite suite s f) p ⟨[], [], s⟩ = pk :=
          by simpa only [derivePublicKeyIdealPrf.public_eqs] using ideal_material_publicKey suite p s f
        simp only [Option.map_some, Option.getD_some, prodLogLayerDigits, prodLogLayerDigest, prodHonestLayerMsg,
          ← ctrEq, pkEq, ideal_material_xmssRoot, ideal_material_forsRoot, thPreHash_eq, secOverlaySuite_thCall_cons2]
        simpa only [signingLayerMsg, root, initial, bottomMsg, mu, v, signingPosition, treeOf, kpOf, pos,
          thPreHash_eq] using (prodGrind_sound honest).2.1
    · contradiction

#verify_constructive collectLayers_get material_core_success

inductive SigningSlot (p : PqHashParams) where
  | fors (leaf : Fin (2^(p.numLayers * p.subtreeHeight))) (j : Fin p.forsTrees) (u : Fin (2^p.forsHeight))
  | wots (i : Fin p.numLayers) (pos : Fin (2^((p.numLayers-i.val)*p.subtreeHeight)))
      (r : Fin p.ell1) (step : Fin (p.w-1))

def SigningSlot.pin {p : PqHashParams} : SigningSlot p → SigningPin
  | .fors leaf j u => .fors (treeOf p leaf) (kpOf p leaf) j u
  | .wots i pos r step => .wots (UInt32.ofNat i) (treeOf p pos) (kpOf p pos) r step

private theorem slot_cut {p : PqHashParams} (slot : SigningSlot p) : slot.pin.cut ≤ p.w-1 := by
  cases slot with
  | fors => exact Nat.zero_le _
  | wots _ _ _ step => exact step.isLt

private def slotUnrevealed (suite : TweakableHashSuite) (p : PqHashParams) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (e : Spec.Bytes × PqHashSig) : SigningSlot p → Prop
  | .fors leaf j u => (leaf.val, j.val, u.val) ∉ prodSigForsLeaves suite p (derivePublicKeyIdealPrf suite p s f) e.1 e.2
  | .wots i pos r step => signingPosition p e.2.leafGlobalIdx i = pos.val →
      step.val < (prodLogLayerDigits (secOverlaySuite suite s f) p ⟨[], [], s⟩ e i).getD r 0

private theorem u32_inj_bounded {a b : Nat} (ha : a < 2^32) (hb : b < 2^32)
    (e : UInt32.ofNat a = UInt32.ofNat b) : a = b := by
  simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using congrArg UInt32.toNat e

private theorem physicalPosition_inj (p : PqHashParams) (wf : p.productionWellFormed = true)
    {a b : Nat} (ha : a < 2^(p.numLayers*p.subtreeHeight)) (hb : b < 2^(p.numLayers*p.subtreeHeight))
    (t : treeOf p a = treeOf p b) (k : UInt32.ofNat (kpOf p a) = UInt32.ofNat (kpOf p b)) : a = b := by
  obtain ⟨_, _, _, _, _, _, hh, _, _, hTot, _⟩ := p.productionWellFormed_facts wf
  let n := 2^p.subtreeHeight
  have hn : 0 < n := Nat.two_pow_pos _
  have bound : 2^(p.numLayers*p.subtreeHeight) ≤ 2^64 := Nat.pow_le_pow_right (by decide) (by omega)
  have small : n ≤ 2^32 := Nat.pow_le_pow_right (by decide) (by omega)
  have ta := Nat.lt_of_le_of_lt (Nat.div_le_self a n) (Nat.lt_of_lt_of_le ha bound)
  have tb := Nat.lt_of_le_of_lt (Nat.div_le_self b n) (Nat.lt_of_lt_of_le hb bound)
  have et : a/n = b/n := by
    have e := congrArg UInt64.toNat t
    change (UInt64.ofNat (a/n)).toNat = (UInt64.ofNat (b/n)).toNat at e
    simpa only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt ta, Nat.mod_eq_of_lt tb] using e
  have ek := u32_inj_bounded (Nat.lt_of_lt_of_le (Nat.mod_lt a hn) small) (Nat.lt_of_lt_of_le (Nat.mod_lt b hn) small) k
  calc a = a%n + n*(a/n) := (Nat.mod_add_div ..).symm
       _ = b%n + n*(b/n) := by rw [et, ek]
       _ = b := Nat.mod_add_div ..

private theorem location_leaf_lt (suite : TweakableHashSuite) (p : PqHashParams) (pk : PqPublicKey)
    (q : ProdSigningQuery) (rand mu : Spec.Bytes) {leaf : Nat} {idxs : List Nat}
    (loc : signLocation suite p pk q rand mu = some (leaf, idxs)) :
    leaf < 2^(p.numLayers*p.subtreeHeight) := by
  unfold signLocation at loc
  split at loc
  · split at loc
    · rename_i hr
      cases loc
      rw [PqHashParams.productionLeafIdxInRange_eq, decide_eq_true_eq] at hr
      split at hr
      · rename_i h
        exact Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp h).2)))
      · exact hr
    · contradiction
  · exact (deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ loc).2.2.1

private theorem slot_permitted (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32)
    (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) (slot : SigningSlot p) (q : ProdSigningQuery)
    (rand : Spec.Bytes) (leaf : Nat) (idxs : List Nat) (sig : PqHashSig) :
    let v := SigningMaterial.ideal suite s f
    let pk := v.publicKey suite p s
    let mu := thPreHash suite s pk.pkRoot q.message
    let counters := planGrind v suite p pk q rand mu leaf
    signLocation suite p pk q rand mu = some (leaf, idxs) →
    materialCore v suite p pk q rand mu leaf idxs none = some sig →
    slotUnrevealed suite p s f (q.message, sig) slot →
    AllowedOpen p slot.pin leaf idxs ∧ AllowedWots p slot.pin leaf counters := by
  intro v pk mu counters loc core safe
  obtain ⟨elt, _, _, _, _, _, _, fh, _, _, _, _, _, layers⟩ := p.productionWellFormed_facts wf
  obtain ⟨eqLeaf, eqRand, digits⟩ := material_core_success suite p s f q rand leaf idxs sig core
  have hl := location_leaf_lt suite p pk q rand mu loc
  cases slot with
  | fors target j u =>
    refine ⟨?_, fun _ _ _ => Nat.zero_le _⟩
    by_cases st : p.statefulJorts = true
    · exact .inl st
    right
    have d : deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu = some (leaf, idxs) := by
      simpa only [signLocation, st, Bool.false_eq_true, ↓reduceIte] using loc
    obtain ⟨_, _, _, len, vals⟩ := deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ d
    have js : prodSigForsIdxs suite p (derivePublicKeyIdealPrf suite p s f) q.message sig = idxs := by
      rw [prodSigForsIdxs, ideal_material_publicKey, eqRand]
      change (match deriveProductionStatelessInputs suite p rand pk.pkSeed pk.pkRoot mu with
        | some (_, l) => l | none => []) = idxs
      rw [d]
    intro a he
    simp only [SigningSlot.pin, SigningPin.cell, forsPrfCell, HashAdrs.mk.injEq, true_and] at he
    have same := physicalPosition_inj p wf hl target.isLt he.1 he.2.1
    have eqj := u32_inj_bounded (Nat.lt_of_lt_of_le a.isLt trees) (Nat.lt_of_lt_of_le j.isLt trees) he.2.2.1
    have small : 2^p.forsHeight ≤ 2^32 := Nat.pow_le_pow_right (by decide) (by omega)
    have hu : idxs.getD a 0 < 2^p.forsHeight := by
      have ha : a.val < idxs.length := by rw [len]; exact a.isLt
      rw [list_getD_eq_getElem _ _ ha]
      exact vals _ (List.getElem_mem ha)
    have equ := u32_inj_bounded (Nat.lt_of_lt_of_le hu small) (Nat.lt_of_lt_of_le u.isLt small) he.2.2.2
    apply safe
    unfold prodSigForsLeaves
    exact List.mem_map.mpr ⟨a.val, List.mem_range.mpr a.isLt, by rw [eqLeaf, same, js, equ, eqj]⟩
  | wots i pos r step =>
    constructor
    · exact .inr fun j => by simp [SigningSlot.pin, SigningPin.cell, forsPrfCell, wotsPrfCell.public_eqs]
    intro l c
    dsimp only
    intro eq
    simp only [SigningSlot.pin, SigningPin.cell, wotsPrfCell.public_eqs, HashAdrs.mk.injEq, and_true, true_and] at eq
    have ei := u32_inj_bounded (Nat.lt_of_lt_of_le l.isLt (by omega)) (Nat.lt_of_lt_of_le i.isLt (by omega)) eq.1
    have ell : p.ell1 ≤ 256 := by rcases p.productionWellFormed_w_ell1 wf with h|h|h|h <;> omega
    have ec := u32_inj_bounded (Nat.lt_of_lt_of_le c.isLt (by omega)) (Nat.lt_of_lt_of_le r.isLt (by omega)) eq.2.2.2
    have hp := Nat.lt_of_lt_of_le pos.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right _ (Nat.sub_le _ _)))
    have ep := physicalPosition_inj p wf (Nat.lt_of_le_of_lt (Nat.div_le_self leaf _) hl) hp eq.2.1 eq.2.2.1
    change step.val+1 ≤ _
    rw [digits l l.isLt, ec, ei]
    apply safe
    rw [eqLeaf]
    exact (congrArg (signingPosition p leaf) ei.symm).trans ep

private theorem pinned_query_eq (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32)
    (s : Spec.Bytes) (f msg : Spec.Bytes → Spec.Bytes) (slot : SigningSlot p) (q : ProdSigningQuery)
    (safe : ∀ sig, signQueryIdealPrf suite p s msg f q = some sig → slotUnrevealed suite p s f (q.message, sig) slot) :
    signQueryIdealPrf suite p s msg f q = materialSignQuery (pinnedView suite s f slot.pin) suite p s msg q (some slot.pin) := by
  rw [ideal_material_signQuery] at safe ⊢
  let v := SigningMaterial.ideal suite s f
  let pv := pinnedView suite s f slot.pin
  let pk := v.publicKey suite p s
  have key : pv.publicKey suite p s = pk := by
    simp only [pv, pk, SigningMaterial.publicKey, pinned_xmssRoot suite p s f _ (slot_cut slot), v]
  let mu := thPreHash suite s pk.pkRoot q.message
  let rand := msg (encodePrfMsg65 q.randomness mu)
  dsimp only [pv] at key
  simp only [materialSignQuery, wf, ↓reduceIte, key] at safe ⊢
  change (signLocation suite p pk q rand mu).bind _ = (signLocation suite p pk q rand mu).bind _
  cases loc : signLocation suite p pk q rand mu with
  | none => rfl
  | some pair =>
    obtain ⟨leaf, idxs⟩ := pair
    change materialCore v suite p pk q rand mu leaf idxs none = materialCore pv suite p pk q rand mu leaf idxs (some slot.pin)
    have h := pinned_core_eq suite p s pk.pkRoot f slot.pin (slot_cut slot) q rand mu leaf idxs
    change materialCore pv suite p pk q rand mu leaf idxs (some slot.pin) =
      (if AllowedOpen p slot.pin leaf idxs ∧ AllowedWots p slot.pin leaf (planGrind v suite p pk q rand mu leaf)
       then materialCore v suite p pk q rand mu leaf idxs none else none) at h
    rw [h]
    split
    · rfl
    · rename_i denied
      cases core : materialCore v suite p pk q rand mu leaf idxs none with
      | none => rfl
      | some sig =>
        apply False.elim
        apply denied
        apply slot_permitted suite p wf trees s f slot q rand leaf idxs sig loc core
        apply safe
        change (signLocation suite p pk q rand mu).bind _ = some sig
        rw [loc]; exact core

private theorem mem_signLog_of_reply {o : ProdSigningQuery → Option PqHashSig} {q : ProdSigningQuery}
    {sig : PqHashSig} (reply : o q = some sig) : ∀ qs, q ∈ qs → (q.message, sig) ∈ signLogFromOracle o qs := by
  intro qs; induction qs with
  | nil => simp
  | cons a rest ih =>
    intro h; rw [signLogFromOracle_cons]
    rcases List.mem_cons.mp h with h|h
    · subst a; simp [reply]
    · exact List.mem_append_right _ (ih h)

def slotRecover {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (msg : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign) (slot : SigningSlot p)
    (off : Spec.Bytes → Spec.Bytes) (s y : Spec.Bytes) : Spec.Bytes :=
  let view := SigningMaterial.pinned suite s off slot.pin y
  let tree := (canonicalizeAdvOptRand adv).run (view.publicKey suite p s)
  let output := (evalLatchedAdaptiveTree latchOn suite.rawHash
    (fun q => materialSignQuery view suite p s msg q (some slot.pin)) tree 0).1.2
  match slot with
  | .fors _ j _ => (output.forsOpenings.getD j ⟨[], []⟩).secretVal
  | .wots i _ r _ => (output.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r []

private theorem slotRecover_eq {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32)
    (msg f : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign) (slot : SigningSlot p) (s : Spec.Bytes) :
    let pk := derivePublicKeyIdealPrf suite p s f
    let o := signQueryIdealPrf suite p s msg f
    let run := evalLatchedAdaptiveTree latchOn suite.rawHash o ((canonicalizeAdvOptRand adv).run pk) 0
    let log := signLogFromOracle o run.2
    (∀ e ∈ log, slotUnrevealed suite p s f e slot) →
    slotRecover latchOn suite p msg adv slot (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s (slot.pin.digest suite s f) =
      match slot with
      | .fors _ j _ => (run.1.2.forsOpenings.getD j ⟨[], []⟩).secretVal
      | .wots i _ r _ => (run.1.2.layerSigs.getD i ⟨0, [], []⟩).wotsChains.getD r [] := by
  intro pk o run log safe
  let pv := pinnedView suite s f slot.pin
  have key : pv.publicKey suite p s = pk := by
    simp only [pk, ideal_material_publicKey, pv, SigningMaterial.publicKey,
      pinned_xmssRoot suite p s f _ (slot_cut slot)]
  have eq := evalLatchedAdaptiveTree_congr_on_log latchOn suite.rawHash o
    (fun q => materialSignQuery pv suite p s msg q (some slot.pin)) ((canonicalizeAdvOptRand adv).run pk) 0
    (fun q hq => pinned_query_eq suite p wf trees s f msg slot q
      (fun sig reply => safe (q.message,sig) (mem_signLog_of_reply reply _ hq)))
  dsimp only [pv, pinnedView] at key eq
  simp only [slotRecover, key, ← eq, run]

#verify_constructive u32_inj_bounded physicalPosition_inj slot_cut location_leaf_lt slot_permitted pinned_query_eq
  mem_signLog_of_reply slotRecover_eq

def SigningSlot.tweak {p : PqHashParams} : SigningSlot p → Spec.Bytes
  | .fors leaf j u => encodeChainFTweak (forsLeafHashAdrs (treeOf p leaf) (kpOf p leaf) j u)
  | .wots i pos r step => encodeChainFTweak ⟨UInt32.ofNat i, treeOf p pos, .wotsHash,
      UInt32.ofNat (kpOf p pos), UInt32.ofNat r, UInt32.ofNat step⟩

def slotWin {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (msg : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign)
    (slot : SigningSlot p) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes) : Bool :=
  let y := slot.pin.digest suite s f
  decide (suiteTweakHash suite s slot.tweak (slotRecover latchOn suite p msg adv slot
    (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)

private theorem position_lt {p : PqHashParams} {leaf i : Nat} (hi : i < p.numLayers)
    (hl : leaf < 2^(p.numLayers*p.subtreeHeight)) : signingPosition p leaf i < 2^((p.numLayers-i)*p.subtreeHeight) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  rwa [← Nat.pow_add, ← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hi)]

private theorem slotWin_of_eq {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (msg : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign)
    (slot : SigningSlot p) (s : Spec.Bytes) (f : Spec.Bytes → Spec.Bytes)
    (h : suiteTweakHash suite s slot.tweak (slotRecover latchOn suite p msg adv slot
      (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s (slot.pin.digest suite s f)) =
      slot.pin.digest suite s f) :
    slotWin latchOn suite p msg adv slot s f = true :=
  decide_eq_true h

private theorem fors_pre_eq (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (t : UInt64) (k j u : Nat)
    (v1 v2 tw y : Spec.Bytes)
    (hV : v1 = v2) (hTw : tw = encodeChainFTweak (forsLeafHashAdrs t k j u))
    (hY : forsIndexedLeafFn (secOverlaySuite suite s f) ⟨[], [], s⟩ t k j u = y)
    (inv : forsIndexedLeafHash suite s t k j u v2 =
      forsIndexedLeafFn (secOverlaySuite suite s f) ⟨[], [], s⟩ t k j u) :
    suiteTweakHash suite s tw v1 = y := by
  cases hV; cases hTw; cases hY
  rw [suiteTweakHash_chainF, ← forsIndexedLeafHash_eq_chainF_adrs]
  exact inv

private theorem wots_pre_eq (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (k r step : Nat)
    (v1 v2 tw y : Spec.Bytes)
    (hV : v1 = v2)
    (hTw : tw = encodeChainFTweak ⟨l, t, .wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat step⟩)
    (hY : cellWotsNode suite s f (wotsPrfCell l t k r) (step + 1) = y)
    (inv : thChainF suite s ⟨l, t, .wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat step⟩ v2 =
      honestChainNode (secOverlaySuite suite s f) ⟨[], [], s⟩ l t k r (step + 1)) :
    suiteTweakHash suite s tw v1 = y := by
  cases hV; cases hTw; cases hY
  rw [suiteTweakHash_chainF, inv, ideal_wots_cell]

private theorem pre_selects_slot {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32) (s : Spec.Bytes)
    (msg f : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign)
    (win : (idealPrfBreakEvents latchOn suite p s msg f adv).2 = true) :
    ∃ slot, (match slot with | .fors .. => p.statefulJorts = false | .wots .. => True) ∧
      slotWin latchOn suite p msg adv slot s f = true := by
  dsimp only [idealPrfBreakEvents] at win
  have pre := of_decide_eq_true win
  let pk0 := derivePublicKeyIdealPrf suite p s f
  let signFn := signQueryIdealPrf suite p s msg f
  let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn
    ((canonicalizeAdvOptRand adv).run pk0) 0
  let log := signLogFromOracle signFn run.2
  let sig := run.1.2
  let sk : PqSecretKey := ⟨[], [], s⟩
  let ov := secOverlaySuite suite s f
  cases pre with
  | fors j hj st hl hu no inv =>
    let u := (prodSigForsIdxs suite p (derivePublicKey ov p sk) run.1.1 sig).getD j 0
    let slot : SigningSlot p := .fors ⟨_, hl⟩ ⟨j, hj⟩ ⟨u, hu⟩
    refine ⟨slot, st, ?_⟩
    have safe : ∀ e ∈ log, slotUnrevealed suite p s f e slot := by
      intro e he
      unfold slotUnrevealed
      dsimp only [slot]
      rw [congrArg (fun k => prodSigForsLeaves suite p k e.1 e.2)
        (derivePublicKeyIdealPrf.public_eqs suite p s f)]
      exact no e he
    have eq := slotRecover_eq latchOn suite p wf trees msg f adv slot s safe
    exact slotWin_of_eq latchOn suite p msg adv slot s f
      (fors_pre_eq suite s f (treeOf p sig.leafGlobalIdx) (kpOf p sig.leafGlobalIdx) j u
        _ _ slot.tweak (slot.pin.digest suite s f) eq rfl rfl inv)
  | wots i hi r hr step hstep hl inv no =>
    let pos := signingPosition p sig.leafGlobalIdx i
    let slot : SigningSlot p := .wots ⟨i,hi⟩ ⟨pos,position_lt hi hl⟩ ⟨r,hr⟩ ⟨step,hstep⟩
    refine ⟨slot, trivial, ?_⟩
    have safe : ∀ e ∈ log, slotUnrevealed suite p s f e slot := no
    have eq := slotRecover_eq latchOn suite p wf trees msg f adv slot s safe
    exact slotWin_of_eq latchOn suite p msg adv slot s f
      (wots_pre_eq suite s f (UInt32.ofNat i) (treeOf p pos) (kpOf p pos) r step
        _ _ slot.tweak (slot.pin.digest suite s f) eq rfl rfl inv)

/-- Class membership of the single PRE program and each preceding WOTS UD program. -/
@[expose] def SlotReductionClass {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (msg f : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign) (slot : SigningSlot p)
    (𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop) (𝒜Ud : Spec.Code Spec.targetIface Bool → Prop) : Prop :=
  let recover := slotRecover latchOn suite p msg adv slot
  𝒜Pre (puncturedTablePreAdv slot.pin.cell slot.tweak recover f) ∧
    match slot with
    | .fors .. => True
    | .wots i pos r step =>
      let l := UInt32.ofNat i
      let t := UInt64.ofNat (pos.val / 2^p.subtreeHeight)
      let k := pos.val % 2^p.subtreeHeight
      ∀ a b, a+1+b = step.val → 𝒜Ud (udDigestTest
        (encodeChainFTweak ⟨l,t,.wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat a⟩)
        (fun s => wotsSlotTest suite l t k r (a+1) b slot.tweak recover (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s))

theorem slotReductionClass_unrestricted {qHash qSign : Nat} (latch : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (msg f : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign)
    (slot : SigningSlot p) : SlotReductionClass latch suite p msg f adv slot (fun _ => True) (fun _ => True) := by
  cases slot <;> simp [SlotReductionClass]

#verify_constructive slotReductionClass_unrestricted

def SigningSlot.cost {p : PqHashParams} : SigningSlot p → Nat
  | .fors .. => 1
  | .wots _ _ _ step => step.val+1

private theorem add_scale_same (a b : Nat) (ε : Spec.RatBound) :
    ((Spec.RatBound.scale a ε).add (Spec.RatBound.scale b ε)).le (Spec.RatBound.scale (a+b) ε) := by
  unfold Spec.RatBound.scale Spec.RatBound.add Spec.RatBound.le
  dsimp only
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.le_refl]

private theorem wotsSlotLoss_scale (ε : Spec.RatBound) (n : Nat) : (wotsSlotLoss ε ε n).le (Spec.RatBound.scale (n+1) ε) := by
  have one : ε.le (Spec.RatBound.scale 1 ε) := by unfold Spec.RatBound.le Spec.RatBound.scale; simp
  induction n with
  | zero => exact one
  | succ n ih => exact Spec.RatBound.le_trans (Spec.RatBound.add_le_add ih one) (add_scale_same _ _ ε)

private theorem wots_slot_pin_digest (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (k r step : Nat)
    (len : (f (s ++ encodeAdrs (wotsPrfCell l t k r))).length = 32) :
    suiteTweakHash suite s
      (encodeChainFTweak ⟨l, t, .wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat step⟩)
      (wotsChainSteps suite s l t k r 0 step (f (s ++ encodeAdrs (wotsPrfCell l t k r)))) =
    SigningPin.digest suite s f (.wots l t k r step) := by
  change _ = cellWotsNode suite s f (wotsPrfCell l t k r) (step + 1)
  rw [← ideal_wots_cell, ← honestChainNode_succ, honestChainNode_eq, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty]
  change _ = thChainF (secOverlaySuite suite s f) s
    ⟨l, t, .wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat step⟩
    (wotsChainSteps (secOverlaySuite suite s f) s l t k r 0 step
      (padBytes32 (f (s ++ encodeAdrs (wotsPrfCell l t k r)))))
  rw [padBytes32_of_len32 len, chainSteps_secOverlay, suiteTweakHash_chainF]
  rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]

private theorem puncturedDigestGame_win_at {nSeed nSec : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (seed : Fin nSeed → Spec.Bytes)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (addr : HashAdrs) (test : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Bool)
    (z : Fin (nSeed * nSec)) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    let s := seed (sp.chal z)
    let f := (table (sp.advc z)).2
    let x := s ++ encodeAdrs addr
    (puncturedDigestGame hs hc seed table addr test).win z =
      test (puncturePrf x f) s (f x) := rfl

private theorem fors_digest_eq (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (t : UInt64) (k j u : Nat) :
    forsIndexedLeafFn (secOverlaySuite suite s f) ⟨[], [], s⟩ t k j u =
      SigningPin.digest suite s f (.fors t k j u) := rfl

private theorem fors_win_imp (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (t : UInt64) (k j u : Nat)
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (y : Spec.Bytes) (addr : HashAdrs) (tweak : Spec.Bytes)
    (hTw : tweak = encodeChainFTweak (forsLeafHashAdrs t k j u))
    (hz : decide (suiteTweakHash suite s tweak (recov (puncturePrf (s ++ encodeAdrs addr) f) s y) = y) = true) :
    decide (forsIndexedLeafHash suite s t k j u (recov (puncturePrf (s ++ encodeAdrs addr) f) s y) = y) = true := by
  rw [forsIndexedLeafHash_eq_chainF_adrs, ← suiteTweakHash_chainF, ← hTw]
  exact hz

private theorem fors_step_hb {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (leaf : Fin (2^(p.numLayers * p.subtreeHeight))) (j : Fin p.forsTrees) (u : Fin (2^p.forsHeight))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (cPre : ∀ c, 𝒜Pre (puncturedTablePreAdv (SigningSlot.fors (p := p) leaf j u).pin.cell
      (SigningSlot.fors (p := p) leaf j u).tweak recov (table c).2)) :
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let pair := samplePair seed table z
      let s := pair.1
      let f := pair.2.2
      let y := forsIndexedLeafFn (secOverlaySuite suite s f) ⟨[], [], s⟩ (treeOf p leaf) (kpOf p leaf) j u
      decide (forsIndexedLeafHash suite s (treeOf p leaf) (kpOf p leaf) j u
        (recov (puncturePrf (s ++ encodeAdrs ⟨0, treeOf p leaf, .forsPrf, UInt32.ofNat (kpOf p leaf), UInt32.ofNat j, UInt32.ofNat u⟩) f) s y) = y)).winProb prim :=
  hulsing_punctured_fors_leaf_pre_bound hs hc suite seed hSeed table hSec (treeOf p leaf) (kpOf p leaf) j u recov hpre cPre

private theorem gameBound_of_imp_scale1 {n : Nat} (hPos : 0 < n)
    (f1 f2 : Fin n → Bool) (prim : Spec.RatBound)
    (hb : Spec.GameBound (Spec.FinGame.mk hPos f2).winProb prim)
    (hImp : ∀ z, f1 z = true → f2 z = true) :
    Spec.GameBound (Spec.FinGame.mk hPos f1).winProb (Spec.RatBound.scale 1 prim) := by
  have one : prim.le (Spec.RatBound.scale 1 prim) := by unfold Spec.RatBound.le Spec.RatBound.scale; simp
  exact Spec.GameBound.trans
    (Spec.event_le_reduction_win (Spec.FinGame.mk hPos f1) (Spec.FinGame.mk hPos f2) hImp)
    (Spec.RatBound.le_trans hb one)

private theorem fors_step_ev {nSeed nSec : Nat}
    (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (leaf : Fin (2^(p.numLayers * p.subtreeHeight))) (j : Fin p.forsTrees) (u : Fin (2^p.forsHeight))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    let slot : SigningSlot p := .fors leaf j u
    ∀ z : Fin (nSeed * nSec),
      (let s := seed (sp.chal z)
       let f := (table (sp.advc z)).2
       let y := slot.pin.digest suite s f
       decide (suiteTweakHash suite s slot.tweak
         (recov (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)) = true →
      (let pair := samplePair seed table z
       let s0 := pair.1
       let f0 := pair.2.2
       let y0 := forsIndexedLeafFn (secOverlaySuite suite s0 f0) ⟨[], [], s0⟩ (treeOf p leaf) (kpOf p leaf) j u
       decide (forsIndexedLeafHash suite s0 (treeOf p leaf) (kpOf p leaf) j u
         (recov (puncturePrf (s0 ++ encodeAdrs ⟨0, treeOf p leaf, .forsPrf, UInt32.ofNat (kpOf p leaf), UInt32.ofNat j, UInt32.ofNat u⟩) f0) s0 y0) = y0)) = true :=
  fun z hz => fors_win_imp suite (seed ((Spec.CoinSplit.prod nSeed nSec).chal z)) (table ((Spec.CoinSplit.prod nSeed nSec).advc z)).2
    (treeOf p leaf) (kpOf p leaf) j u recov
    ((SigningSlot.fors (p := p) leaf j u).pin.digest suite (seed ((Spec.CoinSplit.prod nSeed nSec).chal z)) (table ((Spec.CoinSplit.prod nSeed nSec).advc z)).2)
    (SigningSlot.fors (p := p) leaf j u).pin.cell (SigningSlot.fors (p := p) leaf j u).tweak rfl hz

private theorem slot_fors_part {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (leaf : Fin (2^(p.numLayers * p.subtreeHeight))) (j : Fin p.forsTrees) (u : Fin (2^p.forsHeight))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (cPre : ∀ c, 𝒜Pre (puncturedTablePreAdv (SigningSlot.fors (p := p) leaf j u).pin.cell
      (SigningSlot.fors (p := p) leaf j u).tweak recov (table c).2)) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    let slot : SigningSlot p := .fors leaf j u
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let s := seed (sp.chal z)
      let f := (table (sp.advc z)).2
      let y := slot.pin.digest suite s f
      decide (suiteTweakHash suite s slot.tweak
        (recov (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)).winProb
      (Spec.RatBound.scale slot.cost prim) :=
  gameBound_of_imp_scale1 (Nat.mul_pos hs hc) _ _ prim
    (fors_step_hb hs hc suite p seed hSeed table hSec leaf j u recov hpre cPre)
    (fors_step_ev suite p seed table leaf j u recov)

private theorem gameBound_of_imp_wots {n : Nat} (hPos : 0 < n)
    (f1 f2 : Fin n → Bool) (prim : Spec.RatBound) (step : Nat)
    (hb : Spec.GameBound (Spec.FinGame.mk hPos f2).winProb (wotsSlotLoss prim prim step))
    (hImp : ∀ z, f1 z = true → f2 z = true) :
    Spec.GameBound (Spec.FinGame.mk hPos f1).winProb (Spec.RatBound.scale (step + 1) prim) :=
  Spec.GameBound.trans
    (Spec.event_le_reduction_win (Spec.FinGame.mk hPos f1) (Spec.FinGame.mk hPos f2) hImp)
    (Spec.RatBound.le_trans hb (wotsSlotLoss_scale prim step))

private theorem wots_win_imp (suite : TweakableHashSuite) (s : Spec.Bytes)
    (f : Spec.Bytes → Spec.Bytes) (l : UInt32) (t : UInt64) (k r step : Nat)
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (x0 tw0 y x1 tw1 : Spec.Bytes)
    (hX : x0 = x1) (hTw : tw1 = tw0)
    (hPt : suiteTweakHash suite s tw0 (wotsChainSteps suite s l t k r 0 step (f x0)) = y)
    (win : decide (suiteTweakHash suite s tw1 (recov (puncturePrf x1 f) s y) = y) = true) :
    wotsSlotTest suite l t k r 0 step tw0 recov (puncturePrf x0 f) s (f x0) = true := by
  cases hX; cases hTw; cases hPt; exact win

private theorem slot_wots_cUd_part {nSec : Nat} (suite : TweakableHashSuite) (p : PqHashParams)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (i : Fin p.numLayers) (pos : Fin (2^((p.numLayers-i.val)*p.subtreeHeight)))
    (r : Fin p.ell1) (step : Fin (p.w-1))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    (cUd : let l := UInt32.ofNat i; let t := UInt64.ofNat (pos.val / 2^p.subtreeHeight); let k := pos.val % 2^p.subtreeHeight
      ∀ a b, a+1+b = step.val → ∀ c, 𝒜Ud (udDigestTest
        (encodeChainFTweak ⟨l,t,.wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat a⟩)
        (fun s => wotsSlotTest suite l t k r (a+1) b (SigningSlot.wots i pos r step).tweak recov
          (puncturePrf (s ++ encodeAdrs (SigningSlot.wots i pos r step).pin.cell) (table c).2) s))) :
    let l := UInt32.ofNat i; let t := treeOf p pos; let k := kpOf p pos
    let addr : HashAdrs := ⟨l, t, .wotsPrf, UInt32.ofNat k, UInt32.ofNat r, 0⟩
    let ha := fun a => HashAdrs.mk l t .wotsHash (UInt32.ofNat k) (UInt32.ofNat r) (UInt32.ofNat a)
    ∀ a b, a+1+b = step.val → ∀ c, 𝒜Ud (udDigestTest (encodeChainFTweak (ha a))
      (fun s => wotsSlotTest suite l t k r (a+1) b (encodeChainFTweak (ha step)) recov
        (puncturePrf (s ++ encodeAdrs addr) (table c).2) s)) := by
  intro l t k addr ha a b hab c
  have hT : UInt64.ofNat (pos.val / 2^p.subtreeHeight) = t := rfl
  have hK : pos.val % 2^p.subtreeHeight = k := rfl
  have hCellW : (SigningSlot.wots i pos r step).pin.cell = addr := rfl
  have hTw : (SigningSlot.wots i pos r step).tweak = encodeChainFTweak (ha step) := rfl
  have h := cUd a b hab c
  rwa [hT, hK, hCellW, hTw] at h

private theorem wots_step_hb {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (i : Fin p.numLayers) (pos : Fin (2^((p.numLayers-i.val)*p.subtreeHeight)))
    (r : Fin p.ell1) (step : Fin (p.w-1))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 prim)
    (cPre : ∀ c, 𝒜Pre (puncturedTablePreAdv (SigningSlot.wots i pos r step).pin.cell
      (SigningSlot.wots i pos r step).tweak recov (table c).2))
    (cUd : let l := UInt32.ofNat i; let t := UInt64.ofNat (pos.val / 2^p.subtreeHeight); let k := pos.val % 2^p.subtreeHeight
      ∀ a b, a+1+b = step.val → ∀ c, 𝒜Ud (udDigestTest
        (encodeChainFTweak ⟨l,t,.wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat a⟩)
        (fun s => wotsSlotTest suite l t k r (a+1) b (SigningSlot.wots i pos r step).tweak recov
          (puncturePrf (s ++ encodeAdrs (SigningSlot.wots i pos r step).pin.cell) (table c).2) s))) :
    let l := UInt32.ofNat i; let t := treeOf p pos; let k := kpOf p pos
    let addr : HashAdrs := ⟨l, t, .wotsPrf, UInt32.ofNat k, UInt32.ofNat r, 0⟩
    let ha := fun a => HashAdrs.mk l t .wotsHash (UInt32.ofNat k) (UInt32.ofNat r) (UInt32.ofNat a)
    Spec.GameBound
      (puncturedDigestGame hs hc seed table addr
        (wotsSlotTest suite l t k r 0 step (encodeChainFTweak (ha step)) recov)).winProb
      (wotsSlotLoss prim prim step) := by
  intro l t k addr ha
  have hCellW : (SigningSlot.wots i pos r step).pin.cell = addr := rfl
  have hTw : (SigningSlot.wots i pos r step).tweak = encodeChainFTweak (ha step) := rfl
  have cPre1 : ∀ c, 𝒜Pre (puncturedTablePreAdv addr (encodeChainFTweak (ha step)) recov (table c).2) := by
    intro c; have h := cPre c; rwa [hCellW, hTw] at h
  exact hulsing_wots_slot_chain_bound hs hc suite seed hSeed table hSec l t k r step recov hpre hud cPre1
    (slot_wots_cUd_part suite p table i pos r step recov cUd)

private theorem wots_step_ev {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (i : Fin p.numLayers) (pos : Fin (2^((p.numLayers-i.val)*p.subtreeHeight)))
    (r : Fin p.ell1) (step : Fin (p.w-1))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    let slot : SigningSlot p := .wots i pos r step
    let l := UInt32.ofNat i; let t := treeOf p pos; let k := kpOf p pos
    let addr : HashAdrs := ⟨l, t, .wotsPrf, UInt32.ofNat k, UInt32.ofNat r, 0⟩
    let ha := fun a => HashAdrs.mk l t .wotsHash (UInt32.ofNat k) (UInt32.ofNat r) (UInt32.ofNat a)
    ∀ z : Fin (nSeed * nSec),
      (let s := seed (sp.chal z)
       let f := (table (sp.advc z)).2
       let y := slot.pin.digest suite s f
       decide (suiteTweakHash suite s slot.tweak
         (recov (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)) = true →
      (puncturedDigestGame hs hc seed table addr
        (wotsSlotTest suite l t k r 0 step (encodeChainFTweak (ha step)) recov)).win z = true := by
  intro sp slot l t k addr ha z win
  rw [puncturedDigestGame_win_at]
  let s := seed (sp.chal z)
  let f := (table (sp.advc z)).2
  have len : (f (s ++ encodeAdrs (wotsPrfCell l t k r))).length = 32 :=
    (((Spec.PrfSampleOk_eq ..).mp (hSec.mem (sp.advc z))).2 _).1
      (secretPrfSlot_input_length hSeed (sp.chal z) (wotsPrfCell l t k r))
  exact wots_win_imp suite s f l t k r step recov
    (s ++ encodeAdrs addr) (encodeChainFTweak (ha step)) (slot.pin.digest suite s f)
    (s ++ encodeAdrs slot.pin.cell) slot.tweak
    (congrArg (fun a => s ++ encodeAdrs a) (rfl : addr = slot.pin.cell))
    rfl (wots_slot_pin_digest suite s f l t k r step len) win

private theorem slot_wots_part {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (i : Fin p.numLayers) (pos : Fin (2^((p.numLayers-i.val)*p.subtreeHeight)))
    (r : Fin p.ell1) (step : Fin (p.w-1))
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 prim)
    (cPre : ∀ c, 𝒜Pre (puncturedTablePreAdv (SigningSlot.wots i pos r step).pin.cell
      (SigningSlot.wots i pos r step).tweak recov (table c).2))
    (cUd : let l := UInt32.ofNat i; let t := UInt64.ofNat (pos.val / 2^p.subtreeHeight); let k := pos.val % 2^p.subtreeHeight
      ∀ a b, a+1+b = step.val → ∀ c, 𝒜Ud (udDigestTest
        (encodeChainFTweak ⟨l,t,.wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat a⟩)
        (fun s => wotsSlotTest suite l t k r (a+1) b (SigningSlot.wots i pos r step).tweak recov
          (puncturePrf (s ++ encodeAdrs (SigningSlot.wots i pos r step).pin.cell) (table c).2) s))) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    let slot : SigningSlot p := .wots i pos r step
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let s := seed (sp.chal z)
      let f := (table (sp.advc z)).2
      let y := slot.pin.digest suite s f
      decide (suiteTweakHash suite s slot.tweak
        (recov (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)).winProb
      (Spec.RatBound.scale slot.cost prim) :=
  gameBound_of_imp_wots (Nat.mul_pos hs hc) _ _ prim step
    (wots_step_hb hs hc suite p seed hSeed table hSec i pos r step recov hpre hud cPre cUd)
    (wots_step_ev hs hc suite p seed hSeed table hSec i pos r step recov)

private theorem slot_bound_of_recov {nSeed nSec seedLen keyLen : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (slot : SigningSlot p)
    (recov : (Spec.Bytes → Spec.Bytes) → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop}
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 prim)
    (cPre : ∀ c, 𝒜Pre (puncturedTablePreAdv slot.pin.cell slot.tweak recov (table c).2))
    (cUd : match slot with
      | .fors .. => True
      | .wots i pos r step =>
        let l := UInt32.ofNat i
        let t := UInt64.ofNat (pos.val / 2^p.subtreeHeight)
        let k := pos.val % 2^p.subtreeHeight
        ∀ a b, a+1+b = step.val → ∀ c, 𝒜Ud (udDigestTest
          (encodeChainFTweak ⟨l,t,.wotsHash, UInt32.ofNat k, UInt32.ofNat r, UInt32.ofNat a⟩)
          (fun s => wotsSlotTest suite l t k r (a+1) b slot.tweak recov
            (puncturePrf (s ++ encodeAdrs slot.pin.cell) (table c).2) s))) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      let s := seed (sp.chal z)
      let f := (table (sp.advc z)).2
      let y := slot.pin.digest suite s f
      decide (suiteTweakHash suite s slot.tweak
        (recov (puncturePrf (s ++ encodeAdrs slot.pin.cell) f) s y) = y)).winProb
      (Spec.RatBound.scale slot.cost prim) := by
  intro sp
  cases slot with
  | fors leaf j u => exact slot_fors_part hs hc suite p seed hSeed table hSec leaf j u recov hpre cPre
  | wots i pos r step => exact slot_wots_part hs hc suite p seed hSeed table hSec i pos r step recov hpre hud cPre cUd

private theorem slot_bound {nSeed nSec seedLen keyLen qHash qSign : Nat}
    (hs : 0 < nSeed) (hc : 0 < nSec) (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (seed : Fin nSeed → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nSec → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (msg : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign) (slot : SigningSlot p)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop} {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 prim)
    (classes : ∀ c, SlotReductionClass latchOn suite p msg (table c).2 adv slot 𝒜Pre 𝒜Ud) :
    let sp := Spec.CoinSplit.prod nSeed nSec
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z => slotWin latchOn suite p msg adv slot
      (seed (sp.chal z)) (table (sp.advc z)).2).winProb (Spec.RatBound.scale slot.cost prim) := by
  intro sp
  refine slot_bound_of_recov hs hc suite p seed hSeed table hSec slot
    (slotRecover latchOn suite p msg adv slot) hpre hud (fun c => (classes c).1) ?_
  cases slot with
  | fors => exact trivial
  | wots => exact fun a b ab c => (classes c).2 a b ab

#verify_constructive position_lt pre_selects_slot add_scale_same wotsSlotLoss_scale slot_bound

/-- Number of XMSS key pairs over all layers, including every tree and every leaf. -/
@[expose] def hypertreeKeyPairs (subtreeHeight : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => 2 ^ ((d + 1) * subtreeHeight) + hypertreeKeyPairs subtreeHeight d

/-- Count one PRE per FORS secret and per WOTS step. A step with index s also costs s
    UD hops, giving w(w-1)/2 primitive calls per chain. -/
@[expose] def globalPreUdCalls (p : PqHashParams) : Nat :=
  let fors := if p.statefulJorts then 0 else 2 ^ (p.numLayers * p.subtreeHeight) * p.forsTrees * 2 ^ p.forsHeight
  fors + hypertreeKeyPairs p.subtreeHeight p.numLayers * p.ell1 * (p.w * (p.w - 1) / 2)

/-- Arithmetic envelope with a common primitive cap. Reserve two PRFs, one open-seed
    collision extraction, and a second collision extraction for message prehashing.
    Stateless signing also reserves one randomizer guess per signing query. -/
@[expose] def globalSlotBudget (p : PqHashParams) (qSign : Nat) (cover prim : Spec.RatBound) : Spec.RatBound :=
  let failed : Spec.RatBound := ⟨if p.statefulJorts then 0 else qSign, 2 ^ 256, by decide⟩
  (cover.add failed).add (Spec.RatBound.scale (4 + globalPreUdCalls p) prim)

private def enumFin {α : Type} (n : Nat) (f : Fin n → List α) := (List.ofFn f).flatten

private theorem enumFin_mem {α : Type} {n : Nat} {f : Fin n → List α} (i : Fin n) {x : α} (h : x ∈ f i) :
    x ∈ enumFin n f := List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i,rfl⟩, h⟩

private theorem enumFin_weight {α : Type} (cost : α → Nat) :
    ∀ n (f : Fin n → List α), ((enumFin n f).map cost).sum =
      Spec.sampleSum n (fun i => ((f i).map cost).sum) := by
  intro n; induction n with
  | zero => intro f; simp [enumFin, Spec.sampleSum_zero]
  | succ n ih =>
    intro f
    rw [enumFin, List.ofFn_succ, List.flatten_cons, List.map_append, List.sum_append, Spec.sampleSum_succ]
    rw [← ih]; rfl

private def allSigningSlots (p : PqHashParams) : List (SigningSlot p) :=
  (if p.statefulJorts then [] else enumFin _ fun l => enumFin _ fun j => enumFin _ fun u => [.fors l j u]) ++
  enumFin _ fun i => enumFin _ fun pos => enumFin _ fun r => enumFin _ fun step => [.wots i pos r step]

private theorem mem_allSigningSlots (p : PqHashParams) (slot : SigningSlot p)
    (active : match slot with | .fors .. => p.statefulJorts = false | .wots .. => True) :
    slot ∈ allSigningSlots p := by
  unfold allSigningSlots
  cases slot with
  | fors l j u =>
    apply List.mem_append_left
    simp only [active, Bool.false_eq_true, ↓reduceIte]
    exact enumFin_mem l (enumFin_mem j (enumFin_mem u (.head _)))
  | wots i pos r step =>
    exact List.mem_append_right _ (enumFin_mem i (enumFin_mem pos (enumFin_mem r (enumFin_mem step (.head _)))))

private theorem layer_sum (h : Nat) : ∀ d, Spec.sampleSum d (fun i => 2^((d-i.val)*h)) = hypertreeKeyPairs h d := by
  intro d; induction d with
  | zero => rfl
  | succ d ih =>
    rw [Spec.sampleSum_succ, hypertreeKeyPairs]
    simpa only [Nat.sub_zero, Nat.add_sub_add_right] using congrArg (2^((d+1)*h) + ·) ih

private theorem step_sum : ∀ n, 2 * Spec.sampleSum n (fun i => i.val+1) = n*(n+1) := by
  intro n; induction n with
  | zero => rfl
  | succ n ih =>
    rw [Spec.sampleSum_succ]
    change 2*(1+Spec.sampleSum n (fun i => (i.val+1)+1)) = _
    rw [Spec.sampleSum_add_fn, Spec.sampleSum_const, Nat.mul_one, Nat.mul_add, Nat.mul_add, ih]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

private theorem allSlots_cost (p : PqHashParams) :
    ((allSigningSlots p).map SigningSlot.cost).sum = globalPreUdCalls p := by
  have steps : Spec.sampleSum (p.w-1) (fun i => i.val+1) = p.w*(p.w-1)/2 := by
    have h := step_sum (p.w-1)
    cases hw : p.w with
    | zero => rfl
    | succ n => rw [hw] at h; simp only [Nat.add_sub_cancel] at h ⊢; rw [Nat.mul_comm _ n]; omega
  unfold allSigningSlots globalPreUdCalls
  rw [List.map_append, List.sum_append]
  by_cases st : p.statefulJorts = true <;>
    simp only [st, Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil, enumFin_weight, List.map_cons,
      List.sum_cons, SigningSlot.cost, Nat.add_zero, Spec.sampleSum_const, Nat.mul_one, steps,
      Spec.sampleSum_mul_right, layer_sum, Nat.mul_assoc]

private theorem weighted_union {α : Type} {n : Nat} (pos : 0 < n) (w : α → Fin n → Bool)
    (cost : α → Nat) (prim : Spec.RatBound) (slots : List α)
    (bounds : ∀ a, Spec.GameBound (Spec.FinGame.mk pos (w a)).winProb (Spec.RatBound.scale (cost a) prim)) :
    Spec.GameBound (Spec.FinGame.mk pos fun z => slots.any (fun a => w a z)).winProb
      (Spec.RatBound.scale (slots.map cost).sum prim) := by
  induction slots with
  | nil =>
    change Spec.sampleSum n (fun _ => 0) * _ ≤ 0 * _ * _
    rw [Spec.sampleSum_const]; simp
  | cons a rest ih =>
    apply Spec.GameBound.trans (Spec.event_le_two_reductions _ _ _ (fun _ win => Bool.or_eq_true_iff.mp win))
      (Spec.RatBound.le_trans (Spec.RatBound.add_le_add (bounds a) ih) (add_scale_same _ _ prim))

private theorem fixed_pre_bound {ns nc seedLen keyLen qHash qSign : Nat} (hs : 0 < ns) (hc : 0 < nc)
    (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32)
    (seed : Fin ns → Spec.Bytes) (hSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (table : Fin nc → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) table)
    (msg : Spec.Bytes → Spec.Bytes) (adv : SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Pre : Spec.Code Spec.targetIface Spec.TargetBreak → Prop} {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound}
    (hpre : Spec.SmDtPreHard 𝒜Pre (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜Ud (suiteTweakHash suite) seedLen 32 32 1 prim)
    (classes : ∀ slot c, SlotReductionClass latchOn suite p msg (table c).2 adv slot 𝒜Pre 𝒜Ud) :
    let sp := Spec.CoinSplit.prod ns nc
    Spec.GameBound (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
      (idealPrfBreakEvents latchOn suite p (seed (sp.chal z)) msg (table (sp.advc z)).2 adv).2).winProb
      (Spec.RatBound.scale (globalPreUdCalls p) prim) := by
  intro sp
  let w := fun slot (z : Fin (ns*nc)) => slotWin latchOn suite p msg adv slot (seed (sp.chal z)) (table (sp.advc z)).2
  have bound := weighted_union (Nat.mul_pos hs hc) w SigningSlot.cost prim (allSigningSlots p)
    (fun slot => slot_bound hs hc latchOn suite p seed hSeed table hSec msg adv slot hpre hud (classes slot))
  rw [allSlots_cost] at bound
  exact Spec.GameBound.trans
    (Spec.event_le_reduction_win
      (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z =>
        (idealPrfBreakEvents latchOn suite p (seed (sp.chal z)) msg (table (sp.advc z)).2 adv).2)
      (Spec.FinGame.mk (Nat.mul_pos hs hc) fun z => (allSigningSlots p).any (fun a => w a z))
      (fun z win => by
        obtain ⟨slot, act, won⟩ := pre_selects_slot latchOn suite p wf trees _ msg _ adv win
        exact List.any_eq_true.mpr ⟨slot, mem_allSigningSlots p slot act, won⟩))
    bound

#verify_constructive enumFin_mem enumFin_weight mem_allSigningSlots layer_sum step_sum allSlots_cost weighted_union fixed_pre_bound

private theorem average_secret_seed {n nm nr nc nz ns na : Nat} (pos : 0 < n)
    (a : Spec.CoinSplit n nm nr) (b : Spec.CoinSplit nr nc nz) (c : Spec.CoinSplit nz ns na)
    (w : Fin nm → Fin nc → Fin ns → Fin na → Bool) (eps : Spec.RatBound)
    (h : ∀ m j,
      let sp := Spec.CoinSplit.prod ns nc
      Spec.sampleSum (ns*nc) (fun z => if w m (sp.advc z) (sp.chal z) j then 1 else 0) * eps.den ≤ eps.num*(ns*nc)) :
    Spec.GameBound (Spec.FinGame.mk pos fun z => w (a.chal z) (b.chal (a.advc z)) (c.chal (b.advc (a.advc z)))
      (c.advc (b.advc (a.advc z)))).winProb eps := by
  let sp := Spec.CoinSplit.prod ns nc
  let t := fun m i s j => (if w m i s j then 1 else 0) * eps.den
  have fixed (m j) : Spec.sampleSum nc (fun i => Spec.sampleSum ns (fun s => t m i s j)) ≤ eps.num*(ns*nc) := by
    have h' := h m j
    dsimp only at h'
    rw [← Spec.sampleSum_mul_right, sp.sampleSum_eq] at h'
    rw [Spec.sampleSum_comm]
    simpa only [t, sp, Spec.CoinSplit.chal_pair, Spec.CoinSplit.advc_pair] using h'
  have per (m : Fin nm) : Spec.sampleSum nr (fun r => t m (b.chal r) (c.chal (b.advc r)) (c.advc (b.advc r))) ≤
      na*(eps.num*(ns*nc)) := by
    rw [b.sampleSum_eq]
    simp only [b.chal_pair,b.advc_pair,c.sampleSum_eq,c.chal_pair,c.advc_pair]
    conv => lhs; arg 2; intro i; rw [Spec.sampleSum_comm ns na]
    rw [Spec.sampleSum_comm nc na]
    have h' := Spec.sampleSum_le na _ _ (fixed m)
    rwa [Spec.sampleSum_const] at h'
  change Spec.sampleSum n _ * eps.den ≤ eps.num*n
  rw [← Spec.sampleSum_mul_right, a.sampleSum_eq]
  simp only [a.chal_pair, a.advc_pair]
  have bound := Spec.sampleSum_le nm _ _ per
  rw [Spec.sampleSum_const] at bound
  conv => rhs; rw [a.card_eq,b.card_eq,c.card_eq]
  simpa only [t,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using bound

theorem hulsing_idealPrf_pre_bound {n nm nr nc nz ns na qHash qSign keyLen seedLen : Nat}
    (pos : 0 < n) (latchOn : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (wf : p.productionWellFormed = true) (trees : p.forsTrees ≤ 2^32)
    (π₁ : Spec.CoinSplit n nm nr) (π₂ : Spec.CoinSplit nr nc nz) (π₃ : Spec.CoinSplit nz ns na)
    (msg : Fin nm → Spec.Bytes → Spec.Bytes)
    (sec : Fin nc → Spec.Bytes × (Spec.Bytes → Spec.Bytes)) (hc : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) sec)
    (seed : Fin ns → Spec.Bytes) (hs : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed)
    (adv : Fin na → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜P : Spec.Code Spec.targetIface Spec.TargetBreak → Prop} {𝒜U : Spec.Code Spec.targetIface Bool → Prop}
    {prim : Spec.RatBound} (classes : ∀ m c a slot, SlotReductionClass latchOn suite p (msg m) (sec c).2 (adv a) slot 𝒜P 𝒜U)
    (hpre : Spec.SmDtPreHard 𝒜P (suiteTweakHash suite) seedLen 32 1 prim)
    (hud : SmDtUdHard 𝒜U (suiteTweakHash suite) seedLen 32 32 1 prim) :
    Spec.GameBound (Spec.FinGame.mk pos fun z => (idealPrfBreakEvents latchOn suite p
      (seed (π₃.chal (π₂.advc (π₁.advc z)))) (msg (π₁.chal z))
      (sec (π₂.chal (π₁.advc z))).2 (adv (π₃.advc (π₂.advc (π₁.advc z))))).2).winProb
      (Spec.RatBound.scale (globalPreUdCalls p) prim) := by
  let r := π₁.advc ⟨0,pos⟩
  have sc := Nat.lt_of_le_of_lt (Nat.zero_le _) (π₂.chal r).isLt
  have ss := Nat.lt_of_le_of_lt (Nat.zero_le _) (π₃.chal (π₂.advc r)).isLt
  exact average_secret_seed pos π₁ π₂ π₃ (fun m c s a => (idealPrfBreakEvents latchOn suite p (seed s)
    (msg m) (sec c).2 (adv a)).2) _ (fun m a => fixed_pre_bound ss sc latchOn suite p wf trees seed hs sec hc
      (msg m) (adv a) hpre hud (fun slot c => classes m c a slot))

#verify_constructive average_secret_seed hulsing_idealPrf_pre_bound

/-- Independent finite coins for message PRF, secret PRF, public seed, and adaptive EUF adversary. -/
structure SigningExperiment (qSign : Nat) where
  n : Nat
  nm : Nat
  nr : Nat
  nc : Nat
  nz : Nat
  ns : Nat
  na : Nat
  keyLen : Nat
  seedLen : Nat
  qHash : Nat
  pos : 0 < n
  a : Spec.CoinSplit n nm nr
  b : Spec.CoinSplit nr nc nz
  c : Spec.CoinSplit nz ns na
  msg : Fin nm → Spec.Bytes × (Spec.Bytes → Spec.Bytes)
  sec : Fin nc → Spec.Bytes × (Spec.Bytes → Spec.Bytes)
  seed : Fin ns → Spec.Bytes
  adv : Fin na → SeedWithheldEufCmaAdv qHash qSign
  uniformMsg : Spec.UniformOn (Spec.PrfSampleOk keyLen 65 32) msg
  uniformSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen+32) 32) sec
  uniformSeed : Spec.UniformOn (fun s : Spec.Bytes => s.length = seedLen) seed

abbrev SigningExperiment.keygen {q : Nat} (E : SigningExperiment q) :=
  multiHopFullKeygen E.a E.b E.c E.msg E.sec E.seed
abbrev SigningExperiment.adversary {q : Nat} (E : SigningExperiment q) :=
  multiHopFullAdv E.a E.b E.c E.adv

/-- Membership is required only for the reductions executed by the proof. The ITSR
    assumption is used only when a stateless signature can open FORS leaves. -/
structure SigningPrimitiveBounds {q : Nat} (E : SigningExperiment q) (latch : Bool) (suite : TweakableHashSuite)
    (p : PqHashParams) (cover prim : Spec.RatBound) where
  word : p.w = 4 ∨ p.w = 16
  oneTime : p.statefulJorts = true → latch = true
  msgClass : Spec.Code Spec.byteOracleIface Bool → Prop
  secClass : Spec.Code Spec.byteOracleIface Bool → Prop
  tcrClass : Spec.Code Spec.targetIface Spec.TargetBreak → Prop
  itsrClass : Spec.Code Spec.byteOracleIface (Spec.Bytes × Spec.Bytes) → Prop
  preClass : Spec.Code Spec.targetIface Spec.TargetBreak → Prop
  udClass : Spec.Code Spec.targetIface Bool → Prop
  msgMember : ∀ r, msgClass (prfMsgHopDistinguisher latch suite p (E.seed (E.c.chal (E.b.advc r)))
    (E.sec (E.b.chal r)).1 (E.adv (E.c.advc (E.b.advc r))))
  secMember : ∀ m z, secClass (prfSecHopDistinguisher latch suite p (E.seed (E.c.chal z)) (E.msg m).2 (E.adv (E.c.advc z)))
  tcrMember : ∀ m c a, tcrClass (openSeedTcrHopAdv latch suite p word (E.msg m).2 (E.sec c).2
    (fun x hx => (((Spec.PrfSampleOk_eq ..).mp (E.uniformMsg.mem m)).2 x).1 hx) oneTime (E.adv a))
  prehashMember : ∀ m c a, tcrClass (openSeedWitnessAdv suite (signingPrehashTcr latch suite p (E.msg m).2 (E.sec c).2 (E.adv a)))
  itsrMember : ∀ s c a, itsrClass (memoItsrAdv latch suite p (E.seed s) (E.sec c).2 (E.adv a))
  slotMember : ∀ m c a slot, SlotReductionClass latch suite p (E.msg m).2 (E.sec c).2 (E.adv a) slot preClass udClass
  prfMsg : Spec.PrfHard msgClass (suitePrfMsg65 suite) E.keyLen 65 32 q prim
  prfSec : Spec.PrfHard secClass (suitePrfSec E.seedLen suite) E.keyLen (E.seedLen+32) 32 (prfSecQueryBudget p q) prim
  itsr : ¬ (p.statefulJorts = true ∨ p.forsTrees = 0) → ∀ s c, Spec.ItsrHard itsrClass
    (forsGlobalSubsetSelector suite p (derivePublicKeyIdealPrf suite p (E.seed s) (E.sec c).2)) 32 q cover
  tcr : SmDtOpenSeedTcrHard tcrClass (suiteTweakHash suite) E.seedLen 1 prim
  pre : Spec.SmDtPreHard preClass (suiteTweakHash suite) E.seedLen 32 1 prim
  ud : SmDtUdHard udClass (suiteTweakHash suite) E.seedLen 32 32 1 prim

private theorem budget_collect (base prim : Spec.RatBound) (k : Nat) :
    (((((base.add prim).add prim).add (Spec.RatBound.scale k prim)).add prim).add prim).le
      (base.add (Spec.RatBound.scale (4+k) prim)) := by
  unfold Spec.RatBound.add Spec.RatBound.scale Spec.RatBound.le
  dsimp only
  apply Nat.le_of_eq
  have four (n : Nat) : 4*n = n+n+n+n := by omega
  simp only [Nat.add_mul, four]
  ac_rfl

/-- Executable EUF-CMA reduction to five primitive notions, on the actual keygen and adaptive adversary. -/
theorem hulsing_closed_multihop_euf_cma_bound_of_primitive_bounds {q : Nat} (E : SigningExperiment q) (latchOn : Bool)
    (suite : TweakableHashSuite) (p : PqHashParams) (wf : p.productionWellFormed = true)
    (trees : p.forsTrees ≤ 2^32) (cover prim : Spec.RatBound)
    (H : SigningPrimitiveBounds E latchOn suite p cover prim) :
    Spec.GameBound (execEufCmaGameWith latchOn E.pos suite p E.keygen E.adversary).winProb
      (globalSlotBudget p q cover prim) := by
  let events := fun z => idealPrfBreakEvents latchOn suite p (E.seed (E.c.chal (E.b.advc (E.a.advc z))))
    (E.msg (E.a.chal z)).2 (E.sec (E.b.chal (E.a.advc z))).2 (E.adv (E.c.advc (E.b.advc (E.a.advc z))))
  let base := cover.add (⟨if p.statefulJorts then 0 else q, 2^256, by decide⟩ : Spec.RatBound)
  have hc := hulsing_idealPrf_cover_bound E.pos latchOn suite p E.a E.b E.c E.msg E.uniformMsg
    (fun c => (E.sec c).2) E.seed E.uniformSeed E.adv H.itsrMember H.prehashMember H.itsr H.tcr (by decide)
  have coverB : Spec.GameBound (Spec.FinGame.mk E.pos fun z => (events z).1).winProb (base.add prim) := by
    apply Spec.GameBound.trans hc
    split
    · change 0 * _ ≤ _ * 1
      simp
    · rename_i h
      have st : p.statefulJorts = false := Bool.eq_false_iff.mpr (fun yes => h (.inl yes))
      simp only [base, st, Bool.false_eq_true, ↓reduceIte, Spec.RatBound.le_refl]
  have preB := hulsing_idealPrf_pre_bound E.pos latchOn suite p wf trees E.a E.b E.c (fun m => (E.msg m).2)
    E.sec E.uniformSec E.seed E.uniformSeed E.adv H.slotMember H.pre H.ud
  exact Spec.GameBound.trans (hulsing_full_multihop_euf_cma_bound_with latchOn E.pos suite p H.oneTime H.word
    E.seedLen E.keyLen q (prfSecQueryBudget p q) 1 (Nat.le_refl _) (Nat.le_refl _) (by decide)
    E.a E.b E.c E.msg E.uniformMsg E.sec E.uniformSec E.seed E.uniformSeed E.adv H.msgMember
    (fun _ => H.secMember _ _) (fun _ => H.tcrMember _ _ _) (fun z => (events z).1) (fun z => (events z).2)
    (fun _ => idealPrfBreakEvents_fst_of _ _ _ _ _ _ _) (fun _ => idealPrfBreakEvents_snd_of _ _ _ _ _ _ _)
    H.prfMsg H.prfSec coverB H.tcr preB) (budget_collect base prim _)

#verify_constructive budget_collect hulsing_closed_multihop_euf_cma_bound_of_primitive_bounds

/-- A zero-query adversary used to test joint reachability of the primitive hypotheses. -/
def emptySigningForgery {qh : Nat} : SeedWithheldEufCmaAdv qh 0 :=
  ⟨fun _ => .pure ([], ⟨[], 0, 0, [], []⟩), fun _ => trivial⟩

private theorem empty_run {qh : Nat} (pk : PqPublicKey) :
    (canonicalizeAdvOptRand (@emptySigningForgery qh)).run pk = .pure ([], ⟨[], 0, 0, [], []⟩) := by
  rw [canonicalizeAdvOptRand_run, emptySigningForgery, canonicalizeTreeOptRand.public_eq_1]

private theorem empty_verify (suite : TweakableHashSuite) (pk : PqPublicKey) :
    verifyProductionPqHashSig suite baggyProdParams pk [] ⟨[],0,0,[],[]⟩ = false := by
  rw [verifyProductionPqHashSig_eq]
  split
  · rfl
  · have h : 0 ≠ baggyProdParams.numLayers := by
      rw [baggyProdParams,baggy128fParams_eq]; decide
    simp [h]

private theorem empty_recover {qh : Nat} (suite : TweakableHashSuite) (p : PqHashParams) (msg : Spec.Bytes → Spec.Bytes)
    (slot : SigningSlot p) (f : Spec.Bytes → Spec.Bytes) (s y : Spec.Bytes) :
    slotRecover false suite p msg (@emptySigningForgery qh) slot f s y = [] := by
  cases slot <;> simp only [slotRecover, empty_run, evalLatchedAdaptiveTree.public_eq_1, List.getD_nil]

private theorem empty_prehash {qh : Nat} (suite : TweakableHashSuite) (p : PqHashParams) (msg f : Spec.Bytes → Spec.Bytes)
    (s : Spec.Bytes) : signingPrehashTcr false suite p msg f (@emptySigningForgery qh) s = none := by
  have transport : ∀ {a b : Spec.Bytes} (e : a = b), (e ▸ (none : Option (ExplicitTcrWitness suite a)) :
      Option (ExplicitTcrWitness suite b)) = none := by intro a b e; cases e; rfl
  simp only [signingPrehashTcr, idealSigningObservation, empty_run, evalLatchedAdaptiveTree.public_eq_1,
    signLogFromOracle.public_eq_1, logPrehashCollision, transport]

/-- Test suite distinguishing an empty chain input from a full-width input. The strict witness
    uses only the reduction programs induced by the empty forgery. -/
def signingWitnessSuite : TweakableHashSuite where
  suiteId := []
  rawHash raw := List.replicate 32 (if ((decodeMultiFrameBytes raw).getD []).getD 3 [] = [] then 0 else 1)
  rawHash_len _ := List.length_replicate

private theorem witness_chain_separates (s : Spec.Bytes) (a : HashAdrs) {v : Spec.Bytes} (len : v.length = 32) :
    thChainF signingWitnessSuite s a [] ≠ thChainF signingWitnessSuite s a v := by
  have ne : v ≠ [] := by intro e; simp [e] at len
  simp only [thChainF_eq, thCall_eq, signingWitnessSuite, thPreimage_eq, List.cons_append, List.nil_append,
    decodeMultiFrameBytes_encodeMultiFrame, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero,
    ↓reduceIte, ne]
  decide

private theorem chain_steps_length (suite : TweakableHashSuite) (s : Spec.Bytes) (l : UInt32) (t : UInt64) (kp r : Nat) :
    ∀ n i v, v.length = 32 → (wotsChainSteps suite s l t kp r i n v).length = 32 := by
  intro n; induction n with
  | zero => intro i v h; rwa [wotsChainSteps_zero]
  | succ n ih =>
    intro i v _
    rw [wotsChainSteps_succ]
    apply ih
    rw [thChainF_eq]; exact thCall_length ..

private theorem zero_le_loss (eps : Spec.RatBound) : Spec.RatBound.zero.le eps := by
  unfold Spec.RatBound.le Spec.RatBound.zero; simp

private theorem dist_zero_of_equal {n : Nat} (A B : Spec.FinGame n) (eps : Spec.RatBound) (h : ∀ z, A.win z = B.win z) :
    Spec.GameBound (Spec.AdvDist A B) eps := by
  rw [Spec.FinGame.ext_win h]
  exact Spec.GameBound.trans (Spec.adv_refl _) (zero_le_loss eps)

private def rejectingPrf (D : Spec.Code Spec.byteOracleIface Bool) : Prop :=
  ∀ f q, (Spec.Code.play (Spec.budgetedFunOracle f q) D 0).1 = false

private theorem rejectingPrf_hard (prf : Spec.Bytes → Spec.Bytes → Spec.Bytes) (k l width q : Nat) (eps : Spec.RatBound) :
    Spec.PrfHard rejectingPrf prf k l width q eps := by
  intro n nc na pos sp sample _ adv h
  apply dist_zero_of_equal
  intro z
  rw [Spec.prfRealGame.public_eqs, Spec.prfIdealGame.public_eqs]
  exact (h (sp.advc z) _ _).trans (h (sp.advc z) _ _).symm

private theorem empty_msg_rejects {qh : Nat} (suite : TweakableHashSuite) (s key : Spec.Bytes) :
    rejectingPrf (prfMsgHopDistinguisher false suite baggyProdParams s key (@emptySigningForgery qh)) := by
  intro f q
  simp only [prfMsgHopDistinguisher.public_eqs, empty_run, prfMsgHopTree_pure, empty_verify, Bool.false_and, Spec.Code.play_ret]

private theorem empty_sec_rejects {qh : Nat} (suite : TweakableHashSuite) (s : Spec.Bytes) (msg : Spec.Bytes → Spec.Bytes) :
    rejectingPrf (prfSecHopDistinguisher false suite baggyProdParams s msg (@emptySigningForgery qh)) := by
  intro f q
  simp only [prfSecHopDistinguisher.public_eqs, code_play_bind, empty_run, prfSecHopTree_pure, empty_verify,
    Bool.false_and, Spec.Code.play_ret]

private def emptyTcrProgram : Spec.Code Spec.targetIface Spec.TargetBreak := .call .reveal fun _ => .ret ⟨[],[],[]⟩

private theorem empty_tcr {qh : Nat} (suite : TweakableHashSuite) (msg f : Spec.Bytes → Spec.Bytes)
    (hw : baggyProdParams.w = 4 ∨ baggyProdParams.w = 16) (hr : ∀ x, x.length = 65 → (msg x).length = 32)
    (st : baggyProdParams.statefulJorts = true → false = true) :
    openSeedTcrHopAdv false suite baggyProdParams hw msg f hr st (@emptySigningForgery qh) = emptyTcrProgram := by
  unfold openSeedTcrHopAdv emptyTcrProgram
  congr 1
  funext seed
  dsimp only
  rw [extractIdealPrfTcrWitnessOpt_lost]
  simp only [ExecEufCmaIdealPrfGame_win, empty_run, evalLatchedAdaptiveTree.public_eq_1, empty_verify, Bool.false_and]

private theorem empty_tcr_hard (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes) (seedLen : Nat) (eps : Spec.RatBound) :
    SmDtOpenSeedTcrHard (· = emptyTcrProgram) th seedLen 1 eps := by
  intro n nc na pos sp seed _ adv h
  apply Spec.GameBound.trans (Spec.FinGame.bound_zero_of_forall_lose _ _) (zero_le_loss eps)
  intro z
  simp only [smDtOpenSeedTcrGame.public_eqs, h, emptyTcrProgram, Spec.Code.play_call,
    smDtOpenSeedTcrOracle_reveal, Spec.Code.play_ret, Spec.smDtTcrWin_eq]
  rfl

private theorem empty_itsr_hard (suite : TweakableHashSuite) (pk : PqPublicKey) (eps : Spec.RatBound) :
    Spec.ItsrHard (fun _ => True) (forsGlobalSubsetSelector suite baggyProdParams pk) 32 0 eps := by
  intro n nc na pos sp rand _ adv _
  apply Spec.GameBound.trans (Spec.FinGame.bound_zero_of_forall_lose _ _) (zero_le_loss eps)
  intro z
  apply Bool.eq_false_iff.mpr
  intro win
  let tape := fun (w : Fin n) i => (rand (sp.chal w)).getD i []
  let A := fun w => adv (sp.advc w)
  let run := Spec.itsrRun 0 tape A z
  let leaves := forsGlobalSubsetSelector suite baggyProdParams pk run.1.1 run.1.2
  have len : leaves.length = baggyProdParams.forsTrees := forsGlobalSubsetSelector_length _ _ _ _ _
    baggy128f_productionWellFormed (by rw [baggyProdParams, baggy128fParams_eq])
  have nonzero : 0 < leaves.length := by rw [len, baggyProdParams, baggy128fParams_eq]; decide
  obtain ⟨_,inLog,_⟩ := (Spec.itsrGame_win_sound pos _ 0 tape A z win).2 _ (List.getElem_mem (l := leaves) nonzero)
  have zero : run.2.length ≤ 0 := Spec.itsrRun_log_length_le 0 tape A z
  have nil : run.2 = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero zero)
  change _ ∈ run.2 at inLog
  rw [nil] at inLog; contradiction

#verify_constructive empty_run empty_verify empty_recover empty_prehash witness_chain_separates chain_steps_length
  zero_le_loss dist_zero_of_equal rejectingPrf_hard empty_msg_rejects empty_sec_rejects empty_tcr empty_tcr_hard empty_itsr_hard

private def rejectingPre (D : Spec.Code Spec.targetIface Spec.TargetBreak) : Prop :=
  let th := suiteTweakHash signingWitnessSuite
  ∀ s hidden, (hidden 0 : Spec.Bytes).length = 32 →
    let run := Spec.Code.play (Spec.smDtPreOracle th 1 hidden) D ⟨s, [], false⟩
    Spec.smDtPreWin th run.2 run.1 = false

private theorem singleton_head_length {xs : List Spec.Bytes} (hl : xs.length = 1)
    (hv : ∀ v ∈ xs, v.length = 32) : (xs.getD 0 []).length = 32 := by
  cases xs with
  | nil => contradiction
  | cons x tail => exact hv x (.head _)

private theorem rejectingPre_hard (seedLen : Nat) (eps : Spec.RatBound) :
    Spec.SmDtPreHard rejectingPre (suiteTweakHash signingWitnessSuite) seedLen 32 1 eps := by
  intro n nc na pos sp sample hu adv adm
  apply Spec.GameBound.trans (Spec.FinGame.bound_zero_of_forall_lose _ _) (zero_le_loss eps)
  intro z
  have ok := (Spec.SmDtPreSampleOk_eq ..).mp (hu.mem (sp.chal z))
  simp only [Spec.smDtPreGame.public_eqs, Spec.smDtPreRun.public_eqs]
  exact adm (sp.advc z) _ _ (singleton_head_length ok.2.1 ok.2.2)

private def rejectingUd (D : Spec.Code Spec.targetIface Bool) : Prop :=
  ∃ addr test, D = udDigestTest (encodeChainFTweak addr) test ∧
    ∀ (s y : Spec.Bytes), y.length = 32 → test s y = false

private theorem rejectingUd_hard (seedLen : Nat) (eps : Spec.RatBound) :
    SmDtUdHard rejectingUd (suiteTweakHash signingWitnessSuite) seedLen 32 32 1 eps := by
  intro n nc na pos sp sample hu adv adm
  apply dist_zero_of_equal
  intro z
  obtain ⟨addr,test,eq,no⟩ := adm (sp.advc z)
  have ok := (SmDtUdSampleOk.public_eqs ..).mp (hu.mem (sp.chal z))
  let s := (sample (sp.chal z)).1
  let hidden := fun i => (sample (sp.chal z)).2.1.getD i []
  let digest := fun i => (sample (sp.chal z)).2.2.getD i []
  simp only [smDtUdRealGame.public_eqs, smDtUdIdealGame.public_eqs, eq]
  have R := udDigestTest_real_win Nat.one_pos (suiteTweakHash signingWitnessSuite) (fun _ => s)
    (fun _ => hidden) (encodeChainFTweak addr) (fun _ => test) ⟨0,Nat.one_pos⟩
  have I := udDigestTest_ideal_win Nat.one_pos (fun _ => s) (fun _ => digest)
    (encodeChainFTweak addr) (fun _ => test) ⟨0,Nat.one_pos⟩
  simp only [smDtUdRealGame.public_eqs] at R
  simp only [smDtUdIdealGame.public_eqs] at I
  change (Spec.Code.play (Spec.smDtPreOracle _ 1 hidden) _ ⟨s,[],false⟩).1 =
    (Spec.Code.play (smDtUdIdealOracle 1 digest) _ ⟨s,[],false⟩).1
  rw [R, I, suiteTweakHash_chainF, no, no]
  · exact singleton_head_length ok.2.2.1 ok.2.2.2
  · rw [thChainF_eq]; exact thCall_length ..

private theorem slot_tweak_address {p : PqHashParams} (slot : SigningSlot p) :
    ∃ addr, slot.tweak = encodeChainFTweak addr := by cases slot <;> exact ⟨_,rfl⟩

private theorem empty_slot_member {qh : Nat} (p : PqHashParams) (msg f : Spec.Bytes → Spec.Bytes) (slot : SigningSlot p) :
    SlotReductionClass false signingWitnessSuite p msg f (@emptySigningForgery qh) slot rejectingPre rejectingUd := by
  let suite := signingWitnessSuite
  constructor
  · intro s hidden len
    dsimp only
    rw [puncturedTablePreAdv_win, empty_recover]
    obtain ⟨a,ha⟩ := slot_tweak_address slot
    rw [ha, suiteTweakHash_chainF, suiteTweakHash_chainF]
    exact decide_eq_false (witness_chain_separates s a len)
  · cases slot with
    | fors => trivial
    | wots i pos r step =>
      intro a b _
      refine ⟨_, _, rfl, ?_⟩
      intro s y len
      simp only [wotsSlotTest, empty_recover, SigningSlot.tweak, suiteTweakHash_chainF]
      apply decide_eq_false
      exact witness_chain_separates s _ (chain_steps_length suite s _ _ _ _ b _ y len)

/-- Joint fixture for strict game bounds. The adversary submits a malformed signature and the
    primitive classes contain its actual induced reductions. No cryptographic hardness of the
    fixture hash against unrestricted adversaries is required. -/
def emptyForgeryBaggyPrimitiveBounds (E : SigningExperiment 0) (advEq : ∀ a, E.adv a = emptySigningForgery)
    (cover prim : Spec.RatBound) : SigningPrimitiveBounds E false signingWitnessSuite baggyProdParams cover prim where
  word := .inl (by rw [baggyProdParams, baggy128fParams_eq])
  oneTime := by rw [baggyProdParams, baggy128fParams_eq]; decide
  msgClass := rejectingPrf
  secClass := rejectingPrf
  itsrClass := fun _ => True
  tcrClass := (· = emptyTcrProgram)
  preClass := rejectingPre
  udClass := rejectingUd
  msgMember := fun r => by rw [advEq]; apply empty_msg_rejects
  secMember := fun m z => by rw [advEq]; apply empty_sec_rejects
  itsrMember := fun _ _ _ => trivial
  tcrMember := fun m c a => by rw [advEq]; apply empty_tcr
  prehashMember := fun m c a => by simp only [advEq, openSeedWitnessAdv.public_eqs, empty_prehash, emptyTcrProgram]
  slotMember := fun m c a slot => by rw [advEq]; apply empty_slot_member
  prfMsg := rejectingPrf_hard _ _ _ _ _ prim
  prfSec := rejectingPrf_hard _ _ _ _ _ prim
  tcr := empty_tcr_hard _ _ prim
  itsr := fun _ _ _ => empty_itsr_hard _ _ _
  pre := rejectingPre_hard _ prim
  ud := rejectingUd_hard _ prim

#verify_constructive singleton_head_length rejectingPre_hard rejectingUd_hard slot_tweak_address empty_slot_member

#verify_constructive overlay_inputs ideal_material_core ideal_material_signQuery

#verify_constructive ideal_material_publicKey pinned_wotsPk pinned_xmssRoot pinned_forsRoot
  signingPosition_next prodGrind_overlay ideal_layers

#verify_constructive off_cell pinned_fors_secret forsLeaf_same_cell pinned_fors_leaf pinned_wots_node
  ideal_material_wotsPk ideal_material_xmssRoot ideal_material_forsRoot ideal_material_openings


end Qsag
end
