module


public import Qsag.Protocol.Aggregation.SuccinctAggregationIop.StepOpTableExtraction

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv
set_option autoImplicit false
set_option exponentiation.threshold 2048
attribute [local irreducible] verifyUpperLayers
attribute [local irreducible] computeMessageMu
attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless


/-! ### Deployed multi-stage WHIR schedule and extension-field error denominators (`pcs.rs`) -/

/-- `pcs.rs:WhirStageSpec`. -/
structure WhirStageSpec where
  /-- Reed-Solomon blowup `1 / ρ_i` of the stage oracle. -/
  blowup : Nat
  /-- Multilinear variables folded during the stage. -/
  stepVars : Nat
  /-- Coset fibers opened from the stage oracle. -/
  numQueries : Nat
  deriving DecidableEq, Repr


namespace WhirSecurityRegime

end WhirSecurityRegime


/-- `pcs.rs:PCS_POW_BITS`: per-stage transcript proof-of-work difficulty. -/
def whirPowBits : Nat := 16


/-- `log2` of a supported blowup (`blowup.trailing_zeros()` on `4 | 16 | 64 | 256`). -/
@[expose] def whirLogBlowup : Nat → Nat
  | 4 => 2
  | 16 => 4
  | 64 => 6
  | 256 => 8
  | _ => 0


@[expose] def whirQueryTable (t0 t1 t2 t3 logB : Nat) : Nat :=
  if logB ≤ 2 then t0 else if logB ≤ 4 then t1 else if logB ≤ 6 then t2 else t3


/-- Denominator `blowup ^ numQueries` of the stage query error `ρ_i ^ q_i`: the error of `q_i`
    fiber queries when a cheating oracle agrees with the code on a `ρ_i` fraction. That
    agreement bound is an input of this accounting; no proximity-gap statement is proved here. -/
def WhirStageSpec.queryErrorDenominator (st : WhirStageSpec) : Nat := st.blowup ^ st.numQueries

/-- Query error denominator times the classical grinding cost `2 ^ whirPowBits` of the stage
    proof of work. A quantum search over nonces pays only about `2 ^ (whirPowBits / 2)`. -/
def WhirStageSpec.fiatShamirDenominator (st : WhirStageSpec) : Nat :=
  2 ^ whirPowBits * st.queryErrorDenominator

/-- Consecutive blowups escalate by a factor of exactly `4`. -/
def whirBlowupsEscalate : List Nat → Bool
  | a :: b :: tl => (b == 4 * a) && whirBlowupsEscalate (b :: tl)
  | _ => true

/-- Production maximum number of sampled fibers per stage. -/
def whirMaxQueryCap : Nat := 512

/-- The domain and step checks of `pcs.rs:WhirSchedule::validate_structural`, stage by stage
    with `remaining` variables left: `step_vars < remaining` and the stage evaluation domain
    `2^remaining * blowup` is at most `2^31`. Returns the variables left after the last stage. -/
def whirStageDomainsOk : Nat → List WhirStageSpec → Option Nat
  | remaining, [] => some remaining
  | remaining, st :: tl =>
    if st.stepVars < remaining ∧ 2 ^ remaining * st.blowup ≤ 2 ^ 31 then
      whirStageDomainsOk (remaining - st.stepVars) tl
    else none


/-- Union bound over the three stages of the `q = (56, 30, 21)` geometry with 16-bit grinding:
    `1/D_0 + 1/D_1 + 1/D_2 ≤ 2^-127` for the Fiat-Shamir denominators `D_i`. -/
theorem whir_base_k8_stage_union_bound :
    2 ^ 127 * (2 ^ 136 * 2 ^ 142 + 2 ^ 128 * 2 ^ 142 + 2 ^ 128 * 2 ^ 136) ≤
      2 ^ 128 * 2 ^ 136 * 2 ^ 142 := by decide

/-- Union bound over the three stages of the default schedule at `numVars = 20`, without any
    proof-of-work credit: `1/2^516 + 1/2^520 + 1/2^528 ≤ 2^-514`. -/
theorem whirStageSchedule_deployed_union_bound :
    2 ^ 514 * (2 ^ 520 * 2 ^ 528 + 2 ^ 516 * 2 ^ 528 + 2 ^ 516 * 2 ^ 520) ≤
      2 ^ 516 * 2 ^ 520 * 2 ^ 528 := by decide +kernel


/-- **The `GoldilocksExt2` cliff.** Over a challenge set of `p^2 < 2^128` elements, every error
    numerator `n ≥ 2^28` leaves fewer than `100` bits: `n / p^2 > 2^-100`. -/
theorem ext2_error_denominator_cliff (n : Nat) (hn : 2 ^ 28 ≤ n) :
    goldilocksPrime ^ 2 < n * 2 ^ 100 := by
  have h1 : goldilocksPrime ^ 2 < 2 ^ 28 * 2 ^ 100 := by decide
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hn)


/-- The same numerator at `|D| = 2^26`, `c = 2^33` leaves fewer than `44` bits over
    `GoldilocksExt2`. -/
theorem ext2_folding_denominator_cliff :
    goldilocksPrime ^ 2 < 2 ^ (2 * 26) * 2 ^ 33 * 2 ^ 44 := by decide





private theorem squeezed_step_arith (N l : Nat) :
    N * (16 * l * N ^ (l - 1)) ≤ 16 * l * N ^ l := by
  cases l with
  | zero => simp only [Nat.mul_zero, Nat.zero_mul, Nat.le_refl]
  | succ k =>
    rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_comm N (N ^ k)]
    exact Nat.le_refl _


/-! ### Row-committed witness cells: canonical codec, extraction, and binding -/

/-- A canonical prefix codec into trace cells: `dec` parses a value off the front of a cell
    list and returns the unconsumed tail; `enc_dec` says every accepted cell list is the
    canonical encoding followed by that tail. -/
structure CellCodec (α : Type) where
  enc : α → List Goldilocks
  dec : List Goldilocks → Option (α × List Goldilocks)
  dec_enc : ∀ (a : α) (rest : List Goldilocks), dec (enc a ++ rest) = some (a, rest)
  enc_dec : ∀ (cs : List Goldilocks) (a : α) (rest : List Goldilocks),
    dec cs = some (a, rest) → cs = enc a ++ rest

def cellMapDec {α β : Type} (da : List Goldilocks → Option (α × List Goldilocks))
    (f : α → β) (cs : List Goldilocks) : Option (β × List Goldilocks) :=
  match da cs with
  | none => none
  | some (a, r) => some (f a, r)

private theorem cellMapDec_some {α β : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)} {f : α → β}
    {cs : List Goldilocks} {b : β} {rest : List Goldilocks}
    (h : cellMapDec da f cs = some (b, rest)) : ∃ a, da cs = some (a, rest) ∧ f a = b := by
  unfold cellMapDec at h
  cases h1 : da cs with
  | none => rw [h1] at h; cases h
  | some x =>
    obtain ⟨a, r⟩ := x
    rw [h1] at h
    obtain ⟨hb, hr⟩ := Prod.mk.inj (Option.some.inj h)
    subst hr
    exact ⟨a, rfl, hb⟩

private theorem cellMapDec_eq {α β : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)} {f : α → β}
    {cs : List Goldilocks} {a : α} {rest : List Goldilocks}
    (h : da cs = some (a, rest)) : cellMapDec da f cs = some (f a, rest) := by
  simp only [cellMapDec, h]

def cellBind2 {α β γ : Type}
    (da : List Goldilocks → Option (α × List Goldilocks))
    (db : List Goldilocks → Option (β × List Goldilocks))
    (k : α → β → γ) (cs : List Goldilocks) : Option (γ × List Goldilocks) :=
  match da cs with
  | none => none
  | some (a, r1) =>
    match db r1 with
    | none => none
    | some (b, r2) => some (k a b, r2)

private theorem cellBind2_some {α β γ : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)}
    {db : List Goldilocks → Option (β × List Goldilocks)}
    {k : α → β → γ} {cs : List Goldilocks} {c : γ} {rest : List Goldilocks}
    (h : cellBind2 da db k cs = some (c, rest)) :
    ∃ a b r1, da cs = some (a, r1) ∧ db r1 = some (b, rest) ∧ k a b = c := by
  unfold cellBind2 at h
  cases h1 : da cs with
  | none => rw [h1] at h; cases h
  | some x =>
    obtain ⟨a, r1⟩ := x
    rw [h1] at h
    dsimp only at h
    cases h2 : db r1 with
    | none => rw [h2] at h; cases h
    | some y =>
      obtain ⟨b, r2⟩ := y
      rw [h2] at h
      obtain ⟨hc, hr⟩ := Prod.mk.inj (Option.some.inj h)
      subst hr
      exact ⟨a, b, r1, rfl, h2, hc⟩

private theorem cellBind2_eq {α β γ : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)}
    {db : List Goldilocks → Option (β × List Goldilocks)}
    {k : α → β → γ} {cs : List Goldilocks} {a : α} {b : β} {r1 rest : List Goldilocks}
    (h1 : da cs = some (a, r1)) (h2 : db r1 = some (b, rest)) :
    cellBind2 da db k cs = some (k a b, rest) := by
  simp only [cellBind2, h1, h2]

/-- One field element in one cell. -/
def cellFld : CellCodec Goldilocks where
  enc := fun a => [a]
  dec := fun cs =>
    match cs with
    | [] => none
    | c :: rest => some (c, rest)
  dec_enc := fun _ _ => rfl
  enc_dec := fun cs a rest h => by
    match cs, h with
    | [], h => cases h
    | c :: tl, h =>
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      rw [← h1, ← h2]
      rfl

/-- The empty encoding of `Unit`. -/
def cellUnit : CellCodec Unit where
  enc := fun _ => []
  dec := fun cs => some ((), cs)
  dec_enc := fun _ _ => rfl
  enc_dec := fun _ _ _ h => (Prod.mk.inj (Option.some.inj h)).2

/-- Concatenation of two codecs. -/
def cellSeq {α β : Type} (ca : CellCodec α) (cb : CellCodec β) : CellCodec (α × β) where
  enc := fun p => ca.enc p.1 ++ cb.enc p.2
  dec := cellBind2 ca.dec cb.dec Prod.mk
  dec_enc := fun p rest => by
    obtain ⟨a, b⟩ := p
    have e : (ca.enc a ++ cb.enc b) ++ rest = ca.enc a ++ (cb.enc b ++ rest) :=
      List.append_assoc _ _ _
    show cellBind2 ca.dec cb.dec Prod.mk ((ca.enc a ++ cb.enc b) ++ rest) = some ((a, b), rest)
    rw [e]
    exact cellBind2_eq (ca.dec_enc a _) (cb.dec_enc b rest)
  enc_dec := fun cs p rest h => by
    obtain ⟨a, b, r1, h1, h2, hk⟩ := cellBind2_some h
    rw [← hk, ca.enc_dec cs a r1 h1, cb.enc_dec r1 b rest h2]
    exact (List.append_assoc _ _ _).symm

/-- Transport of a codec along a bijection. -/
def cellIso {α β : Type} (c : CellCodec α) (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) : CellCodec β where
  enc := fun b => c.enc (g b)
  dec := cellMapDec c.dec f
  dec_enc := fun b rest => by
    have h := cellMapDec_eq (f := f) (c.dec_enc (g b) rest)
    rw [hfg] at h
    exact h
  enc_dec := fun cs b rest h => by
    obtain ⟨a, h1, hf⟩ := cellMapDec_some h
    have e := c.enc_dec cs a rest h1
    rw [← hf]
    show cs = c.enc (g (f a)) ++ rest
    rw [hgf]
    exact e

def cellSumEnc {α β : Type} (ea : α → List Goldilocks) (eb : β → List Goldilocks) :
    Sum α β → List Goldilocks
  | .inl a => Goldilocks.zero :: ea a
  | .inr b => Goldilocks.one :: eb b

def cellSumDec {α β : Type} (da : List Goldilocks → Option (α × List Goldilocks))
    (db : List Goldilocks → Option (β × List Goldilocks)) :
    List Goldilocks → Option (Sum α β × List Goldilocks)
  | [] => none
  | m :: cs =>
    if m = Goldilocks.zero then cellMapDec da Sum.inl cs
    else if m = Goldilocks.one then cellMapDec db Sum.inr cs
    else none

private theorem goldilocks_one_ne_zero : ¬ (Goldilocks.one = Goldilocks.zero) := by decide

/-- Tagged union: selector cell `0` or `1` followed by the payload; any other selector is
    rejected. -/
def cellSum {α β : Type} (ca : CellCodec α) (cb : CellCodec β) : CellCodec (Sum α β) where
  enc := cellSumEnc ca.enc cb.enc
  dec := cellSumDec ca.dec cb.dec
  dec_enc := fun s rest => by
    match s with
    | .inl a =>
      show cellSumDec ca.dec cb.dec (Goldilocks.zero :: (ca.enc a ++ rest)) = some (Sum.inl a, rest)
      rw [cellSumDec, ite_eq_left rfl]
      exact cellMapDec_eq (ca.dec_enc a rest)
    | .inr b =>
      show cellSumDec ca.dec cb.dec (Goldilocks.one :: (cb.enc b ++ rest)) = some (Sum.inr b, rest)
      rw [cellSumDec, ite_eq_right goldilocks_one_ne_zero, ite_eq_left rfl]
      exact cellMapDec_eq (cb.dec_enc b rest)
  enc_dec := fun cs s rest h => by
    match cs, h with
    | [], h => cases h
    | m :: tl, h =>
      rw [cellSumDec] at h
      by_cases hm0 : m = Goldilocks.zero
      · rw [ite_eq_left hm0] at h
        obtain ⟨a, h1, hf⟩ := cellMapDec_some h
        rw [← hf, hm0, ca.enc_dec tl a rest h1]
        rfl
      · rw [ite_eq_right hm0] at h
        by_cases hm1 : m = Goldilocks.one
        · rw [ite_eq_left hm1] at h
          obtain ⟨b, h1, hf⟩ := cellMapDec_some h
          rw [← hf, hm1, cb.enc_dec tl b rest h1]
          rfl
        · rw [ite_eq_right hm1] at h; cases h

def cellListEnc {α : Type} (enc : α → List Goldilocks) : List α → List Goldilocks
  | [] => [Goldilocks.zero]
  | x :: xs => Goldilocks.one :: (enc x ++ cellListEnc enc xs)

def cellListDec {α : Type} (dec : List Goldilocks → Option (α × List Goldilocks)) :
    Nat → List Goldilocks → Option (List α × List Goldilocks)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, m :: cs =>
    if m = Goldilocks.zero then some ([], cs)
    else if m = Goldilocks.one then cellBind2 dec (cellListDec dec fuel) List.cons cs
    else none

private theorem cellListEnc_length_gt {α : Type} (enc : α → List Goldilocks) :
    ∀ (xs : List α), xs.length < (cellListEnc enc xs).length
  | [] => Nat.zero_lt_succ _
  | x :: xs => by
    have ih := cellListEnc_length_gt enc xs
    show xs.length + 1 < (enc x ++ cellListEnc enc xs).length + 1
    rw [List.length_append]
    exact Nat.succ_lt_succ (Nat.lt_of_lt_of_le ih (Nat.le_add_left _ _))

private theorem cellListDec_enc {α : Type} (c : CellCodec α) :
    ∀ (xs : List α) (fuel : Nat) (rest : List Goldilocks), xs.length < fuel →
      cellListDec c.dec fuel (cellListEnc c.enc xs ++ rest) = some (xs, rest)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | [], f + 1, rest, _ => by
    show cellListDec c.dec (f + 1) (Goldilocks.zero :: rest) = some ([], rest)
    rw [cellListDec, ite_eq_left rfl]
  | x :: xs, f + 1, rest, h => by
    have ih := cellListDec_enc c xs f rest (Nat.lt_of_succ_lt_succ h)
    have hb := cellBind2_eq (k := List.cons) (c.dec_enc x (cellListEnc c.enc xs ++ rest)) ih
    have e : (c.enc x ++ cellListEnc c.enc xs) ++ rest =
        c.enc x ++ (cellListEnc c.enc xs ++ rest) := List.append_assoc _ _ _
    show cellListDec c.dec (f + 1)
      (Goldilocks.one :: ((c.enc x ++ cellListEnc c.enc xs) ++ rest)) = some (x :: xs, rest)
    rw [e, cellListDec, ite_eq_right goldilocks_one_ne_zero, ite_eq_left rfl]
    exact hb

private theorem cellListDec_canonical {α : Type} (c : CellCodec α) :
    ∀ (fuel : Nat) (cs : List Goldilocks) (xs : List α) (rest : List Goldilocks),
      cellListDec c.dec fuel cs = some (xs, rest) → cs = cellListEnc c.enc xs ++ rest
  | 0, _, _, _, h => by rw [cellListDec] at h; cases h
  | _ + 1, [], _, _, h => by rw [cellListDec] at h; cases h
  | fuel + 1, m :: tl, xs, rest, h => by
    rw [cellListDec] at h
    by_cases hm0 : m = Goldilocks.zero
    · rw [ite_eq_left hm0] at h
      obtain ⟨hx, hr⟩ := Prod.mk.inj (Option.some.inj h)
      rw [← hx, ← hr, hm0]
      rfl
    · rw [ite_eq_right hm0] at h
      by_cases hm1 : m = Goldilocks.one
      · rw [ite_eq_left hm1] at h
        obtain ⟨x, ys, r1, h1, h2, hk⟩ := cellBind2_some h
        rw [← hk, hm1, c.enc_dec tl x r1 h1, cellListDec_canonical c fuel r1 ys rest h2]
        exact (congrArg (List.cons Goldilocks.one) (List.append_assoc _ _ _)).symm
      · rw [ite_eq_right hm1] at h; cases h

/-- Continuation-marked list: each element is preceded by a cell `1`, and the list ends with a
    cell `0`. -/
def cellListOf {α : Type} (c : CellCodec α) : CellCodec (List α) where
  enc := cellListEnc c.enc
  dec := fun cs => cellListDec c.dec cs.length cs
  dec_enc := fun xs rest =>
    cellListDec_enc c xs _ rest
      (Nat.lt_of_lt_of_le (cellListEnc_length_gt c.enc xs)
        (by rw [List.length_append]; exact Nat.le_add_right _ _))
  enc_dec := fun cs xs rest h => cellListDec_canonical c cs.length cs xs rest h

/-- Radix of the natural-number cell encoding: `p - 1`. -/
def cellNatRadix : Nat := goldilocksPrime - 1

/-- The cell value `p - 1`, used as the carry marker of `cellNatEnc`. -/
def goldilocksTop : Goldilocks := ⟨goldilocksPrime - 1, by decide⟩

def cellNatEncAux : Nat → Goldilocks → List Goldilocks
  | 0, r => [r]
  | q + 1, r => goldilocksTop :: cellNatEncAux q r

/-- `n = q * (p - 1) + r` is encoded as `q` carry cells `p - 1` followed by the cell `r`. -/
def cellNatEnc (n : Nat) : List Goldilocks :=
  cellNatEncAux (n / cellNatRadix) (Goldilocks.ofNat (n % cellNatRadix))

def cellNatDec : List Goldilocks → Option (Nat × List Goldilocks)
  | [] => none
  | c :: cs =>
    if c = goldilocksTop then
      match cellNatDec cs with
      | none => none
      | some (n, r) => some (n + cellNatRadix, r)
    else some (c.val, cs)

private theorem goldilocks_val_lt_radix_of_ne_top {c : Goldilocks} (h : c ≠ goldilocksTop) :
    c.val < cellNatRadix := by
  have hne : c.val ≠ cellNatRadix := fun e => h (Goldilocks.ext e)
  have hM : cellNatRadix + 1 = goldilocksPrime := by decide
  have hlt : c.val < cellNatRadix + 1 := by rw [hM]; exact c.isLt
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne

private theorem cellNatDec_encAux (r : Goldilocks) (hr : r ≠ goldilocksTop) :
    ∀ (q : Nat) (rest : List Goldilocks),
      cellNatDec (cellNatEncAux q r ++ rest) = some (q * cellNatRadix + r.val, rest)
  | 0, rest => by
    show cellNatDec (r :: rest) = some (0 * cellNatRadix + r.val, rest)
    rw [cellNatDec, ite_eq_right hr, Nat.zero_mul, Nat.zero_add]
  | q + 1, rest => by
    have ih := cellNatDec_encAux r hr q rest
    show cellNatDec (goldilocksTop :: (cellNatEncAux q r ++ rest)) =
      some ((q + 1) * cellNatRadix + r.val, rest)
    rw [cellNatDec, ite_eq_left rfl, ih]
    exact congrArg (fun n => some (n, rest))
      (show q * cellNatRadix + r.val + cellNatRadix = (q + 1) * cellNatRadix + r.val by
        rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_right_comm _ _ _)

private theorem cellNatDec_enc (n : Nat) (rest : List Goldilocks) :
    cellNatDec (cellNatEnc n ++ rest) = some (n, rest) := by
  have hpos : 0 < cellNatRadix := by decide
  have hmod : n % cellNatRadix < cellNatRadix := Nat.mod_lt n hpos
  have hRp : cellNatRadix < goldilocksPrime := by decide
  have hval : (Goldilocks.ofNat (n % cellNatRadix)).val = n % cellNatRadix :=
    Nat.mod_eq_of_lt (Nat.lt_trans hmod hRp)
  have hne : Goldilocks.ofNat (n % cellNatRadix) ≠ goldilocksTop := by
    intro e
    have e' : (Goldilocks.ofNat (n % cellNatRadix)).val = cellNatRadix :=
      congrArg Goldilocks.val e
    rw [hval] at e'
    rw [e'] at hmod
    exact Nat.lt_irrefl _ hmod
  have h := cellNatDec_encAux _ hne (n / cellNatRadix) rest
  rw [hval, Nat.div_add_mod'] at h
  exact h

private theorem cellNatDec_canonical :
    ∀ (cs : List Goldilocks) (n : Nat) (rest : List Goldilocks),
      cellNatDec cs = some (n, rest) → cs = cellNatEnc n ++ rest
  | [], _, _, h => by rw [cellNatDec] at h; cases h
  | c :: tl, n, rest, h => by
    have hpos : 0 < cellNatRadix := by decide
    rw [cellNatDec] at h
    by_cases hc : c = goldilocksTop
    · rw [ite_eq_left hc] at h
      cases hd : cellNatDec tl with
      | none => rw [hd] at h; cases h
      | some p =>
        obtain ⟨n', r⟩ := p
        rw [hd] at h
        obtain ⟨hn, hr⟩ := Prod.mk.inj (Option.some.inj h)
        rw [hc, cellNatDec_canonical tl n' r hd, ← hn, ← hr]
        show goldilocksTop ::
            (cellNatEncAux (n' / cellNatRadix) (Goldilocks.ofNat (n' % cellNatRadix)) ++ r) =
          cellNatEncAux ((n' + cellNatRadix) / cellNatRadix)
            (Goldilocks.ofNat ((n' + cellNatRadix) % cellNatRadix)) ++ r
        rw [Nat.add_div_right n' hpos, Nat.add_mod_right]
        rfl
    · rw [ite_eq_right hc] at h
      obtain ⟨hn, hr⟩ := Prod.mk.inj (Option.some.inj h)
      have hlt := goldilocks_val_lt_radix_of_ne_top hc
      have hc' : Goldilocks.ofNat c.val = c := Goldilocks.ext (Nat.mod_eq_of_lt c.isLt)
      rw [← hn, ← hr]
      show c :: tl =
        cellNatEncAux (c.val / cellNatRadix) (Goldilocks.ofNat (c.val % cellNatRadix)) ++ tl
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hc']
      rfl

/-- Unbounded natural numbers in radix `p - 1` with unary carry cells. -/
def cellNat : CellCodec Nat where
  enc := cellNatEnc
  dec := cellNatDec
  dec_enc := cellNatDec_enc
  enc_dec := cellNatDec_canonical

def cellCodecLane4 : CellCodec Lane4 :=
  cellIso (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld cellFld)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun l => (l.x0, l.x1, l.x2, l.x3))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecDigest5 : CellCodec Digest5 :=
  cellIso (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld cellFld))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun d => (d.limb0, d.limb1, d.limb2, d.limb3, d.limb4))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecState12 : CellCodec Poseidon2State12 :=
  cellIso (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 cellCodecLane4))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun s => (s.b0, s.b1, s.b2))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecPerm : CellCodec Poseidon2PermWitness :=
  cellIso
    (cellSeq cellCodecState12 (cellSeq (cellListOf cellCodecState12)
      (cellSeq (cellListOf cellFld) (cellSeq (cellListOf cellCodecState12) cellCodecState12))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.input, w.initExtSbox, w.intSbox, w.termExtSbox, w.output))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecLimb63 : CellCodec Limb63DecompWitness :=
  cellIso (cellSeq cellFld (cellSeq (cellListOf cellFld) cellFld))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.limbVal, w.digits, w.topBit))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsg5Decomp : CellCodec Hmsg5DecompWitness :=
  cellIso
    (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63
      (cellSeq cellCodecLimb63 cellCodecLimb63))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.l0, w.l1, w.l2, w.l3, w.l4))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecUnaryChain : CellCodec UnaryWotsChainWitness :=
  cellIso
    (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld (cellSeq cellCodecLane4
      (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 (cellSeq cellCodecLane4
        (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecPerm)))))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2⟩)
    (fun w => (w.act0, w.act1, w.act2, w.sigVal, w.s1, w.s2, w.endVal, w.perm0, w.perm1, w.perm2))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecMerkleLevel : CellCodec MerkleLevelWitness :=
  cellIso
    (cellSeq cellFld (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 (cellSeq cellCodecLane4
      (cellSeq cellCodecLane4 (cellSeq cellCodecPerm cellCodecPerm))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2⟩)
    (fun w => (w.dirBit, w.sibling, w.leftChild, w.rightChild, w.parent, w.perm0, w.perm1))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecSponge : CellCodec SpongeAbsorbWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq (cellListOf cellCodecPerm)
      (cellSeq cellCodecPerm cellCodecLane4)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.initPerm, w.pairPerms, w.finalPerm, w.outDigest))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsgStateful : CellCodec HmsgStatefulTraceWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecDigest5)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.perm2, w.outMsg))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsgDetTree : CellCodec HmsgDetTreeTraceWitness :=
  cellIso (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecDigest5))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.outMsg))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecWotsLayer : CellCodec WotsLayerTraceWitness :=
  cellIso
    (cellSeq cellNat (cellSeq cellCodecHmsg5Decomp (cellSeq (cellListOf cellCodecUnaryChain)
      (cellSeq cellCodecSponge (cellSeq (cellListOf cellCodecMerkleLevel) cellCodecLane4)))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩)
    (fun w => (w.tswCtr, w.decomp, w.chains, w.pkSponge, w.merkle, w.rootOut))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecUpperNode : CellCodec UpperLayerTraceNode :=
  cellIso (cellSeq cellCodecHmsgDetTree cellCodecWotsLayer)
    (fun t => ⟨t.1, t.2⟩)
    (fun w => (w.detHmsg, w.wotsStep))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecForsOpening : CellCodec ForsOpeningTraceWitness :=
  cellIso
    (cellSeq cellCodecLane4 (cellSeq cellCodecPerm
      (cellSeq (cellListOf cellCodecMerkleLevel) cellCodecLane4)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.secretVal, w.leafPerm, w.merkle, w.treeRoot))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecForsAndRecover : CellCodec ForsAndRecoverTraceWitness :=
  cellIso (cellSeq (cellListOf cellCodecForsOpening) (cellSeq cellCodecSponge cellCodecLane4))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.openings, w.rootsSponge, w.forsPkOut))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecXof : CellCodec StatelessXofTraceWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq cellCodecPerm (cellSeq cellCodecLimb63
      (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63
        (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 cellCodecLimb63))))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.lim0, w.lim1, w.lim2, w.lim3, w.lim4, w.lim5, w.lim6))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecProfile : CellCodec AggSigProfile :=
  cellIso (cellSum cellUnit cellUnit)
    (fun s => match s with
      | .inl _ => AggSigProfile.xmssPoseidon2
      | .inr _ => AggSigProfile.corduroyPoseidon2)
    (fun p => match p with
      | .xmssPoseidon2 => Sum.inl ()
      | .corduroyPoseidon2 => Sum.inr ())
    (fun p => by cases p <;> rfl)
    (fun s => by cases s <;> rfl)

def cellCodecModeTrace : CellCodec AggSignerModeTrace :=
  cellIso
    (cellSum (cellSeq cellNat cellCodecHmsgStateful)
      (cellSeq cellCodecXof (cellSeq cellCodecForsAndRecover cellCodecHmsgDetTree)))
    (fun s => match s with
      | .inl t => AggSignerModeTrace.stateful t.1 t.2
      | .inr t => AggSignerModeTrace.stateless t.1 t.2.1 t.2.2)
    (fun m => match m with
      | .stateful i h => Sum.inl (i, h)
      | .stateless x f h => Sum.inr (x, f, h))
    (fun m => by cases m <;> rfl)
    (fun s => by cases s <;> rfl)

/-- Canonical cell stream of one signer's witness block: profile selector, `rRand`, the
    stateful / stateless mode trace, the bottom WOTS layer, and the upper hypertree layers. -/
def aggSignerWitnessCodec : CellCodec AggSignerTraceWitness :=
  cellIso
    (cellSeq cellCodecProfile (cellSeq cellCodecLane4 (cellSeq cellCodecModeTrace
      (cellSeq cellCodecWotsLayer (cellListOf cellCodecUpperNode)))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.profile, w.rRand, w.modeTrace, w.layer0, w.upperNodes))
    (fun _ => rfl) (fun _ => rfl)

/-- Witness block committed in a row: the cells from column `14` on (columns `0..13` are the
    boundary columns of `expectedBoundaryCols`) must be exactly one canonical witness encoding,
    with no trailing cell. -/
def decodeRowWitness (row : List Goldilocks) : Option AggSignerTraceWitness :=
  match aggSignerWitnessCodec.dec (row.drop 14) with
  | some (w, []) => some w
  | _ => none

/-- A row decodes to `w` exactly when its cells from column `14` on are the encoding of `w`. -/
