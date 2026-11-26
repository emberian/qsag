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
theorem decodeRowWitness_eq_some_iff (row : List Goldilocks) (w : AggSignerTraceWitness) :
    decodeRowWitness row = some w ↔ row.drop 14 = aggSignerWitnessCodec.enc w := by
  constructor
  · intro h
    unfold decodeRowWitness at h
    cases hd : aggSignerWitnessCodec.dec (row.drop 14) with
    | none => rw [hd] at h; cases h
    | some p =>
      obtain ⟨w', r⟩ := p
      rw [hd] at h
      cases r with
      | cons _ _ => cases h
      | nil =>
        have hw : w' = w := Option.some.inj h
        have e := aggSignerWitnessCodec.enc_dec _ _ _ hd
        rw [List.append_nil, hw] at e
        exact e
  · intro h
    have hd := aggSignerWitnessCodec.dec_enc w []
    rw [List.append_nil, ← h] at hd
    simp only [decodeRowWitness, hd]

/-- **Deterministic row projection.** Decodes the witness block of each of the first `K` rows;
    fails if a row is missing or does not carry a canonical witness encoding. -/
def extractSignerWitnessesFromRows :
    Nat → List (List Goldilocks) → Option (List AggSignerTraceWitness)
  | 0, _ => some []
  | _ + 1, [] => none
  | k + 1, row :: rows =>
    match decodeRowWitness row with
    | none => none
    | some w =>
      match extractSignerWitnessesFromRows k rows with
      | none => none
      | some ws => some (w :: ws)

/-- Row gate of one active row, a function of the committed row alone: the boundary columns
    `0..13` equal `expectedBoundaryCols`, the remaining cells decode to a witness block, and
    every transition residual of that block vanishes. -/
def committedRowOk (geom : AggSigGeometry) (msg : List UInt8) (pk : AggValidatorPk)
    (row : List Goldilocks) : Bool :=
  decide (row.take 14 = expectedBoundaryCols pk msg) &&
  match decodeRowWitness row with
  | none => false
  | some w => allZeroGoldilocks (signerTraceResiduals geom pk msg w)

def committedActiveRowsOk (geom : AggSigGeometry) (msg : List UInt8) :
    List AggValidatorPk → List (List Goldilocks) → Bool
  | [], padRows => allZeroGoldilocks (padRows.flatMap id)
  | _ :: _, [] => false
  | pk :: pks, row :: rows =>
    committedRowOk geom msg pk row && committedActiveRowsOk geom msg pks rows

/-- All row-gate and boundary constraints as a predicate on the committed `rows` only: no
    witness is supplied beside the rows. -/
def committedRowsSatisfyAllConstraints (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks)) : Bool :=
  stmt.wellFormed && decide (rows.length = 2 ^ stmt.logRows) &&
  committedActiveRowsOk stmt.geom stmt.msg stmt.committeePks rows

private theorem committedRowOk_unpack {geom : AggSigGeometry} {msg : List UInt8}
    {pk : AggValidatorPk} {row : List Goldilocks}
    (h : committedRowOk geom msg pk row = true) :
    row.take 14 = expectedBoundaryCols pk msg ∧
    ∃ w, decodeRowWitness row = some w ∧
      allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true := by
  unfold committedRowOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hT, hM⟩ := h
  refine ⟨hT, ?_⟩
  cases hd : decodeRowWitness row with
  | none => rw [hd] at hM; cases hM
  | some w => rw [hd] at hM; exact ⟨w, rfl, hM⟩

private theorem committedRowOk_intro {geom : AggSigGeometry} {msg : List UInt8}
    {pk : AggValidatorPk} {row : List Goldilocks} {w : AggSignerTraceWitness}
    (hT : row.take 14 = expectedBoundaryCols pk msg)
    (hd : decodeRowWitness row = some w)
    (hZ : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    committedRowOk geom msg pk row = true := by
  unfold committedRowOk
  rw [hd, decide_eq_true hT]
  exact hZ

private theorem committedRow_boundary_gates_vanish {pk : AggValidatorPk} {msg : List UInt8}
    {row : List Goldilocks} (hT : row.take 14 = expectedBoundaryCols pk msg) :
    allZeroGoldilocks (evalRowGateList (boundaryRowGates pk msg) row) = true := by
  have h := boundaryGatesFrom_exact 0 (expectedBoundaryCols pk msg) [] (row.drop 14) rfl
  have hRow : [] ++ expectedBoundaryCols pk msg ++ row.drop 14 = row := by
    rw [List.nil_append, ← hT]
    exact List.take_append_drop 14 row
  rw [hRow] at h
  exact h

private theorem extractSignerWitnesses_succ_cons {k : Nat} {row : List Goldilocks}
    {rows : List (List Goldilocks)} {ws : List AggSignerTraceWitness}
    (h : extractSignerWitnessesFromRows (k + 1) (row :: rows) = some ws) :
    ∃ w wt, decodeRowWitness row = some w ∧
      extractSignerWitnessesFromRows k rows = some wt ∧ ws = w :: wt := by
  rw [extractSignerWitnessesFromRows] at h
  cases hd : decodeRowWitness row with
  | none => rw [hd] at h; cases h
  | some w =>
    rw [hd] at h
    dsimp only at h
    cases hE : extractSignerWitnessesFromRows k rows with
    | none => rw [hE] at h; cases h
    | some wt =>
      rw [hE] at h
      exact ⟨w, wt, rfl, rfl, (Option.some.inj h).symm⟩

private theorem committedActiveRowsOk_extract (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (rows : List (List Goldilocks)),
      committedActiveRowsOk geom msg pks rows = true →
      ∃ ws, extractSignerWitnessesFromRows pks.length rows = some ws ∧
        ws.length = pks.length ∧
        ∀ (k : Nat) (hk : k < pks.length) (hkW : k < ws.length),
          (rows.getD k []).take 14 = expectedBoundaryCols (pks[k]'hk) msg ∧
          decodeRowWitness (rows.getD k []) = some (ws[k]'hkW) ∧
          allZeroGoldilocks (signerTraceResiduals geom (pks[k]'hk) msg (ws[k]'hkW)) = true
  | [], _, _ => ⟨[], rfl, rfl, fun _ hk _ => absurd hk (Nat.not_lt_zero _)⟩
  | _ :: _, [], h => by rw [committedActiveRowsOk] at h; cases h
  | pk :: pks, row :: rows, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    obtain ⟨hRow, hRest⟩ := h
    obtain ⟨hT, w, hd, hZ⟩ := committedRowOk_unpack hRow
    obtain ⟨ws, hE, hLen, hA⟩ := committedActiveRowsOk_extract geom msg pks rows hRest
    refine ⟨w :: ws, ?_, congrArg Nat.succ hLen, ?_⟩
    · show extractSignerWitnessesFromRows (pks.length + 1) (row :: rows) = some (w :: ws)
      simp only [extractSignerWitnessesFromRows, hd, hE]
    · intro k hk hkW
      cases k with
      | zero => exact ⟨hT, hd, hZ⟩
      | succ k' => exact hA k' (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hkW)

private theorem committedActiveRowsOk_at (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (rows : List (List Goldilocks)) (k : Nat)
      (hk : k < pks.length),
      committedActiveRowsOk geom msg pks rows = true →
      committedRowOk geom msg (pks[k]'hk) (rows.getD k []) = true
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => by rw [committedActiveRowsOk] at h; cases h
  | _ :: _, _ :: _, 0, _, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    exact h.1
  | _ :: pks, _ :: rows, k + 1, hk, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    exact committedActiveRowsOk_at geom msg pks rows k (Nat.lt_of_succ_lt_succ hk) h.2

private theorem extractSignerWitnesses_unique :
    ∀ (K : Nat) (rows : List (List Goldilocks)) (ws ws' : List AggSignerTraceWitness),
      extractSignerWitnessesFromRows K rows = some ws →
      ws'.length = K →
      (∀ (k : Nat) (hk : k < ws'.length),
        (rows.getD k []).drop 14 = aggSignerWitnessCodec.enc (ws'[k]'hk)) →
      ws' = ws
  | 0, _, _, _, hE, hLen, _ => by
    rw [extractSignerWitnessesFromRows] at hE
    rw [List.eq_nil_of_length_eq_zero hLen]
    exact Option.some.inj hE
  | _ + 1, [], _, _, hE, _, _ => by rw [extractSignerWitnessesFromRows] at hE; cases hE
  | _ + 1, _ :: _, _, [], _, hLen, _ => by cases hLen
  | K + 1, row :: rows, ws, w' :: ws', hE, hLen, hCells => by
    obtain ⟨w, wt, hd, hEt, hws⟩ := extractSignerWitnesses_succ_cons hE
    have hd' : decodeRowWitness row = some w' :=
      (decodeRowWitness_eq_some_iff row w').mpr (hCells 0 (Nat.zero_lt_succ _))
    have hw : w' = w := Option.some.inj (hd'.symm.trans hd)
    have ih := extractSignerWitnesses_unique K rows wt ws' hEt (Nat.succ.inj hLen)
      (fun k hk => hCells (k + 1) (Nat.succ_lt_succ hk))
    rw [hws, hw, ih]

/-- **Committed rows determine valid witnesses (`committed_rows_extract_valid_witnesses`).**
    If the committed `rows` alone satisfy every row-gate and boundary constraint, then the row
    projection `extractSignerWitnessesFromRows` returns `K` witness blocks; on row `k` the
    boundary gates vanish, the transition residuals of the extracted block vanish, and the block
    yields a signature accepted by `verifyAggNativeSig` for committee key `k`; and any other
    list of `K` witness blocks whose encodings occupy the witness cells of the same rows is
    equal to the extracted one. -/
theorem committed_rows_extract_valid_witnesses (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks))
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true) :
    ∃ ws : List AggSignerTraceWitness,
      extractSignerWitnessesFromRows stmt.committeePks.length rows = some ws ∧
      ws.length = stmt.committeePks.length ∧
      (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
        allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
          (rows.getD k [])) = true ∧
        allZeroGoldilocks
          (signerTraceResiduals stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (ws[k]'hkW)) = true ∧
        verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
          (extractSignerWitnessSig (ws[k]'hkW)) = true) ∧
      (∀ ws' : List AggSignerTraceWitness,
        ws'.length = stmt.committeePks.length →
        (∀ (k : Nat) (hk : k < ws'.length),
          (rows.getD k []).drop 14 = aggSignerWitnessCodec.enc (ws'[k]'hk)) →
        ws' = ws) := by
  unfold committedRowsSatisfyAllConstraints at hSat
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSat
  obtain ⟨⟨_, _⟩, hAct⟩ := hSat
  obtain ⟨ws, hE, hWsLen, hBody⟩ :=
    committedActiveRowsOk_extract stmt.geom stmt.msg stmt.committeePks rows hAct
  refine ⟨ws, hE, hWsLen, ?_, ?_⟩
  · intro k hkP hkW
    obtain ⟨hT, _, hZ⟩ := hBody k hkP hkW
    exact ⟨committedRow_boundary_gates_vanish hT, hZ,
      signerTraceResiduals_sound stmt.geom (stmt.committeePks[k]'hkP) stmt.msg _ hZ⟩
  · intro ws' hLen' hCells
    exact extractSignerWitnesses_unique _ rows ws ws' hE hLen' hCells

private theorem committedRowsSatisfy_row_at (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks)) (k : Nat) (hk : k < stmt.committeePks.length)
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true) :
    committedRowOk stmt.geom stmt.msg (stmt.committeePks[k]'hk) (rows.getD k []) = true := by
  unfold committedRowsSatisfyAllConstraints at hSat
  simp only [Bool.and_eq_true] at hSat
  exact committedActiveRowsOk_at stmt.geom stmt.msg stmt.committeePks rows k hk hSat.2

/-- **`#tooth`: a tampered committed row breaks a gate or the binding.** Start from committed
    rows that satisfy every constraint and change any cell of an active row `k`. Then either the
    tampered rows are rejected, or row `k` now decodes to a different witness block (which the
    row gates then check in place of the original one). No change to an active row leaves both
    acceptance and the bound witness intact. -/
theorem tooth_tampered_committed_row_breaks_gate_or_binding (stmt : AggArithPublicStmt)
    (rows rows' : List (List Goldilocks)) (k : Nat) (hk : k < stmt.committeePks.length)
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true)
    (hTamper : rows'.getD k [] ≠ rows.getD k []) :
    committedRowsSatisfyAllConstraints stmt rows' = false ∨
    decodeRowWitness (rows'.getD k []) ≠ decodeRowWitness (rows.getD k []) := by
  cases hV : committedRowsSatisfyAllConstraints stmt rows' with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr (fun hEq => hTamper ?_)
    obtain ⟨hT, w, hd, _⟩ := committedRowOk_unpack (committedRowsSatisfy_row_at stmt rows k hk hSat)
    obtain ⟨hT', w', hd', _⟩ :=
      committedRowOk_unpack (committedRowsSatisfy_row_at stmt rows' k hk hV)
    have hw : w' = w := Option.some.inj ((hd'.symm.trans hEq).trans hd)
    have hD := (decodeRowWitness_eq_some_iff _ w).mp hd
    have hD' := (decodeRowWitness_eq_some_iff _ w').mp hd'
    rw [hw] at hD'
    rw [← List.take_append_drop 14 (rows'.getD k []), ← List.take_append_drop 14 (rows.getD k []),
      hT, hT', hD, hD']

private theorem expectedBoundaryCols_length (pk : AggValidatorPk) (msg : List UInt8) :
    (expectedBoundaryCols pk msg).length = 14 := by
  simp only [expectedBoundaryCols.public_eqs]
  rfl

private theorem committedRowOk_honest (geom : AggSigGeometry) (msg : List UInt8)
    (pk : AggValidatorPk) (w : AggSignerTraceWitness)
    (hZ : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    committedRowOk geom msg pk (expectedBoundaryCols pk msg ++ aggSignerWitnessCodec.enc w) =
      true := by
  have hLen := expectedBoundaryCols_length pk msg
  exact committedRowOk_intro (List.take_left' hLen)
    ((decodeRowWitness_eq_some_iff _ w).mpr (List.drop_left' hLen)) hZ

/-- Honest committed rows: row `k` is the 14 boundary columns of validator `k` followed by the
    canonical cell stream of its honest witness block; padding rows are zero. -/
def buildCommittedRows (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature) :
    List (List Goldilocks) :=
  (stmt.committeePks.zip sigs).map (fun (pk, sig) =>
    expectedBoundaryCols pk stmt.msg ++
      aggSignerWitnessCodec.enc (buildHonestSignerTraceWitness stmt.geom pk stmt.msg sig)) ++
  List.replicate (2 ^ stmt.logRows - stmt.committeePks.length)
    (List.replicate 14 Goldilocks.zero)

private theorem committedActiveRowsOk_honest (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (sigs : List AggNativeSignature)
      (padRows : List (List Goldilocks)),
      pks.length = sigs.length →
      allZeroGoldilocks (padRows.flatMap id) = true →
      (∀ (k : Nat) (hkP : k < pks.length) (hkS : k < sigs.length),
        verifyAggNativeSig geom (pks[k]'hkP) msg (sigs[k]'hkS) = true) →
      committedActiveRowsOk geom msg pks
        ((pks.zip sigs).map (fun (pk, sig) =>
          expectedBoundaryCols pk msg ++
            aggSignerWitnessCodec.enc (buildHonestSignerTraceWitness geom pk msg sig)) ++
          padRows) = true
  | [], [], _, _, hPad, _ => hPad
  | _ :: _, [], _, hLen, _, _ => by cases hLen
  | [], _ :: _, _, hLen, _, _ => by cases hLen
  | pk :: pks, sig :: sigs, padRows, hLen, hPad, hAll => by
    have hVer0 : verifyAggNativeSig geom pk msg sig = true :=
      hAll 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    have hSigZ := (signerTraceResiduals_complete geom pk msg sig hVer0).2
    have ih := committedActiveRowsOk_honest geom msg pks sigs padRows (Nat.succ.inj hLen) hPad
      (fun k hkP hkS => hAll (k + 1) (Nat.succ_lt_succ hkP) (Nat.succ_lt_succ hkS))
    have hRow := committedRowOk_honest geom msg pk
      (buildHonestSignerTraceWitness geom pk msg sig) hSigZ
    simp only [List.zip_cons_cons, List.map_cons, List.cons_append, committedActiveRowsOk,
      Bool.and_eq_true]
    exact ⟨hRow, ih⟩

/-- **Completeness of the row-committed layout.** For valid signatures of all `K` committee
    keys, the honest committed rows satisfy every row-only constraint. -/
theorem buildCommittedRows_satisfy_constraints
    (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature)
    (hWf : stmt.wellFormed = true)
    (hLen : sigs.length = stmt.committeePks.length)
    (hAll : ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true) :
    committedRowsSatisfyAllConstraints stmt (buildCommittedRows stmt sigs) = true := by
  have hKLePow : stmt.committeePks.length ≤ 2 ^ stmt.logRows := by
    unfold AggArithPublicStmt.wellFormed at hWf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    exact hWf.1.2
  have hRowsLen : (buildCommittedRows stmt sigs).length = 2 ^ stmt.logRows := by
    unfold buildCommittedRows
    rw [List.length_append, List.length_map, List.length_zip, List.length_replicate, hLen,
      Nat.min_self]
    exact Nat.add_sub_of_le hKLePow
  have hAct := committedActiveRowsOk_honest stmt.geom stmt.msg stmt.committeePks sigs
    (List.replicate (2 ^ stmt.logRows - stmt.committeePks.length)
      (List.replicate 14 Goldilocks.zero))
    hLen.symm (allZero_flatMap_replicate_zeros _ 14) hAll
  unfold committedRowsSatisfyAllConstraints
  rw [hWf, decide_eq_true hRowsLen]
  exact hAct

/-- Inhabitedness witness for the row-committed layout: for the audit key and any valid signing
    counters, the honest committed rows satisfy the row-only constraints, so the hypotheses of
    `committed_rows_extract_valid_witnesses` and of the `#tooth` are jointly satisfiable. -/
theorem inhabited_committed_row_extraction :
    let pk0 := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let stmt : AggArithPublicStmt :=
      { geom := xmssPoseidon2Geom, msg := auditMsg, committeePks := [pk0], logRows := 1 }
    stmt.wellFormed = true ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0),
      let sig0 := signAggNative xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0
                    ctrs.layer0Ctr ctrs.upperCtrs
      committedRowsSatisfyAllConstraints stmt (buildCommittedRows stmt [sig0]) = true) := by
  intro pk0 stmt
  have hGeomWf : xmssPoseidon2Geom.wellFormed = true := deployedAggGeometries_wellFormed.1
  have hPkProf : (pk0.profile == xmssPoseidon2Geom.profile) = true := rfl
  have hStmtWf : stmt.wellFormed = true := by
    unfold AggArithPublicStmt.wellFormed
    dsimp only [stmt]
    simp [hGeomWf, hPkProf]
  refine ⟨hStmtWf, fun ctrs => ?_⟩
  intro sig0
  have hVer0 := aggNativeSig_completeness xmssPoseidon2Geom auditSkSeed auditPkSeed
    auditMsg auditRRand 0 hGeomWf ctrs
  refine buildCommittedRows_satisfy_constraints stmt [sig0] hStmtWf rfl ?_
  intro k hkP _
  have hk0 : k = 0 := by simp [stmt] at hkP; omega
  subst hk0
  exact hVer0

/-! ### Execution trace: committed rows only -/

/-- Execution trace on `{0, 1}^logRows`: the committed rows and nothing else. Every witness
    block the constraints speak about is read out of `rows`. -/
structure AggExecutionTrace where
  rows : List (List Goldilocks)
  deriving DecidableEq, Repr

/-- The per-validator witness blocks of a trace, as a function of its committed rows. -/
def AggExecutionTrace.signerWitnesses (stmt : AggArithPublicStmt) (tr : AggExecutionTrace) :
    Option (List AggSignerTraceWitness) :=
  extractSignerWitnessesFromRows stmt.committeePks.length tr.rows

/-- Every row-gate and boundary constraint of the trace: `stmt.wellFormed`, exactly
    `2^stmt.logRows` rows, on each active row `k < K` the 14 boundary columns pinned to
    `(profileFieldTag, pkSeed, pkRoot, mu)` and the transition residuals of the witness block
    decoded from that row, and all-zero padding rows. -/
def traceSatisfiesAllConstraints (stmt : AggArithPublicStmt) (tr : AggExecutionTrace) : Bool :=
  committedRowsSatisfyAllConstraints stmt tr.rows

/-- The canonical honest execution trace of `K` valid `AggNativeSignature`s. -/
def buildHonestAggExecutionTrace (stmt : AggArithPublicStmt)
    (sigs : List AggNativeSignature) : AggExecutionTrace :=
  { rows := buildCommittedRows stmt sigs }

/-- All-zero execution trace (`2^logRows` zero rows of `numCols` cells). -/
def zeroAggExecutionTrace (logRows numCols : Nat) : AggExecutionTrace :=
  { rows := List.replicate (2 ^ logRows) (List.replicate numCols Goldilocks.zero) }

/-- **Per-validator signature extractor.** From a trace satisfying every constraint, reads the
    witness block out of row `k` and returns the signature it encodes, accepted by
    `verifyAggNativeSig` for committee key `k`. -/
def extractValidCommitteeSigsFromTrace (stmt : AggArithPublicStmt) (tr : AggExecutionTrace)
    (hSat : traceSatisfiesAllConstraints stmt tr = true) :
    ∀ (k : Nat) (hk : k < stmt.committeePks.length),
      { sig : AggNativeSignature //
        verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hk) stmt.msg sig = true } :=
  fun k hk =>
    match hd : decodeRowWitness (tr.rows.getD k []) with
    | some w => ⟨extractSignerWitnessSig w, by
        obtain ⟨_, w', hd', hZ⟩ :=
          committedRowOk_unpack (committedRowsSatisfy_row_at stmt tr.rows k hk hSat)
        have hw : w' = w := Option.some.inj (hd'.symm.trans hd)
        rw [← hw]
        exact signerTraceResiduals_sound stmt.geom (stmt.committeePks[k]'hk) stmt.msg w' hZ⟩
    | none => False.elim (by
        obtain ⟨_, w', hd', _⟩ :=
          committedRowOk_unpack (committedRowsSatisfy_row_at stmt tr.rows k hk hSat)
        rw [hd] at hd'
        cases hd')

/-- **Honest execution trace completeness.** Whenever all `K` committee validators have valid
    `AggNativeSignature`s on `stmt.msg`, the honest trace satisfies every constraint. -/
theorem buildHonestAggExecutionTrace_satisfies_constraints
    (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature)
    (hWf : stmt.wellFormed = true)
    (hLen : sigs.length = stmt.committeePks.length)
    (hAll : ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true) :
    traceSatisfiesAllConstraints stmt (buildHonestAggExecutionTrace stmt sigs) = true :=
  buildCommittedRows_satisfy_constraints stmt sigs hWf hLen hAll

/-- **Row-constraint exactness (`trace_satisfies_constraints_iff_all_k_sigs_valid`).**
    1. Every trace whose constraints vanish has `2^logRows` rows, and its rows decode to `K`
       witness blocks whose boundary gates vanish and which encode signatures accepted by
       `verifyAggNativeSig` for `(stmt.msg, stmt.committeePks[k])`.
    2. A constraint-satisfying trace exists if and only if all `K` committee keys have valid
       `AggNativeSignature`s on `stmt.msg`. -/
theorem trace_satisfies_constraints_iff_all_k_sigs_valid
    (stmt : AggArithPublicStmt) (hWf : stmt.wellFormed = true) :
    (∀ (tr : AggExecutionTrace),
      traceSatisfiesAllConstraints stmt tr = true →
      tr.rows.length = 2 ^ stmt.logRows ∧
      ∃ ws : List AggSignerTraceWitness,
        tr.signerWitnesses stmt = some ws ∧
        ws.length = stmt.committeePks.length ∧
        (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
          allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
            (tr.rows.getD k [])) = true ∧
          verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
            (extractSignerWitnessSig (ws[k]'hkW)) = true)) ∧
    (Nonempty { tr : AggExecutionTrace // traceSatisfiesAllConstraints stmt tr = true } ↔
     Nonempty { sigs : List AggNativeSignature //
       sigs.length = stmt.committeePks.length ∧
       ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
         verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true }) := by
  have hSound : ∀ (tr : AggExecutionTrace),
      traceSatisfiesAllConstraints stmt tr = true →
      tr.rows.length = 2 ^ stmt.logRows ∧
      ∃ ws : List AggSignerTraceWitness,
        tr.signerWitnesses stmt = some ws ∧
        ws.length = stmt.committeePks.length ∧
        (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
          allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
            (tr.rows.getD k [])) = true ∧
          verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
            (extractSignerWitnessSig (ws[k]'hkW)) = true) := by
    intro tr hSat
    have hLen : tr.rows.length = 2 ^ stmt.logRows := by
      have h := hSat
      unfold traceSatisfiesAllConstraints committedRowsSatisfyAllConstraints at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    obtain ⟨ws, hE, hWsLen, hPer, _⟩ := committed_rows_extract_valid_witnesses stmt tr.rows hSat
    exact ⟨hLen, ws, hE, hWsLen, fun k hkP hkW => ⟨(hPer k hkP hkW).1, (hPer k hkP hkW).2.2⟩⟩
  refine ⟨hSound, ?_⟩
  constructor
  · rintro ⟨⟨tr, hSat⟩⟩
    obtain ⟨_, ws, _, hWLen, hPerK⟩ := hSound tr hSat
    let sigs := ws.map extractSignerWitnessSig
    refine ⟨⟨sigs, by simp [sigs, hWLen], fun k hkP hkS => ?_⟩⟩
    have hkW : k < ws.length := by simp [sigs] at hkS; exact hkS
    have hEqSig : sigs[k]'hkS = extractSignerWitnessSig (ws[k]'hkW) := by
      simp [sigs]
    rw [hEqSig]
    exact (hPerK k hkP hkW).2
  · rintro ⟨⟨sigs, hLen, hAll⟩⟩
    exact ⟨⟨buildHonestAggExecutionTrace stmt sigs,
      buildHonestAggExecutionTrace_satisfies_constraints stmt sigs hWf hLen hAll⟩⟩

/-- **`#tooth`: the all-zero trace is rejected (`tooth_zero_trace_rejected_for_any_pk`).** For
    every well-formed statement, with no assumption on `pkSeed`, `pkRoot`, `msg` or `numCols`,
    the all-zero rows fail: boundary gate `(row = 0, col = 0)` pins
    `profileFieldTag pk0.profile ∈ {1, 2} ≠ 0`. -/
theorem tooth_zero_trace_rejected_for_any_pk
    (stmt : AggArithPublicStmt) (numCols : Nat)
    (hWf : stmt.wellFormed = true) :
    traceSatisfiesAllConstraints stmt (zeroAggExecutionTrace stmt.logRows numCols) = false := by
  apply Bool.eq_false_iff.mpr
  intro hSat
  have hNonEmpty : stmt.committeePks ≠ [] := by
    unfold AggArithPublicStmt.wellFormed at hWf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hWf
    exact hWf.1.1.1.2
  have hk : 0 < stmt.committeePks.length := by
    cases hPks : stmt.committeePks with
    | nil => exact absurd hPks hNonEmpty
    | cons _ _ => exact Nat.zero_lt_succ _
  obtain ⟨hT, _⟩ := committedRowOk_unpack
    (committedRowsSatisfy_row_at stmt (zeroAggExecutionTrace stmt.logRows numCols).rows 0 hk hSat)
  have hB := committedRow_boundary_gates_vanish hT
  have hRowEq : (zeroAggExecutionTrace stmt.logRows numCols).rows.getD 0 [] =
      List.replicate numCols Goldilocks.zero := by
    dsimp only [zeroAggExecutionTrace]
    cases hPow : 2 ^ stmt.logRows with
    | zero => exact absurd hPow (Nat.ne_of_gt (Nat.two_pow_pos _))
    | succ m => rfl
  rw [hRowEq] at hB
  unfold boundaryRowGates at hB
  simp only [expectedBoundaryCols.public_eqs] at hB
  simp only [List.singleton_append] at hB
  have hCol0 := boundaryGatesFrom_zero_at_col0 (profileFieldTag _) _ _ hB
  rw [getD_zero_replicate_zero] at hCol0
  exact profileFieldTag_ne_zero _ hCol0.symm

/-- Inhabitedness witness for the row constraints: the audit statement is well formed, its
    all-zero trace is rejected, and the honest trace of any valid signing counters is accepted. -/
theorem inhabited_agg_arithmetization_pipeline :
    let pk0 := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let stmt : AggArithPublicStmt :=
      { geom := xmssPoseidon2Geom, msg := auditMsg, committeePks := [pk0], logRows := 1 }
    stmt.wellFormed = true ∧
    traceSatisfiesAllConstraints stmt (zeroAggExecutionTrace 1 14) = false ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0),
      let sig0 := signAggNative xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0
                    ctrs.layer0Ctr ctrs.upperCtrs
      traceSatisfiesAllConstraints stmt (buildHonestAggExecutionTrace stmt [sig0]) = true) := by
  intro pk0 stmt
  obtain ⟨hStmtWf, hHon⟩ := inhabited_committed_row_extraction
  exact ⟨hStmtWf, tooth_zero_trace_rejected_for_any_pk stmt 14 hStmtWf, hHon⟩

/-- A 32-byte digest. -/
abbrev CanopyDigest32 : Type := { b : ByteArray // b.data.toList.length = 32 }

/-- An explicit collision of a byte-string hash `H`: two distinct inputs with equal outputs,
    as data (a subtype of pairs), not as an existence statement. -/
@[expose] def ExtractedHashCollision (H : ByteArray → ByteArray) : Type :=
  { p : ByteArray × ByteArray // p.1 ≠ p.2 ∧ H p.1 = H p.2 }

/-- `pcs.rs:hash_merkle_internal` input frame: `0x00 || node_idx (4 bytes LE) || left || right`. -/
def canopyNodeFrame (nodeIdx : Nat) (l r : CanopyDigest32) : ByteArray :=
  ⟨⟨(0 : UInt8) ::
    ([leByte nodeIdx 1, leByte nodeIdx 256, leByte nodeIdx 65536, leByte nodeIdx 16777216] ++
      (l.1.data.toList ++ r.1.data.toList))⟩⟩

/-- `pcs.rs:hash_tree_root` input frame: `0x01 || log_leaves || top`. -/
def canopyRootFrame (logLeaves : Nat) (top : CanopyDigest32) : ByteArray :=
  ⟨⟨(1 : UInt8) :: leByte logLeaves 1 :: top.1.data.toList⟩⟩

/-- Node hash induced by `H` on `canopyNodeFrame`, for `H` with 32-byte output. -/
def canopyNodeHashOf (H : ByteArray → ByteArray) (hOut : ∀ x, (H x).data.toList.length = 32)
    (nodeIdx : Nat) (l r : CanopyDigest32) : CanopyDigest32 :=
  ⟨H (canopyNodeFrame nodeIdx l r), hOut _⟩

/-- Root hash induced by `H` on `canopyRootFrame`. -/
def canopyRootHashOf (H : ByteArray → ByteArray) (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (top : CanopyDigest32) : CanopyDigest32 :=
  ⟨H (canopyRootFrame logLeaves top), hOut _⟩

private theorem byteArray_eq_of_toList_eq {a b : ByteArray}
    (h : a.data.toList = b.data.toList) : a = b := by
  obtain ⟨⟨la⟩⟩ := a
  obtain ⟨⟨lb⟩⟩ := b
  have h' : la = lb := h
  rw [h']

private theorem canopyNodeFrame_inj {i : Nat} {l r l' r' : CanopyDigest32}
    (h : canopyNodeFrame i l r = canopyNodeFrame i l' r') : l = l' ∧ r = r' := by
  have h1 : (0 : UInt8) ::
      ([leByte i 1, leByte i 256, leByte i 65536, leByte i 16777216] ++
        (l.1.data.toList ++ r.1.data.toList)) =
      (0 : UInt8) ::
      ([leByte i 1, leByte i 256, leByte i 65536, leByte i 16777216] ++
        (l'.1.data.toList ++ r'.1.data.toList)) :=
    congrArg (fun b : ByteArray => b.data.toList) h
  have h2 := List.append_cancel_left (List.cons.inj h1).2
  obtain ⟨e1, e2⟩ := List.append_inj h2 (l.2.trans l'.2.symm)
  exact ⟨Subtype.ext (byteArray_eq_of_toList_eq e1), Subtype.ext (byteArray_eq_of_toList_eq e2)⟩

private theorem canopyRootFrame_inj {k : Nat} {top top' : CanopyDigest32}
    (h : canopyRootFrame k top = canopyRootFrame k top') : top = top' := by
  have h1 : (1 : UInt8) :: leByte k 1 :: top.1.data.toList =
      (1 : UInt8) :: leByte k 1 :: top'.1.data.toList :=
    congrArg (fun b : ByteArray => b.data.toList) h
  exact Subtype.ext (byteArray_eq_of_toList_eq (List.cons.inj (List.cons.inj h1).2).2)

/-- **Transcript-extracted hash collision.** For a byte-string hash `H` with 32-byte output, two
    accepted `CanopyMultiProof` openings of one index set against one commitment that differ in
    a leaf digest or a sibling yield an explicit pair of distinct frames with equal `H` digests,
    computed from the two transcripts by `extractCanopyCollision`. -/
def extractHashCollisionFromCanopyTranscripts (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (commitment : CanopyDigest32)
    (leaves₁ leaves₂ : List (Nat × CanopyDigest32)) (proof₁ proof₂ : List CanopyDigest32)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) : ExtractedHashCollision H :=
  match extractCanopyCollision (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut) logLeaves
      commitment leaves₁ leaves₂ proof₁ proof₂ hIdx hAcc₁ hAcc₂ hNe with
  | .inl c =>
    ⟨(canopyRootFrame logLeaves c.top₁, canopyRootFrame logLeaves c.top₂),
      fun h => c.ne (canopyRootFrame_inj h), congrArg Subtype.val c.eq⟩
  | .inr c =>
    ⟨(canopyNodeFrame c.idx c.l c.r, canopyNodeFrame c.idx c.l' c.r'),
      fun h => c.ne (by
        obtain ⟨e1, e2⟩ := canopyNodeFrame_inj h
        rw [e1, e2]),
      congrArg Subtype.val c.eq⟩

/-- Two distinct leaf assignments accepted against one `CanopyMultiProof` commitment yield an
    explicit `H` collision. -/
def extractHashCollisionFromDistinctLeaves (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (commitment : CanopyDigest32)
    (leaves₁ leaves₂ : List (Nat × CanopyDigest32)) (proof₁ proof₂ : List CanopyDigest32)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₂ proof₂ = true)
    (hNe : leaves₁ ≠ leaves₂) : ExtractedHashCollision H :=
  extractHashCollisionFromCanopyTranscripts H hOut logLeaves commitment leaves₁ leaves₂
    proof₁ proof₂ hIdx hAcc₁ hAcc₂ (fun h => hNe (Prod.mk.inj h).1)

end Qsag

end

public section

namespace Qsag

/-- Computational projection without exposing the subtype's private proof helper. -/
theorem canopyNodeHashOf_val (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32) (i : Nat) (l r : CanopyDigest32) :
    (canopyNodeHashOf H hOut i l r).val = H (canopyNodeFrame i l r) := by rfl
theorem canopyRootHashOf_val (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32) (i : Nat) (top : CanopyDigest32) :
    (canopyRootHashOf H hOut i top).val = H (canopyRootFrame i top) := by rfl
#export_eqns canopyNodeFrame canopyRootFrame

end Qsag
end
