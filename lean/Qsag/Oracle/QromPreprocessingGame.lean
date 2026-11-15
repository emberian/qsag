module
/-
# Classical oracle-dependent advice and fresh challenge chronology

This is a classical finite experiment beside, not a replacement for, `QuantumAdv`.
Preprocessing may read the entire oracle and produces exactly `bits` bits. Only the
online adaptive program has a query budget. Advice capacity is not online memory.
The challenge is sampled after advice: `preprocess` has no challenge argument.

The proved generic connection charges a union over all advice strings. The sharper
stored-table bound applies only to the specified zero-query table strategy, not to
arbitrary advice. Neither theorem is a QAI-QROM theorem; quantum advice would require
state semantics and non-cloning/measurement accounting absent from this module.
-/
public import Qsag.Oracle.MultiRoundFsQrom
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Protocol.Signing.HashSigs

public section
namespace Qsag.PreprocessingGame
set_option autoImplicit false

/-- A classical adaptive online algorithm with an upper bound on queries on every branch.
There is no restriction on the size of its code or its local workspace. -/
inductive Program (X Y Out : Type) : Nat → Type where
  | done {q : Nat} : Out → Program X Y Out q
  | query {q : Nat} : X → (Y → Program X Y Out q) → Program X Y Out (q + 1)

def Program.run {X Y Out : Type} {q : Nat} (H : X → Y) :
    Program X Y Out q → Out × Nat
  | .done out => (out, 0)
  | .query x next => let result := (next (H x)).run H; (result.1, result.2 + 1)

theorem Program.queries_le {X Y Out : Type} {q : Nat} (H : X → Y)
    (A : Program X Y Out q) : (A.run H).2 ≤ q := by
  induction A with
  | done out => exact Nat.zero_le _
  | query x next ih => exact Nat.succ_le_succ (ih (H x))

/-- Unbounded offline computation with oracle-dependent classical advice. Challenge
randomness is unavailable to preprocessing; oracle dependence is deliberately allowed. -/
structure ClassicalAdvice (n w k bits q : Nat) (Out : Type) where
  preprocess : (Fin n → BitVec w) → BitVec bits
  online : BitVec bits → Fin k → Program (Fin n) (BitVec w) Out q

def ClassicalAdvice.run {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out) (H : Fin n → BitVec w) (salt : Fin k) : Out × Nat :=
  (A.online (A.preprocess H) salt).run H

theorem ClassicalAdvice.online_queries_le {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out) (H : Fin n → BitVec w) (salt : Fin k) :
    (A.run H salt).2 ≤ q := Program.queries_le H _

/-- Counts oracle/challenge pairs. The denominator for positive k is `(2^w)^n * k`.
The win predicate can include verification calls; those calls are NOT in the online count. -/
def adviceWinCount {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) : Nat :=
  uniformOracleSum w n fun H => qsum k fun salt =>
    if win H salt (A.run H salt).1 then 1 else 0

def fixedAdviceWinCount {n w k bits q : Nat} {Out : Type}
    (online : BitVec bits → Fin k → Program (Fin n) (BitVec w) Out q)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) (advice : BitVec bits) : Nat :=
  uniformOracleSum w n fun H => qsum k fun salt =>
    if win H salt ((online advice salt).run H).1 then 1 else 0

/-- A selected term is at most the sum, constructively and without a finite-set library. -/
theorem selected_le_sum {m : Nat} (a : Fin m) (f : Fin m → Nat) : f a ≤ qsum m f := by
  rw [← qsum_ite_eq m a (f a)]
  exact qsum_le_qsum fun i => by
    by_cases h : i = a
    · subst i; simp
    · simp [h]

/-- Exact reduction to the sum of fixed-advice experiments. No hardness premise, no
oracle-independent assumption on preprocessing, and no assumption of successful extraction. -/
theorem adviceWinCount_le_sum_fixed {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) :
    adviceWinCount A win ≤ qsum (2 ^ bits) fun a =>
      fixedAdviceWinCount A.online win (BitVec.ofFin a) := by
  unfold adviceWinCount fixedAdviceWinCount
  rw [← uniformOracleSum_qsum]
  apply uniformOracleSum_le
  intro H
  rw [qsum_comm]
  apply qsum_le_qsum
  intro salt
  have h := selected_le_sum (A.preprocess H).toFin (fun a =>
    if win H salt ((A.online (BitVec.ofFin a) salt).run H).1 then 1 else 0)
  exact h

/-- If each oracle-independent fixed-advice experiment has count at most B, the
oracle-dependent experiment has count at most `2^bits * B`. This deliberately loose
classical advice union bound does not claim the literature's stronger QAI estimates. -/
theorem adviceWinCount_le_capacity_mul {n w k bits q : Nat} {Out : Type}
    (A : ClassicalAdvice n w k bits q Out)
    (win : (Fin n → BitVec w) → Fin k → Out → Bool) (B : Nat)
    (hB : ∀ a, fixedAdviceWinCount A.online win a ≤ B) :
    adviceWinCount A win ≤ 2 ^ bits * B := by
  apply Nat.le_trans (adviceWinCount_le_sum_fixed A win)
  have h := qsum_le_qsum (fun a : Fin (2 ^ bits) => hB (BitVec.ofFin a))
  simpa only [qsum_const] using h

/-- The actual output pair must be distinct and collide; existence of some other pair
is irrelevant to this verifier. -/
def collisionWin {n w : Nat} (H : Fin n → BitVec w) (pair : Fin n × Fin n) : Bool :=
  decide (pair.1 ≠ pair.2 ∧ H pair.1 = H pair.2)

/-- Two advice bits choose one of three pairs; no online oracle call is made. -/
def storedCollisionAdvice (H : Fin 3 → BitVec 1) : BitVec 2 :=
  if H 0 = H 1 then 0 else if H 0 = H 2 then 1 else 2

def storedCollisionPair (advice : BitVec 2) : Fin 3 × Fin 3 :=
  if advice = 0 then (0, 1) else if advice = 1 then (0, 2) else (1, 2)

def storedCollision : ClassicalAdvice 3 1 1 2 0 (Fin 3 × Fin 3) where
  preprocess := storedCollisionAdvice
  online := fun advice _ => .done (storedCollisionPair advice)

/-- A real zero-online-query strategy wins on EVERY oracle in this finite family.
This is an inhabited counterexample to unsalted collision hardness with free preprocessing. -/
theorem storedCollision_wins (H : Fin 3 → BitVec 1) :
    collisionWin H (storedCollision.run H 0).1 = true := by
  have hpigeon : ∀ a b c : BitVec 1, a = b ∨ a = c ∨ b = c := by decide
  have hp := hpigeon (H 0) (H 1) (H 2)
  by_cases h01 : H 0 = H 1
  · simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
      Program.run, storedCollisionPair, collisionWin, h01]
  · by_cases h02 : H 0 = H 2
    · have h21 : H 2 ≠ H 1 := by intro he; exact h01 (h02.trans he)
      simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
        Program.run, storedCollisionPair, collisionWin, h02, h21]
    · have h12 : H 1 = H 2 := hp.resolve_left h01 |>.resolve_left h02
      simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
        Program.run, storedCollisionPair, collisionWin, h02, h12]

theorem storedCollision_count :
    adviceWinCount storedCollision (fun H _ pair => collisionWin H pair) = 8 := by
  have hEach : ∀ H : Fin 3 → BitVec 1, qsum 1 (fun salt =>
      if collisionWin H (storedCollision.run H salt).1 then 1 else 0) = 1 := by
    intro H
    have hTerms : ∀ salt : Fin 1,
        (if collisionWin H (storedCollision.run H salt).1 then 1 else 0) = 1 := by
      intro salt
      have hs : salt = (0 : Fin 1) := Fin.ext (by omega)
      rw [hs, storedCollision_wins]
      rfl
    rw [qsum_congr hTerms, qsum_const]
  unfold adviceWinCount
  rw [uniformOracleSum_congr 1 3 _ _ hEach, uniformOracleSum_const]

/-! ## A fresh-salt table attack with a sharp table-entry bound

This strategy is a special case, not a bound on arbitrary S-bit advice. An entry
contains one salt and one candidate. After seeing the fresh uniform salt, the online
algorithm returns the first matching candidate or fails. It does not inspect H.
Table capacity is number of entries, and is not mislabeled as number of advice bits.
-/

def lookup {k : Nat} {Out : Type} (salt : Fin k) : List (Fin k × Out) → Option Out
  | [] => none
  | (s, out) :: rest => if salt = s then some out else lookup salt rest

/-- The stored-table online algorithm explicitly has budget zero. -/
def tableOnline {k : Nat} {Out X Y : Type} (table : List (Fin k × Out)) (salt : Fin k) :
    Program X Y (Option Out) 0 := .done (lookup salt table)

theorem tableOnline_run {k : Nat} {Out X Y : Type} (H : X → Y)
    (table : List (Fin k × Out)) (salt : Fin k) :
    (tableOnline table salt).run H = (lookup salt table, 0) := by
  unfold tableOnline Program.run
  rfl

def tableWin {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (table : List (Fin k × Out)) (salt : Fin k) : Nat :=
  match lookup salt table with
  | none => 0
  | some out => if check salt out then 1 else 0

theorem tableWin_cons_le {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (s : Fin k) (out : Out) (rest : List (Fin k × Out)) (salt : Fin k) :
    tableWin check ((s, out) :: rest) salt ≤
      (if salt = s then 1 else 0) + tableWin check rest salt := by
  by_cases h : salt = s
  · simp only [tableWin, lookup, h, ↓reduceIte]
    split <;> omega
  · simp [tableWin, lookup, h]

/-- For every fixed oracle-dependent table, at most its length of the fresh salts win.
No independence of table contents from the oracle is required. -/
theorem freshSalt_table_bound {k : Nat} {Out : Type} (check : Fin k → Out → Bool)
    (table : List (Fin k × Out)) : qsum k (tableWin check table) ≤ table.length := by
  induction table with
  | nil =>
    change qsum k (fun _ => 0) ≤ 0
    rw [qsum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  | cons entry rest ih =>
    have h := qsum_le_qsum (tableWin_cons_le check entry.1 entry.2 rest)
    rw [qsum_add, qsum_ite_eq] at h
    exact Nat.le_trans h (by simp only [List.length_cons]; omega)

/-- Averaging the pointwise salt bound over the actual uniform oracle enumeration.
For positive k this is probability ≤ entries/k, even with unbounded preprocessing. -/
theorem freshSalt_preprocessed_table_bound {n w k : Nat} {Out : Type}
    (preprocess : (Fin n → BitVec w) → List (Fin k × Out))
    (check : (Fin n → BitVec w) → Fin k → Out → Bool) (entries : Nat)
    (capacity : ∀ H, (preprocess H).length ≤ entries) :
    uniformOracleSum w n (fun H => qsum k (tableWin (check H) (preprocess H))) ≤
      (2 ^ w) ^ n * entries := by
  rw [← uniformOracleSum_const w n entries]
  exact uniformOracleSum_le w n _ _ fun H =>
    Nat.le_trans (freshSalt_table_bound (check H) (preprocess H)) (capacity H)

/-! ## Production signature/Merkle seed encoding connection

`thNodeH` feeds `pkSeed` into the self-delimiting `thPreimage`. Distinct seed slices
are disjoint inputs, proved below, but the implementation does not generate a new
uniform challenge seed for each call. Disjoint encoding is not freshness.
-/

def nodeRequest (seed : List UInt8) (adrs : HashAdrs) (left right : List UInt8) : List UInt8 :=
  thPreimage tagThH seed adrs [left, right]

theorem nodeRequest_seed_separation {seed₁ seed₂ : List UInt8}
    (adrs₁ adrs₂ : HashAdrs) (left₁ right₁ left₂ right₂ : List UInt8)
    (different : seed₁ ≠ seed₂) :
    nodeRequest seed₁ adrs₁ left₁ right₁ ≠ nodeRequest seed₂ adrs₂ left₂ right₂ := by
  intro same
  exact different (thPreimage_injective same).2.1

theorem nodeRequest_is_production (suite : TweakableHashSuite) (seed : List UInt8)
    (adrs : HashAdrs) (left right : List UInt8) :
    thNodeH suite seed adrs left right = suite.rawHash (nodeRequest seed adrs left right) := by
  unfold thNodeH thCall nodeRequest
  rfl

/-- Concrete reduction output: distinct accepted node pairs give the two actual
encoded raw-hash inputs, not merely a proposition that a collision exists. -/
def nodeCollisionWitness (suite : TweakableHashSuite) (seed : List UInt8) (adrs : HashAdrs)
    (left right : List UInt8 × List UInt8) (hne : left ≠ right)
    (heq : thNodeH suite seed adrs left.1 left.2 = thNodeH suite seed adrs right.1 right.2) :
    HashCollisionWitness suite.rawHash where
  m1 := nodeRequest seed adrs left.1 left.2
  m2 := nodeRequest seed adrs right.1 right.2
  ne := by
    intro same
    have args := (thPreimage_injective same).2.2.2
    have hl := (List.cons.inj args).1
    have hr := (List.cons.inj (List.cons.inj args).2).1
    exact hne (Prod.ext hl hr)
  eq := by simpa only [nodeRequest_is_production] using heq

/-- Production public-key derivation preserves the supplied seed; it does not sample
fresh salt. Any fresh-key preprocessing theorem must account for key generation upstream. -/
theorem production_seed_is_preserved (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl

/-- The fresh-salt table theorem applies to encoded production node requests for any
finite collection of candidate seeds. No distributional claim about the real keygen
is introduced: the experiment explicitly samples the seed index after preprocessing. -/
theorem freshSalt_node_requests_bound {k : Nat}
    (seeds : Fin k → List UInt8) (suite : TweakableHashSuite) (adrs : HashAdrs)
    (table : List (Fin k × ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)))) :
    qsum k (tableWin (fun salt pair => decide
      (pair.1 ≠ pair.2 ∧
        thNodeH suite (seeds salt) adrs pair.1.1 pair.1.2 =
        thNodeH suite (seeds salt) adrs pair.2.1 pair.2.2)) table) ≤ table.length :=
  freshSalt_table_bound _ _

#verify_constructive
  Qsag.PreprocessingGame.Program.queries_le
  Qsag.PreprocessingGame.ClassicalAdvice.online_queries_le
  Qsag.PreprocessingGame.adviceWinCount_le_sum_fixed
  Qsag.PreprocessingGame.adviceWinCount_le_capacity_mul
  Qsag.PreprocessingGame.storedCollision_wins
  Qsag.PreprocessingGame.storedCollision_count
  Qsag.PreprocessingGame.tableOnline_run
  Qsag.PreprocessingGame.freshSalt_table_bound
  Qsag.PreprocessingGame.freshSalt_preprocessed_table_bound
  Qsag.PreprocessingGame.nodeRequest_seed_separation
  Qsag.PreprocessingGame.nodeRequest_is_production
  Qsag.PreprocessingGame.production_seed_is_preserved
  Qsag.PreprocessingGame.freshSalt_node_requests_bound
end Qsag.PreprocessingGame
end
