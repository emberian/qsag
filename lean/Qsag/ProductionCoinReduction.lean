module
public import Qsag.RssSlhFullSecurity
import all Qsag.UcGames
import all Qsag.RssSlhFullSecurity

/-! Executable primitive reduction for the production preprocessing coin *helper*.
This models the two loops in `run_commit_and_open_coin_with_hook`, including its
less obvious choice to XOR the original private shares, not mutated openings.
It is a classical oracle program, not a QROM query-log argument. Private RNG
expansion, distributed scheduling, and secrecy of the full mask stream are not
asserted by this module. -/
public section
namespace Qsag.ProductionCoinReduction
set_option autoImplicit false
attribute [-instance] UInt8.instLawfulEqOrd UInt8.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd BitVec.instTransOrd

abbrev Query := List UInt8 × List UInt8
abbrev Digest := List UInt8
abbrev HashOracle := Query → Digest

def concrete : HashOracle := fun q => cshake256Bytes q.1 q.2

def commitQuery (ctx : ProductionCoinContext) (party : UInt64) (share : BitVec 256) : Query :=
  (productionCoinCommitCustom, productionCoinCommitFrame ctx party share)

def deriveQuery (ctx : ProductionCoinContext) (share : BitVec 256) : Query :=
  (productionCoinDeriveCustom, encodeMultiFrame [bvToFixedBytes 32 ctx.sessionId,
    ctx.phaseLabel, bvToFixedBytes 32 ctx.transcriptDigest, bvToFixedBytes 32 share])

theorem concrete_commit (ctx : ProductionCoinContext) (party : UInt64) (share : BitVec 256) :
    concrete (commitQuery ctx party share) = productionCoinCommit ctx party share := by
  unfold concrete commitQuery productionCoinCommit
  rfl

theorem concrete_derive (ctx : ProductionCoinContext) (share : BitVec 256) :
    concrete (deriveQuery ctx share) = productionCoinDerive ctx share := by
  unfold concrete deriveQuery productionCoinDerive
  rfl

/-- Domain-separated inputs to the primitive, before cSHAKE. -/
theorem commit_ne_derive (ctx ctx' : ProductionCoinContext) (party : UInt64)
    (share share' : BitVec 256) : commitQuery ctx party share ≠ deriveQuery ctx' share' := by
  intro h
  exact tooth_production_coin_domains_distinct (congrArg Prod.fst h)

/-- An entry fixes the original RNG output and the opening selected by the hook.
List order is party order; callers use `UInt64.ofNat` on the array index. An
arbitrary hook can depend on its private state and all earlier calls. -/
structure Entry where
  party : UInt64
  share : BitVec 256
  opened : BitVec 256

abbrev Committed := Entry × Digest

def lock (O : HashOracle) (ctx : ProductionCoinContext) : List Entry → List Committed
  | [] => []
  | e :: es => (e, O (commitQuery ctx e.party e.share)) :: lock O ctx es

def release (O : HashOracle) (ctx : ProductionCoinContext) :
    List Committed → BitVec 256 → Option Digest
  | [], combined => some (O (deriveQuery ctx combined))
  | (e, commitment) :: es, combined =>
    if O (commitQuery ctx e.party e.opened) == commitment then
      release O ctx es (combined ^^^ e.share)
    else none

def run (O : HashOracle) (ctx : ProductionCoinContext) (entries : List Entry) : Option Digest :=
  release O ctx (lock O ctx entries) 0

/-- Compiling the full two-pass helper into the named cSHAKE oracle interface.
The continuation receives all commitments only after every commitment is locked. -/
def lockProgram {α : Type} (ctx : ProductionCoinContext) :
    List Entry → (List Committed → OracleComp Query Digest α) → OracleComp Query Digest α
  | [], k => k []
  | e :: es, k => .query (commitQuery ctx e.party e.share)
      (fun digest => lockProgram ctx es (fun rest => k ((e, digest) :: rest)))

def releaseProgram (ctx : ProductionCoinContext) :
    List Committed → BitVec 256 → OracleComp Query Digest (Option Digest)
  | [], combined => .query (deriveQuery ctx combined) (fun d => .pure (some d))
  | (e, commitment) :: es, combined => .query (commitQuery ctx e.party e.opened)
      (fun d => if d == commitment then releaseProgram ctx es (combined ^^^ e.share)
        else .pure none)

def program (ctx : ProductionCoinContext) (entries : List Entry) :
    OracleComp Query Digest (Option Digest) :=
  lockProgram ctx entries (fun locked => releaseProgram ctx locked 0)

theorem eval_lock {α : Type} (O : HashOracle) (ctx : ProductionCoinContext)
    (es : List Entry) (k : List Committed → OracleComp Query Digest α) :
    evalOracleComp O (lockProgram ctx es k) = evalOracleComp O (k (lock O ctx es)) := by
  induction es generalizing k with
  | nil => rfl
  | cons e es ih => exact ih (fun rest => k ((e, O (commitQuery ctx e.party e.share)) :: rest))

theorem eval_release (O : HashOracle) (ctx : ProductionCoinContext)
    (es : List Committed) (combined : BitVec 256) :
    evalOracleComp O (releaseProgram ctx es combined) = release O ctx es combined := by
  induction es generalizing combined with
  | nil => rfl
  | cons e es ih =>
    simp only [releaseProgram, evalOracleComp, release]
    split <;> simp_all only [evalOracleComp]

theorem eval_program (O : HashOracle) (ctx : ProductionCoinContext) (es : List Entry) :
    evalOracleComp O (program ctx es) = run O ctx es := by
  rw [program, eval_lock, eval_release]; rfl

theorem lock_bound {α : Type} (ctx : ProductionCoinContext) (es : List Entry) (q : Nat)
    (k : List Committed → OracleComp Query Digest α)
    (hk : ∀ locked, locked.length = es.length → QueryBounded q (k locked)) :
    QueryBounded (es.length + q) (lockProgram ctx es k) := by
  induction es generalizing k with
  | nil => simpa only [lockProgram, List.length_nil, Nat.zero_add] using hk [] rfl
  | cons e es ih =>
    change QueryBounded (es.length + 1 + q) (.query _ _)
    rw [Nat.add_right_comm es.length 1 q]
    intro d
    apply ih
    intro locked hl
    apply hk
    simp only [List.length_cons, hl]

theorem release_bound (ctx : ProductionCoinContext) (es : List Committed)
    (combined : BitVec 256) :
    QueryBounded (es.length + 1) (releaseProgram ctx es combined) := by
  induction es generalizing combined with
  | nil => intro d; trivial
  | cons e es ih =>
    intro d
    dsimp only
    split
    · exact ih _
    · trivial

theorem program_bound (ctx : ProductionCoinContext) (es : List Entry) :
    QueryBounded (es.length + (es.length + 1)) (program ctx es) := by
  apply lock_bound
  intro locked hl
  rw [← hl]
  exact release_bound ctx locked 0

/-- D observes success bytes OR abort. Conditioning on success is deliberately absent. -/
def observe {α β : Type} (f : α → β) : OracleComp Query Digest α → OracleComp Query Digest β
  | .pure a => .pure (f a)
  | .query q k => .query q (fun d => observe f (k d))

theorem eval_observe {α β : Type} (O : HashOracle) (f : α → β)
    (p : OracleComp Query Digest α) : evalOracleComp O (observe f p) = f (evalOracleComp O p) := by
  induction p with
  | pure a => rfl
  | query q k ih => exact ih (O q)

theorem observe_bound {α β : Type} (f : α → β) (q : Nat)
    (p : OracleComp Query Digest α) (h : QueryBounded q p) : QueryBounded q (observe f p) := by
  induction p generalizing q with
  | pure a => cases q <;> exact True.intro
  | query x k ih =>
    cases q with
    | zero => exact h
    | succ q => intro d; exact ih d q (h d)

/-- An actual primitive adversary, obtained by running the helper then D. -/
def reduction (ctx : ProductionCoinContext) (es : List Entry) (D : Option Digest → Bool) :
    OracleComp Query Digest Bool := observe D (program ctx es)

theorem reduction_correct (O : HashOracle) (ctx : ProductionCoinContext)
    (es : List Entry) (D : Option Digest → Bool) :
    evalOracleComp O (reduction ctx es D) = D (run O ctx es) := by
  rw [reduction, eval_observe, eval_program]

theorem reduction_bound (ctx : ProductionCoinContext) (es : List Entry)
    (D : Option Digest → Bool) :
    QueryBounded (es.length + (es.length + 1)) (reduction ctx es D) :=
  observe_bound D _ _ (program_bound ctx es)

/-- Primitive-game assumption over *all* bounded classical oracle adversaries.
The oracle families and fixed public/private auxiliary data are independent of
which oracle index is sampled. This is a hypothesis about cSHAKE/ideal families,
not a renamed protocol gap or a proof that concrete cSHAKE is random.
Unrestricted classical computations can themselves evaluate concrete cSHAKE;
instantiating this with concrete-vs-random families therefore requires an
appropriate ideal-primitive model or a separate computational admissibility
condition. Query count alone does not prove concrete-hash pseudorandomness. -/
def OracleIndistinguishable (N q eps : Nat) (left right : Fin N → HashOracle) : Prop :=
  ∀ A : OracleComp Query Digest Bool, QueryBounded q A →
    natAbsDiff (finSum N (fun i => if evalOracleComp (left i) A then 1 else 0))
      (finSum N (fun i => if evalOracleComp (right i) A then 1 else 0)) ≤ eps

theorem helper_reduces_to_primitive (N eps : Nat) (left right : Fin N → HashOracle)
    (ctx : ProductionCoinContext) (es : List Entry) (D : Option Digest → Bool)
    (h : OracleIndistinguishable N (es.length + (es.length + 1)) eps left right) :
    natAbsDiff (finSum N (fun i => if D (run (left i) ctx es) then 1 else 0))
      (finSum N (fun i => if D (run (right i) ctx es) then 1 else 0)) ≤ eps := by
  have hb := h (reduction ctx es D) (reduction_bound ctx es D)
  simpa only [reduction_correct] using hb

/-- Telescoping primitive families, with the concrete reduction at every hop. -/
theorem helper_hybrid_bound (N stages eps : Nat) (family : Nat → Fin N → HashOracle)
    (ctx : ProductionCoinContext) (es : List Entry) (D : Option Digest → Bool)
    (h : ∀ j, j < stages → OracleIndistinguishable N (es.length + (es.length + 1)) eps
      (family j) (family (j + 1))) :
    natAbsDiff (finSum N (fun i => if D (run (family 0 i) ctx es) then 1 else 0))
      (finSum N (fun i => if D (run (family stages i) ctx es) then 1 else 0)) ≤ stages * eps := by
  apply natAbsDiff_telescope stages eps (fun j =>
    finSum N (fun i => if D (run (family j i) ctx es) then 1 else 0))
  intro j hj
  exact helper_reduces_to_primitive N eps _ _ ctx es D (h j hj)

def combinedShares : List Entry → BitVec 256 → BitVec 256
  | [], acc => acc
  | e :: es, acc => combinedShares es (acc ^^^ e.share)

/-- Positive execution for every actual cSHAKE context and every honest RNG tape. -/
theorem honest_release (O : HashOracle) (ctx : ProductionCoinContext) (es : List Entry)
    (h : ∀ e ∈ es, e.opened = e.share) (acc : BitVec 256) :
    release O ctx (lock O ctx es) acc = some (O (deriveQuery ctx (combinedShares es acc))) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [lock, release, h e (List.mem_cons_self), beq_self_eq_true, ↓reduceIte,
      combinedShares]
    exact ih (fun e he => h e (List.mem_cons_of_mem _ he)) _

theorem honest_concrete (ctx : ProductionCoinContext) (es : List Entry)
    (h : ∀ e ∈ es, e.opened = e.share) :
    run concrete ctx es = some (productionCoinDerive ctx (combinedShares es 0)) :=
  honest_release concrete ctx es h 0

/-- A reused two-party share cancels before the final hash. This is a deterministic
coin fixed by public context, even if the reused private share has 256 bits of entropy. -/
theorem reused_share_cancels (ctx : ProductionCoinContext) (s : BitVec 256) :
    run concrete ctx [⟨0, s, s⟩, ⟨1, s, s⟩] = some (productionCoinDerive ctx 0) := by
  have h : ∀ e ∈ ([⟨0, s, s⟩, ⟨1, s, s⟩] : List Entry), e.opened = e.share := by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  rw [honest_concrete ctx _ h]
  simp [combinedShares]


/-- Even a colliding hook opening cannot change the helper's original XOR.
It can affect whether the result is released. This is specific to the actual
Rust helper and must not be substituted for a network commitment protocol. -/
theorem release_abort_or_original (O : HashOracle) (ctx : ProductionCoinContext)
    (es : List Entry) (acc : BitVec 256) :
    release O ctx (lock O ctx es) acc = none ∨
    release O ctx (lock O ctx es) acc =
      some (O (deriveQuery ctx (combinedShares es acc))) := by
  induction es generalizing acc with
  | nil => exact Or.inr rfl
  | cons e es ih =>
    simp only [lock, release, combinedShares]
    split
    · exact ih _
    · exact Or.inl rfl

theorem helper_abort_or_original (O : HashOracle) (ctx : ProductionCoinContext)
    (es : List Entry) :
    run O ctx es = none ∨
    run O ctx es = some (O (deriveQuery ctx (combinedShares es 0))) :=
  release_abort_or_original O ctx es 0

/-- The preimage binds the complete transcript digest, not a truncated prefix. -/
theorem derive_frame_binds_transcript (ctx ctx' : ProductionCoinContext)
    (s s' : BitVec 256) (h : (deriveQuery ctx s).2 = (deriveQuery ctx' s').2) :
    ctx.transcriptDigest = ctx'.transcriptDigest := by
  have fields := encodeMultiFrame_injective h
  have hb : bvToFixedBytes 32 ctx.transcriptDigest = bvToFixedBytes 32 ctx'.transcriptDigest := by
    simp only [List.cons.injEq, and_true] at fields
    exact fields.2.2.1
  have recovered := congrArg (fixedBytesToBv 32) hb
  simpa only [fixedBytesToBv_bvToFixedBytes] using recovered

/-- Accepting the same derivation under changed transcript context supplies a
concrete collision, instead of assuming an injective 256-bit hash. -/
def changed_context_collision (ctx ctx' : ProductionCoinContext)
    (s s' : BitVec 256) (hne : ctx.transcriptDigest ≠ ctx'.transcriptDigest)
    (h : productionCoinDerive ctx s = productionCoinDerive ctx' s') :
    HashCollisionWitness (cshake256Bytes productionCoinDeriveCustom) where
  m1 := (deriveQuery ctx s).2
  m2 := (deriveQuery ctx' s').2
  ne := fun eq => hne (derive_frame_binds_transcript ctx ctx' s s' eq)
  eq := h

/-- A context-misbound mutant drops transcript binding before hashing. Unlike
`derive_frame_binds_transcript`, it produces identical inputs for every digest. -/
def misboundDeriveQuery (ctx : ProductionCoinContext) (s : BitVec 256) : Query :=
  deriveQuery { ctx with transcriptDigest := 0 } s

theorem misbound_context_replays (ctx : ProductionCoinContext) (a b s : BitVec 256) :
    concrete (misboundDeriveQuery { ctx with transcriptDigest := a } s) =
    concrete (misboundDeriveQuery { ctx with transcriptDigest := b } s) := by
  unfold misboundDeriveQuery
  rfl


/-- Independent auxiliary tapes (keys, sharing, public context and hook state)
may be arbitrarily correlated with each other, but not with the primitive-family
index. The product sampling is explicit; the loss is T*eps over T*N samples. -/
theorem independent_auxiliary_reduction (T N n eps : Nat)
    (left right : Fin N → HashOracle) (contexts : Fin T → ProductionCoinContext)
    (entries : Fin T → List Entry) (tests : Fin T → Option Digest → Bool)
    (hlen : ∀ t, (entries t).length = n)
    (h : OracleIndistinguishable N (n + (n + 1)) eps left right) :
    natAbsDiff
      (finSum T (fun t => finSum N (fun i =>
        if tests t (run (left i) (contexts t) (entries t)) then 1 else 0)))
      (finSum T (fun t => finSum N (fun i =>
        if tests t (run (right i) (contexts t) (entries t)) then 1 else 0))) ≤ T * eps := by
  apply Nat.le_trans (natAbsDiff_finSum_le _ _)
  rw [← finSum_const T eps]
  apply finSum_le_finSum
  intro t
  apply helper_reduces_to_primitive
  simpa only [hlen t] using h

end Qsag.ProductionCoinReduction
