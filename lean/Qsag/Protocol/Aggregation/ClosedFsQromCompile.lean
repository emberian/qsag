module
/-
# Qsag.Protocol.Aggregation.ClosedFsQromCompile — executable Merkle-opening verifier ⟶ oracle IOP ⟶ Fiat–Shamir QROM

A reduction functor with no protocol-specific content. For an oracle IOP whose verifier reads
committed tables only at queried positions (`OracleIop`), a tweaked Merkle hash (`MerkleSetup`)
and a Boolean round-by-round state function (`BoolRbrCert`):

* `extractMerkleCollision`, `openingCollision`, `findCollision`: from an accepted opening that
  disagrees with the committed table, an explicit collision of the node or leaf hash, as data.
* `exec_accept_reduces`: the executable verifier (`execVerify`: authentication paths against
  the roots, then the IOP verdict on the opened values) accepts only if `findCollision` returns
  a collision or the IOP verifier accepts the same transcript.
* `fs_qrom_bool_rbr_soundness`: Fiat–Shamir over a uniformly random oracle. The round covering
  premise of `qrom_uniform_oracle_success_bound` is proved here from the state function, by a
  first-flip argument on the transcript prefixes of the adversary's output.
* `exec_fs_qrom_closed_soundness`: for a false statement and any `Q`-query adversary, the
  acceptance mass of the executable verifier is at most
  `(2Q+1)² · Σ_r bad_r / 2^w` plus the mass of outputs on which `findCollision` succeeds.

Modelling limits. The Fiat–Shamir oracle is queried on the whole message prefix, tables
included, and the adversary's output carries the tables next to the openings: the reduction
reads the tables from the output instead of extracting them from oracle queries. The Merkle
hash is a fixed function, and the collision term is the success mass of the explicit
collision finder, not a number.
-/

public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Oracle.Qrom
public import Qsag.Spec.Assumptions
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ClosedFs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## §1. Merkle openings: constructive collision extraction -/

/-- Root recomputed from a node digest and its authentication path (same recursion as
    `Qsag.merkleRootFromPath`). -/
def merklePathRoot {D : Type} (H : Nat → Nat → D → D → D) : Nat → Nat → D → List D → D
  | _, _, cur, [] => cur
  | lvl, idx, cur, sib :: rest =>
    merklePathRoot H (lvl + 1) (idx / 2)
      (if idx % 2 = 0 then H lvl (idx / 2) cur sib else H lvl (idx / 2) sib cur) rest

theorem merklePathRoot_eq_merkleRootFromPath {D : Type} (H : Nat → Nat → D → D → D) :
    ∀ (path : List D) (lvl idx : Nat) (cur : D),
      merklePathRoot H lvl idx cur path = merkleRootFromPath H lvl idx cur path
  | [], _, _, _ => by rw [merkleRootFromPath_nil]; rfl
  | sib :: rest, lvl, idx, cur => by
    rw [merkleRootFromPath_cons]
    show merklePathRoot H (lvl + 1) (idx / 2) _ rest = merkleRootFromPath H (lvl + 1) (idx / 2) _ rest
    exact merklePathRoot_eq_merkleRootFromPath H rest _ _ _

/-- Two child pairs with the same digest under one `(lvl, node)` tweak. -/
structure MerkleCollisionWitness {D : Type} (H : Nat → Nat → D → D → D) where
  lvl : Nat
  node : Nat
  a : D
  b : D
  a' : D
  b' : D
  distinct : ¬ (a = a' ∧ b = b')
  collides : H lvl node a b = H lvl node a' b'

/-- Two openings of one position to one root coincide, or yield a collision as data. -/
def extractMerkleCollision {D : Type} [DecidableEq D] (H : Nat → Nat → D → D → D) :
    (path path' : List D) → (lvl idx : Nat) → (leaf leaf' : D) →
    path.length = path'.length →
    merklePathRoot H lvl idx leaf path = merklePathRoot H lvl idx leaf' path' →
    PSum (leaf = leaf' ∧ path = path') (MerkleCollisionWitness H)
  | [], [], _, _, _, _, _, h => .inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | sib :: rest, sib' :: rest', lvl, idx, leaf, leaf', hl, h =>
    match extractMerkleCollision H rest rest' (lvl + 1) (idx / 2)
        (if idx % 2 = 0 then H lvl (idx / 2) leaf sib else H lvl (idx / 2) sib leaf)
        (if idx % 2 = 0 then H lvl (idx / 2) leaf' sib' else H lvl (idx / 2) sib' leaf')
        (Nat.succ.inj hl) h with
    | .inr c => .inr c
    | .inl hp =>
      if hEq : leaf = leaf' ∧ sib = sib' then
        .inl ⟨hEq.1, by rw [hEq.2, hp.2]⟩
      else if hpar : idx % 2 = 0 then
        .inr ⟨lvl, idx / 2, leaf, sib, leaf', sib', hEq,
          by have h1 := hp.1; rw [ite_eq_left hpar, ite_eq_left hpar] at h1; exact h1⟩
      else
        .inr ⟨lvl, idx / 2, sib, leaf, sib', leaf', fun h' => hEq ⟨h'.2, h'.1⟩,
          by have h1 := hp.1; rw [ite_eq_right hpar, ite_eq_right hpar] at h1; exact h1⟩

/-- Node `i` at height `l` of the complete tree over the leaf digests `leafD`. -/
def treeNode {D : Type} (H : Nat → Nat → D → D → D) (leafD : Nat → D) : Nat → Nat → D
  | 0, i => leafD i
  | l + 1, i => H l i (treeNode H leafD l (2 * i)) (treeNode H leafD l (2 * i + 1))

def sibIdx (i : Nat) : Nat := if i % 2 = 0 then i + 1 else i - 1

/-- The honest authentication path of node `i` at height `l`, `r` levels long. -/
def treePathFrom {D : Type} (H : Nat → Nat → D → D → D) (leafD : Nat → D) : Nat → Nat → Nat → List D
  | _, _, 0 => []
  | l, i, r + 1 => treeNode H leafD l (sibIdx i) :: treePathFrom H leafD (l + 1) (i / 2) r

theorem treePathFrom_length {D : Type} (H : Nat → Nat → D → D → D) (leafD : Nat → D) :
    ∀ (r l i : Nat), (treePathFrom H leafD l i r).length = r
  | 0, _, _ => by rfl
  | r + 1, l, i => by
    show (treePathFrom H leafD (l + 1) (i / 2) r).length + 1 = r + 1
    rw [treePathFrom_length H leafD r]

theorem treePathFrom_opens {D : Type} (H : Nat → Nat → D → D → D) (leafD : Nat → D) :
    ∀ (r l i : Nat),
      merklePathRoot H l i (treeNode H leafD l i) (treePathFrom H leafD l i r) =
        treeNode H leafD (l + r) (i / 2 ^ r)
  | 0, l, i => by
    show treeNode H leafD l i = treeNode H leafD (l + 0) (i / 2 ^ 0)
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one]
  | r + 1, l, i => by
    show merklePathRoot H (l + 1) (i / 2)
        (if i % 2 = 0 then H l (i / 2) (treeNode H leafD l i) (treeNode H leafD l (sibIdx i))
          else H l (i / 2) (treeNode H leafD l (sibIdx i)) (treeNode H leafD l i))
        (treePathFrom H leafD (l + 1) (i / 2) r) = treeNode H leafD (l + (r + 1)) (i / 2 ^ (r + 1))
    have hParent : (if i % 2 = 0 then H l (i / 2) (treeNode H leafD l i) (treeNode H leafD l (sibIdx i))
          else H l (i / 2) (treeNode H leafD l (sibIdx i)) (treeNode H leafD l i)) =
        treeNode H leafD (l + 1) (i / 2) := by
      show _ = H l (i / 2) (treeNode H leafD l (2 * (i / 2))) (treeNode H leafD l (2 * (i / 2) + 1))
      if hpar : i % 2 = 0 then
        have e1 : 2 * (i / 2) = i := by omega
        have e2 : sibIdx i = 2 * (i / 2) + 1 := by unfold sibIdx; rw [ite_eq_left hpar]; omega
        rw [ite_eq_left hpar, e2, e1]
      else
        have e1 : 2 * (i / 2) + 1 = i := by omega
        have e2 : sibIdx i = 2 * (i / 2) := by unfold sibIdx; rw [ite_eq_right hpar]; omega
        rw [ite_eq_right hpar, e2, e1]
    rw [hParent, treePathFrom_opens H leafD r (l + 1) (i / 2)]
    have eL : l + 1 + r = l + (r + 1) := by omega
    have eI : i / 2 / 2 ^ r = i / 2 ^ (r + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [eL, eI]

/-- Tweaked Merkle hash: inner compression and position-tweaked leaf hash. -/
structure MerkleSetup (D F : Type) where
  node : Nat → Nat → D → D → D
  leaf : Nat → Nat → F → D

def MerkleSetup.oracleLeaves {D F : Type} (M : MerkleSetup D F) (i : Nat) (tbl : Nat → F) : Nat → D :=
  fun p => M.leaf i p (tbl p)

/-- Commitment to table `tbl` of oracle `i`: root of the depth-`depth` tree. -/
def MerkleSetup.root {D F : Type} (M : MerkleSetup D F) (i depth : Nat) (tbl : Nat → F) : D :=
  treeNode M.node (M.oracleLeaves i tbl) depth 0

/-- A collision of the node hash or of the leaf hash. -/
inductive CollisionWitness {D F : Type} (node : Nat → Nat → D → D → D) (leaf : Nat → Nat → F → D) where
  | node (c : MerkleCollisionWitness node)
  | leaf (oracle pos : Nat) (v v' : F) (distinct : v ≠ v')
      (collides : leaf oracle pos v = leaf oracle pos v')

/-- Node and leaf hash realized by one byte hash `Hb` through prefix-free framings. -/
def framedSetup {F : Type} (Hb : Spec.Bytes → Spec.Bytes)
    (nodeC : Spec.FramedCodec (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (leafC : Spec.FramedCodec (Nat × Nat × F)) : MerkleSetup Spec.Bytes F where
  node := fun l i a b => Hb (nodeC.encode (l, i, a, b))
  leaf := fun o p v => Hb (leafC.encode (o, p, v))

/-- A collision of the framed Merkle hash is a `Spec.HashCollision` of the byte hash. -/
def CollisionWitness.toHashCollision {F : Type} (Hb : Spec.Bytes → Spec.Bytes)
    (nodeC : Spec.FramedCodec (Nat × Nat × Spec.Bytes × Spec.Bytes))
    (leafC : Spec.FramedCodec (Nat × Nat × F)) :
    CollisionWitness (framedSetup Hb nodeC leafC).node (framedSetup Hb nodeC leafC).leaf →
      Spec.HashCollision Hb
  | .node c =>
    { m₁ := nodeC.encode (c.lvl, c.node, c.a, c.b)
      m₂ := nodeC.encode (c.lvl, c.node, c.a', c.b')
      distinct := fun h =>
        c.distinct (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (nodeC.encode_injective h)).2).2)
      collides := c.collides }
  | .leaf o p v v' hne hcol =>
    { m₁ := leafC.encode (o, p, v)
      m₂ := leafC.encode (o, p, v')
      distinct := fun h =>
        hne (Prod.mk.inj (Prod.mk.inj (leafC.encode_injective h)).2).2
      collides := hcol }

/-- An accepted opening shows the committed value, or yields a collision. -/
def openingCollision {D F : Type} [DecidableEq D] [DecidableEq F] (M : MerkleSetup D F)
    (i depth : Nat) (tbl : Nat → F) (pos : Nat) (op : F × List D)
    (hpos : pos < 2 ^ depth) (hlen : op.2.length = depth)
    (hroot : merklePathRoot M.node 0 pos (M.leaf i pos op.1) op.2 = M.root i depth tbl) :
    PSum (op.1 = tbl pos) (CollisionWitness M.node M.leaf) :=
  match extractMerkleCollision M.node op.2
      (treePathFrom M.node (M.oracleLeaves i tbl) 0 pos depth) 0 pos
      (M.leaf i pos op.1) (M.oracleLeaves i tbl pos)
      (by rw [treePathFrom_length]; exact hlen)
      (by
        rw [hroot]
        have h := treePathFrom_opens M.node (M.oracleLeaves i tbl) depth 0 pos
        rw [Nat.zero_add, Nat.div_eq_of_lt hpos] at h
        exact h.symm) with
  | .inr c => .inr (.node c)
  | .inl h =>
    if hv : op.1 = tbl pos then .inl hv
    else .inr (.leaf i pos op.1 (tbl pos) hv h.1)

def openingCollisionOpt {D F : Type} [DecidableEq D] [DecidableEq F] (M : MerkleSetup D F)
    (i depth : Nat) (tbl : Nat → F) (pos : Nat) (op : F × List D)
    (hpos : pos < 2 ^ depth) (hlen : op.2.length = depth)
    (hroot : merklePathRoot M.node 0 pos (M.leaf i pos op.1) op.2 = M.root i depth tbl) :
    Option (CollisionWitness M.node M.leaf) :=
  match openingCollision M i depth tbl pos op hpos hlen hroot with
  | .inr c => some c
  | .inl _ => none

theorem openingCollisionOpt_none {D F : Type} [DecidableEq D] [DecidableEq F] (M : MerkleSetup D F)
    (i depth : Nat) (tbl : Nat → F) (pos : Nat) (op : F × List D)
    (hpos : pos < 2 ^ depth) (hlen : op.2.length = depth)
    (hroot : merklePathRoot M.node 0 pos (M.leaf i pos op.1) op.2 = M.root i depth tbl)
    (h : openingCollisionOpt M i depth tbl pos op hpos hlen hroot = none) : op.1 = tbl pos := by
  unfold openingCollisionOpt at h
  split at h
  · cases h
  · assumption

/-! ## §2. Oracle IOPs and their executable Merkle-opening verifier -/

/-- A `k`-round public-coin oracle IOP with `2^w` challenges per round. The verifier sees the
    public part of the statement and of each message, reads committed tables at `queries`, and
    decides by `verdict` on the values read. -/
structure OracleIop (Stmt PStmt Msg Pub F : Type) (k : Nat) where
  w : Nat
  inLang : Stmt → Prop
  pubStmt : Stmt → PStmt
  pubMsg : Msg → Pub
  depth : Nat → Nat
  table : Stmt → List Msg → Nat → Nat → F
  queries : PStmt → List (Pub × Nat) → List (Nat × Nat)
  verdict : PStmt → List (Pub × Nat) → List F → Bool

section Iop
variable {Stmt PStmt Msg Pub F D : Type} {k : Nat}

def OracleIop.pubTr (iop : OracleIop Stmt PStmt Msg Pub F k) (tr : List (Msg × Nat)) :
    List (Pub × Nat) :=
  tr.map (fun mc => (iop.pubMsg mc.1, mc.2))

def OracleIop.readValues (iop : OracleIop Stmt PStmt Msg Pub F k) (x : Stmt)
    (tr : List (Msg × Nat)) : List F :=
  (iop.queries (iop.pubStmt x) (iop.pubTr tr)).map
    (fun q => iop.table x (tr.map (fun mc => mc.1)) q.1 q.2)

/-- The IOP verifier: full length, then the verdict on the table values at the queries. -/
def OracleIop.verify (iop : OracleIop Stmt PStmt Msg Pub F k) (x : Stmt)
    (tr : List (Msg × Nat)) : Bool :=
  decide (tr.length = k) && iop.verdict (iop.pubStmt x) (iop.pubTr tr) (iop.readValues x tr)

theorem OracleIop.verify_eq (iop : OracleIop Stmt PStmt Msg Pub F k) (x : Stmt)
    (tr : List (Msg × Nat)) :
    iop.verify x tr =
      (decide (tr.length = k) &&
       iop.verdict (iop.pubStmt x) (tr.map (fun mc => (iop.pubMsg mc.1, mc.2)))
         ((iop.queries (iop.pubStmt x) (tr.map (fun mc => (iop.pubMsg mc.1, mc.2)))).map
           (fun q => iop.table x (tr.map (fun mc => mc.1)) q.1 q.2))) := by
  rfl

/-- The IOP as a `PublicCoinIop` of `MultiRoundFsQrom`. -/
def OracleIop.toPublicCoin (iop : OracleIop Stmt PStmt Msg Pub F k) : PublicCoinIop Stmt Msg k where
  challengeCard := fun _ => 2 ^ iop.w
  h_chal_pos := fun _ => Nat.two_pow_pos iop.w
  inLang := iop.inLang
  verify := iop.verify

/-- Boolean round-by-round state function for false statements: a false statement starts
    doomed, acceptance implies live, and for a false statement at most `bad r` of the `2^w`
    challenges of round `r` lead from a doomed prefix to a live one. Nothing is required of the
    state on true statements. -/
structure BoolRbrCert (iop : OracleIop Stmt PStmt Msg Pub F k) where
  state : Stmt → List (Msg × Nat) → Bool
  bad : Fin k → Nat
  init : ∀ x : Stmt, ¬ iop.inLang x → state x [] = false
  accept : ∀ (x : Stmt) (tr : List (Msg × Nat)), iop.verify x tr = true → state x tr = true
  flip : ∀ (x : Stmt), ¬ iop.inLang x → ∀ (r : Fin k) (pref : List (Msg × Nat)) (m : Msg),
    pref.length = r.1 → state x pref = false →
    qsum (2 ^ iop.w) (fun ch => if state x (pref ++ [(m, ch.1)]) = true then 1 else 0) ≤ bad r

/-- The certificate as an `RbrStateFunction`: a prefix is live when the statement is true or
    the Boolean state is. -/
def BoolRbrCert.toRbr {iop : OracleIop Stmt PStmt Msg Pub F k} (cert : BoolRbrCert iop) :
    RbrStateFunction iop.toPublicCoin where
  Live := fun x tr => iop.inLang x ∨ cert.state x tr = true
  badCard := cert.bad
  doomed_init := fun x hx hLive => by
    rcases hLive with h | h
    · exact hx h
    · rw [cert.init x hx] at h
      exact Bool.false_ne_true h
  accept_implies_live := fun x tr _ hv => .inr (cert.accept x tr hv)
  round_flip_bound := fun x r pref m hLen hDoomed L hNd hL => by
    have hx : ¬ iop.inLang x := fun h => hDoomed (.inl h)
    have hFalse : cert.state x pref = false := by
      cases h : cert.state x pref
      · rfl
      · exact absurd (.inr h) hDoomed
    have hSub : ∀ ch ∈ L, ch ∈ finFilterList (2 ^ iop.w)
        (fun ch => cert.state x (pref ++ [(m, ch.1)])) :=
      fun ch hch => finFilterList_complete _ _ ch
        (Decidable.of_not_not (fun hN => hL ch hch (fun hLive => by
          rcases hLive with h | h
          · exact hx h
          · exact hN h)))
    have h1 := nodup_length_le_of_subset hNd hSub
    exact Nat.le_trans (Nat.le_trans h1 (Nat.le_of_eq (finFilterList_length _ _)))
      (cert.flip x hx r pref m hLen hFalse)

/-- Classical adaptive state-restoration soundness of the certified IOP. -/
theorem BoolRbrCert.state_restoration_soundness [DecidableEq Msg]
    {iop : OracleIop Stmt PStmt Msg Pub F k} (cert : BoolRbrCert iop)
    (x : Stmt) (hx : ¬ iop.inLang x) (sched : List (Fin k))
    (tree : SrScheduleTree iop.toPublicCoin sched) :
    RatBound.le (srTreeAcceptProb iop.toPublicCoin tree x) (srScheduleErrorSum cert.toRbr sched) :=
  rbr_implies_state_restoration_soundness cert.toRbr x hx sched tree

def openingOk [DecidableEq D] (M : MerkleSetup D F) (depth : Nat → Nat) (roots : Nat → D)
    (q : Nat × Nat) (op : F × List D) : Bool :=
  decide (q.2 < 2 ^ depth q.1) && decide (op.2.length = depth q.1) &&
    decide (merklePathRoot M.node 0 q.2 (M.leaf q.1 q.2 op.1) op.2 = roots q.1)

def openingsOk [DecidableEq D] (M : MerkleSetup D F) (depth : Nat → Nat) (roots : Nat → D) :
    List (Nat × Nat) → List (F × List D) → Bool
  | [], [] => true
  | q :: qs, op :: ops => openingOk M depth roots q op && openingsOk M depth roots qs ops
  | _, _ => false

/-- The executable verifier. It holds roots, the public transcript and one opening
    `(value, authentication path)` per query; it never reads a table. -/
def execVerify [DecidableEq D] (iop : OracleIop Stmt PStmt Msg Pub F k) (M : MerkleSetup D F)
    (ps : PStmt) (roots : Nat → D) (ptr : List (Pub × Nat)) (ops : List (F × List D)) : Bool :=
  decide (ptr.length = k) && openingsOk M iop.depth roots (iop.queries ps ptr) ops &&
    iop.verdict ps ptr (ops.map (fun op => op.1))

/-- First collision among the openings, measured against the committed tables `tbl`. -/
def findCollision [DecidableEq D] [DecidableEq F] (M : MerkleSetup D F) (depth : Nat → Nat)
    (tbl : Nat → Nat → F) :
    List (Nat × Nat) → List (F × List D) → Option (CollisionWitness M.node M.leaf)
  | q :: qs, op :: ops =>
    if h : q.2 < 2 ^ depth q.1 ∧ op.2.length = depth q.1 ∧
        merklePathRoot M.node 0 q.2 (M.leaf q.1 q.2 op.1) op.2 = M.root q.1 (depth q.1) (tbl q.1) then
      match openingCollisionOpt M q.1 (depth q.1) (tbl q.1) q.2 op h.1 h.2.1 h.2.2 with
      | some c => some c
      | none => findCollision M depth tbl qs ops
    else findCollision M depth tbl qs ops
  | _, _ => none

theorem openings_agree [DecidableEq D] [DecidableEq F] (M : MerkleSetup D F) (depth : Nat → Nat)
    (tbl : Nat → Nat → F) :
    ∀ (qs : List (Nat × Nat)) (ops : List (F × List D)),
      openingsOk M depth (fun i => M.root i (depth i) (tbl i)) qs ops = true →
      findCollision M depth tbl qs ops = none →
      ops.map (fun op => op.1) = qs.map (fun q => tbl q.1 q.2)
  | [], [], _, _ => rfl
  | [], _ :: _, hOk, _ => absurd hOk (by show ¬ (false = true); exact Bool.false_ne_true)
  | _ :: _, [], hOk, _ => absurd hOk (by show ¬ (false = true); exact Bool.false_ne_true)
  | q :: qs, op :: ops, hOk, hNone => by
    have hOk' : (openingOk M depth (fun i => M.root i (depth i) (tbl i)) q op &&
        openingsOk M depth (fun i => M.root i (depth i) (tbl i)) qs ops) = true := hOk
    rw [Bool.and_eq_true] at hOk'
    obtain ⟨hHead, hTail⟩ := hOk'
    unfold openingOk at hHead
    rw [Bool.and_eq_true, Bool.and_eq_true] at hHead
    have hg : q.2 < 2 ^ depth q.1 ∧ op.2.length = depth q.1 ∧
        merklePathRoot M.node 0 q.2 (M.leaf q.1 q.2 op.1) op.2 = M.root q.1 (depth q.1) (tbl q.1) :=
      ⟨of_decide_eq_true hHead.1.1, of_decide_eq_true hHead.1.2, of_decide_eq_true hHead.2⟩
    unfold findCollision at hNone
    rw [dite_eq_left hg] at hNone
    cases hc : openingCollisionOpt M q.1 (depth q.1) (tbl q.1) q.2 op hg.1 hg.2.1 hg.2.2 with
    | some c =>
      rw [hc] at hNone
      cases hNone
    | none =>
      rw [hc] at hNone
      have hv := openingCollisionOpt_none M q.1 (depth q.1) (tbl q.1) q.2 op hg.1 hg.2.1 hg.2.2 hc
      have ih := openings_agree M depth tbl qs ops hTail hNone
      show op.1 :: ops.map (fun op => op.1) = tbl q.1 q.2 :: qs.map (fun q => tbl q.1 q.2)
      rw [hv, ih]

/-- **Executable acceptance reduces to a collision or to IOP acceptance.** -/
theorem exec_accept_reduces [DecidableEq D] [DecidableEq F]
    (iop : OracleIop Stmt PStmt Msg Pub F k) (M : MerkleSetup D F)
    (x : Stmt) (tr : List (Msg × Nat)) (ops : List (F × List D))
    (hExec : execVerify iop M (iop.pubStmt x)
      (fun i => M.root i (iop.depth i) (iop.table x (tr.map (fun mc => mc.1)) i))
      (iop.pubTr tr) ops = true)
    (hNone : findCollision M iop.depth (iop.table x (tr.map (fun mc => mc.1)))
      (iop.queries (iop.pubStmt x) (iop.pubTr tr)) ops = none) :
    iop.verify x tr = true := by
  unfold execVerify at hExec
  rw [Bool.and_eq_true, Bool.and_eq_true] at hExec
  obtain ⟨⟨hLen, hOpen⟩, hVerdict⟩ := hExec
  have hVals := openings_agree M iop.depth (iop.table x (tr.map (fun mc => mc.1))) _ ops hOpen hNone
  have hLen' : tr.length = k := by
    have h := of_decide_eq_true hLen
    unfold OracleIop.pubTr at h
    rw [List.length_map] at h
    exact h
  unfold OracleIop.verify OracleIop.readValues
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true hLen', ?_⟩
  rw [← hVals]
  exact hVerdict

end Iop

/-! ## §3. Fiat–Shamir over a uniformly random oracle -/

/-- Addresses of message prefixes in the oracle domain. `valid` carves out the (finite) set of
    well-shaped messages: outputs always decode to valid messages, and `enc` is injective on
    valid lists of at most `k` messages. -/
structure FsCodec (Msg : Type) (k cardX : Nat) where
  valid : Msg → Bool
  enc : List Msg → Fin cardX
  dec : Fin cardX → List Msg
  dec_valid : ∀ (o : Fin cardX) (m : Msg), m ∈ dec o → valid m = true
  dec_enc : ∀ ms : List Msg, ms.length ≤ k → (∀ m, m ∈ ms → valid m = true) → dec (enc ms) = ms

section Fs
variable {Msg : Type} {k cardX w : Nat}

theorem FsCodec.enc_inj (c : FsCodec Msg k cardX) {a b : List Msg}
    (ha : a.length ≤ k) (hb : b.length ≤ k)
    (hva : ∀ m, m ∈ a → c.valid m = true) (hvb : ∀ m, m ∈ b → c.valid m = true)
    (h : c.enc a = c.enc b) : a = b := by
  have h' := congrArg c.dec h
  rw [c.dec_enc a ha hva, c.dec_enc b hb hvb] at h'
  exact h'

/-- Fiat–Shamir transcript of the messages after prefix `pre`: the challenge of a round is the
    oracle value at the address of the prefix ending in that round's message. -/
def fsAux (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w) : List Msg → List Msg → List (Msg × Nat)
  | _, [] => []
  | pre, m :: rest => (m, (H (c.enc (pre ++ [m]))).toNat) :: fsAux c H (pre ++ [m]) rest

def fsTranscript (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w) (ms : List Msg) :
    List (Msg × Nat) :=
  fsAux c H [] ms

theorem fsAux_length (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w) :
    ∀ (ms pre : List Msg), (fsAux c H pre ms).length = ms.length
  | [], _ => by rfl
  | m :: rest, pre => by
    show (fsAux c H (pre ++ [m]) rest).length + 1 = rest.length + 1
    rw [fsAux_length c H rest]

theorem fsAux_map_fst (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w) :
    ∀ (ms pre : List Msg), (fsAux c H pre ms).map (fun mc => mc.1) = ms
  | [], _ => by rfl
  | m :: rest, pre => by
    show m :: (fsAux c H (pre ++ [m]) rest).map (fun mc => mc.1) = m :: rest
    rw [fsAux_map_fst c H rest]

theorem fsAux_append_single (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w) (m : Msg) :
    ∀ (a pre : List Msg),
      fsAux c H pre (a ++ [m]) = fsAux c H pre a ++ [(m, (H (c.enc (pre ++ a ++ [m]))).toNat)]
  | [], pre => by
    show [(m, (H (c.enc (pre ++ [m]))).toNat)] = [(m, (H (c.enc (pre ++ [] ++ [m]))).toNat)]
    rw [List.append_nil]
  | x :: a, pre => by
    show (x, (H (c.enc (pre ++ [x]))).toNat) :: fsAux c H (pre ++ [x]) (a ++ [m]) =
      (x, (H (c.enc (pre ++ [x]))).toNat) ::
        (fsAux c H (pre ++ [x]) a ++ [(m, (H (c.enc (pre ++ (x :: a) ++ [m]))).toNat)])
    rw [fsAux_append_single c H m a (pre ++ [x])]
    have e : pre ++ [x] ++ a = pre ++ (x :: a) := by
      rw [List.append_assoc]; rfl
    rw [e]

theorem fsAux_congr (c : FsCodec Msg k cardX) (H H' : Fin cardX → BitVec w) :
    ∀ (a pre : List Msg),
      (∀ j, j < a.length → H' (c.enc (pre ++ a.take (j + 1))) = H (c.enc (pre ++ a.take (j + 1)))) →
      fsAux c H' pre a = fsAux c H pre a
  | [], _, _ => by rfl
  | x :: a, pre, h => by
    show (x, (H' (c.enc (pre ++ [x]))).toNat) :: fsAux c H' (pre ++ [x]) a =
      (x, (H (c.enc (pre ++ [x]))).toNat) :: fsAux c H (pre ++ [x]) a
    have h0 : H' (c.enc (pre ++ [x])) = H (c.enc (pre ++ [x])) :=
      h 0 (Nat.zero_lt_succ _)
    have hT : fsAux c H' (pre ++ [x]) a = fsAux c H (pre ++ [x]) a := by
      apply fsAux_congr c H H' a (pre ++ [x])
      intro j hj
      have hj' := h (j + 1) (Nat.succ_lt_succ hj)
      have e : pre ++ (x :: a).take (j + 1 + 1) = pre ++ [x] ++ a.take (j + 1) := by
        rw [List.append_assoc]; rfl
      rw [e] at hj'
      exact hj'
    rw [h0, hT]

theorem first_flip (s : Nat → Bool) :
    ∀ (n : Nat), s 0 = false → s n = true → ∃ r, r < n ∧ s r = false ∧ s (r + 1) = true
  | 0, h0, hn => by rw [h0] at hn; exact absurd hn Bool.false_ne_true
  | n + 1, h0, hn => by
    cases hs : s n with
    | false => exact ⟨n, Nat.lt_succ_self n, hs, hn⟩
    | true =>
      obtain ⟨r, hr, h1, h2⟩ := first_flip s n h0 hs
      exact ⟨r, Nat.lt_succ_of_lt hr, h1, h2⟩

theorem split_last {α : Type} :
    ∀ (n : Nat) (l : List α), l.length = n + 1 → ∃ pre m, l = pre ++ [m] ∧ l.take n = pre
  | 0, [x], _ => ⟨[], x, rfl, rfl⟩
  | 0, [], h => absurd h (Nat.succ_ne_zero 0).symm
  | 0, _ :: _ :: _, h => absurd (Nat.succ.inj h) (Nat.succ_ne_zero _)
  | n + 1, [], h => absurd h (Nat.succ_ne_zero _).symm
  | n + 1, x :: t, h => by
    have ht : t.length = n + 1 := Nat.succ.inj h
    obtain ⟨pre, m, e, hTake⟩ := split_last n t ht
    refine ⟨x :: pre, m, ?_, ?_⟩
    · rw [e]; rfl
    · show x :: t.take n = x :: pre
      rw [hTake]

theorem qsum_term_le : ∀ (n : Nat) (f : Fin n → Nat) (i : Fin n), f i ≤ qsum n f
  | 0, _, i => Fin.elim0 i
  | _ + 1, _, ⟨0, _⟩ => by rw [qsum_succ]; exact Nat.le_add_right _ _
  | n + 1, f, ⟨j + 1, hj⟩ =>
    Nat.le_trans
      (qsum_term_le n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
      (by rw [qsum_succ]; exact Nat.le_add_left _ _)

/-- Projection of an output to the address of its length-`r + 1` message prefix. -/
def fsProj (c : FsCodec Msg k cardX) (r : Nat) (o : Fin cardX) : Fin cardX :=
  c.enc ((c.dec o).take (r + 1))

/-- The point is a canonical length-`r + 1` prefix whose length-`r` prefix is doomed. -/
def fsDoomed (c : FsCodec Msg k cardX) (st : List (Msg × Nat) → Bool) (r : Nat)
    (H : Fin cardX → BitVec w) (p : Fin cardX) : Bool :=
  decide (c.enc (c.dec p) = p ∧ (c.dec p).length = r + 1) &&
    !(st (fsTranscript c H ((c.dec p).take r)))

def fsLive (c : FsCodec Msg k cardX) (st : List (Msg × Nat) → Bool)
    (H : Fin cardX → BitVec w) (p : Fin cardX) : Bool :=
  st (fsTranscript c H (c.dec p))

theorem fs_reprogram_prefix (c : FsCodec Msg k cardX) (H : Fin cardX → BitVec w)
    (r : Nat) (hr : r + 1 ≤ k) (p : Fin cardX) (ch : BitVec w)
    (hg : c.enc (c.dec p) = p ∧ (c.dec p).length = r + 1) :
    fsTranscript c (reprogramOracle H p ch) ((c.dec p).take r) =
      fsTranscript c H ((c.dec p).take r) := by
  unfold fsTranscript
  apply fsAux_congr
  intro j _
  have hne : c.enc ([] ++ ((c.dec p).take r).take (j + 1)) ≠ p := by
    intro he
    have h1 : (((c.dec p).take r).take (j + 1)).length ≤ r := by
      rw [List.length_take, List.length_take]; omega
    have he' : c.enc (((c.dec p).take r).take (j + 1)) = c.enc (c.dec p) := by
      rw [hg.1]; exact he
    have h2 := c.enc_inj (by omega) (by omega)
      (fun m hm => c.dec_valid p m (List.mem_of_mem_take (List.mem_of_mem_take hm)))
      (c.dec_valid p) he'
    have h3 := congrArg List.length h2
    omega
  exact reprogramOracle_of_ne H p ch _ hne

/-- The Fiat–Shamir round as a `QromRbrRound`. -/
def fsRound {cardAnc : Nat} (c : FsCodec Msg k cardX) (st : List (Msg × Nat) → Bool)
    (bad : Fin k → Nat)
    (hFlip : ∀ (r : Fin k) (pref : List (Msg × Nat)) (m : Msg),
      pref.length = r.1 → st pref = false →
      qsum (2 ^ w) (fun ch => if st (pref ++ [(m, ch.1)]) = true then 1 else 0) ≤ bad r)
    (_cardAncTag : Fin (cardAnc + 1)) (r : Fin k) (H : Fin cardX → BitVec w) :
    QromRbrRound cardX w H where
  proj := fsProj c r.1
  isDoomedAt := fsDoomed c st r.1
  isLiveAfter := fsLive c st
  badCard := bad r
  doomed_local := by
    intro p ch
    unfold fsDoomed
    if hg : c.enc (c.dec p) = p ∧ (c.dec p).length = r.1 + 1 then
      rw [fs_reprogram_prefix c H r.1 r.2 p ch hg]
    else
      rw [decide_eq_false hg]
      rfl
  flip_bound := by
    intro p hDoomed
    unfold fsDoomed at hDoomed
    rw [Bool.and_eq_true] at hDoomed
    have hg : c.enc (c.dec p) = p ∧ (c.dec p).length = r.1 + 1 := of_decide_eq_true hDoomed.1
    have hPre : st (fsTranscript c H ((c.dec p).take r.1)) = false := by
      cases h : st (fsTranscript c H ((c.dec p).take r.1)) with
      | false => rfl
      | true => rw [h] at hDoomed; exact absurd hDoomed.2 Bool.false_ne_true
    obtain ⟨pre, m, hSplit, hTake⟩ := split_last r.1 (c.dec p) hg.2
    have hPreLen : (fsTranscript c H pre).length = r.1 := by
      unfold fsTranscript
      rw [fsAux_length, ← hTake, List.length_take, hg.2]
      omega
    have hEach : ∀ j : Fin (2 ^ w),
        fsLive c st (reprogramOracle H p (BitVec.ofFin j)) p =
          st (fsTranscript c H pre ++ [(m, j.1)]) := by
      intro j
      unfold fsLive
      have hT := fs_reprogram_prefix c H r.1 r.2 p (BitVec.ofFin j) hg
      rw [hTake] at hT
      have hAddr : c.enc ([] ++ pre ++ [m]) = p := by
        rw [List.nil_append, ← hSplit, hg.1]
      rw [hSplit]
      unfold fsTranscript at hT ⊢
      rw [fsAux_append_single, hT, hAddr]
      rw [reprogramOracle_self, BitVec.toNat_ofFin]
    rw [qsum_congr (fun j => by rw [hEach j])]
    rw [hTake] at hPre
    exact hFlip r (fsTranscript c H pre) m hPreLen hPre

/-- Mass of an event covered by per-round flags at projected points. -/
theorem cover_mass {cardAnc : Nat} (ψ : QVec cardX w cardAnc) (acc : Fin cardX → Bool)
    (proj : Fin k → Fin cardX → Fin cardX) (flag : Fin k → Fin cardX → Bool)
    (h : ∀ o, acc o = true → ∃ r, flag r (proj r o) = true) :
    QVec.queryMassOn acc ψ ≤
      qsum k (fun r => qsum cardX (fun p =>
        if flag r p = true then QVec.queryMassOn (fun z => decide (p = proj r z)) ψ else 0)) := by
  have key : ∀ r : Fin k,
      qsum cardX (fun p =>
        if flag r p = true then QVec.queryMassOn (fun z => decide (p = proj r z)) ψ else 0) =
      qsum cardX (fun o => if flag r (proj r o) = true then QVec.queryWeight ψ o else 0) := by
    intro r
    have e1 : ∀ p : Fin cardX,
        (if flag r p = true then QVec.queryMassOn (fun z => decide (p = proj r z)) ψ else 0) =
        qsum cardX (fun o => if p = proj r o then
          (if flag r (proj r o) = true then QVec.queryWeight ψ o else 0) else 0) := by
      intro p
      rw [QVec.queryMassOn_def]
      cases hf : flag r p with
      | false =>
        rw [ite_eq_right Bool.false_ne_true]
        have hz : ∀ o : Fin cardX, (if p = proj r o then
            (if flag r (proj r o) = true then QVec.queryWeight ψ o else 0) else 0) = 0 := by
          intro o
          if hp : p = proj r o then
            rw [ite_eq_left hp, ← hp, hf, ite_eq_right Bool.false_ne_true]
          else
            rw [ite_eq_right hp]
        rw [qsum_congr hz, qsum_const, Nat.mul_zero]
      | true =>
        rw [ite_eq_left rfl]
        apply qsum_congr
        intro o
        if hp : p = proj r o then
          rw [ite_eq_left (decide_eq_true hp), ite_eq_left hp, ← hp, hf, ite_eq_left rfl]
        else
          rw [ite_eq_right (fun hd => hp (of_decide_eq_true hd)), ite_eq_right hp]
    rw [qsum_congr e1, qsum_comm]
    apply qsum_congr
    intro o
    exact qsum_ite_eq cardX (proj r o) _
  rw [qsum_congr key, qsum_comm, QVec.queryMassOn_def]
  apply qsum_le_qsum
  intro o
  cases ha : acc o with
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    exact Nat.zero_le _
  | true =>
    obtain ⟨r, hr⟩ := h o ha
    rw [ite_eq_left rfl]
    have hTerm := qsum_term_le k
      (fun r => if flag r (proj r o) = true then QVec.queryWeight ψ o else 0) r
    have hEq : (if flag r (proj r o) = true then QVec.queryWeight ψ o else 0) =
        QVec.queryWeight ψ o := by rw [ite_eq_left hr]
    rw [hEq] at hTerm
    exact hTerm

/-- **Fiat–Shamir QROM soundness from a Boolean state function.** If acceptance of an output
    forces a full-length message list whose Fiat–Shamir transcript is live, while the empty
    transcript is doomed and each round flips on at most `bad r` challenges, then the acceptance
    mass of any `Q`-query adversary, averaged over the oracle, is at most
    `(2Q+1)² · Σ_r bad r / 2^w`. -/
theorem fs_qrom_bool_rbr_soundness {cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (c : FsCodec Msg k cardX)
    (st : List (Msg × Nat) → Bool) (bad : Fin k → Nat)
    (hInit : st [] = false)
    (hFlip : ∀ (r : Fin k) (pref : List (Msg × Nat)) (m : Msg),
      pref.length = r.1 → st pref = false →
      qsum (2 ^ w) (fun ch => if st (pref ++ [(m, ch.1)]) = true then 1 else 0) ≤ bad r)
    (accept : (Fin cardX → BitVec w) → Fin cardX → Bool)
    (hAcc : ∀ H o, accept H o = true →
      (c.dec o).length = k ∧ st (fsTranscript c H (c.dec o)) = true) :
    RatBound.le
      ⟨uniformOracleSum w cardX (fun H => QVec.queryMassOn (accept H) (runQuantumAdv A H)),
        (2 ^ w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      ⟨(2 * Q + 1) ^ 2 * qsum k bad, 2 ^ w, Nat.two_pow_pos w⟩ := by
  refine qrom_uniform_oracle_success_bound A accept
    (fun r H => fsRound (cardAnc := cardAnc) c st bad hFlip 0 r H)
    (fun r => fsProj c r.1) (fun r => fsDoomed c st r.1) (fun _ => fsLive c st) bad
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) ?_
  intro H
  simp only [qromOrdinaryFlipMass_def]
  refine cover_mass (runQuantumAdv A H) (accept H) (fun r => fsProj c r.1)
    (fun r p => fsDoomed c st r.1 H p && fsLive c st H p) ?_
  intro o ho
  obtain ⟨hLen, hLive⟩ := hAcc H o ho
  have h0 : (fun j => st (fsTranscript c H ((c.dec o).take j))) 0 = false := hInit
  have hk : (fun j => st (fsTranscript c H ((c.dec o).take j))) k = true := by
    show st (fsTranscript c H ((c.dec o).take k)) = true
    rw [List.take_of_length_le (Nat.le_of_eq hLen)]
    exact hLive
  obtain ⟨r, hr, hF, hT⟩ :=
    first_flip (fun j => st (fsTranscript c H ((c.dec o).take j))) k h0 hk
  refine ⟨⟨r, hr⟩, ?_⟩
  have hTakeLen : ((c.dec o).take (r + 1)).length = r + 1 := by
    rw [List.length_take, hLen]; omega
  have hDec : c.dec (fsProj c r o) = (c.dec o).take (r + 1) := by
    unfold fsProj
    exact c.dec_enc _ (by omega) (fun m hm => c.dec_valid o m (List.mem_of_mem_take hm))
  have hTT : ((c.dec o).take (r + 1)).take r = (c.dec o).take r := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_succ r)]
  rw [Bool.and_eq_true]
  constructor
  · unfold fsDoomed
    rw [Bool.and_eq_true]
    refine ⟨decide_eq_true ⟨?_, ?_⟩, ?_⟩
    · rw [hDec]; rfl
    · rw [hDec]; exact hTakeLen
    · rw [hDec, hTT]
      have hF' : st (fsTranscript c H ((c.dec o).take r)) = false := hF
      rw [hF']; rfl
  · unfold fsLive
    rw [hDec]
    exact hT

end Fs

/-! ## §4. The closed theorem -/

section Closed
variable {Stmt PStmt Msg Pub F D : Type} {k cardX : Nat}

/-- The executable verifier run on an adversary output `o` under Fiat–Shamir oracle `H`: the
    messages are `c.dec o`, the challenges are derived from `H`, the roots are the commitments to
    the tables carried by the messages, the openings are `aux o`. -/
def execFsAccept [DecidableEq D] (iop : OracleIop Stmt PStmt Msg Pub F k) (M : MerkleSetup D F)
    (c : FsCodec Msg k cardX) (aux : Fin cardX → List (F × List D)) (x : Stmt)
    (H : Fin cardX → BitVec iop.w) (o : Fin cardX) : Bool :=
  execVerify iop M (iop.pubStmt x)
    (fun i => M.root i (iop.depth i)
      (iop.table x ((fsTranscript c H (c.dec o)).map (fun mc => mc.1)) i))
    (iop.pubTr (fsTranscript c H (c.dec o))) (aux o)

/-- The collision finder run on the same output. -/
def execFsCollision [DecidableEq D] [DecidableEq F] (iop : OracleIop Stmt PStmt Msg Pub F k)
    (M : MerkleSetup D F) (c : FsCodec Msg k cardX) (aux : Fin cardX → List (F × List D))
    (x : Stmt) (H : Fin cardX → BitVec iop.w) (o : Fin cardX) :
    Option (CollisionWitness M.node M.leaf) :=
  findCollision M iop.depth (iop.table x ((fsTranscript c H (c.dec o)).map (fun mc => mc.1)))
    (iop.queries (iop.pubStmt x) (iop.pubTr (fsTranscript c H (c.dec o)))) (aux o)

/-- The event "the executable verifier accepts and the collision finder succeeds". -/
def execFsCollisionEvent [DecidableEq D] [DecidableEq F] (iop : OracleIop Stmt PStmt Msg Pub F k)
    (M : MerkleSetup D F) (c : FsCodec Msg k cardX) (aux : Fin cardX → List (F × List D))
    (x : Stmt) (H : Fin cardX → BitVec iop.w) (o : Fin cardX) : Bool :=
  execFsAccept iop M c aux x H o && (execFsCollision iop M c aux x H o).isSome

/-- **Closed executable-verifier soundness in the QROM.** For a false statement, any Boolean
    round-by-round certificate of the IOP and any `Q`-query adversary:
    `Pr[execVerify accepts] ≤ (2Q+1)² · Σ_r bad_r / 2^w + Pr[accepts and findCollision succeeds]`,
    both probabilities over the uniform Fiat–Shamir oracle and the adversary's measurement. -/
theorem exec_fs_qrom_closed_soundness [DecidableEq D] [DecidableEq F] {cardAnc Q : Nat}
    (iop : OracleIop Stmt PStmt Msg Pub F k) (M : MerkleSetup D F)
    (cert : BoolRbrCert iop) (c : FsCodec Msg k cardX)
    (aux : Fin cardX → List (F × List D))
    (x : Stmt) (hx : ¬ iop.inLang x)
    (A : QuantumAdv cardX iop.w cardAnc Q) :
    RatBound.le
      ⟨uniformOracleSum iop.w cardX (fun H =>
          QVec.queryMassOn (execFsAccept iop M c aux x H) (runQuantumAdv A H)),
        (2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos iop.w))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
      (RatBound.add
        ⟨(2 * Q + 1) ^ 2 * qsum k cert.bad, 2 ^ iop.w, Nat.two_pow_pos iop.w⟩
        ⟨uniformOracleSum iop.w cardX (fun H =>
            QVec.queryMassOn (execFsCollisionEvent iop M c aux x H) (runQuantumAdv A H)),
          (2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init),
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos iop.w))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩) := by
  let noColl : (Fin cardX → BitVec iop.w) → Fin cardX → Bool := fun H o =>
    execFsAccept iop M c aux x H o && !(execFsCollision iop M c aux x H o).isSome
  have hNo := fs_qrom_bool_rbr_soundness A c (cert.state x) cert.bad (cert.init x hx)
    (fun r pref m hl hd => cert.flip x hx r pref m hl hd) noColl
    (by
      intro H o ho
      have ho' : (execFsAccept iop M c aux x H o &&
          !(execFsCollision iop M c aux x H o).isSome) = true := ho
      rw [Bool.and_eq_true] at ho'
      have hNone : execFsCollision iop M c aux x H o = none := by
        cases hc : execFsCollision iop M c aux x H o with
        | none => rfl
        | some w =>
          rw [hc] at ho'
          exact absurd ho'.2 Bool.false_ne_true
      have hVer := exec_accept_reduces iop M x (fsTranscript c H (c.dec o)) (aux o) ho'.1 hNone
      refine ⟨?_, cert.accept x _ hVer⟩
      unfold OracleIop.verify at hVer
      rw [Bool.and_eq_true] at hVer
      have hLen := of_decide_eq_true hVer.1
      unfold fsTranscript at hLen
      rw [fsAux_length] at hLen
      exact hLen)
  have hSplit : ∀ H : Fin cardX → BitVec iop.w,
      QVec.queryMassOn (execFsAccept iop M c aux x H) (runQuantumAdv A H) ≤
        QVec.queryMassOn (noColl H) (runQuantumAdv A H) +
          QVec.queryMassOn (execFsCollisionEvent iop M c aux x H) (runQuantumAdv A H) := by
    intro H
    refine Nat.le_trans ?_ (queryMassOn_union_le (noColl H)
      (execFsCollisionEvent iop M c aux x H) (runQuantumAdv A H))
    rw [QVec.queryMassOn_def, QVec.queryMassOn_def]
    apply qsum_le_qsum
    intro o
    cases ha : execFsAccept iop M c aux x H o with
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      exact Nat.zero_le _
    | true =>
      have hOr : (noColl H o || execFsCollisionEvent iop M c aux x H o) = true := by
        show ((execFsAccept iop M c aux x H o &&
            !(execFsCollision iop M c aux x H o).isSome) ||
          (execFsAccept iop M c aux x H o &&
            (execFsCollision iop M c aux x H o).isSome)) = true
        rw [ha]
        cases (execFsCollision iop M c aux x H o).isSome <;> rfl
      rw [ite_eq_left rfl, ite_eq_left hOr]
      exact Nat.le_refl _
  have hSum := uniformOracleSum_le iop.w cardX _ _ hSplit
  rw [uniformOracleSum_add] at hSum
  have hNo' : uniformOracleSum iop.w cardX (fun H =>
        QVec.queryMassOn (noColl H) (runQuantumAdv A H)) * 2 ^ iop.w ≤
      (2 * Q + 1) ^ 2 * qsum k cert.bad *
        ((2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) := hNo
  show uniformOracleSum iop.w cardX (fun H =>
        QVec.queryMassOn (execFsAccept iop M c aux x H) (runQuantumAdv A H)) *
      (2 ^ iop.w * ((2 ^ iop.w) ^ cardX *
        (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init))) ≤
    ((2 * Q + 1) ^ 2 * qsum k cert.bad *
        ((2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init)) +
      uniformOracleSum iop.w cardX (fun H =>
        QVec.queryMassOn (execFsCollisionEvent iop M c aux x H) (runQuantumAdv A H)) * 2 ^ iop.w) *
      ((2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init))
  generalize (2 ^ iop.w) ^ cardX * (prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init) = N
    at hNo' ⊢
  generalize uniformOracleSum iop.w cardX (fun H =>
    QVec.queryMassOn (execFsAccept iop M c aux x H) (runQuantumAdv A H)) = a at hSum ⊢
  generalize uniformOracleSum iop.w cardX (fun H =>
    QVec.queryMassOn (noColl H) (runQuantumAdv A H)) = a1 at hSum hNo'
  generalize uniformOracleSum iop.w cardX (fun H =>
    QVec.queryMassOn (execFsCollisionEvent iop M c aux x H) (runQuantumAdv A H)) = cc at hSum ⊢
  generalize (2 * Q + 1) ^ 2 * qsum k cert.bad = B at hNo' ⊢
  generalize 2 ^ iop.w = W at hNo' ⊢
  have h1 : a * (W * N) ≤ (a1 + cc) * (W * N) := Nat.mul_le_mul_right _ hSum
  have h2 : (a1 + cc) * (W * N) = a1 * W * N + cc * W * N := by
    rw [Nat.add_mul, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have h3 : a1 * W * N ≤ B * N * N := Nat.mul_le_mul_right N hNo'
  have h4 : (B * N + cc * W) * N = B * N * N + cc * W * N := Nat.add_mul _ _ _
  rw [h4]
  rw [h2] at h1
  exact Nat.le_trans h1 (Nat.add_le_add_right h3 _)

/-- Whenever the collision event holds, the finder's output is a collision witness (as data). -/
def execFsCollisionWitness [DecidableEq D] [DecidableEq F] (iop : OracleIop Stmt PStmt Msg Pub F k)
    (M : MerkleSetup D F) (c : FsCodec Msg k cardX) (aux : Fin cardX → List (F × List D))
    (x : Stmt) (H : Fin cardX → BitVec iop.w) (o : Fin cardX)
    (h : execFsCollisionEvent iop M c aux x H o = true) : CollisionWitness M.node M.leaf :=
  match hc : execFsCollision iop M c aux x H o with
  | some wit => wit
  | none => absurd h (by
      unfold execFsCollisionEvent
      rw [hc]
      cases execFsAccept iop M c aux x H o <;> exact Bool.false_ne_true)

end Closed

#verify_constructive Qsag.ClosedFs.merklePathRoot_eq_merkleRootFromPath
#verify_constructive Qsag.ClosedFs.treePathFrom_length
#verify_constructive Qsag.ClosedFs.treePathFrom_opens
#verify_constructive Qsag.ClosedFs.openingCollisionOpt_none
#verify_constructive Qsag.ClosedFs.openings_agree
#verify_constructive Qsag.ClosedFs.exec_accept_reduces
#verify_constructive Qsag.ClosedFs.BoolRbrCert.state_restoration_soundness
#verify_constructive Qsag.ClosedFs.FsCodec.enc_inj
#verify_constructive Qsag.ClosedFs.fsAux_length
#verify_constructive Qsag.ClosedFs.fsAux_map_fst
#verify_constructive Qsag.ClosedFs.fsAux_append_single
#verify_constructive Qsag.ClosedFs.fsAux_congr
#verify_constructive Qsag.ClosedFs.first_flip
#verify_constructive Qsag.ClosedFs.split_last
#verify_constructive Qsag.ClosedFs.qsum_term_le
#verify_constructive Qsag.ClosedFs.fs_reprogram_prefix
#verify_constructive Qsag.ClosedFs.cover_mass
#verify_constructive Qsag.ClosedFs.fs_qrom_bool_rbr_soundness
#verify_constructive Qsag.ClosedFs.exec_fs_qrom_closed_soundness

end Qsag.ClosedFs
end
