module
/-
Hybrid envelope reductions, policy release composition and production parameter classification.
The hash interface below represents domain-separated, decoded preimages, not an assumption
that hashing is injective. Every failed binding returns distinct colliding preimages.
Signature verification and threshold share provenance are explicit cryptographic interfaces;
these are conditional reductions, not proofs of ECDSA, ML-DSA or a Rust refinement.
Address metadata binds the expected address; the Rust signing transcript itself omits HRP
and address version. Applications needing network-exclusive signatures must bind them in msg.
-/
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Oracle.Sponge
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Algebra
public section
namespace Qsag.HybridSecurity
set_option autoImplicit false
set_option exponentiation.threshold 2048

abbrev Bytes := List UInt8
abbrev Digest := Fin (256 ^ 32)

/-- Rust's little-endian u64 frame prefix (on supported 32/64-bit targets). -/
def frame64 (x : Bytes) : Bytes := (be 8 x.length).reverse ++ x

theorem frame64_prefix_injective {x y a b : Bytes}
    (hx : x.length < 256 ^ 8) (hy : y.length < 256 ^ 8)
    (h : frame64 x ++ a = frame64 y ++ b) : x = y ∧ a = b := by
  simp only [frame64, List.append_assoc] at h
  obtain ⟨hp, ht⟩ := List.append_inj h (by simp only [List.length_reverse, length_be])
  have hn := be_injective hx hy (List.reverse_inj.mp hp)
  exact List.append_inj ht hn

inductive Suite where
  | secpMl44 | edMl65
  deriving DecidableEq, Repr

def suiteBytes : Suite → Bytes
  | .secpMl44 => [5, 1, 0, 1, 1, 1]
  | .edMl65 => [5, 2, 0, 2, 1, 2]

structure Keys where
  suite : Suite
  classical : Bytes
  pq : Bytes
  deriving DecidableEq

inductive Preimage where
  | key (pq : Bool) (suite : Suite) (pk : Bytes)
  | identity (suite : Suite) (classical pq : Digest)
  | address (hrp : Bytes) (version : Nat) (suite : Suite) (id : Digest)
  deriving DecidableEq

abbrev Hash := Preimage → Digest
def Collision (H : Hash) : Prop := ∃ x y, x ≠ y ∧ H x = H y
def keyHash (H : Hash) (k : Keys) (pq : Bool) : Digest :=
  H (.key pq k.suite (if pq then k.pq else k.classical))
def idInput (H : Hash) (k : Keys) : Preimage :=
  .identity k.suite (keyHash H k false) (keyHash H k true)
def idCommit (H : Hash) (k : Keys) : Digest := H (idInput H k)

structure QsagAddress where
  hrp : Bytes
  version : Nat
  suite : Suite
  commitment : Digest

def addressOf (H : Hash) (k : Keys) (hrp : Bytes) (v : Nat) : QsagAddress :=
  ⟨hrp, v, k.suite, H (.address hrp v k.suite (idCommit H k))⟩

structure Transcript where
  pq : Bool
  suite : Suite
  id : Digest
  classicalDigest : Digest
  pqDigest : Digest
  msg : Bytes
  deriving DecidableEq

def transcript (H : Hash) (k : Keys) (pq : Bool) (msg : Bytes) : Transcript :=
  ⟨pq, k.suite, idCommit H k, keyHash H k false, keyHash H k true, msg⟩

/-- Exact V2 transcript, including the BE u64 message length. -/
def Transcript.bytes (t : Transcript) : Bytes :=
  "QSAG.HYBRID.V2".toUTF8.toList ++
  ((if t.pq then 2 else 1) :: (suiteBytes t.suite ++
  (be 32 t.id.val ++ (be 32 t.classicalDigest.val ++
  (be 32 t.pqDigest.val ++ (be 8 t.msg.length ++ t.msg))))))

theorem transcript_bytes_injective {x y : Transcript} (h : x.bytes = y.bytes) : x = y := by
  have h := List.append_cancel_left h
  obtain ⟨hr, h⟩ := List.cons.inj h
  have hr' : x.pq = y.pq := by
    cases hx : x.pq <;> cases hy : y.pq <;> simp_all
  obtain ⟨hs, h⟩ := List.append_inj h (by cases x.suite <;> cases y.suite <;> rfl)
  have hs' : x.suite = y.suite := by
    cases hx : x.suite <;> cases hy : y.suite <;> simp_all [suiteBytes]
  obtain ⟨hi, h⟩ := List.append_inj h (by simp only [length_be])
  obtain ⟨hc, h⟩ := List.append_inj h (by simp only [length_be])
  obtain ⟨hp, h⟩ := List.append_inj h (by simp only [length_be])
  obtain ⟨_, hm⟩ := List.append_inj h (by simp only [length_be])
  have hi' := Fin.ext (be_injective x.id.isLt y.id.isLt hi)
  have hc' := Fin.ext (be_injective x.classicalDigest.isLt y.classicalDigest.isLt hc)
  have hp' := Fin.ext (be_injective x.pqDigest.isLt y.pqDigest.isLt hp)
  cases x; cases y; cases hr'; cases hs'; cases hi'; cases hc'; cases hp'; cases hm; rfl

structure HybridPinnedEnvelope where
  keys : Keys
  classicalSignature : Bytes
  pqSignature : Bytes

abbrev Verifier := Bytes → Transcript → Bytes → Bool
def verifyWith (H : Hash) (vc vp : Verifier) (e : HybridPinnedEnvelope) (m : Bytes) : Prop :=
  vc e.keys.classical (transcript H e.keys false m) e.classicalSignature = true ∧
  vp e.keys.pq (transcript H e.keys true m) e.pqSignature = true

def validateForAddress (H : Hash) (e : HybridPinnedEnvelope) (a : QsagAddress) : Prop :=
  e.keys.suite = a.suite ∧
  H (.address a.hrp a.version e.keys.suite (idCommit H e.keys)) = a.commitment

theorem equal_hash_extract (H : Hash) {x y : Preimage} (h : H x = H y) :
    x = y ∨ Collision H := by
  by_cases he : x = y
  · exact .inl he
  · exact .inr ⟨x, y, he, h⟩

theorem identity_binding (H : Hash) (a b : Keys) (h : idCommit H a = idCommit H b) :
    a = b ∨ Collision H := by
  rcases equal_hash_extract H h with he | bad
  · obtain ⟨hs, hc, hp⟩ := Preimage.identity.inj he
    rcases equal_hash_extract H hc with hc | bad
    · rcases equal_hash_extract H hp with hp | bad
      · have hc' := (Preimage.key.inj hc).2.2
        have hp' := (Preimage.key.inj hp).2.2
        cases a; cases b; simp only [Bool.false_eq_true, ↓reduceIte] at hc' hp'
        cases hs; cases hc'; cases hp'; exact .inl rfl
      · exact .inr bad
    · exact .inr bad
  · exact .inr bad

theorem address_binding (H : Hash) (e : HybridPinnedEnvelope) (k : Keys) (hrp : Bytes) (v : Nat)
    (h : validateForAddress H e (addressOf H k hrp v)) : e.keys = k ∨ Collision H := by
  rcases equal_hash_extract H h.2 with he | bad
  · exact identity_binding H e.keys k (Preimage.address.inj he).2.2.2
  · exact .inr bad

/-- EUF freshness is on messages, not signature bytes; both role oracles see the same queries. -/
def ComponentForgery (V : Verifier) (pk : Bytes) (tr : Transcript) (sig : Bytes)
    (queries : List Transcript) : Prop := V pk tr sig = true ∧ tr ∉ queries

theorem fresh_transcript (H : Hash) (k : Keys) (role : Bool) (m : Bytes) (qs : List Bytes)
    (fresh : m ∉ qs) : transcript H k role m ∉ qs.map (transcript H k role) := by
  intro h
  obtain ⟨q, hq, he⟩ := List.mem_map.mp h
  have hm : q = m := congrArg Transcript.msg he
  exact fresh (hm ▸ hq)

/-- Every fresh fixed-address forgery extracts BOTH component forgeries or a hash collision.
The component games must use the same attack model (quantum if the adversary is quantum). -/
theorem dual_key_euf_cma (H : Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes) (v : Nat)
    (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes)
    (bound : validateForAddress H e (addressOf H k hrp v))
    (valid : verifyWith H vc vp e m) (fresh : m ∉ qs) :
    (ComponentForgery vc k.classical (transcript H k false m) e.classicalSignature
      (qs.map (transcript H k false)) ∧
     ComponentForgery vp k.pq (transcript H k true m) e.pqSignature
      (qs.map (transcript H k true))) ∨ Collision H := by
  rcases address_binding H e k hrp v bound with hk | bad
  · unfold verifyWith at valid
    rw [hk] at valid
    exact .inl ⟨⟨valid.1, fresh_transcript H k false m qs fresh⟩,
      ⟨valid.2, fresh_transcript H k true m qs fresh⟩⟩
  · exact .inr bad

/-- An honest PQ signature cannot be re-bound to a different classical key without
a new PQ-message forgery or a classical public-key hash collision. No classical security used. -/
theorem rogue_partner_resistance (H : Hash) (vp : Verifier) (a b : Keys) (m : Bytes)
    (sig : Bytes) (qs : List Bytes) (samePq : a.pq = b.pq)
    (changed : a.classical ≠ b.classical)
    (valid : vp b.pq (transcript H b true m) sig = true) :
    ComponentForgery vp a.pq (transcript H b true m) sig (qs.map (transcript H a true)) ∨
      Collision H := by
  by_cases hc : keyHash H a false = keyHash H b false
  · exact .inr ⟨.key false a.suite a.classical, .key false b.suite b.classical,
      fun he => changed (Preimage.key.inj he).2.2, hc⟩
  · refine .inl ⟨samePq ▸ valid, ?_⟩
    intro hm
    obtain ⟨q, _, he⟩ := List.mem_map.mp hm
    exact hc (congrArg Transcript.classicalDigest he)

def naiveTranscript (_k : Keys) (m : Bytes) : Bytes := m
theorem naive_rogue_rebinding : ∃ a b : Keys, a.pq = b.pq ∧ a.classical ≠ b.classical ∧
    naiveTranscript a [7] = naiveTranscript b [7] :=
  ⟨⟨.secpMl44, [1], [3]⟩, ⟨.secpMl44, [2], [3]⟩, rfl, by decide, rfl⟩

/-- Weighted event masses; divide by the common positive total weight for advantages. -/
def mass {N : Nat} (w : Fin N → Nat) (event : Fin N → Bool) : Nat :=
  qsum N (fun i => if event i then w i else 0)

theorem robust_min_bound {N : Nat} (w : Fin N → Nat) (win c p bad : Fin N → Bool)
    (extract : ∀ i, win i = true → (c i = true ∧ p i = true) ∨ bad i = true) :
    mass w win ≤ min (mass w c) (mass w p) + mass w bad := by
  have hc := qsum_le_qsum (f := fun i => if win i then w i else 0)
    (g := fun i => (if c i then w i else 0) + (if bad i then w i else 0)) (by
      intro i; cases hw : win i
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · rcases extract i hw with ⟨hc, _⟩ | hb <;> simp_all)
  have hp := qsum_le_qsum (f := fun i => if win i then w i else 0)
    (g := fun i => (if p i then w i else 0) + (if bad i then w i else 0)) (by
      intro i; cases hw : win i
      · simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · rcases extract i hw with ⟨_, hp⟩ | hb <;> simp_all)
  rw [qsum_add] at hc hp
  change mass w win ≤ mass w c + mass w bad at hc
  change mass w win ≤ mass w p + mass w bad at hp
  omega

/-- Setting either component's bound to the whole sample space leaves the other bound. -/
theorem total_component_break {hybrid classical pq collision total : Nat}
    (h : hybrid ≤ min classical pq + collision) (hc : classical = total) (hp : pq ≤ total) :
    hybrid ≤ pq + collision := by omega

def hybridWins (H : Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes) (v : Nat)
    (qs : List Bytes) (o : HybridPinnedEnvelope × Bytes) : Bool :=
  decide (o.1.keys.suite = k.suite) &&
  decide (H (.address hrp v o.1.keys.suite (idCommit H o.1.keys)) =
    (addressOf H k hrp v).commitment) &&
  vc o.1.keys.classical (transcript H o.1.keys false o.2) o.1.classicalSignature &&
  vp o.1.keys.pq (transcript H o.1.keys true o.2) o.1.pqSignature && decide (o.2 ∉ qs)

/-- The concrete hybrid experiment, with key substitution counted only on accepting runs.
Each counted bad run supplies a collision; both extracted component games retain freshness.
This is the min bound with a common denominator, including nonuniform integer weights. -/
theorem hybrid_advantage_bound {N : Nat} (w : Fin N → Nat) (H : Hash) (vc vp : Verifier)
    (k : Keys) (hrp : Bytes) (v : Nat) (qs : List Bytes) (out : Fin N → HybridPinnedEnvelope × Bytes) :
    let win := fun j => hybridWins H vc vp k hrp v qs (out j)
    let c := fun j => vc k.classical (transcript H k false (out j).2)
      (out j).1.classicalSignature && decide ((out j).2 ∉ qs)
    let p := fun j => vp k.pq (transcript H k true (out j).2)
      (out j).1.pqSignature && decide ((out j).2 ∉ qs)
    let bad := fun j => win j && decide ((out j).1.keys ≠ k)
    mass w win ≤ min (mass w c) (mass w p) + mass w bad ∧
    (∀ j, bad j = true → Collision H) := by
  intro win c p bad
  have decode (j : Fin N) (h : win j = true) :
      validateForAddress H (out j).1 (addressOf H k hrp v) ∧
      verifyWith H vc vp (out j).1 (out j).2 ∧ (out j).2 ∉ qs := by
    simp only [win, hybridWins, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨⟨h.1.1.1.1, h.1.1.1.2⟩, ⟨h.1.1.2, h.1.2⟩, h.2⟩
  constructor
  · apply robust_min_bound
    intro j hj
    by_cases hk : (out j).1.keys = k
    · have h := decode j hj
      unfold verifyWith at h
      rw [hk] at h
      apply Or.inl
      simpa only [c, p, Bool.and_eq_true, decide_eq_true_eq] using
        And.intro (And.intro h.2.1.1 h.2.2) (And.intro h.2.1.2 h.2.2)
    · apply Or.inr
      simpa only [bad, Bool.and_eq_true, decide_eq_true_eq] using And.intro hj hk
  · intro j hj
    have h : win j = true ∧ (out j).1.keys ≠ k := by
      simpa only [bad, Bool.and_eq_true, decide_eq_true_eq] using hj
    rcases address_binding H (out j).1 k hrp v (decode j h.1).1 with hk | hc
    · exact False.elim (h.2 hk)
    · exact hc

-- POLICY

def cardinal {n : Nat} (q : Fin n → Bool) : Nat := qsum n (fun i => if q i then 1 else 0)

theorem honest_in_quorum {n t f : Nat} (q corrupt : Fin n → Bool)
    (hq : t ≤ cardinal q) (hf : cardinal corrupt ≤ f) (ht : f < t) :
    ∃ i, q i = true ∧ corrupt i = false := by
  by_cases h : ∃ i, q i = true ∧ corrupt i = false
  · exact h
  · have le : cardinal q ≤ cardinal corrupt := qsum_le_qsum (by
      intro i; cases hq : q i <;> cases hc : corrupt i <;> simp_all)
    omega

theorem honest_quorum_intersection {n t f : Nat} (q r corrupt : Fin n → Bool)
    (hq : t ≤ cardinal q) (hr : t ≤ cardinal r) (hf : cardinal corrupt ≤ f)
    (overlap : n + f < 2 * t) : ∃ i, q i = true ∧ r i = true ∧ corrupt i = false := by
  by_cases h : ∃ i, q i = true ∧ r i = true ∧ corrupt i = false
  · exact h
  · have le := qsum_le_qsum (f := fun i => (if q i then 1 else 0) + (if r i then 1 else 0))
      (g := fun i => 1 + (if corrupt i then 1 else 0)) (by
        intro i; cases hq : q i <;> cases hr : r i <;> cases hc : corrupt i <;> simp_all)
    rw [qsum_add, qsum_add, qsum_const] at le
    change cardinal q + cardinal r ≤ n * 1 + cardinal corrupt at le
    omega

/-- Pairwise honest intersections suffice for global nonce uniqueness, even though they
do not suffice for a global cumulative sum. Local uniqueness comes from ledger_trace_safety. -/
theorem intersecting_nonce_distinct {n K t f : Nat} (q : Fin K → Fin n → Bool)
    (corrupt : Fin n → Bool) (nonce : Fin K → Nat) (sizes : ∀ a, t ≤ cardinal (q a))
    (hf : cardinal corrupt ≤ f) (overlap : n + f < 2 * t)
    (localUnique : ∀ j, corrupt j = false → ∀ a b, a ≠ b →
      q a j = true → q b j = true → nonce a ≠ nonce b) :
    ∀ a b, a ≠ b → nonce a ≠ nonce b := by
  intro a b hab
  obtain ⟨j, ha, hb, hc⟩ := honest_quorum_intersection (q a) (q b) corrupt (sizes a) (sizes b) hf overlap
  exact localUnique j hc a b hab ha hb

structure QuorumTierRule where
  cap : Nat
  need : Nat
  deriving DecidableEq
structure TransactionPolicy where
  digest : Nat
  recipients : List Nat
  perTxCap : Nat
  maxWindowSpend : Nat
  tiers : List QuorumTierRule
structure TransactionIntent where
  recipient : Nat
  amount : Nat
  reportedSpend : Nat
  nonce : Nat
  session : Nat
  window : Nat
  deriving DecidableEq

/-- Projection of evaluate: first matching tier, recipient and amount. The Rust guard
additionally checks chain, suite, clock, distinct approvers, initiator and guardian. -/
def PolicyAccepts (p : TransactionPolicy) (i : TransactionIntent) (approvals : Nat) : Prop :=
  i.recipient ∈ p.recipients ∧ i.amount ≤ p.perTxCap ∧
  ∃ r, p.tiers.find? (fun r => decide (i.amount ≤ r.cap)) = some r ∧ r.need ≤ approvals

structure Ledger where
  spent : Nat
  nonces : List Nat
  sessions : List Nat
  deriving DecidableEq
def projected (s : Ledger) (i : TransactionIntent) : Nat := max s.spent i.reportedSpend + i.amount
def burn (s : Ledger) (i : TransactionIntent) : Ledger :=
  ⟨projected s i, i.nonce :: s.nonces, i.session :: s.sessions⟩
def LedgerStep (cap w : Nat) (s : Ledger) (i : TransactionIntent) (next : Ledger) : Prop :=
  i.window = w ∧ i.nonce ∉ s.nonces ∧ i.session ∉ s.sessions ∧
  projected s i ≤ cap ∧ next = burn s i

structure AuthorizedSignReleaseToken where
  policyDigest : Nat
  intentDigest : Nat
  sessionId : Nat
  nonce : Nat
  windowEpoch : Nat
  deriving DecidableEq
def minted (hashIntent : TransactionIntent → Nat) (p : TransactionPolicy) (i : TransactionIntent) : AuthorizedSignReleaseToken :=
  ⟨p.digest, hashIntent i, i.session, i.nonce, i.window⟩
def ValidRelease (hashIntent : TransactionIntent → Nat) (p : TransactionPolicy) (t w : Nat) (i : TransactionIntent)
    (s next : Ledger) (token : AuthorizedSignReleaseToken) : Prop :=
  token = minted hashIntent p i ∧ PolicyAccepts p i t ∧ LedgerStep p.maxWindowSpend w s i next

/-- A downstream digest match transports a token to the same intent, or exhibits the
canonical-intent hash collision. Nonce, session and authoritative epoch are explicit pins. -/
theorem token_binding (H : TransactionIntent → Nat) (p : TransactionPolicy)
    (i j : TransactionIntent) (h : minted H p i = minted H p j) :
    i.session = j.session ∧ i.nonce = j.nonce ∧ i.window = j.window ∧
    (i = j ∨ (i ≠ j ∧ H i = H j)) := by
  have hs := congrArg AuthorizedSignReleaseToken.sessionId h
  have hn := congrArg AuthorizedSignReleaseToken.nonce h
  have hw := congrArg AuthorizedSignReleaseToken.windowEpoch h
  refine ⟨hs, hn, hw, ?_⟩
  by_cases he : i = j
  · exact .inl he
  · exact .inr ⟨he, congrArg AuthorizedSignReleaseToken.intentDigest h⟩

/-- Exact t distinct shares; provenance excludes a threshold forgery or a token-binding
break. Hash/MAC security and durable storage integrity are the interface assumptions. -/
theorem threshold_policy_composition {n t f w : Nat} (p : TransactionPolicy) (hashIntent : TransactionIntent → Nat)
    (i : TransactionIntent) (q corrupt : Fin n → Bool)
    (before after : Fin n → Ledger) (tokens : Fin n → AuthorizedSignReleaseToken)
    (hq : cardinal q = t) (hf : cardinal corrupt ≤ f) (ht : f < t)
    (release : ∀ j, q j = true → corrupt j = false →
      ValidRelease hashIntent p t w i (before j) (after j) (tokens j)) :
    PolicyAccepts p i t ∧ ∃ j, q j = true ∧ corrupt j = false ∧ tokens j = minted hashIntent p i := by
  obtain ⟨j, hj, hc⟩ := honest_in_quorum q corrupt (Nat.le_of_eq hq.symm) hf ht
  have h := release j hj hc
  exact ⟨h.2.1, j, hj, hc, h.1⟩

inductive LedgerTrace (cap w : Nat) : Ledger → List TransactionIntent → Ledger → Prop where
  | nil (s) : LedgerTrace cap w s [] s
  | cons {s next final i is} : LedgerStep cap w s i next → LedgerTrace cap w next is final →
      LedgerTrace cap w s (i :: is) final

/-- Applies to each honest custodian's own releases, or to the authoritative shared ledger.
A common honest accountant must observe ALL intents to infer a global, rather than local, cap. -/
theorem ledger_trace_safety {cap w : Nat} {s final : Ledger} {is : List TransactionIntent}
    (tr : LedgerTrace cap w s is final) (initial : s.spent ≤ cap) :
    (is.map TransactionIntent.amount).sum + s.spent ≤ final.spent ∧ final.spent ≤ cap ∧
    is.Pairwise (fun a b => a.nonce ≠ b.nonce) ∧
    (∀ i ∈ is, i.nonce ∉ s.nonces ∧ i.session ∉ s.sessions ∧ i.window = w) := by
  induction tr with
  | nil s => exact ⟨by simp, initial, .nil, by intro i hi; cases hi⟩
  | @cons s next final i is step rest ih =>
    rcases step with ⟨hw, hn, hs, hcap, rfl⟩
    obtain ⟨sumBound, capBound, pairs, fresh⟩ := ih hcap
    refine ⟨?_, capBound, .cons ?_ pairs, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      have hm := Nat.le_max_left s.spent i.reportedSpend
      change (is.map TransactionIntent.amount).sum + projected s i ≤ final.spent at sumBound
      unfold projected at sumBound; omega
    · intro j hj he
      have h := (fresh j hj).1
      exact h (by simp only [burn]; exact List.mem_cons.mpr (.inl he.symm))
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨hn, hs, hw⟩
      · have h := fresh j hj
        exact ⟨fun hm => h.1 (List.mem_cons_of_mem _ hm),
          fun hm => h.2.1 (List.mem_cons_of_mem _ hm), h.2.2⟩

/-- K is arbitrary (the length of is). Shared durable accounting, or one honest signer in
every quorum, supplies the trace. Mere pairwise quorum intersection does not supply it. -/
theorem threshold_spending_safety {n t f w : Nat} (p : TransactionPolicy) (hashIntent : TransactionIntent → Nat)
    (is : List TransactionIntent) (corrupt : Fin n → Bool)
    (quorum : TransactionIntent → Fin n → Bool)
    (before after : TransactionIntent → Fin n → Ledger)
    (tokens : TransactionIntent → Fin n → AuthorizedSignReleaseToken) (final : Ledger)
    (hf : cardinal corrupt ≤ f) (ht : f < t)
    (sizes : ∀ i ∈ is, cardinal (quorum i) = t)
    (releases : ∀ i ∈ is, ∀ j, quorum i j = true → corrupt j = false →
      ValidRelease hashIntent p t w i (before i j) (after i j) (tokens i j))
    (accounting : LedgerTrace p.maxWindowSpend w ⟨0, [], []⟩ is final) :
    (∀ i ∈ is, PolicyAccepts p i t) ∧ is.Pairwise (fun a b => a.nonce ≠ b.nonce) ∧
    (is.map TransactionIntent.amount).sum ≤ p.maxWindowSpend := by
  obtain ⟨hs, hc, hn, _⟩ := ledger_trace_safety accounting (Nat.zero_le _)
  refine ⟨?_, hn, by simpa using Nat.le_trans hs hc⟩
  intro i hi
  exact (threshold_policy_composition p hashIntent i (quorum i) corrupt (before i) (after i)
    (tokens i) (sizes i hi) hf ht (releases i hi)).1

def advanceWindow (authenticated : Bool) (old next : Nat) : Option Ledger :=
  if authenticated && decide (old < next) then some ⟨0, [], []⟩ else none
theorem authenticated_window_required (old next : Nat) : advanceWindow false old next = none := by
  unfold advanceWindow; rfl

structure WindowAdvanceAuthorization where
  nextEpoch : Nat
  mac : Nat
def advanceAuthorized (mac : Nat → Nat → Nat → Nat) (policy old : Nat)
    (a : WindowAdvanceAuthorization) : Option Ledger :=
  advanceWindow (decide (a.mac = mac policy old a.nextEpoch)) old a.nextEpoch

/-- The MAC oracle closes over the provisioned secret key, and binds policy plus both epochs.
Only a successful authenticated strict advance can reset the accounting state. -/
theorem authorized_window_binding (mac : Nat → Nat → Nat → Nat) (policy old : Nat)
    (a : WindowAdvanceAuthorization) (s : Ledger) (h : advanceAuthorized mac policy old a = some s) :
    a.mac = mac policy old a.nextEpoch ∧ old < a.nextEpoch ∧ s = ⟨0, [], []⟩ := by
  unfold advanceAuthorized advanceWindow at h
  split at h
  · rename_i hc
    have hc' : a.mac = mac policy old a.nextEpoch ∧ old < a.nextEpoch := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hc
    exact ⟨hc'.1, hc'.2, (Option.some.inj h).symm⟩
  · cases h

def exampleIntent (nonce window : Nat) : TransactionIntent := ⟨7, 60, 0, nonce, nonce, window⟩
theorem unauthenticated_window_reset_attack :
    ∃ a b : TransactionIntent, advanceWindow false 0 1 = none ∧
    LedgerStep 100 0 ⟨0, [], []⟩ a (burn ⟨0, [], []⟩ a) ∧
    LedgerStep 100 1 ⟨0, [], []⟩ b (burn ⟨0, [], []⟩ b) ∧ 100 < a.amount + b.amount := by
  refine ⟨exampleIntent 1 0, exampleIntent 2 1, ?_⟩
  unfold advanceWindow LedgerStep burn projected exampleIntent; decide

/-- Three 2-of-3 quorums, f=0: every pair intersects honestly, every local ledger totals
100, but global spend is 150. An intersection is not a common serialized ledger. -/
def rotatingQuorum (round party : Fin 3) : Bool := decide (round ≠ party)
theorem pairwise_intersection_not_global_accounting :
    (∀ r : Fin 3, cardinal (rotatingQuorum r) = 2) ∧
    (∀ a b : Fin 3, ∃ j : Fin 3, rotatingQuorum a j = true ∧ rotatingQuorum b j = true) ∧
    (∀ j : Fin 3, qsum 3 (fun r => if rotatingQuorum r j then 50 else 0) ≤ 100) ∧
    100 < qsum 3 (fun _ => 50) := by
  unfold cardinal rotatingQuorum; simp only [qsum_succ, qsum_zero]; decide

-- PRESETS

inductive FipsSet where
  | shake128s | shake128f | shake192s | shake192f | shake256s | shake256f
  deriving DecidableEq
def fipsParams : FipsSet → Fips205Params
  | .shake128s => slhDsaShake128s | .shake128f => slhDsaShake128f
  | .shake192s => slhDsaShake192s | .shake192f => slhDsaShake192f
  | .shake256s => slhDsaShake256s | .shake256f => slhDsaShake256f
def fipsCategory : FipsSet → Nat
  | .shake128s | .shake128f => 1
  | .shake192s | .shake192f => 3
  | .shake256s | .shake256f => 5
def fipsWireBytes : FipsSet → Nat
  | .shake128s => 7856 | .shake128f => 17088 | .shake192s => 16224
  | .shake192f => 35664 | .shake256s => 29792 | .shake256f => 49856

/-- Table 2 classifications and exact Rust sig_bytes formula. Width/Grover exponents
are generic preimage ceilings, not a concrete multi-target SLH-DSA advantage estimate. -/
theorem all_fips_profiles (f : FipsSet) :
    let p := fipsParams f
    p.wellFormed = true ∧ p.h = p.d * p.hp ∧ 0 < p.hp ∧ p.hp ≤ 16 ∧
    0 < p.a ∧ p.a ≤ 20 ∧ p.k * 2 ^ p.a ≤ 2 ^ 32 ∧
    (p.n = 16 ∨ p.n = 24 ∨ p.n = 32) ∧
    8 * p.n = 32 * (fipsCategory f + 3) ∧ 4 * p.n = 16 * (fipsCategory f + 3) ∧
    p.ell = p.ell1 + p.ell2 ∧ (p.ell = 35 ∨ p.ell = 51 ∨ p.ell = 67) ∧
    p.sigBytes = p.n * (1 + p.k * (1 + p.a) + p.d * (p.ell + p.hp)) ∧
    p.sigBytes = fipsWireBytes f ∧ p.sigBytes < 2 ^ 32 ∧
    p.m = p.mdBytes + p.treeBytes + p.leafBytes ∧
    p.k * p.a ≤ 8 * p.mdBytes ∧ 8 * p.mdBytes < p.k * p.a + 8 ∧
    p.h - p.hp ≤ 96 ∧ p.h - p.hp ≤ 8 * p.treeBytes ∧
    8 * p.treeBytes < p.h - p.hp + 8 ∧
    p.hp ≤ 8 * p.leafBytes ∧ 8 * p.leafBytes < p.hp + 8 := by
  cases f <;>
    simp only [fipsParams, fipsCategory, fipsWireBytes, slhDsaShake128s, slhDsaShake128f,
      slhDsaShake192s_eq, slhDsaShake192f_eq, slhDsaShake256s_eq, slhDsaShake256f_eq,
      Fips205Params.wellFormed_eq, Fips205Params.ell_eq, Fips205Params.ell1_eq,
      Fips205Params.ell2_eq, Fips205Params.sigBytes_eq, Fips205Params.mdBytes_eq,
      Fips205Params.treeBytes_eq, Fips205Params.leafBytes_eq] <;>
    decide

/-- Deployed 32-byte-node `FrontierFtsProfile` presets (`crates/qsag-fts/src/frontier.rs:39-53`;
    the retired 16-byte FTS profiles have been removed). -/
inductive FrontierProfile where
  | compact1122 | full256Bit
  deriving DecidableEq, Repr
structure FrontierParams where
  nodeBytes : Nat
  height : Nat
  w : Nat
  len : Nat
  target : Nat
  indexBits : Nat
  counterBits : Nat
  maxSafeUses : Nat
@[expose] def frontierParams : FrontierProfile → FrontierParams
  | .compact1122 => ⟨32, 8, 96, 34, 1615, 256, 16, 1⟩
  | .full256Bit => ⟨32, 8, 5, 72, 144, 256, 16, 1⟩
def frontierWireBytes : FrontierProfile → Nat
  | .compact1122 => 1122 | .full256Bit => 2338
def useBudget : FrontierProfile → Nat
  | .compact1122 | .full256Bit => 1

theorem all_frontier_profiles (f : FrontierProfile) :
    let p := frontierParams f
    (p.len + 1) * p.nodeBytes + (p.counterBits + 7) / 8 = frontierWireBytes f ∧
    p.maxSafeUses = useBudget f ∧ p.maxSafeUses = 1 ∧ p.counterBits = 16 ∧
    p.len ≤ 2 ^ p.height ∧ p.target ≤ p.len * (p.w - 1) ∧ p.indexBits ≤ 384 ∧
    p.nodeBytes = 32 ∧ p.indexBits = 256 ∧ 8 * p.nodeBytes = 256 ∧ 4 * p.nodeBytes = 128 := by
  cases f <;> dsimp [frontierParams, frontierWireBytes, useBudget] <;> decide

/-- N(t,l) row: coefficient of x^l in P_0=x, P_(t+1)=x+P_t^2.
For l≥2 the root split has exactly the same coefficient; the root singleton is excluded. -/
@[expose] def frontierRow (L : Nat) : Nat → List Nat
  | 0 => 0 :: 1 :: List.replicate (L - 1) 0
  | h + 1 =>
    let prev := frontierRow L h
    (List.range (L + 1)).map fun l => if l = 1 then 1 else
      ((List.range (l + 1)).map fun j => prev.getD j 0 * prev.getD (l - j) 0).sum

/-- D(k,s) row of (1+x+...+x^(w-1))^k, using a sliding convolution window. -/
@[expose] def windowScan : List Nat → List Nat → Nat → List Nat
  | [], _, _ => []
  | x :: xs, ys, acc =>
    let next := acc + x - ys.headD 0
    next :: windowScan xs ys.tail next
@[expose] def decorationRow (w S : Nat) : Nat → List Nat
  | 0 => 1 :: List.replicate S 0
  | k + 1 => let prev := decorationRow w S k
    windowScan prev (List.replicate w 0 ++ prev) 0
@[expose] def codeSize (p : FrontierParams) : Nat :=
  (frontierRow p.len p.height).getD p.len 0 * (decorationRow p.w p.target p.len).getD p.target 0

/-- The mathematical bounded convolution, including the zero boundary. -/
def windowSum (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, u => f u + if u = 0 then 0 else windowSum f w (u - 1)
private theorem window_shift (f : Nat → Nat) : ∀ w u,
    windowSum f w (u + 1) + (if w ≤ u + 1 then f (u + 1 - w) else 0) =
      f (u + 1) + windowSum f w u
  | 0, _ => by simp [windowSum]
  | 1, 0 => by simp [windowSum]
  | m + 2, 0 => by
    have hn : ¬ m + 2 ≤ 1 := by omega
    simp [windowSum, hn]
  | m + 1, v + 1 => by
    have ih := window_shift f m v
    have hc : (m + 1 ≤ v + 2) ↔ (m ≤ v + 1) := by constructor <;> intro h <;> omega
    have hs : v + 2 - (m + 1) = v + 1 - m := by omega
    unfold windowSum
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hm : m ≤ v + 1
    · simp only [hm, hc.mpr hm, ↓reduceIte, hs] at ih ⊢; omega
    · have hn : ¬ m + 1 ≤ v + 2 := fun h => hm (hc.mp h)
      simp only [hm, hn, ↓reduceIte] at ih ⊢; omega

private theorem scan_spec (f : Nat → Nat) (w : Nat) (xs : List Nat) :
    ∀ (start acc : Nat) (ys : List Nat),
      (∀ i < xs.length, xs.getD i 0 = f (start + i)) →
      (∀ i < xs.length, ys.getD i 0 = if w ≤ start + i then f (start + i - w) else 0) →
      acc = (if start = 0 then 0 else windowSum f w (start - 1)) →
      windowScan xs ys acc = List.ofFn (fun i : Fin xs.length => windowSum f w (start + i.val)) := by
  induction xs with
  | nil => intros; rfl
  | cons x xs ih =>
    intro start acc ys hx hy ha
    have hx0 : x = f start := by simpa using hx 0 (by simp)
    have hy0 : ys.headD 0 = (if w ≤ start then f (start - w) else 0) := by
      have h := hy 0 (by simp); cases ys <;> simpa using h
    have he : acc + x - ys.headD 0 = windowSum f w start := by
      rw [hx0, hy0, ha]
      cases start with
      | zero => cases w <;> simp [windowSum]
      | succ u =>
        have h := window_shift f w u
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        omega
    simp only [windowScan, he, List.ofFn_succ, Fin.val_zero, Nat.add_zero]
    congr 1
    suffices h : windowScan xs ys.tail (windowSum f w start) =
        List.ofFn (fun i : Fin xs.length => windowSum f w (start + 1 + i.val)) by
      simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using h
    apply ih (start + 1) (windowSum f w start) ys.tail
    · intro i hi
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hx (i + 1) (by simpa using Nat.succ_lt_succ hi)
    · intro i hi
      have h := hy (i + 1) (by simpa using Nat.succ_lt_succ hi)
      cases ys <;> simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
    · simp

private theorem delayed_get (xs : List Nat) : ∀ w i,
    (List.replicate w 0 ++ xs).getD i 0 = if w ≤ i then xs.getD (i - w) 0 else 0
  | 0, _ => by simp
  | w + 1, 0 => by simp [List.replicate_succ]
  | w + 1, i + 1 => by
    simpa only [List.replicate_succ, List.cons_append, List.getD_cons_succ,
      Nat.add_le_add_iff_right, Nat.add_sub_add_right] using delayed_get xs w i

/-- Each computed next-row coefficient is the exact Rust sum over offsets 0..min(w-1,u).
This proves the sliding evaluator used by the large kernel checks has no underflow shortcut. -/
theorem decoration_row_recurrence (w S k : Nat) :
    let prev := decorationRow w S k
    decorationRow w S (k + 1) =
      List.ofFn (fun i : Fin prev.length => windowSum (fun u => prev.getD u 0) w i.val) := by
  change windowScan (decorationRow w S k) (List.replicate w 0 ++ decorationRow w S k) 0 = _
  have h := scan_spec (fun u => (decorationRow w S k).getD u 0) w (decorationRow w S k)
    0 0 (List.replicate w 0 ++ decorationRow w S k)
    (by intro i _; simp only [Nat.zero_add])
    (by intro i _; simpa only [Nat.zero_add] using delayed_get (decorationRow w S k) w i)
    rfl
  simpa only [Nat.zero_add] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem wide_code_domains :
    2 ^ 256 < codeSize (frontierParams .compact1122) ∧
    2 ^ 256 < codeSize (frontierParams .full256Bit) := by
  decide

def FrontierParams.isFullWidth256 (p : FrontierParams) : Prop :=
  p.nodeBytes = 32 ∧ p.indexBits = 256 ∧ p.maxSafeUses = 1 ∧ 2 ^ 256 < codeSize p ∧
    4 * p.nodeBytes = 128

theorem security_regime_separation (f : FrontierProfile) :
    (f = .compact1122 ∨ f = .full256Bit) ∧ (frontierParams f).isFullWidth256 := by
  cases f
  · exact ⟨.inl rfl, rfl, rfl, rfl, wide_code_domains.1, rfl⟩
  · exact ⟨.inr rfl, rfl, rfl, rfl, wide_code_domains.2, rfl⟩

/-- Tooth: a narrow 16-byte / 128-bit index parameter set is excluded by `FrontierParams.isFullWidth256`. -/
theorem tooth_narrow_16byte_frontier_excluded :
    ¬ (FrontierParams.mk 16 14 5 31 62 128 16 1).isFullWidth256 := by
  rintro ⟨hNode, _⟩
  cases hNode

/-- Equal sums plus coordinate domination force equality, constructively. -/
theorem equal_sum_dominated {n : Nat} (a b : Fin n → Nat)
    (hs : qsum n a = qsum n b) (dom : ∀ i, a i ≤ b i) : a = b := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    have tail := qsum_le_qsum (fun i : Fin n => dom i.succ)
    have h0 := dom 0
    rw [qsum_succ, qsum_succ] at hs
    change a 0 + qsum n (fun i => a i.succ) = b 0 + qsum n (fun i => b i.succ) at hs
    have he : a 0 = b 0 := by omega
    have ht : qsum n (fun i => a i.succ) = qsum n (fun i => b i.succ) := by omega
    have het := ih (fun i => a i.succ) (fun i => b i.succ) ht (fun i => dom i.succ)
    funext i; refine Fin.cases he (fun j => congrFun het j) i

/-- Either orientation has a strict coordinate: a single revealed chain vector cannot
advance to a distinct vector of the same sum. This alone is not a full FTS reduction. -/
theorem one_use_incomparable {n : Nat} (a b : Fin n → Nat)
    (hs : qsum n a = qsum n b) (hne : a ≠ b) : ∃ i, a i < b i := by
  by_cases h : ∃ i, a i < b i
  · exact h
  · have dom : ∀ i, b i ≤ a i := by
      intro i; have hn : ¬ a i < b i := fun hi => h ⟨i, hi⟩; omega
    exact False.elim (hne (equal_sum_dominated b a hs.symm dom).symm)

def smallVector (a b : Nat) : Fin 2 → Nat := fun i => if i.val = 0 then a else b
theorem two_uses_cover_third : ∃ a b c : Fin 2 → Nat,
    qsum 2 a = 2 ∧ qsum 2 b = 2 ∧ qsum 2 c = 2 ∧ a ≠ c ∧ b ≠ c ∧
    (∀ i, min (a i) (b i) ≤ c i) := by
  refine ⟨smallVector 0 2, smallVector 2 0, smallVector 1 1,
    by simp only [qsum_succ, qsum_zero]; decide, by simp only [qsum_succ, qsum_zero]; decide,
    by simp only [qsum_succ, qsum_zero]; decide, ?_, ?_, ?_⟩
  · intro he; have h := congrFun he 0; contradiction
  · intro he; have h := congrFun he 0; contradiction
  · intro i; unfold smallVector; split <;> decide

theorem hybrid_inhabited : ∃ (H : Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes) (v : Nat)
    (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
    validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs := by
  refine ⟨fun _ => 0, (fun pk _ sig => decide (sig = pk)), (fun pk _ sig => decide (sig = pk)),
    ⟨.secpMl44, [1], [2]⟩, [113], 1, ⟨⟨.secpMl44, [1], [2]⟩, [1], [2]⟩, [7], [[8]], ?_⟩
  unfold validateForAddress addressOf verifyWith; decide

def examplePolicy : TransactionPolicy := ⟨9, [7], 100, 100, [⟨100, 2⟩]⟩
theorem threshold_inhabited : ∃ (n t f w : Nat) (p : TransactionPolicy)
    (H : TransactionIntent → Nat) (i : TransactionIntent) (q corrupt : Fin n → Bool)
    (before after : Fin n → Ledger) (tokens : Fin n → AuthorizedSignReleaseToken),
    cardinal q = t ∧ cardinal corrupt ≤ f ∧ f < t ∧
    (∀ j, q j = true → corrupt j = false → ValidRelease H p t w i (before j) (after j) (tokens j)) := by
  refine ⟨2, 2, 0, 0, examplePolicy, fun i => i.nonce, exampleIntent 1 0,
    fun _ => true, fun _ => false, fun _ => ⟨0, [], []⟩,
    fun _ => burn ⟨0, [], []⟩ (exampleIntent 1 0),
    fun _ => minted (fun i => i.nonce) examplePolicy (exampleIntent 1 0), ?_⟩
  refine ⟨by unfold cardinal; simp only [qsum_succ, qsum_zero]; decide,
    by unfold cardinal; simp only [qsum_succ, qsum_zero]; decide, by decide, ?_⟩
  intro j _ _
  unfold ValidRelease PolicyAccepts LedgerStep examplePolicy exampleIntent projected
  refine ⟨rfl, ⟨by decide, by decide, ⟨⟨100, 2⟩, rfl, by decide⟩⟩, ?_⟩
  dsimp only
  decide

theorem ledger_inhabited : ∃ cap w s final is, LedgerTrace cap w s is final ∧ s.spent ≤ cap := by
  refine ⟨100, 0, ⟨0, [], []⟩, burn ⟨0, [], []⟩ (exampleIntent 1 0), [exampleIntent 1 0], ?_,
    Nat.zero_le _⟩
  exact .cons (by unfold LedgerStep exampleIntent projected; decide) (.nil _)

theorem incomparable_inhabited : ∃ a b : Fin 2 → Nat, qsum 2 a = qsum 2 b ∧ a ≠ b := by
  refine ⟨smallVector 0 2, smallVector 2 0, by simp only [qsum_succ, qsum_zero]; decide, ?_⟩
  intro h; have h0 := congrFun h 0; contradiction

theorem spending_inhabited : ∃ (n t f w : Nat) (p : TransactionPolicy) (H : TransactionIntent → Nat)
    (is : List TransactionIntent) (corrupt : Fin n → Bool) (q : TransactionIntent → Fin n → Bool)
    (before after : TransactionIntent → Fin n → Ledger)
    (tokens : TransactionIntent → Fin n → AuthorizedSignReleaseToken) (final : Ledger),
    cardinal corrupt ≤ f ∧ f < t ∧ (∀ i ∈ is, cardinal (q i) = t) ∧
    (∀ i ∈ is, ∀ j, q i j = true → corrupt j = false →
      ValidRelease H p t w i (before i j) (after i j) (tokens i j)) ∧
    LedgerTrace p.maxWindowSpend w ⟨0, [], []⟩ is final := by
  refine ⟨2, 2, 0, 0, examplePolicy, fun i => i.nonce, [exampleIntent 1 0],
    fun _ => false, fun _ _ => true, fun _ _ => ⟨0, [], []⟩,
    fun i _ => burn ⟨0, [], []⟩ i, fun i _ => minted (fun i => i.nonce) examplePolicy i,
    burn ⟨0, [], []⟩ (exampleIntent 1 0), ?_⟩
  refine ⟨by unfold cardinal; simp only [qsum_succ, qsum_zero]; decide, by decide, ?_, ?_, ?_⟩
  · intro i _; unfold cardinal; simp only [qsum_succ, qsum_zero]; decide
  · intro i hi j _ _
    have he := List.mem_singleton.mp hi; subst i
    unfold ValidRelease PolicyAccepts LedgerStep examplePolicy exampleIntent projected
    refine ⟨rfl, ⟨by decide, by decide, ⟨⟨100, 2⟩, rfl, by decide⟩⟩, ?_⟩
    dsimp only; decide
  · exact .cons (by unfold LedgerStep examplePolicy exampleIntent projected; decide) (.nil _)

end Qsag.HybridSecurity
end

namespace Qsag.HybridSecurity

#verify_constructive frame64_prefix_injective transcript_bytes_injective identity_binding address_binding
  fresh_transcript dual_key_euf_cma rogue_partner_resistance naive_rogue_rebinding
  robust_min_bound total_component_break hybrid_advantage_bound honest_in_quorum honest_quorum_intersection
  intersecting_nonce_distinct authorized_window_binding
  token_binding threshold_policy_composition ledger_trace_safety threshold_spending_safety
  authenticated_window_required unauthenticated_window_reset_attack pairwise_intersection_not_global_accounting
  all_fips_profiles all_frontier_profiles decoration_row_recurrence wide_code_domains security_regime_separation
  equal_sum_dominated one_use_incomparable two_uses_cover_third
#verify_inhabited dual_key_euf_cma hybrid_inhabited
#verify_inhabited threshold_policy_composition threshold_inhabited
#verify_inhabited ledger_trace_safety ledger_inhabited
#verify_inhabited threshold_spending_safety spending_inhabited
#tooth_pair rogue_partner_resistance vs naive_rogue_rebinding
#tooth_pair authenticated_window_required vs unauthenticated_window_reset_attack
#tooth_pair ledger_trace_safety vs unauthenticated_window_reset_attack
#tooth_pair security_regime_separation vs tooth_narrow_16byte_frontier_excluded

end Qsag.HybridSecurity

/-! ### Exports for lane sig -/
public section

#verify_inhabited Qsag.HybridSecurity.one_use_incomparable Qsag.HybridSecurity.incomparable_inhabited
#export_eqns Qsag.HybridSecurity.suiteBytes Qsag.HybridSecurity.keyHash Qsag.HybridSecurity.idInput
  Qsag.HybridSecurity.idCommit Qsag.HybridSecurity.addressOf Qsag.HybridSecurity.transcript
  Qsag.HybridSecurity.validateForAddress Qsag.HybridSecurity.verifyWith

end

/-! ## Executed `cSHAKE256` (`keccakF1600`) envelope and policy-release instances of `Tests/CompositionInstances`

Evaluated here over 24-round `keccakF1600` NIST SP 800-185 `cSHAKE256` sponges, where
`validateForAddress`, `verifyWith`, `PolicyAccepts`, `LedgerStep` and the other definitions of
this module unfold. Negative-control combiner instances replace constant-`true` strawmen with a
single-guard-dropped message-blind `cSHAKE256` key-tag verifier (`msgBlindClassicalVerifier`) that
still authenticates `(pk, suite, pq)` while omitting transcript-message binding. -/
public section
namespace Qsag.CompositionInstances
set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 1000000
open Qsag.HybridSecurity

private def kZeroState : KState :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def kLoadLe64 (block : List UInt8) (laneIdx : Nat) : UInt64 :=
  let base := 8 * laneIdx
  (block.getD base 0).toUInt64 |||
  ((block.getD (base + 1) 0).toUInt64 <<< 8) |||
  ((block.getD (base + 2) 0).toUInt64 <<< 16) |||
  ((block.getD (base + 3) 0).toUInt64 <<< 24) |||
  ((block.getD (base + 4) 0).toUInt64 <<< 32) |||
  ((block.getD (base + 5) 0).toUInt64 <<< 40) |||
  ((block.getD (base + 6) 0).toUInt64 <<< 48) |||
  ((block.getD (base + 7) 0).toUInt64 <<< 56)

private def kXorRate136 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0  := s.a0  ^^^ kLoadLe64 block 0,  a1  := s.a1  ^^^ kLoadLe64 block 1,
    a2  := s.a2  ^^^ kLoadLe64 block 2,  a3  := s.a3  ^^^ kLoadLe64 block 3,
    a4  := s.a4  ^^^ kLoadLe64 block 4,  a5  := s.a5  ^^^ kLoadLe64 block 5,
    a6  := s.a6  ^^^ kLoadLe64 block 6,  a7  := s.a7  ^^^ kLoadLe64 block 7,
    a8  := s.a8  ^^^ kLoadLe64 block 8,  a9  := s.a9  ^^^ kLoadLe64 block 9,
    a10 := s.a10 ^^^ kLoadLe64 block 10, a11 := s.a11 ^^^ kLoadLe64 block 11,
    a12 := s.a12 ^^^ kLoadLe64 block 12, a13 := s.a13 ^^^ kLoadLe64 block 13,
    a14 := s.a14 ^^^ kLoadLe64 block 14, a15 := s.a15 ^^^ kLoadLe64 block 15,
    a16 := s.a16 ^^^ kLoadLe64 block 16 }

private def kLaneBytesLE (w : UInt64) : List UInt8 :=
  [UInt8.ofNat (w.toNat % 256),
   UInt8.ofNat ((w.toNat / 256) % 256),
   UInt8.ofNat ((w.toNat / 65536) % 256),
   UInt8.ofNat ((w.toNat / 16777216) % 256),
   UInt8.ofNat ((w.toNat / 4294967296) % 256),
   UInt8.ofNat ((w.toNat / 1099511627776) % 256),
   UInt8.ofNat ((w.toNat / 281474976710656) % 256),
   UInt8.ofNat ((w.toNat / 72057594037927936) % 256)]

private def kRateBlockBytes (s : KState) : List UInt8 :=
  kLaneBytesLE s.a0 ++ kLaneBytesLE s.a1 ++ kLaneBytesLE s.a2 ++ kLaneBytesLE s.a3 ++
  kLaneBytesLE s.a4 ++ kLaneBytesLE s.a5 ++ kLaneBytesLE s.a6 ++ kLaneBytesLE s.a7 ++
  kLaneBytesLE s.a8 ++ kLaneBytesLE s.a9 ++ kLaneBytesLE s.a10 ++ kLaneBytesLE s.a11 ++
  kLaneBytesLE s.a12 ++ kLaneBytesLE s.a13 ++ kLaneBytesLE s.a14 ++ kLaneBytesLE s.a15 ++
  kLaneBytesLE s.a16

/-- Precomputed 136-byte SP 800-185 `bytepad(encodeString("") || encodeString("QSAG.HYBRID.ENV/v1"), 136)`. -/
private def hybridEnvPrefix136 : Bytes :=
  [
   0x01, 0x88, 0x01, 0x00, 0x01, 0x90, 0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44,
   0x2E, 0x45, 0x4E, 0x56, 0x2F, 0x76, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- Precomputed 136-byte SP 800-185 `bytepad(encodeString("") || encodeString("QSAG.HYBRID.SIG/v1"), 136)`. -/
private def hybridSigPrefix136 : Bytes :=
  [
   0x01, 0x88, 0x01, 0x00, 0x01, 0x90, 0x51, 0x53, 0x41, 0x47, 0x2E, 0x48, 0x59, 0x42, 0x52, 0x49, 0x44,
   0x2E, 0x53, 0x49, 0x47, 0x2F, 0x76, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- 32-byte NIST SP 800-185 `cSHAKE256` (`keccakF1600`, domain `0x04`) digest under `"QSAG.HYBRID.ENV/v1"`. -/
def cshakeEnvDigest32 (msg : Bytes) : Bytes :=
  evalSponge 136 0x04 keccakF1600 kZeroState kXorRate136 kRateBlockBytes
    (hybridEnvPrefix136 ++ msg) 32

/-- 32-byte NIST SP 800-185 `cSHAKE256` (`keccakF1600`, domain `0x04`) tag under `"QSAG.HYBRID.SIG/v1"`. -/
def cshakeSigTag32 (msg : Bytes) : Bytes :=
  evalSponge 136 0x04 keccakF1600 kZeroState kXorRate136 kRateBlockBytes
    (hybridSigPrefix136 ++ msg) 32

def encodePre : Preimage → Bytes
  | .key pq s pk => (if pq then 2 else 1) :: (suiteBytes s ++ pk)
  | .identity s c p => 3 :: (suiteBytes s ++ (be 32 c.val ++ be 32 p.val))
  | .address hrp v s id =>
    4 :: (be 8 hrp.length ++ (hrp ++ (be 8 v ++ (suiteBytes s ++ be 32 id.val))))

/-- Real 256-bit `cSHAKE256` (`keccakF1600`) domain-separated envelope hash (`"QSAG.HYBRID.ENV/v1"`). -/
def envCshakeHash : HybridSecurity.Hash := fun x =>
  ⟨ofBE (cshakeEnvDigest32 (encodePre x)) % 256 ^ 32,
   Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

/-- V2 transcript byte framing binding `(pq, suite, id, classicalDigest, pqDigest, msg)`. -/
def transcriptFields (t : Transcript) : Bytes :=
  (if t.pq then 2 else 1) :: (suiteBytes t.suite ++ (be 32 t.id.val ++
    (be 32 t.classicalDigest.val ++ (be 32 t.pqDigest.val ++ (be 8 t.msg.length ++ t.msg)))))

/-- Key- and full-transcript-bound 32-byte `cSHAKE256` (`"QSAG.HYBRID.SIG/v1"`) signature tag. -/
def cshakeTranscriptSign (pk : Bytes) (t : Transcript) : Bytes :=
  cshakeSigTag32 (0x01 :: (frame64 pk ++ transcriptFields t))

/-- Real `cSHAKE256` key- and transcript-binding signature verifier. -/
def cshakeTranscriptVerifier : Verifier := fun pk t sig =>
  decide (sig = cshakeTranscriptSign pk t)

def envelopeFor (k : Keys) (m : Bytes) : HybridPinnedEnvelope :=
  ⟨k, cshakeTranscriptSign k.classical (transcript envCshakeHash k false m),
    cshakeTranscriptSign k.pq (transcript envCshakeHash k true m)⟩

def hk : Keys := ⟨.secpMl44, [2, 0xA1, 0xA2], [0xB1, 0xB2, 0xB3]⟩

def hrpQs : Bytes := [113, 115]

def paid : Bytes := [0x70, 0x61, 0x79]

def unpaid : Bytes := [0x70, 0x61, 0x7A]

theorem hybrid_honest_accepts :
    validateForAddress envCshakeHash (envelopeFor hk paid) (addressOf envCshakeHash hk hrpQs 1) ∧
    verifyWith envCshakeHash cshakeTranscriptVerifier cshakeTranscriptVerifier (envelopeFor hk paid) paid := by
  unfold validateForAddress verifyWith; decide +kernel

theorem hybrid_rejects_other_message :
    ¬ verifyWith envCshakeHash cshakeTranscriptVerifier cshakeTranscriptVerifier (envelopeFor hk paid) unpaid := by
  unfold verifyWith; decide +kernel

/-- The envelope carries no HRP or version, so it validates for every address derived from the
same keys. Network exclusivity has to be bound in the message, as the source module states. -/
theorem hybrid_envelope_valid_for_every_network :
    validateForAddress envCshakeHash (envelopeFor hk paid) (addressOf envCshakeHash hk [113, 116] 1) ∧
    validateForAddress envCshakeHash (envelopeFor hk paid) (addressOf envCshakeHash hk hrpQs 2) := by
  unfold validateForAddress; decide +kernel

/-- Address metadata is bound by the commitment: relabelling the HRP or the version without
recomputing the commitment is rejected. -/
theorem hybrid_rejects_relabelled_hrp :
    ¬ validateForAddress envCshakeHash (envelopeFor hk paid)
      { addressOf envCshakeHash hk hrpQs 1 with hrp := [113, 116] } := by
  unfold validateForAddress; decide +kernel

theorem hybrid_rejects_relabelled_version :
    ¬ validateForAddress envCshakeHash (envelopeFor hk paid)
      { addressOf envCshakeHash hk hrpQs 1 with version := 2 } := by
  unfold validateForAddress; decide +kernel

theorem hybrid_address_commitments_differ :
    (addressOf envCshakeHash hk [113, 116] 1).commitment ≠ (addressOf envCshakeHash hk hrpQs 1).commitment ∧
    (addressOf envCshakeHash hk hrpQs 2).commitment ≠ (addressOf envCshakeHash hk hrpQs 1).commitment := by
  decide +kernel

theorem hybrid_rejects_other_keys_address :
    ¬ validateForAddress envCshakeHash (envelopeFor hk paid)
      (addressOf envCshakeHash { hk with classical := [3, 0xA1, 0xA2] } hrpQs 1) := by
  unfold validateForAddress; decide +kernel

/-- Identical component keys and one verification algorithm: the role flag in the transcript
alone keeps a classical-role signature from being accepted in the PQ role. -/
def twin : Keys := ⟨.secpMl44, [9], [9]⟩

theorem hybrid_rejects_swapped_roles :
    verifyWith envCshakeHash cshakeTranscriptVerifier cshakeTranscriptVerifier (envelopeFor twin paid) paid ∧
    ¬ verifyWith envCshakeHash cshakeTranscriptVerifier cshakeTranscriptVerifier
      ⟨twin, (envelopeFor twin paid).pqSignature, (envelopeFor twin paid).classicalSignature⟩
      paid := by
  unfold verifyWith; decide +kernel

/-- An honest PQ signature is not accepted next to a substituted classical key. -/
theorem hybrid_rejects_rogue_partner :
    ¬ (cshakeTranscriptVerifier hk.pq (transcript envCshakeHash { hk with classical := [0xEE] } true paid)
      (envelopeFor hk paid).pqSignature = true) := by decide +kernel

theorem hybrid_keybound_instance : ∃ (H : HybridSecurity.Hash) (vc vp : Verifier) (k : Keys) (hrp : Bytes)
    (v : Nat) (e : HybridPinnedEnvelope) (m : Bytes) (qs : List Bytes),
    validateForAddress H e (addressOf H k hrp v) ∧ verifyWith H vc vp e m ∧ m ∉ qs :=
  ⟨envCshakeHash, cshakeTranscriptVerifier, cshakeTranscriptVerifier, hk, hrpQs, 1,
    envelopeFor hk paid, paid, [unpaid],
    hybrid_honest_accepts.1, hybrid_honest_accepts.2, by decide⟩

/-- Single-guard-dropped `cSHAKE256` tag binding `(pq, suite, pk)` while omitting `t.msg` / `t.id`
    binding: rejects malformed/wrong-key signatures (`[0]`), yet transfers across messages! -/
def msgBlindKeyTag (pk : Bytes) (s : Suite) (pq : Bool) : Bytes :=
  cshakeSigTag32 (0x02 :: ((if pq then 2 else 1) :: (suiteBytes s ++ frame64 pk)))

/-- Single-guard-dropped mutated verifier: checks the 32-byte `cSHAKE256` `(pq, suite, pk)` tag
    (rejecting `[0]` and wrong keys/roles) while dropping message-binding. -/
def msgBlindClassicalVerifier : Verifier := fun pk t sig =>
  decide (sig = msgBlindKeyTag pk t.suite t.pq)

/-- Output `0`: message-blind `(pq, suite, pk)` key tags reused on fresh `unpaid`.
    Output `1`: replay of honest envelope on queried `paid`. -/
def advOut (j : Fin 2) : HybridPinnedEnvelope × Bytes :=
  if j.val = 0 then
    (⟨hk, msgBlindKeyTag hk.classical hk.suite false, msgBlindKeyTag hk.pq hk.suite true⟩, unpaid)
  else
    (envelopeFor hk paid, paid)

/-- Classical component dropping message-binding (`msgBlindClassicalVerifier`, still rejecting `[0]`),
    PQ component binding the full transcript (`cshakeTranscriptVerifier`): hybrid win mass is `0`
    while the mutated classical component game is won with mass `1`. -/
theorem robust_combiner_instance :
    msgBlindClassicalVerifier hk.classical (transcript envCshakeHash hk false unpaid) [0] = false ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      hybridWins envCshakeHash msgBlindClassicalVerifier cshakeTranscriptVerifier hk hrpQs 1 [paid] (advOut j)) = 0 ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      msgBlindClassicalVerifier hk.classical (transcript envCshakeHash hk false (advOut j).2)
        (advOut j).1.classicalSignature && decide ((advOut j).2 ∉ [paid])) = 1 ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      cshakeTranscriptVerifier hk.pq (transcript envCshakeHash hk true (advOut j).2)
        (advOut j).1.pqSignature && decide ((advOut j).2 ∉ [paid])) = 0 := by
  decide +kernel

/-- When both components drop message-binding (`msgBlindClassicalVerifier`), the fresh message
    reuse wins the hybrid game with mass `1` despite `[0]` still being rejected. -/
theorem both_components_broken_instance :
    msgBlindClassicalVerifier hk.pq (transcript envCshakeHash hk true unpaid) [0] = false ∧
    mass (fun _ : Fin 2 => 1) (fun j =>
      hybridWins envCshakeHash msgBlindClassicalVerifier msgBlindClassicalVerifier hk hrpQs 1 [paid] (advOut j)) = 1 := by
  decide +kernel

def pol : TransactionPolicy := ⟨9, [7, 8], 100, 150, [⟨50, 1⟩, ⟨100, 2⟩]⟩

def intentHash (i : TransactionIntent) : Nat :=
  ((((i.recipient * 1000003 + i.amount) * 1000003 + i.reportedSpend) * 1000003 + i.nonce) *
    1000003 + i.session) * 1000003 + i.window

def payA : TransactionIntent := ⟨7, 60, 0, 1, 11, 5⟩

def payB : TransactionIntent := ⟨8, 80, 60, 2, 12, 5⟩

def genesis : Ledger := ⟨0, [], []⟩

def quorum01 (j : Fin 3) : Bool := decide (j.val < 2)

def corrupt0 (j : Fin 3) : Bool := decide (j.val = 0)

/-- The corrupt quorum member holds a token that was never minted for the intent. -/
def tokensA (j : Fin 3) : AuthorizedSignReleaseToken :=
  if j.val = 0 then ⟨0, 0, 0, 0, 0⟩ else minted intentHash pol payA

theorem only_honest_member : ∀ j : Fin 3,
    quorum01 j = true → corrupt0 j = false → j = 1 := by decide +kernel

theorem acceptsA : PolicyAccepts pol payA 2 :=
  ⟨by decide +kernel, by decide +kernel, ⟨100, 2⟩, by decide +kernel, by decide +kernel⟩

theorem acceptsB : PolicyAccepts pol payB 2 :=
  ⟨by decide +kernel, by decide +kernel, ⟨100, 2⟩, by decide +kernel, by decide +kernel⟩

theorem stepA : LedgerStep pol.maxWindowSpend 5 genesis payA (burn genesis payA) := by
  unfold LedgerStep; decide +kernel

theorem stepB : LedgerStep pol.maxWindowSpend 5 (burn genesis payA) payB
    (burn (burn genesis payA) payB) := by
  unfold LedgerStep; decide +kernel

theorem corrupt_token_not_minted : tokensA 0 ≠ minted intentHash pol payA := by decide +kernel

/-- `n = 3`, `t = 2`, `f = 1`: the quorum contains the corrupt party; the honest member alone
supplies the release. -/
theorem corrupt_quorum_instance : ∃ (n t f w : Nat) (p : TransactionPolicy)
    (H : TransactionIntent → Nat) (i : TransactionIntent) (q corrupt : Fin n → Bool)
    (before after : Fin n → Ledger) (tokens : Fin n → AuthorizedSignReleaseToken),
    cardinal q = t ∧ cardinal corrupt ≤ f ∧ f < t ∧
    (∀ j, q j = true → corrupt j = false →
      ValidRelease H p t w i (before j) (after j) (tokens j)) :=
  ⟨3, 2, 1, 5, pol, intentHash, payA, quorum01, corrupt0, fun _ => genesis,
    fun _ => burn genesis payA, tokensA, by decide +kernel, by decide +kernel, by decide,
    fun j hq hc => by
      obtain rfl := only_honest_member j hq hc
      exact ⟨rfl, acceptsA, stepA⟩⟩

def quorumOf (i : TransactionIntent) (j : Fin 3) : Bool :=
  if i = payA then decide (j.val < 2) else decide (0 < j.val)

def beforeOf (i : TransactionIntent) : Ledger := if i = payA then genesis else burn genesis payA

/-- Two intents, two different quorums sharing honest party `1`, one serialized ledger. -/
theorem two_intent_spending_instance : ∃ (n t f w : Nat) (p : TransactionPolicy)
    (H : TransactionIntent → Nat) (is : List TransactionIntent) (corrupt : Fin n → Bool)
    (q : TransactionIntent → Fin n → Bool) (before after : TransactionIntent → Fin n → Ledger)
    (tokens : TransactionIntent → Fin n → AuthorizedSignReleaseToken) (final : Ledger),
    cardinal corrupt ≤ f ∧ f < t ∧ (∀ i ∈ is, cardinal (q i) = t) ∧
    (∀ i ∈ is, ∀ j, q i j = true → corrupt j = false →
      ValidRelease H p t w i (before i j) (after i j) (tokens i j)) ∧
    LedgerTrace p.maxWindowSpend w ⟨0, [], []⟩ is final := by
  refine ⟨3, 2, 1, 5, pol, intentHash, [payA, payB], corrupt0, quorumOf,
    fun i _ => beforeOf i, fun i _ => burn (beforeOf i) i, fun i _ => minted intentHash pol i,
    burn (burn genesis payA) payB, by decide +kernel, by decide, ?_, ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · decide +kernel
    · obtain rfl := List.mem_singleton.mp hi
      decide +kernel
  · intro i hi j _ _
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨rfl, acceptsA, stepA⟩
    · obtain rfl := List.mem_singleton.mp hi
      exact ⟨rfl, acceptsB, stepB⟩
  · exact .cons stepA (.cons stepB (.nil _))

theorem rejects_over_per_tx_cap : ¬ PolicyAccepts pol ⟨7, 101, 0, 3, 13, 5⟩ 3 :=
  fun h => absurd h.2.1 (by decide +kernel)

theorem rejects_unlisted_recipient : ¬ PolicyAccepts pol ⟨9, 10, 0, 3, 13, 5⟩ 3 :=
  fun h => absurd h.1 (by decide +kernel)

theorem rejects_insufficient_approvals : ¬ PolicyAccepts pol payB 1 := by
  rintro ⟨_, _, r, hr, hn⟩
  have e : pol.tiers.find? (fun r => decide (payB.amount ≤ r.cap)) = some ⟨100, 2⟩ := by
    decide +kernel
  rw [e] at hr
  cases hr
  exact absurd hn (by decide +kernel)

theorem rejects_nonce_replay :
    ¬ LedgerStep pol.maxWindowSpend 5 (burn genesis payA) payA
      (burn (burn genesis payA) payA) :=
  fun h => absurd h.2.1 (by decide +kernel)

/-- After `payA` and `payB` (140 of 150 spent) a further 20 has no ledger step at all. -/
theorem rejects_window_overspend (next : Ledger) :
    ¬ LedgerStep pol.maxWindowSpend 5 (burn (burn genesis payA) payB)
      ⟨7, 20, 0, 3, 13, 5⟩ next :=
  fun h => absurd h.2.2.2.1 (by decide +kernel)

theorem rejects_stale_window (next : Ledger) :
    ¬ LedgerStep pol.maxWindowSpend 6 genesis payA next :=
  fun h => absurd h.1 (by decide +kernel)

theorem token_is_intent_specific :
    minted intentHash pol payA ≠ minted intentHash pol payB := by decide +kernel

def toyMac (policy old next : Nat) : Nat := (policy * 65537 + old) * 65537 + next + 0x5eed

theorem window_advance_accepts :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6⟩ = some ⟨0, [], []⟩ := by decide +kernel

/-- Wrong tag, non-increasing epoch, tag for another policy, tag for another old epoch. -/
theorem window_advance_rejects :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6 + 1⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨5, toyMac 9 5 5⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 8 5 6⟩ = none ∧
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 4 6⟩ = none := by decide +kernel

theorem window_advance_rejects_wrong_tag :
    advanceAuthorized toyMac 9 5 ⟨6, toyMac 9 5 6 + 1⟩ ≠ some ⟨0, [], []⟩ := by decide +kernel

/-- The two demonstration messages differ (used where `paid`, `unpaid` do not unfold). -/
theorem paid_ne_unpaid : paid ≠ unpaid := by decide

#verify_constructive paid_ne_unpaid hybrid_honest_accepts hybrid_rejects_other_message
  hybrid_envelope_valid_for_every_network hybrid_rejects_relabelled_hrp
  hybrid_rejects_relabelled_version hybrid_address_commitments_differ
  hybrid_rejects_other_keys_address hybrid_rejects_swapped_roles
  hybrid_rejects_rogue_partner hybrid_keybound_instance robust_combiner_instance
  both_components_broken_instance
  only_honest_member acceptsA acceptsB stepA stepB
  corrupt_token_not_minted corrupt_quorum_instance two_intent_spending_instance
  rejects_over_per_tx_cap rejects_unlisted_recipient rejects_insufficient_approvals
  rejects_nonce_replay rejects_window_overspend rejects_stale_window token_is_intent_specific
  window_advance_accepts window_advance_rejects window_advance_rejects_wrong_tag
#verify_inhabited Qsag.HybridSecurity.dual_key_euf_cma hybrid_keybound_instance
#verify_inhabited Qsag.HybridSecurity.threshold_policy_composition corrupt_quorum_instance
#verify_inhabited Qsag.HybridSecurity.threshold_spending_safety two_intent_spending_instance
#tooth_pair Qsag.HybridSecurity.dual_key_euf_cma vs hybrid_rejects_other_message
#tooth_pair Qsag.HybridSecurity.address_binding vs hybrid_rejects_relabelled_hrp
#tooth_pair Qsag.HybridSecurity.rogue_partner_resistance vs hybrid_rejects_rogue_partner
#tooth_pair Qsag.HybridSecurity.threshold_policy_composition vs rejects_insufficient_approvals
#tooth_pair Qsag.HybridSecurity.ledger_trace_safety vs rejects_nonce_replay
#tooth_pair Qsag.HybridSecurity.threshold_spending_safety vs rejects_window_overspend
#tooth_pair Qsag.HybridSecurity.authorized_window_binding vs window_advance_rejects_wrong_tag
#export_eqns encodePre transcriptFields hrpQs paid unpaid

end Qsag.CompositionInstances
end
