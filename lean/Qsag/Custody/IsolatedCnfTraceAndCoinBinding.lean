module
public import Qsag.Oracle.ByteFraming
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Custody
set_option autoImplicit false

abbrev WireDescriptor := Nat × Nat × Nat

/-- One receiver's view, in transport order. The indexed byte function lets the
    semantics emit large correction frames without materializing their contents. -/
structure WireFrame where
  sender : Nat
  round : Nat
  size : Nat
  payload : Fin size → UInt8

def wireShape (frames : List WireFrame) : List WireDescriptor :=
  frames.map fun f => (f.sender, f.round, f.size)

/-- Public routing and the barrier/open frame schedule for one observer. -/
structure CnfRouting where
  correctionSenders : List Nat
  barrier : List WireDescriptor
  finalOpen : Nat → List WireDescriptor

/-- One observer's receive order. `correction` selects the peers whose designated
    slot the observer holds. `missing` counts each peer's slots absent locally. -/
def CnfRouting.forObserver (peers : List Nat) (correction : Nat → Bool)
    (missing : Nat → Nat) (digestBytes : Nat) : CnfRouting :=
  let senders := peers.filter correction
  let all := fun (tag size : Nat) => peers.map (fun p => (p,tag,size))
  let fieldProduct := senders.map (fun p => (p,0x04000000,16))
  let openShares := fun (tag size : Nat) => peers.map (fun p => (p,tag,size * missing p))
  ⟨senders,all 0x04010000 32 ++ all 0x04020000 32 ++ all 0x04030000 64 ++
      fieldProduct ++ fieldProduct ++ all 0x04010000 32 ++ openShares 0x04040000 16,
    fun width => openShares 0x04050000 (width * digestBytes)⟩

abbrev Chain := Fin 16 × BitVec 256

/-- The first component is the WOTS digit. A completed slot keeps its last value. -/
def advanceChain (hash : Nat → BitVec 256 → BitVec 256) (step : Nat) (c : Chain) : Chain :=
  (c.1, if step < c.1.val then hash step c.2 else c.2)

def emit (data : Nat → Nat → Nat → UInt8) (ds : List WireDescriptor) : List WireFrame :=
  ds.map fun (s,r,n) => ⟨s,r,n,fun i => data s r i.val⟩

private theorem append_eq {α : Type} {a b c d : List α} (h : a = b) (g : c = d) : a ++ c = b ++ d := by rw [h,g]

private theorem shape_emit (data : Nat → Nat → Nat → UInt8) (ds : List WireDescriptor) :
    wireShape (emit data ds) = ds := by simp [wireShape, emit, List.map_map, Function.comp_def]

/-- Each Keccak permutation performs 24 multiplications. Each correction carries
    25 bit words and 128 randomizer planes of 25 words per sponge. -/
def permutationTraffic (route : CnfRouting) (width pending : Nat) :
    List WireDescriptor × Nat :=
  let flush := 24 * 64 * 25 ≤ pending
  let round := route.correctionSenders.map fun s => (s, 0x04000000, 8 * 129 * 25 * width)
  ((if flush then route.barrier else []) ++ (List.replicate 24 round).flatten,
    (if flush then 0 else pending) + 24 * 25 * width)

structure ChunkResult where
  frames : List WireFrame
  chains : List Chain
  pending : Nat

/-- Execute the selected slots for each round and retain pending multiplication
    words across chunk boundaries, exactly where the Rust evaluator may flush. -/
def sweep (prune : Bool) (route : CnfRouting) (hash : Nat → BitVec 256 → BitVec 256)
    (bytes : List Chain → Nat → Nat → Nat → UInt8) :
    List Nat → Nat → List Chain → ChunkResult
  | [], pending, cs => ⟨[], cs, pending⟩
  | step :: rest, pending, cs =>
    let batch := if prune then cs.filter (fun c => step < c.1.val) else cs
    let (traffic, next) := if batch.isEmpty then ([], pending)
      else permutationTraffic route batch.length pending
    let later := sweep prune route hash bytes rest next (cs.map (advanceChain hash step))
    {later with frames := emit (bytes batch) traffic ++ later.frames}

private theorem sweep_independent (route : CnfRouting) (hash : Nat → BitVec 256 → BitVec 256)
    (bytes : List Chain → Nat → Nat → Nat → UInt8) (steps : List Nat) :
    ∀ pending (a b : List Chain), a.length = b.length →
    let x := sweep false route hash bytes steps pending a
    let y := sweep false route hash bytes steps pending b
    wireShape x.frames = wireShape y.frames ∧ x.pending = y.pending ∧ x.chains.length = y.chains.length := by
  induction steps with
  | nil => intro _ a b h; exact ⟨rfl,rfl,h⟩
  | cons i rest ih =>
    intro pending a b h
    have emptyEq : a.isEmpty = b.isEmpty := by
      cases a <;> cases b <;> first | rfl | exact nomatch h
    simp only [sweep, Bool.false_eq_true, ↓reduceIte, emptyEq, h]
    split
    all_goals
      have hm : (a.map (advanceChain hash i)).length = (b.map (advanceChain hash i)).length := by
        simpa only [List.length_map] using h
      refine ⟨?_,(ih _ _ _ hm).2⟩
      simp only [wireShape,List.map_append]
      exact append_eq ((shape_emit _ _).trans (shape_emit _ _).symm) (ih _ _ _ hm).1

/-- Process a public partition of the WOTS chains. Initial values and WOTS
    digits may depend on the key. The final opening covers all completed chunks. -/
def isolatedCnfChunks {Key : Type} (prune : Bool) (route : CnfRouting)
    (init : Key → Nat → (w : Nat) → Fin w → Chain) (hash : Nat → BitVec 256 → BitVec 256)
    (bytes : List Chain → Nat → Nat → Nat → UInt8) (sk : Key) :
    List Nat → Nat → Nat → List Chain → List WireFrame × List Chain
  | [], _, pending, cs => (emit (bytes cs)
      ((if pending = 0 then [] else route.barrier) ++ route.finalOpen cs.length),cs)
  | width :: rest, chunk, pending, cs =>
    let input := List.ofFn (init sk chunk width)
    let (traffic, next) := permutationTraffic route width pending
    let part := sweep prune route hash bytes (List.range 15) next input
    let (later,output) := isolatedCnfChunks prune route init hash bytes sk rest
      (chunk+1) part.pending (cs ++ part.chains)
    (emit (bytes input) traffic ++ part.frames ++ later,output)

theorem isolatedCnf_fixedWidth_wireShape_keyIndependent {Key : Type}
    (route : CnfRouting) (widths : List Nat) (init : Key → Nat → (w : Nat) → Fin w → Chain)
    (hash : Nat → BitVec 256 → BitVec 256) (bytes : List Chain → Nat → Nat → Nat → UInt8)
    (sk₁ sk₂ : Key) : ∀ chunk pending (a b : List Chain), a.length = b.length →
    wireShape (isolatedCnfChunks false route init hash bytes sk₁ widths chunk pending a).1 =
    wireShape (isolatedCnfChunks false route init hash bytes sk₂ widths chunk pending b).1 := by
  induction widths with
  | nil => intro _ _ a b h; simp [isolatedCnfChunks,shape_emit,h]
  | cons width rest ih =>
    intro chunk pending a b hab
    obtain ⟨hf,hp,hl⟩ := sweep_independent route hash bytes (List.range 15)
      (permutationTraffic route width pending).2
      (List.ofFn (init sk₁ chunk width)) (List.ofFn (init sk₂ chunk width)) (by simp)
    simp only [isolatedCnfChunks,wireShape,List.map_append]
    apply append_eq
    · exact append_eq ((shape_emit _ _).trans (shape_emit _ _).symm) hf
    · rw [hp]
      apply ih
      simp only [List.length_append,hab,hl]

theorem tooth_prunedChain_wireShape_leaks_key :
    ∃ (sk₁ sk₂ : Bool),
    let run := fun sk => isolatedCnfChunks true ⟨[0], [], fun _ => []⟩
      (fun (k : Bool) _ _ _ => ((if k then 1 else 0), 0#256))
      (fun _ v => v) (fun _ _ _ _ => 0) sk [1] 0 0 []
    (wireShape (run sk₁).1).length = 24 ∧ (wireShape (run sk₂).1).length = 48 := by
  exact ⟨false,true,by decide +kernel⟩

#tooth_pair isolatedCnf_fixedWidth_wireShape_keyIndependent vs tooth_prunedChain_wireShape_leaks_key

abbrev CoinBytes := List UInt8
structure CoinContext where
  relationDigest : CoinBytes
  schedule : CoinBytes
  statement : CoinBytes
  deriving DecidableEq

inductive CoinPurpose where | mask | blinder | salt
  deriving DecidableEq

def CoinPurpose.tag : CoinPurpose → UInt8
  | .mask => 0 | .blinder => 1 | .salt => 2

/-- Direct XOF query addressing. The counter identifies a block within a stream. -/
def deriveProverCoins (seed : CoinBytes) (ctx : CoinContext) (witness : CoinBytes)
    (purpose : CoinPurpose) (block : Nat) : CoinBytes :=
  encodeMultiFrame ["QSAG.ZKHEM2.COINS/v1".toUTF8.toList, seed, ctx.relationDigest,
    ctx.schedule, ctx.statement, witness, [purpose.tag], leb128 block]

theorem proverCoins_schedule_non_reuse (seed witness : CoinBytes) {a b : CoinContext}
    (hne : a ≠ b) (p q : CoinPurpose) (i j : Nat) :
    deriveProverCoins seed a witness p i ≠ deriveProverCoins seed b witness q j := by
  intro h
  have e := encodeMultiFrame_injective h
  cases a; cases b
  simp only [List.cons.injEq, true_and] at e
  exact hne (by cases e.1; cases e.2.1; cases e.2.2.1; rfl)

theorem tooth_unbound_schedule_repeats_masks (seed witness relation stmt : CoinBytes) :
    ∃ s t : CoinBytes, let omitted := fun (c : CoinContext) =>
      deriveProverCoins seed { c with schedule := [] } witness
    (⟨relation,s,stmt⟩ : CoinContext) ≠ ⟨relation,t,stmt⟩ ∧
      ∀ p i, omitted ⟨relation,s,stmt⟩ p i = omitted ⟨relation,t,stmt⟩ p i := by
  exact ⟨[0],[1],by intro e; have h := congrArg CoinContext.schedule e; exact (by decide : ([0] : CoinBytes) ≠ [1]) h, fun _ _ => rfl⟩

#tooth_pair proverCoins_schedule_non_reuse vs tooth_unbound_schedule_repeats_masks

abbrev DigestBytes := { b : CoinBytes // b.length = 32 }

/-- The V2 stream puts the profile and layout in the seed query. Statement and
    witness use separate digest domains. Every downstream block uses the same
    stream domain and the fixed-width little-endian counter. -/
structure V2CoinRegime where
  profile : UInt8
  relation : DigestBytes
  layout : CoinBytes
  statement : CoinBytes
  deriving DecidableEq

def v2SeedQuery (seed : DigestBytes) (regime : V2CoinRegime)
    (hashStatement : CoinBytes → DigestBytes) (witnessDigest : DigestBytes) : CoinBytes :=
  seed.val ++ (regime.profile :: (regime.relation.val ++
    ((regime.layout ++ (hashStatement regime.statement).val) ++ witnessDigest.val)))

/-- Equality of stream addresses across regimes exhibits a collision in one of
    the two concrete compression domains. The counter is shared across purposes. -/
theorem v2Stream_reuse_implies_collision (seed wit : DigestBytes)
    (hs hk : CoinBytes → DigestBytes) {a b : V2CoinRegime} (ne : a ≠ b) (i j : UInt64)
    (same : (hk (v2SeedQuery seed a hs wit),i) = (hk (v2SeedQuery seed b hs wit),j)) :
    (a.statement ≠ b.statement ∧ hs a.statement = hs b.statement) ∨
    (v2SeedQuery seed a hs wit ≠ v2SeedQuery seed b hs wit ∧
      hk (v2SeedQuery seed a hs wit) = hk (v2SeedQuery seed b hs wit)) := by
  by_cases he : v2SeedQuery seed a hs wit = v2SeedQuery seed b hs wit
  · have pref := (List.append_inj he (rfl : seed.val.length = seed.val.length)).2
    obtain ⟨hp,tail⟩ := List.cons.inj pref
    obtain ⟨hr,trailer⟩ := List.append_inj tail (a.relation.property.trans b.relation.property.symm)
    have middle := List.append_cancel_right trailer
    have lens := congrArg List.length middle
    simp only [List.length_append,(hs a.statement).property,(hs b.statement).property] at lens
    obtain ⟨hl,hd⟩ := List.append_inj middle (by omega)
    refine Or.inl ⟨?_,Subtype.ext hd⟩
    intro eqs
    apply ne
    cases a; cases b
    cases hp; cases Subtype.ext hr; cases hl; cases eqs; rfl
  · exact Or.inr ⟨he,congrArg Prod.fst same⟩

end Qsag.Custody
