module

public import Qsag.Exec.PosixCrashWal.CeremonyJournal
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ### Append-Only MAC-Chained Burn Journal (`qsag-fts/src/wal.rs`) -/

/-- The journal file after chunking into `RECORD_LEN = 42`-byte records: each full chunk is a
    10-byte body `(party_be16 ‖ epoch_be64)` and a 32-byte tag; `tornTail` is whatever follows the
    last full chunk (`len % 42` bytes). -/
structure BurnJournalFile where
  records  : List (List UInt8 × List UInt8)
  tornTail : List UInt8
  deriving Repr, DecidableEq

/-- `record_tag` chained through `last_tag`: each tag authenticates its body AND the previous
    tag. Returns the bodies and the final tag, or `none` at the first tag that does not chain. -/
def verifyBurnChain (tagFn : List UInt8 → List UInt8 → List UInt8) :
    List UInt8 → List (List UInt8 × List UInt8) → Option (List (List UInt8) × List UInt8)
  | prev, [] => some ([], prev)
  | prev, (body, tag) :: rest =>
    if tag = tagFn prev body then
      match verifyBurnChain tagFn tag rest with
      | some (bodies, last) => some (body :: bodies, last)
      | none => none
    else none

/-- `DurableBurnJournal::load` (recovery path): the length must be a whole number of records,
    every tag must chain from the genesis tag, and no entry may repeat. Fails closed otherwise;
    there is no truncate-and-continue path. -/
def openBurnJournal (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8)
    (f : BurnJournalFile) : Option (List (List UInt8) × List UInt8) :=
  if f.tornTail = [] then
    match verifyBurnChain tagFn genesisTag f.records with
    | some (bodies, last) => if bodies.Nodup then some (bodies, last) else none
    | none => none
  else none

/-- `reserve`: one appended, synced record tagged against the current `last_tag`. -/
def appendBurnRecord (tagFn : List UInt8 → List UInt8 → List UInt8) (last body : List UInt8)
    (f : BurnJournalFile) : BurnJournalFile :=
  { f with records := f.records ++ [(body, tagFn last body)] }

theorem verifyBurnChain_append (tagFn : List UInt8 → List UInt8 → List UInt8) :
    ∀ (rs : List (List UInt8 × List UInt8)) (prev : List UInt8)
      (bodies : List (List UInt8)) (last body tag : List UInt8),
      verifyBurnChain tagFn prev rs = some (bodies, last) →
      verifyBurnChain tagFn prev (rs ++ [(body, tag)]) =
        if tag = tagFn last body then some (bodies ++ [body], tag) else none
  | [], prev, bodies, last, body, tag, h => by
    simp only [verifyBurnChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.nil_append, verifyBurnChain]
  | (b0, t0) :: rs, prev, bodies, last, body, tag, h => by
    simp only [verifyBurnChain] at h
    split at h
    · rename_i hTag
      cases hRest : verifyBurnChain tagFn t0 rs with
      | none => rw [hRest] at h; cases h
      | some bl =>
        obtain ⟨bs, l⟩ := bl
        rw [hRest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        subst hTag
        have ih := verifyBurnChain_append tagFn rs _ bs l body tag hRest
        simp only [List.cons_append, verifyBurnChain, ↓reduceIte, ih]
        by_cases hT : tag = tagFn l body <;> simp [hT]
    · cases h

/-- **Authenticated history is append-only**: whatever verifies after more records were written
    still starts with exactly the bodies that verified before. A reservation that was durable
    and verified is in every later successful recovery of the extended file. -/
theorem verifyBurnChain_prefix (tagFn : List UInt8 → List UInt8 → List UInt8) :
    ∀ (rs rs' : List (List UInt8 × List UInt8)) (prev : List UInt8)
      (bodies' : List (List UInt8)) (last' : List UInt8),
      verifyBurnChain tagFn prev (rs ++ rs') = some (bodies', last') →
      ∃ bodies last tail, verifyBurnChain tagFn prev rs = some (bodies, last) ∧
        verifyBurnChain tagFn last rs' = some (tail, last') ∧ bodies' = bodies ++ tail
  | [], rs', prev, bodies', last', h => ⟨[], prev, bodies', rfl, h, rfl⟩
  | (b0, t0) :: rs, rs', prev, bodies', last', h => by
    simp only [List.cons_append, verifyBurnChain] at h
    split at h
    · rename_i hTag
      cases hRest : verifyBurnChain tagFn t0 (rs ++ rs') with
      | none => rw [hRest] at h; cases h
      | some bl =>
        obtain ⟨bs, l⟩ := bl
        rw [hRest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨bodies, last, tail, h1, h2, h3⟩ :=
          verifyBurnChain_prefix tagFn rs rs' t0 bs l hRest
        subst hTag
        refine ⟨b0 :: bodies, last, tail, ?_, h2, by rw [h3]; rfl⟩
        simp only [verifyBurnChain, ↓reduceIte, h1]
    · cases h

/-- A crash inside `reserve` leaves the appended region in one of three shapes; recovery of each:
    nothing reached the medium (old journal), the whole record did (old entries plus the new
    one), or a partial/garbled record did. A short tail always FAILS CLOSED; a full-length
    garbled record fails closed unless its tag chains (`tag = tagFn last body'`), which for a
    body other than the reserved one is a forgery of the chain MAC. -/
theorem burnJournal_append_crash_outcomes (tagFn : List UInt8 → List UInt8 → List UInt8)
    (genesisTag : List UInt8) (f : BurnJournalFile) (bodies : List (List UInt8))
    (last body : List UInt8)
    (hOpen : openBurnJournal tagFn genesisTag f = some (bodies, last))
    (hFresh : body ∉ bodies) :
    openBurnJournal tagFn genesisTag (appendBurnRecord tagFn last body f) =
      some (bodies ++ [body], tagFn last body) ∧
    (∀ tail : List UInt8, tail ≠ [] →
      openBurnJournal tagFn genesisTag { f with tornTail := tail } = none) ∧
    (∀ body' tag' : List UInt8, tag' ≠ tagFn last body' →
      openBurnJournal tagFn genesisTag { f with records := f.records ++ [(body', tag')] } =
        none) := by
  unfold openBurnJournal at hOpen
  split at hOpen
  · rename_i hTail
    cases hV : verifyBurnChain tagFn genesisTag f.records with
    | none => rw [hV] at hOpen; cases hOpen
    | some bl =>
      obtain ⟨bs, l⟩ := bl
      rw [hV] at hOpen
      dsimp only at hOpen
      split at hOpen
      · rename_i hNd
        simp only [Option.some.injEq, Prod.mk.injEq] at hOpen
        obtain ⟨rfl, rfl⟩ := hOpen
        refine ⟨?_, ?_, ?_⟩
        · have hApp := verifyBurnChain_append tagFn f.records genesisTag bs l body
            (tagFn l body) hV
          simp only [↓reduceIte] at hApp
          have hNd' : (bs ++ [body]).Nodup := nodup_snoc hNd (fun y hy hEq => hFresh (hEq ▸ hy))
          simp only [openBurnJournal, appendBurnRecord, hTail, ↓reduceIte, hApp, hNd']
        · intro tail hNe
          simp only [openBurnJournal, hNe, ↓reduceIte]
        · intro body' tag' hBad
          have hApp := verifyBurnChain_append tagFn f.records genesisTag bs l body' tag' hV
          simp only [hBad, ↓reduceIte] at hApp
          simp only [openBurnJournal, hTail, ↓reduceIte, hApp]
      · cases hOpen
  · cases hOpen

/-- **`#tooth` (`tooth_burnJournal_truncation_is_undetectable_without_anchor`)**: dropping the
    last authenticated record leaves a journal that still opens, with one burn fewer. The chain
    authenticates prefixes; only an external count (or the last tag) pins the newest record. -/
theorem tooth_burnJournal_truncation_is_undetectable_without_anchor
    (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8)
    (f : BurnJournalFile) (bodies : List (List UInt8)) (last body : List UInt8)
    (hOpen : openBurnJournal tagFn genesisTag f = some (bodies, last))
    (hFresh : body ∉ bodies) :
    ∃ g : BurnJournalFile,
      openBurnJournal tagFn genesisTag g = some (bodies ++ [body], tagFn last body) ∧
      openBurnJournal tagFn genesisTag { g with records := g.records.dropLast } =
        some (bodies, last) := by
  refine ⟨appendBurnRecord tagFn last body f,
    (burnJournal_append_crash_outcomes tagFn genesisTag f bodies last body hOpen hFresh).1, ?_⟩
  have hEq : ({ appendBurnRecord tagFn last body f with
      records := (appendBurnRecord tagFn last body f).records.dropLast } : BurnJournalFile) = f := by
    cases f with
    | mk rs t => simp [appendBurnRecord]
  rw [hEq]
  exact hOpen

/-- Recovery pinned by an external burn count. -/
def openBurnJournalAnchored (tagFn : List UInt8 → List UInt8 → List UInt8)
    (genesisTag : List UInt8) (anchoredCount : Nat) (f : BurnJournalFile) :
    Option (List (List UInt8) × List UInt8) :=
  match openBurnJournal tagFn genesisTag f with
  | some (bodies, last) => if anchoredCount ≤ bodies.length then some (bodies, last) else none
  | none => none

/-- With the external count the truncated journal is refused. -/
theorem burnJournal_anchor_rejects_truncation
    (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8)
    (f : BurnJournalFile) (bodies : List (List UInt8)) (last : List UInt8) (anchoredCount : Nat)
    (hOpen : openBurnJournal tagFn genesisTag f = some (bodies, last))
    (hShort : bodies.length < anchoredCount) :
    openBurnJournalAnchored tagFn genesisTag anchoredCount f = none := by
  have hNot : ¬ anchoredCount ≤ bodies.length := by omega
  simp only [openBurnJournalAnchored, hOpen, hNot, ↓reduceIte]

/-- Whatever verifies returns exactly the record bodies, in file order. -/
theorem verifyBurnChain_bodies (tagFn : List UInt8 → List UInt8 → List UInt8) :
    ∀ (rs : List (List UInt8 × List UInt8)) (prev : List UInt8)
      (bodies : List (List UInt8)) (last : List UInt8),
      verifyBurnChain tagFn prev rs = some (bodies, last) → bodies = rs.map (·.1)
  | [], _, bodies, last, h => by
    simp only [verifyBurnChain, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | (b0, t0) :: rs, prev, bodies, last, h => by
    simp only [verifyBurnChain] at h
    split at h
    · cases hRest : verifyBurnChain tagFn t0 rs with
      | none => rw [hRest] at h; cases h
      | some bl =>
        obtain ⟨bs, l⟩ := bl
        rw [hRest] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, verifyBurnChain_bodies tagFn rs t0 bs l hRest]
        rfl
    · cases h

theorem openBurnJournal_some {tagFn : List UInt8 → List UInt8 → List UInt8}
    {genesisTag : List UInt8} {f : BurnJournalFile} {bodies : List (List UInt8)}
    {last : List UInt8} (h : openBurnJournal tagFn genesisTag f = some (bodies, last)) :
    f.tornTail = [] ∧ verifyBurnChain tagFn genesisTag f.records = some (bodies, last) ∧
      bodies.Nodup := by
  unfold openBurnJournal at h
  split at h
  · rename_i hTail
    cases hV : verifyBurnChain tagFn genesisTag f.records with
    | none => rw [hV] at h; cases h
    | some bl =>
      obtain ⟨bs, l⟩ := bl
      rw [hV] at h
      dsimp only at h
      split at h
      · rename_i hNd
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hTail, rfl, hNd⟩
      · cases h
  · cases h

/-- The cryptographic bad event of a recovery, stated on the accepted bytes themselves: at some
    position of the honest chain, behind an unchanged prefix, the recovered file carries a
    DIFFERENT body whose tag verifies against the honest previous tag. The honest writer tagged
    exactly one body under that previous tag, so this is a valid chain tag on a message it never
    tagged (or a collision between two honest chain tags). It is a property of one concrete
    accepted file, not a statement that such tags do not exist. -/
def BurnChainSubstitution (tagFn : List UInt8 → List UInt8 → List UInt8) :
    List UInt8 → List (List UInt8 × List UInt8) → List (List UInt8 × List UInt8) → Prop
  | prev, (b0, t0) :: rs, (b, t) :: gs =>
    (b ≠ b0 ∧ t = tagFn prev b) ∨ (b = b0 ∧ BurnChainSubstitution tagFn t0 rs gs)
  | _, _, _ => False

/-- **Recovery after arbitrary damage, no MAC assumption**: let `rs` be the honest chain and
    `gs` ANY record list that verifies and is not shorter. Then `gs` extends `rs` record for
    record, or `gs` exhibits a `BurnChainSubstitution`. -/
theorem burnChain_recovery_extends_or_substitution
    (tagFn : List UInt8 → List UInt8 → List UInt8) :
    ∀ (rs gs : List (List UInt8 × List UInt8)) (prev : List UInt8)
      (bodies bodies' : List (List UInt8)) (last last' : List UInt8),
      verifyBurnChain tagFn prev rs = some (bodies, last) →
      verifyBurnChain tagFn prev gs = some (bodies', last') →
      rs.length ≤ gs.length →
      (∃ ext, gs = rs ++ ext) ∨ BurnChainSubstitution tagFn prev rs gs
  | [], gs, _, _, _, _, _, _, _, _ => Or.inl ⟨gs, rfl⟩
  | (_, _) :: _, [], _, _, _, _, _, _, _, hLen => absurd hLen (Nat.not_succ_le_zero _)
  | (b0, t0) :: rs, (b, t) :: gs, prev, bodies, bodies', last, last', hR, hG, hLen => by
    simp only [verifyBurnChain] at hR hG
    split at hR
    · rename_i hT0
      split at hG
      · rename_i hT
        cases hRr : verifyBurnChain tagFn t0 rs with
        | none => rw [hRr] at hR; cases hR
        | some bl =>
          cases hGr : verifyBurnChain tagFn t gs with
          | none => rw [hGr] at hG; cases hG
          | some bl' =>
            by_cases hb : b = b0
            · have htt : t = t0 := by rw [hT, hT0, hb]
              rw [htt] at hGr
              rcases burnChain_recovery_extends_or_substitution tagFn rs gs t0
                  bl.1 bl'.1 bl.2 bl'.2 hRr hGr (Nat.le_of_succ_le_succ hLen) with ⟨ext, hExt⟩ | hSub
              · exact Or.inl ⟨ext, by rw [hb, htt, hExt]; rfl⟩
              · refine Or.inr ?_
                simp only [BurnChainSubstitution]
                exact Or.inr ⟨hb, hSub⟩
            · refine Or.inr ?_
              simp only [BurnChainSubstitution]
              exact Or.inl ⟨hb, hT⟩
      · cases hG
    · cases hR

/-- `wal.rs` host across crashes, at record granularity. `file` is what the medium holds,
    `handle` the entries and last tag of a live locked descriptor, `burned` the bodies whose
    `reserve` returned `Ok` (the leaves a signature may have been released for), and
    `macBroken` a ghost latch set by the one step that needs a `BurnChainSubstitution`. -/
structure BurnHost where
  file      : BurnJournalFile
  handle    : Option (List (List UInt8) × List UInt8) := none
  burned    : List (List UInt8) := []
  macBroken : Bool := false

/-- A crash may only strike the medium while an append is in flight (a synced idle inode is
    immune, `syncedInode_immune_to_crashStep`). The three crash constructors cover EVERY file
    `g` that is not shorter than the old one (`burnAppendCrash_outcome_complete`): the old
    records survive as a prefix, the file no longer opens, or the chain MAC was broken. Damage
    to old records sharing the append sector is included; losing file length is not (that is
    rollback, refused only by an external count, see the truncation `#tooth`). The same three
    constructors cover a `reserve` that returned `Err` without any crash: the handle is dead
    (`failed`), and the medium later holds nothing, a short tail, or the record. -/
inductive BurnHostStep (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8) :
    BurnHost → BurnHost → Prop where
  | openExisting (s : BurnHost) (bodies : List (List UInt8)) (last : List UInt8)
      (closed : s.handle = none)
      (opened : openBurnJournal tagFn genesisTag s.file = some (bodies, last)) :
      BurnHostStep tagFn genesisTag s { s with handle := some (bodies, last) }
  | reserve (s : BurnHost) (bodies : List (List UInt8)) (last body : List UInt8)
      (live : s.handle = some (bodies, last)) (fresh : body ∉ bodies) :
      BurnHostStep tagFn genesisTag s
        { s with
            file := appendBurnRecord tagFn last body s.file
            handle := some (bodies ++ [body], tagFn last body)
            burned := s.burned ++ [body] }
  | idleCrash (s : BurnHost) :
      BurnHostStep tagFn genesisTag s { s with handle := none }
  | appendCrashKeepsPrefix (s : BurnHost) (bodies : List (List UInt8)) (last : List UInt8)
      (g : BurnJournalFile) (ext : List (List UInt8 × List UInt8))
      (live : s.handle = some (bodies, last))
      (shape : g.records = s.file.records ++ ext) :
      BurnHostStep tagFn genesisTag s { s with file := g, handle := none }
  | appendCrashUnrecoverable (s : BurnHost) (bodies : List (List UInt8)) (last : List UInt8)
      (g : BurnJournalFile)
      (live : s.handle = some (bodies, last))
      (closed : openBurnJournal tagFn genesisTag g = none) :
      BurnHostStep tagFn genesisTag s { s with file := g, handle := none }
  | appendCrashSubstituted (s : BurnHost) (bodies : List (List UInt8)) (last : List UInt8)
      (g : BurnJournalFile)
      (live : s.handle = some (bodies, last))
      (bad : BurnChainSubstitution tagFn genesisTag s.file.records g.records) :
      BurnHostStep tagFn genesisTag s { s with file := g, handle := none, macBroken := true }

/-- Unless the chain MAC was broken: no leaf is burned twice, every burned leaf is in every
    journal state that still opens, and a live handle agrees with the medium. -/
def BurnHostInv (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8)
    (s : BurnHost) : Prop :=
  s.macBroken = true ∨
  (s.burned.Nodup ∧
   (∀ bodies last, openBurnJournal tagFn genesisTag s.file = some (bodies, last) →
      ∀ b ∈ s.burned, b ∈ bodies) ∧
   (∀ bodies last, s.handle = some (bodies, last) →
      openBurnJournal tagFn genesisTag s.file = some (bodies, last)))

theorem burnHostStep_preserves {tagFn : List UInt8 → List UInt8 → List UInt8}
    {genesisTag : List UInt8} {s t : BurnHost}
    (step : BurnHostStep tagFn genesisTag s t) (inv : BurnHostInv tagFn genesisTag s) :
    BurnHostInv tagFn genesisTag t := by
  rcases inv with hBroken | ⟨hNd, hSub, hLive⟩
  · cases step <;> exact Or.inl (by first | exact hBroken | rfl)
  · cases step with
    | openExisting bodies last closed opened =>
      refine Or.inr ⟨hNd, hSub, ?_⟩
      intro bs l h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact opened
    | reserve bodies last body live fresh =>
      have hOpen := hLive bodies last live
      have hNew := (burnJournal_append_crash_outcomes tagFn genesisTag s.file bodies last body
        hOpen fresh).1
      have hFresh : ∀ y ∈ s.burned, y ≠ body := fun y hy hEq =>
        fresh (hEq ▸ hSub bodies last hOpen y hy)
      refine Or.inr ⟨nodup_snoc hNd hFresh, ?_, ?_⟩
      · intro bs l h b hb
        have hEq : (bodies ++ [body], tagFn last body) = (bs, l) :=
          Option.some.inj (hNew.symm.trans h)
        obtain ⟨rfl, _⟩ := Prod.mk.inj hEq
        rcases List.mem_append.mp hb with hOld | hSing
        · exact List.mem_append_left _ (hSub bodies last hOpen b hOld)
        · exact List.mem_append_right _ hSing
      · intro bs l h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact hNew
    | idleCrash =>
      exact Or.inr ⟨hNd, hSub, fun _ _ h => by cases h⟩
    | appendCrashKeepsPrefix bodies last g ext live shape =>
      have hOld := (openBurnJournal_some (hLive bodies last live)).2.1
      refine Or.inr ⟨hNd, ?_, fun _ _ h => by cases h⟩
      intro bs l h b hb
      have hV := (openBurnJournal_some h).2.1
      rw [shape] at hV
      obtain ⟨bodies0, last0, tail, h0, _, hEq⟩ :=
        verifyBurnChain_prefix tagFn s.file.records ext genesisTag bs l hV
      obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (hOld.symm.trans h0))
      rw [hEq]
      exact List.mem_append_left _ (hSub bodies last (hLive bodies last live) b hb)
    | appendCrashUnrecoverable bodies last g live closed =>
      refine Or.inr ⟨hNd, ?_, fun _ _ h => by cases h⟩
      intro bs l h
      rw [closed] at h
      cases h
    | appendCrashSubstituted bodies last g live bad =>
      exact Or.inl rfl

inductive BurnHostRun (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8) :
    BurnHost → BurnHost → Prop where
  | refl (s : BurnHost) : BurnHostRun tagFn genesisTag s s
  | next {s t u : BurnHost} : BurnHostRun tagFn genesisTag s t →
      BurnHostStep tagFn genesisTag t u → BurnHostRun tagFn genesisTag s u

/-- **Append-journal multi-crash leaf non-reuse (`wal.rs`)**: over every interleaving of opens,
    successful reservations, idle crashes, and crashes during an append that leave ANY file not
    shorter than before, either a `BurnChainSubstitution` was accepted, or no leaf was burned
    twice and every later successful recovery still contains every burned leaf. No statement
    about the MAC is assumed; refusal to open is always allowed. -/
theorem burnHost_multi_crash_no_double_burn
    (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8) {s : BurnHost}
    (run : BurnHostRun tagFn genesisTag { file := ⟨[], []⟩ } s) :
    s.macBroken = true ∨
    (s.burned.Nodup ∧
     ∀ bodies last, openBurnJournal tagFn genesisTag s.file = some (bodies, last) →
       ∀ b ∈ s.burned, b ∈ bodies) := by
  have hInv : BurnHostInv tagFn genesisTag s := by
    induction run with
    | refl =>
      exact Or.inr ⟨List.nodup_nil, fun _ _ _ b hb => (by cases hb), fun _ _ h => by cases h⟩
    | next _ step ih => exact burnHostStep_preserves step ih
  rcases hInv with h | ⟨h1, h2, _⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

/-- **Completeness of the crash alphabet**: with a live handle, EVERY file `g` holding at least
    as many records as before is reached by one of the three append-crash constructors. -/
theorem burnAppendCrash_outcome_complete
    (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag : List UInt8)
    (old g : BurnJournalFile) (bodies : List (List UInt8)) (last : List UInt8)
    (hOpen : openBurnJournal tagFn genesisTag old = some (bodies, last))
    (noShrink : old.records.length ≤ g.records.length) :
    openBurnJournal tagFn genesisTag g = none ∨
    (∃ ext, g.records = old.records ++ ext) ∨
    BurnChainSubstitution tagFn genesisTag old.records g.records := by
  cases hG : openBurnJournal tagFn genesisTag g with
  | none => exact Or.inl rfl
  | some bl =>
    exact Or.inr (burnChain_recovery_extends_or_substitution tagFn old.records g.records
      genesisTag bodies bl.1 last bl.2 (openBurnJournal_some hOpen).2.1
      (openBurnJournal_some (f := g) (bodies := bl.1) (last := bl.2) hG).2.1 noShrink)

/-- Non-vacuity: a journal is opened, burns a leaf, crashes mid-append of a second leaf with a
    torn tail that keeps the old records, and the burned leaf is on the medium. -/
theorem witness_burnHost_burn_then_torn_append
    (tagFn : List UInt8 → List UInt8 → List UInt8) (genesisTag body tail : List UInt8) :
    ∃ s, BurnHostRun tagFn genesisTag { file := ⟨[], []⟩ } s ∧
      s.burned = [body] ∧ s.macBroken = false ∧ s.handle = none ∧
      s.file = ⟨[(body, tagFn genesisTag body)], tail⟩ := by
  refine ⟨{ file := ⟨[(body, tagFn genesisTag body)], tail⟩, burned := [body] }, ?_, rfl, rfl, rfl, rfl⟩
  have h1 : BurnHostStep tagFn genesisTag { file := ⟨[], []⟩ }
      { file := ⟨[], []⟩, handle := some ([], genesisTag) } :=
    BurnHostStep.openExisting _ [] genesisTag rfl (by simp [openBurnJournal, verifyBurnChain])
  have h2 := BurnHostStep.reserve (tagFn := tagFn) (genesisTag := genesisTag)
    { file := ⟨[], []⟩, handle := some ([], genesisTag) } [] genesisTag body rfl (by simp)
  have h3 := BurnHostStep.appendCrashKeepsPrefix (tagFn := tagFn) (genesisTag := genesisTag)
    { file := ⟨[(body, tagFn genesisTag body)], []⟩, handle := some ([body], tagFn genesisTag body),
      burned := [body] }
    [body] (tagFn genesisTag body) ⟨[(body, tagFn genesisTag body)], tail⟩ [] rfl (by simp)
  exact BurnHostRun.next (BurnHostRun.next (BurnHostRun.next (BurnHostRun.refl _) h1) h2) h3

#verify_inhabited burnHost_multi_crash_no_double_burn witness_burnHost_burn_then_torn_append
#tooth_pair burnHost_multi_crash_no_double_burn vs tooth_burnJournal_truncation_is_undetectable_without_anchor

#export_eqns BurnHostInv

/-! ## 8. Rust storage layouts and explicit implementation boundaries

The backend encodings below include `LockedRecord.lock_identity_seal`: device and inode
in little endian followed by the creation nonce. Identity verification compares all 24 bytes
against authenticated custody and poisons the handle on mismatch.
-/
namespace RustDurability

abbrev Bytes := List UInt8

def u64le (n : Nat) : Bytes := (encodeU64BeNat n).reverse

def u32le (n : Nat) : Bytes := (pcwEncodeU32Be n).reverse

def framed64 (frames : List Bytes) : Bytes :=
  u64le frames.length ++ (frames.flatMap fun b => u64le b.length ++ b)

/-- Actual cSHAKE256 keyed primitive, not the small-state test authenticator. -/
def keyedMac (domain key input : Bytes) : Bytes := cshake256Bytes domain (key ++ input)

theorem keyedMac_width (domain : Bytes) : WellFormedMacFn (keyedMac domain) := by
  intro key input
  exact cshake256Bytes_length _ _

/-- `LockedRecord` sidecar: lockSeal is random eight bytes; identity is unauthenticated metadata. -/
def sidecarBytes (lockSeal : Bytes) (device inode : Nat) : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x4c, 0x43, 0x4b, 0x31] ++ lockSeal ++ u64le device ++ u64le inode

def recordBytes (lockSeal payload : Bytes) : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x52, 0x45, 0x43, 0x31] ++ lockSeal ++ payload

theorem sidecarBytes_length (lockSeal : Bytes) (device inode : Nat) (h : lockSeal.length = 8) :
    (sidecarBytes lockSeal device inode).length = 32 := by
  simp [sidecarBytes, u64le, encodeU64BeNat_length, h]

/-- `LockedRecord::lock_identity_seal`, in exactly its Rust field order. -/
def lockIdentitySeal (device inode : Nat) (nonce : Bytes) : Bytes :=
  u64le device ++ u64le inode ++ nonce

theorem lockIdentitySeal_length (device inode : Nat) (nonce : Bytes) (h : nonce.length = 8) :
    (lockIdentitySeal device inode nonce).length = 24 := by
  simp [lockIdentitySeal, u64le, encodeU64BeNat_length, h]

structure LockedIdentityHandle where
  device : Nat
  inode : Nat
  nonce : Bytes
  poisoned : Bool := false

def verifyLockIdentity (s : LockedIdentityHandle) (authenticated : Bytes) :
    LockedIdentityHandle × Bool :=
  if s.poisoned || !(lockIdentitySeal s.device s.inode s.nonce == authenticated) then
    ({ s with poisoned := true }, false)
  else (s, true)

theorem verifyLockIdentity_accepts_exact {s : LockedIdentityHandle} {expected : Bytes}
    (h : (verifyLockIdentity s expected).2 = true) :
    lockIdentitySeal s.device s.inode s.nonce = expected := by
  unfold verifyLockIdentity at h
  split at h
  · cases h
  · rename_i good
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at good
    have hb : (lockIdentitySeal s.device s.inode s.nonce == expected) = true := by
      cases he : (lockIdentitySeal s.device s.inode s.nonce == expected) <;> simp_all
    exact eq_of_beq hb

/-- Evidence for the deployed `LockedRecord` opening order. Each syscall consumes the state
    produced by the previous one; the identity check is on the inode returned by `fstat`, not
    on a pathname looked up before `flock`. -/
structure LockedRecordOpenEvidence where
  initial : PosixFsState
  openedState : PosixFsState
  lockedState : PosixFsState
  pid : Pid
  path : DirName
  fd : FdId
  description : OpenDescriptionId
  device : Nat
  inode : InodeId
  nonce : Bytes
  authenticated : Bytes
  opened : posixOpenExistingNoFollow initial pid path true = .ok (openedState, fd)
  locked : posixFlockExNb openedState pid fd = .ok lockedState
  stated : posixFstatDescAndInode lockedState pid fd = .ok (description, inode)
  sealed : lockIdentitySeal device inode nonce = authenticated

def LockedRecordOpenEvidence.handle (e : LockedRecordOpenEvidence) : LockedIdentityHandle :=
  ⟨e.device, e.inode, e.nonce, false⟩

private theorem bytes_beq_self : ∀ xs : Bytes, (xs == xs) = true
  | [] => rfl
  | x :: xs => by
    have hx : (x == x) = true := by
      cases x with | ofBitVec bv => cases bv with | ofFin f => exact Nat.beq_refl f.val
    show (List.beq (x :: xs) (x :: xs)) = true
    simp only [List.beq, hx, Bool.true_and]
    exact bytes_beq_self xs

theorem lockedRecord_open_identity_seal (e : LockedRecordOpenEvidence) :
    verifyLockIdentity e.handle e.authenticated = (e.handle, true) := by
  unfold verifyLockIdentity LockedRecordOpenEvidence.handle
  rw [e.sealed, bytes_beq_self]
  rfl

theorem lockedRecord_open_uses_locked_fd (e : LockedRecordOpenEvidence) :
    posixFstatDescAndInode e.lockedState e.pid e.fd = .ok (e.description, e.inode) ∧
      posixFlockExNb e.openedState e.pid e.fd = .ok e.lockedState ∧
      posixOpenExistingNoFollow e.initial e.pid e.path true = .ok (e.openedState, e.fd) :=
  ⟨e.stated, e.locked, e.opened⟩

structure CeremonyContext where
  policyId : BitVec 256 := 0
  spendAmount : UInt64 := 0
  mpcNonceEpoch : UInt64 := 0
  deriving Repr, DecidableEq

def ceremonyContextBytes (c : CeremonyContext) : Bytes :=
  List.ofFn (fun i : Fin 32 => UInt8.ofNat (c.policyId.toNat / 256 ^ (31 - i.val))) ++
    encodeU64BeNat c.spendAmount.toNat ++ encodeU64BeNat c.mpcNonceEpoch.toNat

structure Reservation where
  ceremonyId : Bytes
  keyId : Bytes
  epochOrCodeword : Bytes
  seedBurnCursor : Nat
  hedgeGeneration : Nat
  deriving Repr, DecidableEq

def Reservation.WellFormed (r : Reservation) : Prop :=
  r.ceremonyId.length = 32 ∧ r.keyId.length = 32 ∧ r.epochOrCodeword.length = 32 ∧
  r.seedBurnCursor < 2^64 ∧ r.hedgeGeneration < 2^64

/-- Common 80-byte reservation prefix. V3 appends one flag byte and an eight-byte epoch;
key identity remains in the header. -/
def reservationBytes (r : Reservation) : Bytes :=
  r.ceremonyId ++ r.epochOrCodeword ++ encodeU64BeNat r.seedBurnCursor ++
    encodeU64BeNat r.hedgeGeneration

theorem reservationBytes_length {r : Reservation} (h : r.WellFormed) :
    (reservationBytes r).length = 80 := by
  simp [reservationBytes, encodeU64BeNat_length, h.1, h.2.2.1]

/-- Private v3 journal metadata accompanies the public reservation. Retries reuse the
binding but require a fresh ceremony ID and strictly advancing seed/hedge cursors. -/
structure JournalEntry where
  reservation : Reservation
  boundEpoch : Option Nat := none
  isRetry : Bool := false
  context : CeremonyContext := {}
  deriving Repr, DecidableEq

def freshEntry (r : Reservation) : JournalEntry := ⟨r, none, false, {}⟩

def journalEntryBytes (e : JournalEntry) : Bytes :=
  reservationBytes e.reservation ++
    [UInt8.ofNat ((if e.boundEpoch.isSome then 1 else 0) + (if e.isRetry then 2 else 0))] ++
    encodeU64BeNat (e.boundEpoch.getD 0) ++ ceremonyContextBytes e.context

theorem journalEntryBytes_length {e : JournalEntry} (h : e.reservation.WellFormed) :
    (journalEntryBytes e).length = 137 := by
  simp [journalEntryBytes, reservationBytes_length h, ceremonyContextBytes, encodeU64BeNat_length]

def ceremonyBodyV3 (keyId : Bytes) (entries : List JournalEntry) : Bytes :=
  [81,83,65,71,67,82,74,51] ++ keyId ++ encodeU64BeNat (entries.length + 1) ++
    entries.flatMap journalEntryBytes

/-- The fresh-unbound subprotocol uses v3 records with flags=0 and encoded epoch=0. -/
def ceremonyBody (keyId : Bytes) (entries : List Reservation) : Bytes :=
  ceremonyBodyV3 keyId (entries.map freshEntry)

def ceremonyTag (key lockSeal body : Bytes) : Bytes :=
  keyedMac [0x51, 0x53, 0x41, 0x47, 0x2e, 0x43, 0x45, 0x52, 0x45, 0x4d, 0x4f, 0x4e, 0x59, 0x2e, 0x4a, 0x4f, 0x55, 0x52, 0x4e, 0x41, 0x4c, 0x2e, 0x4d, 0x41, 0x43, 0x2f, 0x76, 0x33] key (lockSeal ++ body)

def ceremonyBytes (key lockSeal keyId : Bytes) (entries : List Reservation) : Bytes :=
  let body := ceremonyBody keyId entries
  body ++ ceremonyTag key lockSeal body

/-- `validate` before appending, including both uniqueness checks and strict last-entry cursors. -/
def reservationValid (keyId : Bytes) (entries : List Reservation) (r : Reservation) : Bool :=
  r.keyId == keyId &&
  !(entries.any fun e => e.ceremonyId == r.ceremonyId || e.epochOrCodeword == r.epochOrCodeword) &&
  (match entries.getLast? with
   | none => true
   | some e => decide (e.seedBurnCursor < r.seedBurnCursor ∧ e.hedgeGeneration < r.hedgeGeneration))

def FreshReservation (entries : List Reservation) (r : Reservation) : Prop :=
  ∀ e ∈ entries, e.ceremonyId ≠ r.ceremonyId ∧ e.epochOrCodeword ≠ r.epochOrCodeword

theorem reservationValid_fresh {key : Bytes} {entries : List Reservation} {r : Reservation}
    (h : reservationValid key entries r = true) :
    ∀ e ∈ entries, e.ceremonyId ≠ r.ceremonyId ∧ e.epochOrCodeword ≠ r.epochOrCodeword := by
  simp only [reservationValid, Bool.and_eq_true, Bool.not_eq_true'] at h
  have ha := h.1.2
  intro e he
  have hf : (e.ceremonyId == r.ceremonyId || e.epochOrCodeword == r.epochOrCodeword) = false :=
    by simpa using (List.any_eq_false.mp ha) e he
  simpa only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] using hf

theorem reservationValid_empty_self (r : Reservation) : reservationValid r.keyId [] r = true := by
  unfold reservationValid
  change ((r.keyId == r.keyId) && !false && true) = true
  rw [(beq_iff_eq (a := r.keyId) (b := r.keyId)).mpr rfl]
  rfl

theorem reservation_fixture_wellFormed :
    (⟨List.replicate 32 1, List.replicate 32 4, List.replicate 32 2, 1, 1⟩ : Reservation).WellFormed := by
  unfold Reservation.WellFormed
  decide

/-- Current Belt MAC binds key, eight-byte seal, generation, and serialized state using
core's LEB128 multi-frame codec (different from FTS's u64le framing). -/
def beltTag (key lockSeal : Bytes) (generation : Nat) (payload : Bytes) : Bytes :=
  cshake256Bytes [81,83,65,71,46,66,69,76,84,46,76,65,84,67,72,46,87,65,76,46,77,65,67,47,118,50]
    (encodeMultiFrame [key, lockSeal, encodeU64BeNat generation, payload])

def ledgerTag (domain key genesisSeal ledgerId purpose body : Bytes) : Bytes :=
  cshake256Bytes [0x51, 0x53, 0x41, 0x47, 0x2e, 0x4c, 0x45, 0x44, 0x47, 0x45, 0x52, 0x2e, 0x4d, 0x41, 0x43, 0x2f, 0x76, 0x32]
    (u64le domain.length ++ domain ++ key ++ genesisSeal ++ ledgerId ++ purpose ++ body)

def ledgerGenesisBody (ledgerId sealA sealB : Bytes) : Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x4c, 0x44, 0x47, 0x32] ++ ledgerId ++ sealA ++ sealB

def ledgerSnapshotBody (generation : Nat) (records : List (Bytes × Bytes)) : Bytes :=
  u64le generation ++ u64le records.length ++ records.flatMap
    (fun (k, v) => u32le k.length ++ u32le v.length ++ k ++ v)

structure Snapshot where
  generation : Nat
  records : List (Bytes × Bytes)
  tag : Bytes
  deriving Repr, DecidableEq

/-- Decoded slot candidate. Unavailable sidecars and any failed codec/MAC check are `none`.
The filter includes the tag at equal generation, absent from the older `TwoSlotWal` abstraction. -/
def usableSnapshot (anchor : ExternalMonotoneAnchor) (parity : Nat)
    (candidate : Option Snapshot) : Option Snapshot :=
  match candidate with
  | none => none
  | some c => if c.generation % 2 = parity ∧
      verifyAgainstExternalAnchor anchor c.generation c.tag = true then some c else none

/-- Rust visits A then B and changes `best` only for a strictly greater generation. -/
def selectSnapshots (a b : Option Snapshot) : Option Snapshot :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => if a.generation < b.generation then some b else some a

def recoverLedger (genesisValid : Bool) (anchor : ExternalMonotoneAnchor)
    (a b : Option Snapshot) : Option Snapshot :=
  if genesisValid then selectSnapshots (usableSnapshot anchor 0 a) (usableSnapshot anchor 1 b)
  else none

theorem usableSnapshot_anchor {anchor : ExternalMonotoneAnchor} {parity : Nat}
    {input : Option Snapshot} {out : Snapshot} (h : usableSnapshot anchor parity input = some out) :
    verifyAgainstExternalAnchor anchor out.generation out.tag = true := by
  cases input with
  | none => simp [usableSnapshot] at h
  | some c =>
    simp only [usableSnapshot] at h
    split at h
    · next hc => cases Option.some.inj h; exact hc.2
    · simp at h

theorem selectSnapshots_member {a b : Option Snapshot} {out : Snapshot}
    (h : selectSnapshots a b = some out) : a = some out ∨ b = some out := by
  cases a <;> cases b <;> simp_all [selectSnapshots]
  split at h <;> simp_all

theorem recoverLedger_anchor {g : Bool} {anchor : ExternalMonotoneAnchor}
    {a b : Option Snapshot} {out : Snapshot} (h : recoverLedger g anchor a b = some out) :
    verifyAgainstExternalAnchor anchor out.generation out.tag = true := by
  unfold recoverLedger at h
  split at h
  · rcases selectSnapshots_member h with ha | hb
    · exact usableSnapshot_anchor ha
    · exact usableSnapshot_anchor hb
  · simp at h

theorem recoverLedger_rejects_stale {g : Bool} {anchor : ExternalMonotoneAnchor}
    {a b : Option Snapshot} {out : Snapshot} (h : recoverLedger g anchor a b = some out) :
    anchor.attestedEpoch ≤ out.generation :=
  externalAnchor_admits_only_min_generation (recoverLedger_anchor h)

/-- The selection never returns a candidate older than a usable one. -/
theorem selectSnapshots_max {a b : Option Snapshot} {out : Snapshot}
    (h : selectSnapshots a b = some out) :
    (∀ x, a = some x → x.generation ≤ out.generation) ∧
    (∀ x, b = some x → x.generation ≤ out.generation) := by
  cases a with
  | none =>
    cases b with
    | none => simp [selectSnapshots] at h
    | some y =>
      simp only [selectSnapshots, Option.some.injEq] at h
      subst h
      exact ⟨fun _ hx => (by cases hx), fun x hx => by cases hx; exact Nat.le_refl _⟩
  | some x0 =>
    cases b with
    | none =>
      simp only [selectSnapshots, Option.some.injEq] at h
      subst h
      exact ⟨fun x hx => by cases hx; exact Nat.le_refl _, fun _ hx => by cases hx⟩
    | some y =>
      simp only [selectSnapshots] at h
      split at h
      · rename_i hLt
        cases h
        exact ⟨fun x hx => by cases hx; exact Nat.le_of_lt hLt,
          fun x hx => by cases hx; exact Nat.le_refl _⟩
      · rename_i hGe
        cases h
        exact ⟨fun x hx => by cases hx; exact Nat.le_refl _,
          fun x hx => by cases hx; exact Nat.le_of_not_lt hGe⟩

/-- **Two-slot crash recovery (`durable_ledger.rs`)**: a write goes to the slot that does NOT
hold the current snapshot, so a crash can only disturb that other slot. Whatever the other
slot then decodes to (the old snapshot, the new one, garbage that fails its MAC, an
unavailable sidecar), recovery succeeds and returns a generation at least the current one:
the intact slot or a newer usable snapshot, never an older state. -/
