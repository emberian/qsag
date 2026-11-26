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
theorem recoverLedger_intact_slot_never_rolls_back {anchor : ExternalMonotoneAnchor}
    {cur : Snapshot} (other : Option Snapshot) :
    (usableSnapshot anchor 0 (some cur) = some cur →
      ∃ out, recoverLedger true anchor (some cur) other = some out ∧
        cur.generation ≤ out.generation ∧
        (out = cur ∨ usableSnapshot anchor 1 other = some out)) ∧
    (usableSnapshot anchor 1 (some cur) = some cur →
      ∃ out, recoverLedger true anchor other (some cur) = some out ∧
        cur.generation ≤ out.generation ∧
        (out = cur ∨ usableSnapshot anchor 0 other = some out)) := by
  constructor
  · intro hCur
    cases hO : usableSnapshot anchor 1 other with
    | none => exact ⟨cur, by simp [recoverLedger, hCur, hO, selectSnapshots], Nat.le_refl _, Or.inl rfl⟩
    | some y =>
      by_cases hLt : cur.generation < y.generation
      · exact ⟨y, by simp [recoverLedger, hCur, hO, selectSnapshots, hLt], Nat.le_of_lt hLt, Or.inr rfl⟩
      · exact ⟨cur, by simp [recoverLedger, hCur, hO, selectSnapshots, hLt], Nat.le_refl _, Or.inl rfl⟩
  · intro hCur
    cases hO : usableSnapshot anchor 0 other with
    | none => exact ⟨cur, by simp [recoverLedger, hCur, hO, selectSnapshots], Nat.le_refl _, Or.inl rfl⟩
    | some y =>
      by_cases hLt : y.generation < cur.generation
      · exact ⟨cur, by simp [recoverLedger, hCur, hO, selectSnapshots, hLt], Nat.le_refl _, Or.inl rfl⟩
      · exact ⟨y, by simp [recoverLedger, hCur, hO, selectSnapshots, hLt], Nat.le_of_not_lt hLt, Or.inr rfl⟩

/-- Missing genesis cannot be replaced by an empty fallback snapshot. -/
theorem recoverLedger_missing_genesis (anchor : ExternalMonotoneAnchor) (a b : Option Snapshot) :
    recoverLedger false anchor a b = none := by
  unfold recoverLedger; rfl

/-- Full FTS framing, including the number of frames and each little-endian u64 length. -/
def burnTag (domain : Bytes) (frames : List Bytes) : Bytes :=
  cshake256Bytes domain (framed64 frames)

/-- `QSBURN05` header body: magic, 32-byte key id, 32-byte genesis salt. -/
def burnHeaderBody (keyId genesis : Bytes) : Bytes :=
  [0x51, 0x53, 0x42, 0x55, 0x52, 0x4e, 0x30, 0x35] ++ keyId ++ genesis

/-- `file_identity`: device and inode of the held descriptor, big-endian. -/
def burnIdentity (device inode : Nat) : Bytes := encodeU64BeNat device ++ encodeU64BeNat inode

/-- V4 genesis tag (`QSAG.BURN.GENESIS.V4`): binds the MAC key, the data inode's identity and the 72-byte header body.
It is also the initial `last_tag` of the record chain. -/
def burnGenesisTag (key identity keyId genesis : Bytes) : Bytes :=
  burnTag [0x51, 0x53, 0x41, 0x47, 0x2e, 0x42, 0x55, 0x52, 0x4e, 0x2e, 0x47, 0x45, 0x4e, 0x45, 0x53, 0x49, 0x53, 0x2e, 0x56, 0x34]
    [key, identity, burnHeaderBody keyId genesis]

def burnHeader (key identity keyId genesis : Bytes) : Bytes :=
  burnHeaderBody keyId genesis ++ burnGenesisTag key identity keyId genesis

def burnRecordBody (party epoch : Nat) : Bytes :=
  [UInt8.ofNat (party / 256), UInt8.ofNat party] ++ encodeU64BeNat epoch

def burnRecordTag (key keyId genesis previous body : Bytes) : Bytes :=
  burnTag [0x51, 0x53, 0x41, 0x47, 0x2e, 0x42, 0x55, 0x52, 0x4e, 0x2e, 0x52, 0x45, 0x43, 0x4f, 0x52, 0x44, 0x2e, 0x56, 0x32] [key, keyId, genesis, previous, body]

def burnRecord (key keyId genesis previous : Bytes) (party epoch : Nat) : Bytes :=
  let body := burnRecordBody party epoch
  body ++ burnRecordTag key keyId genesis previous body

theorem burnGenesisTag_length (key identity keyId genesis : Bytes) :
    (burnGenesisTag key identity keyId genesis).length = 32 := by
  simp [burnGenesisTag, burnTag, cshake256Bytes_length]

theorem burnHeader_length {key identity keyId genesis : Bytes}
    (hk : keyId.length = 32) (hg : genesis.length = 32) :
    (burnHeader key identity keyId genesis).length = 104 := by
  simp [burnHeader, burnHeaderBody, burnGenesisTag_length, hk, hg]

theorem burnRecord_length (key keyId genesis previous : Bytes) (party epoch : Nat) :
    (burnRecord key keyId genesis previous party epoch).length = 42 := by
  simp [burnRecord, burnRecordBody, burnRecordTag, burnTag, encodeU64BeNat_length,
    cshake256Bytes_length]

/-- Byte decoder: split full chunks into 10-byte bodies and 32-byte tags. Fuel is the record
count derived from the input length. -/
def burnChunks : Nat → Bytes → Option (List (Bytes × Bytes))
  | 0, bs => if bs = [] then some [] else none
  | n+1, bs =>
    if bs = [] then some [] else
    if bs.length < 42 then none else
    match burnChunks n (bs.drop 42) with
    | none => none
    | some rest => some ((bs.take 10, (bs.drop 10).take 32) :: rest)

/-- `DurableBurnJournal::load` on the raw file bytes, for the descriptor identity `identity`:
length check, magic and key id, genesis tag over the first 72 bytes, then the record chain
from the genesis tag with duplicate rejection. -/
def openBurnBytes (key identity keyId bytes : Bytes) : Option (List Bytes × Bytes) :=
  if bytes.length < 104 ∨ (bytes.length - 104) % 42 ≠ 0 then none else
  if bytes.take 104 ≠ burnHeader key identity keyId ((bytes.drop 40).take 32) then none else
  match burnChunks ((bytes.length - 104) / 42) (bytes.drop 104) with
  | none => none
  | some chunks =>
    openBurnJournal (burnRecordTag key keyId ((bytes.drop 40).take 32))
      (burnGenesisTag key identity keyId ((bytes.drop 40).take 32)) ⟨chunks, []⟩

theorem openBurnBytes_short_tail (key identity keyId bytes : Bytes)
    (h : (bytes.length - 104) % 42 ≠ 0) : openBurnBytes key identity keyId bytes = none := by
  simp [openBurnBytes, h]

/-- The file a writer with these parameters produces: header, then 42-byte records. -/
def burnJournalBytes (key identity keyId genesis : Bytes) (records : List (Bytes × Bytes)) :
    Bytes :=
  burnHeader key identity keyId genesis ++ records.flatMap (fun r => r.1 ++ r.2)

private theorem burnRecords_flat_length (records : List (Bytes × Bytes))
    (hr : ∀ r ∈ records, r.1.length = 10 ∧ r.2.length = 32) :
    (records.flatMap (fun r => r.1 ++ r.2)).length = 42 * records.length := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    have h0 := hr r (List.mem_cons_self ..)
    have ih' := ih (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, ih', h0.1, h0.2]
    omega

private theorem burnChunks_flat (records : List (Bytes × Bytes))
    (hr : ∀ r ∈ records, r.1.length = 10 ∧ r.2.length = 32) :
    burnChunks records.length (records.flatMap (fun r => r.1 ++ r.2)) = some records := by
  induction records with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨b, t⟩ := r
    have h0 := hr (b, t) (List.mem_cons_self ..)
    have hb : b.length = 10 := h0.1
    have ht : t.length = 32 := h0.2
    have ih' := ih (fun x hx => hr x (List.mem_cons_of_mem _ hx))
    have hbt : (b ++ t).length = 42 := by rw [List.length_append, hb, ht]
    have hNe : (b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2) ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_append, hbt] at this
      simp at this
    have hLen : ¬ ((b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2)).length < 42 := by
      rw [List.length_append, hbt]; omega
    have hDrop : ((b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2)).drop 42 =
        rest.flatMap (fun r => r.1 ++ r.2) := List.drop_left' hbt
    have hTake : ((b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2)).take 10 = b := by
      rw [List.append_assoc]; exact List.take_left' hb
    have hMid : (((b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2)).drop 10).take 32 = t := by
      rw [List.append_assoc, List.drop_left' hb]; exact List.take_left' ht
    show burnChunks (rest.length + 1) ((b ++ t) ++ rest.flatMap (fun r => r.1 ++ r.2)) = _
    rw [burnChunks, ite_eq_right hNe, ite_eq_right hLen, hDrop, ih', hTake, hMid]

/-- **Byte decoder ↔ record model**: on the bytes an honest writer lays down, `load` is exactly
the chained-record recovery `openBurnJournal`, started from the V3 genesis tag. Every
record-level theorem about `openBurnJournal` therefore speaks about the real 104 + 42·n byte
file, and the decoder is not vacuous. -/
theorem openBurnBytes_journalBytes (key identity keyId genesis : Bytes)
    (records : List (Bytes × Bytes))
    (hk : keyId.length = 32) (hg : genesis.length = 32)
    (hr : ∀ r ∈ records, r.1.length = 10 ∧ r.2.length = 32) :
    openBurnBytes key identity keyId (burnJournalBytes key identity keyId genesis records) =
      openBurnJournal (burnRecordTag key keyId genesis)
        (burnGenesisTag key identity keyId genesis) ⟨records, []⟩ := by
  have hH : (burnHeader key identity keyId genesis).length = 104 := burnHeader_length hk hg
  have hF := burnRecords_flat_length records hr
  have hLen : (burnJournalBytes key identity keyId genesis records).length =
      104 + 42 * records.length := by
    rw [burnJournalBytes, List.length_append, hH, hF]
  have hTake : (burnJournalBytes key identity keyId genesis records).take 104 =
      burnHeader key identity keyId genesis := List.take_left' hH
  have hDrop : (burnJournalBytes key identity keyId genesis records).drop 104 =
      records.flatMap (fun r => r.1 ++ r.2) := List.drop_left' hH
  have hGen : ((burnJournalBytes key identity keyId genesis records).drop 40).take 32 =
      genesis := by
    have hSplit : burnJournalBytes key identity keyId genesis records =
        ([0x51, 0x53, 0x42, 0x55, 0x52, 0x4e, 0x30, 0x35] ++ keyId) ++
          (genesis ++ (burnGenesisTag key identity keyId genesis ++
            records.flatMap (fun r => r.1 ++ r.2))) := by
      simp [burnJournalBytes, burnHeader, burnHeaderBody, List.append_assoc]
    rw [hSplit, List.drop_left' (by simp [hk]), List.take_left' hg]
  have hC1 : ¬ ((burnJournalBytes key identity keyId genesis records).length < 104 ∨
      ((burnJournalBytes key identity keyId genesis records).length - 104) % 42 ≠ 0) := by
    rw [hLen]; omega
  have hDiv : ((burnJournalBytes key identity keyId genesis records).length - 104) / 42 =
      records.length := by
    rw [hLen]; omega
  unfold openBurnBytes
  rw [ite_eq_right hC1, hGen, hTake, ite_eq_right (fun h => h rfl), hDrop, hDiv,
    burnChunks_flat records hr]

/-- A journal copied to another inode fails closed: the V3 genesis tag is recomputed for the
identity of the descriptor actually held, so the copy opens only if the two genesis tags
collide (the stated premise is that this one concrete pair of tags differs). -/
theorem openBurnBytes_copied_inode_refused (key identity identity' keyId genesis : Bytes)
    (records : List (Bytes × Bytes))
    (hk : keyId.length = 32) (hg : genesis.length = 32)
    (distinct : burnGenesisTag key identity' keyId genesis ≠
      burnGenesisTag key identity keyId genesis) :
    openBurnBytes key identity' keyId (burnJournalBytes key identity keyId genesis records) =
      none := by
  have hH : (burnHeader key identity keyId genesis).length = 104 := burnHeader_length hk hg
  have hTake : (burnJournalBytes key identity keyId genesis records).take 104 =
      burnHeader key identity keyId genesis := List.take_left' hH
  have hGen : ((burnJournalBytes key identity keyId genesis records).drop 40).take 32 =
      genesis := by
    have hSplit : burnJournalBytes key identity keyId genesis records =
        ([0x51, 0x53, 0x42, 0x55, 0x52, 0x4e, 0x30, 0x35] ++ keyId) ++
          (genesis ++ (burnGenesisTag key identity keyId genesis ++
            records.flatMap (fun r => r.1 ++ r.2))) := by
      simp [burnJournalBytes, burnHeader, burnHeaderBody, List.append_assoc]
    rw [hSplit, List.drop_left' (by simp [hk]), List.take_left' hg]
  have hNe : burnHeader key identity keyId genesis ≠ burnHeader key identity' keyId genesis := by
    intro h
    exact distinct (List.append_cancel_left h).symm
  unfold openBurnBytes
  split
  · rfl
  · rw [hGen, hTake, ite_eq_left hNe]

/-- A partial `write_all` is observable in file length. It is not atomic replacement. -/
theorem partial_append_refuses (key identity keyId old tail : Bytes) (n : Nat)
    (hOld : old.length = 104 + 42*n) (hTail : 0 < tail.length ∧ tail.length < 42) :
    openBurnBytes key identity keyId (old ++ tail) = none := by
  apply openBurnBytes_short_tail
  rw [List.length_append, hOld]
  have h : 104 + 42*n + tail.length - 104 = 42*n + tail.length := by omega
  rw [h, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hTail.2]
  omega

/-- `LockedRecord::replace` syscall stages (identity check, type check, temp create, three
writes, temp sync, re-check, rename, parent sync). The journal machines in
`CeremonyAtomicityAndAbort` step through these and allow a crash or an I/O error at each one.
The POSIX `replaceAtomic` model of this file writes the record in one `pwrite` and closes the
temp descriptor before the rename; it is not a syscall-for-syscall model of `LockedRecord`. -/
inductive ReplacePc where
  | checkBefore | checkTypes | createTemp | writeMagic | writeSeal | writePayload
  | syncTemp | checkAfter | rename | syncParent | done | poisoned
  deriving Repr, DecidableEq

/-- Adaptive adversary with access only to the signing oracle's returned tags. Its final
record is the candidate, not an existential quantifier over all mathematically valid tags. -/
inductive WalMacAttack where
  | output (candidate : WalRecord)
  | query (body : WalRecordBody) (wellFormed : body.WellFormed) (next : Bytes → WalMacAttack)

def runWalMacAttack (mac : KeyedMacFn) (key : Bytes) :
    WalMacAttack → List WalRecordBody × WalRecord
  | .output r => ([], r)
  | .query b _ next =>
    let result := runWalMacAttack mac key (next (computeWalMac mac key b))
    (b :: result.1, result.2)

theorem runWalMacAttack_queries_wellFormed (mac : KeyedMacFn) (key : Bytes)
    (attack : WalMacAttack) :
    ∀ b ∈ (runWalMacAttack mac key attack).1, b.WellFormed := by
  induction attack with
  | output r => simp [runWalMacAttack]
  | query b wf next ih =>
    intro x hx
    simp only [runWalMacAttack, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact wf
    · exact ih _ x hx

/-- The standard primitive-game output: a candidate preimage/tag pair and the actual oracle
query preimages. Width and authentication security are deliberately separate obligations. -/
def primitiveMacWin (mac : KeyedMacFn) (key : Bytes)
    (queries : List Bytes) (message tag : Bytes) : Prop :=
  message ∉ queries ∧ tag = mac key message

theorem wal_forgery_extracts_primitive_forgery (mac : KeyedMacFn) (key : Bytes)
    (queries : List WalRecordBody) (r : WalRecord)
    (wf : ∀ b ∈ queries, b.WellFormed) (bad : MacForgery mac key queries r) :
    primitiveMacWin mac key (queries.map encodeWalBody) (encodeWalBody r.body) r.keyedMac := by
  rw [MacForgery.public_eq_1] at bad
  refine ⟨?_, ?_⟩
  · intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    have eq := encodeWalBody_injective (wf b hb) bad.1.1 he
    exact bad.2.1 (eq ▸ hb)
  · have h := bad.2.2
    rw [verifyWalMac.public_eq_1, computeWalMac.public_eq_1] at h
    exact eq_of_beq h

/-- Explicit finite probability transfer. Each sample fixes key and adversary coins; the
adversary may adapt its queries to returned tags. Counts divided by `samples.length` are
probabilities when the list is nonempty. Any primitive-game bound transfers with no loss. -/
theorem wal_mac_experiment_bound (mac : KeyedMacFn) (samples : List (Bytes × WalMacAttack))
    (walWin primitiveWin : Bytes × WalMacAttack → Bool)
    (walSpec : ∀ sample, walWin sample = true →
      MacForgery mac sample.1 (runWalMacAttack mac sample.1 sample.2).1
        (runWalMacAttack mac sample.1 sample.2).2)
    (primitiveSpec : ∀ sample,
      primitiveMacWin mac sample.1 ((runWalMacAttack mac sample.1 sample.2).1.map encodeWalBody)
        (encodeWalBody (runWalMacAttack mac sample.1 sample.2).2.body)
        (runWalMacAttack mac sample.1 sample.2).2.keyedMac → primitiveWin sample = true) :
    (samples.filter walWin).length ≤ (samples.filter primitiveWin).length := by
  have pointwise : ∀ sample, walWin sample = true → primitiveWin sample = true := by
    intro sample h
    exact primitiveSpec sample (wal_forgery_extracts_primitive_forgery mac sample.1 _ _
      (runWalMacAttack_queries_wellFormed mac sample.1 sample.2) (walSpec sample h))
  induction samples with
  | nil => simp
  | cons sample rest ih =>
    cases hw : walWin sample <;> cases hp : primitiveWin sample <;>
      simp_all <;> omega

/-- Belt's resource identity is key-scoped; identical replay is permitted, different
message/salt/digits for the same epoch are not. Capacity and bounded forward jumps are real
checks in `latched_salt`, not a globally unique receipt-epoch abstraction. -/
structure BeltBinding where
  epoch : Nat
  digest : Bytes
  retrySalt : Bytes
  digits : Bytes
  deriving Repr, DecidableEq

structure BeltState where
  keyId : Bytes
  nextEpoch : Nat
  inFlight : Option BeltBinding
  poisoned : Bool
  deriving Repr, DecidableEq

inductive BeltBindOutcome where
  | fresh | replay
  deriving Repr, DecidableEq

/-- Binding decision and post-state on successful persistence. `beltPersistFailure` is the
error branch; this function alone is not an I/O refinement theorem. -/
def beltBind (capacityLog2 : Nat) (s : BeltState) (r : BeltBinding) :
    Option (BeltState × BeltBindOutcome) :=
  if s.poisoned then none else
  if s.inFlight = some r then some (s, .replay) else
  if (s.inFlight.any fun old => old.epoch == r.epoch) then none else
  if s.nextEpoch ≤ r.epoch ∧ r.epoch < 2^capacityLog2 ∧ r.epoch ≤ s.nextEpoch + 64 then
    some ({ s with nextEpoch := r.epoch + 1, inFlight := some r }, .fresh)
  else none

theorem belt_replay_identical {cap : Nat} {s s' : BeltState} {r : BeltBinding}
    (h : beltBind cap s r = some (s', .replay)) : s.inFlight = some r := by
  unfold beltBind at h
  split at h
  · cases h
  · split at h
    · assumption
    · split at h
      · cases h
      · split at h <;> cases h

theorem belt_same_epoch_different_binding_rejected {cap : Nat} {s : BeltState}
    {old r : BeltBinding} (held : s.inFlight = some old) (epoch : old.epoch = r.epoch)
    (different : old ≠ r) : beltBind cap s r = none := by
  simp [beltBind, held, different, epoch]

/-- Decode exactly one fixed-width reservation, with key identity supplied by the header. -/
def decodeReservation (keyId bytes : Bytes) : Option Reservation := do
  let (cid, b1) ← splitExactBytes 32 bytes
  let (codeword, b2) ← splitExactBytes 32 b1
  let (seed, b3) ← splitExactBytes 8 b2
  let (hedge, tail) ← splitExactBytes 8 b3
  if tail ≠ [] then none else do
    let seed ← decodeU64BeNat seed
    let hedge ← decodeU64BeNat hedge
    pure ⟨cid, keyId, codeword, seed, hedge⟩

/-- Decode and validate in insertion order, just as `open_existing` calls `validate` before
pushing each entry. This rejects duplicate ceremony/codeword IDs and non-increasing cursors. -/
def decodeReservations (keyId : Bytes) : Nat → Bytes → List Reservation → Option (List Reservation)
  | 0, bytes, entries => if bytes = [] then some entries else none
  | n+1, bytes, entries => do
    let (entry, tail) ← splitExactBytes 137 bytes
    if entry.drop 80 ≠ List.replicate 57 0 then none else do
    let r ← decodeReservation keyId (entry.take 80)
    if reservationValid keyId entries r then
      decodeReservations keyId n tail (entries ++ [r])
    else none

/-- Decoder restricted to the fresh-unbound subprotocol. Full retries use
`openCeremonyBytesV3` below; they must not be projected to an all-codewords-Nodup claim. -/
def openCeremonyBytes (key lockSeal keyId bytes : Bytes) : Option (List Reservation) :=
  if bytes.length < 80 ∨ (bytes.length - 80) % 137 ≠ 0 then none else do
    let body := bytes.take (bytes.length - 32)
    let count := (bytes.length - 80) / 137
    if bytes.take 40 ≠ [81,83,65,71,67,82,74,51] ++ keyId ∨
        bytes.drop (bytes.length - 32) ≠ ceremonyTag key lockSeal body then none else do
    let generation ← decodeU64BeNat ((bytes.drop 40).take 8)
    if generation ≠ count + 1 then none else
    decodeReservations keyId count (body.drop 48) []

theorem openCeremonyBytes_short_tail (key lockSeal keyId bytes : Bytes)
    (h : (bytes.length - 80) % 137 ≠ 0) : openCeremonyBytes key lockSeal keyId bytes = none := by
  simp [openCeremonyBytes, h]

/-- Snapshot parser consumes all bytes and rejects duplicate map keys instead of silently
letting insertion overwrite an earlier value. -/
def decodeLedgerRecords : Nat → Bytes → List (Bytes × Bytes) → Option (List (Bytes × Bytes))
  | 0, bytes, records => if bytes = [] then some records else none
  | n+1, bytes, records => do
    let (kb, b1) ← splitExactBytes 4 bytes
    let (vb, b2) ← splitExactBytes 4 b1
    let k ← pcwDecodeU32Be kb.reverse
    let v ← pcwDecodeU32Be vb.reverse
    let (key, b3) ← splitExactBytes k b2
    let (value, tail) ← splitExactBytes v b3
    if records.any (fun kv => kv.1 == key) then none else
    decodeLedgerRecords n tail (records ++ [(key, value)])

private theorem decodeLedgerRecords_roundtrip_aux :
    ∀ (records acc : List (Bytes × Bytes)),
      (records.map Prod.fst).Nodup →
      (∀ kv ∈ records, kv.1.length < 2 ^ 32 ∧ kv.2.length < 2 ^ 32) →
      (∀ old ∈ acc, ∀ r ∈ records, old.1 ≠ r.1) →
      decodeLedgerRecords records.length (records.flatMap fun kv =>
        u32le kv.1.length ++ u32le kv.2.length ++ kv.1 ++ kv.2) acc = some (acc ++ records) := by
  intro records
  induction records with
  | nil => intro acc _ _ _; simp [decodeLedgerRecords]
  | cons r rest ih =>
    rcases r with ⟨k, v⟩
    intro acc hNd hBounds hDisjoint
    have hKv := hBounds (k, v) List.mem_cons_self
    have hNdTail : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hNd).2
    have hFresh : k ∉ rest.map Prod.fst := (List.nodup_cons.mp hNd).1
    have hNot : (acc.any fun old => old.1 == k) = false := by
      apply List.any_eq_false.mpr
      intro old hOld hTrue
      exact hDisjoint old hOld (k, v) List.mem_cons_self (eq_of_beq hTrue)
    have hKLen : (u32le k.length).length = 4 := by simp [u32le, pcwEncodeU32Be_length]
    have hVLen : (u32le v.length).length = 4 := by simp [u32le, pcwEncodeU32Be_length]
    have hKDec : pcwDecodeU32Be (u32le k.length).reverse = some k.length := by
      simpa [u32le] using pcwDecodeU32Be_encodeU32Be hKv.1
    have hVDec : pcwDecodeU32Be (u32le v.length).reverse = some v.length := by
      simpa [u32le] using pcwDecodeU32Be_encodeU32Be hKv.2
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decodeLedgerRecords,
      bind, Option.bind, splitExactBytes_append hKLen, splitExactBytes_append hVLen,
      hKDec, hVDec, splitExactBytes_append rfl, hNot, Bool.false_eq_true, ↓reduceIte]
    have hNext : ∀ old ∈ acc ++ [(k, v)], ∀ r ∈ rest, old.1 ≠ r.1 := by
      intro old hOld r hr
      rcases List.mem_append.mp hOld with hPrev | hNew
      · exact hDisjoint old hPrev r (List.mem_cons_of_mem (k, v) hr)
      · rcases List.mem_singleton.mp hNew with rfl
        intro hEq
        apply hFresh
        have hm : r.1 ∈ rest.map Prod.fst := List.mem_map.mpr ⟨r, hr, rfl⟩
        exact Eq.mp (congrArg (· ∈ rest.map Prod.fst) hEq.symm) hm
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      ih (acc ++ [(k, v)]) hNdTail
        (fun kv hkv => hBounds kv (List.mem_cons_of_mem (k, v) hkv)) hNext

/-- General snapshot-record roundtrip: canonical fixed-width lengths and duplicate-free keys
    decode to exactly the original association list, with no accumulator or fixture restriction. -/
theorem decodeLedgerRecords_roundtrip (records : List (Bytes × Bytes))
    (hNd : (records.map Prod.fst).Nodup)
    (hBounds : ∀ kv ∈ records, kv.1.length < 2 ^ 32 ∧ kv.2.length < 2 ^ 32) :
    decodeLedgerRecords records.length (records.flatMap fun kv =>
      u32le kv.1.length ++ u32le kv.2.length ++ kv.1 ++ kv.2) [] = some records := by
  simpa using decodeLedgerRecords_roundtrip_aux records [] hNd hBounds (by simp)

/-- `read_slot` after the LockedRecord wrapper and seal checks. The byte-size limit,
MAC, parity, bounded count, duplicate keys, and exact parser exhaustion are all checked. -/
def openLedgerSlot (domain key genesisSeal ledgerId : Bytes) (parity : Nat)
    (bytes : Bytes) : Option Snapshot :=
  if bytes.length < 48 ∨ 16 * 1024 * 1024 < bytes.length then none else do
    let body := bytes.take (bytes.length - 32)
    let tag := bytes.drop (bytes.length - 32)
    if tag ≠ ledgerTag domain key genesisSeal ledgerId [115,110,97,112,115,104,111,116] body
      then none else do
    let (gb, b1) ← splitExactBytes 8 body
    let (cb, recordsBytes) ← splitExactBytes 8 b1
    let generation ← decodeU64BeNat gb.reverse
    let count ← decodeU64BeNat cb.reverse
    if generation % 2 ≠ parity ∨ recordsBytes.length / 8 < count then none else do
      let records ← decodeLedgerRecords count recordsBytes []
      pure ⟨generation, records, tag⟩

def ledgerGenesisBytes (domain key genesisSeal ledgerId sealA sealB : Bytes) : Bytes :=
  let body := ledgerGenesisBody ledgerId sealA sealB
  body ++ ledgerTag domain key genesisSeal ledgerId [103,101,110,101,115,105,115] body

/-- An unavailable slot remains unavailable for future writes. Opening the surviving slot
never recreates a sidecar or silently changes its genesis-authenticated seal. -/
def recoverLedgerBytes (domain key genesisSeal ledgerId sealA sealB genesisBytes : Bytes)
    (anchor : ExternalMonotoneAnchor) (slotA slotB : Option Bytes) : Option Snapshot :=
  recoverLedger (genesisBytes == ledgerGenesisBytes domain key genesisSeal ledgerId sealA sealB)
    anchor (slotA.bind (openLedgerSlot domain key genesisSeal ledgerId 0))
      (slotB.bind (openLedgerSlot domain key genesisSeal ledgerId 1))

theorem recoverLedgerBytes_checkpoint {domain key genesisSeal ledgerId sealA sealB genesis : Bytes}
    {anchor : ExternalMonotoneAnchor} {a b : Option Bytes} {out : Snapshot}
    (h : recoverLedgerBytes domain key genesisSeal ledgerId sealA sealB genesis anchor a b = some out) :
    verifyAgainstExternalAnchor anchor out.generation out.tag = true :=
  recoverLedger_anchor h

/-- Locked FTS descriptor state. The same journal inode remains locked throughout append;
there is no temp inode and no rename. `failed` is set before identity checking or writing. -/
structure BurnAppendState where
  keyId : Bytes
  genesis : Bytes
  lastTag : Bytes
  bodies : List Bytes
  inode : Nat
  descriptor : Nat
  locked : Bool
  failed : Bool
  disk : Bytes
  visible : Bytes
  pending : Option Bytes := none
  dirty : Bool := false
  deriving Repr, DecidableEq

/-- Caller supplies the observed pathname inode and length from `check_identity`. -/
def beginBurnAppend (key : Bytes) (s : BurnAppendState) (requestedKey : Bytes)
    (pathInode party epoch : Nat) : BurnAppendState :=
  if s.failed ∨ requestedKey ≠ s.keyId ∨ burnRecordBody party epoch ∈ s.bodies then s else
  let failed := { s with failed := true }
  if !s.locked ∨ pathInode ≠ s.inode ∨ s.visible.length ≠ 104 + 42*s.bodies.length ∨
      2^16 ≤ party ∨ 2^64 ≤ epoch then failed else
  { failed with pending := some (burnRecord key s.keyId s.genesis s.lastTag party epoch) }

/-- Partial progress of `write_all`; 0 through 42 bytes can be present at a crash cut. -/
def writeBurnAppend (s : BurnAppendState) (written : Nat) : BurnAppendState :=
  match s.pending with
  | none => s
  | some record => { s with visible := s.disk ++ record.take written, dirty := true }

/-- Full media sync is the commit point. No receipt exists for partial append or failed sync. -/
def syncBurnAppend (s : BurnAppendState) (ioSucceeded : Bool) : BurnAppendState × Option Bytes :=
  match s.pending with
  | none => (s, none)
  | some record =>
    if ioSucceeded ∧ s.visible = s.disk ++ record ∧ record.length = 42 then
      ({ s with disk := s.visible, bodies := s.bodies ++ [record.take 10], lastTag := record.drop 10, pending := none, failed := false, dirty := false }, some (record.take 10))
    else ({ s with failed := true, pending := none }, none)

/-- Physical sectors overlap the old tail and new append: corruption is applied to the whole
inode, not only to the appended 42 bytes. Process/descriptor lifetime ends on power loss. -/
def crashBurnAppend (s : BurnAppendState) (mask : SectorTearMask) : Bytes :=
  if s.dirty then mixSectors mask.geometry.byteWidth mask.sectorChoices s.disk s.visible
  else s.disk

/-- Direct weld to the existing inode crash semantics. In particular a tear can damage an
already present record sharing the append sector; the byte decoder may then refuse recovery. -/
theorem burnAppend_posix_crash_outcomes {fs crashed : PosixFsState} {inode : Nat}
    {old : Bytes} (disk : assocLookup fs.nand.fileBlocks inode = some old)
    (crash : CrashStep fs crashed) :
    assocLookup crashed.nand.fileBlocks inode = some old ∨
    (∃ cache, assocLookup fs.driveCache.cachedFiles inode = some cache ∧
      assocLookup crashed.nand.fileBlocks inode = some cache) ∨
    (∃ (pending : Bytes) (mask : SectorTearMask), pendingVolatileWrite fs inode = some pending ∧
      assocLookup crashed.nand.fileBlocks inode =
        some (mixSectors mask.geometry.byteWidth mask.sectorChoices old pending)) :=
  crashStep_inode_outcome disk crash

theorem syncBurnAppend_release_durable {s s' : BurnAppendState} {ok : Bool} {body : Bytes}
    (h : syncBurnAppend s ok = (s', some body)) :
    s'.disk = s.visible ∧ body ∈ s'.bodies ∧ s'.failed = false := by
  unfold syncBurnAppend at h
  cases hp : s.pending with
  | none => simp [hp] at h
  | some record =>
    simp only [hp] at h
    split at h
    · cases h
      exact ⟨rfl, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
    · cases h

/-- Record-level host view of the byte-oriented append machine. Failed handles are closed;
    every successfully synced body is both recovered state and a burned host leaf. -/
def burnAppendHostOfFile (s : BurnAppendState) (f : BurnJournalFile) : BurnHost :=
  { file := f
    handle := if s.failed then none else some (s.bodies, s.lastTag)
    burned := s.bodies }

theorem burnAppendHostOfFile_inv (tagFn : List UInt8 → List UInt8 → List UInt8)
    (genesisTag : List UInt8) (s : BurnAppendState) (f : BurnJournalFile)
    (hOpen : openBurnJournal tagFn genesisTag f = some (s.bodies, s.lastTag)) :
    BurnHostInv tagFn genesisTag (burnAppendHostOfFile s f) := by
  have hNd := (openBurnJournal_some hOpen).2.2
  rw [BurnHostInv.public_eq_1]
  right
  refine ⟨?_, ?_, ?_⟩
  · simpa [burnAppendHostOfFile] using hNd
  · intro bodies last h b hb
    have hEq := Option.some.inj (hOpen.symm.trans h)
    have hBodies : s.bodies = bodies := (Prod.mk.inj hEq).1
    rw [← hBodies]
    exact hb
  · intro bodies last h
    simp only [burnAppendHostOfFile] at h
    split at h
    · cases h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact hOpen

private theorem burnRecordBody_length (party epoch : Nat) :
    (burnRecordBody party epoch).length = 10 := by
  simp [burnRecordBody, encodeU64BeNat_length]

private theorem burnRecord_take_10 (key keyId genesis previous : Bytes) (party epoch : Nat) :
    (burnRecord key keyId genesis previous party epoch).take 10 = burnRecordBody party epoch := by
  unfold burnRecord
  exact List.take_left' (burnRecordBody_length party epoch)

private theorem burnRecord_drop_10 (key keyId genesis previous : Bytes) (party epoch : Nat) :
    (burnRecord key keyId genesis previous party epoch).drop 10 =
      burnRecordTag key keyId genesis previous (burnRecordBody party epoch) := by
  unfold burnRecord
  exact List.drop_left' (burnRecordBody_length party epoch)

/-- A successful full-length `fsync` append is an exact host `reserve` step and preserves
    `BurnHostInv` on the resulting record-level host state. -/
theorem burnAppend_sync_welds_host_reserve (key identity keyId genesis : Bytes)
    (s : BurnAppendState) (f : BurnJournalFile) (party epoch : Nat)
    (hOpen : openBurnJournal (burnRecordTag key keyId genesis)
      (burnGenesisTag key identity keyId genesis) f = some (s.bodies, s.lastTag))
    (hPending : s.pending = some (burnRecord key keyId genesis s.lastTag party epoch))
    (hVisible : s.visible = s.disk ++ burnRecord key keyId genesis s.lastTag party epoch)
    (hFailed : s.failed = false)
    (hFresh : burnRecordBody party epoch ∉ s.bodies) :
    BurnHostStep (burnRecordTag key keyId genesis) (burnGenesisTag key identity keyId genesis)
      (burnAppendHostOfFile s f)
      (burnAppendHostOfFile (syncBurnAppend s true).1
        (appendBurnRecord (burnRecordTag key keyId genesis) s.lastTag
          (burnRecordBody party epoch) f)) ∧
    BurnHostInv (burnRecordTag key keyId genesis) (burnGenesisTag key identity keyId genesis)
      (burnAppendHostOfFile (syncBurnAppend s true).1
        (appendBurnRecord (burnRecordTag key keyId genesis) s.lastTag
          (burnRecordBody party epoch) f)) := by
  let body := burnRecordBody party epoch
  let next : BurnAppendState :=
    { s with
      disk := s.visible
      bodies := s.bodies ++ [body]
      lastTag := burnRecordTag key keyId genesis s.lastTag body
      pending := none
      failed := false
      dirty := false }
  have hSync : syncBurnAppend s true = (next, some body) := by
    simp only [syncBurnAppend, hPending, hVisible, burnRecord_length, and_self, ↓reduceIte,
      burnRecord_take_10, burnRecord_drop_10, next, body]
  have hLive : (burnAppendHostOfFile s f).handle = some (s.bodies, s.lastTag) := by
    simp [burnAppendHostOfFile, hFailed]
  have hStep0 := BurnHostStep.reserve (tagFn := burnRecordTag key keyId genesis)
    (genesisTag := burnGenesisTag key identity keyId genesis)
    (burnAppendHostOfFile s f) s.bodies s.lastTag body hLive hFresh
  have hStep :
      BurnHostStep (burnRecordTag key keyId genesis) (burnGenesisTag key identity keyId genesis)
        (burnAppendHostOfFile s f)
        (burnAppendHostOfFile (syncBurnAppend s true).1
          (appendBurnRecord (burnRecordTag key keyId genesis) s.lastTag body f)) := by
    rw [hSync]
    simpa only [burnAppendHostOfFile, Bool.false_eq_true, ↓reduceIte, next, body] using hStep0
  exact ⟨hStep, burnHostStep_preserves hStep (burnAppendHostOfFile_inv _ _ s f hOpen)⟩

/-- Full-write failure poisons Belt's in-memory handle; it does not roll back the on-disk
write or authorize retry with a different binding. Recovery uses a new handle. -/
def beltPersistFailure (s : BeltState) : BeltState := { s with poisoned := true }

theorem beltPersistFailure_refuses (cap : Nat) (s : BeltState) (r : BeltBinding) :
    beltBind cap (beltPersistFailure s) r = none := by
  simp [beltBind, beltPersistFailure]

/-- Exact v3 validation: retries may repeat only the current binding; fresh numeric epochs
must exceed every previously bound epoch. Ceremony IDs are always fresh. -/
def journalEntryValid (keyId : Bytes) (entries : List JournalEntry) (e : JournalEntry) : Bool :=
  e.reservation.keyId == keyId &&
  !(entries.any fun old => old.reservation.ceremonyId == e.reservation.ceremonyId) &&
  (match entries.getLast? with
   | none => true
   | some old => decide (old.reservation.seedBurnCursor < e.reservation.seedBurnCursor ∧
       old.reservation.hedgeGeneration < e.reservation.hedgeGeneration ∧
       (e.context = {} ∧ old.context = {} ∨ old.context.mpcNonceEpoch < e.context.mpcNonceEpoch))) &&
  (if e.isRetry then
    match entries.getLast? with
    | none => false
    | some old => (old.boundEpoch == e.boundEpoch &&
        old.reservation.epochOrCodeword == e.reservation.epochOrCodeword) &&
        decide (old.context.policyId = e.context.policyId ∧ old.context.spendAmount = e.context.spendAmount)
  else
    !(entries.any fun old => old.reservation.epochOrCodeword == e.reservation.epochOrCodeword) &&
    (match e.boundEpoch with
     | none => true
     | some epoch => entries.all fun old =>
       match old.boundEpoch with | none => true | some prior => decide (prior < epoch)))

def ceremonyBytesV3 (key lockSeal keyId : Bytes) (entries : List JournalEntry) : Bytes :=
  let body := ceremonyBodyV3 keyId entries
  body ++ ceremonyTag key lockSeal body

def decodeJournalEntry (keyId bytes : Bytes) : Option JournalEntry := do
  let (rb, tail) ← splitExactBytes 80 bytes
  let r ← decodeReservation keyId rb
  match tail with
  | [] => none
  | flag :: fields =>
    let (epochBytes, ctx) ← splitExactBytes 8 fields
    let (policy, ctx) ← splitExactBytes 32 ctx
    let (spend, nonce) ← splitExactBytes 8 ctx
    let spend ← decodeU64BeNat spend
    let nonce ← decodeU64BeNat nonce
    let epoch ← decodeU64BeNat epochBytes
    if 4 ≤ flag.toNat then none else
    let hasEpoch := flag.toNat % 2 == 1
    if !hasEpoch ∧ epoch ≠ 0 then none else
    pure ⟨r, if hasEpoch then some epoch else none, decide (2 ≤ flag.toNat),
      ⟨BitVec.ofNat 256 (policy.foldl (fun n b => 256 * n + b.toNat) 0),
        UInt64.ofNat spend, UInt64.ofNat nonce⟩⟩

theorem ceremony_v3_nonzero_context_roundtrip :
    let e : JournalEntry := ⟨⟨List.replicate 32 1, List.replicate 32 2,
      List.replicate 32 3, 4, 5⟩, some 6, true, ⟨7, 8, 9⟩⟩
    decodeJournalEntry e.reservation.keyId (journalEntryBytes e) = some e := by
  simp only [journalEntryBytes, reservationBytes, ceremonyContextBytes, decodeJournalEntry,
    decodeReservation, encodeU64BeNat.public_eq_1, decodeU64BeNat.public_eq_1]
  decide +kernel

def decodeJournalEntries (keyId : Bytes) : Nat → Bytes → List JournalEntry → Option (List JournalEntry)
  | 0, bytes, entries => if bytes = [] then some entries else none
  | n+1, bytes, entries => do
    let (entry, tail) ← splitExactBytes 137 bytes
    let e ← decodeJournalEntry keyId entry
    if journalEntryValid keyId entries e then
      decodeJournalEntries keyId n tail (entries ++ [e])
    else none

/-- Current `QSAGCRJ3` open: 48-byte header, 137-byte entries, 32-byte tag, generation=count+1,
checkpoint generation/tag filter, reserved flag-bit rejection and strict replay validation. -/
def openCeremonyBytesV3 (key lockSeal keyId bytes : Bytes) (anchor : ExternalMonotoneAnchor) :
    Option (Nat × List JournalEntry) :=
  if bytes.length < 80 ∨ (bytes.length - 80) % 137 ≠ 0 then none else do
    let body := bytes.take (bytes.length - 32)
    let tag := bytes.drop (bytes.length - 32)
    let count := (bytes.length - 80) / 137
    if bytes.take 40 ≠ [81,83,65,71,67,82,74,51] ++ keyId ∨
        tag ≠ ceremonyTag key lockSeal body then none else do
    let generation ← decodeU64BeNat ((bytes.drop 40).take 8)
    if generation ≠ count + 1 ∨ verifyAgainstExternalAnchor anchor generation tag ≠ true
      then none else do
    let entries ← decodeJournalEntries keyId count (body.drop 48) []
    pure (generation, entries)

/-- Retry validity extracts the exact prior binding, rather than claiming codeword uniqueness. -/
theorem journal_retry_preserves_binding {key : Bytes} {entries : List JournalEntry}
    {e : JournalEntry} (retry : e.isRetry = true) (valid : journalEntryValid key entries e = true) :
    ∃ old, entries.getLast? = some old ∧ old.boundEpoch = e.boundEpoch ∧
      old.reservation.epochOrCodeword = e.reservation.epochOrCodeword := by
  simp only [journalEntryValid, retry, ↓reduceIte, Bool.and_eq_true] at valid
  cases hl : entries.getLast? with
  | none => simp [hl] at valid
  | some old =>
    refine ⟨old, rfl, ?_⟩
    have hv := valid.2
    simp only [hl, Bool.and_eq_true, beq_iff_eq] at hv
    exact hv.1

theorem journalEntryValid_fresh_attempt {key : Bytes} {entries : List JournalEntry}
    {e : JournalEntry} (valid : journalEntryValid key entries e = true) :
    ∀ old ∈ entries, old.reservation.ceremonyId ≠ e.reservation.ceremonyId := by
  simp only [journalEntryValid, Bool.and_eq_true, Bool.not_eq_true'] at valid
  intro old ho
  have h := List.any_eq_false.mp valid.1.1.2 old ho
  simpa only [beq_iff_eq] using h

/-- Permit contains all v3 identity fields. The machine must additionally own and consume it;
this pure checker does not turn freely constructible Lean values into linear capabilities. -/
structure JournalPermitV3 where
  entry : JournalEntry
  generation : Nat
  lockSeal : Bytes
  deriving Repr, DecidableEq

def verifyCurrentPermitV3 (key lockSeal keyId : Bytes) (entries : List JournalEntry)
    (checkpoint : ExternalMonotoneAnchor) (readBack : Bytes) (permit : JournalPermitV3) : Bool :=
  permit.lockSeal == lockSeal && permit.generation == checkpoint.attestedEpoch &&
  permit.entry.reservation.keyId == keyId && entries.getLast? == some permit.entry &&
  checkpoint.attestedEpoch == entries.length + 1 &&
  checkpoint.attestedTag == ceremonyTag key lockSeal (ceremonyBodyV3 keyId entries) &&
  readBack == ceremonyBytesV3 key lockSeal keyId entries

/-- Policy-aware release must match the complete committed context. -/
def verifyCurrentPermitWithContext (key lockSeal keyId : Bytes) (entries : List JournalEntry)
    (checkpoint : ExternalMonotoneAnchor) (readBack : Bytes) (permit : JournalPermitV3)
    (expected : CeremonyContext) : Bool :=
  decide (permit.entry.context = expected) &&
    verifyCurrentPermitV3 key lockSeal keyId entries checkpoint readBack permit

theorem ceremony_context_mismatch_rejected (key lockSeal keyId : Bytes) (entries : List JournalEntry)
    (checkpoint : ExternalMonotoneAnchor) (readBack : Bytes) (permit : JournalPermitV3)
    (expected : CeremonyContext) (hm : permit.entry.context ≠ expected) :
    verifyCurrentPermitWithContext key lockSeal keyId entries checkpoint readBack permit expected = false := by
  simp [verifyCurrentPermitWithContext, hm]

theorem stale_v3_permit_refused (key lockSeal keyId : Bytes) (entries : List JournalEntry)
    (checkpoint : ExternalMonotoneAnchor) (readBack : Bytes) (permit : JournalPermitV3)
    (stale : permit.generation ≠ checkpoint.attestedEpoch) :
    verifyCurrentPermitV3 key lockSeal keyId entries checkpoint readBack permit = false := by
  simp [verifyCurrentPermitV3, stale]

/-- Retry attempts need fresh randomness even though the epoch/codeword binding is unchanged. -/
theorem journalEntryValid_advances_cursors {key : Bytes} {entries : List JournalEntry}
    {e old : JournalEntry} (last : entries.getLast? = some old)
    (valid : journalEntryValid key entries e = true) :
    old.reservation.seedBurnCursor < e.reservation.seedBurnCursor ∧
    old.reservation.hedgeGeneration < e.reservation.hedgeGeneration := by
  simp only [journalEntryValid, Bool.and_eq_true] at valid
  have hv := valid.1.2
  simp only [last, decide_eq_true_eq] at hv
  exact ⟨hv.1, hv.2.1⟩

end RustDurability

end Qsag
end
