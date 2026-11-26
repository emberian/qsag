module

public import Qsag.Exec.TwoSlotHwmCrashModel
public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
public import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive Finite Association Maps, Byte-Sequence `DirName`, & `u64be` Framing -/

/-- Process identifier in the local POSIX OS model. -/
abbrev Pid := Nat

/-- Persistent filesystem inode number (`st_ino`). -/
abbrev InodeId := Nat

/-- Process-wide file descriptor number (`fd`). -/
abbrev FdId := Nat

/-- Kernel open file description identifier (`struct file` identity, shared across `dup`/`fork`). -/
abbrev OpenDescriptionId := Nat

/-- Constructive `LawfulBEq` negation helper avoiding classical boolean lemmas. -/
theorem eq_of_not_bne_true {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : ¬(a != b) = true) : a = b := by
  cases hBeq : (a == b)
  · exfalso
    apply h
    simp [bne, hBeq]
  · exact eq_of_beq hBeq

/-- Constructive finite association-list lookup (choice-free). -/
@[expose]
def assocLookup {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (k, v) :: rest, q => if q = k then some v else assocLookup rest q

/-- Constructive finite association-list upsert replacing the first matching key or appending. -/
@[expose] def assocInsert {K V : Type} [DecidableEq K] (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: rest => if k = k' then (k, v) :: rest else (k', v') :: assocInsert k v rest

/-- Constructive finite association-list key removal erasing every binding for `k`. -/
@[expose] def assocErase {K V : Type} [DecidableEq K] (k : K) : List (K × V) → List (K × V)
  | [] => []
  | (k', v') :: rest => if k = k' then assocErase k rest else (k', v') :: assocErase k rest

/-- Map values pointwise across a finite association list while preserving key order. -/
@[expose] def mapAssocValues {K V W : Type} (f : K → V → W) : List (K × V) → List (K × W)
  | [] => []
  | (k, v) :: rest => (k, f k v) :: mapAssocValues f rest

@[simp]
theorem assocLookup_nil {K V : Type} [DecidableEq K] (q : K) :
    assocLookup ([] : List (K × V)) q = none := by rfl

@[simp]
theorem assocLookup_insert {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) (q : K) :
    assocLookup (assocInsert k v m) q = if q = k then some v else assocLookup m q := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    dsimp only [assocInsert]
    by_cases hkk : k = k'
    · subst hkk
      simp only [↓reduceIte, assocLookup]
      by_cases hqk : q = k <;> simp [hqk]
    · simp only [hkk, ↓reduceIte, assocLookup]
      by_cases hqk' : q = k'
      · subst hqk'
        have hqk : q ≠ k := fun hEq => hkk hEq.symm
        simp only [↓reduceIte, hqk]
      · simp only [hqk', ↓reduceIte, ih]

@[simp]
theorem assocLookup_cons_self {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) :
    assocLookup ((k, v) :: m) k = some v := by
  simp [assocLookup]

@[simp]
theorem assocLookup_insert_self {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) :
    assocLookup (assocInsert k v m) k = some v := by
  simp

theorem assocLookup_insert_of_ne {K V : Type} [DecidableEq K]
    {k q : K} (v : V) (m : List (K × V)) (hNe : q ≠ k) :
    assocLookup (assocInsert k v m) q = assocLookup m q := by
  simp [hNe]

@[simp]
theorem assocLookup_erase {K V : Type} [DecidableEq K]
    (k : K) (m : List (K × V)) (q : K) :
    assocLookup (assocErase k m) q = if q = k then none else assocLookup m q := by
  induction m with
  | nil =>
    by_cases h : q = k <;> simp [assocErase, h]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    dsimp only [assocErase]
    by_cases hkk : k = k'
    · subst hkk
      simp only [↓reduceIte, ih]
      by_cases hqk : q = k
      · simp [hqk]
      · simp [hqk, assocLookup]
    · simp only [hkk, ↓reduceIte, assocLookup]
      by_cases hqk' : q = k'
      · subst hqk'
        have hqk : q ≠ k := fun hEq => hkk hEq.symm
        simp [hqk]
      · simp [hqk', ih]

@[simp]
theorem assocLookup_mapAssocValues {K V W : Type} [DecidableEq K]
    (f : K → V → W) (m : List (K × V)) (q : K) :
    assocLookup (mapAssocValues f m) q = (assocLookup m q).map (f q) := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [mapAssocValues, assocLookup]
    by_cases h : q = k
    · simp [h]
    · simp [h, ih]

theorem mapAssocValues_id {K V : Type} {f : K → V → V}
    (hId : ∀ k v, f k v = v) (m : List (K × V)) :
    mapAssocValues f m = m := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [mapAssocValues]
    rw [hId k v, ih]

theorem option_map_id_ext {α : Type} {f : α → α} (hId : ∀ x, f x = x) (o : Option α) :
    o.map f = o := by
  cases o with
  | none => rfl
  | some x => exact congrArg some (hId x)

theorem assocLookup_mem_of_some {K V : Type} [DecidableEq K]
    {m : List (K × V)} {q : K} {v : V} (h : assocLookup m q = some v) :
    (q, v) ∈ m := by
  induction m with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, v'⟩
    dsimp only [assocLookup] at h
    by_cases hqk : q = k
    · subst hqk
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.Mem.head rest
    · simp only [hqk, ↓reduceIte] at h
      exact List.Mem.tail (k, v') (ih h)

theorem two_pow_32_lt_two_pow_64 : 2 ^ 32 < 2 ^ 64 := by decide

@[expose] def encodeLeBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: encodeLeBytes w (n / 256)

@[expose] def decodeLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLeBytes bs

private theorem encodeLeBytes_length : ∀ (w n : Nat), (encodeLeBytes w n).length = w
  | 0, _ => rfl
  | w + 1, n => congrArg Nat.succ (encodeLeBytes_length w (n / 256))

private theorem decodeLeBytes_encodeLeBytes :
    ∀ (w n : Nat), n < 256 ^ w → decodeLeBytes (encodeLeBytes w n) = n
  | 0, n, h => by
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := by omega
    subst hn; rfl
  | w + 1, n, h => by
    dsimp only [encodeLeBytes, decodeLeBytes]
    have hMod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      change ((BitVec.ofNat 8 (n % 256)).toNat) = n % 256
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    rw [hMod]
    have hDiv : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    rw [decodeLeBytes_encodeLeBytes w (n / 256) hDiv]
    omega

private theorem decodeLeBytes_canonical :
    ∀ (bs : List UInt8),
      decodeLeBytes bs < 256 ^ bs.length ∧ encodeLeBytes bs.length (decodeLeBytes bs) = bs
  | [] => ⟨by decide, rfl⟩
  | b :: bs => by
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs
    dsimp only [List.length_cons, decodeLeBytes, encodeLeBytes]
    have hb : b.toNat < 256 := b.toBitVec.isLt
    refine ⟨by rw [Nat.pow_succ]; omega, ?_⟩
    have hMod : (b.toNat + 256 * decodeLeBytes bs) % 256 = b.toNat := by omega
    have hDiv : (b.toNat + 256 * decodeLeBytes bs) / 256 = decodeLeBytes bs := by omega
    have hU8 : UInt8.ofNat b.toNat = b :=
      UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt hb))
    rw [hMod, hDiv, hU8, hCan]

private theorem pow_256_8_eq_two_pow_64 : (256 : Nat) ^ 8 = 2 ^ 64 := by
  show (2 ^ 8) ^ 8 = 2 ^ 64
  rw [← Nat.pow_mul]

/-- Encode a natural number `< 2^64` as 8 big-endian bytes (`u64be`). -/
def encodeU64BeNat (n : Nat) : List UInt8 :=
  (encodeLeBytes 8 n).reverse

/-- Decode 8 big-endian bytes into a natural number `< 2^64`. -/
def decodeU64BeNat (bs : List UInt8) : Option Nat :=
  if bs.length == 8 then
    some (decodeLeBytes bs.reverse)
  else
    none

theorem encodeU64BeNat_length (n : Nat) : (encodeU64BeNat n).length = 8 := by
  simp [encodeU64BeNat, encodeLeBytes_length]

theorem lt_two_pow_32_of_le_8192 {n : Nat} (h : n ≤ 8192) : n < 2 ^ 32 :=
  Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide : 8192 < 2 ^ 14)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 14 ≤ 32)))

theorem decodeU64BeNat_encodeU64BeNat {n : Nat} (hLt : n < 2 ^ 64) :
    decodeU64BeNat (encodeU64BeNat n) = some n := by
  unfold decodeU64BeNat encodeU64BeNat
  have hLen : ((encodeLeBytes 8 n).reverse.length == 8) = true := by
    rw [List.length_reverse, encodeLeBytes_length]; rfl
  rw [hLen]
  simp only [↓reduceIte, List.reverse_reverse]
  have hLt256 : n < 256 ^ 8 := by rw [pow_256_8_eq_two_pow_64]; exact hLt
  rw [decodeLeBytes_encodeLeBytes 8 n hLt256]

theorem encodeU64BeNat_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hEq : encodeU64BeNat a = encodeU64BeNat b) : a = b := by
  have hDec := congrArg decodeU64BeNat hEq
  rw [decodeU64BeNat_encodeU64BeNat ha, decodeU64BeNat_encodeU64BeNat hb] at hDec
  injection hDec

theorem decodeU64BeNat_canonical {bs : List UInt8} {v : Nat}
    (h : decodeU64BeNat bs = some v) : v < 2 ^ 64 ∧ encodeU64BeNat v = bs := by
  unfold decodeU64BeNat at h
  by_cases hLen : (bs.length == 8) = true
  · simp only [hLen, ↓reduceIte] at h
    injection h with hVal
    subst hVal
    have hBsLen : bs.length = 8 := Nat.eq_of_beq_eq_true hLen
    have hRevLen : bs.reverse.length = 8 := by rw [List.length_reverse, hBsLen]
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs.reverse
    rw [hRevLen] at hLt hCan
    refine ⟨by rw [← pow_256_8_eq_two_pow_64]; exact hLt, ?_⟩
    unfold encodeU64BeNat
    rw [hCan, List.reverse_reverse]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h
    cases h

attribute [irreducible] encodeU64BeNat decodeU64BeNat

private theorem pow_256_4_eq_two_pow_32 : (256 : Nat) ^ 4 = 2 ^ 32 := by
  show (2 ^ 8) ^ 4 = 2 ^ 32
  rw [← Nat.pow_mul]

def pcwEncodeU32Be (n : Nat) : List UInt8 :=
  (encodeLeBytes 4 n).reverse

def pcwDecodeU32Be (bs : List UInt8) : Option Nat :=
  if bs.length == 4 then some (decodeLeBytes bs.reverse) else none

theorem pcwEncodeU32Be_length (n : Nat) : (pcwEncodeU32Be n).length = 4 := by
  simp [pcwEncodeU32Be, encodeLeBytes_length]

theorem pcwDecodeU32Be_encodeU32Be {n : Nat} (hLt : n < 2 ^ 32) :
    pcwDecodeU32Be (pcwEncodeU32Be n) = some n := by
  unfold pcwDecodeU32Be pcwEncodeU32Be
  have hLen : ((encodeLeBytes 4 n).reverse.length == 4) = true := by
    rw [List.length_reverse, encodeLeBytes_length]; rfl
  rw [hLen]
  simp only [↓reduceIte, List.reverse_reverse]
  have hLt256 : n < 256 ^ 4 := by rw [pow_256_4_eq_two_pow_32]; exact hLt
  rw [decodeLeBytes_encodeLeBytes 4 n hLt256]

private theorem pcwDecodeU32Be_canonical {bs : List UInt8} {v : Nat}
    (h : pcwDecodeU32Be bs = some v) : v < 2 ^ 32 ∧ pcwEncodeU32Be v = bs := by
  unfold pcwDecodeU32Be at h
  by_cases hLen : (bs.length == 4) = true
  · simp only [hLen, ↓reduceIte] at h
    injection h with hVal
    subst hVal
    have hBsLen : bs.length = 4 := Nat.eq_of_beq_eq_true hLen
    have hRevLen : bs.reverse.length = 4 := by rw [List.length_reverse, hBsLen]
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs.reverse
    rw [hRevLen] at hLt hCan
    refine ⟨by rw [← pow_256_4_eq_two_pow_32]; exact hLt, ?_⟩
    unfold pcwEncodeU32Be
    rw [hCan, List.reverse_reverse]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h
    cases h

def pcwFrameBytes (payload : List UInt8) : List UInt8 :=
  pcwEncodeU32Be payload.length ++ payload

def pcwUnframeBytes (buf : List UInt8) : Option (List UInt8 × List UInt8) :=
  if buf.length < 4 then
    none
  else
    match pcwDecodeU32Be (buf.take 4) with
    | none => none
    | some len =>
      let body := buf.drop 4
      if body.length < len then
        none
      else
        some (body.take len, body.drop len)

def pcwConcatFramed : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => pcwFrameBytes x ++ pcwConcatFramed xs

@[simp]
theorem pcwFrameBytes_length (xs : List UInt8) :
    (pcwFrameBytes xs).length = 4 + xs.length := by
  simp [pcwFrameBytes, pcwEncodeU32Be_length]

theorem pcwConcatFramed_nil : pcwConcatFramed [] = [] := by rfl

theorem pcwConcatFramed_cons (x : List UInt8) (xs : List (List UInt8)) :
    pcwConcatFramed (x :: xs) = pcwFrameBytes x ++ pcwConcatFramed xs := by rfl

theorem pcwUnframe_frame_append {payload : List UInt8} (hLen : payload.length < 2 ^ 32)
    (rest : List UInt8) :
    pcwUnframeBytes (pcwFrameBytes payload ++ rest) = some (payload, rest) := by
  unfold pcwUnframeBytes pcwFrameBytes
  rw [List.append_assoc]
  have hNotLt4 : ¬ (pcwEncodeU32Be payload.length ++ (payload ++ rest)).length < 4 := by
    rw [List.length_append, pcwEncodeU32Be_length]
    omega
  have hNotLtBody : ¬ (payload ++ rest).length < payload.length := by
    rw [List.length_append]
    omega
  simp only [hNotLt4, ↓reduceIte,
    take_append_of_len_eq (pcwEncodeU32Be_length payload.length),
    drop_append_of_len_eq (pcwEncodeU32Be_length payload.length),
    pcwDecodeU32Be_encodeU32Be hLen,
    hNotLtBody, take_append_exact, drop_append_exact]

theorem pcwUnframeBytes_canonical {buf payload rest : List UInt8}
    (h : pcwUnframeBytes buf = some (payload, rest)) :
    payload.length < 2 ^ 32 ∧ buf = pcwFrameBytes payload ++ rest := by
  unfold pcwUnframeBytes at h
  by_cases hLt4 : buf.length < 4
  · simp only [hLt4, ↓reduceIte] at h
    cases h
  · simp only [hLt4, ↓reduceIte] at h
    cases hDec : pcwDecodeU32Be (buf.take 4) with
    | none => rw [hDec] at h; cases h
    | some len =>
      rw [hDec] at h
      dsimp only at h
      by_cases hBody : (buf.drop 4).length < len
      · simp only [hBody, ↓reduceIte] at h
        cases h
      · simp only [hBody, ↓reduceIte] at h
        injection h with hPair
        injection hPair with hPay hRest
        obtain ⟨hLenLt, hDecCan⟩ := pcwDecodeU32Be_canonical hDec
        have hPayLen : payload.length = len := by
          rw [← hPay, List.length_take]
          omega
        refine ⟨hPayLen ▸ hLenLt, ?_⟩
        unfold pcwFrameBytes
        rw [hPayLen, hDecCan, ← hPay, ← hRest]
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem pcwConcatFramed_injective :
    ∀ {xs ys : List (List UInt8)},
      (∀ x ∈ xs, x.length < 2 ^ 32) →
      (∀ y ∈ ys, y.length < 2 ^ 32) →
      pcwConcatFramed xs = pcwConcatFramed ys →
      xs = ys
  | [], [], _, _, _ => rfl
  | x :: xs, [], hx, _, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwUnframe_frame_append (hx x (.head _))] at hUnf
    cases hUnf
  | [], y :: ys, _, hy, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwUnframe_frame_append (hy y (.head _))] at hUnf
    cases hUnf
  | x :: xs, y :: ys, hx, hy, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwConcatFramed_cons,
        pcwUnframe_frame_append (hx x (.head _)),
        pcwUnframe_frame_append (hy y (.head _))] at hUnf
    injection hUnf with hPair
    injection hPair with hHead hTail
    rw [hHead, pcwConcatFramed_injective
      (fun a ha => hx a (.tail _ ha))
      (fun b hb => hy b (.tail _ hb))
      hTail]

attribute [irreducible] pcwFrameBytes pcwUnframeBytes pcwConcatFramed

/-! ## 4. Dual-Bound `lockGenesisId` Inode Seal & Keyed-MAC `GenesisSealedWal` Protocol -/

/-- Domain tag `"QSAGLCK1"` (`8` bytes) framing the `.lock` sidecar seal. -/
def lockSidecarMagicTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x4c, 0x43, 0x4b, 0x31]

/-- Domain tag `"QSAGWAL1"` (`8` bytes) framing on-disk WAL records. -/
def walFileMagicTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x57, 0x41, 0x4c, 0x31]

/-- Domain tag `"QSAGMAC1"` (`8` bytes) domain-separating the keyed-MAC preimage. -/
def walMacDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x4d, 0x41, 0x43, 0x31]

/-- Dual-bound `.lock` sidecar seal binding the kernel `st_ino` allocated at genesis together
    with a 256-bit (32-byte) genesis nonce. -/
structure LockSidecarSeal where
  sealedLockInode : InodeId
  genesisNonce    : List UInt8
  deriving Repr, DecidableEq

/-- Well-formedness of a `LockSidecarSeal` (`st_ino < 2^64`, 32-byte 256-bit `genesisNonce`). -/
@[expose] def LockSidecarSeal.WellFormed (s : LockSidecarSeal) : Prop :=
  s.sealedLockInode < 2 ^ 64 ∧ s.genesisNonce.length = 32

/-- Compute the 40-byte dual-bound `lockGenesisId := u64be(lockIno) || genesisNonce32`. -/
@[expose]
def computeLockGenesisId (lockIno : InodeId) (genesisNonce : List UInt8) : List UInt8 :=
  encodeU64BeNat lockIno ++ genesisNonce

theorem computeLockGenesisId_length {lockIno : InodeId} {nonce : List UInt8}
    (hNonce : nonce.length = 32) :
    (computeLockGenesisId lockIno nonce).length = 40 := by
  simp [computeLockGenesisId, encodeU64BeNat_length, hNonce]

theorem computeLockGenesisId_injective {ino₁ ino₂ : InodeId} {n₁ n₂ : List UInt8}
    (hIno₁ : ino₁ < 2 ^ 64) (hIno₂ : ino₂ < 2 ^ 64)
    (hEq : computeLockGenesisId ino₁ n₁ = computeLockGenesisId ino₂ n₂) :
    ino₁ = ino₂ ∧ n₁ = n₂ := by
  unfold computeLockGenesisId at hEq
  have hTake := congrArg (List.take 8) hEq
  have hDrop := congrArg (List.drop 8) hEq
  rw [take_append_of_len_eq (encodeU64BeNat_length ino₁),
      take_append_of_len_eq (encodeU64BeNat_length ino₂)] at hTake
  rw [drop_append_of_len_eq (encodeU64BeNat_length ino₁),
      drop_append_of_len_eq (encodeU64BeNat_length ino₂)] at hDrop
  exact ⟨encodeU64BeNat_injective hIno₁ hIno₂ hTake, hDrop⟩

/-- Encode `LockSidecarSeal` onto `.lock` media (`pcwConcatFramed [magic, u64be(ino), nonce32]`). -/
def encodeLockSidecar (s : LockSidecarSeal) : List UInt8 :=
  pcwConcatFramed [lockSidecarMagicTag, encodeU64BeNat s.sealedLockInode, s.genesisNonce]

/-- Decode and validate canonical `LockSidecarSeal` bytes. -/
def decodeLockSidecar (bs : List UInt8) : Option LockSidecarSeal :=
  match pcwUnframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != lockSidecarMagicTag then none
    else match pcwUnframeBytes r1 with
    | none => none
    | some (inoBytes, r2) =>
      match decodeU64BeNat inoBytes with
      | none => none
      | some ino =>
        match pcwUnframeBytes r2 with
        | none => none
        | some (nonce, tail) =>
          match tail with
          | [] =>
            if nonce.length == 32 then
              some { sealedLockInode := ino, genesisNonce := nonce }
            else none
          | _ :: _ => none

theorem decodeLockSidecar_encodeLockSidecar {s : LockSidecarSeal} (hWf : s.WellFormed) :
    decodeLockSidecar (encodeLockSidecar s) = some s := by
  rcases hWf with ⟨hIno, hNonce⟩
  rw [decodeLockSidecar.eq_1, encodeLockSidecar.eq_1]
  have hm : lockSidecarMagicTag.length < 2 ^ 32 :=
    lt_two_pow_32_of_le_8192 (by decide)
  have hi : (encodeU64BeNat s.sealedLockInode).length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
  have hn : s.genesisNonce.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hNonce]; decide
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hm]
  dsimp only
  rw [bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hi]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hIno]
  dsimp only
  rw [pcwConcatFramed_cons, pcwConcatFramed_nil, pcwUnframe_frame_append hn]
  dsimp only
  have hNBeq : (s.genesisNonce.length == 32) = true := by rw [hNonce]; rfl
  rw [hNBeq]
  simp only [↓reduceIte]

theorem decodeLockSidecar_canonical {bs : List UInt8} {s : LockSidecarSeal}
    (hDec : decodeLockSidecar bs = some s) :
    s.WellFormed ∧ encodeLockSidecar s = bs := by
  rw [decodeLockSidecar.eq_1] at hDec
  cases h1 : pcwUnframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != lockSidecarMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = lockSidecarMagicTag := eq_of_not_bne_true hMag
      cases h2 : pcwUnframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨inoBytes, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        cases hIno : decodeU64BeNat inoBytes with
        | none => rw [hIno] at hDec; cases hDec
        | some ino =>
          rw [hIno] at hDec
          dsimp only at hDec
          cases h3 : pcwUnframeBytes r2 with
          | none => rw [h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨nonce, tail⟩
            rw [h3] at hDec
            dsimp only at hDec
            cases tail with
            | cons _ _ => cases hDec
            | nil =>
              dsimp only at hDec
              by_cases hNLen : (nonce.length == 32) = true
              · simp only [hNLen, ↓reduceIte] at hDec
                injection hDec with hEqS
                subst hEqS
                obtain ⟨_, hBs1⟩ := pcwUnframeBytes_canonical h1
                obtain ⟨_, hBs2⟩ := pcwUnframeBytes_canonical h2
                obtain ⟨_, hBs3⟩ := pcwUnframeBytes_canonical h3
                obtain ⟨hInoLt, hInoCan⟩ := decodeU64BeNat_canonical hIno
                refine ⟨⟨hInoLt, Nat.eq_of_beq_eq_true hNLen⟩, ?_⟩
                rw [encodeLockSidecar.eq_1]
                rw [pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_nil]
                rw [hMagEq] at hBs1
                rw [hInoCan, hBs1, hBs2, hBs3]
              · simp only [hNLen, Bool.false_eq_true, ↓reduceIte] at hDec; cases hDec

/-- Authenticated body of a `GenesisSealedWal` record. -/
structure WalRecordBody where
  vaultKeyId    : List UInt8 -- 32-byte (256-bit) enrolled vault public-key / share identifier
  lockGenesisId : List UInt8 -- 40-byte dual-bound `(sealedLockInode, genesisNonce)` seal
  epoch         : Nat        -- Monotonic 64-bit signing epoch watermark
  payload       : List UInt8 -- Length-framed protocol state payload
  deriving Repr, DecidableEq

/-- Width invariants on `WalRecordBody` (`256`-bit `vaultKeyId`, `40`-byte `lockGenesisId`,
    `64`-bit `epoch`, `< 2^32`-byte length-framed `payload`). -/
@[expose] def WalRecordBody.WellFormed (b : WalRecordBody) : Prop :=
  b.vaultKeyId.length = 32 ∧
  b.lockGenesisId.length = 40 ∧
  b.epoch < 2 ^ 64 ∧
  b.payload.length < 2 ^ 32

/-- Full on-disk MAC-authenticated WAL record (`body` + 256-bit `keyedMac`). -/
structure WalRecord where
  body     : WalRecordBody
  keyedMac : List UInt8 -- 32-byte (256-bit) keyed MAC tag
  deriving Repr, DecidableEq

/-- Width invariants on `WalRecord`. -/
@[expose] def WalRecord.WellFormed (r : WalRecord) : Prop :=
  r.body.WellFormed ∧ r.keyedMac.length = 32

/-- Canonical length-framed MAC preimage covering **every** field of `WalRecordBody`. -/
def encodeWalBody (b : WalRecordBody) : List UInt8 :=
  pcwConcatFramed [walMacDomainTag, b.vaultKeyId, b.lockGenesisId, encodeU64BeNat b.epoch, b.payload]

/-- **MAC Preimage Collision-Freedom (`encodeWalBody_injective`)**:
    Every field of `WalRecordBody` is length-framed via `pcwConcatFramed`, so distinct well-formed
    record bodies **never** share a MAC preimage (choice-free). -/
theorem encodeWalBody_injective {b₁ b₂ : WalRecordBody}
    (h₁ : b₁.WellFormed) (h₂ : b₂.WellFormed)
    (hEq : encodeWalBody b₁ = encodeWalBody b₂) : b₁ = b₂ := by
  rcases h₁ with ⟨hk₁, hl₁, he₁, hp₁⟩
  rcases h₂ with ⟨hk₂, hl₂, he₂, hp₂⟩
  rw [encodeWalBody.eq_1, encodeWalBody.eq_1] at hEq
  have hBnd₁ : ∀ x ∈ [walMacDomainTag, b₁.vaultKeyId, b₁.lockGenesisId, encodeU64BeNat b₁.epoch, b₁.payload],
      x.length < 2 ^ 32 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · apply lt_two_pow_32_of_le_8192; rw [hk₁]; decide
      · rcases List.mem_cons.mp hx with rfl | hx
        · apply lt_two_pow_32_of_le_8192; rw [hl₁]; decide
        · rcases List.mem_cons.mp hx with rfl | hx
          · apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hp₁
            · cases hx
  have hBnd₂ : ∀ y ∈ [walMacDomainTag, b₂.vaultKeyId, b₂.lockGenesisId, encodeU64BeNat b₂.epoch, b₂.payload],
      y.length < 2 ^ 32 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hy with rfl | hy
      · apply lt_two_pow_32_of_le_8192; rw [hk₂]; decide
      · rcases List.mem_cons.mp hy with rfl | hy
        · apply lt_two_pow_32_of_le_8192; rw [hl₂]; decide
        · rcases List.mem_cons.mp hy with rfl | hy
          · apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact hp₂
            · cases hy
  have hListEq := pcwConcatFramed_injective hBnd₁ hBnd₂ hEq
  injection hListEq with _ hTail1
  injection hTail1 with hVk hTail2
  injection hTail2 with hLg hTail3
  injection hTail3 with hEpBytes hTail4
  injection hTail4 with hPay _
  have hEp := encodeU64BeNat_injective he₁ he₂ hEpBytes
  cases b₁; cases b₂
  dsimp only at hVk hLg hEp hPay
  subst hVk hLg hEp hPay
  rfl

/-- Encode a complete `WalRecord` onto disk bytes using strict prefix-free framing. -/
def encodeWalRecord (r : WalRecord) : List UInt8 :=
  pcwConcatFramed [walFileMagicTag, r.body.vaultKeyId, r.body.lockGenesisId,
                   encodeU64BeNat r.body.epoch, r.body.payload, r.keyedMac]

/-- Decode a complete `WalRecord` from disk bytes, rejecting truncated, torn, or trailing bytes. -/
def decodeWalRecord (bs : List UInt8) : Option WalRecord :=
  match pcwUnframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != walFileMagicTag then none
    else match pcwUnframeBytes r1 with
    | none => none
    | some (vkId, r2) =>
      if vkId.length != 32 then none
      else match pcwUnframeBytes r2 with
      | none => none
      | some (lgId, r3) =>
        if lgId.length != 40 then none
        else match pcwUnframeBytes r3 with
        | none => none
        | some (epBytes, r4) =>
          match decodeU64BeNat epBytes with
          | none => none
          | some ep =>
            match pcwUnframeBytes r4 with
            | none => none
            | some (payload, r5) =>
              match pcwUnframeBytes r5 with
              | none => none
              | some (mac, tail) =>
                match tail with
                | [] =>
                  if mac.length == 32 then
                    some { body := { vaultKeyId := vkId
                                     lockGenesisId := lgId
                                     epoch := ep
                                     payload := payload }
                           keyedMac := mac }
                  else none
                | _ :: _ => none

theorem decodeWalRecord_encodeWalRecord {r : WalRecord} (hWf : r.WellFormed) :
    decodeWalRecord (encodeWalRecord r) = some r := by
  rcases hWf with ⟨⟨hVk, hLg, hEp, hPay⟩, hMac⟩
  rw [decodeWalRecord.eq_1, encodeWalRecord.eq_1]
  have hm : walFileMagicTag.length < 2 ^ 32 :=
    lt_two_pow_32_of_le_8192 (by decide)
  have hvkLt : r.body.vaultKeyId.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hVk]; decide
  have hlgLt : r.body.lockGenesisId.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hLg]; decide
  have hepLt : (encodeU64BeNat r.body.epoch).length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
  have hmacLt : r.keyedMac.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hMac]; decide
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hm]
  dsimp only
  rw [bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hvkLt]
  dsimp only
  have hVkNe : (r.body.vaultKeyId.length != 32) = false := by rw [hVk]; rfl
  rw [hVkNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hlgLt]
  dsimp only
  have hLgNe : (r.body.lockGenesisId.length != 40) = false := by rw [hLg]; rfl
  rw [hLgNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hepLt]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hEp]
  dsimp only
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hPay]
  dsimp only
  rw [pcwConcatFramed_cons, pcwConcatFramed_nil, pcwUnframe_frame_append hmacLt]
  dsimp only
  have hMacEq : (r.keyedMac.length == 32) = true := by rw [hMac]; rfl
  rw [hMacEq]
  simp only [↓reduceIte]

theorem decodeWalRecord_canonical {bs : List UInt8} {r : WalRecord}
    (hDec : decodeWalRecord bs = some r) :
    r.WellFormed ∧ encodeWalRecord r = bs := by
  rw [decodeWalRecord.eq_1] at hDec
  cases h1 : pcwUnframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != walFileMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = walFileMagicTag := eq_of_not_bne_true hMag
      cases h2 : pcwUnframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨vkId, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        by_cases hVk : (vkId.length != 32) = true
        · simp only [hVk, ↓reduceIte] at hDec; cases hDec
        · simp only [hVk, Bool.false_eq_true, ↓reduceIte] at hDec
          have hVkEq : vkId.length = 32 := eq_of_not_bne_true hVk
          cases h3 : pcwUnframeBytes r2 with
          | none => rw [h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨lgId, r3⟩
            rw [h3] at hDec
            dsimp only at hDec
            by_cases hLg : (lgId.length != 40) = true
            · simp only [hLg, ↓reduceIte] at hDec; cases hDec
            · simp only [hLg, Bool.false_eq_true, ↓reduceIte] at hDec
              have hLgEq : lgId.length = 40 := eq_of_not_bne_true hLg
              cases h4 : pcwUnframeBytes r3 with
              | none => rw [h4] at hDec; cases hDec
              | some p4 =>
                rcases p4 with ⟨epBytes, r4⟩
                rw [h4] at hDec
                dsimp only at hDec
                cases hEp : decodeU64BeNat epBytes with
                | none => rw [hEp] at hDec; cases hDec
                | some ep =>
                  rw [hEp] at hDec
                  dsimp only at hDec
                  cases h5 : pcwUnframeBytes r4 with
                  | none => rw [h5] at hDec; cases hDec
                  | some p5 =>
                    rcases p5 with ⟨payload, r5⟩
                    rw [h5] at hDec
                    dsimp only at hDec
                    cases h6 : pcwUnframeBytes r5 with
                    | none => rw [h6] at hDec; cases hDec
                    | some p6 =>
                      rcases p6 with ⟨mac, tail⟩
                      rw [h6] at hDec
                      dsimp only at hDec
                      cases tail with
                      | cons _ _ => cases hDec
                      | nil =>
                        dsimp only at hDec
                        by_cases hMac : (mac.length == 32) = true
                        · simp only [hMac, ↓reduceIte] at hDec
                          injection hDec with hRec
                          subst hRec
                          obtain ⟨_, hBs1⟩ := pcwUnframeBytes_canonical h1
                          obtain ⟨_, hBs2⟩ := pcwUnframeBytes_canonical h2
                          obtain ⟨_, hBs3⟩ := pcwUnframeBytes_canonical h3
                          obtain ⟨_, hBs4⟩ := pcwUnframeBytes_canonical h4
                          obtain ⟨hPayLt, hBs5⟩ := pcwUnframeBytes_canonical h5
                          obtain ⟨_, hBs6⟩ := pcwUnframeBytes_canonical h6
                          obtain ⟨hEpLt, hEpCan⟩ := decodeU64BeNat_canonical hEp
                          have hMacLen : mac.length = 32 := Nat.eq_of_beq_eq_true hMac
                          refine ⟨⟨⟨hVkEq, hLgEq, hEpLt, hPayLt⟩, hMacLen⟩, ?_⟩
                          rw [encodeWalRecord.eq_1]
                          rw [pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons,
                              pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_nil]
                          rw [hMagEq] at hBs1
                          rw [hEpCan, hBs1, hBs2, hBs3, hBs4, hBs5, hBs6]
                        · simp only [hMac, Bool.false_eq_true, ↓reduceIte] at hDec; cases hDec

attribute [irreducible] encodeLockSidecar decodeLockSidecar encodeWalBody encodeWalRecord decodeWalRecord

/-- Keyed-MAC function type (`Key → Preimage → 32-byte Tag`, e.g. `KMAC256` / `HMAC-SHA3-256`). -/
abbrev KeyedMacFn := List UInt8 → List UInt8 → List UInt8

/-- Width invariant on a 256-bit `KeyedMacFn` (`∀ key msg, (macFn key msg).length = 32`). -/
@[expose] def WellFormedMacFn (macFn : KeyedMacFn) : Prop :=
  ∀ key msg, (macFn key msg).length = 32

/-- Compute a 32-byte keyed MAC over the domain-separated length-framed `WalRecordBody`. -/
def computeWalMac (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) : List UInt8 :=
  macFn macKey (encodeWalBody b)

/-- Attach a 256-bit `keyedMac` tag to `WalRecordBody`. -/
@[expose] def signWalRecord (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) : WalRecord :=
  { body := b, keyedMac := computeWalMac macFn macKey b }

/-- Verify a `WalRecord`'s 256-bit `keyedMac`. -/
def verifyWalMac (macFn : KeyedMacFn) (macKey : List UInt8) (r : WalRecord) : Bool :=
  r.keyedMac == computeWalMac macFn macKey r.body

theorem signWalRecord_wellFormed {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn)
    (macKey : List UInt8) {b : WalRecordBody} (hb : b.WellFormed) :
    (signWalRecord macFn macKey b).WellFormed :=
  ⟨hb, hMacWf macKey (encodeWalBody b)⟩

@[simp]
theorem verifyWalMac_signWalRecord (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) :
    verifyWalMac macFn macKey (signWalRecord macFn macKey b) = true :=
  (beq_iff_eq (a := computeWalMac macFn macKey b) (b := computeWalMac macFn macKey b)).mpr rfl

/-- **Candidate-specific EUF-CMA bad event**:
    Holds iff an adversary produces a well-formed `WalRecord` with a valid 256-bit `keyedMac`
    whose `WalRecordBody` was **never** authenticated by the honest vault (`r.body ∉ honestBodies`). -/
def MacForgery (macFn : KeyedMacFn) (macKey : List UInt8)
    (queriedBodies : List WalRecordBody) (r : WalRecord) : Prop :=
    r.WellFormed ∧
    r.body ∉ queriedBodies ∧
    verifyWalMac macFn macKey r = true

/-- **Constructive Authentication Split (`verifyWalMac_authentic_or_macForgery`, `0 choice-free`)**:
    Branching via `DecidableEq WalRecordBody`, any well-formed `WalRecord` passing `verifyWalMac`
    either belongs to `honestBodies` OR constructively witnesses `MacForgery`! -/
theorem verifyWalMac_authentic_or_macForgery
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {honestBodies : List WalRecordBody} {r : WalRecord}
    (hWf : r.WellFormed) (hVer : verifyWalMac macFn macKey r = true) :
    r.body ∈ honestBodies ∨ MacForgery macFn macKey honestBodies r := by
  by_cases hMem : r.body ∈ honestBodies
  · exact Or.inl hMem
  · exact Or.inr ⟨hWf, hMem, hVer⟩

#export_eqns assocInsert
#export_eqns assocErase
#export_eqns computeWalMac
#export_eqns verifyWalMac

#export_eqns MacForgery encodeU64BeNat decodeU64BeNat

theorem nodup_snoc {α : Type} {xs : List α} {x : α}
    (hNodup : xs.Nodup) (hFresh : ∀ y ∈ xs, y ≠ x) :
    (xs ++ [x]).Nodup := by
  induction xs with
  | nil =>
    simp [List.Nodup]
  | cons a rest ih =>
    rw [List.cons_append, List.Nodup, List.pairwise_cons] at *
    refine ⟨?_, ih hNodup.2 (fun y hy => hFresh y (by simp [hy]))⟩
    intro y hy
    rcases List.mem_append.mp hy with hInRest | hInSing
    · exact hNodup.1 y hInRest
    · simp only [List.mem_singleton] at hInSing
      subst hInSing
      exact hFresh a (by simp)

end Qsag
end
