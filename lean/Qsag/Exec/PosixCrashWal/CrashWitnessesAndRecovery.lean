module

public import Qsag.Exec.PosixCrashWal.CeremonyJournal
public import Qsag.Exec.PosixCrashWal.CustodyCrashSafety
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ## 6. Hardware / POSIX `#tooth` Mutation Witnesses & Concrete Multi-Crash Trace Witness -/

/-- Constructive bounded key-digest accumulator for concrete protocol witnesses (`choice-free`). -/
def insecureTestMacKeyDigest64 (key : List UInt8) : Nat :=
  (key.length % 64) + 64 * key.foldl (fun (h : Nat) b => (h * 3 + b.toNat + 1) % 16) 5

/-- INSECURE test authenticator: 32 output bytes, at most 16^4 message tags per key.
    Used only for executable storage counterexamples; never a cryptographic instantiation. -/
def insecureTestKeyedMac256 (key msg : List UInt8) : List UInt8 :=
  let k0 : Nat := insecureTestMacKeyDigest64 key
  let m0 : Nat := msg.foldl (fun (h : Nat) b => (h * 3 + b.toNat + 1) % 16) 3
  let m1 : Nat := msg.foldl (fun (h : Nat) b => (h * 5 + b.toNat + 3) % 16) 7
  let m2 : Nat := msg.foldl (fun (h : Nat) b => (h * 7 + b.toNat + 5) % 16) 11
  let m3 : Nat := msg.foldl (fun (h : Nat) b => (h * 11 + b.toNat + 7) % 16) 13
  encodeU64BeNat (k0 + 1088 * m0) ++
  encodeU64BeNat (k0 + 1088 * m1 + 1) ++
  encodeU64BeNat (k0 + 1088 * m2 + 2) ++
  encodeU64BeNat (k0 + 1088 * m3 + 3)

theorem insecureTestKeyedMac256_wellFormed : WellFormedMacFn insecureTestKeyedMac256 := by
  intro key msg
  unfold insecureTestKeyedMac256
  simp [encodeU64BeNat_length]

/-- `#tooth`: the test authenticator is not collision resistant. For every key two different
    one-byte messages share a tag, so it witnesses tag width and rogue-key separation only. -/
theorem tooth_insecureTestKeyedMac256_collides (key : List UInt8) :
    insecureTestKeyedMac256 key [0] = insecureTestKeyedMac256 key [16] ∧
    ([0] : List UInt8) ≠ [16] :=
  ⟨rfl, by decide⟩

/-- Concrete 32-byte secret MAC key used in hardware/POSIX `#tooth` & trace witnesses. -/
def concreteVaultMacKey : List UInt8 :=
  List.replicate 32 0xA5

/-- Concrete 32-byte enrolled `vaultKeyId`. -/
def concreteVaultKeyId : List UInt8 :=
  List.replicate 32 0x11

/-- Concrete 32-byte `genesisNonce`. -/
def concreteGenesisNonce : List UInt8 :=
  List.replicate 32 0x22

private theorem foldl_mod_16_lt (bs : List UInt8) (step : Nat → UInt8 → Nat) (init : Nat)
    (hInit : init < 16) (hStep : ∀ h b, step h b < 16) :
    bs.foldl step init < 16 := by
  induction bs generalizing init with
  | nil => exact hInit
  | cons b rest ih => exact ih (step init b) (hStep init b)

/-- Constructive proof that `insecureTestKeyedMac256` under `concreteVaultMacKey` universally rejects
    any rogue record authenticated under the untrusted empty key `[]`! -/
theorem insecureTestKeyedMac256_rogueReject (b : WalRecordBody) :
    verifyWalMac insecureTestKeyedMac256 concreteVaultMacKey
      (signWalRecord insecureTestKeyedMac256 [] b) = false := by
  rw [verifyWalMac.public_eq_1]
  unfold signWalRecord
  simp only [computeWalMac.public_eq_1]
  cases hBeq : (insecureTestKeyedMac256 [] (encodeWalBody b) ==
                insecureTestKeyedMac256 concreteVaultMacKey (encodeWalBody b))
  · rfl
  · exfalso
    have hEq := eq_of_beq hBeq
    unfold insecureTestKeyedMac256 at hEq
    dsimp only at hEq
    have hTake := congrArg (List.take 8) hEq
    rw [List.append_assoc, List.append_assoc,
        take_append_of_len_eq (encodeU64BeNat_length _),
        List.append_assoc, List.append_assoc,
        take_append_of_len_eq (encodeU64BeNat_length _)] at hTake
    let m0 : Nat := (encodeWalBody b).foldl (fun (h : Nat) x => (h * 3 + x.toNat + 1) % 16) 3
    have hm0Lt : m0 < 16 :=
      foldl_mod_16_lt (encodeWalBody b) (fun (h : Nat) x => (h * 3 + x.toNat + 1) % 16) 3
        (by decide) (fun _ _ => Nat.mod_lt _ (by decide))
    have hkEmptyLt : insecureTestMacKeyDigest64 [] < 1088 := by
      unfold insecureTestMacKeyDigest64; decide
    have hkKeyLt : insecureTestMacKeyDigest64 concreteVaultMacKey < 1088 := by
      unfold insecureTestMacKeyDigest64
      have hf := foldl_mod_16_lt concreteVaultMacKey (fun (h : Nat) x => (h * 3 + x.toNat + 1) % 16) 5
        (by decide) (fun _ _ => Nat.mod_lt _ (by decide))
      have hl : concreteVaultMacKey.length % 64 < 64 := Nat.mod_lt _ (by decide)
      omega
    have hPow64 : 18496 < 2 ^ 64 := by
      have h18 : 18496 < 65536 := by decide
      have h32 : 65536 < 2 ^ 32 := by
        have hp : 2 ^ 32 = 65536 * 65536 := by decide
        omega
      exact Nat.lt_trans h18 (Nat.lt_trans h32
        two_pow_32_lt_two_pow_64)
    have hLtA : insecureTestMacKeyDigest64 [] + 1088 * m0 < 2 ^ 64 := by omega
    have hLtB : insecureTestMacKeyDigest64 concreteVaultMacKey + 1088 * m0 < 2 ^ 64 := by omega
    have hNatEq := encodeU64BeNat_injective hLtA hLtB hTake
    have hKeyEq : insecureTestMacKeyDigest64 [] = insecureTestMacKeyDigest64 concreteVaultMacKey := by omega
    have hModA : insecureTestMacKeyDigest64 [] % 64 = 0 := by unfold insecureTestMacKeyDigest64; decide
    have hModB : insecureTestMacKeyDigest64 concreteVaultMacKey % 64 = 32 := by
      unfold insecureTestMacKeyDigest64 concreteVaultMacKey
      rw [List.length_replicate]
      omega
    have hModEq := congrArg (· % 64) hKeyEq
    rw [hModA, hModB] at hModEq
    cases hModEq

private theorem openExisting_ok_of_steps
    {st s1 s2 s3 : PosixFsState} {pid : Pid} {basePath : DirName}
    {vkId : List UInt8} {macFn : KeyedMacFn} {macKey : List UInt8}
    {lockFd recFd : FdId} {lockDescId : OpenDescriptionId} {lockIno : InodeId}
    {rawLock rawRec : List UInt8} {ls : LockSidecarSeal} {rec : WalRecord}
    (hSeal : decodeLockSidecar rawLock = some ls)
    (hRec : decodeWalRecord rawRec = some rec)
    (h1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true = .ok (s1, lockFd))
    (h2 : posixFlockExNb s1 pid lockFd = .ok s2)
    (h3 : posixFstatDescAndInode s2 pid lockFd = .ok (lockDescId, lockIno))
    (h4 : posixPreadAll s2 pid lockFd = .ok rawLock)
    (h6 : ls.sealedLockInode = lockIno)
    (h7 : posixOpenExistingNoFollow s2 pid basePath false = .ok (s3, recFd))
    (h8 : posixPreadAll s3 pid recFd = .ok rawRec)
    (h10 : rec.body.lockGenesisId = computeLockGenesisId lockIno ls.genesisNonce)
    (h11 : rec.body.vaultKeyId = vkId)
    (h12 : verifyWalMac macFn macKey rec = true) :
    (openExisting st pid basePath vkId macFn macKey).2 =
      .ok ({ pid := pid
             basePath := basePath
             lockFd := lockFd
             lockDescId := lockDescId
             lockInode := lockIno
             lockGenesisId := computeLockGenesisId lockIno ls.genesisNonce
             vaultKeyId := vkId
             ioPoisoned := false }, rec) := by
  rw [openExisting.public_eq_1]
  rw [h1]; dsimp only
  rw [h2]; dsimp only
  rw [h3, h4]; dsimp only
  rw [hSeal]; dsimp only
  rw [h6]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [h7]; dsimp only
  rw [h8]; dsimp only
  rw [hRec]; dsimp only
  rw [h10]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [h11, h12]
  simp only [bne_self_eq_false, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

/-- **#tooth 3 (`tooth_missing_parent_dir_sync_loses_genesis_after_power_loss`)**:
    Demonstrates why `posixSyncAllMedia` on `.lock` and `concreteBasePath` alone is insufficient
    during `provisionGenesis` without `posixSyncParentDir`:
    before power loss `openExisting` succeeds, but `PowerLossCrash .revertToNand` wipes the
    unsynced parent directory entries so `openExisting` fails with `.error .enoent`! -/
theorem tooth_missing_parent_dir_sync_loses_genesis_after_power_loss :
    let lockPath := walLockPath concreteBasePath
    let sealBytes := encodeLockSidecar { sealedLockInode := 1, genesisNonce := concreteGenesisNonce }
    let rec0 := signWalRecord insecureTestKeyedMac256 concreteVaultMacKey
      { vaultKeyId := concreteVaultKeyId
        lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce
        epoch := 0
        payload := [] }
    ∃ s1 s2 s3 s4 s5 s6 s7 s8 sNoDirSync hLive,
      posixCreateExclNoFollow PosixFsState.empty 1 lockPath = .ok (s1, 3, 1) ∧
      posixFlockExNb s1 1 3 = .ok s2 ∧
      posixPwriteAll s2 1 3 sealBytes = .ok s3 ∧
      posixSyncAllMedia s3 1 3 false = (s4, .ok ()) ∧
      posixCreateExclNoFollow s4 1 concreteBasePath = .ok (s5, 4, 2) ∧
      posixPwriteAll s5 1 4 (encodeWalRecord rec0) = .ok s6 ∧
      posixSyncAllMedia s6 1 4 false = (s7, .ok ()) ∧
      posixCloseFd s7 1 4 = .ok s8 ∧
      posixCloseFd s8 1 3 = .ok sNoDirSync ∧
      -- Before power loss, `openExisting` succeeds and reads `rec0`:
      (openExisting sNoDirSync 2 concreteBasePath concreteVaultKeyId
        insecureTestKeyedMac256 concreteVaultMacKey).2 = .ok (hLive, rec0) ∧
      -- After `PowerLossCrash .revertToNand`, unsynced dentries vanish and `openExisting` returns `.enoent`:
      let sCrashed :=
        PowerLossCrash .revertToNand (fun _ => SectorTearMask.dropAllVolatile) sNoDirSync
      assocLookup sCrashed.kernel.dirInode.unsyncedEntries concreteBasePath = none ∧
      openExisting sCrashed 2 concreteBasePath concreteVaultKeyId
        insecureTestKeyedMac256 concreteVaultMacKey = (sCrashed, .error .enoent) := by
  have h1Lt64 : (1 : InodeId) < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192))
      two_pow_32_lt_two_pow_64
  have hSealWf : ({ sealedLockInode := 1, genesisNonce := concreteGenesisNonce } : LockSidecarSeal).WellFormed :=
    ⟨h1Lt64, by decide⟩
  have hBodyWf :
      ({ vaultKeyId := concreteVaultKeyId
         lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce
         epoch := 0
         payload := [] } : WalRecordBody).WellFormed :=
    ⟨by decide,
     computeLockGenesisId_length (by decide),
     Nat.pow_pos (by decide : 0 < 2),
     Nat.pow_pos (by decide : 0 < 2)⟩
  have hRecWf := signWalRecord_wellFormed insecureTestKeyedMac256_wellFormed concreteVaultMacKey hBodyWf
  have hSealDec := decodeLockSidecar_encodeLockSidecar hSealWf
  have hRecDec := decodeWalRecord_encodeWalRecord hRecWf
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, live, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      ⟨_, _, _, hOpen, hLock, hStat, hReadSeal, hOpenRecord, hReadRecord⟩, hMissing, hOpenMissing⟩ :=
    unsyncedGenesis_file_operations
      (encodeLockSidecar { sealedLockInode := 1, genesisNonce := concreteGenesisNonce })
      (encodeWalRecord (signWalRecord insecureTestKeyedMac256 concreteVaultMacKey
        { vaultKeyId := concreteVaultKeyId, lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
          epoch := 0, payload := [] }))
  refine ⟨s1, s2, s3, s4, s5, s6, s7, s8, live,
    { pid := 2, basePath := concreteBasePath, lockFd := 5, lockDescId := 3, lockInode := 1,
      lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
      vaultKeyId := concreteVaultKeyId, ioPoisoned := false }, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    ?_, hMissing, ?_⟩
  · exact openExisting_ok_of_steps hSealDec hRecDec hOpen hLock hStat hReadSeal rfl
      hOpenRecord hReadRecord rfl rfl (verifyWalMac_signWalRecord _ _ _)
  · rw [openExisting.public_eq_1, hOpenMissing]

/-- Buggy sign-with-fallback helper that treats `.enoent` (missing WAL) as "uninitialized" and
    re-provisions a fresh epoch-`0` genesis WAL instead of fail-stopping! -/
def buggySignTreatingMissingWalAsFresh (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (keyKind : StatefulKeyKind) (vaultKeyId genesisNonce : List UInt8) (maxEpochCap : Nat)
    (msg : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8) :
    PosixFsState × Option SignedEpochReceipt :=
  match openExisting st pid basePath vaultKeyId macFn macKey with
  | (_, .ok _) =>
    execReserveBeforeSignAtomic st pid basePath keyKind vaultKeyId maxEpochCap msg macFn macKey {}
  | (stAfterOpen, .error .enoent) =>
    let initPay := encodeCustodyWalPayload keyKind maxEpochCap []
    match provisionGenesis stAfterOpen pid basePath vaultKeyId genesisNonce initPay macFn macKey {} with
    | (stErr, .error _) => (stErr, none)
    | (stReinit, .ok _) =>
      execReserveBeforeSignAtomic (KernelPanicCrash stReinit) pid basePath keyKind
        vaultKeyId maxEpochCap msg macFn macKey {}
  | (stErr, .error _) => (stErr, none)

private theorem replaceAtomic_nextInode_le
    (st : PosixFsState) (h : LockedVaultHandle) (ep : Nat) (pay : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8) (faults : IoFaultSchedule) :
    (replaceAtomic st h ep pay macFn macKey faults).1.nand.nextInode ≤ st.nand.nextInode + 1 := by
  rw [replaceAtomic.public_eq_1]
  by_cases h1 : h.ioPoisoned = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!(decide (ep < 2 ^ 64)) || !(decide (pay.length < 2 ^ 32))) = true
    · simp [h2]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none => simp
      | some dp =>
        rcases dp with ⟨dId, lDesc⟩
        dsimp only
        by_cases h3 : (dId != h.lockDescId || lDesc.inode != h.lockInode || lDesc.stickyFsyncErr ||
            st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp [h3]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          let stClean := posixUnlinkIfPresent st (walTmpPath h.basePath)
          let newRec := signWalRecord macFn macKey
            { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId, epoch := ep, payload := pay }
          cases hCr : posixCreateExclNoFollow stClean h.pid (walTmpPath h.basePath) with
          | error _ =>
            dsimp +zetaDelta only
            simp [posixUnlinkIfPresent]
          | ok pCr =>
            rcases pCr with ⟨stCr, tmpFd, tmpIno⟩
            have hCrNext : stCr.nand.nextInode = st.nand.nextInode + 1 := by
              rw [posixCreateExclNoFollow.public_eq_1] at hCr
              cases hL : assocLookup stClean.kernel.dirInode.unsyncedEntries (walTmpPath h.basePath) with
              | some _ => rw [hL] at hCr; cases hCr
              | none =>
                rw [hL] at hCr
                injection hCr with hP
                rcases Prod.mk.inj hP with ⟨hStCr, _⟩
                rw [← hStCr]
                rfl
            dsimp +zetaDelta only
            cases hWr : posixPwriteAll stCr h.pid tmpFd (encodeWalRecord newRec) with
            | error _ =>
              have hc := posixCloseFd_preserves_storage stCr h.pid tmpFd
              dsimp +zetaDelta only
              rw [hc.2.2.2, hCrNext]; exact Nat.le_refl _
            | ok stWr =>
              have hWrNand : stWr.nand.nextInode = st.nand.nextInode + 1 := by
                rw [posixPwriteAll.public_eq_1] at hWr
                cases hRO : resolveOpenFd stCr.kernel.openFds h.pid tmpFd with
                | none => rw [hRO] at hWr; cases hWr
                | some dp2 =>
                  rcases dp2 with ⟨_, d2⟩
                  rw [hRO] at hWr; dsimp only at hWr
                  by_cases hw1 : (!d2.writable) = true
                  · simp [hw1] at hWr
                  · simp only [hw1, Bool.false_eq_true, ↓reduceIte] at hWr
                    by_cases hw2 : d2.stickyFsyncErr = true
                    · simp [hw2] at hWr
                    · simp only [hw2, Bool.false_eq_true, ↓reduceIte] at hWr
                      injection hWr with eW; rw [← eW]; exact hCrNext
              dsimp +zetaDelta only
              cases hSy : posixSyncAllMedia stWr h.pid tmpFd faults.failRecordSync with
              | mk stSy syRes =>
                have hSyNand : stSy.nand.nextInode = stWr.nand.nextInode := by
                  rw [posixSyncAllMedia.public_eq_1] at hSy
                  cases hRO2 : resolveOpenFd stWr.kernel.openFds h.pid tmpFd with
                  | none => rw [hRO2] at hSy; injection hSy with eS _; rw [← eS]
                  | some dp3 =>
                    rcases dp3 with ⟨_, d3⟩
                    rw [hRO2] at hSy; dsimp only at hSy
                    by_cases hs1 : d3.stickyFsyncErr = true
                    · simp only [hs1, ↓reduceIte] at hSy; injection hSy with eS _; rw [← eS]
                    · simp only [hs1, Bool.false_eq_true, ↓reduceIte] at hSy
                      by_cases hs2 : faults.failRecordSync = true
                      · simp only [hs2, ↓reduceIte] at hSy; injection hSy with eS _; rw [← eS]
                      · simp only [hs2, Bool.false_eq_true, ↓reduceIte] at hSy
                        cases hRI : readInodeHierarchy stWr d3.inode with
                        | none => rw [hRI] at hSy; injection hSy with eS _; rw [← eS]
                        | some _ => rw [hRI] at hSy; injection hSy with eS _; rw [← eS]
                have hcSy := posixCloseFd_preserves_storage stSy h.pid tmpFd
                let stClSy := (posixCloseFd stSy h.pid tmpFd).toOption.getD stSy
                cases syRes with
                | error _ =>
                  dsimp +zetaDelta only
                  rw [hcSy.2.2.2, hSyNand, hWrNand]; exact Nat.le_refl _
                | ok u =>
                  cases u; dsimp +zetaDelta only
                  cases hRn : posixRename stClSy (walTmpPath h.basePath) h.basePath with
                  | error _ =>
                    dsimp +zetaDelta only
                    rw [hcSy.2.2.2, hSyNand, hWrNand]; exact Nat.le_refl _
                  | ok stRn =>
                    have hRnNand : stRn.nand = stClSy.nand := by
                      rw [posixRename.public_eq_1] at hRn
                      cases hLA : assocLookup stClSy.kernel.dirInode.unsyncedEntries (walTmpPath h.basePath) with
                      | none => rw [hLA] at hRn; cases hRn
                      | some _ => rw [hLA] at hRn; injection hRn with eR; rw [← eR]
                    dsimp +zetaDelta only
                    rw [posixSyncParentDir.public_eq_1]
                    cases faults.failParentSync with
                    | true =>
                      simp only [↓reduceIte]
                      rw [hRnNand]
                      dsimp +zetaDelta only [stClSy]
                      rw [hcSy.2.2.2, hSyNand, hWrNand]
                      exact Nat.le_refl _
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      rw [hRnNand]
                      dsimp +zetaDelta only [stClSy]
                      rw [hcSy.2.2.2, hSyNand, hWrNand]
                      exact Nat.le_refl _

/-- **#tooth 5 (`tooth_missing_wal_treated_as_fresh_causes_epoch_zero_amnesia`)**:
    Proves that if a vault already provisioned and used to sign `msg₁ = [0x01]` at `epoch = 0`
    has its WAL files deleted (`posixUnlinkIfPresent` + directory sync), then:
    1. Hardened `execReserveBeforeSignAtomic` **fail-stops** (`(_, none)`), whereas
    2. `buggySignTreatingMissingWalAsFresh` re-provisions a fresh genesis WAL and signs a
       **distinct** message `msg₂ = [0x02]` (`msg₁ ≠ msg₂`) at **`epoch = 0`** (two-time epoch-`0`
       signature collision / amnesia)! -/
theorem tooth_missing_wal_treated_as_fresh_causes_epoch_zero_amnesia :
    let msg₁ : List UInt8 := [0x01]
    let msg₂ : List UInt8 := [0x02]
    let initPay := encodeCustodyWalPayload .beltLatch 100 []
    ∃ fs0 rec0 fsAfter1 rcpt₁ fsBuggy rcpt₂,
      provisionGenesis PosixFsState.empty 1 concreteBasePath
        concreteVaultKeyId concreteGenesisNonce initPay
        insecureTestKeyedMac256 concreteVaultMacKey {} = (fs0, .ok (1, rec0)) ∧
      execReserveBeforeSignAtomic (KernelPanicCrash fs0) 1 concreteBasePath .beltLatch
        concreteVaultKeyId 100 msg₁ insecureTestKeyedMac256 concreteVaultMacKey {} =
        (fsAfter1, some rcpt₁) ∧
      let sDel := posixUnlinkIfPresent
                    (posixUnlinkIfPresent fsAfter1 concreteBasePath)
                    (walLockPath concreteBasePath)
      let sMissingWal := KernelPanicCrash (posixSyncParentDir sDel false).1
      -- Hardened protocol refuses when WAL is missing:
      execReserveBeforeSignAtomic sMissingWal 1 concreteBasePath .beltLatch
        concreteVaultKeyId 100 msg₂ insecureTestKeyedMac256 concreteVaultMacKey {} =
        (sMissingWal, none) ∧
      -- Buggy `.enoent -> provisionGenesis` fallback resets to `epoch = 0` on `msg₂ ≠ msg₁`!
      buggySignTreatingMissingWalAsFresh sMissingWal 1 concreteBasePath .beltLatch
        concreteVaultKeyId concreteGenesisNonce 100 msg₂
        insecureTestKeyedMac256 concreteVaultMacKey = (fsBuggy, some rcpt₂) ∧
      rcpt₁.epoch = 0 ∧
      rcpt₂.epoch = 0 ∧
      rcpt₁.msg ≠ rcpt₂.msg := by
  let msg₁ : List UInt8 := [0x01]
  let msg₂ : List UInt8 := [0x02]
  let initPay := encodeCustodyWalPayload .beltLatch 100 []
  have hPay32 : initPay.length < 2 ^ 32 := encodeCustodyWalPayload_lt_two_pow_32 .beltLatch 100 []
  have h1Lt64 : (1 : InodeId) < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192))
      two_pow_32_lt_two_pow_64
  obtain ⟨fs0, hGen0, hNextFs0, hDur0⟩ :=
    provisionGenesis_rebooted_succeeds PosixFsState.empty 1 concreteBasePath
      concreteVaultKeyId concreteGenesisNonce initPay
      insecureTestKeyedMac256 insecureTestKeyedMac256_wellFormed concreteVaultMacKey
      rfl rfl rfl rfl rfl rfl h1Lt64 (by decide) (by decide) hPay32
  let rec0 := signWalRecord insecureTestKeyedMac256 concreteVaultMacKey
    { vaultKeyId := concreteVaultKeyId
      lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce
      epoch := 0
      payload := initPay }
  have hDurClean0 : VaultDurableAt (KernelPanicCrash fs0) concreteBasePath 1
      concreteGenesisNonce insecureTestKeyedMac256 concreteVaultMacKey rec0 :=
    vaultDurableAt_after_crash hDur0 (CrashStep.kernelPanic fs0)
  obtain ⟨fsAfter1, hSign1⟩ :=
    honest_sign_complete_when_healthy (rec := rec0) 1 .beltLatch 100 msg₁
      rfl rfl hDurClean0 (by decide) h1Lt64
  have hAfter1NextLe : fsAfter1.nand.nextInode ≤ 4 := by
    have hUnf := hSign1
    dsimp only [rec0, signWalRecord] at hUnf
    unfold execReserveBeforeSignAtomic at hUnf
    cases hOpA : openExisting (KernelPanicCrash fs0) 1 concreteBasePath concreteVaultKeyId
        insecureTestKeyedMac256 concreteVaultMacKey with
    | mk sO rO =>
      rw [hOpA] at hUnf
      cases rO with
      | error _ => cases (Prod.mk.inj hUnf).2
      | ok pO =>
        rcases pO with ⟨vhO, rRead⟩
        obtain ⟨_, _, _, _, hDurO⟩ := openExisting_ok_of_vaultDurableAt hDurClean0 hOpA
        have hSafeK0 : EntryWatermarkSafe (KernelPanicCrash fs0) concreteVaultKeyId
            insecureTestKeyedMac256 concreteVaultMacKey 0
            (assocLookup (KernelPanicCrash fs0).kernel.dirInode.unsyncedEntries concreteBasePath) := by
          rcases hDurClean0 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, rI, hRI, hRU, _, hRP, hRD, hRN⟩
          rw [hRU]
          simp only [EntryWatermarkSafe.public_eqs]
          exact ⟨hRI, hRP, hRD, _, hRN, fun _ _ _ _ => Nat.zero_le _⟩
        have hOpenNand : sO.nand = (KernelPanicCrash fs0).nand :=
          (openExisting_preserves_storage_and_bounds_epoch hSafeK0 hOpA).2.2.2.1
        dsimp +zetaDelta only at hUnf
        by_cases hc : (!(decide (rRead.body.epoch < 100)) || !(decide (rRead.body.epoch + 1 < 2 ^ 64))) = true
        · simp [hc] at hUnf
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hUnf
          have hLeRep := replaceAtomic_nextInode_le sO vhO (rRead.body.epoch + 1)
            (encodeCustodyWalPayload .beltLatch 100 msg₁)
            insecureTestKeyedMac256 concreteVaultMacKey {}
          cases hRepA : replaceAtomic sO vhO (rRead.body.epoch + 1)
              (encodeCustodyWalPayload .beltLatch 100 msg₁)
              insecureTestKeyedMac256 concreteVaultMacKey {} with
          | mk sR restR =>
            rcases restR with ⟨hR, resR⟩
            rw [hRepA] at hUnf hLeRep
            dsimp only at hLeRep
            cases resR with
            | error _ => cases (Prod.mk.inj hUnf).2
            | ok _ =>
              dsimp +zetaDelta only at hUnf
              have hcR := posixCloseFd_preserves_storage sR hR.pid hR.lockFd
              rcases Prod.mk.inj hUnf with ⟨eFsA, _⟩
              dsimp only [closeVaultHandle] at eFsA
              rw [← eFsA, hcR.2.2.2]
              have hS0Next : sO.nand.nextInode = 3 := by
                rw [hOpenNand]
                change fs0.nand.nextInode = 3
                rw [hNextFs0]; rfl
              rw [hS0Next] at hLeRep
              exact hLeRep
  let sDel := posixUnlinkIfPresent
                (posixUnlinkIfPresent fsAfter1 concreteBasePath)
                (walLockPath concreteBasePath)
  let sMissingWal := KernelPanicCrash (posixSyncParentDir sDel false).1
  have hNeLock : concreteBasePath ≠ walLockPath concreteBasePath :=
    fun he => walLockPath_ne_base concreteBasePath he.symm
  have hMissBaseNone : assocLookup sMissingWal.kernel.dirInode.unsyncedEntries concreteBasePath = none := by
    simp [sMissingWal, KernelPanicCrash, posixSyncParentDir.public_eqs, sDel, posixUnlinkIfPresent, hNeLock]
  have hMissLockNone : assocLookup sMissingWal.kernel.dirInode.unsyncedEntries (walLockPath concreteBasePath) = none := by
    simp [sMissingWal, KernelPanicCrash, posixSyncParentDir.public_eqs, sDel, posixUnlinkIfPresent]
  have hOpenMiss :
      openExisting sMissingWal 1 concreteBasePath concreteVaultKeyId
        insecureTestKeyedMac256 concreteVaultMacKey = (sMissingWal, .error .enoent) := by
    rw [openExisting.public_eq_1]
    rw [posixOpenExistingNoFollow.public_eq_1]
    rw [resolveDentryNoFollow.public_eq_1]
    rw [hMissLockNone]
  have hHardenedStop :
      execReserveBeforeSignAtomic sMissingWal 1 concreteBasePath .beltLatch
        concreteVaultKeyId 100 msg₂ insecureTestKeyedMac256 concreteVaultMacKey {} =
        (sMissingWal, none) := by
    unfold execReserveBeforeSignAtomic
    rw [hOpenMiss]
  have hMissNext64 : sMissingWal.nand.nextInode < 2 ^ 64 := by
    change fsAfter1.nand.nextInode < 2 ^ 64
    exact Nat.lt_trans
      (lt_two_pow_32_of_le_8192 (Nat.le_trans hAfter1NextLe (by decide : 4 ≤ 8192)))
      two_pow_32_lt_two_pow_64
  obtain ⟨stReinit, hGenReinit, _, hDurReinit⟩ :=
    provisionGenesis_rebooted_succeeds sMissingWal 1 concreteBasePath
      concreteVaultKeyId concreteGenesisNonce initPay
      insecureTestKeyedMac256 insecureTestKeyedMac256_wellFormed concreteVaultMacKey
      rfl rfl rfl rfl hMissBaseNone hMissLockNone hMissNext64 (by decide) (by decide) hPay32
  have hDurReinitClean :=
    vaultDurableAt_after_crash hDurReinit (CrashStep.kernelPanic stReinit)
  obtain ⟨fsBuggy, hSignBuggy⟩ :=
    honest_sign_complete_when_healthy 1 .beltLatch 100 msg₂
      rfl rfl hDurReinitClean (by dsimp [signWalRecord]; decide) h1Lt64
  have hBuggyRun :
      buggySignTreatingMissingWalAsFresh sMissingWal 1 concreteBasePath .beltLatch
        concreteVaultKeyId concreteGenesisNonce 100 msg₂
        insecureTestKeyedMac256 concreteVaultMacKey =
      (fsBuggy, some { keyKind := .beltLatch
                       vaultKeyId := concreteVaultKeyId
                       epoch := 0
                       msg := msg₂ }) := by
    unfold buggySignTreatingMissingWalAsFresh
    rw [hOpenMiss]
    dsimp +zetaDelta only
    rw [hGenReinit]
    dsimp +zetaDelta only
    exact hSignBuggy
  exact ⟨fs0, rec0, fsAfter1, _, fsBuggy, _,
    hGen0, hSign1, hHardenedStop, hBuggyRun, rfl, rfl, by decide⟩

/-- **Non-Vacuous End-to-End Multi-Crash Witness (`inhabited_posix_crash_wal_trace`)**:
    Constructively inhabits **both** `initProvisionedCustodyState` (instantiating
    `reserve_before_sign_multi_crash_epoch_uniqueness` across a concrete multi-crash + adversarial
    trace that emits 2 distinct signed receipts at epochs `0` and `1` and survives `KernelPanicCrash`,
    `PowerLossCrash`, `.lock` unlink + spoofed recreation, rogue genesis re-provisioning, and
    contender attacks) **and** `initProvisionedCeremonyState` (instantiating
    `ceremony_journal_released_implies_all_reservations_durable_and_no_reuse`)! -/
theorem inhabited_posix_crash_wal_trace :
    ∃ (s₀ : MultiCrashCustodyState) (c₀ : CeremonyCrashState),
      initProvisionedCustodyState 1 concreteBasePath .beltLatch
        concreteVaultKeyId concreteGenesisNonce 1024
        insecureTestKeyedMac256 concreteVaultMacKey = some s₀ ∧
      initProvisionedCeremonyState 1 concreteBasePath
        concreteVaultKeyId concreteGenesisNonce 1000
        insecureTestKeyedMac256 concreteVaultMacKey = some c₀ ∧
      let prefixTrace : List MultiCrashWalEvent :=
        [.kernelPanic,
         .signAtomic 1 [0xAA] {},
         .powerLoss .revertToNand SectorTearMask.dropAllVolatile [],
         .signAtomic 1 [0xBB] {},
         .kernelPanic]
      let suffixTrace : List MultiCrashWalEvent :=
        [.unlinkLockSidecar,
         .recreateSpoofLock 99 [0xDE, 0xAD],
         .attemptReprovisionGenesis 99 (List.replicate 32 0x99),
         .contenderSignAttempt 2 [0xFF],
         .deleteWalRecord]
      let sMid := runMultiCrashCustodyTrace insecureTestKeyedMac256 concreteVaultMacKey s₀ prefixTrace
      let sFinal := runMultiCrashCustodyTrace insecureTestKeyedMac256 concreteVaultMacKey s₀
                      (prefixTrace ++ suffixTrace)
      sMid.emittedReceipts.length = 2 ∧
      (∃ r₀ ∈ sMid.emittedReceipts, r₀.epoch = 0 ∧ r₀.msg = [0xAA]) ∧
      (∃ r₁ ∈ sMid.emittedReceipts, r₁.epoch = 1 ∧ r₁.msg = [0xBB]) ∧
      (sFinal.emittedReceipts.map (·.epoch)).Nodup ∧
      2 ≤ sFinal.ghostWatermark ∧
      (let cTrace : List CeremonyCrashEvent :=
         [.kernelPanic,
          .reserveAndEmitRound1 1 (List.replicate 32 0x33) [0xCA, 0xFE] 25 (List.replicate 32 0x44) {},
          .releaseSignatureFromRound1 1 [0x55, 0x66] {},
          .powerLoss .revertToNand SectorTearMask.dropAllVolatile []]
       let cFinal := runCeremonyCrashTrace insecureTestKeyedMac256 concreteVaultMacKey c₀ cTrace
       ∃ fsRecovered rec j views,
         CrashRecoverCeremony (KernelPanicCrash cFinal.fs) 2 cFinal.basePath cFinal.vaultKeyId
           insecureTestKeyedMac256 concreteVaultMacKey = (fsRecovered, .ok (rec, j, views)) ∧
         views.policyCumulativeSpend ≤ cFinal.policySpendCap ∧
         (∀ sig ∈ cFinal.releasedSigs, AllRequiredReservationsDurable sig views) ∧
         (∀ pkt ∈ cFinal.emittedRound1Msgs, AllRound1ReservationsDurable pkt views)) := by
  have h1Lt64 : (1 : InodeId) < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192))
      two_pow_32_lt_two_pow_64
  have h2Lt64 : (2 : Nat) < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 2 ≤ 8192))
      two_pow_32_lt_two_pow_64
  -- 1. Provision `s₀` for `MultiCrashCustodyState`:
  let initCustPay := encodeCustodyWalPayload .beltLatch 1024 []
  have hCustPay32 : initCustPay.length < 2 ^ 32 :=
    encodeCustodyWalPayload_lt_two_pow_32 .beltLatch 1024 []
  obtain ⟨fsCust0, hGenCust0, _, hDurCust0⟩ :=
    provisionGenesis_rebooted_succeeds PosixFsState.empty 1 concreteBasePath
      concreteVaultKeyId concreteGenesisNonce initCustPay
      insecureTestKeyedMac256 insecureTestKeyedMac256_wellFormed concreteVaultMacKey
      rfl rfl rfl rfl rfl rfl h1Lt64 (by decide) (by decide) hCustPay32
  let s₀ : MultiCrashCustodyState :=
    { fs := fsCust0
      basePath := concreteBasePath
      keyKind := .beltLatch
      vaultKeyId := concreteVaultKeyId
      enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce
      maxEpochCap := 1024
      activeHold := none
      emittedReceipts := []
      ghostWatermark := 0 }
  have hInitCust :
      initProvisionedCustodyState 1 concreteBasePath .beltLatch
        concreteVaultKeyId concreteGenesisNonce 1024
        insecureTestKeyedMac256 concreteVaultMacKey = some s₀ := by
    unfold initProvisionedCustodyState
    dsimp +zetaDelta only
    rw [hGenCust0]
    rfl
  -- 2. Provision `c₀` for `CeremonyCrashState`:
  let initCerPay := encodeCeremonyJournalRecord ceremonyGenesisJournal
  have hCerPay32 : initCerPay.length < 2 ^ 32 :=
    encodeCeremonyJournalRecord_lt_two_pow_32 ceremonyGenesisJournal_wellFormed
  obtain ⟨fsCer0, hGenCer0, _, _⟩ :=
    provisionGenesis_rebooted_succeeds PosixFsState.empty 1 concreteBasePath
      concreteVaultKeyId concreteGenesisNonce initCerPay
      insecureTestKeyedMac256 insecureTestKeyedMac256_wellFormed concreteVaultMacKey
      rfl rfl rfl rfl rfl rfl h1Lt64 (by decide) (by decide) hCerPay32
  let c₀ : CeremonyCrashState :=
    { fs := fsCer0
      basePath := concreteBasePath
      vaultKeyId := concreteVaultKeyId
      policySpendCap := 1000
      emittedRound1Msgs := []
      releasedSigs := []
      pendingRound1Lease := none }
  have hInitCer :
      initProvisionedCeremonyState 1 concreteBasePath
        concreteVaultKeyId concreteGenesisNonce 1000
        insecureTestKeyedMac256 concreteVaultMacKey = some c₀ := by
    unfold initProvisionedCeremonyState
    dsimp +zetaDelta only
    rw [hGenCer0]
  -- 3. Step through `prefixTrace` using `honest_sign_complete_when_healthy` & `replaceAtomic_ok_durable`:
  have hDurK0 := vaultDurableAt_after_crash hDurCust0 (CrashStep.kernelPanic fsCust0)
  obtain ⟨fsAfterA, hExecA⟩ :=
    honest_sign_complete_when_healthy 1 .beltLatch 1024 [0xAA]
      rfl rfl hDurK0 (by decide) h1Lt64
  -- Note `stepMultiCrashCustody` on `.signAtomic` computes the exact same `(fs, some rcpt)` as `execReserveBeforeSignAtomic`!
  have hStepSignEq : ∀ (stX : PosixFsState) (msgX : List UInt8) (stY : PosixFsState) (rcptX : SignedEpochReceipt)
      (emX : List SignedEpochReceipt) (wmX : Nat),
      execReserveBeforeSignAtomic stX 1 concreteBasePath .beltLatch concreteVaultKeyId 1024
        msgX insecureTestKeyedMac256 concreteVaultMacKey {} = (stY, some rcptX) →
      (stepMultiCrashCustody insecureTestKeyedMac256 concreteVaultMacKey
        { fs := stX, basePath := concreteBasePath, keyKind := .beltLatch,
          vaultKeyId := concreteVaultKeyId,
          enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
          maxEpochCap := 1024, activeHold := none,
          emittedReceipts := emX, ghostWatermark := wmX }
        (.signAtomic 1 msgX {})).1 =
      { fs := stY, basePath := concreteBasePath, keyKind := .beltLatch,
        vaultKeyId := concreteVaultKeyId,
        enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
        maxEpochCap := 1024, activeHold := none,
        emittedReceipts := emX ++ [rcptX], ghostWatermark := rcptX.epoch + 1 } := by
    intro stX msgX stY rcptX emX wmX hEx
    unfold execReserveBeforeSignAtomic at hEx
    simp only [stepMultiCrashCustody.public_eqs]
    cases hO : openExisting stX 1 concreteBasePath concreteVaultKeyId insecureTestKeyedMac256 concreteVaultMacKey with
    | mk sO rO =>
      rw [hO] at hEx
      cases rO with
      | error _ => cases (Prod.mk.inj hEx).2
      | ok pO =>
        rcases pO with ⟨vhO, recO⟩
        dsimp +zetaDelta only at hEx ⊢
        by_cases hc : (!(decide (recO.body.epoch < 1024)) || !(decide (recO.body.epoch + 1 < 2 ^ 64))) = true
        · simp [hc] at hEx
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hEx ⊢
          cases hR : replaceAtomic sO vhO (recO.body.epoch + 1)
              (encodeCustodyWalPayload .beltLatch 1024 msgX)
              insecureTestKeyedMac256 concreteVaultMacKey {} with
          | mk sR restR =>
            rcases restR with ⟨hR, resR⟩
            rw [hR] at hEx
            cases resR with
            | error _ => cases (Prod.mk.inj hEx).2
            | ok _ =>
              dsimp +zetaDelta only at hEx ⊢
              rcases Prod.mk.inj hEx with ⟨hStYEq, hSomeEq⟩
              injection hSomeEq with hRcptEq
              rw [← hStYEq, ← hRcptEq]
  -- Also prove `VaultDurableAt` at `epoch = 1` on `fsAfterA`:
  let recCust1 := signWalRecord insecureTestKeyedMac256 concreteVaultMacKey
    { vaultKeyId := concreteVaultKeyId
      lockGenesisId := computeLockGenesisId 1 concreteGenesisNonce
      epoch := 1
      payload := encodeCustodyWalPayload .beltLatch 1024 [0xAA] }
  have hDurAfterA : VaultDurableAt fsAfterA concreteBasePath 1
      concreteGenesisNonce insecureTestKeyedMac256 concreteVaultMacKey recCust1 := by
    have hEx := hExecA
    dsimp only [signWalRecord] at hEx
    unfold execReserveBeforeSignAtomic at hEx
    cases hO : openExisting (KernelPanicCrash fsCust0) 1 concreteBasePath concreteVaultKeyId
        insecureTestKeyedMac256 concreteVaultMacKey with
    | mk sO rO =>
      rw [hO] at hEx
      cases rO with
      | error _ => cases (Prod.mk.inj hEx).2
      | ok pO =>
        rcases pO with ⟨vhO, recO⟩
        obtain ⟨hReadEqO, hBaseO, hVkO, hGidO, hDurO⟩ := openExisting_ok_of_vaultDurableAt hDurK0 hO
        subst recO
        dsimp +zetaDelta only [signWalRecord] at hEx
        have hDec1024 : decide ((0 : Nat) < 1024) = true := by decide
        simp only [hDec1024, h1Lt64, decide_true, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hEx
        cases hR : replaceAtomic sO vhO 1
            (encodeCustodyWalPayload .beltLatch 1024 [0xAA])
            insecureTestKeyedMac256 concreteVaultMacKey {} with
        | mk sR restR =>
          rcases restR with ⟨vhR, resR⟩
          rw [hR] at hEx
          cases resR with
          | error _ => cases (Prod.mk.inj hEx).2
          | ok recCom =>
            dsimp +zetaDelta only at hEx
            have hDurOH := hDurO
            rw [← hBaseO] at hDurOH
            obtain ⟨_, hComEq, hDurR⟩ :=
              replaceAtomic_ok_durable insecureTestKeyedMac256_wellFormed hVkO hGidO hDurOH hR
            rw [hBaseO] at hDurR
            have hComRec1 : recCom = recCust1 := by
              rw [hComEq, hVkO, hGidO]; rfl
            rw [hComRec1] at hDurR
            rcases Prod.mk.inj hEx with ⟨hFsAEq, _⟩
            rw [← hFsAEq]
            exact vaultDurableAt_storage_frame
              (posixCloseFd_preserves_storage sR vhR.pid vhR.lockFd) hDurR
  let fsCrashP := PowerLossCrash .revertToNand
    (evalFiniteTearSchedule SectorTearMask.dropAllVolatile []) fsAfterA
  have hDurP1 : VaultDurableAt fsCrashP concreteBasePath 1
      concreteGenesisNonce insecureTestKeyedMac256 concreteVaultMacKey recCust1 :=
    vaultDurableAt_after_crash hDurAfterA
      (CrashStep.powerLoss .revertToNand
        (evalFiniteTearSchedule SectorTearMask.dropAllVolatile []) fsAfterA)
  obtain ⟨fsAfterB, hExecB⟩ :=
    honest_sign_complete_when_healthy (rec := recCust1) 1 .beltLatch 1024 [0xBB]
      rfl rfl hDurP1 (by decide) h2Lt64
  let prefixTrace : List MultiCrashWalEvent :=
    [.kernelPanic,
     .signAtomic 1 [0xAA] {},
     .powerLoss .revertToNand SectorTearMask.dropAllVolatile [],
     .signAtomic 1 [0xBB] {},
     .kernelPanic]
  let suffixTrace : List MultiCrashWalEvent :=
    [.unlinkLockSidecar,
     .recreateSpoofLock 99 [0xDE, 0xAD],
     .attemptReprovisionGenesis 99 (List.replicate 32 0x99),
     .contenderSignAttempt 2 [0xFF],
     .deleteWalRecord]
  let rcpt₀ : SignedEpochReceipt :=
    { keyKind := .beltLatch, vaultKeyId := concreteVaultKeyId, epoch := 0, msg := [0xAA] }
  let rcpt₁ : SignedEpochReceipt :=
    { keyKind := .beltLatch, vaultKeyId := concreteVaultKeyId, epoch := 1, msg := [0xBB] }
  have hSMidEq :
      runMultiCrashCustodyTrace insecureTestKeyedMac256 concreteVaultMacKey s₀ prefixTrace =
      { fs := KernelPanicCrash fsAfterB
        basePath := concreteBasePath
        keyKind := .beltLatch
        vaultKeyId := concreteVaultKeyId
        enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce
        maxEpochCap := 1024
        activeHold := none
        emittedReceipts := [rcpt₀, rcpt₁]
        ghostWatermark := 2 } := by
    simp only [prefixTrace, runMultiCrashCustodyTrace.public_eqs]
    have hK0 : (stepMultiCrashCustody insecureTestKeyedMac256 concreteVaultMacKey s₀ .kernelPanic).1 =
        { s₀ with fs := KernelPanicCrash fsCust0, activeHold := none } := by
          simp only [stepMultiCrashCustody.public_eqs]
          rfl
    rw [hK0]
    have hS1 := hStepSignEq (KernelPanicCrash fsCust0) [0xAA] fsAfterA rcpt₀ [] 0 hExecA
    rw [hS1]
    dsimp only [List.nil_append, rcpt₀]
    have hP1 : (stepMultiCrashCustody insecureTestKeyedMac256 concreteVaultMacKey
        { fs := fsAfterA, basePath := concreteBasePath, keyKind := .beltLatch,
          vaultKeyId := concreteVaultKeyId,
          enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
          maxEpochCap := 1024, activeHold := none,
          emittedReceipts := [rcpt₀], ghostWatermark := 1 }
        (.powerLoss .revertToNand SectorTearMask.dropAllVolatile [])).1 =
        { fs := fsCrashP, basePath := concreteBasePath, keyKind := .beltLatch,
          vaultKeyId := concreteVaultKeyId,
          enrolledGenesisId := computeLockGenesisId 1 concreteGenesisNonce,
          maxEpochCap := 1024, activeHold := none,
          emittedReceipts := [rcpt₀], ghostWatermark := 1 } := by
            simp only [stepMultiCrashCustody.public_eqs]
            rfl
    rw [hP1]
    have hS2 := hStepSignEq fsCrashP [0xBB] fsAfterB rcpt₁ [rcpt₀] 1 hExecB
    rw [hS2]
    simp only [stepMultiCrashCustody.public_eqs]
    rfl
  -- Instantiate both flagship theorems!
  have hCustFlagship :=
    reserve_before_sign_multi_crash_epoch_uniqueness
      insecureTestKeyedMac256_wellFormed
      (fun b _ _ => insecureTestKeyedMac256_rogueReject b)
      hInitCust prefixTrace suffixTrace
  dsimp +zetaDelta only at hCustFlagship
  rcases hCustFlagship with ⟨hNodupFin, _, hWmLeFin, _⟩
  let cTrace : List CeremonyCrashEvent :=
    [.kernelPanic,
     .reserveAndEmitRound1 1 (List.replicate 32 0x33) [0xCA, 0xFE] 25 (List.replicate 32 0x44) {},
     .releaseSignatureFromRound1 1 [0x55, 0x66] {},
     .powerLoss .revertToNand SectorTearMask.dropAllVolatile []]
  have hCerFlagship :=
    ceremony_journal_released_implies_all_reservations_durable_and_no_reuse
      (recoveryPid := 2) insecureTestKeyedMac256_wellFormed hInitCer cTrace
      (CrashStep.kernelPanic _)
  dsimp +zetaDelta only at hCerFlagship
  rcases hCerFlagship with ⟨_, _, _, _, _, _, ⟨fsRecC, recC, jC, viewsC, hCrOk, _, hPolC, hSigC, hPktC⟩⟩
  refine ⟨s₀, c₀, hInitCust, hInitCer, ?_, ?_, ?_, hNodupFin, ?_,
    ⟨fsRecC, recC, jC, viewsC, hCrOk, hPolC, hSigC, hPktC⟩⟩
  · rw [hSMidEq]; rfl
  · rw [hSMidEq]; exact ⟨rcpt₀, by simp, rfl, rfl⟩
  · rw [hSMidEq]; exact ⟨rcpt₁, by simp, rfl, rfl⟩
  · exact Nat.le_trans (by rw [hSMidEq]; exact Nat.le_refl 2) hWmLeFin

/-- **Reserve-before-sign with the anchor outside the rollback domain.** The disk is fully
    adversarial between steps: `replaceDevice image` installs ANY filesystem state (an old
    whole-device snapshot, a bit-rotted image, a forged image). The signer releases an epoch only
    if the epoch it read under the lock is at or above the external anchor, and it advances the
    anchor before the release permit exists. -/
structure AnchoredCustodyState where
  fs          : PosixFsState
  anchorEpoch : Nat
  pending     : Option SignedEpochReceipt
  emitted     : List SignedEpochReceipt

inductive AnchoredCustodyEvent where
  | reserve (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
  | release
  | processCrash
  | replaceDevice (image : PosixFsState)

/-- One step. `checkAnchor = false` is the unanchored machine used by the `#tooth`. -/
def stepAnchoredCustody (checkAnchor : Bool) (basePath : DirName) (keyKind : StatefulKeyKind)
    (vaultKeyId : List UInt8) (maxEpochCap : Nat) (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : AnchoredCustodyState) (ev : AnchoredCustodyEvent) : AnchoredCustodyState :=
  match ev with
  | .reserve pid msg faults =>
    match s.pending with
    | some _ => s
    | none =>
      match execReserveBeforeSignAtomic s.fs pid basePath keyKind vaultKeyId maxEpochCap msg
              macFn macKey faults with
      | (fs', none) => { s with fs := fs' }
      | (fs', some r) =>
        if checkAnchor && !(decide (s.anchorEpoch ≤ r.epoch)) then
          { s with fs := fs' }
        else
          { s with fs := fs', anchorEpoch := r.epoch + 1, pending := some r }
  | .release =>
    match s.pending with
    | none => s
    | some r => { s with pending := none, emitted := s.emitted ++ [r] }
  | .processCrash => { s with pending := none }
  | .replaceDevice image => { s with fs := image }

def runAnchoredCustody (checkAnchor : Bool) (basePath : DirName) (keyKind : StatefulKeyKind)
    (vaultKeyId : List UInt8) (maxEpochCap : Nat) (macFn : KeyedMacFn) (macKey : List UInt8) :
    AnchoredCustodyState → List AnchoredCustodyEvent → AnchoredCustodyState
  | s, [] => s
  | s, ev :: rest =>
    runAnchoredCustody checkAnchor basePath keyKind vaultKeyId maxEpochCap macFn macKey
      (stepAnchoredCustody checkAnchor basePath keyKind vaultKeyId maxEpochCap macFn macKey s ev)
      rest

def AnchoredCustodyInv (s : AnchoredCustodyState) : Prop :=
  (s.emitted.map (·.epoch)).Nodup ∧
  (∀ r ∈ s.emitted, r.epoch < s.anchorEpoch) ∧
  (∀ r, s.pending = some r → r.epoch < s.anchorEpoch ∧ ∀ r' ∈ s.emitted, r'.epoch ≠ r.epoch)

theorem stepAnchoredCustody_preserves_inv (basePath : DirName) (keyKind : StatefulKeyKind)
    (vaultKeyId : List UInt8) (maxEpochCap : Nat) (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : AnchoredCustodyState) (ev : AnchoredCustodyEvent) (hInv : AnchoredCustodyInv s) :
    AnchoredCustodyInv
      (stepAnchoredCustody true basePath keyKind vaultKeyId maxEpochCap macFn macKey s ev) := by
  obtain ⟨hNd, hLt, hPend⟩ := hInv
  cases ev with
  | reserve pid msg faults =>
    unfold stepAnchoredCustody
    cases hP : s.pending with
    | some r0 => exact ⟨hNd, hLt, hPend⟩
    | none =>
      dsimp only
      rcases hExec : execReserveBeforeSignAtomic s.fs pid basePath keyKind vaultKeyId maxEpochCap
        msg macFn macKey faults with ⟨fs', ro⟩
      cases ro with
      | none => exact ⟨hNd, hLt, fun r h => by simp at h⟩
      | some r =>
        dsimp only
        by_cases hGe : s.anchorEpoch ≤ r.epoch
        · simp only [hGe, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte]
          refine ⟨hNd, fun r' hr' => ?_, fun r1 h1 => ?_⟩
          · have := hLt r' hr'
            show r'.epoch < r.epoch + 1
            omega
          · have hEq : r = r1 := Option.some.inj h1
            subst hEq
            refine ⟨Nat.lt_succ_self _, fun r' hr' => ?_⟩
            have := hLt r' hr'
            omega
        · simp only [hGe, decide_false, Bool.not_false, Bool.and_true, ↓reduceIte]
          exact ⟨hNd, hLt, fun r h => by simp at h⟩
  | release =>
    unfold stepAnchoredCustody
    cases hP : s.pending with
    | none => exact ⟨hNd, hLt, hPend⟩
    | some r =>
      dsimp only
      obtain ⟨hrLt, hrFresh⟩ := hPend r hP
      refine ⟨?_, ?_, fun r1 h1 => by simp at h1⟩
      · rw [List.map_append]
        refine nodup_snoc hNd (fun y hy => ?_)
        rcases List.mem_map.mp hy with ⟨r', hr', rfl⟩
        exact hrFresh r' hr'
      · intro r' hr'
        rcases List.mem_append.mp hr' with h | h
        · exact hLt r' h
        · rcases List.mem_singleton.mp h with rfl
          exact hrLt
  | processCrash =>
    exact ⟨hNd, hLt, fun r1 h1 => by simp [stepAnchoredCustody] at h1⟩
  | replaceDevice image =>
    exact ⟨hNd, hLt, hPend⟩

/-- **Whole-device rollback cannot reuse an epoch
    (`anchored_custody_epoch_unique_under_device_rollback`)**: for EVERY trace of reservations,
    releases, process crashes and arbitrary device replacements (snapshot restore, bit-rot,
    forged images), with ANY MAC function, the released epochs are pairwise distinct. The proof
    uses nothing about the disk: the anchor alone carries the invariant. -/
theorem anchored_custody_epoch_unique_under_device_rollback (basePath : DirName)
    (keyKind : StatefulKeyKind) (vaultKeyId : List UInt8) (maxEpochCap : Nat)
    (macFn : KeyedMacFn) (macKey : List UInt8) (trace : List AnchoredCustodyEvent) :
    ∀ s : AnchoredCustodyState, AnchoredCustodyInv s →
      AnchoredCustodyInv
        (runAnchoredCustody true basePath keyKind vaultKeyId maxEpochCap macFn macKey s trace) ∧
      ((runAnchoredCustody true basePath keyKind vaultKeyId maxEpochCap macFn macKey s
        trace).emitted.map (·.epoch)).Nodup := by
  induction trace with
  | nil => intro s hInv; exact ⟨hInv, hInv.1⟩
  | cons ev rest ih =>
    intro s hInv
    exact ih _ (stepAnchoredCustody_preserves_inv basePath keyKind vaultKeyId maxEpochCap macFn
      macKey s ev hInv)

/-- **`#tooth` (`tooth_unanchored_device_restore_reuses_epoch`)**: the same machine WITHOUT the
    anchor check. From any state in which one reservation succeeds, restoring the device image
    taken before that reservation makes the machine release the same epoch a second time. -/
theorem tooth_unanchored_device_restore_reuses_epoch (basePath : DirName)
    (keyKind : StatefulKeyKind) (vaultKeyId : List UInt8) (maxEpochCap : Nat)
    (macFn : KeyedMacFn) (macKey : List UInt8) (s : AnchoredCustodyState)
    (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
    {fs' : PosixFsState} {r : SignedEpochReceipt}
    (hIdle : s.pending = none)
    (hExec : execReserveBeforeSignAtomic s.fs pid basePath keyKind vaultKeyId maxEpochCap msg
      macFn macKey faults = (fs', some r)) :
    (runAnchoredCustody false basePath keyKind vaultKeyId maxEpochCap macFn macKey s
      [.reserve pid msg faults, .release, .replaceDevice s.fs,
       .reserve pid msg faults, .release]).emitted = s.emitted ++ [r] ++ [r] := by
  simp only [runAnchoredCustody, stepAnchoredCustody, hIdle, hExec, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

/-- The `#tooth` is inhabited: a freshly provisioned, rebooted vault admits a reservation, so the
    unanchored machine really does release epoch `0` twice. -/
theorem witness_unanchored_device_restore_reuses_epoch :
    ∃ (s : AnchoredCustodyState) (trace : List AnchoredCustodyEvent),
      s.emitted = [] ∧
      ¬ ((runAnchoredCustody false concreteBasePath .beltLatch concreteVaultKeyId 1024
        insecureTestKeyedMac256 concreteVaultMacKey s trace).emitted.map (·.epoch)).Nodup := by
  have h1Lt64 : (1 : InodeId) < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192)) two_pow_32_lt_two_pow_64
  have hPay32 : (encodeCustodyWalPayload .beltLatch 1024 []).length < 2 ^ 32 :=
    encodeCustodyWalPayload_lt_two_pow_32 .beltLatch 1024 []
  obtain ⟨fs0, _, _, hDur0⟩ :=
    provisionGenesis_rebooted_succeeds PosixFsState.empty 1 concreteBasePath
      concreteVaultKeyId concreteGenesisNonce (encodeCustodyWalPayload .beltLatch 1024 [])
      insecureTestKeyedMac256 insecureTestKeyedMac256_wellFormed concreteVaultMacKey
      rfl rfl rfl rfl rfl rfl h1Lt64 (by decide) (by decide) hPay32
  have hDurBoot := vaultDurableAt_after_crash hDur0 (CrashStep.kernelPanic fs0)
  obtain ⟨fs1, hSign⟩ := honest_sign_complete_when_healthy (st := KernelPanicCrash fs0) 1
    .beltLatch 1024 [0xAA] rfl rfl hDurBoot (by decide) (by decide)
  refine ⟨{ fs := KernelPanicCrash fs0, anchorEpoch := 0, pending := none, emitted := [] },
    [.reserve 1 [0xAA] {}, .release, .replaceDevice (KernelPanicCrash fs0),
     .reserve 1 [0xAA] {}, .release], rfl, ?_⟩
  rw [tooth_unanchored_device_restore_reuses_epoch concreteBasePath .beltLatch concreteVaultKeyId
    1024 insecureTestKeyedMac256 concreteVaultMacKey _ 1 [0xAA] {} rfl hSign]
  intro hNd
  simp at hNd

/-! ### Two-File Vault Update: Companion MAC Then Atomic Rename (`qsag-cli/src/vault.rs`) -/

/-- What `Vault::authenticate` reads: the 32-byte companion MAC held in the locked
    `.vault.lock` inode, and the secret-state file (its recorded `state_mac` and its contents). -/
structure VaultTwoFileState (Secret : Type) where
  companionMac : List UInt8
  recordedMac  : List UInt8
  secret       : Secret

/-- `authenticate`: the recorded MAC and the companion MAC must both equal the MAC recomputed
    over the state. -/
def vaultAuthenticate {Secret : Type} (tag : Secret → List UInt8) (v : VaultTwoFileState Secret) :
    Bool :=
  v.recordedMac == tag v.secret && v.companionMac == tag v.secret

/-- Every state a crash can leave during `Vault::reserve`, which first overwrites the companion
    MAC in place (`seal`: `write_all` + `sync_all`) and then replaces the state file by
    temp-file + rename (`replace_secret`). `companionTorn g`: the in-place 32-byte overwrite was
    torn into arbitrary bytes `g`. -/
inductive VaultReserveCrashPoint where
  | beforeSeal
  | companionTorn (g : List UInt8)
  | sealedNotReplaced
  | replaced

def vaultReserveCrashState {Secret : Type} (tag : Secret → List UInt8) (old new : Secret) :
    VaultReserveCrashPoint → VaultTwoFileState Secret
  | .beforeSeal => { companionMac := tag old, recordedMac := tag old, secret := old }
  | .companionTorn g => { companionMac := g, recordedMac := tag old, secret := old }
  | .sealedNotReplaced => { companionMac := tag new, recordedMac := tag old, secret := old }
  | .replaced => { companionMac := tag new, recordedMac := tag new, secret := new }

/-- **Interrupted two-file update is old, new, or fail-closed
    (`vault_reserve_crash_old_new_or_fail_closed`)**: at every crash point, `authenticate`
    succeeds only on the complete old state or the complete new state. In particular the window
    between `seal` and the rename fails closed whenever the two states have different MACs. -/
theorem vault_reserve_crash_old_new_or_fail_closed {Secret : Type} (tag : Secret → List UInt8)
    (old new : Secret) (pt : VaultReserveCrashPoint)
    (hAuth : vaultAuthenticate tag (vaultReserveCrashState tag old new pt) = true) :
    (vaultReserveCrashState tag old new pt).secret = old ∧
      (vaultReserveCrashState tag old new pt).companionMac = tag old ∨
    (vaultReserveCrashState tag old new pt).secret = new ∧
      (vaultReserveCrashState tag old new pt).companionMac = tag new ∧ pt = .replaced := by
  cases pt with
  | beforeSeal => exact Or.inl ⟨rfl, rfl⟩
  | companionTorn g =>
    simp only [vaultAuthenticate, vaultReserveCrashState, Bool.and_eq_true, beq_iff_eq] at hAuth
    exact Or.inl ⟨rfl, hAuth.2⟩
  | sealedNotReplaced =>
    simp only [vaultAuthenticate, vaultReserveCrashState, Bool.and_eq_true, beq_iff_eq] at hAuth
    exact Or.inl ⟨rfl, hAuth.2⟩
  | replaced => exact Or.inr ⟨rfl, rfl, rfl⟩

/-- **State-file rollback is caught by the companion MAC**: after a completed `reserve`, putting
    the OLD state file back (without rolling back the locked companion inode) fails
    authentication unless the two states collide under the MAC. Rolling back BOTH files is a
    whole-vault restore and needs the external anchor. -/
theorem vault_state_file_rollback_rejected {Secret : Type} (tag : Secret → List UInt8)
    (old new : Secret) (hDistinct : tag old ≠ tag new) :
    vaultAuthenticate tag
      { companionMac := tag new, recordedMac := tag old, secret := old } = false := by
  have h : (tag new == tag old) = false := by
    cases hb : (tag new == tag old) with
    | false => rfl
    | true => exact absurd (eq_of_beq hb).symm hDistinct
  show ((tag old == tag old) && (tag new == tag old)) = false
  rw [h, Bool.and_false]

end Qsag
end
