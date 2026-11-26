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
