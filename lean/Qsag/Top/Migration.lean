module
public import Qsag.Machine.Gf128ClmulLoopAgreement
/-
# Qsag.Top.Migration — End-to-End Composed Post-Quantum Ownership Migration Security

Top-level composition module (zero `import all`) connecting:
1. The ideal migration functionality `Spec.idealMigrateMachine` (enrolled snapshot, derived
   nullifier, ownership relation): per-identity non-double-claim and conservation against the total
   enrolled entitlement,
2. Constructive Pocklington–Pratt primality certificates for `secp256k1` field and scalar-order
   primes (`PrattPrimalityCert`),
3. `ZKBoo` 2-of-3 special-soundness scalar extraction, Zcash Orchard `RedPallas` rerandomized key
   extraction, and active field-check bounds across `secp256k1`, `Ed25519`, `BLS12-381`, `Pallas`,
   and `Goldilocks³` (`PallasAndBlsMigration`),
4. Unconditional 438-repetition circuit-to-sacrifice ceremony defect bounds, QROM soundness scaling,
   and five-way `𝔽_{2^{128}}` multiplication equivalence (`ActiveMigrationZeroTest`, `Math.Gf2Pow128`),
5. The discrete-log instance `dlogOwnershipScheme` of `Spec.LegacyOwnershipScheme` over a
   `PrimeSubgroup`, and acceptance by the ideal machine of the scalar extracted by `ZKBoo`,
6. Refinement of the settlement ledger `MigrationExecution.settle` into `Spec.idealMigrateMachine`
   (`migrationSettlement_refines_idealMigrate`), conditional on `LegacySettlementBinding`: the
   settlement model has no enrolled snapshot, entitlement or key-derived nullifier, so the link
   from an accepted settlement to `Spec.ValidLegacyOwnership` is a hypothesis of that structure.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealMigrate
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Primality
public import Qsag.Protocol.Migration.PallasAndBlsMigration
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
public import Qsag.Protocol.Migration.HdToprfAndMigrationSecurity
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 1. Certified Curve Primality + `ZKBoo` / `RedPallas` Witness Extraction + Ideal Nullifier Safety -/

/-- **Certified Primality, `ZKBoo` / `RedPallas` Extraction, and Ideal Migration Conservation
    (`legacy_curve_primality_extraction_and_ideal_migration_chain`)**:
    Composes `Spec.idealMigrateMachine_reachable_inv`, `PrattPrimalityCert`
    (`secp256k1FieldPrime_isPrime`, `secp256k1OrderPrime_isPrime`, `verifyPrimeCert_sound`),
    and `PallasAndBlsMigration` (`zkboo_two_challenge_extraction_sound`,
    `orchard_redpallas_rerandomized_extraction_sound`, `migration_active_field_check_exact_bounds`):
    1. Every reachable state of `idealMigrateMachine` maintains `spentNullifiers.Nodup`, settles
       each legacy key at most once, and has `totalMigrated ≤ EnrolledSnapshot.total snapshot`,
    2. `secp256k1` base-field and scalar-order moduli are constructively certified primes,
    3. Distinct `ZKBoo` opened views `(e₁ ≠ e₂)` extract the unique canonical secret scalar `sk < ord`
       satisfying `grp.smul sk = pk`, and
    4. `RedPallas` rerandomized views extract `(ask, alpha, rsk)` satisfying `grp.add (grp.smul ask) (grp.smul alpha) = rk`! -/
theorem legacy_curve_primality_extraction_and_ideal_migration_chain
    {LegacyPk Witness : Type} [DecidableEq LegacyPk]
    (scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness)
    (snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk)
    {stMig : Qsag.Spec.IdealMigrateState LegacyPk}
    (hReach : (Qsag.Spec.idealMigrateMachine scheme snapshot).Reachable stMig)
    {chain : List Qsag.PocklingtonStep} {targetPrime : Nat}
    (hCert : Qsag.verifyPrimeCert chain targetPrime = true)
    {C : Qsag.SwCurve} {G pk : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValidDlog : Qsag.ZkBooDlogCommitted grp pk shares)
    {C_pal : Qsag.SwCurve} {G_pal rk : Qsag.SwPoint}
    (grpPal : Qsag.PrimeSubgroup C_pal G_pal Qsag.q_pallas)
    (askShares alphaShares : Fin 3 → Nat)
    (hAskRange : 0 < Qsag.zkbooReconstructScalar Qsag.q_pallas (askShares 0) (askShares 1) (askShares 2) ∧
                 Qsag.zkbooReconstructScalar Qsag.q_pallas (askShares 0) (askShares 1) (askShares 2) < Qsag.q_pallas)
    (hAlphaRange : Qsag.zkbooReconstructScalar Qsag.q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2) < Qsag.q_pallas)
    (hRskPos : 0 < Qsag.redpallasEffectiveScalar Qsag.q_pallas
      (Qsag.zkbooReconstructScalar Qsag.q_pallas (askShares 0) (askShares 1) (askShares 2))
      (Qsag.zkbooReconstructScalar Qsag.q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2)))
    (hCurveRk : grpPal.smul (Qsag.redpallasEffectiveScalar Qsag.q_pallas
      (Qsag.zkbooReconstructScalar Qsag.q_pallas (askShares 0) (askShares 1) (askShares 2))
      (Qsag.zkbooReconstructScalar Qsag.q_pallas (alphaShares 0) (alphaShares 1) (alphaShares 2))) = rk) :
    let (s0, s1, s2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1) (Qsag.zkbooOpenedPair shares e2)
    let sk := Qsag.zkbooReconstructScalar ord s0 s1 s2
    let (a0, a1, a2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair askShares e1) (Qsag.zkbooOpenedPair askShares e2)
    let (r0, r1, r2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair alphaShares e1) (Qsag.zkbooOpenedPair alphaShares e2)
    let ask := Qsag.zkbooReconstructScalar Qsag.q_pallas a0 a1 a2
    let alpha := Qsag.zkbooReconstructScalar Qsag.q_pallas r0 r1 r2
    (stMig.totalMigrated ≤ Qsag.Spec.EnrolledSnapshot.total snapshot ∧
     stMig.spentNullifiers.Nodup ∧
     (stMig.settledClaims.map (fun r => r.claim.legacyPk)).Nodup) ∧
    (Qsag.Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F ∧
     Qsag.Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 ∧
     Qsag.Weierstrass.IsPrime targetPrime) ∧
    (0 < sk ∧ sk < ord ∧ grp.smul sk = pk) ∧
    (grpPal.add (grpPal.smul ask) (grpPal.smul alpha) = rk) ∧
    (Qsag.ActiveFieldCheckBound 35 250 Qsag.migrationSecp256k1P ∧
     Qsag.ActiveFieldCheckBound 35 249 Qsag.p_bls381 ∧
     Qsag.ActiveFieldCheckBound 35 248 Qsag.p_pallas) := by
  have hInv := Qsag.Spec.idealMigrateMachine_reachable_inv scheme snapshot hReach
  obtain ⟨hSkPos, hSkLt, hSmul, _⟩ :=
    Qsag.zkboo_two_challenge_extraction_sound grp shares e1 e2 hNe hValidDlog
  obtain ⟨_, _, _, _, _, hPalEq, _⟩ :=
    Qsag.orchard_redpallas_rerandomized_extraction_sound grpPal askShares alphaShares e1 e2 hNe
      hAskRange hAlphaRange hRskPos hCurveRk
  obtain ⟨hSecp, _, hBlsP, _, hPalP, _, _⟩ := Qsag.migration_active_field_check_exact_bounds
  exact ⟨⟨hInv.totalMigrated_le_enrolled, hInv.2.1, hInv.settled_legacyPk_nodup⟩,
         ⟨Qsag.secp256k1FieldPrime_isPrime, Qsag.secp256k1OrderPrime_isPrime,
          Qsag.verifyPrimeCert_sound hCert⟩,
         ⟨hSkPos, hSkLt, hSmul⟩,
         hPalEq,
         ⟨hSecp, hBlsP, hPalP⟩⟩

/-! ## 2. Unconditional 438-Repetition Sacrifice Ceremony Defect + QROM Scaling + `𝔽_{2^{128}}` Bridge -/

/-- **Active 438-Repetition Sacrifice Ceremony Soundness & Canonical `Gf2Pow128` Bridge
    (`active_migration_ceremony_qrom_and_gf2pow128_chain`)**:
    Composes `MigrationExecution.migration_unconditional_circuit_to_sacrifice_ceremony_bound`,
    `MigrationExecution.migration_438_zkboo_and_ceremony_qrom_soundness`, and
    `Math.gf2Pow128_five_way_mul_agreement` (connecting `MigrationExecution.rustGf128Mul` to
    canonical `Math.Gf2Pow128.mul` and hardware `PCLMULQDQ` / `PMULL`!). -/
theorem active_migration_ceremony_qrom_and_gf2pow128_chain
    (gates : List Qsag.MigrationExecution.Gate)
    (relB : Qsag.MigrationKey256 → Bool)
    (hCirc : Qsag.MigrationExecution.CircuitSoundForRel gates relB)
    (batches : Qsag.MigrationWitnessBatches)
    (hBatch : Qsag.MigrationBatchConsistent batches)
    (hFalse : relB (Qsag.extractRepetitionWitness (batches 0) 0) = false)
    (st : Fin 7 → Qsag.MigrationExecution.GateState) (numSuper : Fin 7 → Nat)
    (hEval : ∀ b : Fin 7, Qsag.MigrationExecution.evalGates ⟨Qsag.MigrationExecution.witnessWires (batches b), []⟩ gates = some (st b))
    (hOpen : ∀ b : Fin 7, Qsag.MigrationExecution.finishWithoutCheck (st b) = .accepted)
    (hCap : ∀ b : Fin 7, (st b).pending.length ≤ 128 * numSuper b)
    (r : Nat) (hr : r ≤ 13)
    (otherGammas : Fin 7 → Nat → Qsag.MigrationExecution.RustGf128)
    (p : Qsag.MigrationExecution.FullCeremonyProver r)
    (hOwn : Qsag.MigrationExecution.FullForkStrategiesPrecedeOwnCoins p)
    (rep : Fin 438) (others : Qsag.MigrationExecution.FullCeremonyCoins)
    (qHash : Nat) (hqHash : qHash + 1 ≤ 2 ^ 56)
    (a b : BitVec 128)
    (pSrv : Fin 3) (srvView : Fin 3 → Qsag.Goldilocks)
    (hViewZero : srvView pSrv = CommRingOps.zero) (blindInput : Qsag.Goldilocks) :
    let fk := Qsag.MigrationExecution.repetitionFork rep
    let lane := Qsag.MigrationExecution.repetitionLane rep
    (relB (Qsag.migrationRepetitionWitness batches rep) = false ∧
     ∃ qStar : Nat, qStar < numSuper fk ∧
       Qsag.MigrationExecution.superBlockDefect (st fk).pending qStar lane ≠ 0#128 ∧
       ((Qsag.MigrationExecution.fullFlushCoinSpace
           Qsag.MigrationExecution.productionFoldCoins
           Qsag.MigrationExecution.productionBaseCoins r).filter (fun gv =>
         Qsag.MigrationExecution.fullCeremonyAccepts r st numSuper otherGammas
           (fun b' => if b' = fk then qStar else 0) p
           (Qsag.MigrationExecution.setFullForkCoins others fk gv))).length * 2 ^ 127 ≤
         (Qsag.MigrationExecution.fullFlushCoinSpace
           Qsag.MigrationExecution.productionFoldCoins
           Qsag.MigrationExecution.productionBaseCoins r).length) ∧
    (8 * (qHash + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 ≤ 3 ^ 438 ∧
     (qHash + 1) * 2 ^ 438 * 2 ^ 192 ≤ 3 ^ 438) ∧
    (∃ c : Fin 3 → Qsag.Goldilocks,
      (Qsag.sum3 c = blindInput ∧ Qsag.rss3ServerView pSrv c = srvView) ∧
      ∀ c' : Fin 3 → Qsag.Goldilocks,
        Qsag.sum3 c' = blindInput → Qsag.rss3ServerView pSrv c' = srvView → c' = c) ∧
    ((Qsag.Math.Gf2Pow128.mul ⟨a⟩ ⟨b⟩).bits = Qsag.MigrationExecution.rustGf128Mul a b ∧
     (Qsag.Math.Gf2Pow128.mul ⟨a⟩ ⟨b⟩).bits =
       Qsag.SimdBinaryEquiv.fastRemainder (Qsag.pclmulqdqFourProduct256 a b)) := by
  have hCer :=
    Qsag.MigrationExecution.migration_unconditional_circuit_to_sacrifice_ceremony_bound
      gates relB hCirc batches hBatch hFalse st numSuper hEval hOpen hCap r hr otherGammas p hOwn rep others
  have hQrom := Qsag.MigrationExecution.migration_438_zkboo_and_ceremony_qrom_soundness qHash hqHash
  have hToprfPriv := Qsag.rss3_client_blind_perfect_privacy pSrv srvView hViewZero blindInput
  obtain ⟨_, hRustMul, _, hClmul, _⟩ := Qsag.Math.gf2Pow128_five_way_mul_agreement a b
  exact ⟨hCer, hQrom, hToprfPriv, ⟨hRustMul, hClmul⟩⟩

/-! ## 3. Discrete-Log Ownership Instance of `Spec.LegacyOwnershipScheme` -/

/-- Discrete-log ownership over a prime-order subgroup: the witness of the legacy key `pk` is the
    canonical scalar `0 < sk < ord` with `grp.smul sk = pk`. The nullifier derivation and its
    injectivity are parameters. -/
def dlogOwnershipScheme {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂) :
    Qsag.Spec.LegacyOwnershipScheme Qsag.SwPoint Nat where
  ownsKey pk sk _ := 0 < sk ∧ sk < ord ∧ grp.smul sk = pk
  checkOwnership pk sk _ := decide (0 < sk ∧ sk < ord ∧ grp.smul sk = pk)
  check_iff _ _ _ := decide_eq_true_iff
  deriveNullifier := deriveNullifier
  deriveNullifier_injective := hInj

/-- A claim accepted by the ideal machine over `dlogOwnershipScheme` carries the unique canonical
    discrete logarithm of an enrolled key and mints that key's entitlement. -/
theorem dlogOwnership_accepted_claim_has_unique_scalar
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.SwPoint)
    {st st' : Qsag.Spec.IdealMigrateState Qsag.SwPoint}
    {claim : Qsag.Spec.MigrationClaim Qsag.SwPoint} {sk : Nat}
    {out : Qsag.Spec.MigrationReceipt Qsag.SwPoint}
    (hStep : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj)
      snapshot).step st (claim, sk) = some (st', out)) :
    Qsag.Spec.EnrolledEntitlement snapshot claim.legacyPk out.amount ∧
    claim.nullifier = deriveNullifier claim.legacyPk ∧
    (0 < sk ∧ sk < ord ∧ grp.smul sk = claim.legacyPk) ∧
    ∀ sk' : Nat, sk' < ord → grp.smul sk' = claim.legacyPk → sk' = sk := by
  obtain ⟨hValid, _, _, _⟩ :=
    (Qsag.Spec.idealMigrateMachine_step_eq_some_iff _ snapshot st st' claim sk out).mp hStep
  obtain ⟨hEnt, hNull, hOwn⟩ := hValid
  have hOwn' : 0 < sk ∧ sk < ord ∧ grp.smul sk = claim.legacyPk := hOwn
  exact ⟨hEnt, hNull, hOwn', fun sk' hLt hSmul =>
    Qsag.canonical_legacy_scalar_unique grp hLt hOwn'.2.1 (hSmul.trans hOwn'.2.2.symm)⟩

/-- The scalar extracted from two distinct `ZKBoo` openings for an enrolled, not yet settled key is
    accepted by the ideal machine over `dlogOwnershipScheme` and mints the enrolled entitlement. -/
theorem zkboo_extracted_scalar_claims_enrolled_entitlement
    {C : Qsag.SwCurve} {G pk : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.SwPoint)
    {st : Qsag.Spec.IdealMigrateState Qsag.SwPoint}
    (hReach : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj)
      snapshot).Reachable st)
    (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValidDlog : Qsag.ZkBooDlogCommitted grp pk shares)
    {amount : Nat} (hEnrolled : Qsag.Spec.EnrolledEntitlement snapshot pk amount)
    (hUnclaimed : pk ∉ st.settledClaims.map (fun r => r.claim.legacyPk))
    (dest : Qsag.Spec.Bytes) :
    let (s0, s1, s2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1) (Qsag.zkbooOpenedPair shares e2)
    let sk := Qsag.zkbooReconstructScalar ord s0 s1 s2
    (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj) snapshot).step st
        (⟨pk, deriveNullifier pk, dest⟩, sk) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := deriveNullifier pk :: st.spentNullifiers
              settledClaims := ⟨⟨pk, deriveNullifier pk, dest⟩, amount⟩ :: st.settledClaims },
            ⟨⟨pk, deriveNullifier pk, dest⟩, amount⟩) := by
  have hExt := Qsag.zkboo_two_challenge_extraction_sound grp shares e1 e2 hNe hValidDlog
  revert hExt
  generalize Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1)
    (Qsag.zkbooOpenedPair shares e2) = triple
  obtain ⟨s0, s1, s2⟩ := triple
  intro hExt
  obtain ⟨hPos, hLt, hSmul, _⟩ := hExt
  exact Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts
    (Qsag.Spec.idealMigrateMachine_reachable_inv _ snapshot hReach)
    ⟨hEnrolled, rfl, hPos, hLt, hSmul⟩ hUnclaimed

/-! ## 4. Settlement Ledger Refinement into `Spec.idealMigrateMachine` -/

/-- Link between the settlement ledger `MigrationExecution.settle` and the ideal migration
    functionality. `MigrationExecution.Statement` has no enrolled snapshot, no entitlement and no
    derivation of its nullifier from a legacy key, so these facts are obligations on the
    authorization verifier and circuit compiler:
    * `encode` maps a claim and ownership witness to the submitted statement, authorization and
      witness lanes, preserving the nullifier (`encode_nullifier`);
    * `creditedAmount` is the amount the settlement layer credits for an accepted claim;
    * `accepted_sound`: an accepted settlement is a claim with `Spec.ValidLegacyOwnership` for the
      credited amount (enrolled key, derived nullifier, ownership witness);
    * `owner_accepted`: a claim with `Spec.ValidLegacyOwnership` and an unspent nullifier is
      accepted. -/
structure LegacySettlementBinding {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness)
    (snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool)
    (compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate) where
  encode : Qsag.Spec.MigrationClaim LegacyPk × Witness →
    Qsag.MigrationExecution.Submission Authorization
  creditedAmount : Qsag.Spec.MigrationClaim LegacyPk → Nat
  encode_nullifier : ∀ (inp : Qsag.Spec.MigrationClaim LegacyPk × Witness),
    (encode inp).statement.nullifier = inp.1.nullifier
  accepted_sound : ∀ (ledger : Qsag.MigrationExecution.Ledger)
      (inp : Qsag.Spec.MigrationClaim LegacyPk × Witness),
    (Qsag.MigrationExecution.settle verifyAuthorization compile ledger (encode inp)).2 =
        .accepted →
      Qsag.Spec.ValidLegacyOwnership scheme snapshot inp.1 inp.2 (creditedAmount inp.1)
  owner_accepted : ∀ (ledger : Qsag.MigrationExecution.Ledger)
      (inp : Qsag.Spec.MigrationClaim LegacyPk × Witness) (amount : Nat),
    Qsag.Spec.ValidLegacyOwnership scheme snapshot inp.1 inp.2 amount →
    inp.1.nullifier ∉ ledger.spent →
      (Qsag.MigrationExecution.settle verifyAuthorization compile ledger (encode inp)).2 =
        .accepted

/-- Receipt emitted for a settlement verdict: only an accepted settlement emits
    `(ledger', receipt)`. -/
def settlementReceipt {LegacyPk : Type} (ledger' : Qsag.MigrationExecution.Ledger)
    (receipt : Qsag.Spec.MigrationReceipt LegacyPk) :
    Qsag.MigrationExecution.SettlementResult →
      Option (Qsag.MigrationExecution.Ledger × Qsag.Spec.MigrationReceipt LegacyPk)
  | .accepted => some (ledger', receipt)
  | .replay => none
  | .unauthorized => none
  | .executionRejected _ => none

private theorem settlementReceipt_eq_some {LegacyPk : Type}
    {ledger' c' : Qsag.MigrationExecution.Ledger}
    {receipt out : Qsag.Spec.MigrationReceipt LegacyPk}
    {res : Qsag.MigrationExecution.SettlementResult}
    (h : settlementReceipt ledger' receipt res = some (c', out)) :
    res = .accepted ∧ c' = ledger' ∧ out = receipt := by
  cases res with
  | accepted =>
    have h' : some (ledger', receipt) = some (c', out) := h
    injection h' with h'
    injection h' with h1 h2
    exact ⟨rfl, h1.symm, h2.symm⟩
  | replay =>
    exact nomatch (show (none : Option (Qsag.MigrationExecution.Ledger ×
      Qsag.Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)
  | unauthorized =>
    exact nomatch (show (none : Option (Qsag.MigrationExecution.Ledger ×
      Qsag.Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)
  | executionRejected _ =>
    exact nomatch (show (none : Option (Qsag.MigrationExecution.Ledger ×
      Qsag.Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)

private theorem settlementReceipt_eq_none {LegacyPk : Type}
    {ledger' : Qsag.MigrationExecution.Ledger}
    {receipt : Qsag.Spec.MigrationReceipt LegacyPk}
    {res : Qsag.MigrationExecution.SettlementResult}
    (h : settlementReceipt ledger' receipt res = none) : ¬ (res = .accepted) := by
  intro hAcc
  subst hAcc
  exact nomatch (show some (ledger', receipt) = (none : Option (Qsag.MigrationExecution.Ledger ×
    Qsag.Spec.MigrationReceipt LegacyPk)) from h)

/-- Settlement machine over the ideal interface: a claim and witness are encoded by the binding and
    settled by `MigrationExecution.settle` against the spent-nullifier ledger; an accepted
    settlement emits the receipt with the credited amount. -/
def migrationSettlementMachine {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness}
    {snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk}
    {verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool}
    {compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate}
    (B : LegacySettlementBinding scheme snapshot verifyAuthorization compile) :
    Qsag.Spec.Machine Qsag.MigrationExecution.Ledger
      (Qsag.Spec.MigrationClaim LegacyPk × Witness) (Qsag.Spec.MigrationReceipt LegacyPk) where
  Init ledger := ledger = ⟨[]⟩
  step ledger inp :=
    settlementReceipt
      (Qsag.MigrationExecution.settle verifyAuthorization compile ledger (B.encode inp)).1
      ⟨inp.1, B.creditedAmount inp.1⟩
      (Qsag.MigrationExecution.settle verifyAuthorization compile ledger (B.encode inp)).2
  errStep ledger _ := ledger

private theorem settle_accepted_fresh {Authorization : Type}
    (verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool)
    (compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate)
    (ledger : Qsag.MigrationExecution.Ledger)
    (submission : Qsag.MigrationExecution.Submission Authorization)
    (hAcc : (Qsag.MigrationExecution.settle verifyAuthorization compile ledger submission).2 =
      .accepted) :
    submission.statement.nullifier ∉ ledger.spent := by
  intro hMem
  rw [Qsag.MigrationExecution.settle_replay_rejected verifyAuthorization compile ledger
    submission hMem] at hAcc
  exact nomatch (show Qsag.MigrationExecution.SettlementResult.replay = .accepted from hAcc)

/-- Under `LegacySettlementBinding` the settlement ledger refines the ideal migration machine, with
    the spent set of the ledger equal to the ideal spent-nullifier list. -/
def migrationSettlement_refines_idealMigrate
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness}
    {snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk}
    {verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool}
    {compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate}
    (B : LegacySettlementBinding scheme snapshot verifyAuthorization compile) :
    Qsag.Spec.Refines (migrationSettlementMachine B)
      (Qsag.Spec.idealMigrateMachine scheme snapshot) where
  Rel ledger st := ledger.spent = st.spentNullifiers
  absInit _ := Qsag.Spec.IdealMigrateState.init
  init_ok {c₀} hInit := by
    have hInit' : c₀ = ⟨[]⟩ := hInit
    subst hInit'
    exact ⟨rfl, rfl⟩
  sim_ok {c c' a inp out} hRel hStep := by
    obtain ⟨claim, wit⟩ := inp
    have hRel' : c.spent = a.spentNullifiers := hRel
    have hEnc : (B.encode (claim, wit)).statement.nullifier = claim.nullifier :=
      B.encode_nullifier (claim, wit)
    obtain ⟨hAcc, hC', hOut⟩ := settlementReceipt_eq_some hStep
    have hValid : Qsag.Spec.ValidLegacyOwnership scheme snapshot claim wit
        (B.creditedAmount claim) := B.accepted_sound c (claim, wit) hAcc
    have hFreshC := settle_accepted_fresh verifyAuthorization compile c _ hAcc
    rw [hEnc, hRel'] at hFreshC
    have hIdeal := (Qsag.Spec.idealMigrateMachine_step_eq_some_iff scheme snapshot a _ claim wit
      ⟨claim, B.creditedAmount claim⟩).mpr ⟨hValid, hFreshC, rfl, rfl⟩
    rw [hIdeal]
    refine ⟨hOut.symm, ?_⟩
    have hIns := Qsag.MigrationExecution.settle_accept_inserts verifyAuthorization compile c
      (B.encode (claim, wit)) hAcc
    rw [hEnc, hRel'] at hIns
    rw [hC']
    exact hIns
  sim_err {c a inp} hRel hNone := by
    obtain ⟨claim, wit⟩ := inp
    have hRel' : c.spent = a.spentNullifiers := hRel
    have hNotAcc := settlementReceipt_eq_none hNone
    refine ⟨?_, hRel⟩
    cases hIdeal : (Qsag.Spec.idealMigrateMachine scheme snapshot).step a (claim, wit) with
    | none => rfl
    | some pair =>
      obtain ⟨a', out⟩ := pair
      obtain ⟨hValid, hFresh, _, _⟩ :=
        (Qsag.Spec.idealMigrateMachine_step_eq_some_iff scheme snapshot a a' claim wit out).mp
          hIdeal
      rw [← hRel'] at hFresh
      exact absurd (B.owner_accepted c (claim, wit) out.amount hValid hFresh) hNotAcc

/-- Safety of the settlement ledger inherited from the ideal machine through
    `migrationSettlement_refines_idealMigrate`: along every trace from the empty ledger, each
    accepted claim has `Spec.ValidLegacyOwnership` for the amount of its receipt, the accepted
    legacy keys are pairwise distinct, the amounts sum to at most the total enrolled entitlement,
    and the ledger has no duplicate nullifier. -/
theorem migrationSettlement_trace_ownership_nodup_conservation
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness}
    {snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk}
    {verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool}
    {compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate}
    (B : LegacySettlementBinding scheme snapshot verifyAuthorization compile)
    {ledger₀ ledger : Qsag.MigrationExecution.Ledger}
    {tr : List ((Qsag.Spec.MigrationClaim LegacyPk × Witness) ×
      Qsag.Spec.MigrationReceipt LegacyPk)}
    (hInit : (migrationSettlementMachine B).Init ledger₀)
    (hTrace : (migrationSettlementMachine B).ValidTrace ledger₀ tr ledger) :
    (∀ io ∈ tr, Qsag.Spec.ValidLegacyOwnership scheme snapshot io.1.1 io.1.2 io.2.amount ∧
      io.2.claim = io.1.1) ∧
    (tr.map (fun io => io.1.1.legacyPk)).Nodup ∧
    (tr.map (fun io => io.2.amount)).sum ≤ Qsag.Spec.EnrolledSnapshot.total snapshot ∧
    ledger.spent.Nodup := by
  obtain ⟨hInitA, hRel₀⟩ := (migrationSettlement_refines_idealMigrate B).init_ok hInit
  obtain ⟨aFinal, hTraceA, hRelFinal⟩ :=
    (migrationSettlement_refines_idealMigrate B).lift_validTrace hRel₀ hTrace
  have hSpent : ledger.spent = aFinal.spentNullifiers := hRelFinal
  have hInv := Qsag.Spec.idealMigrateMachine_reachable_inv scheme snapshot
    ⟨_, tr, hInitA, hTraceA⟩
  refine ⟨Qsag.Spec.idealMigrateMachine_trace_ownership_sound scheme snapshot hTraceA,
    Qsag.Spec.idealMigrateMachine_trace_no_double_claim scheme snapshot hTraceA,
    Qsag.Spec.idealMigrateMachine_trace_minted_le_enrolled scheme snapshot hInitA hTraceA, ?_⟩
  rw [hSpent]
  exact hInv.2.1

/-- `#tooth` After the settlement ledger accepts a claim for a legacy key, a second claim for the
    same key is rejected whatever nullifier, destination and witness it carries: a different
    nullifier fails `accepted_sound`, the derived one is in the ledger. -/
theorem tooth_migrationSettlement_second_claim_same_legacyPk_rejected
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {scheme : Qsag.Spec.LegacyOwnershipScheme LegacyPk Witness}
    {snapshot : Qsag.Spec.EnrolledSnapshot LegacyPk}
    {verifyAuthorization : Qsag.MigrationExecution.Statement → Authorization → Bool}
    {compile : Qsag.MigrationExecution.Statement → List Qsag.MigrationExecution.Gate}
    (B : LegacySettlementBinding scheme snapshot verifyAuthorization compile)
    {ledger ledger' : Qsag.MigrationExecution.Ledger}
    {claim : Qsag.Spec.MigrationClaim LegacyPk} {wit : Witness}
    {out : Qsag.Spec.MigrationReceipt LegacyPk}
    (hStep : (migrationSettlementMachine B).step ledger (claim, wit) = some (ledger', out))
    (claim' : Qsag.Spec.MigrationClaim LegacyPk) (wit' : Witness)
    (hSame : claim'.legacyPk = claim.legacyPk) :
    (migrationSettlementMachine B).step ledger' (claim', wit') = none := by
  have hEnc : (B.encode (claim, wit)).statement.nullifier = claim.nullifier :=
    B.encode_nullifier (claim, wit)
  have hEnc' : (B.encode (claim', wit')).statement.nullifier = claim'.nullifier :=
    B.encode_nullifier (claim', wit')
  obtain ⟨hAcc, hL, _⟩ := settlementReceipt_eq_some hStep
  have hValid : Qsag.Spec.ValidLegacyOwnership scheme snapshot claim wit
      (B.creditedAmount claim) := B.accepted_sound ledger (claim, wit) hAcc
  have hIns := Qsag.MigrationExecution.settle_accept_inserts verifyAuthorization compile ledger
    (B.encode (claim, wit)) hAcc
  rw [hEnc] at hIns
  cases hSecond : (migrationSettlementMachine B).step ledger' (claim', wit') with
  | none => rfl
  | some pair =>
    obtain ⟨ledger'', out'⟩ := pair
    obtain ⟨hAcc', _, _⟩ := settlementReceipt_eq_some hSecond
    have hValid' : Qsag.Spec.ValidLegacyOwnership scheme snapshot claim' wit'
        (B.creditedAmount claim') := B.accepted_sound ledger' (claim', wit') hAcc'
    have hFresh' := settle_accepted_fresh verifyAuthorization compile ledger' _ hAcc'
    rw [hEnc'] at hFresh'
    have hNullEq : claim'.nullifier = claim.nullifier :=
      hValid'.2.1.trans ((congrArg scheme.deriveNullifier hSame).trans hValid.2.1.symm)
    have hMem : claim'.nullifier ∈ ledger'.spent := by
      rw [hL, hIns, hNullEq]
      exact .head _
    exact absurd hMem hFresh'

#verify_constructive
  Qsag.Top.legacy_curve_primality_extraction_and_ideal_migration_chain
  Qsag.Top.active_migration_ceremony_qrom_and_gf2pow128_chain
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.migrationSettlement_trace_ownership_nodup_conservation
  Qsag.Top.tooth_migrationSettlement_second_claim_same_legacyPk_rejected

#tooth_pair Qsag.Top.migrationSettlement_trace_ownership_nodup_conservation vs
  Qsag.Top.tooth_migrationSettlement_second_claim_same_legacyPk_rejected

end Qsag.Top
end
