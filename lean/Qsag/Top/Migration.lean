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
4. 438-repetition circuit-to-sacrifice ceremony defect bounds for the `D0_BITS = 16` bit-check
   packing, the staged bit-check count at the `outer_mpc.rs` geometry (`BIT_CHECK_NUMERATOR = 63`,
   with the soundness of the stages ahead of the halving rounds as a hypothesis), QROM scaling
   arithmetic, and five-way `𝔽_{2^{128}}` multiplication equivalence (`ActiveMigrationZeroTest`,
   `Math.Gf2Pow128`),
5. The destination-bound discrete-log instance `dlogOwnershipScheme` of `Spec.LegacyOwnershipScheme`
   over a `PrimeSubgroup` (witness `DlogOwnershipWitness` binding `authorizedDest = claim.pqDestinationPk`,
   paired with `tooth_dlogOwnership_rejects_destination_swap`, and inhabited on `SwCurve` via
   `secp7Mod43_primeSubgroup` and `secp256k1_primeSubgroup`),
6. The settlement registry as a machine over RAW `MigrationExecution.Submission`s
   (`rawSettlementMachine`: snapshot admission, then `MigrationExecution.settle`) and its
   `Spec.DataRefines` forward simulation by `Spec.idealMigrateMachine` through `SettlementWire.decode`
   (`rawSettlement_dataRefines_idealMigrate`, `rawSettlement_trace_simulated`), unified end-to-end
   with `dlogOwnershipScheme` in `dlogSettlement_circuitSound`, `dlogSettlement_dataRefines_idealMigrate`,
   and `secp7Mod43_dlogSettlement_honest_accepted`!
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
  exact ⟨hCer, ⟨hQrom.1, hQrom.2.1⟩, hToprfPriv, ⟨hRustMul, hClmul⟩⟩

/-! ### Bit-check count at the `outer_mpc.rs` geometry (`BIT_CHECK_NUMERATOR = 63`)

The ceremony theorem above models the `D0_BITS = 16` packing (numerator `54`). The current
`verify_pending_bits_slice` runs seven weight stages, six ternary sumcheck rounds, eighteen
halving rounds and the base sacrifice. -/

open Qsag.MigrationExecution in
/-- **Staged bit-check count, one instance.** If each stage ahead of the halving rounds is
    sound with its degree (`StagesSound`, a hypothesis: the weighted embedding and the ternary
    sumcheck of `outer_mpc.rs` are not modelled), an adaptive prover starting from a false claim
    is accepted on at most `stagedBadCoinBound` coin vectors through the stages, `r` halving
    rounds and the base sacrifice. At the Rust stage list (`7` stages of degree `1`, `6` of
    degree `3`), `18` halving rounds, fold coins over `GF(2^128)` and a nonzero base coin, that
    count is at most `63 / (2^128 - 1)` of the coin space, and `7 + 18 + 36 + 2 = 63`. -/
theorem migration_bit_check_staged_count_numerator_63 {Cl Msg : Type}
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat)
    (stage : Nat → Cl → Msg → RustGf128 → Cl) (embed : Cl → IpClaim) (ds : List Nat)
    (hStages : StagesSound S stage (fun s => decide ((embed s).err ≠ 0#128)) ds)
    (p : StagedProver Msg (FoldProver r) ds) (s : Cl) (hErr : (embed s).err ≠ 0#128) :
    ((stagedCoinVectors S (coinVectors S Sb r) ds).filter
      (stagedAccepts stage (fun q c coins => sacrificeAccepts r q (embed c) coins) ds p s)).length ≤
      stagedBadCoinBound S.length (S.length ^ r * Sb.length)
        (sacrificeBadCoinBound S.length Sb.length r) ds ∧
    rustBitCheckStageNumerators.sum + 2 * rustBitCheckHalvingRounds + 2 = 63 ∧
    stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      63 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))) :=
  ⟨staged_sacrifice_false_claim_accepting_coins_bound S Sb hS hSb r stage embed ds hStages p s hErr,
    rust_bit_check_numerator_63_bound.2.1, rust_bit_check_numerator_63_bound.2.2.1⟩

/-! ## 3. Destination-Bound Discrete-Log Ownership Instance of `Spec.LegacyOwnershipScheme` -/

/-- Destination-bound discrete-log ownership witness: pairs the canonical curve scalar `scalar`
    with the owner-authorized destination bytes `authorizedDest`. -/
structure DlogOwnershipWitness where
  scalar : Nat
  authorizedDest : Qsag.Spec.Bytes
  deriving DecidableEq, Repr

/-- Discrete-log ownership over a prime-order subgroup (`PrimeSubgroup`, inhabited on `SwCurve` by
    `secp7Mod43_primeSubgroup` and conditionally by `secp256k1_primeSubgroup` / `pallas_primeSubgroup`):
    `ownsKey pk w claim` checks BOTH `0 < w.scalar < ord ∧ grp.smul w.scalar = pk` AND
    `w.authorizedDest = claim.pqDestinationPk`, preventing destination-swap replay of an ownership
    witness (`tooth_dlogOwnership_rejects_destination_swap`). -/
def dlogOwnershipScheme {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂) :
    Qsag.Spec.LegacyOwnershipScheme Qsag.SwPoint DlogOwnershipWitness where
  ownsKey pk w claim :=
    0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = pk ∧
      w.authorizedDest = claim.pqDestinationPk
  checkOwnership pk w claim :=
    decide (0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = pk ∧
      w.authorizedDest = claim.pqDestinationPk)
  check_iff _ _ _ := decide_eq_true_iff
  deriveNullifier := deriveNullifier
  deriveNullifier_injective := hInj

/-- A claim accepted by the ideal machine over `dlogOwnershipScheme` carries the unique canonical
    discrete logarithm of an enrolled key, binds the authorized destination, and mints that key's
    entitlement. -/
theorem dlogOwnership_accepted_claim_has_unique_scalar
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.SwPoint)
    {st st' : Qsag.Spec.IdealMigrateState Qsag.SwPoint}
    {claim : Qsag.Spec.MigrationClaim Qsag.SwPoint} {w : DlogOwnershipWitness}
    {out : Qsag.Spec.MigrationReceipt Qsag.SwPoint}
    (hStep : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj)
      snapshot).step st (claim, w) = some (st', out)) :
    Qsag.Spec.EnrolledEntitlement snapshot claim.legacyPk out.amount ∧
    claim.nullifier = deriveNullifier claim.legacyPk ∧
    w.authorizedDest = claim.pqDestinationPk ∧
    (0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = claim.legacyPk) ∧
    ∀ sk' : Nat, sk' < ord → grp.smul sk' = claim.legacyPk → sk' = w.scalar := by
  obtain ⟨hValid, _, _, _⟩ :=
    (Qsag.Spec.idealMigrateMachine_step_eq_some_iff _ snapshot st st' claim w out).mp hStep
  obtain ⟨hEnt, hNull, hOwn⟩ := hValid
  have hOwn' : 0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = claim.legacyPk ∧
      w.authorizedDest = claim.pqDestinationPk := hOwn
  exact ⟨hEnt, hNull, hOwn'.2.2.2, ⟨hOwn'.1, hOwn'.2.1, hOwn'.2.2.1⟩, fun sk' hLt hSmul =>
    Qsag.canonical_legacy_scalar_unique grp hLt hOwn'.2.1 (hSmul.trans hOwn'.2.2.1.symm)⟩

/-- **`#tooth` Destination-Swap Replay Rejected by `dlogOwnershipScheme`
    (`tooth_dlogOwnership_rejects_destination_swap`)**:
    Any witness `w` authorized for `dest₁` is deterministically rejected by both `checkOwnership`
    and `idealMigrateMachine.step` when replayed on a claim naming `dest₂ ≠ dest₁`, even before the
    legacy key has been settled! -/
theorem tooth_dlogOwnership_rejects_destination_swap
    {C : Qsag.SwCurve} {G pk : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Qsag.Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.SwPoint)
    (st : Qsag.Spec.IdealMigrateState Qsag.SwPoint)
    (sk : Nat) (dest₁ dest₂ : Qsag.Spec.Bytes) (hSwap : dest₁ ≠ dest₂) :
    (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj) snapshot).step
      st (⟨pk, deriveNullifier pk, dest₂⟩, ⟨sk, dest₁⟩) = none := by
  cases hS : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj)
      snapshot).step st (⟨pk, deriveNullifier pk, dest₂⟩, ⟨sk, dest₁⟩) with
  | none => rfl
  | some pair =>
    obtain ⟨_, _, hDestEq, _, _⟩ :=
      dlogOwnership_accepted_claim_has_unique_scalar grp deriveNullifier hInj snapshot hS
    exact absurd hDestEq hSwap

/-- The scalar extracted from two distinct `ZKBoo` openings for an enrolled, not yet settled key,
    paired with its authorized destination `dest`, is accepted by the ideal machine over
    `dlogOwnershipScheme` and mints the enrolled entitlement. -/
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
        (⟨pk, deriveNullifier pk, dest⟩, ⟨sk, dest⟩) =
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
    ⟨hEnrolled, rfl, hPos, hLt, hSmul, rfl⟩ hUnclaimed

/-! ## 4. Raw Settlement Machine and its Simulation by `Spec.idealMigrateMachine` -/

/-- Wire format of the settlement registry: how a raw `MigrationExecution.Submission` (carrying
    statement, authorization proof, and RSS witness lanes) is read as an ideal claim and witness.
    * `legacyPkOf` parses the legacy commitment bytes (partial);
    * `destinationBytes` serializes the 256-bit destination, injectively;
    * `extractWitness` reads the ownership witness off the submitted authorization and witness lanes
      (never off `statement.destination`, so destination binding is genuinely enforced);
    * `migrationDomain`, `epoch` identify the campaign. -/
structure SettlementWire (LegacyPk Witness Authorization : Type) where
  legacyPkOf : List UInt8 → Option LegacyPk
  destinationBytes : BitVec 256 → Spec.Bytes
  destinationBytes_injective : ∀ {d₁ d₂ : BitVec 256},
    destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂
  extractWitness : Authorization → RssWitnessLanes3 → Witness
  migrationDomain : BitVec 256
  epoch : UInt64

/-- The claim a statement makes for the parsed key `pk`: its nullifier and serialized
    destination. -/
def SettlementWire.claimOf {LegacyPk Witness Authorization : Type}
    (D : SettlementWire LegacyPk Witness Authorization)
    (pk : LegacyPk) (st : MigrationExecution.Statement) : Spec.MigrationClaim LegacyPk :=
  ⟨pk, st.nullifier, D.destinationBytes st.destination⟩

/-- Partial decoder from raw submissions to ideal inputs. -/
def SettlementWire.decode {LegacyPk Witness Authorization : Type}
    (D : SettlementWire LegacyPk Witness Authorization)
    (sub : MigrationExecution.Submission Authorization) :
    Option (Spec.MigrationClaim LegacyPk × Witness) :=
  match D.legacyPkOf sub.statement.legacyCommitment with
  | none => none
  | some pk => some (D.claimOf pk sub.statement, D.extractWitness sub.authorization sub.witness)

/-- Registry admission of a raw statement: its commitment parses to a key enrolled in the
    snapshot; returns the key and its entitlement. -/
def rawSettlementAdmit {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (st : MigrationExecution.Statement) : Option (LegacyPk × Nat) :=
  match D.legacyPkOf st.legacyCommitment with
  | none => none
  | some pk =>
    match Spec.EnrolledSnapshot.entitlement snapshot pk with
    | none => none
    | some amount => some (pk, amount)

private theorem rawSettlementAdmit_eq_some {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization} {snapshot : Spec.EnrolledSnapshot LegacyPk}
    {st : MigrationExecution.Statement} {pk : LegacyPk} {amount : Nat}
    (h : rawSettlementAdmit D snapshot st = some (pk, amount)) :
    D.legacyPkOf st.legacyCommitment = some pk ∧
      Spec.EnrolledSnapshot.entitlement snapshot pk = some amount := by
  unfold rawSettlementAdmit at h
  split at h
  · cases h
  · rename_i pk' hPk
    split at h
    · cases h
    · rename_i amount' hEnt
      injection h with h
      injection h with h1 h2
      subst h1
      subst h2
      exact ⟨hPk, hEnt⟩

private theorem rawSettlementAdmit_eq_none {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization} {snapshot : Spec.EnrolledSnapshot LegacyPk}
    {st : MigrationExecution.Statement} {pk : LegacyPk}
    (hPk : D.legacyPkOf st.legacyCommitment = some pk)
    (hEnt : Spec.EnrolledSnapshot.entitlement snapshot pk = none) :
    rawSettlementAdmit D snapshot st = none := by
  unfold rawSettlementAdmit
  rw [hPk]
  show (match Spec.EnrolledSnapshot.entitlement snapshot pk with
    | none => none
    | some amount => some (pk, amount)) = none
  rw [hEnt]

/-- Receipt emitted for a settlement verdict: only an accepted settlement emits
    `(ledger', receipt)`. -/
def settlementReceipt {LegacyPk : Type} (ledger' : MigrationExecution.Ledger)
    (receipt : Spec.MigrationReceipt LegacyPk) :
    MigrationExecution.SettlementResult →
      Option (MigrationExecution.Ledger × Spec.MigrationReceipt LegacyPk)
  | .accepted => some (ledger', receipt)
  | .replay => none
  | .unauthorized => none
  | .executionRejected _ => none

private theorem settlementReceipt_eq_some {LegacyPk : Type}
    {ledger' c' : MigrationExecution.Ledger}
    {receipt out : Spec.MigrationReceipt LegacyPk}
    {res : MigrationExecution.SettlementResult}
    (h : settlementReceipt ledger' receipt res = some (c', out)) :
    res = .accepted ∧ c' = ledger' ∧ out = receipt := by
  cases res with
  | accepted =>
    have h' : some (ledger', receipt) = some (c', out) := h
    injection h' with h'
    injection h' with h1 h2
    exact ⟨rfl, h1.symm, h2.symm⟩
  | replay =>
    exact nomatch (show (none : Option (MigrationExecution.Ledger ×
      Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)
  | unauthorized =>
    exact nomatch (show (none : Option (MigrationExecution.Ledger ×
      Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)
  | executionRejected _ =>
    exact nomatch (show (none : Option (MigrationExecution.Ledger ×
      Spec.MigrationReceipt LegacyPk)) = some (c', out) from h)

private theorem settlementReceipt_eq_none {LegacyPk : Type}
    {ledger' : MigrationExecution.Ledger}
    {receipt : Spec.MigrationReceipt LegacyPk}
    {res : MigrationExecution.SettlementResult}
    (h : settlementReceipt ledger' receipt res = none) : ¬ (res = .accepted) := by
  intro hAcc
  subst hAcc
  exact nomatch (show some (ledger', receipt) = (none : Option (MigrationExecution.Ledger ×
    Spec.MigrationReceipt LegacyPk)) from h)

/-- One step of the settlement registry on a RAW submission: admit the statement against the
    snapshot, then run `MigrationExecution.settle`; an accepted settlement emits the receipt for
    the parsed key, the statement's nullifier and destination, and the looked-up entitlement. -/
def rawSettlementStep {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (ledger : MigrationExecution.Ledger) (sub : MigrationExecution.Submission Authorization) :
    Option (MigrationExecution.Ledger × Spec.MigrationReceipt LegacyPk) :=
  match rawSettlementAdmit D snapshot sub.statement with
  | none => none
  | some pa =>
    settlementReceipt (MigrationExecution.settle verifyAuthorization compile ledger sub).1
      ⟨D.claimOf pa.1 sub.statement, pa.2⟩
      (MigrationExecution.settle verifyAuthorization compile ledger sub).2

/-- Ledger after a rejected raw submission: unchanged if not admitted, else the ledger returned
    by `settle`. -/
def rawSettlementErr {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (ledger : MigrationExecution.Ledger) (sub : MigrationExecution.Submission Authorization) :
    MigrationExecution.Ledger :=
  match rawSettlementAdmit D snapshot sub.statement with
  | none => ledger
  | some _ => (MigrationExecution.settle verifyAuthorization compile ledger sub).1

/-- Settlement registry as a machine over raw `MigrationExecution.Submission`s: the input is the
    adversary's interface to `settle`, with arbitrary statement, authorization and witness lanes. -/
def rawSettlementMachine {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) :
    Spec.Machine MigrationExecution.Ledger (MigrationExecution.Submission Authorization)
      (Spec.MigrationReceipt LegacyPk) where
  Init ledger := ledger = ⟨[]⟩
  step := rawSettlementStep D snapshot verifyAuthorization compile
  errStep := rawSettlementErr D snapshot verifyAuthorization compile

/-- Every ACCEPTED raw submission decodes, and the receipt is determined by the statement and the
    snapshot: the claim is the decoded one (parsed key, statement nullifier, serialized statement
    destination), the amount is the enrolled entitlement of the parsed key, the authorization
    verified, the compiled circuit run was accepted, and the nullifier was unspent and is inserted.
    No hypothesis on the verifier or the circuit is used. -/
theorem rawSettlement_accepted_decodes {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    {ledger ledger' : MigrationExecution.Ledger}
    {sub : MigrationExecution.Submission Authorization}
    {out : Spec.MigrationReceipt LegacyPk}
    (hStep : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub =
      some (ledger', out)) :
    D.decode sub = some (out.claim, D.extractWitness sub.authorization sub.witness) ∧
    D.legacyPkOf sub.statement.legacyCommitment = some out.claim.legacyPk ∧
    out.claim = D.claimOf out.claim.legacyPk sub.statement ∧
    Spec.EnrolledEntitlement snapshot out.claim.legacyPk out.amount ∧
    verifyAuthorization sub.statement sub.authorization = true ∧
    MigrationExecution.run sub.witness (compile sub.statement) = .accepted ∧
    sub.statement.nullifier ∉ ledger.spent ∧
    ledger'.spent = sub.statement.nullifier :: ledger.spent := by
  have h : rawSettlementStep D snapshot verifyAuthorization compile ledger sub =
      some (ledger', out) := hStep
  unfold rawSettlementStep at h
  split at h
  · cases h
  · rename_i pa hAd
    obtain ⟨pk, amount⟩ := pa
    obtain ⟨hPk, hEnt⟩ := rawSettlementAdmit_eq_some hAd
    obtain ⟨hAcc, hL, hOut⟩ := settlementReceipt_eq_some h
    obtain ⟨hFresh, hAuth, hRun⟩ :=
      (MigrationExecution.settle_accepted_iff verifyAuthorization compile ledger sub).mp hAcc
    have hIns := MigrationExecution.settle_accept_inserts verifyAuthorization compile ledger
      sub hAcc
    subst hOut
    subst hL
    refine ⟨?_, hPk, rfl, hEnt, hAuth, hRun, hFresh, hIns⟩
    unfold SettlementWire.decode
    rw [hPk]

/-- A rejected raw submission leaves the ledger unchanged. -/
theorem rawSettlement_rejected_ledger_unchanged {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    {ledger : MigrationExecution.Ledger} {sub : MigrationExecution.Submission Authorization}
    (hNone : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub =
      none) :
    (rawSettlementMachine D snapshot verifyAuthorization compile).errStep ledger sub =
      ledger := by
  have h : rawSettlementStep D snapshot verifyAuthorization compile ledger sub = none := hNone
  show rawSettlementErr D snapshot verifyAuthorization compile ledger sub = ledger
  unfold rawSettlementStep at h
  unfold rawSettlementErr
  split at h
  · rfl
  · exact MigrationExecution.settle_reject_ledger_unchanged verifyAuthorization compile ledger
      sub (settlementReceipt_eq_none h)

/-- What is assumed about the authorization verifier and the compiled circuit. The settlement
    model takes `verifyAuthorization` and `compile` as arbitrary parameters, so their soundness is
    external to it; enrollment, the entitlement, replay protection and the binding of the receipt
    to the statement are NOT assumed (`rawSettlement_accepted_decodes`).
    * `authorization_campaign` (verifier only): a verified statement is in this campaign's
      domain and epoch;
    * `accepted_nullifier_derived`: for a verified statement with an accepted circuit run, the
      statement nullifier is the one derived from the parsed legacy key;
    * `accepted_witness_owns`: for a verified statement with an accepted circuit run, the witness
      extracted from the submitted lanes satisfies `ownsKey` for the parsed key and for the claim
      this statement makes (its nullifier and destination).
    `migrationToy_circuitSound` is an instance over the executable `MigrationExecution.run` with a
    one-key snapshot. Its ownership relation is lane well-formedness
    (`MigrationExecution.run_checks_actual_lanes`), not a discrete logarithm: the tree contains no
    proof that a compiled circuit enforces a curve ownership relation
    (`MigrationExecution.CircuitSoundForRel` is a hypothesis wherever it is used), so no
    production instance exists. -/
structure SettlementCircuitSound {LegacyPk Witness Authorization : Type}
    (D : SettlementWire LegacyPk Witness Authorization)
    (scheme : Spec.LegacyOwnershipScheme LegacyPk Witness)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) : Prop where
  authorization_campaign : ∀ (st : MigrationExecution.Statement) (auth : Authorization),
    verifyAuthorization st auth = true →
      st.migrationDomain = D.migrationDomain ∧ st.epoch = D.epoch
  accepted_nullifier_derived : ∀ (st : MigrationExecution.Statement) (auth : Authorization)
      (w : RssWitnessLanes3) (pk : LegacyPk),
    verifyAuthorization st auth = true →
    MigrationExecution.run w (compile st) = .accepted →
    D.legacyPkOf st.legacyCommitment = some pk →
      st.nullifier = scheme.deriveNullifier pk
  accepted_witness_owns : ∀ (st : MigrationExecution.Statement) (auth : Authorization)
      (w : RssWitnessLanes3) (pk : LegacyPk),
    verifyAuthorization st auth = true →
    MigrationExecution.run w (compile st) = .accepted →
    D.legacyPkOf st.legacyCommitment = some pk →
      scheme.ownsKey pk (D.extractWitness auth w) (D.claimOf pk st)

/-- Ownership soundness of one accepted raw submission, derived from `SettlementCircuitSound` and
    the registry's own snapshot lookup: the decoded claim has `Spec.ValidLegacyOwnership` for the
    receipt amount with the witness extracted from the submitted lanes, and the statement is in
    the campaign's domain and epoch. -/
theorem rawSettlement_accepted_ownership {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    {ledger ledger' : MigrationExecution.Ledger}
    {sub : MigrationExecution.Submission Authorization}
    {out : Spec.MigrationReceipt LegacyPk}
    (hStep : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub =
      some (ledger', out)) :
    Spec.ValidLegacyOwnership scheme snapshot out.claim (D.extractWitness sub.authorization sub.witness)
      out.amount ∧
    sub.statement.migrationDomain = D.migrationDomain ∧ sub.statement.epoch = D.epoch := by
  obtain ⟨_, hPk, hClaim, hEnt, hAuth, hRun, _, _⟩ :=
    rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep
  have hNull := S.accepted_nullifier_derived sub.statement sub.authorization sub.witness
    out.claim.legacyPk hAuth hRun hPk
  have hOwn := S.accepted_witness_owns sub.statement sub.authorization sub.witness
    out.claim.legacyPk hAuth hRun hPk
  rw [← hClaim] at hOwn
  have hClaimNull : out.claim.nullifier = sub.statement.nullifier := by
    rw [hClaim]
    rfl
  exact ⟨⟨hEnt, hClaimNull.trans hNull, hOwn⟩,
    S.authorization_campaign sub.statement sub.authorization hAuth⟩

/-- Ideal view of an accepted raw step: the claim of the receipt with the witness extracted from
    the submitted authorization and lanes, and the same receipt. -/
def rawSettlementVis {LegacyPk Witness Authorization : Type}
    (D : SettlementWire LegacyPk Witness Authorization)
    (io : MigrationExecution.Submission Authorization × Spec.MigrationReceipt LegacyPk) :
    (Spec.MigrationClaim LegacyPk × Witness) × Spec.MigrationReceipt LegacyPk :=
  ((io.2.claim, D.extractWitness io.1.authorization io.1.witness), io.2)

/-- Interface-abstracting refinement of raw settlement into `IdealMigrate`. Accepted inputs use
only the wire decoder and witness extraction; malformed inputs cannot be accepted, and rejected
submissions stutter. The circuit/authorization obligation remains explicit in `S`. -/
def rawSettlement_dataRefines_idealMigrate {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk) :
    Spec.DataRefines (rawSettlementMachine D snapshot verifyAuthorization compile)
      (Spec.idealMigrateMachine scheme snapshot) D.decode id where
  Rel ledger a := ledger.spent = a.spentNullifiers
  absInit _ := Spec.IdealMigrateState.init
  init_ok := by
    intro ledger hInit
    cases hInit
    exact ⟨rfl, rfl⟩
  sim_visible := by
    intro ledger ledger' a sub out j hRel hStep hVis
    obtain ⟨hDec, _, hClaim, _, _, _, hFresh, hIns⟩ :=
      rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep
    have hJ := Option.some.inj (hVis.symm.trans hDec)
    subst j
    obtain ⟨hValid, _, _⟩ := rawSettlement_accepted_ownership S snapshot hStep
    have hClaimNull : out.claim.nullifier = sub.statement.nullifier := by rw [hClaim]; rfl
    rw [← hClaimNull, hRel] at hFresh hIns
    refine ⟨{ totalMigrated := a.totalMigrated + out.amount
              spentNullifiers := out.claim.nullifier :: a.spentNullifiers
              settledClaims := out :: a.settledClaims }, ?_, hIns⟩
    exact (Spec.idealMigrateMachine_step_eq_some_iff scheme snapshot a _ out.claim
      (D.extractWitness sub.authorization sub.witness) out).mpr ⟨hValid, hFresh, rfl, rfl⟩
  sim_internal := by
    intro ledger ledger' a sub out _ hStep hVis
    have hDec := (rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep).1
    rw [hVis] at hDec
    cases hDec
  sim_reject := by
    intro ledger a sub hRel hNone
    rw [rawSettlement_rejected_ledger_unchanged D snapshot verifyAuthorization compile hNone]
    exact hRel

theorem rawSettlement_refinement_exists {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk) :
    Nonempty (Spec.DataRefines (rawSettlementMachine D snapshot verifyAuthorization compile)
      (Spec.idealMigrateMachine scheme snapshot) D.decode id) :=
  ⟨rawSettlement_dataRefines_idealMigrate S snapshot⟩

#verify_constructive rawSettlement_refinement_exists

/-- Forward simulation with an input map. `Spec.Refines` needs one input alphabet and equal
    accept/reject verdicts; here the concrete input is a raw submission, the ideal input is its
    decoding, and a raw submission may be rejected for a reason the ideal machine does not see
    (authorization). So the simulation is stated on traces: every valid trace of the raw
    settlement machine, from a ledger whose spent set is the ideal spent-nullifier list, maps
    under `rawSettlementVis` to a valid trace of `Spec.idealMigrateMachine` with the same
    receipts, and the spent sets agree at the end. Rejected raw submissions are ideal no-ops. -/
theorem rawSettlement_trace_simulated {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk) :
    ∀ {ledger ledger' : MigrationExecution.Ledger} {a : Spec.IdealMigrateState LegacyPk}
      {tr : List (MigrationExecution.Submission Authorization ×
        Spec.MigrationReceipt LegacyPk)},
      ledger.spent = a.spentNullifiers →
      (rawSettlementMachine D snapshot verifyAuthorization compile).ValidTrace ledger tr
        ledger' →
      ∃ a' : Spec.IdealMigrateState LegacyPk,
        (Spec.idealMigrateMachine scheme snapshot).ValidTrace a
          (tr.map (rawSettlementVis D)) a' ∧
        ledger'.spent = a'.spentNullifiers
  | _, _, a, _, hRel, .nil _ => ⟨a, .nil a, hRel⟩
  | ledger, _, a, _, hRel, .accept (inp := sub) (out := out) hStep hRest => by
    obtain ⟨_, _, hClaim, _, _, _, hFresh, hIns⟩ :=
      rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep
    obtain ⟨hValid, _, _⟩ := rawSettlement_accepted_ownership S snapshot hStep
    have hClaimNull : out.claim.nullifier = sub.statement.nullifier := by
      rw [hClaim]
      rfl
    rw [← hClaimNull] at hFresh hIns
    rw [hRel] at hFresh hIns
    have hIdeal := (Spec.idealMigrateMachine_step_eq_some_iff scheme snapshot a _ out.claim
      (D.extractWitness sub.authorization sub.witness) out).mpr ⟨hValid, hFresh, rfl, rfl⟩
    obtain ⟨a', hTr, hRel'⟩ := rawSettlement_trace_simulated S snapshot
      (a := { totalMigrated := a.totalMigrated + out.amount
              spentNullifiers := out.claim.nullifier :: a.spentNullifiers
              settledClaims := out :: a.settledClaims }) hIns hRest
    exact ⟨a', .accept hIdeal hTr, hRel'⟩
  | ledger, _, a, _, hRel, .reject sub hNone hRest => by
    have hErr := rawSettlement_rejected_ledger_unchanged D snapshot verifyAuthorization compile
      hNone
    have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep ledger
        sub).spent = a.spentNullifiers := by
      rw [hErr]
      exact hRel
    exact rawSettlement_trace_simulated S snapshot hRel' hRest

/-- Safety of the raw settlement machine: along every trace of raw submissions from the empty
    ledger, each accepted submission is a claim with `Spec.ValidLegacyOwnership` for the receipt
    amount under the witness extracted from its lanes, the accepted legacy keys are pairwise
    distinct, the amounts sum to at most the total enrolled entitlement, and the ledger has no
    duplicate nullifier. -/
theorem rawSettlement_trace_ownership_nodup_conservation
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    {ledger₀ ledger : MigrationExecution.Ledger}
    {tr : List (MigrationExecution.Submission Authorization × Spec.MigrationReceipt LegacyPk)}
    (hInit : (rawSettlementMachine D snapshot verifyAuthorization compile).Init ledger₀)
    (hTrace : (rawSettlementMachine D snapshot verifyAuthorization compile).ValidTrace ledger₀ tr
      ledger) :
    (∀ io ∈ tr, Spec.ValidLegacyOwnership scheme snapshot io.2.claim
      (D.extractWitness io.1.authorization io.1.witness) io.2.amount) ∧
    (tr.map (fun io => io.2.claim.legacyPk)).Nodup ∧
    (tr.map (fun io => io.2.amount)).sum ≤ Spec.EnrolledSnapshot.total snapshot ∧
    ledger.spent.Nodup := by
  have hInit' : ledger₀ = ⟨[]⟩ := hInit
  have hRel₀ : ledger₀.spent =
      (Spec.IdealMigrateState.init : Spec.IdealMigrateState LegacyPk).spentNullifiers := by
    rw [hInit']
    rfl
  obtain ⟨aFinal, hTraceA, hRelFinal⟩ := rawSettlement_trace_simulated S snapshot hRel₀ hTrace
  have hInitA : (Spec.idealMigrateMachine scheme snapshot).Init Spec.IdealMigrateState.init := rfl
  have hInv := Spec.idealMigrateMachine_reachable_inv scheme snapshot ⟨_, _, hInitA, hTraceA⟩
  have hSound := Spec.idealMigrateMachine_trace_ownership_sound scheme snapshot hTraceA
  have hNd := Spec.idealMigrateMachine_trace_no_double_claim scheme snapshot hTraceA
  have hSum := Spec.idealMigrateMachine_trace_minted_le_enrolled scheme snapshot hInitA hTraceA
  rw [List.map_map] at hNd hSum
  refine ⟨fun io hio => (hSound _ (List.mem_map_of_mem (f := rawSettlementVis D) hio)).1,
    hNd, hSum, ?_⟩
  rw [hRelFinal]
  exact hInv.2.1

/-- `#tooth` A raw submission whose legacy commitment does not parse is rejected, whatever its
    authorization, witness lanes and nullifier. -/
theorem tooth_rawSettlement_undecodable_submission_rejected
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (ledger : MigrationExecution.Ledger) (sub : MigrationExecution.Submission Authorization)
    (hUndecodable : D.decode sub = none) :
    (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub = none := by
  cases hS : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub with
  | none => rfl
  | some pair =>
    obtain ⟨ledger', out⟩ := pair
    obtain ⟨hDec, _⟩ := rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hS
    rw [hUndecodable] at hDec
    cases hDec

/-- `#tooth` A raw submission for a parsed key outside the snapshot is rejected, whatever its
    authorization, witness lanes and nullifier: the fresh-nullifier drain on the raw interface. -/
theorem tooth_rawSettlement_unenrolled_submission_rejected
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (ledger : MigrationExecution.Ledger) (sub : MigrationExecution.Submission Authorization)
    {pk : LegacyPk} (hPk : D.legacyPkOf sub.statement.legacyCommitment = some pk)
    (hUnenrolled : Spec.EnrolledSnapshot.entitlement snapshot pk = none) :
    (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub = none := by
  show rawSettlementStep D snapshot verifyAuthorization compile ledger sub = none
  unfold rawSettlementStep
  rw [rawSettlementAdmit_eq_none hPk hUnenrolled]

/-- The destination of a receipt is the serialized destination of the accepted statement and of
    no other: a settlement recorded for any `other` destination is not an accepted step. -/
theorem tooth_rawSettlement_receipt_destination_not_substituted
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization) (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    {ledger ledger' : MigrationExecution.Ledger}
    {sub : MigrationExecution.Submission Authorization}
    {out : Spec.MigrationReceipt LegacyPk}
    (hStep : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub =
      some (ledger', out))
    (other : BitVec 256) (hOther : ¬ (other = sub.statement.destination)) :
    ¬ (out.claim.pqDestinationPk = D.destinationBytes other) := by
  obtain ⟨_, _, hClaim, _⟩ :=
    rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep
  intro hEq
  have hDest : out.claim.pqDestinationPk = D.destinationBytes sub.statement.destination := by
    rw [hClaim]
    rfl
  exact hOther (D.destinationBytes_injective (hEq.symm.trans hDest))

/-- `#tooth` Destination substitution by resubmission: after a raw submission for a legacy
    commitment is accepted, every further raw submission with the same commitment is rejected,
    whatever destination, nullifier, authorization and witness lanes it carries. -/
theorem tooth_rawSettlement_resubmission_other_destination_rejected
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    {ledger ledger' : MigrationExecution.Ledger}
    {sub : MigrationExecution.Submission Authorization}
    {out : Spec.MigrationReceipt LegacyPk}
    (hStep : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub =
      some (ledger', out))
    (sub' : MigrationExecution.Submission Authorization)
    (hSame : sub'.statement.legacyCommitment = sub.statement.legacyCommitment) :
    (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger' sub' = none := by
  obtain ⟨_, hPk, _, _, hAuth, hRun, _, hIns⟩ :=
    rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep
  have hNull := S.accepted_nullifier_derived sub.statement sub.authorization sub.witness
    out.claim.legacyPk hAuth hRun hPk
  cases hS : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger' sub' with
  | none => rfl
  | some pair =>
    obtain ⟨ledger'', out'⟩ := pair
    obtain ⟨_, hPk', _, _, hAuth', hRun', hFresh', _⟩ :=
      rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hS
    rw [hSame, hPk] at hPk'
    injection hPk' with hPkEq
    have hNull' := S.accepted_nullifier_derived sub'.statement sub'.authorization sub'.witness
      out.claim.legacyPk hAuth' hRun' (hSame ▸ hPk)
    have hMem : sub'.statement.nullifier ∈ ledger'.spent := by
      rw [hIns, hNull', ← hNull]
      exact .head _
    exact absurd hMem hFresh'

/-! ## 5. An Instance of `SettlementCircuitSound` over the Executable Circuit Run -/

/-- Toy wire format: the only commitment that parses is the one of
    `MigrationExecution.honestSubmission`, to the key given by its nullifier; destinations are
    serialized in unary; the witness is the lanes themselves. -/
def migrationToyWire : SettlementWire Spec.Digest256 RssWitnessLanes3 Unit where
  legacyPkOf c :=
    if c = MigrationExecution.honestSubmission.statement.legacyCommitment then
      some MigrationExecution.honestSubmission.statement.nullifier
    else none
  destinationBytes d := List.replicate d.toNat 0
  destinationBytes_injective h := by
    have hLen := congrArg List.length h
    rw [List.length_replicate, List.length_replicate] at hLen
    exact BitVec.eq_of_toNat_eq hLen
  extractWitness _ w := w
  migrationDomain := MigrationExecution.honestSubmission.statement.migrationDomain
  epoch := MigrationExecution.honestSubmission.statement.epoch

/-- Toy ownership scheme: the nullifier of a key is the key; a witness owns a key when its lanes
    pass `shareUniformLanesCheck`. -/
def migrationToyScheme : Spec.LegacyOwnershipScheme Spec.Digest256 RssWitnessLanes3 where
  ownsKey _ w _ := shareUniformLanesCheck w = true
  checkOwnership _ w _ := shareUniformLanesCheck w
  check_iff _ _ _ := Iff.rfl
  deriveNullifier pk := pk
  deriveNullifier_injective h := h

/-- Toy authorization verifier: the statement carries the nullifier, domain and epoch of
    `MigrationExecution.honestSubmission`. -/
def migrationToyVerify (st : MigrationExecution.Statement) (_ : Unit) : Bool :=
  decide (st.nullifier = MigrationExecution.honestSubmission.statement.nullifier ∧
    st.migrationDomain = MigrationExecution.honestSubmission.statement.migrationDomain ∧
    st.epoch = MigrationExecution.honestSubmission.statement.epoch)

/-- Toy snapshot: the single parsed key with entitlement `100`. -/
def migrationToySnapshot : Spec.EnrolledSnapshot Spec.Digest256 :=
  [(MigrationExecution.honestSubmission.statement.nullifier, 100)]

private theorem migrationToyWire_legacyPkOf_eq_some {c : List UInt8} {pk : Spec.Digest256}
    (h : migrationToyWire.legacyPkOf c = some pk) :
    pk = MigrationExecution.honestSubmission.statement.nullifier := by
  have h' : (if c = MigrationExecution.honestSubmission.statement.legacyCommitment then
      some MigrationExecution.honestSubmission.statement.nullifier else none) = some pk := h
  split at h'
  · injection h' with h'
    exact h'.symm
  · cases h'

/-- `SettlementCircuitSound` holds for the toy wire, scheme and verifier with the executable
    circuit `MigrationExecution.honestCircuit`. -/
theorem migrationToy_circuitSound :
    SettlementCircuitSound migrationToyWire migrationToyScheme migrationToyVerify
      MigrationExecution.honestCircuit where
  authorization_campaign _ _ hAuth := (of_decide_eq_true hAuth).2
  accepted_nullifier_derived _ _ _ _ hAuth _ hPk :=
    (of_decide_eq_true hAuth).1.trans (migrationToyWire_legacyPkOf_eq_some hPk).symm
  accepted_witness_owns st _ w _ _ hRun _ :=
    MigrationExecution.run_checks_actual_lanes w (MigrationExecution.honestCircuit st) hRun

/-- The honest raw submission is accepted by the toy registry from the empty ledger and mints
    the enrolled entitlement `100`. -/
theorem migrationToy_honest_submission_accepted :
    ∃ ledger' : MigrationExecution.Ledger,
      (rawSettlementMachine migrationToyWire migrationToySnapshot migrationToyVerify
        MigrationExecution.honestCircuit).step ⟨[]⟩ MigrationExecution.honestSubmission =
      some (ledger', ⟨migrationToyWire.claimOf
        MigrationExecution.honestSubmission.statement.nullifier
        MigrationExecution.honestSubmission.statement, 100⟩) := by
  have hRun := ((MigrationExecution.settle_accepted_iff (fun _ (_ : Unit) => true)
    MigrationExecution.honestCircuit ⟨[]⟩ MigrationExecution.honestSubmission).mp
    MigrationExecution.settlement_acceptance_witness).2.2
  have hAcc : (MigrationExecution.settle migrationToyVerify MigrationExecution.honestCircuit
      ⟨[]⟩ MigrationExecution.honestSubmission).2 = .accepted :=
    (MigrationExecution.settle_accepted_iff migrationToyVerify MigrationExecution.honestCircuit
      ⟨[]⟩ MigrationExecution.honestSubmission).mpr
      ⟨(by intro h; cases h),
       (by unfold migrationToyVerify; exact decide_eq_true ⟨rfl, rfl, rfl⟩), hRun⟩
  have hPk : migrationToyWire.legacyPkOf
      MigrationExecution.honestSubmission.statement.legacyCommitment =
      some MigrationExecution.honestSubmission.statement.nullifier := by
    show (if MigrationExecution.honestSubmission.statement.legacyCommitment =
        MigrationExecution.honestSubmission.statement.legacyCommitment then
      some MigrationExecution.honestSubmission.statement.nullifier else none) = _
    simp only [↓reduceIte]
  have hEnt : Spec.EnrolledSnapshot.entitlement migrationToySnapshot
      MigrationExecution.honestSubmission.statement.nullifier = some 100 := by
    simp only [migrationToySnapshot, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hAd : rawSettlementAdmit migrationToyWire migrationToySnapshot
      MigrationExecution.honestSubmission.statement =
      some (MigrationExecution.honestSubmission.statement.nullifier, 100) := by
    unfold rawSettlementAdmit
    rw [hPk]
    show (match Spec.EnrolledSnapshot.entitlement migrationToySnapshot
        MigrationExecution.honestSubmission.statement.nullifier with
      | none => none
      | some amount => some (MigrationExecution.honestSubmission.statement.nullifier, amount)) = _
    rw [hEnt]
  refine ⟨(MigrationExecution.settle migrationToyVerify MigrationExecution.honestCircuit ⟨[]⟩
    MigrationExecution.honestSubmission).1, ?_⟩
  show rawSettlementStep migrationToyWire migrationToySnapshot migrationToyVerify
    MigrationExecution.honestCircuit ⟨[]⟩ MigrationExecution.honestSubmission = _
  unfold rawSettlementStep
  rw [hAd]
  show settlementReceipt _ _ (MigrationExecution.settle migrationToyVerify
    MigrationExecution.honestCircuit ⟨[]⟩ MigrationExecution.honestSubmission).2 = _
  rw [hAcc]
  rfl

/-- `#tooth` A forged raw submission to the toy registry under any nullifier other than the
    derived one is rejected in every ledger, whatever its commitment, destination and lanes. -/
theorem tooth_migrationToy_forged_nullifier_rejected
    (ledger : MigrationExecution.Ledger) (sub : MigrationExecution.Submission Unit)
    (hForged : ¬ (sub.statement.nullifier =
      MigrationExecution.honestSubmission.statement.nullifier)) :
    (rawSettlementMachine migrationToyWire migrationToySnapshot migrationToyVerify
      MigrationExecution.honestCircuit).step ledger sub = none := by
  cases hS : (rawSettlementMachine migrationToyWire migrationToySnapshot migrationToyVerify
      MigrationExecution.honestCircuit).step ledger sub with
  | none => rfl
  | some pair =>
    obtain ⟨ledger', out⟩ := pair
    obtain ⟨_, _, _, _, hAuth, _⟩ := rawSettlement_accepted_decodes migrationToyWire
      migrationToySnapshot migrationToyVerify MigrationExecution.honestCircuit hS
    exact absurd (of_decide_eq_true hAuth).1 hForged

/-! ## 6. Unified Curve-Ownership Settlement (`dlogOwnershipScheme` ↔ `rawSettlementMachine`) -/

/-- ZKBoo 2-of-3 discrete-log + destination authorization proof for curve-ownership settlement. -/
structure DlogSettlementAuth where
  e1 : Fin 3
  e2 : Fin 3
  opened1 : Nat × Nat
  opened2 : Nat × Nat
  authorizedDest : BitVec 256
  deriving DecidableEq, Repr

/-- Extract the reconstructed scalar `zkbooReconstructScalar ord s0 s1 s2` from a `DlogSettlementAuth`. -/
def DlogSettlementAuth.reconstructScalar (ord : Nat) (auth : DlogSettlementAuth) : Nat :=
  let (s0, s1, s2) := Qsag.extractThreeShares auth.e1 auth.e2 auth.opened1 auth.opened2
  Qsag.zkbooReconstructScalar ord s0 s1 s2

/-- Canonical `SettlementWire` for curve-ownership migration over a `PrimeSubgroup C G ord`:
    reads `(reconstructScalar ord auth, destinationBytes auth.authorizedDest)` strictly from `auth`
    (never from `statement.destination`). -/
def dlogSettlementWire (ord : Nat)
    (legacyPkOf : List UInt8 → Option Qsag.SwPoint)
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64) :
    SettlementWire Qsag.SwPoint DlogOwnershipWitness DlogSettlementAuth where
  legacyPkOf := legacyPkOf
  destinationBytes := destinationBytes
  destinationBytes_injective := hDestInj
  extractWitness auth _ := ⟨auth.reconstructScalar ord, destinationBytes auth.authorizedDest⟩
  migrationDomain := migrationDomain
  epoch := epoch

/-- Curve-ownership settlement authorization verifier: checks distinct ZKBoo challenges `e1 ≠ e2`,
    campaign `(migrationDomain, epoch)`, destination authorization `auth.authorizedDest = st.destination`,
    nullifier derivation `st.nullifier = deriveNullifier pk`, and discrete-log relation
    `0 < sk < ord ∧ grp.smul sk = pk`. -/
def dlogSettlementVerify {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option Qsag.SwPoint)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (st : MigrationExecution.Statement) (auth : DlogSettlementAuth) : Bool :=
  match legacyPkOf st.legacyCommitment with
  | none => false
  | some pk =>
    let sk := auth.reconstructScalar ord
    decide (auth.e1 ≠ auth.e2 ∧
      st.migrationDomain = migrationDomain ∧
      st.epoch = epoch ∧
      auth.authorizedDest = st.destination ∧
      st.nullifier = deriveNullifier pk ∧
      0 < sk ∧ sk < ord ∧ grp.smul sk = pk)

/-- **`SettlementCircuitSound` for Unified Curve-Ownership Settlement (`dlogSettlement_circuitSound`)**:
    Bridges `dlogOwnershipScheme grp deriveNullifier hInj` (Half A) directly into
    `SettlementCircuitSound` (Half B) over any `PrimeSubgroup C G ord`! -/
theorem dlogSettlement_circuitSound {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (legacyPkOf : List UInt8 → Option Qsag.SwPoint)
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) :
    SettlementCircuitSound
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
      (dlogOwnershipScheme grp deriveNullifier hInj)
      (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
      compile where
  authorization_campaign st auth hAuth := by
    unfold dlogSettlementVerify at hAuth
    cases hPk : legacyPkOf st.legacyCommitment with
    | none => rw [hPk] at hAuth; cases hAuth
    | some pk =>
      rw [hPk] at hAuth
      have hDec := of_decide_eq_true hAuth
      exact ⟨hDec.2.1, hDec.2.2.1⟩
  accepted_nullifier_derived st auth _ pk hAuth _ hPk := by
    have hPk' : legacyPkOf st.legacyCommitment = some pk := hPk
    unfold dlogSettlementVerify at hAuth
    rw [hPk'] at hAuth
    exact (of_decide_eq_true hAuth).2.2.2.2.1
  accepted_witness_owns st auth _ pk hAuth _ hPk := by
    have hPk' : legacyPkOf st.legacyCommitment = some pk := hPk
    unfold dlogSettlementVerify at hAuth
    rw [hPk'] at hAuth
    have hDec := of_decide_eq_true hAuth
    exact ⟨hDec.2.2.2.2.2.1, hDec.2.2.2.2.2.2.1, hDec.2.2.2.2.2.2.2,
      congrArg destinationBytes hDec.2.2.2.1⟩

/-- **Unified Forward Simulation (`dlogSettlement_dataRefines_idealMigrate`)**:
    `rawSettlementMachine` parameterized by `dlogSettlementWire` and `dlogSettlementVerify` refines
    `Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj) snapshot` via
    `Spec.DataRefines`! -/
def dlogSettlement_dataRefines_idealMigrate {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Spec.Digest256)
    (hInj : ∀ {pk₁ pk₂ : Qsag.SwPoint}, deriveNullifier pk₁ = deriveNullifier pk₂ → pk₁ = pk₂)
    (legacyPkOf : List UInt8 → Option Qsag.SwPoint)
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot Qsag.SwPoint) :
    Spec.DataRefines
      (rawSettlementMachine
        (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
        snapshot
        (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
        compile)
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier hInj) snapshot)
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch).decode
      id :=
  rawSettlement_dataRefines_idealMigrate
    (dlogSettlement_circuitSound grp deriveNullifier hInj legacyPkOf destinationBytes hDestInj
      migrationDomain epoch compile)
    snapshot

/-- **`#tooth` Destination Tampering Rejected by `dlogSettlementMachine`
    (`tooth_dlogSettlement_destination_tamper_rejected`)**:
    Mutating `sub.statement.destination` to `dest' ≠ sub.authorization.authorizedDest` while
    replaying the owner's ZKBoo shares and RSS witness lanes causes `rawSettlementMachine` to
    reject (`= none`) in every ledger! -/
theorem tooth_dlogSettlement_destination_tamper_rejected
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.SwPoint → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option Qsag.SwPoint)
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot Qsag.SwPoint)
    (ledger : MigrationExecution.Ledger)
    (sub : MigrationExecution.Submission DlogSettlementAuth)
    (hTamper : sub.authorization.authorizedDest ≠ sub.statement.destination) :
    (rawSettlementMachine
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
      snapshot
      (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
      compile).step ledger sub = none := by
  cases hS : (rawSettlementMachine
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
      snapshot
      (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
      compile).step ledger sub with
  | none => rfl
  | some pair =>
    obtain ⟨_, hPk, _, _, hAuth, _⟩ := rawSettlement_accepted_decodes
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
      snapshot (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
      compile hS
    have hPk' : legacyPkOf sub.statement.legacyCommitment = some pair.2.claim.legacyPk := hPk
    unfold dlogSettlementVerify at hAuth
    rw [hPk'] at hAuth
    exact absurd (of_decide_eq_true hAuth).2.2.2.1 hTamper

/-- Encode `SwPoint` on `secp7Mod43` (`x, y < 43`) injectively into a 256-bit nullifier digest
    tagged by `NULLIFIER_DOMAIN`. -/
def secp7Mod43Nullifier : Qsag.SwPoint → Spec.Digest256
  | none => 0#256
  | some (x, y) =>
    BitVec.ofNat 256 (1 + (x % 64) * 2 + (y % 64) * 128 + Qsag.NULLIFIER_DOMAIN.toNat * 16384)

/-- Decode a 2-byte compressed point `[x, y]` with `x < 43, y < 43`. -/
def secp7Mod43DecodePk : List UInt8 → Option Qsag.SwPoint
  | [bx, by_] =>
    if bx.toNat < 43 ∧ by_.toNat < 43 then some (some (bx.toNat, by_.toNat)) else none
  | _ => none

/-- **Concrete End-to-End Curve Settlement Witness (`secp7Mod43_dlogSettlement_honest_accepted`)**:
    Instantiates `rawSettlementMachine` on the concrete elliptic curve `secp7Mod43_primeSubgroup`
    (`y² = x³ + 7` over `ℤ/43`, generator `G = (2, 12)` of prime order `31`) with enrolled legacy
    key `[2]G = (7, 7)` (ZKBoo scalar shares `(1, 1, 0)` reconstructing `sk = 2`), executing the
    actual `MigrationExecution.honestCircuit` and minting the enrolled entitlement! -/
theorem secp7Mod43_dlogSettlement_honest_accepted :
    let pk2 : Qsag.SwPoint := some (7, 7)
    let wire := dlogSettlementWire 31 secp7Mod43DecodePk
      (fun d => List.replicate d.toNat 0)
      (fun {d₁ d₂} h => by
        have hLen := congrArg List.length h
        rw [List.length_replicate, List.length_replicate] at hLen
        exact BitVec.eq_of_toNat_eq hLen)
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let snap : Spec.EnrolledSnapshot Qsag.SwPoint := [(pk2, 250)]
    let stmt : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [7, 7]
        nullifier := secp7Mod43Nullifier pk2 }
    let auth : DlogSettlementAuth :=
      ⟨0, 1, (1, 1), (1, 0), stmt.destination⟩
    let sub : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt, auth, MigrationExecution.honestSubmission.witness⟩
    let compile := fun (_ : MigrationExecution.Statement) =>
      MigrationExecution.honestCircuit MigrationExecution.honestSubmission.statement
    ∃ ledger' : MigrationExecution.Ledger,
      (rawSettlementMachine wire snap
        (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
          MigrationExecution.honestSubmission.statement.migrationDomain
          MigrationExecution.honestSubmission.statement.epoch)
        compile).step ⟨[]⟩ sub =
      some (ledger', ⟨wire.claimOf pk2 stmt, 250⟩) := by
  dsimp only
  let pk2 : Qsag.SwPoint := some (7, 7)
  let wire := dlogSettlementWire 31 secp7Mod43DecodePk
    (fun d => List.replicate d.toNat 0)
    (fun {d₁ d₂} h => by
      have hLen := congrArg List.length h
      rw [List.length_replicate, List.length_replicate] at hLen
      exact BitVec.eq_of_toNat_eq hLen)
    MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch
  let snap : Spec.EnrolledSnapshot Qsag.SwPoint := [(pk2, 250)]
  let stmt : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [7, 7]
      nullifier := secp7Mod43Nullifier pk2 }
  let auth : DlogSettlementAuth := ⟨0, 1, (1, 1), (1, 0), stmt.destination⟩
  let sub : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt, auth, MigrationExecution.honestSubmission.witness⟩
  let compile := fun (_ : MigrationExecution.Statement) =>
    MigrationExecution.honestCircuit MigrationExecution.honestSubmission.statement
  have hRunOrig := ((MigrationExecution.settle_accepted_iff (fun _ (_ : Unit) => true)
    MigrationExecution.honestCircuit ⟨[]⟩ MigrationExecution.honestSubmission).mp
    MigrationExecution.settlement_acceptance_witness).2.2
  have hPk2Smul : Qsag.secp7Mod43_primeSubgroup.smul 2 = pk2 := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.2.2.1
  have hDecPk : secp7Mod43DecodePk [7, 7] = some pk2 := by decide
  have hSkEq : auth.reconstructScalar 31 = 2 := by
    unfold DlogSettlementAuth.reconstructScalar
    dsimp only [auth]
    rw [Qsag.extractThreeShares_zero_one, Qsag.zkbooReconstructScalar_eq]
    decide
  have hVerOk : dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier
      secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch stmt auth = true := by
    unfold dlogSettlementVerify
    cases hD : secp7Mod43DecodePk stmt.legacyCommitment with
    | none =>
      have hComm : stmt.legacyCommitment = [7, 7] := rfl
      rw [hComm, hDecPk] at hD
      cases hD
    | some pk =>
      have hComm : stmt.legacyCommitment = [7, 7] := rfl
      rw [hComm, hDecPk] at hD
      injection hD with hPkEq
      subst hPkEq
      dsimp only
      rw [hSkEq, hPk2Smul]
      apply decide_eq_true_eq.mpr
      exact ⟨by decide, rfl, rfl, rfl, rfl, by decide, by decide, rfl⟩
  have hAcc : (MigrationExecution.settle
      (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch)
      compile ⟨[]⟩ sub).2 = .accepted :=
    (MigrationExecution.settle_accepted_iff _ compile ⟨[]⟩ sub).mpr
      ⟨(by intro h; cases h), hVerOk, hRunOrig⟩
  have hEnt : Spec.EnrolledSnapshot.entitlement snap pk2 = some 250 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hAd : rawSettlementAdmit wire snap stmt = some (pk2, 250) := by
    unfold rawSettlementAdmit
    change (match secp7Mod43DecodePk [7, 7] with
      | none => none
      | some pk =>
        match Spec.EnrolledSnapshot.entitlement snap pk with
        | none => none
        | some amount => some (pk, amount)) = some (pk2, 250)
    rw [hDecPk]
    dsimp only
    rw [hEnt]
  refine ⟨(MigrationExecution.settle
      (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch)
      compile ⟨[]⟩ sub).1, ?_⟩
  show rawSettlementStep wire snap _ compile ⟨[]⟩ sub = _
  unfold rawSettlementStep
  rw [hAd]
  show settlementReceipt _ _ (MigrationExecution.settle _ compile ⟨[]⟩ sub).2 = _
  rw [hAcc]
  rfl

#verify_constructive
  Qsag.Top.legacy_curve_primality_extraction_and_ideal_migration_chain
  Qsag.Top.active_migration_ceremony_qrom_and_gf2pow128_chain
  Qsag.Top.migration_bit_check_staged_count_numerator_63
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.tooth_dlogOwnership_rejects_destination_swap
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.rawSettlement_accepted_decodes
  Qsag.Top.rawSettlement_rejected_ledger_unchanged
  Qsag.Top.rawSettlement_accepted_ownership
  Qsag.Top.rawSettlement_trace_simulated
  Qsag.Top.rawSettlement_trace_ownership_nodup_conservation
  Qsag.Top.tooth_rawSettlement_undecodable_submission_rejected
  Qsag.Top.tooth_rawSettlement_unenrolled_submission_rejected
  Qsag.Top.tooth_rawSettlement_receipt_destination_not_substituted
  Qsag.Top.tooth_rawSettlement_resubmission_other_destination_rejected
  Qsag.Top.migrationToy_circuitSound
  Qsag.Top.migrationToy_honest_submission_accepted
  Qsag.Top.tooth_migrationToy_forged_nullifier_rejected
  Qsag.Top.dlogSettlement_circuitSound
  Qsag.Top.tooth_dlogSettlement_destination_tamper_rejected
  Qsag.Top.secp7Mod43_dlogSettlement_honest_accepted

#tooth_pair Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar vs
  Qsag.Top.tooth_dlogOwnership_rejects_destination_swap
#tooth_pair Qsag.Top.secp7Mod43_dlogSettlement_honest_accepted vs
  Qsag.Top.tooth_dlogSettlement_destination_tamper_rejected

#tooth_pair Qsag.Top.rawSettlement_accepted_decodes vs
  Qsag.Top.tooth_rawSettlement_undecodable_submission_rejected
#tooth_pair Qsag.Top.rawSettlement_trace_simulated vs
  Qsag.Top.tooth_rawSettlement_unenrolled_submission_rejected
#tooth_pair Qsag.Top.rawSettlement_accepted_ownership vs
  Qsag.Top.tooth_rawSettlement_receipt_destination_not_substituted
#tooth_pair Qsag.Top.rawSettlement_trace_ownership_nodup_conservation vs
  Qsag.Top.tooth_rawSettlement_resubmission_other_destination_rejected
#tooth_pair Qsag.Top.migrationToy_honest_submission_accepted vs
  Qsag.Top.tooth_migrationToy_forged_nullifier_rejected

end Qsag.Top
end
