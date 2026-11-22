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
   both parameterized by `StagesSound` in `migration_bit_check_staged_count_numerator_63` and with
   `StagesSound` discharged unconditionally on `MigrationExecution.rustBitStageStep` via
   `MigrationExecution.rustBitCheckStages_sound` in `migration_bit_check_concrete_bound_63`), QROM
   scaling arithmetic, and five-way `𝔽_{2^{128}}` multiplication equivalence
   (`ActiveMigrationZeroTest`, `Math.Gf2Pow128`),
5. The destination-bound discrete-log instance `dlogOwnershipScheme` of `Spec.LegacyOwnershipScheme`
   over finite canonical curve keys `CanonicalSwPk C` (`x < C.p`, `y < C.p`, `C.onCurve = true`),
   with no injectivity hypothesis on the nullifier; witness `DlogOwnershipWitness` binding
   `authorizedDest = claim.pqDestinationPk`, paired with `tooth_dlogOwnership_rejects_destination_swap`.
   The scheme is parameterised by a `PrimeSubgroup`. The only `PrimeSubgroup` constructed in the
   tree is `secp7Mod43_primeSubgroup`: the toy curve `y² = x³ + 7` over `ℤ/43` with a generator of
   order `31`. `secp256k1_primeSubgroup`, `pallas_primeSubgroup` and `bls381_primeSubgroup` are
   functions of a `PrimeOrderGroup` hypothesis (closure, additivity, order and exactness of the
   generator) that is proved for none of those curves, so nothing in this module is instantiated
   at secp256k1, Pallas or BLS12-381.
6. The settlement registry as a machine over raw `MigrationExecution.Submission`s
   (`rawSettlementMachine`: snapshot admission, then `MigrationExecution.settle`); its
   `Spec.DataRefines` forward simulations into `Spec.idealMigrateMachine` and
   `Spec.idealKeyMigrateMachine`, given `SettlementCircuitSound`
   (`rawSettlement_dataRefines_idealMigrate`, `rawSettlement_dataRefines_idealKeyMigrate`); and the
   multi-turn dichotomy "every honest enrolled submission settles, or two enrolled keys collide
   under the nullifier" (`rawSettlement_schedule_refines_or_nullifierCollision`), with no
   injectivity hypothesis on the nullifier.
7. The discrete-log instance of item 6 (`dlogSettlementWire`, `dlogSettlementVerify`,
   `dlogSettlement_circuitSound`, `dlogSettlement_dataRefines_idealMigrate`,
   `dlogSettlement_schedule_refines_or_nullifierCollision`), paired with the single-challenge ZKBoo
   commitment verifier and special-soundness bridge (`SingleChallengeZkBooProof`,
   `singleChallengeZkBooVerify`, `singleChallengeZkBoo_two_transcript_extract_or_collision`,
   `tooth_singleChallengeZkBoo_hides_scalar`). What `DlogSettlementAuth` models: an authorization
   that already carries the opened views for two distinct ZKBoo challenges (the output of the
   2-transcript special-soundness knowledge extractor), from which `dlogSettlementVerify`
   reconstructs the scalar and checks `grp.smul sk = pk`. By contrast, `SingleChallengeZkBooProof`
   carries one challenge `e : Fin 3`, one opened share pair, and three share commitments: a single
   accepted proof information-theoretically hides `sk` (`tooth_singleChallengeZkBoo_hides_scalar`),
   while two accepted proofs on distinct challenges `e1 ≠ e2` with matching share commitments
   constructively yield a verifying `DlogSettlementAuth` or an explicit share-commitment collision
   (`singleChallengeZkBoo_two_transcript_extract_or_collision`). `dlogSettlement_circuitSound` does
   not use the compiled circuit or its run, and nothing here states that a compiled circuit enforces
   the discrete-log relation. One joint instance is exhibited, on the toy curve:
   `secp7Mod43_dlogSettlement_complete_refinement_witness` (two enrolled keys, three submissions;
   its circuit is the lane well-formedness circuit of `MigrationExecution.honestSubmission` for
   every statement). `bls381_dlogSettlement_refines_or_nullifierCollision` is the dichotomy over
   BLS12-381 coordinates, conditional on a `PrimeOrderGroup` hypothesis for `bls381G1`.
8. `zk-Hem v2` R1CS migration (`ZkHemV2Migration`): `production_curves_all_certified_prime`
   (primality of the twelve base-field and scalar-order moduli; integers only, no group-order
   statement), `zkHemV2_r1cs_migration_extract_or_qrom_128_break` and
   `zkHemV2_r1cs_migration_trace_conservation_and_nodup` for `zkHemV2MigrationMachine` (an
   uninterpreted `verifyProof`, snapshot and nullifier checks, `NullifierRegistry.register`).
   Standing hypotheses of these two: `hCodeSound` / `ZkHemV2ExtractorSound` (the extractor's
   output owns the key; no extractor is constructed), a `WhirScheduleCert` for
   `ZkHemV2Cert.zkHemV2ProdSched logCells` (none is constructed for a deployed size), and the
   Merkle collision bound `merkle400QromBound Q`. `realCurveR1csScheme` is parameterised by the
   R1CS shape and public-input map; no compiled relation of `crates/qsag-migrate` is instantiated.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealMigrate
public import Qsag.Math.CurvePrimeCerts
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Primality
public import Qsag.Protocol.Migration.PallasAndBlsMigration
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
public import Qsag.Protocol.Migration.HdToprfAndMigrationSecurity
public import Qsag.Protocol.Migration.ZkHemV2Migration
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

open Qsag.MigrationExecution in
/-- **Unconditional concrete staged bit-check bound at `BIT_CHECK_NUMERATOR = 63`
    (`migration_bit_check_concrete_bound_63`).**
    Specializes `migration_bit_check_staged_count_numerator_63` to the concrete `outer_mpc.rs`
    13-stage transition `rustBitStageStep` (`7` degree-1 weight stages + `6` degree-3 ternary
    sumcheck rounds) and discharges `StagesSound` unconditionally via `rustBitCheckStages_sound`. -/
theorem migration_bit_check_concrete_bound_63
    (p : StagedProver RustBitStageMsg (FoldProver rustBitCheckHalvingRounds)
      rustBitCheckStageNumerators)
    (cl : RustBitStageClaim) (hErr : (rustBitStageEmbed cl).err ≠ 0#128) :
    StagesSound productionFoldCoins rustBitStageStep
      (fun s => decide ((rustBitStageEmbed s).err ≠ 0#128)) rustBitCheckStageNumerators ∧
    rustBitCheckStageNumerators.sum + 2 * rustBitCheckHalvingRounds + 2 = 63 ∧
    ((stagedCoinVectors productionFoldCoins
        (coinVectors productionFoldCoins productionBaseCoins rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators).filter
      (stagedAccepts rustBitStageStep
        (fun q c coins =>
          sacrificeAccepts rustBitCheckHalvingRounds q (rustBitStageEmbed c) coins)
        rustBitCheckStageNumerators p cl)).length * (2 ^ 128 - 1) ≤
      BIT_CHECK_NUMERATOR *
        (stagedCoinVectors productionFoldCoins
          (coinVectors productionFoldCoins productionBaseCoins rustBitCheckHalvingRounds)
          rustBitCheckStageNumerators).length ∧
    stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      63 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))) :=
  let hSound := rustBitCheckStages_sound productionFoldCoins productionFoldCoins_nodup
  let hSpec := migration_bit_check_staged_count_numerator_63
    productionFoldCoins productionBaseCoins productionFoldCoins_nodup productionBaseCoins_nodup
    rustBitCheckHalvingRounds rustBitStageStep rustBitStageEmbed rustBitCheckStageNumerators
    hSound p cl hErr
  ⟨hSound, hSpec.2.1, rust_bit_check_63_concrete_accepting_coins_bound p cl hErr, hSpec.2.2⟩

/-! ## 3. Destination-Bound Discrete-Log Ownership Instance of `Spec.LegacyOwnershipScheme` -/

/-- Destination-bound discrete-log ownership witness: pairs the canonical curve scalar `scalar`
    with the owner-authorized destination bytes `authorizedDest`. -/
structure DlogOwnershipWitness where
  scalar : Nat
  authorizedDest : Qsag.Spec.Bytes
  deriving DecidableEq, Repr

/-- Discrete-log ownership over finite canonical curve keys `CanonicalSwPk C` (`x < C.p`, `y < C.p`,
    `C.onCurve = true`, cardinality `≤ C.p²`) in a prime-order subgroup `PrimeSubgroup`. The only
    constructed `PrimeSubgroup` is `secp7Mod43_primeSubgroup` (toy curve over `ℤ/43`, order `31`);
    `secp256k1_primeSubgroup`, `pallas_primeSubgroup` and `bls381_primeSubgroup` each take the
    group laws of their generator as a hypothesis that is not proved in the tree.
    `ownsKey pk w claim` is `0 < w.scalar < ord ∧ grp.smul w.scalar = pk.toSwPoint` together with
    `w.authorizedDest = claim.pqDestinationPk`. No injectivity of `deriveNullifier` is assumed. -/
def dlogOwnershipScheme {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Qsag.Spec.Digest256) :
    Qsag.Spec.LegacyOwnershipScheme (Qsag.CanonicalSwPk C) DlogOwnershipWitness where
  ownsKey pk w claim :=
    0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = pk.toSwPoint ∧
      w.authorizedDest = claim.pqDestinationPk
  checkOwnership pk w claim :=
    decide (0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = pk.toSwPoint ∧
      w.authorizedDest = claim.pqDestinationPk)
  check_iff _ _ _ := decide_eq_true_iff
  deriveNullifier := deriveNullifier

/-- A claim accepted by the ideal machine over `dlogOwnershipScheme` carries the unique canonical
    discrete logarithm of a canonically bounded curve key (`x < C.p`, `y < C.p`), binds the
    authorized destination, and mints that key's entitlement (with zero injectivity hypothesis). -/
theorem dlogOwnership_accepted_claim_has_unique_scalar
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Qsag.Spec.Digest256)
    (snapshot : Qsag.Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    {st st' : Qsag.Spec.IdealMigrateState (Qsag.CanonicalSwPk C)}
    {claim : Qsag.Spec.MigrationClaim (Qsag.CanonicalSwPk C)} {w : DlogOwnershipWitness}
    {out : Qsag.Spec.MigrationReceipt (Qsag.CanonicalSwPk C)}
    (hStep : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier)
      snapshot).step st (claim, w) = some (st', out)) :
    Qsag.Spec.EnrolledEntitlement snapshot claim.legacyPk out.amount ∧
    claim.nullifier = deriveNullifier claim.legacyPk ∧
    w.authorizedDest = claim.pqDestinationPk ∧
    (claim.legacyPk.x < C.p ∧ claim.legacyPk.y < C.p) ∧
    (0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = claim.legacyPk.toSwPoint) ∧
    ∀ sk' : Nat, sk' < ord → grp.smul sk' = claim.legacyPk.toSwPoint → sk' = w.scalar := by
  obtain ⟨hValid, _, _, _⟩ :=
    (Qsag.Spec.idealMigrateMachine_step_eq_some_iff _ snapshot st st' claim w out).mp hStep
  obtain ⟨hEnt, hNull, hOwn⟩ := hValid
  have hOwn' : 0 < w.scalar ∧ w.scalar < ord ∧ grp.smul w.scalar = claim.legacyPk.toSwPoint ∧
      w.authorizedDest = claim.pqDestinationPk := hOwn
  have hb := claim.legacyPk.bounds
  exact ⟨hEnt, hNull, hOwn'.2.2.2, ⟨hb.1, hb.2.1⟩, ⟨hOwn'.1, hOwn'.2.1, hOwn'.2.2.1⟩,
    fun sk' hLt hSmul =>
      Qsag.canonical_legacy_scalar_unique grp hLt hOwn'.2.1 (hSmul.trans hOwn'.2.2.1.symm)⟩

/-- **`#tooth` Destination-Swap Replay Rejected by `dlogOwnershipScheme`
    (`tooth_dlogOwnership_rejects_destination_swap`)**:
    Any witness `w` authorized for `dest₁` is deterministically rejected by both `checkOwnership`
    and `idealMigrateMachine.step` when replayed on a claim naming `dest₂ ≠ dest₁`, even before the
    legacy key has been settled! -/
theorem tooth_dlogOwnership_rejects_destination_swap
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Qsag.Spec.Digest256)
    (pk : Qsag.CanonicalSwPk C)
    (snapshot : Qsag.Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    (st : Qsag.Spec.IdealMigrateState (Qsag.CanonicalSwPk C))
    (sk : Nat) (dest₁ dest₂ : Qsag.Spec.Bytes) (hSwap : dest₁ ≠ dest₂) :
    (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).step
      st (⟨pk, deriveNullifier pk, dest₂⟩, ⟨sk, dest₁⟩) = none := by
  cases hS : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier)
      snapshot).step st (⟨pk, deriveNullifier pk, dest₂⟩, ⟨sk, dest₁⟩) with
  | none => rfl
  | some pair =>
    obtain ⟨_, _, hDestEq, _, _, _⟩ :=
      dlogOwnership_accepted_claim_has_unique_scalar grp deriveNullifier snapshot hS
    exact absurd hDestEq hSwap

/-- Collision-branching ZKBoo claim liveness over `CanonicalSwPk C` (zero hash-injectivity
    assumption): the scalar extracted from two distinct `ZKBoo` openings for an enrolled, unsettled
    canonical key `pk` EITHER is accepted and mints `amount` OR exhibits an explicit
    `Spec.NullifierCollision` against a settled enrolled key `pk_prev ≠ pk`. -/
theorem zkboo_extracted_scalar_claims_enrolled_entitlement_or_collision
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Qsag.Spec.Digest256)
    (pk : Qsag.CanonicalSwPk C)
    (snapshot : Qsag.Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    {st : Qsag.Spec.IdealMigrateState (Qsag.CanonicalSwPk C)}
    (hReach : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier)
      snapshot).Reachable st)
    (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValidDlog : Qsag.ZkBooDlogCommitted grp pk.toSwPoint shares)
    {amount : Nat} (hEnrolled : Qsag.Spec.EnrolledEntitlement snapshot pk amount)
    (hUnclaimed : pk ∉ st.settledClaims.map (fun r => r.claim.legacyPk))
    (dest : Qsag.Spec.Bytes) :
    let (s0, s1, s2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1) (Qsag.zkbooOpenedPair shares e2)
    let sk := Qsag.zkbooReconstructScalar ord s0 s1 s2
    (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).step st
        (⟨pk, deriveNullifier pk, dest⟩, ⟨sk, dest⟩) =
      some ({ totalMigrated := st.totalMigrated + amount
              spentNullifiers := deriveNullifier pk :: st.spentNullifiers
              settledClaims := ⟨⟨pk, deriveNullifier pk, dest⟩, amount⟩ :: st.settledClaims },
            ⟨⟨pk, deriveNullifier pk, dest⟩, amount⟩) ∨
    ∃ pk_prev ∈ st.settledClaims.map (fun r => r.claim.legacyPk),
      pk_prev ∈ snapshot.map Prod.fst ∧
      Qsag.Spec.NullifierCollision deriveNullifier pk_prev pk := by
  have hExt := Qsag.zkboo_two_challenge_extraction_sound grp shares e1 e2 hNe hValidDlog
  revert hExt
  generalize Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1)
    (Qsag.zkbooOpenedPair shares e2) = triple
  obtain ⟨s0, s1, s2⟩ := triple
  intro hExt
  obtain ⟨hPos, hLt, hSmul, _⟩ := hExt
  exact Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts_or_collision
    (Qsag.Spec.idealMigrateMachine_reachable_inv _ snapshot hReach)
    ⟨hEnrolled, rfl, hPos, hLt, hSmul, rfl⟩ hUnclaimed

/-- Corollary under finite-snapshot `Spec.NullifierInjOn`: the `ZKBoo`-extracted scalar for an
    enrolled unsettled canonical key `pk` is accepted unconditionally and mints `amount`. -/
theorem zkboo_extracted_scalar_claims_enrolled_entitlement
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Qsag.Spec.Digest256)
    (pk : Qsag.CanonicalSwPk C)
    (snapshot : Qsag.Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    (hInj : Qsag.Spec.NullifierInjOn deriveNullifier (snapshot.map Prod.fst))
    {st : Qsag.Spec.IdealMigrateState (Qsag.CanonicalSwPk C)}
    (hReach : (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier)
      snapshot).Reachable st)
    (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (hNe : e1 ≠ e2)
    (hValidDlog : Qsag.ZkBooDlogCommitted grp pk.toSwPoint shares)
    {amount : Nat} (hEnrolled : Qsag.Spec.EnrolledEntitlement snapshot pk amount)
    (hUnclaimed : pk ∉ st.settledClaims.map (fun r => r.claim.legacyPk))
    (dest : Qsag.Spec.Bytes) :
    let (s0, s1, s2) := Qsag.extractThreeShares e1 e2 (Qsag.zkbooOpenedPair shares e1) (Qsag.zkbooOpenedPair shares e2)
    let sk := Qsag.zkbooReconstructScalar ord s0 s1 s2
    (Qsag.Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).step st
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
  exact Qsag.Spec.idealMigrateMachine_unclaimed_owner_accepts hInj
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

private theorem rawSettlementAdmit_of_decoded {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization} {snapshot : Spec.EnrolledSnapshot LegacyPk}
    {st : MigrationExecution.Statement} {pk : LegacyPk} {amount : Nat}
    (hPk : D.legacyPkOf st.legacyCommitment = some pk)
    (hEnt : Spec.EnrolledSnapshot.entitlement snapshot pk = some amount) :
    rawSettlementAdmit D snapshot st = some (pk, amount) := by
  unfold rawSettlementAdmit
  rw [hPk]
  show (match Spec.EnrolledSnapshot.entitlement snapshot pk with
    | none => none
    | some amount => some (pk, amount)) = some (pk, amount)
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

/-- Unconditional `Spec.DataRefines` from `rawSettlementMachine` into the pure key-indexed ideal
    machine `Spec.idealKeyMigrateMachine` (zero nullifier-injectivity assumptions). -/
def rawSettlement_dataRefines_idealKeyMigrate {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk) :
    Spec.DataRefines (rawSettlementMachine D snapshot verifyAuthorization compile)
      (Spec.idealKeyMigrateMachine scheme snapshot) D.decode id where
  Rel ledger a := ledger.spent = a.spentNullifiers ∧ a.Inv scheme snapshot
  absInit _ := Spec.IdealMigrateState.init
  init_ok hInit := by
    cases hInit
    exact ⟨(Spec.idealKeyMigrateMachine_init_iff scheme snapshot _).mpr rfl, rfl,
      Spec.IdealMigrateState.init_inv scheme snapshot⟩
  sim_visible {ledger ledger' a sub out j} hRel hStep hVis := by
    obtain ⟨a', hStepM, hSpent'⟩ :=
      (rawSettlement_dataRefines_idealMigrate S snapshot).sim_visible hRel.1 hStep hVis
    obtain ⟨a'', hStepK, hRelK⟩ :=
      (Spec.idealMigrate_dataRefines_idealKeyMigrate scheme snapshot).sim_visible
        ((Spec.idealMigrate_dataRefines_idealKeyMigrate_rel_iff scheme snapshot a a).mpr
          ⟨rfl, hRel.2⟩) hStepM rfl
    obtain ⟨hEqK, hInv'⟩ :=
      (Spec.idealMigrate_dataRefines_idealKeyMigrate_rel_iff scheme snapshot a' a'').mp hRelK
    subst hEqK
    exact ⟨a', hStepK, hSpent', hInv'⟩
  sim_internal {ledger ledger' a sub out} _ hStep hVis := by
    have hDec := (rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hStep).1
    rw [hVis] at hDec
    cases hDec
  sim_reject {ledger a sub} hRel hNone := by
    rw [rawSettlement_rejected_ledger_unchanged D snapshot verifyAuthorization compile hNone]
    exact hRel

/-- Predicate characterizing an honest raw submission for enrolled key `pk` with entitlement
    `amount`: `legacyCommitment` decodes to `pk`, `pk` is enrolled with `amount`, the authorization
    proof verifies, and the compiled circuit run accepts. -/
def HonestRawSubmission {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (sub : MigrationExecution.Submission Authorization) (pk : LegacyPk) (amount : Nat) : Prop :=
  D.legacyPkOf sub.statement.legacyCommitment = some pk ∧
  Spec.EnrolledEntitlement snapshot pk amount ∧
  verifyAuthorization sub.statement sub.authorization = true ∧
  MigrationExecution.run sub.witness (compile sub.statement) = .accepted

/-- Total multi-turn schedule runner over raw submissions, returning the final ledger and the
    accepted `(submission, receipt)` trace. -/
def runRawSettlementSchedule {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) :
    MigrationExecution.Ledger → List (MigrationExecution.Submission Authorization) →
      MigrationExecution.Ledger ×
        List (MigrationExecution.Submission Authorization × Spec.MigrationReceipt LegacyPk)
  | ledger, [] => (ledger, [])
  | ledger, sub :: rest =>
    match (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub with
    | some (ledger', out) =>
      let res := runRawSettlementSchedule D snapshot verifyAuthorization compile ledger' rest
      (res.1, (sub, out) :: res.2)
    | none =>
      runRawSettlementSchedule D snapshot verifyAuthorization compile
        ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep ledger sub) rest

theorem runRawSettlementSchedule_validTrace {LegacyPk Witness Authorization : Type}
    [DecidableEq LegacyPk]
    (D : SettlementWire LegacyPk Witness Authorization)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (verifyAuthorization : MigrationExecution.Statement → Authorization → Bool)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) :
    ∀ (ledger : MigrationExecution.Ledger)
      (subs : List (MigrationExecution.Submission Authorization)),
      let res := runRawSettlementSchedule D snapshot verifyAuthorization compile ledger subs
      (rawSettlementMachine D snapshot verifyAuthorization compile).ValidTrace ledger res.2 res.1
  | ledger, [] => .nil ledger
  | ledger, sub :: rest => by
    dsimp only [runRawSettlementSchedule]
    cases hS : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub with
    | some pair =>
      exact .accept hS
        (runRawSettlementSchedule_validTrace D snapshot verifyAuthorization compile pair.1 rest)
    | none =>
      exact .reject sub hS
        (runRawSettlementSchedule_validTrace D snapshot verifyAuthorization compile _ rest)

private theorem rawSettlement_schedule_complete_or_collision_aux
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk) :
    ∀ {ledger : MigrationExecution.Ledger} {a : Spec.IdealMigrateState LegacyPk}
      (subs : List (MigrationExecution.Submission Authorization)),
      ledger.spent = a.spentNullifiers →
      a.Inv scheme snapshot →
      let res := runRawSettlementSchedule D snapshot verifyAuthorization compile ledger subs
      (∀ sub ∈ subs, ∀ (pk : LegacyPk) (amount : Nat),
        HonestRawSubmission D snapshot verifyAuthorization compile sub pk amount →
          pk ∈ a.settledClaims.map (fun r => r.claim.legacyPk) ++
            res.2.map (fun io => io.2.claim.legacyPk)) ∨
      (∃ pk₁ pk₂ : LegacyPk,
        pk₁ ∈ snapshot.map Prod.fst ∧
        pk₂ ∈ snapshot.map Prod.fst ∧
        Spec.NullifierCollision scheme.deriveNullifier pk₁ pk₂)
  | _, _, [], _, _ => .inl (fun _ hMem => nomatch hMem)
  | ledger, a, sub :: rest, hRel, hInv => by
    dsimp only [runRawSettlementSchedule]
    cases hS : (rawSettlementMachine D snapshot verifyAuthorization compile).step ledger sub with
    | some pair =>
      obtain ⟨ledger', out⟩ := pair
      obtain ⟨hDecSub, hPkOut, _, _, _, _, _, _⟩ :=
        rawSettlement_accepted_decodes D snapshot verifyAuthorization compile hS
      obtain ⟨a', hStepM, hRel'⟩ :=
        (rawSettlement_dataRefines_idealMigrate S snapshot).sim_visible hRel hS hDecSub
      obtain ⟨hInv', _, _⟩ := Spec.idealMigrateMachine_step_preserves_inv hInv hStepM
      obtain ⟨_, _, _, hStA⟩ :=
        (Spec.idealMigrateMachine_step_eq_some_iff scheme snapshot a a' out.claim
          (D.extractWitness sub.authorization sub.witness) out).mp hStepM
      rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv' with
        hAllRest | hColl
      · left
        intro sub₀ hMem pk amount hHon
        rcases List.mem_cons.mp hMem with rfl | hInRest
        · have hEqPk : pk = out.claim.legacyPk :=
            Option.some.inj (hHon.1.symm.trans hPkOut)
          subst hEqPk
          exact List.mem_append_right _ (.head _)
        · have hIn := hAllRest sub₀ hInRest pk amount hHon
          rw [hStA] at hIn
          dsimp only [List.map] at hIn
          rcases List.mem_append.mp hIn with hSettledA' | hTrRest
          · rcases List.mem_cons.mp hSettledA' with rfl | hOld
            · exact List.mem_append_right _ (.head _)
            · exact List.mem_append_left _ hOld
          · exact List.mem_append_right _ (.tail _ hTrRest)
      · exact .inr hColl
    | none =>
      have hErr := rawSettlement_rejected_ledger_unchanged D snapshot verifyAuthorization compile hS
      cases hPk : D.legacyPkOf sub.statement.legacyCommitment with
      | none =>
        have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep
            ledger sub).spent = a.spentNullifiers := by rw [hErr]; exact hRel
        rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv with
          hAllRest | hColl
        · left
          intro sub₀ hMem pk amount hHon
          rcases List.mem_cons.mp hMem with rfl | hInRest
          · have hNone := hPk.symm.trans hHon.1
            cases hNone
          · exact hAllRest sub₀ hInRest pk amount hHon
        · exact .inr hColl
      | some pk =>
        cases hEnt : Spec.EnrolledSnapshot.entitlement snapshot pk with
        | none =>
          have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep
              ledger sub).spent = a.spentNullifiers := by rw [hErr]; exact hRel
          rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv with
            hAllRest | hColl
          · left
            intro sub₀ hMem pk' amount hHon
            rcases List.mem_cons.mp hMem with rfl | hInRest
            · have hEqPk : pk = pk' := Option.some.inj (hPk.symm.trans hHon.1)
              subst hEqPk
              have hEntSome : Spec.EnrolledSnapshot.entitlement snapshot pk = some amount := hHon.2.1
              rw [hEnt] at hEntSome
              exact nomatch hEntSome
            · exact hAllRest sub₀ hInRest pk' amount hHon
          · exact .inr hColl
        | some amount =>
          cases hVer : verifyAuthorization sub.statement sub.authorization with
          | false =>
            have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep
                ledger sub).spent = a.spentNullifiers := by rw [hErr]; exact hRel
            rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv with
              hAllRest | hColl
            · left
              intro sub₀ hMem pk' amount' hHon
              rcases List.mem_cons.mp hMem with rfl | hInRest
              · have hFalse := hVer.symm.trans hHon.2.2.1
                cases hFalse
              · exact hAllRest sub₀ hInRest pk' amount' hHon
            · exact .inr hColl
          | true =>
            by_cases hRun : MigrationExecution.run sub.witness (compile sub.statement) = .accepted
            · by_cases hSettled : pk ∈ a.settledClaims.map (fun r => r.claim.legacyPk)
              · have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep
                    ledger sub).spent = a.spentNullifiers := by rw [hErr]; exact hRel
                rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv with
                  hAllRest | hColl
                · left
                  intro sub₀ hMem pk' amount' hHon
                  rcases List.mem_cons.mp hMem with rfl | hInRest
                  · have hEqPk : pk = pk' := Option.some.inj (hPk.symm.trans hHon.1)
                    subst hEqPk
                    exact List.mem_append_left _ hSettled
                  · exact hAllRest sub₀ hInRest pk' amount' hHon
                · exact .inr hColl
              · right
                have hAd : rawSettlementAdmit D snapshot sub.statement = some (pk, amount) :=
                  rawSettlementAdmit_of_decoded hPk hEnt
                have hSpent : sub.statement.nullifier ∈ ledger.spent := by
                  cases (inferInstance : Decidable (sub.statement.nullifier ∈ ledger.spent)) with
                  | isTrue hIn => exact hIn
                  | isFalse hFresh =>
                    have hAcc : (MigrationExecution.settle verifyAuthorization compile ledger sub).2 =
                        .accepted :=
                      (MigrationExecution.settle_accepted_iff verifyAuthorization compile ledger
                        sub).mpr ⟨hFresh, hVer, hRun⟩
                    have hStepSome : (rawSettlementMachine D snapshot verifyAuthorization
                        compile).step ledger sub =
                        some ((MigrationExecution.settle verifyAuthorization compile ledger sub).1,
                          ⟨D.claimOf pk sub.statement, amount⟩) := by
                      show rawSettlementStep D snapshot verifyAuthorization compile ledger sub = _
                      unfold rawSettlementStep
                      rw [hAd]
                      show settlementReceipt _ _ (MigrationExecution.settle verifyAuthorization
                        compile ledger sub).2 = _
                      rw [hAcc]
                      rfl
                    rw [hS] at hStepSome
                    cases hStepSome
                have hNull := S.accepted_nullifier_derived sub.statement sub.authorization
                  sub.witness pk hVer hRun hPk
                rw [hRel, hInv.1] at hSpent
                obtain ⟨pk_prev, hpkPrev, hNullEq⟩ := List.exists_of_mem_map hSpent
                obtain ⟨r, hrMem, hrEq⟩ := List.exists_of_mem_map hpkPrev
                have hSnapPrev : pk_prev ∈ snapshot.map Prod.fst := by
                  rw [← hrEq]
                  exact List.mem_map_of_mem (f := Prod.fst)
                    (Spec.EnrolledEntitlement.mem (hInv.2.2.1 r hrMem).1)
                have hEnrPk : Spec.EnrolledEntitlement snapshot pk amount := hEnt
                have hSnapPk : pk ∈ snapshot.map Prod.fst :=
                  List.mem_map_of_mem (f := Prod.fst) (Spec.EnrolledEntitlement.mem hEnrPk)
                exact ⟨pk_prev, pk, hSnapPrev, hSnapPk,
                  fun hSame => hSettled (hSame ▸ hpkPrev), hNullEq.trans hNull⟩
            · have hRel' : ((rawSettlementMachine D snapshot verifyAuthorization compile).errStep
                  ledger sub).spent = a.spentNullifiers := by rw [hErr]; exact hRel
              rcases rawSettlement_schedule_complete_or_collision_aux S snapshot rest hRel' hInv with
                hAllRest | hColl
              · left
                intro sub₀ hMem pk' amount' hHon
                rcases List.mem_cons.mp hMem with rfl | hInRest
                · exact False.elim (hRun hHon.2.2.2)
                · exact hAllRest sub₀ hInRest pk' amount' hHon
              · exact .inr hColl

/-- **Collision-Branching Multi-Turn Refinement & Non-Blocking Completeness
    (`rawSettlement_schedule_refines_or_nullifierCollision`)**:
    With **ZERO** hash-injectivity assumption on `scheme.deriveNullifier`, executing any multi-turn
    schedule `subs` of raw submissions from the empty ledger EITHER:
    1. Projects onto admitted executions of BOTH `Spec.idealMigrateMachine` and the hash-free
       `Spec.idealKeyMigrateMachine`, satisfies ownership soundness, per-key non-double-claim,
       entitlement conservation, and `spent.Nodup`, AND settles every honest enrolled submission in
       `subs` without cross-key blocking, OR
    2. Constructively exhibits two distinct enrolled keys `pk₁ ≠ pk₂` (`pk₁, pk₂ ∈ snapshot.map Prod.fst`)
       colliding under `scheme.deriveNullifier` (`Spec.NullifierCollision`). -/
theorem rawSettlement_schedule_refines_or_nullifierCollision
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (subs : List (MigrationExecution.Submission Authorization)) :
    let res := runRawSettlementSchedule D snapshot verifyAuthorization compile ⟨[]⟩ subs
    ((Spec.idealMigrateMachine scheme snapshot).AdmitsTrace
        (Spec.projectTrace D.decode id res.2) ∧
      (Spec.idealKeyMigrateMachine scheme snapshot).AdmitsTrace
        (Spec.projectTrace D.decode id res.2) ∧
      (∀ io ∈ res.2, Spec.ValidLegacyOwnership scheme snapshot io.2.claim
        (D.extractWitness io.1.authorization io.1.witness) io.2.amount) ∧
      (res.2.map (fun io => io.2.claim.legacyPk)).Nodup ∧
      (res.2.map (fun io => io.2.amount)).sum ≤ Spec.EnrolledSnapshot.total snapshot ∧
      res.1.spent.Nodup ∧
      (∀ sub ∈ subs, ∀ (pk : LegacyPk) (amount : Nat),
        HonestRawSubmission D snapshot verifyAuthorization compile sub pk amount →
          pk ∈ res.2.map (fun io => io.2.claim.legacyPk))) ∨
    (∃ pk₁ pk₂ : LegacyPk,
      pk₁ ∈ snapshot.map Prod.fst ∧
      pk₂ ∈ snapshot.map Prod.fst ∧
      Spec.NullifierCollision scheme.deriveNullifier pk₁ pk₂) := by
  dsimp only
  have hTrC := runRawSettlementSchedule_validTrace D snapshot verifyAuthorization compile ⟨[]⟩ subs
  have hInitC : (rawSettlementMachine D snapshot verifyAuthorization compile).Init ⟨[]⟩ := rfl
  have hAdmC : (rawSettlementMachine D snapshot verifyAuthorization compile).AdmitsTrace
      (runRawSettlementSchedule D snapshot verifyAuthorization compile ⟨[]⟩ subs).2 :=
    ⟨⟨[]⟩, _, hInitC, hTrC⟩
  have hAdmM := (rawSettlement_dataRefines_idealMigrate S snapshot).preserve_admitsTrace hAdmC
  have hAdmK := (rawSettlement_dataRefines_idealKeyMigrate S snapshot).preserve_admitsTrace hAdmC
  have hSafety := rawSettlement_trace_ownership_nodup_conservation S snapshot hInitC hTrC
  rcases rawSettlement_schedule_complete_or_collision_aux S snapshot subs
      (a := Spec.IdealMigrateState.init) rfl (Spec.IdealMigrateState.init_inv scheme snapshot) with
    hComp | hColl
  · exact .inl ⟨hAdmM, hAdmK, hSafety.1, hSafety.2.1, hSafety.2.2.1, hSafety.2.2.2, hComp⟩
  · exact .inr hColl

/-- Finite-snapshot `Spec.NullifierInjOn` corollary of
    `rawSettlement_schedule_refines_or_nullifierCollision`. -/
theorem rawSettlement_schedule_complete_of_injOn
    {LegacyPk Witness Authorization : Type} [DecidableEq LegacyPk]
    {D : SettlementWire LegacyPk Witness Authorization}
    {scheme : Spec.LegacyOwnershipScheme LegacyPk Witness}
    {verifyAuthorization : MigrationExecution.Statement → Authorization → Bool}
    {compile : MigrationExecution.Statement → List MigrationExecution.Gate}
    (S : SettlementCircuitSound D scheme verifyAuthorization compile)
    (snapshot : Spec.EnrolledSnapshot LegacyPk)
    (hInj : Spec.NullifierInjOn scheme.deriveNullifier (snapshot.map Prod.fst))
    (subs : List (MigrationExecution.Submission Authorization)) :
    let res := runRawSettlementSchedule D snapshot verifyAuthorization compile ⟨[]⟩ subs
    (Spec.idealMigrateMachine scheme snapshot).AdmitsTrace
      (Spec.projectTrace D.decode id res.2) ∧
    (Spec.idealKeyMigrateMachine scheme snapshot).AdmitsTrace
      (Spec.projectTrace D.decode id res.2) ∧
    (∀ io ∈ res.2, Spec.ValidLegacyOwnership scheme snapshot io.2.claim
      (D.extractWitness io.1.authorization io.1.witness) io.2.amount) ∧
    (res.2.map (fun io => io.2.claim.legacyPk)).Nodup ∧
    (res.2.map (fun io => io.2.amount)).sum ≤ Spec.EnrolledSnapshot.total snapshot ∧
    res.1.spent.Nodup ∧
    (∀ sub ∈ subs, ∀ (pk : LegacyPk) (amount : Nat),
      HonestRawSubmission D snapshot verifyAuthorization compile sub pk amount →
        pk ∈ res.2.map (fun io => io.2.claim.legacyPk)) := by
  rcases rawSettlement_schedule_refines_or_nullifierCollision S snapshot subs with
    hOk | ⟨pk₁, pk₂, h₁, h₂, hNe, hEq⟩
  · exact hOk
  · exact absurd ((Spec.NullifierInjOn_iff _ _).mp hInj h₁ h₂ hEq) hNe

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

/-- Authorization format of the discrete-log settlement model: two challenges `e1`, `e2`, the
    opened pair of additive scalar shares for each, and the authorized destination.
    When `e1 ≠ e2` the two opened pairs contain all three shares, so the scalar is determined by
    the authorization (`DlogSettlementAuth.reconstructScalar`). This is the transcript pair that
    the special-soundness extractor of ZKBoo consumes, not a ZKBoo proof: a proof opens one
    challenge per repetition, and its verifier checks view consistency against commitments, which
    this structure does not contain. A submission in this model therefore discloses the scalar. -/
structure DlogSettlementAuth where
  e1 : Fin 3
  e2 : Fin 3
  opened1 : Nat × Nat
  opened2 : Nat × Nat
  authorizedDest : BitVec 256
  deriving DecidableEq, Repr

/-- The scalar `zkbooReconstructScalar ord s0 s1 s2` of the three shares read off the two opened
    pairs of a `DlogSettlementAuth` by `extractThreeShares`. -/
def DlogSettlementAuth.reconstructScalar (ord : Nat) (auth : DlogSettlementAuth) : Nat :=
  let (s0, s1, s2) := Qsag.extractThreeShares auth.e1 auth.e2 auth.opened1 auth.opened2
  Qsag.zkbooReconstructScalar ord s0 s1 s2

/-- Canonical `SettlementWire` for curve-ownership migration over finite canonical curve keys
    `CanonicalSwPk C` (`x < C.p`, `y < C.p`, `C.onCurve = true`):
    reads `(reconstructScalar ord auth, destinationBytes auth.authorizedDest)` strictly from `auth`
    (never from `statement.destination`). -/
def dlogSettlementWire {C : Qsag.SwCurve} (ord : Nat)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64) :
    SettlementWire (Qsag.CanonicalSwPk C) DlogOwnershipWitness DlogSettlementAuth where
  legacyPkOf := legacyPkOf
  destinationBytes := destinationBytes
  destinationBytes_injective := hDestInj
  extractWitness auth _ := ⟨auth.reconstructScalar ord, destinationBytes auth.authorizedDest⟩
  migrationDomain := migrationDomain
  epoch := epoch

/-- Authorization verifier of the discrete-log settlement model over `CanonicalSwPk C`: checks
    `e1 ≠ e2`, campaign `(migrationDomain, epoch)`, destination authorization
    `auth.authorizedDest = st.destination`, nullifier derivation `st.nullifier = deriveNullifier pk`,
    and, for the scalar `sk` reconstructed from the two opened pairs,
    `0 < sk < ord ∧ grp.smul sk = pk.toSwPoint`.
    The verifier recomputes the scalar and checks the discrete-log relation directly. It models
    "an accepted authorization yields an extracted witness" by putting the extractor's input in
    the authorization; it is not the verifier of a zero-knowledge proof and it checks no
    commitment, view or circuit. -/
def dlogSettlementVerify {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
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
      0 < sk ∧ sk < ord ∧ grp.smul sk = pk.toSwPoint)

private theorem dlogSettlementVerify_eq_true {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (migrationDomain : BitVec 256) (epoch : UInt64)
    {st : MigrationExecution.Statement} {auth : DlogSettlementAuth} {pk : Qsag.CanonicalSwPk C}
    (hPk : legacyPkOf st.legacyCommitment = some pk)
    (h : auth.e1 ≠ auth.e2 ∧
      st.migrationDomain = migrationDomain ∧
      st.epoch = epoch ∧
      auth.authorizedDest = st.destination ∧
      st.nullifier = deriveNullifier pk ∧
      0 < auth.reconstructScalar ord ∧ auth.reconstructScalar ord < ord ∧
      grp.smul (auth.reconstructScalar ord) = pk.toSwPoint) :
    dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch st auth = true := by
  unfold dlogSettlementVerify
  rw [hPk]
  exact decide_eq_true h

/-- `SettlementCircuitSound` for `dlogSettlementWire`, `dlogOwnershipScheme` and
    `dlogSettlementVerify`, for every `compile`.
    Proved: each of the three fields follows from `dlogSettlementVerify … = true` alone, because
    that verifier checks the campaign, the derived nullifier and the discrete-log relation of the
    scalar reconstructed from the authorization, and `dlogSettlementWire.extractWitness` returns
    that same scalar.
    Not used: the hypothesis `MigrationExecution.run w (compile st) = .accepted` of the fields
    `accepted_nullifier_derived` and `accepted_witness_owns`. `compile` is arbitrary and the
    witness lanes `w` play no role, so this is not a soundness statement about a compiled circuit.
    Assumed by the model: that an accepted authorization contains two openings under distinct
    challenges (`DlogSettlementAuth`), i.e. the special-soundness extractor has already run. No
    injectivity of `deriveNullifier` is assumed. -/
theorem dlogSettlement_circuitSound {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate) :
    SettlementCircuitSound
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
      (dlogOwnershipScheme grp deriveNullifier)
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

/-- Single-challenge ZKBoo proof for one repetition: carries one challenge `e : Fin 3`, the two
    opened shares `opened = (s_e, s_{(e+1) mod 3})` for that challenge, three 256-bit share
    commitments `shareCommits : Fin 3 → Spec.Digest256`, and `authorizedDest`. Unlike the
    post-extraction `DlogSettlementAuth`, a single proof leaves one of the three additive shares
    unopened (`tooth_singleChallengeZkBoo_hides_scalar`). -/
structure SingleChallengeZkBooProof where
  e : Fin 3
  opened : Nat × Nat
  shareCommits : Fin 3 → Spec.Digest256
  authorizedDest : BitVec 256

/-- Next ZKBoo party index `(e + 1) mod 3`. -/
def zkbooNextParty (e : Fin 3) : Fin 3 :=
  ⟨(e.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Single-challenge ZKBoo submission verifier: checks campaign `(migrationDomain, epoch)`,
    destination binding `pf.authorizedDest = st.destination`, nullifier derivation
    `st.nullifier = deriveNullifier pk`, and that the two opened shares match the commitments at
    `pf.e` and `zkbooNextParty pf.e` under `commitShare`. Never reconstructs the scalar or inspects
    the unopened third share. -/
def singleChallengeZkBooVerify {C : Qsag.SwCurve}
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (commitShare : Fin 3 → Nat → Spec.Digest256)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (st : MigrationExecution.Statement) (pf : SingleChallengeZkBooProof) : Bool :=
  match legacyPkOf st.legacyCommitment with
  | none => false
  | some pk =>
    decide (st.migrationDomain = migrationDomain ∧
      st.epoch = epoch ∧
      pf.authorizedDest = st.destination ∧
      st.nullifier = deriveNullifier pk ∧
      commitShare pf.e pf.opened.1 = pf.shareCommits pf.e ∧
      commitShare (zkbooNextParty pf.e) pf.opened.2 = pf.shareCommits (zkbooNextParty pf.e))

/-- **2-transcript special-soundness extractor bridge from `SingleChallengeZkBooProof` to
    `DlogSettlementAuth` (`singleChallengeZkBoo_two_transcript_extract_or_collision`).**
    Given two accepted single-challenge proofs `pf1` (challenge `0`) and `pf2` (challenge `1`) for
    statement `st` (`legacyPkOf` resolving to `pk`) with matching share commitments
    (`∀ i, pf2.shareCommits i = pf1.shareCommits i`) committed to a valid discrete-log sharing
    `shares` (`ZkBooDlogCommitted grp pk.toSwPoint shares`), EITHER:
    1. the assembled `DlogSettlementAuth` `⟨0, 1, pf1.opened, pf2.opened, pf1.authorizedDest⟩`
       passes `dlogSettlementVerify` and reconstructs the exact discrete-log scalar of `pk`, OR
    2. one of the opened shares exhibits an explicit `commitShare` collision against `shares`. -/
theorem singleChallengeZkBoo_two_transcript_extract_or_collision
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (commitShare : Fin 3 → Nat → Spec.Digest256)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    {st : MigrationExecution.Statement} {pk : Qsag.CanonicalSwPk C}
    (hPk : legacyPkOf st.legacyCommitment = some pk)
    (shares : Fin 3 → Nat) (hDlog : Qsag.ZkBooDlogCommitted grp pk.toSwPoint shares)
    {pf1 pf2 : SingleChallengeZkBooProof}
    (hCom1 : ∀ i : Fin 3, pf1.shareCommits i = commitShare i (shares i))
    (hCom2 : ∀ i : Fin 3, pf2.shareCommits i = pf1.shareCommits i)
    (hE1 : pf1.e = 0) (hE2 : pf2.e = 1)
    (hVer1 : singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
      migrationDomain epoch st pf1 = true)
    (hVer2 : singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
      migrationDomain epoch st pf2 = true) :
    (let auth : DlogSettlementAuth := ⟨0, 1, pf1.opened, pf2.opened, pf1.authorizedDest⟩;
      dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch st auth = true ∧
      auth.reconstructScalar ord =
        Qsag.zkbooReconstructScalar ord (shares 0) (shares 1) (shares 2)) ∨
    (∃ (idx : Fin 3) (sForged : Nat),
      sForged ≠ shares idx ∧ commitShare idx sForged = commitShare idx (shares idx)) := by
  unfold singleChallengeZkBooVerify at hVer1 hVer2
  rw [hPk] at hVer1 hVer2
  obtain ⟨hDom, hEp, hDest1, hNull, hC1a, hC1b⟩ := of_decide_eq_true hVer1
  obtain ⟨_, _, _, _, _, hC2b⟩ := of_decide_eq_true hVer2
  have hNext0 : zkbooNextParty 0 = 1 := rfl
  have hNext1 : zkbooNextParty 1 = 2 := rfl
  rw [hE1, hCom1 0] at hC1a
  rw [hE1, hNext0, hCom1 1] at hC1b
  rw [hE2, hNext1, hCom2 2, hCom1 2] at hC2b
  by_cases h0 : pf1.opened.1 = shares 0
  · by_cases h1 : pf1.opened.2 = shares 1
    · by_cases h2 : pf2.opened.2 = shares 2
      · left
        have hRec : (DlogSettlementAuth.mk 0 1 pf1.opened pf2.opened
            pf1.authorizedDest).reconstructScalar ord =
            Qsag.zkbooReconstructScalar ord (shares 0) (shares 1) (shares 2) := by
          unfold DlogSettlementAuth.reconstructScalar
          dsimp only
          rw [Qsag.extractThreeShares_zero_one, h0, h1, h2]
        obtain ⟨hPos, hLt, hSmul⟩ := (Qsag.ZkBooDlogCommitted_iff grp pk.toSwPoint shares).mp hDlog
        refine ⟨dlogSettlementVerify_eq_true grp deriveNullifier legacyPkOf
          migrationDomain epoch hPk ⟨(by decide : (0 : Fin 3) ≠ 1), hDom, hEp, hDest1, hNull, ?_, ?_, ?_⟩, hRec⟩
        · rw [hRec]; exact hPos
        · rw [hRec]; exact hLt
        · rw [hRec]; exact hSmul
      · exact .inr ⟨2, pf2.opened.2, h2, hC2b⟩
    · exact .inr ⟨1, pf1.opened.2, h1, hC1b⟩
  · exact .inr ⟨0, pf1.opened.1, h0, hC1a⟩

/-- `#tooth` A single accepted `SingleChallengeZkBooProof` at challenge `e = 0` opens only
    `(s0, s1)` and information-theoretically hides `sk`: for any two distinct scalars `skA ≠ skB`
    below `ord`, there exist distinct third shares `s2A ≠ s2B` whose share vectors both pass
    `singleChallengeZkBooVerify` with the identical opened pair `(s0, s1)`, yet reconstruct `skA`
    and `skB` respectively. -/
theorem tooth_singleChallengeZkBoo_hides_scalar
    {C : Qsag.SwCurve}
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (commitShare : Fin 3 → Nat → Spec.Digest256)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    {st : MigrationExecution.Statement} {pk : Qsag.CanonicalSwPk C}
    (hPk : legacyPkOf st.legacyCommitment = some pk)
    (hDom : st.migrationDomain = migrationDomain)
    (hEp : st.epoch = epoch)
    (hNull : st.nullifier = deriveNullifier pk)
    {ord s0 s1 skA skB : Nat} (hA : skA < ord) (hB : skB < ord) (hNe : skA ≠ skB) :
    ∃ (sharesA sharesB : Fin 3 → Nat),
      let pfA : SingleChallengeZkBooProof :=
        ⟨0, (s0, s1), fun i => commitShare i (sharesA i), st.destination⟩
      let pfB : SingleChallengeZkBooProof :=
        ⟨0, (s0, s1), fun i => commitShare i (sharesB i), st.destination⟩
      pfA.opened = (s0, s1) ∧ pfB.opened = (s0, s1) ∧
      singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
        migrationDomain epoch st pfA = true ∧
      singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
        migrationDomain epoch st pfB = true ∧
      Qsag.zkbooReconstructScalar ord (sharesA 0) (sharesA 1) (sharesA 2) = skA ∧
      Qsag.zkbooReconstructScalar ord (sharesB 0) (sharesB 1) (sharesB 2) = skB ∧
      sharesA 2 ≠ sharesB 2 := by
  obtain ⟨s2A, s2B, _, _, hS2Ne, hRecA, hRecB⟩ :=
    Qsag.tooth_zkboo_single_challenge_information_theoretically_hides_witness
      (s0 := s0) (s1 := s1) hA hB hNe
  let sharesA : Fin 3 → Nat := fun i => if i.val = 0 then s0 else if i.val = 1 then s1 else s2A
  let sharesB : Fin 3 → Nat := fun i => if i.val = 0 then s0 else if i.val = 1 then s1 else s2B
  refine ⟨sharesA, sharesB, rfl, rfl, ?_, ?_, hRecA, hRecB, hS2Ne⟩
  · unfold singleChallengeZkBooVerify
    rw [hPk]
    exact decide_eq_true ⟨hDom, hEp, rfl, hNull, rfl, rfl⟩
  · unfold singleChallengeZkBooVerify
    rw [hPk]
    exact decide_eq_true ⟨hDom, hEp, rfl, hNull, rfl, rfl⟩

/-- `Spec.DataRefines` from `rawSettlementMachine` with `dlogSettlementWire` and
    `dlogSettlementVerify` over `CanonicalSwPk C` into
    `Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot`, with no
    injectivity premise on `deriveNullifier`. The ownership step rests on
    `dlogSettlement_circuitSound`, hence on the authorization format `DlogSettlementAuth` (both
    openings present), not on a property of `compile`. -/
def dlogSettlement_dataRefines_idealMigrate {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C)) :
    Spec.DataRefines
      (rawSettlementMachine
        (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
        snapshot
        (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
        compile)
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot)
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch).decode
      id :=
  rawSettlement_dataRefines_idealMigrate
    (dlogSettlement_circuitSound grp deriveNullifier legacyPkOf destinationBytes hDestInj
      migrationDomain epoch compile)
    snapshot

/-- `Spec.DataRefines` of the discrete-log settlement model into the key-indexed ideal machine
    `Spec.idealKeyMigrateMachine`, under the same modelling assumption as
    `dlogSettlement_dataRefines_idealMigrate`. -/
def dlogSettlement_dataRefines_idealKeyMigrate {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C)) :
    Spec.DataRefines
      (rawSettlementMachine
        (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
        snapshot
        (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
        compile)
      (Spec.idealKeyMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot)
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch).decode
      id :=
  rawSettlement_dataRefines_idealKeyMigrate
    (dlogSettlement_circuitSound grp deriveNullifier legacyPkOf destinationBytes hDestInj
      migrationDomain epoch compile)
    snapshot

theorem dlogSettlement_refinement_exists {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C)) :
    Nonempty (Spec.DataRefines
      (rawSettlementMachine
        (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
        snapshot
        (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
        compile)
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot)
      (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch).decode
      id) :=
  ⟨dlogSettlement_dataRefines_idealMigrate grp deriveNullifier legacyPkOf destinationBytes hDestInj
    migrationDomain epoch compile snapshot⟩

/-- Collision-branching dichotomy for the discrete-log settlement model
    (`rawSettlement_schedule_refines_or_nullifierCollision` at `dlogSettlement_circuitSound`).
    For every `PrimeSubgroup C G ord` and every `deriveNullifier : CanonicalSwPk C → Digest256`,
    with no injectivity assumption, every schedule `subs` either
    1. projects to admitted traces of `Spec.idealMigrateMachine` and `Spec.idealKeyMigrateMachine`,
       with ownership soundness, non-double-claim, conservation and `spent.Nodup`, and settles
       every honest enrolled submission in `subs`, or
    2. exhibits two distinct keys of `snapshot` with equal nullifiers
       (`Spec.NullifierCollision deriveNullifier pk₁ pk₂`).
    The `PrimeSubgroup` is a parameter; the only one constructed is `secp7Mod43_primeSubgroup`. -/
theorem dlogSettlement_schedule_refines_or_nullifierCollision
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    (subs : List (MigrationExecution.Submission DlogSettlementAuth)) :
    let wire := dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch
    let verify := dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch
    let res := runRawSettlementSchedule wire snapshot verify compile ⟨[]⟩ subs
    ((Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).AdmitsTrace
        (Spec.projectTrace wire.decode id res.2) ∧
      (Spec.idealKeyMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).AdmitsTrace
        (Spec.projectTrace wire.decode id res.2) ∧
      (∀ io ∈ res.2, Spec.ValidLegacyOwnership (dlogOwnershipScheme grp deriveNullifier) snapshot
        io.2.claim (wire.extractWitness io.1.authorization io.1.witness) io.2.amount) ∧
      (res.2.map (fun io => io.2.claim.legacyPk)).Nodup ∧
      (res.2.map (fun io => io.2.amount)).sum ≤ Spec.EnrolledSnapshot.total snapshot ∧
      res.1.spent.Nodup ∧
      (∀ sub ∈ subs, ∀ (pk : Qsag.CanonicalSwPk C) (amount : Nat),
        HonestRawSubmission wire snapshot verify compile sub pk amount →
          pk ∈ res.2.map (fun io => io.2.claim.legacyPk))) ∨
    (∃ pk₁ pk₂ : Qsag.CanonicalSwPk C,
      pk₁ ∈ snapshot.map Prod.fst ∧
      pk₂ ∈ snapshot.map Prod.fst ∧
      Spec.NullifierCollision deriveNullifier pk₁ pk₂) :=
  rawSettlement_schedule_refines_or_nullifierCollision
    (dlogSettlement_circuitSound grp deriveNullifier legacyPkOf destinationBytes hDestInj
      migrationDomain epoch compile)
    snapshot subs

/-- Corollary of `dlogSettlement_schedule_refines_or_nullifierCollision` when `deriveNullifier` is
    injective on the finite enrolled snapshot (`Spec.NullifierInjOn`). -/
theorem dlogSettlement_schedule_complete_of_injOn
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
    (hInj : Spec.NullifierInjOn deriveNullifier (snapshot.map Prod.fst))
    (subs : List (MigrationExecution.Submission DlogSettlementAuth)) :
    let wire := dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch
    let verify := dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch
    let res := runRawSettlementSchedule wire snapshot verify compile ⟨[]⟩ subs
    (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).AdmitsTrace
      (Spec.projectTrace wire.decode id res.2) ∧
    (Spec.idealKeyMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).AdmitsTrace
      (Spec.projectTrace wire.decode id res.2) ∧
    (∀ io ∈ res.2, Spec.ValidLegacyOwnership (dlogOwnershipScheme grp deriveNullifier) snapshot
      io.2.claim (wire.extractWitness io.1.authorization io.1.witness) io.2.amount) ∧
    (res.2.map (fun io => io.2.claim.legacyPk)).Nodup ∧
    (res.2.map (fun io => io.2.amount)).sum ≤ Spec.EnrolledSnapshot.total snapshot ∧
    res.1.spent.Nodup ∧
    (∀ sub ∈ subs, ∀ (pk : Qsag.CanonicalSwPk C) (amount : Nat),
      HonestRawSubmission wire snapshot verify compile sub pk amount →
        pk ∈ res.2.map (fun io => io.2.claim.legacyPk)) :=
  rawSettlement_schedule_complete_of_injOn
    (dlogSettlement_circuitSound grp deriveNullifier legacyPkOf destinationBytes hDestInj
      migrationDomain epoch compile)
    snapshot hInj subs

/-- **`#tooth` Destination Tampering Rejected by `dlogSettlementMachine`
    (`tooth_dlogSettlement_destination_tamper_rejected`)**:
    Mutating `sub.statement.destination` to `dest' ≠ sub.authorization.authorizedDest` while
    replaying the owner's ZKBoo shares and RSS witness lanes causes `rawSettlementMachine` to
    reject (`= none`) in every ledger! -/
theorem tooth_dlogSettlement_destination_tamper_rejected
    {C : Qsag.SwCurve} {G : Qsag.SwPoint} {ord : Nat}
    (grp : Qsag.PrimeSubgroup C G ord)
    (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
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

/-! ## 7. Joint Refinement Witness on the Toy Curve `secp7Mod43`; `BLS12-381` Conditional on its Group Laws -/

/-- Canonical injective 256-bit nullifier encoding on `CanonicalSwPk Weierstrass.secp7Mod43`:
    packs `pk.encodeCoordNat = pk.x + 43 * pk.y < 1849` alongside `NULLIFIER_DOMAIN`. -/
def secp7Mod43Nullifier (pk : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) : Spec.Digest256 :=
  BitVec.ofNat 256 (1 + pk.encodeCoordNat * 2 + Qsag.NULLIFIER_DOMAIN.toNat * 8192)

private theorem secp7Mod43Nullifier_pack_lt {e d : Nat} (he : e < 1849)
    (hd : d < 18446744073709551616) : 1 + e * 2 + d * 8192 < 2 ^ 256 := by
  have h : 1 + e * 2 + d * 8192 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    omega
  exact h

private theorem secp7Mod43Nullifier_pack_inj {e₁ e₂ d : Nat}
    (h : 1 + e₁ * 2 + d * 8192 = 1 + e₂ * 2 + d * 8192) : e₁ = e₂ := by
  omega

/-- `secp7Mod43Nullifier` is injective on `CanonicalSwPk secp7Mod43`: the carrier bounds
    `x, y < 43`, so `encodeCoordNat < 1849` and the packed value is below `2^256`. -/
theorem secp7Mod43Nullifier_injective : Spec.NullifierInjective secp7Mod43Nullifier := by
  refine (Spec.NullifierInjective_iff _).mpr ?_
  intro pk₁ pk₂ hEq
  have hp : Qsag.Weierstrass.secp7Mod43.p = 43 :=
    congrArg (fun C : Qsag.SwCurve => C.p) Qsag.Weierstrass.secp7Mod43_eq
  have hc₁ : pk₁.encodeCoordNat < 1849 := by
    have h := pk₁.encodeCoordNat_lt_sq
    rw [hp] at h
    exact h
  have hc₂ : pk₂.encodeCoordNat < 1849 := by
    have h := pk₂.encodeCoordNat_lt_sq
    rw [hp] at h
    exact h
  have hd : Qsag.NULLIFIER_DOMAIN.toNat < 18446744073709551616 :=
    Qsag.NULLIFIER_DOMAIN.toFin.isLt
  have hNat := congrArg BitVec.toNat hEq
  unfold secp7Mod43Nullifier at hNat
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (secp7Mod43Nullifier_pack_lt hc₁ hd),
    Nat.mod_eq_of_lt (secp7Mod43Nullifier_pack_lt hc₂ hd)] at hNat
  exact Qsag.CanonicalSwPk.encodeCoordNat_injective (secp7Mod43Nullifier_pack_inj hNat)

/-- Validated 2-byte curve public-key decoder on `secp7Mod43`: decodes `[bx, by_]` via
    `CanonicalSwPk.ofSwPoint?`, rejecting off-curve and unreduced (`≥ 43`) coordinates. -/
def secp7Mod43DecodePk : List UInt8 → Option (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43)
  | [bx, by_] =>
    Qsag.CanonicalSwPk.ofSwPoint? Qsag.Weierstrass.secp7Mod43 (some (bx.toNat, by_.toNat))
  | _ => none

private theorem secp7Mod43DecodePk_eq_some {bx by_ : UInt8}
    {pk : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43}
    (h : pk.toSwPoint = some (bx.toNat, by_.toNat)) :
    secp7Mod43DecodePk [bx, by_] = some pk :=
  Qsag.CanonicalSwPk.ofSwPoint?_eq_some_iff.mpr h.symm

private theorem secp7Mod43DecodePk_eq_none {bx by_ : UInt8}
    (h : Qsag.SwCurve.onCurve ⟨43, 0, 7⟩ (some (bx.toNat, by_.toNat)) = false) :
    secp7Mod43DecodePk [bx, by_] = none := by
  cases hD : secp7Mod43DecodePk [bx, by_] with
  | none => rfl
  | some pk =>
    have hPt : some (bx.toNat, by_.toNat) = pk.toSwPoint :=
      Qsag.CanonicalSwPk.ofSwPoint?_eq_some_iff.mp hD
    have hOn := pk.toSwPoint_onCurve
    rw [← hPt, Qsag.Weierstrass.secp7Mod43_eq, h] at hOn
    cases hOn

/-- `#tooth` Off-curve (`[0, 0]`) and unreduced (`[50, 7]`, `[71, 7]`) byte pairs are deterministically
    rejected by `secp7Mod43DecodePk`. -/
theorem tooth_secp7Mod43DecodePk_rejects_offCurve_and_unreduced :
    secp7Mod43DecodePk [0, 0] = none ∧
    secp7Mod43DecodePk [50, 7] = none ∧
    secp7Mod43DecodePk [71, 7] = none :=
  ⟨secp7Mod43DecodePk_eq_none (by decide +kernel), secp7Mod43DecodePk_eq_none (by decide +kernel),
    secp7Mod43DecodePk_eq_none (by decide +kernel)⟩

/-- Unary serialization of a 256-bit destination (toy wire format of the `secp7Mod43` instance). -/
def unaryDestBytes (d : BitVec 256) : Spec.Bytes :=
  List.replicate d.toNat 0

theorem unaryDestBytes_injective {d₁ d₂ : BitVec 256}
    (h : unaryDestBytes d₁ = unaryDestBytes d₂) : d₁ = d₂ := by
  have hLen := congrArg List.length h
  unfold unaryDestBytes at hLen
  rw [List.length_replicate, List.length_replicate] at hLen
  exact BitVec.eq_of_toNat_eq hLen

private def secp7Mod43Wire :
    SettlementWire (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43)
      DlogOwnershipWitness DlogSettlementAuth :=
  dlogSettlementWire 31 secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
    MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch

/-- Circuit compiler of the `secp7Mod43` instance: every statement gets the circuit of
    `MigrationExecution.honestSubmission`, so the circuit does not depend on the statement and
    checks lane well-formedness only. -/
def secp7Mod43Compile (_ : MigrationExecution.Statement) : List MigrationExecution.Gate :=
  MigrationExecution.honestCircuit MigrationExecution.honestSubmission.statement

private theorem secp7Mod43_honest_submission_valid
    (bx by_ : UInt8) (pk : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43)
    (hDec : secp7Mod43DecodePk [bx, by_] = some pk)
    (s0 s1 s2 sk : Nat)
    (hSk : Qsag.zkbooReconstructScalar 31 s0 s1 s2 = sk)
    (hPos : 0 < sk) (hLt : sk < 31)
    (hSmul : Qsag.secp7Mod43_primeSubgroup.smul sk = pk.toSwPoint)
    (deriveNullifier : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43 → Spec.Digest256) :
    let stmt : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [bx, by_]
        nullifier := deriveNullifier pk }
    let auth : DlogSettlementAuth := ⟨0, 1, (s0, s1), (s1, s2), stmt.destination⟩
    let sub : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt, auth, MigrationExecution.honestSubmission.witness⟩
    dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup deriveNullifier secp7Mod43DecodePk
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch stmt auth = true ∧
      MigrationExecution.run sub.witness (secp7Mod43Compile stmt) = .accepted := by
  dsimp only
  have hRunOrig := ((MigrationExecution.settle_accepted_iff (fun _ (_ : Unit) => true)
    MigrationExecution.honestCircuit ⟨[]⟩ MigrationExecution.honestSubmission).mp
    MigrationExecution.settlement_acceptance_witness).2.2
  have hRec : ∀ d : BitVec 256,
      (DlogSettlementAuth.mk 0 1 (s0, s1) (s1, s2) d).reconstructScalar 31 = sk := by
    intro d
    unfold DlogSettlementAuth.reconstructScalar
    rw [Qsag.extractThreeShares_zero_one]
    exact hSk
  exact ⟨dlogSettlementVerify_eq_true Qsag.secp7Mod43_primeSubgroup deriveNullifier
    secp7Mod43DecodePk _ _ (pk := pk) hDec
    ⟨(by decide : (0 : Fin 3) ≠ 1), rfl, rfl, rfl, rfl, Nat.lt_of_lt_of_eq hPos (hRec _).symm,
      Nat.lt_of_le_of_lt (Nat.le_of_eq (hRec _)) hLt, (congrArg _ (hRec _)).trans hSmul⟩,
    hRunOrig⟩

/-- One accepted step of the discrete-log settlement model on the toy curve: over
    `secp7Mod43_primeSubgroup` with enrolled key `secp7Mod43Pk2 = (7, 7) = [2]G`, the submission
    whose authorization opens shares `(1, 1, 0)` is accepted from the empty ledger and its
    receipt carries the enrolled entitlement `250`. The circuit run is that of
    `secp7Mod43Compile` on the lanes of `MigrationExecution.honestSubmission`; it is unrelated to
    the curve relation. -/
theorem secp7Mod43_dlogSettlement_honest_accepted :
    let pk2 := Qsag.secp7Mod43Pk2
    let wire := dlogSettlementWire 31 secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
      [(pk2, 250)]
    let stmt : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [7, 7]
        nullifier := secp7Mod43Nullifier pk2 }
    let auth : DlogSettlementAuth := ⟨0, 1, (1, 1), (1, 0), stmt.destination⟩
    let sub : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt, auth, MigrationExecution.honestSubmission.witness⟩
    ∃ ledger' : MigrationExecution.Ledger,
      (rawSettlementMachine wire snap
        (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
          MigrationExecution.honestSubmission.statement.migrationDomain
          MigrationExecution.honestSubmission.statement.epoch)
        secp7Mod43Compile).step ⟨[]⟩ sub =
      some (ledger', ⟨wire.claimOf pk2 stmt, 250⟩) := by
  dsimp only
  have hDec2 : secp7Mod43DecodePk [7, 7] = some Qsag.secp7Mod43Pk2 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.2.1
  have hSmul2 : Qsag.secp7Mod43_primeSubgroup.smul 2 = Qsag.secp7Mod43Pk2.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.2.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.2.2.1
  obtain ⟨hVer, hRun⟩ := secp7Mod43_honest_submission_valid 7 7 Qsag.secp7Mod43Pk2 hDec2
    1 1 0 2 (Qsag.zkbooReconstructScalar_eq 31 1 1 0) (by decide) (by decide) hSmul2
    secp7Mod43Nullifier
  let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
    [(Qsag.secp7Mod43Pk2, 250)]
  let stmt : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [7, 7]
      nullifier := secp7Mod43Nullifier Qsag.secp7Mod43Pk2 }
  let auth : DlogSettlementAuth := ⟨0, 1, (1, 1), (1, 0), stmt.destination⟩
  let sub : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt, auth, MigrationExecution.honestSubmission.witness⟩
  have hAcc : (MigrationExecution.settle
      (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch)
      secp7Mod43Compile ⟨[]⟩ sub).2 = .accepted :=
    (MigrationExecution.settle_accepted_iff _ secp7Mod43Compile ⟨[]⟩ sub).mpr
      ⟨(by intro h; cases h), hVer, hRun⟩
  have hEnt : Spec.EnrolledSnapshot.entitlement snap Qsag.secp7Mod43Pk2 = some 250 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hAd : rawSettlementAdmit secp7Mod43Wire snap stmt = some (Qsag.secp7Mod43Pk2, 250) :=
    rawSettlementAdmit_of_decoded (D := secp7Mod43Wire) (st := stmt) hDec2 hEnt
  refine ⟨(MigrationExecution.settle
      (dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier secp7Mod43DecodePk
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch)
      secp7Mod43Compile ⟨[]⟩ sub).1, ?_⟩
  show rawSettlementStep secp7Mod43Wire snap _ secp7Mod43Compile ⟨[]⟩ sub = _
  unfold rawSettlementStep
  rw [hAd]
  show settlementReceipt _ _ (MigrationExecution.settle _ secp7Mod43Compile ⟨[]⟩ sub).2 = _
  rw [hAcc]
  rfl

/-- Joint instance of the discrete-log settlement model on the toy curve `secp7Mod43` (`p = 43`,
    subgroup order `31`), with the snapshot `[(Pk1, 150), (Pk2, 250)]` and the schedule
    `[sub1, sub2, sub2Replay]`. In this one instance, with no hypotheses:
    1. `Spec.NullifierInjective secp7Mod43Nullifier`;
    2. `SettlementCircuitSound` for the instance (`dlogSettlement_circuitSound`);
    3. the accepted trace of the schedule projects to admitted traces of
       `Spec.idealMigrateMachine` and `Spec.idealKeyMigrateMachine` (the first of these is stated
       twice: it is obtained once from `dlogSettlement_schedule_complete_of_injOn` and once from
       `dlogSettlement_dataRefines_idealMigrate`);
    4. the schedule settles exactly `Pk1 = [1]G = (2, 12)` and `Pk2 = [2]G = (7, 7)`, amounts
       summing to `400`, the replay `sub2Replay` with another destination being rejected.
    Limits of the instance: the curve is a toy; `secp7Mod43Compile` gives every statement the
    lane well-formedness circuit of `MigrationExecution.honestSubmission`; and each authorization
    carries both openings (`DlogSettlementAuth`), so the scalars `1` and `2` are in the
    submissions. -/
theorem secp7Mod43_dlogSettlement_complete_refinement_witness :
    let pk1 := Qsag.secp7Mod43Pk1
    let pk2 := Qsag.secp7Mod43Pk2
    let wire := dlogSettlementWire 31 secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let verify := dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier
      secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
      [(pk1, 150), (pk2, 250)]
    let stmt1 : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [2, 12]
        nullifier := secp7Mod43Nullifier pk1 }
    let sub1 : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt1, ⟨0, 1, (1, 0), (0, 0), stmt1.destination⟩, MigrationExecution.honestSubmission.witness⟩
    let stmt2 : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [7, 7]
        nullifier := secp7Mod43Nullifier pk2 }
    let sub2 : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt2, ⟨0, 1, (1, 1), (1, 0), stmt2.destination⟩, MigrationExecution.honestSubmission.witness⟩
    let stmt2Replay : MigrationExecution.Statement :=
      { stmt2 with destination := 1#256 }
    let sub2Replay : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt2Replay, ⟨0, 1, (1, 1), (1, 0), 1#256⟩, MigrationExecution.honestSubmission.witness⟩
    let res := runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩
      [sub1, sub2, sub2Replay]
    Spec.NullifierInjective secp7Mod43Nullifier ∧
    SettlementCircuitSound wire (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier)
      verify secp7Mod43Compile ∧
    (Spec.idealMigrateMachine (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier)
      snap).AdmitsTrace (Spec.projectTrace wire.decode id res.2) ∧
    (Spec.idealKeyMigrateMachine (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier)
      snap).AdmitsTrace (Spec.projectTrace wire.decode id res.2) ∧
    res.2.map (fun io => io.2.claim.legacyPk) = [pk1, pk2] ∧
    (res.2.map (fun io => io.2.amount)).sum = 400 ∧
    (rawSettlementMachine wire snap verify secp7Mod43Compile).AdmitsTrace res.2 ∧
    (Spec.idealMigrateMachine (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier)
      snap).AdmitsTrace (Spec.projectTrace wire.decode id res.2) := by
  dsimp only
  let pk1 := Qsag.secp7Mod43Pk1
  let pk2 := Qsag.secp7Mod43Pk2
  let wire := secp7Mod43Wire
  let verify := dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier
    secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch
  let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
    [(pk1, 150), (pk2, 250)]
  let stmt1 : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [2, 12]
      nullifier := secp7Mod43Nullifier pk1 }
  let sub1 : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt1, ⟨0, 1, (1, 0), (0, 0), stmt1.destination⟩, MigrationExecution.honestSubmission.witness⟩
  let stmt2 : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [7, 7]
      nullifier := secp7Mod43Nullifier pk2 }
  let sub2 : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt2, ⟨0, 1, (1, 1), (1, 0), stmt2.destination⟩, MigrationExecution.honestSubmission.witness⟩
  let stmt2Replay : MigrationExecution.Statement :=
    { stmt2 with destination := 1#256 }
  let sub2Replay : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt2Replay, ⟨0, 1, (1, 1), (1, 0), 1#256⟩, MigrationExecution.honestSubmission.witness⟩
  have hDec1 : secp7Mod43DecodePk [2, 12] = some pk1 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.1
  have hDec2 : secp7Mod43DecodePk [7, 7] = some pk2 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.2.1
  have hSmul1 : Qsag.secp7Mod43_primeSubgroup.smul 1 = pk1.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.1
  have hSmul2 : Qsag.secp7Mod43_primeSubgroup.smul 2 = pk2.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.2.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.2.2.1
  obtain ⟨hVer1, hRun1⟩ := secp7Mod43_honest_submission_valid 2 12 pk1 hDec1
    1 0 0 1 (Qsag.zkbooReconstructScalar_eq 31 1 0 0) (by decide) (by decide) hSmul1
    secp7Mod43Nullifier
  obtain ⟨hVer2, hRun2⟩ := secp7Mod43_honest_submission_valid 7 7 pk2 hDec2
    1 1 0 2 (Qsag.zkbooReconstructScalar_eq 31 1 1 0) (by decide) (by decide) hSmul2
    secp7Mod43Nullifier
  have hPkNe : pk2 ≠ pk1 := Ne.symm Qsag.secp7Mod43_canonicalPks_props.2.2.2.2.2.2.2.2.2.1
  have hNullNe : secp7Mod43Nullifier pk2 ≠ secp7Mod43Nullifier pk1 :=
    fun hEq => hPkNe ((Spec.NullifierInjective_iff _).mp secp7Mod43Nullifier_injective hEq)
  have hEnt1 : Spec.EnrolledSnapshot.entitlement snap pk1 = some 150 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hEnt2 : Spec.EnrolledSnapshot.entitlement snap pk2 = some 250 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, hPkNe, ↓reduceIte]
  have hAd1 : rawSettlementAdmit wire snap stmt1 = some (pk1, 150) :=
    rawSettlementAdmit_of_decoded (D := wire) (st := stmt1) hDec1 hEnt1
  have hAd2 : rawSettlementAdmit wire snap stmt2 = some (pk2, 250) :=
    rawSettlementAdmit_of_decoded (D := wire) (st := stmt2) hDec2 hEnt2
  have hStep1 : (rawSettlementMachine wire snap verify secp7Mod43Compile).step ⟨[]⟩ sub1 =
      some (⟨[secp7Mod43Nullifier pk1]⟩, ⟨wire.claimOf pk1 stmt1, 150⟩) := by
    have hAcc1 : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).2 = .accepted :=
      (MigrationExecution.settle_accepted_iff _ _ ⟨[]⟩ sub1).mpr ⟨(by intro h; cases h), hVer1, hRun1⟩
    have hIns1 := MigrationExecution.settle_accept_inserts verify secp7Mod43Compile ⟨[]⟩ sub1 hAcc1
    show rawSettlementStep wire snap verify secp7Mod43Compile ⟨[]⟩ sub1 = _
    unfold rawSettlementStep; rw [hAd1]
    show settlementReceipt _ _ (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).2 = _
    rw [hAcc1]
    have hL1 : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).1 =
        ⟨[secp7Mod43Nullifier pk1]⟩ := by
      cases hs : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).1
      rw [hs] at hIns1; dsimp only at hIns1; subst hIns1; rfl
    rw [hL1]; rfl
  have hStep2 : (rawSettlementMachine wire snap verify secp7Mod43Compile).step
      ⟨[secp7Mod43Nullifier pk1]⟩ sub2 =
      some (⟨[secp7Mod43Nullifier pk2, secp7Mod43Nullifier pk1]⟩, ⟨wire.claimOf pk2 stmt2, 250⟩) := by
    have hFresh2 : stmt2.nullifier ∉ [secp7Mod43Nullifier pk1] := by
      intro hMem
      rcases List.mem_cons.mp hMem with hEq | hNil
      · exact hNullNe hEq
      · nomatch hNil
    have hAcc2 : (MigrationExecution.settle verify secp7Mod43Compile
        ⟨[secp7Mod43Nullifier pk1]⟩ sub2).2 = .accepted :=
      (MigrationExecution.settle_accepted_iff _ _ _ sub2).mpr ⟨hFresh2, hVer2, hRun2⟩
    have hIns2 := MigrationExecution.settle_accept_inserts verify secp7Mod43Compile
      ⟨[secp7Mod43Nullifier pk1]⟩ sub2 hAcc2
    show rawSettlementStep wire snap verify secp7Mod43Compile _ sub2 = _
    unfold rawSettlementStep; rw [hAd2]
    show settlementReceipt _ _ (MigrationExecution.settle verify secp7Mod43Compile _ sub2).2 = _
    rw [hAcc2]
    have hL2 : (MigrationExecution.settle verify secp7Mod43Compile
        ⟨[secp7Mod43Nullifier pk1]⟩ sub2).1 =
        ⟨[secp7Mod43Nullifier pk2, secp7Mod43Nullifier pk1]⟩ := by
      cases hs : (MigrationExecution.settle verify secp7Mod43Compile
        ⟨[secp7Mod43Nullifier pk1]⟩ sub2).1
      rw [hs] at hIns2; dsimp only at hIns2; subst hIns2; rfl
    rw [hL2]; rfl
  have hStepReplay : (rawSettlementMachine wire snap verify secp7Mod43Compile).step
      ⟨[secp7Mod43Nullifier pk2, secp7Mod43Nullifier pk1]⟩ sub2Replay = none :=
    tooth_rawSettlement_resubmission_other_destination_rejected
      (dlogSettlement_circuitSound Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier
        secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
        MigrationExecution.honestSubmission.statement.migrationDomain
        MigrationExecution.honestSubmission.statement.epoch secp7Mod43Compile)
      snap hStep2 sub2Replay rfl
  have hSched : runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩
      [sub1, sub2, sub2Replay] =
      (⟨[secp7Mod43Nullifier pk2, secp7Mod43Nullifier pk1]⟩,
       [(sub1, ⟨wire.claimOf pk1 stmt1, 150⟩), (sub2, ⟨wire.claimOf pk2 stmt2, 250⟩)]) := by
    unfold runRawSettlementSchedule
    rw [hStep1]
    dsimp only
    unfold runRawSettlementSchedule
    rw [hStep2]
    dsimp only
    unfold runRawSettlementSchedule
    rw [hStepReplay, rawSettlement_rejected_ledger_unchanged wire snap verify secp7Mod43Compile hStepReplay]
    rfl
  have hComp := dlogSettlement_schedule_complete_of_injOn Qsag.secp7Mod43_primeSubgroup
    secp7Mod43Nullifier secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
    MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch secp7Mod43Compile snap
    (secp7Mod43Nullifier_injective.injOn _) [sub1, sub2, sub2Replay]
  have hTrC := runRawSettlementSchedule_validTrace wire snap verify secp7Mod43Compile ⟨[]⟩
    [sub1, sub2, sub2Replay]
  have hAdmC : (rawSettlementMachine wire snap verify secp7Mod43Compile).AdmitsTrace
      (runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩
        [sub1, sub2, sub2Replay]).2 := ⟨⟨[]⟩, _, rfl, hTrC⟩
  let ref := dlogSettlement_dataRefines_idealMigrate Qsag.secp7Mod43_primeSubgroup
    secp7Mod43Nullifier secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
    MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch secp7Mod43Compile snap
  refine ⟨secp7Mod43Nullifier_injective,
    dlogSettlement_circuitSound Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier
      secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch secp7Mod43Compile,
    hComp.1, hComp.2.1, ?_, ?_, hAdmC, ref.preserve_admitsTrace hAdmC⟩
  · exact congrArg (fun r => r.2.map (fun io => io.2.claim.legacyPk)) hSched
  · exact congrArg (fun r => (r.2.map (fun io => io.2.amount)).sum) hSched

/-- Defective x-only nullifier on `secp7Mod43` that omits `y`-parity (`[1]G = (2, 12)` and
    `[30]G = (2, 31)` share `x = 2`). -/
def secp7Mod43XOnlyNullifier (pk : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) : Spec.Digest256 :=
  BitVec.ofNat 256 pk.x

/-- **`#tooth` X-Only Nullifier Collision Constructively Extracted by
    `dlogSettlement_schedule_refines_or_nullifierCollision`
    (`tooth_dlogSettlement_xOnlyNullifier_extracts_collision`)**:
    When `deriveNullifier` omits `y`-parity (`secp7Mod43XOnlyNullifier`), `[1]G = (2, 12)` and
    `[30]G = (2, 31)` are two distinct enrolled canonical subgroup keys whose honest owners BOTH
    submit valid ZKBoo proofs (`sk = 1` and `sk = 30`), `[1]G` blocks `[30]G`, and
    `dlogSettlement_schedule_refines_or_nullifierCollision` constructively extracts
    `Spec.NullifierCollision secp7Mod43XOnlyNullifier pk₁ pk₂`! -/
theorem tooth_dlogSettlement_xOnlyNullifier_extracts_collision :
    let pk1 := Qsag.secp7Mod43Pk1
    let pk30 := Qsag.secp7Mod43Pk30
    let wire := dlogSettlementWire 31 secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let verify := dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43XOnlyNullifier
      secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch
    let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
      [(pk1, 150), (pk30, 250)]
    let stmt1 : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [2, 12]
        nullifier := secp7Mod43XOnlyNullifier pk1 }
    let sub1 : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt1, ⟨0, 1, (1, 0), (0, 0), stmt1.destination⟩, MigrationExecution.honestSubmission.witness⟩
    let stmt30 : MigrationExecution.Statement :=
      { MigrationExecution.honestSubmission.statement with
        legacyCommitment := [2, 31]
        nullifier := secp7Mod43XOnlyNullifier pk30 }
    let sub30 : MigrationExecution.Submission DlogSettlementAuth :=
      ⟨stmt30, ⟨0, 1, (10, 10), (10, 10), stmt30.destination⟩, MigrationExecution.honestSubmission.witness⟩
    let res := runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩ [sub1, sub30]
    HonestRawSubmission wire snap verify secp7Mod43Compile sub1 pk1 150 ∧
    HonestRawSubmission wire snap verify secp7Mod43Compile sub30 pk30 250 ∧
    pk30 ∉ res.2.map (fun io => io.2.claim.legacyPk) ∧
    (∃ pkA pkB : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43,
      pkA ∈ snap.map Prod.fst ∧
      pkB ∈ snap.map Prod.fst ∧
      Spec.NullifierCollision secp7Mod43XOnlyNullifier pkA pkB) := by
  dsimp only
  let pk1 := Qsag.secp7Mod43Pk1
  let pk30 := Qsag.secp7Mod43Pk30
  let wire := secp7Mod43Wire
  let verify := dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43XOnlyNullifier
    secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
    MigrationExecution.honestSubmission.statement.epoch
  let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
    [(pk1, 150), (pk30, 250)]
  let stmt1 : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [2, 12]
      nullifier := secp7Mod43XOnlyNullifier pk1 }
  let sub1 : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt1, ⟨0, 1, (1, 0), (0, 0), stmt1.destination⟩, MigrationExecution.honestSubmission.witness⟩
  let stmt30 : MigrationExecution.Statement :=
    { MigrationExecution.honestSubmission.statement with
      legacyCommitment := [2, 31]
      nullifier := secp7Mod43XOnlyNullifier pk30 }
  let sub30 : MigrationExecution.Submission DlogSettlementAuth :=
    ⟨stmt30, ⟨0, 1, (10, 10), (10, 10), stmt30.destination⟩, MigrationExecution.honestSubmission.witness⟩
  have hDec1 : secp7Mod43DecodePk [2, 12] = some pk1 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.1
  have hDec30 : secp7Mod43DecodePk [2, 31] = some pk30 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.2.2.1
  have hSmul1 : Qsag.secp7Mod43_primeSubgroup.smul 1 = pk1.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.1
  have hSmul30 : Qsag.secp7Mod43_primeSubgroup.smul 30 = pk30.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.2.2.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.2.1
  obtain ⟨hVer1, hRun1⟩ := secp7Mod43_honest_submission_valid 2 12 pk1 hDec1
    1 0 0 1 (Qsag.zkbooReconstructScalar_eq 31 1 0 0) (by decide) (by decide) hSmul1
    secp7Mod43XOnlyNullifier
  obtain ⟨hVer30, hRun30⟩ := secp7Mod43_honest_submission_valid 2 31 pk30 hDec30
    10 10 10 30 (Qsag.zkbooReconstructScalar_eq 31 10 10 10) (by decide) (by decide) hSmul30
    secp7Mod43XOnlyNullifier
  have hPkNe : pk30 ≠ pk1 := Ne.symm Qsag.secp7Mod43_canonicalPks_props.2.2.2.2.2.2.2.2.2.2
  have hEnt1 : Spec.EnrolledSnapshot.entitlement snap pk1 = some 150 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hEnt30 : Spec.EnrolledSnapshot.entitlement snap pk30 = some 250 := by
    simp only [snap, Spec.EnrolledSnapshot.entitlement, hPkNe, ↓reduceIte]
  have hHon1 : HonestRawSubmission wire snap verify secp7Mod43Compile sub1 pk1 150 :=
    ⟨hDec1, hEnt1, hVer1, hRun1⟩
  have hHon30 : HonestRawSubmission wire snap verify secp7Mod43Compile sub30 pk30 250 :=
    ⟨hDec30, hEnt30, hVer30, hRun30⟩
  have hNullEq : secp7Mod43XOnlyNullifier pk1 = secp7Mod43XOnlyNullifier pk30 := by
    unfold secp7Mod43XOnlyNullifier
    rw [Qsag.secp7Mod43_canonicalPks_props.2.2.2.1,
        Qsag.secp7Mod43_canonicalPks_props.2.2.2.2.2.2.2.1]
  have hAd1 : rawSettlementAdmit wire snap stmt1 = some (pk1, 150) :=
    rawSettlementAdmit_of_decoded (D := wire) (st := stmt1) hDec1 hEnt1
  have hAd30 : rawSettlementAdmit wire snap stmt30 = some (pk30, 250) :=
    rawSettlementAdmit_of_decoded (D := wire) (st := stmt30) hDec30 hEnt30
  have hStep1 : (rawSettlementMachine wire snap verify secp7Mod43Compile).step ⟨[]⟩ sub1 =
      some (⟨[secp7Mod43XOnlyNullifier pk1]⟩, ⟨wire.claimOf pk1 stmt1, 150⟩) := by
    have hAcc1 : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).2 = .accepted :=
      (MigrationExecution.settle_accepted_iff _ _ ⟨[]⟩ sub1).mpr ⟨(by intro h; cases h), hVer1, hRun1⟩
    have hIns1 := MigrationExecution.settle_accept_inserts verify secp7Mod43Compile ⟨[]⟩ sub1 hAcc1
    show rawSettlementStep wire snap verify secp7Mod43Compile ⟨[]⟩ sub1 = _
    unfold rawSettlementStep; rw [hAd1]
    show settlementReceipt _ _ (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).2 = _
    rw [hAcc1]
    have hL1 : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).1 =
        ⟨[secp7Mod43XOnlyNullifier pk1]⟩ := by
      cases hs : (MigrationExecution.settle verify secp7Mod43Compile ⟨[]⟩ sub1).1
      rw [hs] at hIns1; dsimp only at hIns1; subst hIns1; rfl
    rw [hL1]; rfl
  have hStep30 : (rawSettlementMachine wire snap verify secp7Mod43Compile).step
      ⟨[secp7Mod43XOnlyNullifier pk1]⟩ sub30 = none := by
    have hRep : MigrationExecution.settle verify secp7Mod43Compile
        ⟨[secp7Mod43XOnlyNullifier pk1]⟩ sub30 =
        (⟨[secp7Mod43XOnlyNullifier pk1]⟩, .replay) :=
      MigrationExecution.settle_replay_rejected verify secp7Mod43Compile _ sub30
        (by show secp7Mod43XOnlyNullifier pk30 ∈ [secp7Mod43XOnlyNullifier pk1]; rw [← hNullEq]; exact .head _)
    show rawSettlementStep wire snap verify secp7Mod43Compile _ sub30 = none
    unfold rawSettlementStep; rw [hAd30, hRep]; rfl
  have hBlocked : pk30 ∉ (runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩
      [sub1, sub30]).2.map (fun io => io.2.claim.legacyPk) := by
    unfold runRawSettlementSchedule
    rw [hStep1]; dsimp only
    unfold runRawSettlementSchedule
    rw [hStep30, rawSettlement_rejected_ledger_unchanged wire snap verify secp7Mod43Compile hStep30]
    intro hMem
    rcases List.mem_cons.mp hMem with hEq | hNil
    · exact hPkNe hEq
    · nomatch hNil
  refine ⟨hHon1, hHon30, hBlocked, ?_⟩
  rcases dlogSettlement_schedule_refines_or_nullifierCollision Qsag.secp7Mod43_primeSubgroup
      secp7Mod43XOnlyNullifier secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
      MigrationExecution.honestSubmission.statement.migrationDomain
      MigrationExecution.honestSubmission.statement.epoch secp7Mod43Compile snap [sub1, sub30] with
    hLeft | hRight
  · exact False.elim (hBlocked (hLeft.2.2.2.2.2.2 sub30 (.tail _ (.head _)) pk30 250 hHon30))
  · exact hRight

/-- `#tooth` The completeness clause of `dlogSettlement_schedule_complete_of_injOn` is false for
    the x-only nullifier: in the schedule `[sub1, sub30]` over the snapshot of `[1]G` and `[30]G`,
    not every honest submission settles its key. -/
theorem tooth_dlogSettlement_xOnlyNullifier_blocks_honest_owner :
    ¬ (let pk1 := Qsag.secp7Mod43Pk1
       let pk30 := Qsag.secp7Mod43Pk30
       let wire := dlogSettlementWire 31 secp7Mod43DecodePk unaryDestBytes unaryDestBytes_injective
         MigrationExecution.honestSubmission.statement.migrationDomain
         MigrationExecution.honestSubmission.statement.epoch
       let verify := dlogSettlementVerify Qsag.secp7Mod43_primeSubgroup secp7Mod43XOnlyNullifier
         secp7Mod43DecodePk MigrationExecution.honestSubmission.statement.migrationDomain
         MigrationExecution.honestSubmission.statement.epoch
       let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
         [(pk1, 150), (pk30, 250)]
       let stmt1 : MigrationExecution.Statement :=
         { MigrationExecution.honestSubmission.statement with
           legacyCommitment := [2, 12]
           nullifier := secp7Mod43XOnlyNullifier pk1 }
       let sub1 : MigrationExecution.Submission DlogSettlementAuth :=
         ⟨stmt1, ⟨0, 1, (1, 0), (0, 0), stmt1.destination⟩,
           MigrationExecution.honestSubmission.witness⟩
       let stmt30 : MigrationExecution.Statement :=
         { MigrationExecution.honestSubmission.statement with
           legacyCommitment := [2, 31]
           nullifier := secp7Mod43XOnlyNullifier pk30 }
       let sub30 : MigrationExecution.Submission DlogSettlementAuth :=
         ⟨stmt30, ⟨0, 1, (10, 10), (10, 10), stmt30.destination⟩,
           MigrationExecution.honestSubmission.witness⟩
       let res := runRawSettlementSchedule wire snap verify secp7Mod43Compile ⟨[]⟩ [sub1, sub30]
       ∀ sub ∈ [sub1, sub30],
         ∀ (pk : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) (amount : Nat),
           HonestRawSubmission wire snap verify secp7Mod43Compile sub pk amount →
             pk ∈ res.2.map (fun io => io.2.claim.legacyPk)) := by
  intro h
  have hTooth := tooth_dlogSettlement_xOnlyNullifier_extracts_collision
  dsimp only at h hTooth
  exact hTooth.2.2.1 (h _ (.tail _ (.head _)) _ 250 hTooth.2.1)

/-- `#tooth` The collision disjunct of `dlogSettlement_schedule_refines_or_nullifierCollision` is
    inhabited: the snapshot of `[1]G` and `[30]G` holds two distinct keys with equal x-only
    nullifiers. -/
theorem tooth_dlogSettlement_xOnlyNullifier_snapshot_collision :
    ∃ pkA pkB : Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43,
      pkA ∈ [(Qsag.secp7Mod43Pk1, 150), (Qsag.secp7Mod43Pk30, 250)].map Prod.fst ∧
      pkB ∈ [(Qsag.secp7Mod43Pk1, 150), (Qsag.secp7Mod43Pk30, 250)].map Prod.fst ∧
      Spec.NullifierCollision secp7Mod43XOnlyNullifier pkA pkB :=
  tooth_dlogSettlement_xOnlyNullifier_extracts_collision.2.2.2

/-! ### 381-Bit `BLS12-381` Compressing-Nullifier Instantiation -/

/-- Compressing 256-bit nullifier fold over 381-bit `CanonicalSwPk bls381Curve` coordinates. -/
def bls381FoldNullifier (pk : Qsag.CanonicalSwPk Qsag.bls381Curve) : Spec.Digest256 :=
  BitVec.ofNat 256
    (pk.x ^^^ (pk.x >>> 256) ^^^ (pk.y <<< 1) ^^^ (pk.y >>> 255) ^^^ Qsag.NULLIFIER_DOMAIN.toNat)

/-- The dichotomy over `CanonicalSwPk bls381Curve` with the compressing nullifier
    `bls381FoldNullifier`, conditional on `hGrp`: the `PrimeOrderGroup` laws of `bls381G1`, which
    are not proved in the tree, so this theorem has no instance here. Given `hGrp`, the
    discrete-log settlement model has a `Spec.DataRefines` into `Spec.idealMigrateMachine` and
    satisfies the collision-branching dichotomy, although `2^256 < p_bls381` rules out an
    injective map from the coordinate range to `Digest256`
    (`tooth_bls381_width_no_injective_bitvec256`). -/
theorem bls381_dlogSettlement_refines_or_nullifierCollision
    (hGrp : Qsag.bls381Curve.PrimeOrderGroup Qsag.bls381G1 Qsag.r_bls381)
    (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk Qsag.bls381Curve))
    (destinationBytes : BitVec 256 → Spec.Bytes)
    (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
    (migrationDomain : BitVec 256) (epoch : UInt64)
    (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
    (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.bls381Curve))
    (subs : List (MigrationExecution.Submission DlogSettlementAuth)) :
    let grp := Qsag.bls381_primeSubgroup hGrp
    let wire := dlogSettlementWire Qsag.r_bls381 legacyPkOf destinationBytes hDestInj migrationDomain epoch
    let verify := dlogSettlementVerify grp bls381FoldNullifier legacyPkOf migrationDomain epoch
    let res := runRawSettlementSchedule wire snapshot verify compile ⟨[]⟩ subs
    Nonempty (Spec.DataRefines
      (rawSettlementMachine wire snapshot verify compile)
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp bls381FoldNullifier) snapshot)
      wire.decode id) ∧
    (((Spec.idealMigrateMachine (dlogOwnershipScheme grp bls381FoldNullifier) snapshot).AdmitsTrace
        (Spec.projectTrace wire.decode id res.2) ∧
      (Spec.idealKeyMigrateMachine (dlogOwnershipScheme grp bls381FoldNullifier) snapshot).AdmitsTrace
        (Spec.projectTrace wire.decode id res.2) ∧
      (∀ sub ∈ subs, ∀ (pk : Qsag.CanonicalSwPk Qsag.bls381Curve) (amount : Nat),
        HonestRawSubmission wire snapshot verify compile sub pk amount →
          pk ∈ res.2.map (fun io => io.2.claim.legacyPk))) ∨
     (∃ pk₁ pk₂ : Qsag.CanonicalSwPk Qsag.bls381Curve,
        pk₁ ∈ snapshot.map Prod.fst ∧
        pk₂ ∈ snapshot.map Prod.fst ∧
        Spec.NullifierCollision bls381FoldNullifier pk₁ pk₂)) := by
  dsimp only
  let grp := Qsag.bls381_primeSubgroup hGrp
  refine ⟨⟨dlogSettlement_dataRefines_idealMigrate grp bls381FoldNullifier legacyPkOf
    destinationBytes hDestInj migrationDomain epoch compile snapshot⟩, ?_⟩
  rcases dlogSettlement_schedule_refines_or_nullifierCollision grp bls381FoldNullifier legacyPkOf
      destinationBytes hDestInj migrationDomain epoch compile snapshot subs with
    hOk | hColl
  · exact .inl ⟨hOk.1, hOk.2.1, hOk.2.2.2.2.2.2⟩
  · exact .inr hColl

/-- `Spec.NullifierInjOn` is satisfiable for the compressing nullifier on 381-bit coordinates:
    `bls381G1Canonical` and `bls381NegG1Canonical` are distinct canonical keys with different
    `bls381FoldNullifier` values, while `2^256 < p_bls381` rules out an injective map from
    `Fin p_bls381` to `BitVec 256`. This concerns the nullifier only; it uses no group law. -/
theorem bls381_compressing_nullifier_nonvacuous :
    Qsag.bls381G1Canonical ≠ Qsag.bls381NegG1Canonical ∧
    bls381FoldNullifier Qsag.bls381G1Canonical ≠ bls381FoldNullifier Qsag.bls381NegG1Canonical ∧
    Spec.NullifierInjOn bls381FoldNullifier [Qsag.bls381G1Canonical, Qsag.bls381NegG1Canonical] ∧
    (2 ^ 256 < Qsag.p_bls381 ∧
      ¬ ∃ f : Fin Qsag.p_bls381 → BitVec 256,
        ∀ {x₁ x₂ : Fin Qsag.p_bls381}, f x₁ = f x₂ → x₁ = x₂) := by
  have hDistinct := Qsag.bls381_canonicalPks_distinct_and_381bit.2.2.1
  have hNullNe : bls381FoldNullifier Qsag.bls381G1Canonical ≠
      bls381FoldNullifier Qsag.bls381NegG1Canonical := by
    obtain ⟨hx, hy, hnx, hny⟩ := Qsag.bls381_canonicalPks_coords
    unfold bls381FoldNullifier
    rw [hnx, hny, hx, hy, Qsag.NULLIFIER_DOMAIN_eq]
    decide +kernel
  refine ⟨hDistinct, hNullNe, (Spec.NullifierInjOn_iff _ _).mpr ?_,
    Qsag.tooth_bls381_width_no_injective_bitvec256⟩
  intro pk₁ pk₂ h₁ h₂ hEq
  rcases List.mem_cons.mp h₁ with rfl | h₁'
  · rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · rcases List.mem_cons.mp h₂' with rfl | hNil
      · exact False.elim (hNullNe hEq)
      · nomatch hNil
  · rcases List.mem_cons.mp h₁' with rfl | hNil
    · rcases List.mem_cons.mp h₂ with rfl | h₂'
      · exact False.elim (hNullNe hEq.symm)
      · rcases List.mem_cons.mp h₂' with rfl | hNil₂
        · rfl
        · nomatch hNil₂
    · nomatch hNil

/-! ### Joint Premise-Inhabitedness Witnesses (`#verify_inhabited`) -/

theorem inhabited_dlogOwnership_accepted_claim :
    ∃ (C : Qsag.SwCurve) (G : Qsag.SwPoint) (ord : Nat)
      (grp : Qsag.PrimeSubgroup C G ord)
      (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
      (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
      (st st' : Spec.IdealMigrateState (Qsag.CanonicalSwPk C))
      (claim : Spec.MigrationClaim (Qsag.CanonicalSwPk C))
      (w : DlogOwnershipWitness)
      (out : Spec.MigrationReceipt (Qsag.CanonicalSwPk C)),
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).step
        st (claim, w) = some (st', out) := by
  let pk1 := Qsag.secp7Mod43Pk1
  let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) := [(pk1, 150)]
  let claim : Spec.MigrationClaim (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) :=
    ⟨pk1, secp7Mod43Nullifier pk1, []⟩
  let w : DlogOwnershipWitness := ⟨1, []⟩
  have hSmul1 : Qsag.secp7Mod43_primeSubgroup.smul 1 = pk1.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.1
  have hEnt : Spec.EnrolledEntitlement snap pk1 150 := by
    show Spec.EnrolledSnapshot.entitlement snap pk1 = some 150
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  have hValid : Spec.ValidLegacyOwnership
      (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier) snap claim w 150 :=
    ⟨hEnt, rfl, (by decide : 0 < 1), (by decide : 1 < 31), hSmul1, rfl⟩
  have hInjOn : Spec.NullifierInjOn
      (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier).deriveNullifier
      (snap.map Prod.fst) :=
    secp7Mod43Nullifier_injective.injOn _
  have hStep := Spec.idealMigrateMachine_unclaimed_owner_accepts
    (st := Spec.IdealMigrateState.init) hInjOn
    (Spec.IdealMigrateState.init_inv
      (dlogOwnershipScheme Qsag.secp7Mod43_primeSubgroup secp7Mod43Nullifier) snap)
    hValid (fun h => nomatch h)
  exact ⟨_, _, _, Qsag.secp7Mod43_primeSubgroup, secp7Mod43Nullifier, snap,
    Spec.IdealMigrateState.init, _, claim, w, ⟨claim, 150⟩, hStep⟩

theorem inhabited_zkboo_extracted_scalar_claim :
    ∃ (C : Qsag.SwCurve) (G : Qsag.SwPoint) (ord : Nat)
      (grp : Qsag.PrimeSubgroup C G ord)
      (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
      (pk : Qsag.CanonicalSwPk C)
      (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
      (st : Spec.IdealMigrateState (Qsag.CanonicalSwPk C))
      (shares : Fin 3 → Nat) (e1 e2 : Fin 3) (amount : Nat),
      Spec.NullifierInjOn deriveNullifier (snapshot.map Prod.fst) ∧
      (Spec.idealMigrateMachine (dlogOwnershipScheme grp deriveNullifier) snapshot).Reachable st ∧
      e1 ≠ e2 ∧
      Qsag.ZkBooDlogCommitted grp pk.toSwPoint shares ∧
      Spec.EnrolledEntitlement snapshot pk amount ∧
      pk ∉ st.settledClaims.map (fun r => r.claim.legacyPk) := by
  let pk2 := Qsag.secp7Mod43Pk2
  let snap : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk Qsag.Weierstrass.secp7Mod43) := [(pk2, 250)]
  let shares : Fin 3 → Nat := fun i => if i.val < 2 then 1 else 0
  have hSmul2 : Qsag.secp7Mod43_primeSubgroup.smul 2 = pk2.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.2.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.2.2.1
  have hDlog : Qsag.ZkBooDlogCommitted Qsag.secp7Mod43_primeSubgroup pk2.toSwPoint shares := by
    refine (Qsag.ZkBooDlogCommitted_iff _ _ _).mpr ?_
    have hRec : Qsag.zkbooReconstructScalar 31 (shares 0) (shares 1) (shares 2) = 2 :=
      (Qsag.zkbooReconstructScalar_eq 31 _ _ _).trans rfl
    rw [hRec]
    exact ⟨by decide, by decide, hSmul2⟩
  have hEnt : Spec.EnrolledEntitlement snap pk2 250 := by
    show Spec.EnrolledSnapshot.entitlement snap pk2 = some 250
    simp only [snap, Spec.EnrolledSnapshot.entitlement, ↓reduceIte]
  exact ⟨_, _, _, Qsag.secp7Mod43_primeSubgroup, secp7Mod43Nullifier, pk2, snap,
    Spec.IdealMigrateState.init, shares, 0, 1, 250,
    secp7Mod43Nullifier_injective.injOn _,
    ⟨Spec.IdealMigrateState.init, [], rfl, .nil _⟩,
    by decide, hDlog, hEnt, fun h => nomatch h⟩

/-- Joint witness for the premises of `dlogSettlement_schedule_complete_of_injOn` on `secp7Mod43`:
    one instance (group, nullifier, decoder, destination encoding, snapshot of two keys, schedule of
    three submissions) in which the destination encoding is injective, the nullifier is injective
    on the snapshot, and the schedule settles exactly the enrolled keys. -/
theorem inhabited_dlogSettlement_schedule_complete :
    ∃ (C : Qsag.SwCurve) (G : Qsag.SwPoint) (ord : Nat)
      (grp : Qsag.PrimeSubgroup C G ord)
      (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
      (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
      (destinationBytes : BitVec 256 → Spec.Bytes)
      (hDestInj : ∀ {d₁ d₂ : BitVec 256}, destinationBytes d₁ = destinationBytes d₂ → d₁ = d₂)
      (migrationDomain : BitVec 256) (epoch : UInt64)
      (compile : MigrationExecution.Statement → List MigrationExecution.Gate)
      (snapshot : Spec.EnrolledSnapshot (Qsag.CanonicalSwPk C))
      (subs : List (MigrationExecution.Submission DlogSettlementAuth)),
      Spec.NullifierInjOn deriveNullifier (snapshot.map Prod.fst) ∧
      (runRawSettlementSchedule
        (dlogSettlementWire ord legacyPkOf destinationBytes hDestInj migrationDomain epoch)
        snapshot (dlogSettlementVerify grp deriveNullifier legacyPkOf migrationDomain epoch)
        compile ⟨[]⟩ subs).2.map (fun io => io.2.claim.legacyPk) = snapshot.map Prod.fst :=
  ⟨_, _, _, Qsag.secp7Mod43_primeSubgroup, secp7Mod43Nullifier, secp7Mod43DecodePk,
    unaryDestBytes, unaryDestBytes_injective,
    MigrationExecution.honestSubmission.statement.migrationDomain,
    MigrationExecution.honestSubmission.statement.epoch, secp7Mod43Compile,
    [(Qsag.secp7Mod43Pk1, 150), (Qsag.secp7Mod43Pk2, 250)], _,
    secp7Mod43Nullifier_injective.injOn _,
    secp7Mod43_dlogSettlement_complete_refinement_witness.2.2.2.2.1⟩

/-- Joint witness for the premises of `singleChallengeZkBoo_two_transcript_extract_or_collision`
    on `secp7Mod43`: two distinct single-challenge ZKBoo proofs (`e = 0` and `e = 1`) for `pk1`
    (`sk = 1`) whose commitments agree and whose extracted `DlogSettlementAuth` verifies. -/
theorem inhabited_singleChallengeZkBoo_two_transcript_extract :
    ∃ (C : Qsag.SwCurve) (G : Qsag.SwPoint) (ord : Nat)
      (grp : Qsag.PrimeSubgroup C G ord)
      (deriveNullifier : Qsag.CanonicalSwPk C → Spec.Digest256)
      (legacyPkOf : List UInt8 → Option (Qsag.CanonicalSwPk C))
      (commitShare : Fin 3 → Nat → Spec.Digest256)
      (migrationDomain : BitVec 256) (epoch : UInt64)
      (st : MigrationExecution.Statement) (pk : Qsag.CanonicalSwPk C)
      (shares : Fin 3 → Nat)
      (pf1 pf2 : SingleChallengeZkBooProof),
      legacyPkOf st.legacyCommitment = some pk ∧
      Qsag.ZkBooDlogCommitted grp pk.toSwPoint shares ∧
      (∀ i : Fin 3, pf1.shareCommits i = commitShare i (shares i)) ∧
      (∀ i : Fin 3, pf2.shareCommits i = pf1.shareCommits i) ∧
      pf1.e = 0 ∧ pf2.e = 1 ∧
      singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
        migrationDomain epoch st pf1 = true ∧
      singleChallengeZkBooVerify deriveNullifier legacyPkOf commitShare
        migrationDomain epoch st pf2 = true := by
  let shares : Fin 3 → Nat := fun i => if i.val = 0 then 1 else 0
  let commitShare : Fin 3 → Nat → Spec.Digest256 :=
    fun i s => BitVec.ofNat 256 (i.val + 4 * s)
  let dom := MigrationExecution.honestSubmission.statement.migrationDomain
  let ep := MigrationExecution.honestSubmission.statement.epoch
  let st : MigrationExecution.Statement :=
    { legacyCommitment := [2, 12]
      migrationDomain := dom
      epoch := ep
      destination := 0xAA#256
      nullifier := secp7Mod43Nullifier Qsag.secp7Mod43Pk1 }
  let pf1 : SingleChallengeZkBooProof :=
    ⟨0, (1, 0), fun i => commitShare i (shares i), 0xAA#256⟩
  let pf2 : SingleChallengeZkBooProof :=
    ⟨1, (0, 0), fun i => commitShare i (shares i), 0xAA#256⟩
  have hPk : secp7Mod43DecodePk st.legacyCommitment = some Qsag.secp7Mod43Pk1 :=
    secp7Mod43DecodePk_eq_some Qsag.secp7Mod43_canonicalPks_props.1
  have hSmul1 : Qsag.secp7Mod43_primeSubgroup.smul 1 = Qsag.secp7Mod43Pk1.toSwPoint := by
    rw [Qsag.secp7Mod43_primeSubgroup_smul_eq, Qsag.secp7Mod43_canonicalPks_props.1]
    exact Qsag.Weierstrass.secp7Mod43_projection_coordinates.1
  have hDlog : Qsag.ZkBooDlogCommitted Qsag.secp7Mod43_primeSubgroup
      Qsag.secp7Mod43Pk1.toSwPoint shares := by
    rw [Qsag.ZkBooDlogCommitted_iff]
    have hRec : Qsag.zkbooReconstructScalar 31 (shares 0) (shares 1) (shares 2) = 1 :=
      (Qsag.zkbooReconstructScalar_eq 31 _ _ _).trans rfl
    rw [hRec]
    exact ⟨by decide, by decide, hSmul1⟩
  have hVer1 : singleChallengeZkBooVerify secp7Mod43Nullifier secp7Mod43DecodePk commitShare
      dom ep st pf1 = true := by
    unfold singleChallengeZkBooVerify
    rw [hPk]
    exact decide_eq_true ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hVer2 : singleChallengeZkBooVerify secp7Mod43Nullifier secp7Mod43DecodePk commitShare
      dom ep st pf2 = true := by
    unfold singleChallengeZkBooVerify
    rw [hPk]
    exact decide_eq_true ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨_, _, _, Qsag.secp7Mod43_primeSubgroup, secp7Mod43Nullifier, secp7Mod43DecodePk,
    commitShare, dom, ep, st, Qsag.secp7Mod43Pk1, shares, pf1, pf2,
    hPk, hDlog, fun _ => rfl, fun _ => rfl, rfl, rfl, hVer1, hVer2⟩

/-! ## 8. Curve moduli primality and the `zk-Hem v2` R1CS migration machine -/

/-- **Primality of the migration curve moduli (`production_curves_all_certified_prime`).**
    `IsPrimeNat` of the base-field and scalar-order moduli of `secp256k1`, `Ed25519`,
    `Pallas`/`Vesta`, `Jubjub` and `BLS12-381` (Pocklington certificates checked by the kernel,
    `Math.CurvePrimeCerts` and its imports), and of `baseP` and `scalarOrd` of every
    `ZkHemV2Migration.MigrationCurveKind`. The statement is about twelve integers; the generator
    checks of `CertifiedPrimeScalarCurve` (`smul_ord_id`, `smul_one_nonid`) are not restated. -/
theorem production_curves_all_certified_prime :
    Qsag.IsPrimeNat Qsag.SECP256K1_FIELD_P ∧
    Qsag.IsPrimeNat Qsag.SECP256K1_ORDER_N ∧
    Qsag.IsPrimeNat Qsag.P_ED25519 ∧
    Qsag.IsPrimeNat Qsag.R_ED25519 ∧
    Qsag.IsPrimeNat Qsag.p_pallas ∧
    Qsag.IsPrimeNat Qsag.q_pallas ∧
    Qsag.IsPrimeNat Qsag.p_vesta ∧
    Qsag.IsPrimeNat Qsag.q_vesta ∧
    Qsag.IsPrimeNat Qsag.q_jubjub ∧
    Qsag.IsPrimeNat Qsag.R_JUBJUB ∧
    Qsag.IsPrimeNat Qsag.p_bls381 ∧
    Qsag.IsPrimeNat Qsag.r_bls381 ∧
    (∀ k : Qsag.ZkHemV2Migration.MigrationCurveKind,
      Qsag.IsPrimeNat k.cert.baseP ∧ Qsag.IsPrimeNat k.cert.scalarOrd) :=
  ⟨Qsag.all_production_curve_moduli_prime.1,
   Qsag.all_production_curve_moduli_prime.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.2.2.2.2.1,
   Qsag.all_production_curve_moduli_prime.2.2.2.2.2.2.2.2.2.2.2,
   fun k =>
     ⟨(Qsag.ZkHemV2Migration.migrationCurveKind_all_certified_prime k).1,
      (Qsag.ZkHemV2Migration.migrationCurveKind_all_certified_prime k).2.1⟩⟩

/-- **Accepted `zkHemV2MigrationMachine` step: owning witness, or a statement outside the WHIR
    language whose Fiat–Shamir acceptance is below `2^-128`
    (`zkHemV2_r1cs_migration_extract_or_qrom_128_break`).**
    For `16 ≤ logCells ≤ 28` and `Q ≤ 2^64`, if `zkHemV2MigrationMachine` accepts `sub`, then
    either `extract sub` satisfies `Spec.ValidLegacyOwnership` for
    `ZkHemV2Migration.realCurveR1csScheme` (snapshot entitlement, derived nullifier, `ownsKey`),
    the nullifier was unspent and the receipt carries the claim; or the lifted statement of `sub`
    is outside `whirInLang` of `ZkHemV2Cert.zkHemV2ProdSched logCells`, and then every `Q`-query
    adversary's succinct Fiat–Shamir acceptance probability on it is below `2^-128`.
    The split is the decidable `checkOwnership` on `extract sub`. Hypotheses, none discharged here:
    * `hCodeSound`: language membership of the lifted statement implies `ownsKey` for
      `extract sub`. This is the knowledge-soundness content; `extract`, `claimOf` and `tblOf` are
      parameters and no extractor is constructed.
    * `sc`: a `ClosedWhir.WhirScheduleCert` for `zkHemV2ProdSched logCells` at width `400`. None
      is constructed for a deployed table size.
    * In the second branch, the Merkle-root consistency premise and the collision-event bound
      `ZkHemV2Cert.merkle400QromBound Q` are premises of the implication.
    `verifyProof` is an arbitrary Boolean function: nothing relates it to `succinctFsAccept`, so
    the second branch bounds the WHIR verifier's acceptance, not `verifyProof`'s.
    `realCurveR1csScheme.ownsKey` asks for `0 < sk < scalarOrd`, equality of both canonical affine coordinates
    with the computed scalar multiple of the curve generator, destination binding, and
    `r1csSatisfied (shapeOf curve) (pubInputsOf claim) wires`; `shapeOf` and `pubInputsOf` are
    parameters. Mapping the proof-system wires to the extracted scalar remains part of extractor soundness.
    `IsPrimeNat … scalarOrd` holds for every `MigrationCurveKind` regardless of the step. -/
theorem zkHemV2_r1cs_migration_extract_or_qrom_128_break {D : Type} [DecidableEq D]
    {cardX cardAnc Q : Nat} (logCells : Nat)
    (hLo : 16 ≤ logCells) (hHi : logCells ≤ 28) (hQ : Q ≤ 2 ^ 64)
    (shapeOf : Qsag.ZkHemV2Migration.MigrationCurveKind → Qsag.ZkHemV2Migration.R1csShape)
    (pubInputsOf : Qsag.Spec.MigrationClaim Qsag.ZkHemV2Migration.LegacyCredential →
      List Qsag.Goldilocks)
    (deriveNullifier : Qsag.ZkHemV2Migration.LegacyCredential → Qsag.Spec.Digest256)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.ZkHemV2Migration.LegacyCredential)
    (verifyProof : Qsag.ZkHemV2Migration.ZkHemV2MigrationSubmission D → Bool)
    (extract : Qsag.ZkHemV2Migration.StraightLineExtractor D)
    (env : Qsag.ClosedWhir.WhirEnv Qsag.QuinticGoldilocks)
    (M : Qsag.ClosedFs.MerkleSetup D Qsag.QuinticGoldilocks) (dfltRoot : D)
    (sc : Qsag.ClosedWhir.WhirScheduleCert env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
    (codec : Qsag.ClosedFs.FsCodec
      (Qsag.ClosedFs.SuccinctRoundMsg D (Qsag.ClosedWhir.WhirPub Qsag.QuinticGoldilocks))
      (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells).numRounds cardX)
    (aux : Fin cardX → List (Qsag.QuinticGoldilocks × List D))
    (claimOf : Qsag.ZkHemV2Migration.ZkHemV2MigrationSubmission D → Qsag.QuinticGoldilocks)
    (tblOf : Nat → D → Nat → Qsag.QuinticGoldilocks)
    (hCodeSound : ∀ sub : Qsag.ZkHemV2Migration.ZkHemV2MigrationSubmission D,
      Qsag.ClosedWhir.whirInLang env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
        ((Qsag.ClosedWhir.whirSuccinctBridge env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
          400 dfltRoot).liftStmt (claimOf sub) (fun _ => sub.proof.initRoot) tblOf) →
      (Qsag.ZkHemV2Migration.realCurveR1csScheme shapeOf pubInputsOf deriveNullifier).ownsKey
        sub.claim.legacyPk (extract sub) sub.claim)
    {st st' : Qsag.ZkHemV2Migration.ZkHemV2MigrateState}
    {sub : Qsag.ZkHemV2Migration.ZkHemV2MigrationSubmission D}
    {out : Qsag.Spec.MigrationReceipt Qsag.ZkHemV2Migration.LegacyCredential}
    (hStep : (Qsag.ZkHemV2Migration.zkHemV2MigrationMachine verifyProof deriveNullifier
      snapshot).step st sub = some (st', out)) :
    (Qsag.Spec.ValidLegacyOwnership
        (Qsag.ZkHemV2Migration.realCurveR1csScheme shapeOf pubInputsOf deriveNullifier)
        snapshot sub.claim (extract sub) out.amount ∧
      Qsag.IsPrimeNat sub.claim.legacyPk.curve.cert.scalarOrd ∧
      sub.claim.nullifier ∉ st.spentNullifiers ∧
      out.claim = sub.claim) ∨
    (¬ Qsag.ClosedWhir.whirInLang env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
        ((Qsag.ClosedWhir.whirSuccinctBridge env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
          400 dfltRoot).liftStmt (claimOf sub) (fun _ => sub.proof.initRoot) tblOf) ∧
      ((∀ (H : Fin cardX → BitVec 400) (o : Fin cardX),
          Qsag.ClosedFs.succinctFsAccept
            (Qsag.ClosedWhir.whirOracleIop env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
            (Qsag.ClosedWhir.whirSuccinctBridge env (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells)
              400 dfltRoot)
            M codec aux (claimOf sub) (fun _ => sub.proof.initRoot) H o = true →
          let str := Qsag.ClosedFs.fsTranscript codec H (codec.dec o)
          ∀ q ∈ (Qsag.ClosedWhir.whirOracleIop env
              (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400).queries (claimOf sub)
              (str.map (fun sc' => (sc'.1.pub, sc'.2))),
            M.root q.1 ((Qsag.ClosedWhir.whirOracleIop env
                (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400).depth q.1)
              (tblOf q.1 ((Qsag.ClosedWhir.whirSuccinctBridge env
                (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
                (fun _ => sub.proof.initRoot) (str.map Prod.fst) q.1)) =
              (Qsag.ClosedWhir.whirSuccinctBridge env
                (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot).rootsOf
                (fun _ => sub.proof.initRoot) (str.map Prod.fst) q.1) →
        ∀ (A : Qsag.QuantumAdv cardX 400 cardAnc Q),
        Qsag.RatBound.le
          ⟨Qsag.uniformOracleSum 400 cardX (fun H =>
              Qsag.QVec.queryMassOn
                (Qsag.ClosedFs.succinctFsCollisionEvent
                  (Qsag.ClosedWhir.whirOracleIop env
                    (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
                  (Qsag.ClosedWhir.whirSuccinctBridge env
                    (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot)
                  M codec aux (claimOf sub) (fun _ => sub.proof.initRoot) tblOf H)
                (Qsag.runQuantumAdv A H)),
            (2 ^ 400) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
            Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 400))
              (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
          (Qsag.ZkHemV2Cert.merkle400QromBound Q) →
        Qsag.RatBound.lt
          ⟨Qsag.uniformOracleSum 400 cardX (fun H =>
              Qsag.QVec.queryMassOn
                (Qsag.ClosedFs.succinctFsAccept
                  (Qsag.ClosedWhir.whirOracleIop env
                    (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400)
                  (Qsag.ClosedWhir.whirSuccinctBridge env
                    (Qsag.ZkHemV2Cert.zkHemV2ProdSched logCells) 400 dfltRoot)
                  M codec aux (claimOf sub) (fun _ => sub.proof.initRoot) H)
                (Qsag.runQuantumAdv A H)),
            (2 ^ 400) ^ cardX * (Qsag.prefixScale A Q (Nat.le_refl Q) * Qsag.QVec.stateNormSq A.init),
            Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 400))
              (Nat.mul_pos (Qsag.prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
          (Qsag.RatBound.invPow2 128))) :=
  Qsag.ZkHemV2Migration.zkHemV2_r1cs_single_transcript_extract_or_qrom_128_break
    logCells hLo hHi hQ shapeOf pubInputsOf deriveNullifier snapshot verifyProof extract env M
    dfltRoot sc codec aux claimOf tblOf hCodeSound hStep

/-- **Conservation and no double claim along every reachable trace of
    `zkHemV2MigrationMachine`**, given `ZkHemV2Migration.ZkHemV2ExtractorSound` (every submission
    `verifyProof` accepts has `ownsKey` for `extract`; a hypothesis, not proved for any verifier):
    the total migrated is at most the enrolled total, spent nullifiers are distinct, and settled
    legacy keys are distinct. Obtained from the `Spec.DataRefines` simulation into
    `Spec.idealMigrateMachine`. -/
theorem zkHemV2_r1cs_migration_trace_conservation_and_nodup {D : Type}
    (shapeOf : Qsag.ZkHemV2Migration.MigrationCurveKind → Qsag.ZkHemV2Migration.R1csShape)
    (pubInputsOf : Qsag.Spec.MigrationClaim Qsag.ZkHemV2Migration.LegacyCredential →
      List Qsag.Goldilocks)
    (deriveNullifier : Qsag.ZkHemV2Migration.LegacyCredential → Qsag.Spec.Digest256)
    (snapshot : Qsag.Spec.EnrolledSnapshot Qsag.ZkHemV2Migration.LegacyCredential)
    (verifyProof : Qsag.ZkHemV2Migration.ZkHemV2MigrationSubmission D → Bool)
    (extract : Qsag.ZkHemV2Migration.StraightLineExtractor D)
    (hSound : Qsag.ZkHemV2Migration.ZkHemV2ExtractorSound shapeOf pubInputsOf deriveNullifier
      verifyProof extract)
    {st : Qsag.ZkHemV2Migration.ZkHemV2MigrateState}
    (hReach : (Qsag.ZkHemV2Migration.zkHemV2MigrationMachine verifyProof deriveNullifier
      snapshot).Reachable st) :
    st.totalMigrated ≤ Qsag.Spec.EnrolledSnapshot.total snapshot ∧
    st.spentNullifiers.Nodup ∧
    (st.settledClaims.map (fun r => r.claim.legacyPk)).Nodup :=
  Qsag.ZkHemV2Migration.zkHemV2Migration_trace_conservation_and_nodup
    shapeOf pubInputsOf deriveNullifier snapshot verifyProof extract hSound hReach

#verify_constructive
  Qsag.Top.legacy_curve_primality_extraction_and_ideal_migration_chain
  Qsag.Top.active_migration_ceremony_qrom_and_gf2pow128_chain
  Qsag.Top.migration_bit_check_staged_count_numerator_63
  Qsag.Top.migration_bit_check_concrete_bound_63
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.tooth_dlogOwnership_rejects_destination_swap
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement_or_collision
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.rawSettlement_accepted_decodes
  Qsag.Top.rawSettlement_rejected_ledger_unchanged
  Qsag.Top.rawSettlement_accepted_ownership
  Qsag.Top.rawSettlement_trace_simulated
  Qsag.Top.rawSettlement_trace_ownership_nodup_conservation
  Qsag.Top.runRawSettlementSchedule_validTrace
  Qsag.Top.rawSettlement_schedule_refines_or_nullifierCollision
  Qsag.Top.rawSettlement_schedule_complete_of_injOn
  Qsag.Top.tooth_rawSettlement_undecodable_submission_rejected
  Qsag.Top.tooth_rawSettlement_unenrolled_submission_rejected
  Qsag.Top.tooth_rawSettlement_receipt_destination_not_substituted
  Qsag.Top.tooth_rawSettlement_resubmission_other_destination_rejected
  Qsag.Top.migrationToy_circuitSound
  Qsag.Top.migrationToy_honest_submission_accepted
  Qsag.Top.tooth_migrationToy_forged_nullifier_rejected
  Qsag.Top.dlogSettlement_circuitSound
  Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision
  Qsag.Top.tooth_singleChallengeZkBoo_hides_scalar
  Qsag.Top.dlogSettlement_refinement_exists
  Qsag.Top.dlogSettlement_schedule_refines_or_nullifierCollision
  Qsag.Top.dlogSettlement_schedule_complete_of_injOn
  Qsag.Top.tooth_dlogSettlement_destination_tamper_rejected
  Qsag.Top.secp7Mod43Nullifier_injective
  Qsag.Top.tooth_secp7Mod43DecodePk_rejects_offCurve_and_unreduced
  Qsag.Top.secp7Mod43_dlogSettlement_honest_accepted
  Qsag.Top.secp7Mod43_dlogSettlement_complete_refinement_witness
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_extracts_collision
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_blocks_honest_owner
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_snapshot_collision
  Qsag.Top.bls381_dlogSettlement_refines_or_nullifierCollision
  Qsag.Top.bls381_compressing_nullifier_nonvacuous
  Qsag.Top.inhabited_dlogOwnership_accepted_claim
  Qsag.Top.inhabited_zkboo_extracted_scalar_claim
  Qsag.Top.inhabited_dlogSettlement_schedule_complete
  Qsag.Top.inhabited_singleChallengeZkBoo_two_transcript_extract
  Qsag.Top.production_curves_all_certified_prime
  Qsag.Top.zkHemV2_r1cs_migration_extract_or_qrom_128_break
  Qsag.Top.zkHemV2_r1cs_migration_trace_conservation_and_nodup

#verify_inhabited
  Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar
  Qsag.Top.inhabited_dlogOwnership_accepted_claim
#verify_inhabited
  Qsag.Top.zkboo_extracted_scalar_claims_enrolled_entitlement
  Qsag.Top.inhabited_zkboo_extracted_scalar_claim
#verify_inhabited
  Qsag.Top.dlogSettlement_schedule_complete_of_injOn
  Qsag.Top.inhabited_dlogSettlement_schedule_complete
#verify_inhabited
  Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision
  Qsag.Top.inhabited_singleChallengeZkBoo_two_transcript_extract

#tooth_pair Qsag.Top.migration_bit_check_concrete_bound_63 vs
  Qsag.MigrationExecution.tooth_rust_bit_check_numerator_62_too_small
#tooth_pair Qsag.Top.singleChallengeZkBoo_two_transcript_extract_or_collision vs
  Qsag.Top.tooth_singleChallengeZkBoo_hides_scalar

#tooth_pair Qsag.Top.dlogOwnership_accepted_claim_has_unique_scalar vs
  Qsag.Top.tooth_dlogOwnership_rejects_destination_swap
#tooth_pair Qsag.Top.secp7Mod43_dlogSettlement_honest_accepted vs
  Qsag.Top.tooth_dlogSettlement_destination_tamper_rejected
#tooth_pair Qsag.Top.secp7Mod43_dlogSettlement_complete_refinement_witness vs
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_blocks_honest_owner
#tooth_pair Qsag.Top.dlogSettlement_schedule_complete_of_injOn vs
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_blocks_honest_owner
#tooth_pair Qsag.Top.dlogSettlement_schedule_refines_or_nullifierCollision vs
  Qsag.Top.tooth_dlogSettlement_xOnlyNullifier_snapshot_collision

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
#tooth_pair Qsag.Top.production_curves_all_certified_prime vs
  Qsag.tooth_cofactor8_edwards_orders_not_prime
#tooth_pair Qsag.Top.zkHemV2_r1cs_migration_extract_or_qrom_128_break vs
  Qsag.ZkHemV2Migration.tooth_zkHemV2MigrationMachine_rejects_double_nullifier

end Qsag.Top
end
