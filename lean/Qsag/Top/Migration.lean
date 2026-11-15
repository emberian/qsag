module
public import Qsag.Machine.Gf128ClmulLoopAgreement
/-
# Qsag.Top.Migration — End-to-End Composed Post-Quantum Ownership Migration Security

Top-level composition module (zero `import all`) connecting:
1. Ideal nullifier-uniqueness and pool-cap conservation (`Spec.IdealMigrate`),
2. Constructive Pocklington–Pratt primality certificates for `secp256k1` field and scalar-order
   primes (`PrattPrimalityCert`),
3. `ZKBoo` 2-of-3 special-soundness scalar extraction, Zcash Orchard `RedPallas` rerandomized key
   extraction, and active field-check bounds across `secp256k1`, `Ed25519`, `BLS12-381`, `Pallas`,
   and `Goldilocks³` (`PallasAndBlsMigration`), and
4. Unconditional 438-repetition circuit-to-sacrifice ceremony defect bounds, QROM soundness scaling,
   and five-way `𝔽_{2^{128}}` multiplication equivalence (`ActiveMigrationZeroTest`, `Math.Gf2Pow128`).
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
    1. Every reachable state of `idealMigrateMachine` maintains `spentNullifiers.Nodup` and
       `totalMigrated ≤ poolCap₀`,
    2. `secp256k1` base-field and scalar-order moduli are constructively certified primes,
    3. Distinct `ZKBoo` opened views `(e₁ ≠ e₂)` extract the unique canonical secret scalar `sk < ord`
       satisfying `grp.smul sk = pk`, and
    4. `RedPallas` rerandomized views extract `(ask, alpha, rsk)` satisfying `grp.add (grp.smul ask) (grp.smul alpha) = rk`! -/
theorem legacy_curve_primality_extraction_and_ideal_migration_chain
    (poolCap₀ : Nat) {stMig : Qsag.Spec.IdealMigrateState}
    (hReach : (Qsag.Spec.idealMigrateMachine poolCap₀).Reachable stMig)
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
    (stMig.totalMigrated ≤ poolCap₀ ∧ stMig.spentNullifiers.Nodup) ∧
    (Qsag.Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F ∧
     Qsag.Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 ∧
     Qsag.Weierstrass.IsPrime targetPrime) ∧
    (0 < sk ∧ sk < ord ∧ grp.smul sk = pk) ∧
    (grpPal.add (grpPal.smul ask) (grpPal.smul alpha) = rk) ∧
    (Qsag.ActiveFieldCheckBound 35 250 Qsag.migrationSecp256k1P ∧
     Qsag.ActiveFieldCheckBound 35 249 Qsag.p_bls381 ∧
     Qsag.ActiveFieldCheckBound 35 248 Qsag.p_pallas) := by
  obtain ⟨_, hCap, _, hNd⟩ := Qsag.Spec.idealMigrateMachine_reachable_inv poolCap₀ hReach
  obtain ⟨hSkPos, hSkLt, hSmul, _⟩ :=
    Qsag.zkboo_two_challenge_extraction_sound grp shares e1 e2 hNe hValidDlog
  obtain ⟨_, _, _, _, _, hPalEq, _⟩ :=
    Qsag.orchard_redpallas_rerandomized_extraction_sound grpPal askShares alphaShares e1 e2 hNe
      hAskRange hAlphaRange hRskPos hCurveRk
  obtain ⟨hSecp, _, hBlsP, _, hPalP, _, _⟩ := Qsag.migration_active_field_check_exact_bounds
  exact ⟨⟨hCap, hNd⟩,
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

#verify_constructive
  Qsag.Top.legacy_curve_primality_extraction_and_ideal_migration_chain
  Qsag.Top.active_migration_ceremony_qrom_and_gf2pow128_chain

end Qsag.Top
end
