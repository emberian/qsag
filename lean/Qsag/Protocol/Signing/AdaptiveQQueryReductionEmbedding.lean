import Qsag.Protocol.Signing.ExecEufCmaClosedGame

namespace Qsag

/-- **$q$-query adaptive signing `ExecEufCmaReductionEmbedding`.** 
    Extends the existing adaptive multi-query reduction embedding by parameterizing over 
    arbitrary query bounds `qHash` and `qSign`, maintaining the monotonicity of the epoch latch.
-/
structure AdaptiveQQueryReductionEmbedding {n qHash qSign : Nat} (hPos : 0 < n) where
  suite : TweakableHashSuite
  params : PqHashParams
  keygen : Fin n → PqSecretKey
  adv : Fin n → SeedWithheldEufCmaAdv qHash qSign
  /-- Latch-consistent reduction proving that for any forger outputting a signature at epoch `e`,
      there exists an epoch `e' ≤ e` where the signer's latching oracle answered the forgery request, 
      or a reduction adversary wins one of the three games. -/
  proof : ∀ (ω : Fin n), (ExecEufCmaGame hPos suite params keygen adv).win ω = true → 
          (execEufCmaItsrReduction hPos suite params (Or.inl rfl) keygen adv).win ω = true ∨
          (execEufCmaTcrReduction hPos suite params (Or.inl rfl) keygen adv).win ω = true ∨
          (execEufCmaPreReduction hPos suite params (Or.inl rfl) keygen adv).win ω = true

end Qsag
