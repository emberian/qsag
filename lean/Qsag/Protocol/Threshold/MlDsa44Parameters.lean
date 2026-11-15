module
public import Qsag.Math.Constructive

public section
namespace Qsag

/-- FIPS 204 ML-DSA-44 masking range, γ₁ = 2^17. -/
@[expose] def mldsa44Gamma1 : Nat := 131072

/-- FIPS 204 ML-DSA-44 secret-shift bound, β = τ · η = 39 · 2. -/
@[expose] def mldsa44Beta : Nat := 78

end Qsag
