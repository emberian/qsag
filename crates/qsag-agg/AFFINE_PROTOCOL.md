# Hem affine monomial protocol

The PCS implements the equal-degree combiner in [CWYZ26, Theorem 5.1](https://eprint.iacr.org/2026/2863) and the asymmetric cascade of Section 5. The aggregate wire header is version 6; the PCS transcript additionally absorbs `AFFINE_MONOMIAL_V1`. Old openings are incompatible.

## Witness and dual functional

The initial Boolean evaluation table is converted once to monomial coefficients. All subsequent witness folds operate directly on coefficients, including two explicit overflow slots. For even and odd coefficient vectors F and G, one fold produces

`P(Y) = G(Y) + (alpha + beta Y) (F(Y) + theta G(Y))`.

Multiplication by Y shifts an array index. The degree recurrence is `d' = floor(d/2) + 1`; both single inputs of degree `2^nv - 1` and batched inputs of degree `2^nv` remain within `2^remaining + 1`. Intermediate encodings use the existing power-of-two core NTT and add the two overflow monomials on the same coset. Domain sizes and tree depths do not increase.

Each fold carries five extension-field scalars. Given the current claim `<c,k> = sigma`, the transcript proceeds in this order:

1. Absorb `sigma_even = <F,k_even>`, `tau_01 = <F,k_odd>`, and `tau_10 = <G,k_even>`.
2. Squeeze phi and form `v = k_even + phi k_odd`, with a trailing zero slot.
3. Absorb `c_F = <Y F,v>` and `c_G = <Y G,v>`.
4. Squeeze theta, alpha, beta and set
   `gamma_F = sigma_even + phi tau_01`,
   `gamma_G = tau_10 + phi (sigma - sigma_even)`,
   `sigma' = gamma_G + alpha (gamma_F + theta gamma_G) + beta (c_F + theta c_G)`.

The verifier retains tensor kernels and their two overflow weights rather than allocating witness-sized vectors. Prefix contractions are products of `1 + phi_j r_j`; overflow weights propagate separately. Its terminal inner product includes both overflow coefficients.

## Batching and oracle binding

Point reduction still establishes each input's evaluation at a common multilinear point. Before any cascade challenges, the prover absorbs each shifted monomial functional evaluation. The first two inputs use the equal-degree combiner. Every later input contributes `(alpha_i + beta_i X) W_i`, so degree growth is exactly one regardless of batch size. Stage-zero openings apply these affine weights at each actual base-field coset coordinate.

Each committed stage receives two independent OOD points. Both evaluations are absorbed before the batching weights are squeezed. Intermediate commitments and both OOD evaluations precede the previous stage's query challenges; final coefficients precede final query challenges. The final polynomial has exactly `2^early_stop + 2` coefficients.

## Accounting boundary

The Johnson QROM schedule (`BciksJohnsonQrom128`) uses `ceil(512/log2(B)) + 2`, giving `(258,130,88,66)` for blowups `(4,16,64,256)`. Classical Johnson (`BciksJohnsonClassical128`) uses `ceil(256/log2(B)) + 1` and is restricted to raw PCS tests (rejected by QROM-128 aggregate validation). Retired capacity-proximity wire tags (`0`, `1`, `3`) fail closed on deserialization (`Crites & Stewart 2025/2046`, `Krachun-Kazanin-Habock 2026/782`). Queries are sampled without replacement and become exhaustive when the target exceeds the number of fibers.

The finite-witness regression checks all 46 non-exhaustive canonical Johnson QROM stages across `nv = 2..24`: exact Theorem 4.8 interpolation inequalities, Johnson list bounds, query error below `2^-256` including the stage fold-coordinate loss, and stage affine-combiner error below `2000/p^4` (more than 245 bits). Its dyadic probability calculation rounds upward at every division; it uses no floating-point approximations. The other stages are queried exhaustively.

These implementation and arithmetic tests do not constitute a complete Fiat–Shamir or QROM security proof. Cascade coordinate losses and protocol-wide union bounds must still be composed separately. Formal security-budget sources outside this crate are not modified by this upgrade.

## Validation

- `cargo clippy -p qsag-agg --all-targets -- -D warnings`: passed.
- `cargo check -p qsag-agg --no-default-features`: passed.
- `cargo test --release -p qsag-agg`: passed.
- The adversarial tests cover all five fold scalars, both shifted claims, both overflow coefficients, both OOD samples at every stage, batch sizes through 16, both signature profiles, and homogeneous merge trees.
- Repository terminology scan: zero findings.

## Release measurements

Intel Core i9-12900, 12 GiB build/run memory cap, K=8, default shard sizing, shared message. Prove is one timed aggregation (key generation/signing excluded); verify is the median of three successful checks. Bytes are the full serialized aggregate, including its wire header. Timings are observations on a shared machine, not statistical performance guarantees.

Command: `cargo test --release -p qsag-agg bench_affine_regimes -- --ignored --nocapture --test-threads=1`.

| Profile | Regime | Proof bytes | Prove ms | Verify median ms |
|---|---|---:|---:|---:|
| JortsPoseidon2 | BciksJohnsonQrom128 | 291352 | 4897.351 | 26.692 |
| CorduroyPoseidon2 | BciksJohnsonQrom128 | 446254 | 48844.355 | 35.330 |
