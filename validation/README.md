# QSAG External Differential Validation & Specification Oracle Suite

Standalone Cargo workspace (`validation/`) and `libFuzzer` harness workspace (`../fuzz/`) that cross-validate both the zero-dependency production `qsag-*` Rust crates and the Lean 4 executable specifications (`../lean/Qsag/*.lean`) against independent upstream cryptography implementations and standard test vectors.

Keeping `validation/` and `fuzz/` as independent Cargo workspaces preserves the zero-dependency footprint of the core library crates (`#![no_std]` / WASM / embedded friendly) while testing every cryptographic primitive, hardware SIMD backend (`AVX-512`, `GFNI`, `VPCLMULQDQ`, `SHA-NI`, `AVX2`, `BMI2/ADX`, and portable scalar), threshold MPC engine, and wire decoder against external reference crates.

## Independent Reference Crates

| Domain | QSAG Crates & Lean Specs Under Test | Upstream Reference Crates |
| :--- | :--- | :--- |
| **NIST FIPS 205 (`SLH-DSA`)** | `qsag-core::fips205`, `qsag-core::keccak_mpc` (`RssSlhMpcCluster`), `lean/Qsag/Fips205.lean` | `fips205` (`v0.4`) |
| **NIST FIPS 204 (`ML-DSA`) & NTT** | `qsag-asm::ntt_simd` (`AVX-512`/`AVX2` Seiler NTT), `qsag-cred::fips204_ntt`, `qsag-cred::threshold_mldsa` | `fips204` (`v0.4`) |
| **Sponges, Hashes & Bitslice MPC** | `qsag-asm` (`x86_64` Keccak 8x/4x, `SHA-NI`, 256-lane bitslice), `qsag-accel`, `qsag-core`, `lean/Qsag/Keccak.lean` | `sha3`, `tiny-keccak`, `sha2`, `hmac`, `ripemd`, `blake3` |
| **Finite Fields & Polynomials** | `qsag-asm` (`GFNI` `GF(2^8)`, `VPCLMULQDQ` `GF(2^128)`, `BMI2/ADX` Goldilocks), `qsag-agg::field`, `lean/Qsag/{Goldilocks,BinaryTower,Poseidon2}.lean` | `p3-goldilocks`, `p3-field`, `p3-dft`, `ghash`, `polyval` |
| **Elliptic Curves & PQ Migration** | `qsag-migrate` (`secp256k1_ct`, `ed25519_ct`, `pallas`, `bls12_381`, ZKBoo ceremonies), `lean/Qsag/Secp256k1GroupLaw.lean` | `k256`, `ed25519-dalek`, `curve25519-dalek`, `pasta_curves`, `blstrs` |

## Integration Test Suites (`validation/tests/`)

- `fips205_slh_dsa.rs`: Keygen and deterministic signing bit-exactness across all six `SLH-DSA-SHAKE` parameter sets (`128s`, `128f`, `192s`, `192f`, `256s`, `256f`), bidirectional hedged signing/verification, `HashSLH-DSA` (`SHA-256`, `SHA-512`, `SHAKE256`), X.509 SPKI DER roundtrips, single-bit fault rejection, and 2-of-3 dealerless RSS MPC (`RssSlhMpcCluster`) signatures verified directly under `fips205`.
- `fips204_mldsa_ntt.rs`: 10,000-polynomial `proptest` campaign over the `AVX-512`/`AVX2` Seiler signed-Montgomery NTT (`q = 8380417`) against schoolbook negacyclic convolution in $\mathbb{Z}_q[X]/(X^{256}+1)$, deterministic `ML-DSA-44/65/87` bit-exactness, and 2-of-3 dealerless threshold `ML-DSA-44/65/87` verification under `fips204`.
- `sponges_hashes_simd.rs`: Rate-boundary and unaligned slice sweeps (`0..=16384` bytes, offsets `1..15`, batch sizes `1..=33`) for `Keccak-f[1600]`, `SHA3-256`, `Keccak-256`, `SHAKE256`, `cSHAKE256`, `SHA-NI` `SHA-256`, BIP-340 tagged hashes, `HMAC-SHA512`, `RIPEMD-160`/`HASH160`, `BLAKE3`, 256-lane bitslice transpose, and 256-lane RSS MPC $\chi$-row gates.
- `simd_fields_goldilocks.rs`: Exhaustive 65,536-pair `GF(2^8)` Wiedemann tower $\mathcal{T}_3 \leftrightarrow \text{AES } \mathbb{F}_{2^8}[x]/(x^8+x^4+x^3+x+1)$ `GFNI` affine isomorphism proof, Shamir Lagrange interpolation, `VPCLMULQDQ` `GF(2^128)` MACs vs `ghash`/`polyval`, `Goldilocks` + `Ext2` + `Ext4` + Radix-2 NTT vs Plonky3 `p3-goldilocks`, and Width-12 `Poseidon2` algebraic bijectivity (`perm12_inv(perm12(x)) == x`).
- `curves_secp_ed25519_pallas_bls.rs`: Differential `proptest` suites and 438-repetition ZKBoo migration ceremonies across Bitcoin (`HASH160` + BIP-341 Taproot), Ethereum (`Keccak256` EOA + Beacon `BLS12-381` `0x00`/`0x02` credentials + torsion subgroup rejection), Solana (`Ed25519` + SLIP-0010), and Zcash Orchard (`Pallas` `SpendAuthG` `ak` + `RedPallas` `rk`).
- `lean_spec_oracle.rs`: Evaluates vectors extracted from `validation/lean/ExternalSpecOracle.lean` and `lean/Main.lean` (`qsag-kat`) against both `qsag-*` Rust crates and upstream `fips205`, `sha3`, `tiny-keccak`, `p3-goldilocks`, `ghash`, `k256`, `pasta_curves`, and `blstrs` (including verifying a 17,088-byte `SLH-DSA-SHAKE-128f` signature computed purely inside Lean 4 under `fips205::slh_dsa_shake_128f::PublicKey::verify`).

## Running

```bash
# Run all differential validation and property-based tests
./scripts/run_differential_validation.sh

# Enforce hardware AVX-512 + GFNI + VPCLMULQDQ + SHA-NI dispatch on x86_64 hosts
QSAG_REQUIRE_AVX512=1 ./scripts/run_differential_validation.sh

# Regenerate Lean 4 specification oracle fixtures and run libFuzzer targets (20s each)
./scripts/run_differential_validation.sh --regen-lean --fuzz 20
```
