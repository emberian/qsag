<img src="assets/qsag-mascot.png" alt="qsag mascot" width="120" align="right" />

# qsag

**Post-quantum threshold signing, signature aggregation and key migration.** QSAG lets custodians share a signing key, change the quorum that can use it and compress committee signatures into a publicly verifiable proof.

**Cut-the-Hash** evaluates four secret hash-oracle families inside MPC and builds the public Merkle layers in the clear. **Hem** proves signature verification with sumcheck and Johnson-radius WHIR over the quintic Goldilocks field. A regional verifier can check each committee against a prepared policy registry. A verifier of a contiguous binary tree of Jorts committees can check a single **639,673 B** recursive proof.

[Results and demos](#performance-and-scaling) · [How it works](#how-it-works) · [Try it](#quickstart) · [Cut-the-Hash](paper/cut-the-hash.typ) · [Quintic Hem](paper/quintic-hem.typ) · [Assurance boundaries](ASSURANCE.md)

QSAG is a research prototype without an external audit. Applications supply their own consensus and settlement rules. The papers and crate security specifications state the assumptions behind the cryptographic claims.

## Performance and scaling

| Proof | Input and profile | Serialized size |
| --- | --- | ---: |
| Public `QSAGHQM2` | Four keys, three active, `HemQuinticProfile::TurboShake400` | 360,391 B |
| Public `QSAGHQM2` | Same keys, bitmap and message, `HemQuinticProfile::Poseidon2Gl24` | 381,661 B |
| Recursive `QSAGIVC1` | Contiguous Jorts committees, fixed `[DKT26]` relation, tag `0x00` | 639,673 B |

The public sizes are pinned wire vectors. A regional aggregate includes one proof per committee. The recursive root stays the same size as the tree grows. Its default leaf checks up to 64 signatures among 256 member positions. Within one committee a merge counts the union of signer bitmaps. A merge across adjacent committees adds the signer totals after checking completion. [Public vectors](crates/qsag-agg/src/hem_quintic/tests.rs) · [Recursive verifier](crates/qsag-agg/src/zk_hem/recursive_ivc/)

Selected signing and verification measurements from [Cut-the-Hash](paper/cut-the-hash.typ).

| Operation | Result |
| --- | --- |
| Prepared Jorts threshold signature, 2-of-3 | 1.0 ms in memory; 81 ms over a simulated WAN |
| Prepared BFT Shamir Jorts signature, 3-of-4 | 2.44 ms, 4,172 B |
| Pooled blinded MAC check (`OtMesh`, active Beaver sacrifice), 3 parties | 31 µs online; 4.04 ms amortized offline refill |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| SpongeMacaroon, three caveats | 161 B; 1.8 µs verify |

## How it works

### Threshold signing: keep only the secret hashes in MPC

Cut-the-Hash evaluates four secret oracle families under MPC, checks the custodians' contributions, opens the boundary digests, and computes the public tree above them in the clear. Each Winternitz chain takes at most 16 sequential secret hashes for SLH-DSA and four for Jorts, Baggy and Corduroy, independent of tree height.

For **SLH-DSA (FIPS 205)**, the public assembler uses the standard wire format. Lean proves byte identity for the replicated-sharing oracle model on matched key and randomness. Rust supplies bitsliced 2-of-3 Keccak and per-custodian honest-majority CNF parties. In `IsolatedCnfParty`, custodians compute the shared mask product before drawing the public coin, then open a masked sum and a blinded check value. The SPDZ cluster also implements the SLH-DSA oracles. Authenticated arithmetic over Goldilocks serves the Poseidon2 paths. Per-party protocols share a `no_std` `WireTransport` interface. A local ceremony that loads several custodian files runs within one host's trust boundary.

| Format | Purpose | Signature size |
| --- | --- | --- |
| **Baggy** | Stateless signing; cached public upper layers, pruned PORS+FP few-time tree | At most 71,654 B |
| **Jorts** / **JortsPoseidon2** | Stateful, one online round after preprocessing; Poseidon2 variant feeds Hem | 4,328–4,776 B |
| **Corduroy** | Stateless Poseidon2 hypertree for public aggregation | 76,896 B |
| **FrontierSumFts** (`fts-compact-1122`) | Single-use live votes; SIMD batch verification | 1,122 B, or 1,218 B with 96-byte header |

### Quorum switching: share a key without reusing a leaf

**BeltLatch** records the leaf and intent and syncs the reservation before share release. A TPM NV counter or a directory on disjoint storage can anchor the journal. A VM generation guard adds clone detection. **HemDynamicShamirQuorum** preserves one JortsPoseidon2 validator key across roster and threshold changes. Each detached custodian persists its own leaf floor before acknowledging. The signing subset releases after an honestly intersecting acknowledgment quorum confirms. The successor is released only after durable retirement of predecessor custody.

### Hem aggregation and zero knowledge

All three proof formats use $\mathbb F_{p^5} = \mathbb F_p[X]/(X^5-3)$ with $p=2^{64}-2^{32}+1$.

- **Public committees.** `prove_hem_quintic_128` and `verify_hem_quintic_128` use 50-byte TurboSHAKE256 or seven-limb Poseidon2-GL-w24 Canopy digests. All 138 non-S-box trace columns are pinned to canonical zero on inactive slots. `prove_hierarchical_hem_prepared` and `verify_hierarchical_hem_prepared` compose the proofs against a `PreparedPolicyRegistry` (`QSAGHEM\x04`).
- **Private statements.** zk-Hem v2 uses fresh Stage-0 tree nonces and leaf salts, with joint masking for LogUp lookups. Its single-prover and split-share encodings are `QSAGZKH2` and `QSAGZKS2`. For all 13 table sizes from $2^{16}$ to $2^{28}$ cells, Lean checks rational error budgets below $2^{-128}$ at $Q\le 2^{64}$. Applying those budgets to a verifier requires the protocol reduction, its schedule premises and the ideal-hash assumptions.
- **Recursive roots.** `prove_ivc_tree` and `verify_ivc_tree` use `IvcTreeStepRelation` to check two child WHIR openings and fold their public-matrix claims with a degree-two sumcheck. [Binary IVC](crates/qsag-agg/src/zk_hem/recursive_ivc.rs)

## Quickstart

The workspace pins Rust `1.99.1` and has zero `crates.io` runtime dependencies.

```sh
# Known-answer tests and supported formats.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign --secret "$D/sk.json" --in "$D/msg" \
  --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"

# Aggregate 128 signatures. For a smaller run, append -- --signers 8.
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
```

The default example verified a 1,238,354-byte aggregate for 112 Jorts and 16 Corduroy signers. Their signatures totalled 1,715,072 bytes before aggregation, a 27.8% reduction on the wire. The example prints both sizes and the prover and verifier times. Proof length can vary with the authenticated Merkle paths.

For a public committee proof, `qsag verify-agg --public committee.json --in message.bin --proof proof.json --min-signers 3` requires at least three authenticated signer positions. Use `--allow-any-subset` to accept any nonempty subset. The expected profile defaults to `quintic-turbo`. Select `--hem-profile quintic-gl24` for a GL24 proof. Stateful key enrollment mixes fresh OS entropy into supplied seeds by default. Reproducible test enrollment uses `--deterministic-test-only`. The HD and credential test modes conflict with anchor options.

## Wallets, migration, and capabilities

| Component | What it provides |
| --- | --- |
| `qsag-hd`, `qsag-addr` | The canonical `PiHdCommitInventory` commits an enrolled batch of child public keys. `hd derive` produces a Bech32m address and inclusion proof from the watch-only table. Custody shares are required for private recovery. |
| `qsag-migrate` | The migration CLI supports 19 statement kinds, including Bitcoin/Taproot/Ethereum secp256k1, Solana Ed25519, BLS12-381 and Zcash NU7 Sapling, Orchard, ZIP-2005 Ironwood and ZIP-2007 Transparent. Ownership claims support local `QSAGZKH2` proofs and collaborative `QSAGZKS2` proofs. `hem::collab::Engine::new_anchored` burns `tape_id()` against an `ExternalMonotoneAnchor` before round 1 and uses nine-triple Toom-3 multiplication over `Fp5`. |
| `qsag-policy` | Stateful velocity, allowlist, and window rules checked before custodians release shares |
| `SpongeMacaroon`, `PqBiscuit`, `QSAGCAU1` | Shared-secret caveat verification, public offline delegation via one-use `Compact1122` signatures, and challenge-bound unlinkable zero-knowledge presentations, respectively. |
| `qsag-cred` | Any enrolled `t` of `n` can evaluate the Shamir-SPDZ Poseidon2 TOPRF. Threshold ML-DSA-44/65/87 requires at least `2t − 1` online and keeps `w1` sealed on rejection. Blind credential issuance uses 438 repetitions of three-party Goldilocks MPC-in-the-head. Selective disclosure and private multisignatures use zk-Hem v2. |

## Verification

Lean mechanizes multi-hop signing reductions conditional on `SigningPrimitiveBounds`. For aggregation, the protocol and extractor theorems carry schedule and oracle hypotheses. The 86 extracted definitions of `qsag-whir-verified` cover selected field, decoding, counting and proof-payload operations. The outer Rust verifier drives the transcript and authenticates Merkle openings. [Aggregation security](crates/qsag-agg/SECURITY.md) · [Migration security](crates/qsag-migrate/SECURITY.md)

The standalone hardware repository contains the silicon and FPGA designs and their signoff evidence. [qsag-chip](https://github.com/emberian/qsag-chip)

## Repository map

| Crates / directory | Contents |
| --- | --- |
| `qsag-core`, `qsag-quorum`, `qsag-fts` | Hash-based signatures, MPC engines, quorum switching, hardware anchors, few-time votes |
| `qsag-agg`, `qsag-accel`, `qsag-asm` | Hem / `HemQuintic128` / `zk-Hem v2` / `QSAGIVC1`, RX 6750 XT Vulkan measurements, SIMD and ISA-level assembly evidence |
| `qsag-hd`, `qsag-addr`, `qsag-policy`, `qsag-cred`, `qsag-migrate` | Wallet, capability, credential, and 19-kind migration crates |
| `qsag-cli` | CLI (`qsag`, synced bijectively to `dregg-sig`) and runnable examples |
| `lean/`, `aeneas/`, `validation/` | Protocol proofs, MIR extractions, six-kernel replay and differential validation |

[Cut-the-Hash](paper/cut-the-hash.typ) · [Quintic Hem](paper/quintic-hem.typ) · [Assurance boundaries](ASSURANCE.md) · [Security and constant-time proofs](docs/SECURITY_AND_CT_PROOFS.md)

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
