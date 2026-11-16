<p align="center">
  <img src="assets/qsag-mascot.png" alt="qsag mascot" width="200" />
</p>

<h1 align="center">qsag</h1>

`qsag` is a post-quantum replacement for the signing layer that wallets, custodians, and validators build on elliptic curves today. It is written in Rust, with its security arguments checked in Lean 4.

| On elliptic curves you use | `qsag` gives you |
| --- | --- |
| FROST or MPC-ECDSA, to split a signing key among $t$-of-$n$ custodians | Threshold signing for hash-based signatures and ML-DSA. The key is generated jointly and never exists in one place. |
| BLS, to compress many validator signatures into one | A single hash-based proof that $K$ signatures verify, built by anyone from the public signatures, with no interaction between signers. |
| BIP-32, to derive child keys and watch-only wallets | Key hierarchies derived jointly by the custodians, with watch-only derivation of child public keys. |
| Nothing (you just move the funds) | A zero-knowledge proof that you own an existing secp256k1, Ed25519, Pallas, or BLS12-381 key, bound to a new post-quantum address, without revealing the old key to anyone. |

It is a signing library, not a consensus engine: it produces and checks signatures and leaves ordering, networking, and fork choice to you.

The name stands for *quorum switching* (changing which custodians sign, and how many, without changing the public key) and *succinct aggregation*.

**Status: research prototype.** It has had no external audit. The proofs described below cover specific models and specific compiled routines, not the whole running system; [ASSURANCE.md](ASSURANCE.md) says exactly where each one stops.

## The ideas

### Threshold signing for hash-based signatures

A hash-based signature such as SLH-DSA (FIPS 205) is a large tree of hashes grown from a secret seed. To sign with a shared key, the obvious approach is to evaluate that whole tree inside a multi-party computation, which costs millions of secret gates per signature.

Most of that work is unnecessary. Almost every hash in the tree is applied to values that the signature publishes anyway. `qsag` keeps only four operations secret (the message randomizer, the one-time-signature chain values, and the two kinds of few-time-signature leaves), has the custodians check each other's work, opens those values, and computes the rest of the tree in the clear. The secret computation is then a few hashes deep no matter how tall the tree is.

This is enough to threshold-sign **standard SLH-DSA**: the output is byte-for-byte what a single signer with the same key and randomness would produce, and any FIPS 205 verifier accepts it. A separate protocol in `qsag-cred` threshold-signs **ML-DSA-44/65/87** (FIPS 204), again for unmodified verifiers.

Standard SLH-DSA was not designed with this in mind, so `qsag` also defines its own signature formats that are cheaper to sign jointly. They use shorter hash chains (4 steps instead of 16) and replace the usual checksum with a rule that the message digits must add up to a fixed total. These formats need their own verifier.

- **Baggy** is stateless, like SLH-DSA: there is no counter to keep and nothing to lose in a crash. The upper layers of its tree sign values that never change, so they are computed once and cached. It signs roughly 8–15× faster than threshold SLH-DSA on the same engine.
- **Jorts** is stateful, like XMSS: a single Merkle tree of one-time keys, each of which may sign exactly once. Signatures are small (4,328 bytes) and the expensive work can be done before the message arrives, leaving one round of opening shares. The price is that the signers must never use a leaf twice.

### Never signing twice with the same leaf

If a one-time key signs two different messages, an attacker can forge. With one signer this is a matter of keeping a counter. With $n$ custodians, any $t$ of whom may sign, it is harder: two different groups of $t$ can each believe that leaf 17 is unused, especially after a crash, a restored backup, or a network partition.

`qsag` handles this in three layers.

1. **Write before you sign.** Each custodian records the leaf and the message in a write-ahead log, and flushes it to disk, before releasing anything derived from the secret. A crash can waste a leaf but cannot reuse one. This mechanism is called *BeltLatch*.
2. **Give each group its own leaves.** In the first quorum mode (*QS-A*), every possible group of $t$ custodians owns a disjoint range of leaves, so two groups cannot collide. Any $t$ custodians who are online can sign in one round. The cost is that the leaves are divided among $\binom{n}{t}$ groups, and the leaf index reveals which group signed.
3. **Or agree on each leaf.** In the second mode (*QS-B*), all custodians share one tree. Before anyone releases a share for a leaf, $q$ custodians must have logged the same message for it, where $2q > n + f$ and $f$ is the number of custodians who may be malicious. Any two such sets of $q$ overlap in an honest custodian, who will not log two messages for one leaf. Staying live with $f$ custodians offline then needs $n \ge 3f + 1$.

The committee can also change. Shares can be refreshed in place, or reshared from $(t, n)$ to $(t', n')$, without ever reconstructing the key and without changing the public key.

### Signatures that fit in one packet

Validators that vote every slot want a signature that fits in one UDP datagram. The few-time signatures in `qsag-fts` trade signing lifetime for size. The main profile, **Compact1122**, is 1,122 bytes with full 256-bit hash values; with a 96-byte vote header it fits in the 1,232 bytes that a QUIC packet can carry without fragmentation. Each key signs once, and the signer records that on disk first, as above.

### Aggregation without pairings

BLS aggregation relies on pairings, which a quantum computer breaks. The post-quantum substitute is a proof: *"I have seen $K$ valid signatures on this message from these public keys."* **Hem** (`qsag-agg`) produces such a proof. It needs only the public signatures, so anyone can run it, and proofs over disjoint sets of signers can be merged.

To make verification cheap to prove, the signatures being aggregated use Poseidon2, a hash designed for arithmetic circuits, in place of Keccak. Hem lays out the $K$ verifications as a table over the 64-bit Goldilocks field, checks the table's constraints with a sumcheck, and commits to it with WHIR, a hash-based polynomial commitment. No trusted setup is involved, and the only cryptographic assumption is on the hash functions.

One parameter choice deserves a sentence. Proof systems of this family choose how many positions of a Reed–Solomon codeword to sample, and many deployed systems choose that number by conjecturing that sampling behaves well all the way up to the code's capacity. Those conjectures were disproved in 2025–26. Hem sets its sample counts from the proven Guruswami–Sudan (Johnson) list-decoding bound instead. The default profile sizes them so that a Grover search over one round of challenges costs at least $2^{128}$ work with no limit on the number of hash queries; four smaller profiles are also accepted, and those are 128-bit secure only for an adversary limited to $2^{38}$ or $2^{40}$ hash queries ([details](docs/SECURITY_AND_CT_PROOFS.md#hem-profile-and-qrom-accounting)). Proofs are a few hundred kilobytes as a result, and soundness does not depend on an open conjecture about codes.

The prover runs on CPUs (AVX2, AVX-512, NEON) and on GPUs through Vulkan compute shaders. Both produce identical proofs.

### Wallet plumbing

- **`qsag-hd`**: hash-based keys have no algebraic structure, so BIP-32's trick of deriving child public keys from a parent public key does not carry over. `qsag-hd` offers two substitutes: a committed inventory of child keys that the custodians derive jointly, and, for lattice keys, linear derivation in which a watch-only party can compute child public keys alone.
- **`qsag-policy`**: spending rules (allowlists, per-transaction and rolling limits, approval tiers) evaluated on the shared state before any custodian releases a signature share.
- **`qsag-addr`**: Bech32m addresses, and hybrid keys that pair a classical key with a post-quantum one.
- **`qsag-migrate`**: three custodians, none of whom learns the old key, jointly prove knowledge of the classical secret key behind an existing address. This works even when the chain has only ever seen a hash of the public key.
- **`qsag-cred`**: threshold ML-DSA, a threshold oblivious PRF, and blind credentials with selective disclosure.

## Committee sizes

Threshold signing is built for general $(t, n)$, but not every path is equally fast at every size.

| Path | Committees | Tolerates | Notes |
| --- | --- | --- | --- |
| SLH-DSA, Baggy, and Jorts on the three-party engine | 2-of-3 | 1 malicious custodian (signing may abort) | The fast path for whole-signature signing. Uses replicated secret sharing, whose storage grows as $\binom{n}{t-1}$, so it stays at three parties. |
| Jorts with quorum switching, QS-A | any $(t, n)$ | $t - 1$ malicious | One round online. Tree capacity is divided among $\binom{n}{t}$ groups, so it suits small and medium committees. |
| Jorts with quorum switching, QS-B | any $(t, n)$ up to 255 custodians | $f$ malicious, with $n \ge 3f + 1$ | Shamir shares of a fixed size per custodian, whatever $n$ is. |
| Threshold ML-DSA | $n \le 64$, $n \ge 2t - 1$ | $t - 1$ malicious | A quorum of $2t - 1 \le 16$ custodians signs together (so $t \le 8$): Shamir shares with an honest majority inside the quorum, and checked multiplications and share conversions. |
| General engine (SPDZ-style authenticated shares) | any $(t, n)$ | up to $n - 1$ malicious (signing may abort) | Slow today: generating its correlated randomness dominates, and signing a whole stateless tree this way takes minutes. |

## Performance

All figures are measured, at the sizes stated. Hardware and method are in §7 of the [paper](paper/qsag.typ).

**Signing**

| Operation | Measured |
| --- | --- |
| Jorts, 2-of-3, prepared ahead, in memory | about 1.0 ms (81 ms over a simulated WAN) |
| QS-A, 3-of-5, loopback TCP, no disk | 0.56 ms |
| QS-A, 2-of-3, encrypted channels, log flushed to disk | 4.37 ms |
| QS-B, 3-of-7 with $q = 5$, encrypted channels, log flushed to disk | 5.21 ms |

**Verifying single-packet votes** (Compact1122, 1,200 votes)

| Setup | Time |
| --- | --- |
| One core, SIMD batch | 1.23 s (about 1 ms per vote) |
| Eight threads | 158–187 ms |

**Aggregation** (Hem over Jorts signatures, post-quantum parameters)

| Batch | Prove | Verify | Proof |
| --- | --- | --- | --- |
| 32 signers, Radeon RX 6750 XT | 322 ms | 5.75 ms | — |
| 128 signers, Radeon RX 6750 XT | 1.13–1.34 s | 3.4 ms | 435 KiB |
| 128 signers, 24 CPU threads | 4.9–8.8 s | 3.4 ms | 435 KiB |
| 1,200 signers, one joint proof, CPU | — | 14.4 ms | 1.93 MiB |

A single proof shard covers up to 128 Jorts signers, and several shards can be proved jointly (the 1,200-signer row). Larger sets are handled by merging proofs, which today means concatenating them: 2,048 validators come to 6.8 MiB and verify in 16–43 ms, and size keeps growing linearly from there. Constant-size recursion is not implemented: a proof that verifies the WHIR openings of up to 16 child shards inside one parent circuit exists (over the Poseidon2 commitment profile), but it certifies those openings rather than the shards' signatures, so the child proofs are still needed for authorization. For comparison, 128 raw Jorts signatures are 541 KiB and 1,200 are 4.95 MiB.

**Primitives** (one Zen 5 core, AVX-512): Keccak at 3.15 GB/s; a Merkle node hash in 111 ns, eight at a time.

## Verification

The project uses formal proof as a design tool. A construction is modelled in Lean, and the attempt to prove it secure is what finds the missing check. There are four layers, each covering something the others cannot.

1. **Protocol proofs** ([`lean/Qsag/`](lean/Qsag)). About 200 Lean 4 modules cover the signature schemes, the threshold protocols, crash recovery of the write-ahead log under a model of POSIX and disk behaviour, the quorum-overlap argument, and the coding-theory bounds behind Hem. The library is constructive: there is no `sorry` and no use of `Classical.choice`, so a security reduction is a function that computes the forgery or collision it promises. Most guards also come with a counterexample, a theorem showing the concrete attack that appears when the guard is removed.
2. **Proofs about the Rust itself** ([`aeneas/`](aeneas)). The safety-critical checks in the Rust code (field arithmetic, the sponge, and the guards that decide whether a share may be released) live in two small crates. Charon and Aeneas translate their compiled MIR into Lean, where they are proved to match the specification. The production crates call these exact functions.
3. **Constant-time proofs about machine code.** The 28 hand-written assembly routines (19 for x86-64, 9 for AArch64) are decoded from the compiled object files, and Lean proves that their branches, memory addresses, and variable-time instructions do not depend on secrets. For 26 of them it also proves that they compute the right function. A separate screen checks every compiled cryptographic symbol for secret-dependent branches, and `dudect` timing tests run on real CPUs. The GPU shaders have a corresponding SPIR-V model, which is not yet connected to the exact shader binaries.
4. **Differential testing** ([`validation/`](validation)). The Lean specifications are executable, so they are run against the Rust byte for byte. Both are also run against 17 independent crates (`fips205`, `fips204`, `sha3`, `k256`, `curve25519-dalek`, `blstrs`, Plonky3's Goldilocks, and others), and the assembly is single-stepped against a real Zen 5 CPU.

What this does not establish: that the whole linked program refines the models, or a complete security reduction for the aggregation proof against quantum adversaries. [ASSURANCE.md](ASSURANCE.md) lists the open obligations and the trusted base.

## Quickstart

You need a Rust toolchain; `rust-toolchain.toml` pins the version. The workspace has no dependencies from crates.io.

```bash
# Run the built-in known-answer tests, then list the supported schemes and their sizes.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign   --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"
```

The CLI also drives threshold custody (`quorum keygen`, `sign`, `refresh`, `reshare`), aggregation (`aggregate`, `verify-aggregate`), addresses, HD derivation, migration, and policy. Every command accepts `--help`.

Worked examples:

```bash
cargo run --release -p qsag-cli --example slh_dsa_quickstart
cargo run --release -p qsag-cli --example few_time_signatures
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example pq_address_and_policy
cargo run --release -p qsag-cli --example dealerless_dkg_consistency_check
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart

# Vote-size and aggregation harnesses shaped like Solana Alpenglow and Ethereum Beam.
cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam
```

`threshold_slh_dsa_quickstart` produces and verifies its 2-of-3 signature, then moves on to the general engine, whose preprocessing did not finish within ten minutes when we last timed it.

To check the proofs and run the differential tests:

```bash
(cd lean && lake build)                      # long, and memory-hungry
./scripts/run_differential_validation.sh
```

## Crates

The libraries are `no_std` with `alloc`. Only the CLI, the file-backed logs, and the socket transports need `std`.

| Crate | Contents |
| --- | --- |
| `qsag-core` | Threshold SLH-DSA, Baggy, Jorts, the write-ahead latch, both MPC engines, joint key generation and resharing |
| `qsag-quorum` | $(t, n)$ quorum switching (QS-A, QS-B), per-custodian protocol nodes, encrypted transport |
| `qsag-fts` | Few-time signatures, including Compact1122, and SIMD batch verification |
| `qsag-agg` | Hem: aggregation prover and verifier, proof merging |
| `qsag-accel` | Prover backends: a portable CPU reference and Vulkan compute shaders |
| `qsag-asm` | Assembly routines for x86-64 (AVX2, AVX-512) and AArch64 (NEON): Keccak, binary-field and Goldilocks arithmetic, the ML-DSA transform |
| `qsag-hd` | Jointly derived key hierarchies and watch-only derivation |
| `qsag-policy` | Spending policy checked before shares are released |
| `qsag-addr` | Bech32m addresses and hybrid classical/post-quantum keys |
| `qsag-cred` | Threshold ML-DSA, threshold oblivious PRF, blind credentials |
| `qsag-migrate` | Zero-knowledge proof of ownership for secp256k1, Ed25519, Pallas, and BLS12-381 keys |
| `qsag-cli` | The `qsag` command-line tool and the examples |

## Further reading

- [paper/qsag.typ](paper/qsag.typ): the constructions, parameters, and measurements in full.
- [ASSURANCE.md](ASSURANCE.md): threat models, what each proof covers, and the trusted base.
- [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md): how aggregation scales to large validator sets.
- [docs/PROOF_ARCHITECTURE.md](docs/PROOF_ARCHITECTURE.md): how the Lean library is organised and where to start reading it.
- [docs/SECURITY_AND_CT_PROOFS.md](docs/SECURITY_AND_CT_PROOFS.md): parameters, the theorems behind them, and the open proof obligations.

## License

Licensed under either of [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
