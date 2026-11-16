<p align="center">
  <img src="assets/qsag-mascot.png" alt="qsag mascot" width="200" />
</p>

<h1 align="center">qsag</h1>

`qsag` is a post-quantum replacement for the signing layer that wallets, custodians and validators build on elliptic curves. It is written in Rust, and its security arguments are checked in Lean 4.

| On elliptic curves you use | `qsag` gives you |
| --- | --- |
| FROST or MPC-ECDSA, to split a key among custodians | Threshold signing for hash-based signatures and ML-DSA. The key is generated jointly and never exists in one place. |
| BLS, to compress many validator signatures | One hash-based proof that $K$ signatures verify, the same size for a hundred signers or a million. |
| BIP-32, to derive child keys | Hierarchies derived jointly by the custodians, with watch-only inventories. |
| Macaroons or biscuits, to delegate narrowed authority | The same three shapes without curves: a MAC chain, a one-time-signature chain, and a zero-knowledge presentation. |
| Nothing (you move the funds) | A zero-knowledge proof that you own a secp256k1, Ed25519, Pallas or BLS12-381 key, bound to a new address, without revealing the old key. |

It is a signing library, not a consensus engine. The name stands for *quorum switching* (changing which custodians sign without changing the public key) and *succinct aggregation*.

**Status: research prototype, no external audit.** [ASSURANCE.md](ASSURANCE.md) says where each proof stops.

## The ideas

### Cut the hash

A hash-based signature such as SLH-DSA (FIPS 205) is a large tree of hashes grown from a secret seed. Signing with a shared key would seem to require evaluating that tree inside a multi-party computation.

Almost every hash in the tree is applied to values the signature publishes anyway. `qsag` keeps four operations secret (the message randomizer, one-time chain values, and two kinds of few-time leaves), has the custodians check each other, opens those values, and computes the rest in the clear. The secret computation is at most 16 hashes deep for SLH-DSA and 4 for `qsag`'s own formats, whatever the height of the tree.

The output for **standard SLH-DSA** is byte for byte what a single signer with the same key and randomness would produce. A separate protocol threshold-signs **ML-DSA-44/65/87** (FIPS 204) for unmodified verifiers.

`qsag` also defines formats that are cheaper to sign jointly: chains of 4 steps instead of 16, and a fixed digit sum in place of a checksum.

- **Baggy** is stateless. Its upper layers sign values that never change, so they are computed once and cached. Its bottom layer is one pruned tree of 2,048 leaves (PORS+FP) that reveals 28 per signature under one Merkle proof of at most 128 nodes; the signature is at most 71,654 bytes. For general $(t, n)$, the signing quorum converts its shares locally into a $t$-of-$t$ sharing and signs as a fixed committee.
- **Jorts** is stateful: one Merkle tree of one-time keys, from $2^6$ to $2^{20}$ of them. Signatures are 4,328 to 4,776 bytes, and the expensive work is done before the message arrives, leaving one round.
- **Compact1122** is a single-use signature of 1,122 bytes. With a 96-byte vote header it fills 1,218 of the 1,232 bytes of a minimum-MTU datagram.

### Never sign twice with one leaf

If a one-time key signs two messages, anyone can forge. With $n$ custodians, any authorized set of whom may sign, two sets can each believe a leaf is unused, especially after a crash, a restored backup or a partition. `qsag` handles this in layers.

1. **Write before you sign** (*BeltLatch*). Each custodian logs the leaf and message, and syncs, before releasing anything derived from the secret. A crash can waste a leaf and cannot reuse one. The log's two high-water marks sit on separate 4,096-byte pages, so one torn sector cannot damage both.
2. **Anchor the log outside the disk.** A log cannot tell that its whole disk or VM was restored from a snapshot, so each stateful object consumes single-use tickets from an external monotone counter. Three are implemented and compose: a TPM 2.0 NV counter (through `/dev/tpmrm0`), the hypervisor's VM generation ID, and a mirrored directory on a second device. The CLI refuses stateful custody without an anchor unless you declare the key ephemeral.
3. **Give each group its own leaves** (*QS-A*), so that groups cannot collide; or
4. **Agree on each leaf** (*QS-B*): before releasing a share, a custodian requires a certificate that a quorum has logged the same message for that leaf.

The safety condition for (4) is that any two quorums able to certify a leaf share a custodian outside every tolerated fault set. The familiar $2q > n + f$ is the symmetric case. `qsag-quorum` also accepts weighted quorums, threshold trees (two chambers that must both approve, say), and asymmetric systems in which each participant names its own quorums, and checks the intersection condition on the sets you give it. The key is shared by a monotone span program with 0/1 entries; every authorized set collapses its shares to an additive sharing by a public linear map, so the signing protocol does not change with the access structure.

When prevention fails (a single-holder key, or more corruption than assumed), misuse is provable: two signatures at one leaf on different messages are self-contained evidence, checkable from the public key alone.

### Aggregation without pairings

**Hem** (`qsag-agg`) proves *"these $K$ public keys signed this message."* It needs only the public signatures, so anyone can run it. The signatures it aggregates use Poseidon2 in place of Keccak; Hem lays their verification out as a table over the 64-bit Goldilocks field, checks it with a sumcheck, and commits to it with WHIR. There is no trusted setup and the only assumption is on the hash functions.

Proof systems of this family choose how many positions of a Reed–Solomon codeword to sample, and many deployed systems choose by conjecturing good behaviour up to the code's capacity. Those conjectures were disproved in 2025–26. Hem sets its counts from the proven Johnson bound. The default profile gives $2^{128}$ Grover work per round with no limit on hash queries; smaller profiles are accepted only by name and are 128-bit secure for an adversary limited to $2^{38}$ or $2^{40}$ queries ([details](docs/SECURITY_AND_CT_PROOFS.md)).

A shard proof covers 128 signers in 435 KiB. To go further Hem verifies proofs inside proofs. A *merge* checks up to 16 child proofs; because the merge's own constraint system is committed to (a *hologram*), verifying a merge takes 11.5 ms whatever its size, and a merge can be the child of another merge. Every merge exposes the same 14-word statement: roster root, epoch, message, the range of key indices beneath it, and the signer count and weight. Children must have increasing index ranges, so no signer is counted twice at any depth and no bitmap is needed.

The result is one proof of 312–340 KiB for any number of signers, checked against a 32-byte roster root. Signers may be a dense validator set or a few hundred keys scattered through a directory of $2^{37}$.

The same prover has a zero-knowledge mode, used for credential presentations, a multisignature that hides who signed and the threshold, and capabilities.

### Capabilities

| Form | Size | Verifier holds | Delegate offline | Hides the token |
| --- | --- | --- | --- | --- |
| `SpongeMacaroon` (MAC chain, third-party discharges) | 161 B with 3 caveats | the secret key | yes | no |
| `PqBiscuit` (chain of one-time signatures) | 1,154 B per hop | a public key | yes | no |
| zk capability (batched, with non-revocation) | 233 KiB per batch | two Merkle roots | in delegated mode | yes |

All three share one caveat language, and the policy engine evaluates them before any custodian releases a share.

### Wallet plumbing

- **`qsag-hd`**: jointly derived hierarchies, committed watch-only inventories, and for 2-of-3 custody a child share computed by each custodian from what it already holds.
- **`qsag-policy`**: spending rules evaluated on shared state; a successful check mints one release token per quorum member, each usable only by that member.
- **`qsag-addr`**: Bech32m addresses and hybrid classical/post-quantum keys.
- **`qsag-migrate`**: three custodians, none of whom learns the old key, prove knowledge of the secret behind an existing address. It works when the chain has only seen a hash of the public key.
- **`qsag-cred`**: threshold ML-DSA, a threshold oblivious PRF, and blind credentials with selective disclosure.

## Committee sizes

| Path | Committees | Tolerates | Notes |
| --- | --- | --- | --- |
| SLH-DSA, Baggy, Jorts on the three-party engine | 2-of-3 | 1 malicious (may abort) | The fast path. |
| Stateless signing, general $(t, n)$ | any | $t - 1$ malicious | The quorum converts to $t$-of-$t$ locally. |
| Jorts, QS-A | any $(t, n)$ | $t - 1$ malicious | One round. Capacity is divided among $\binom{n}{t}$ groups. |
| Jorts, QS-B | up to 255 custodians; symmetric, weighted, tree or asymmetric quorums | any fault set the quorum system admits | Fixed-size shares. The symmetric case needs $n \ge 3f + 1$ to stay live. |
| Threshold ML-DSA | $n \le 64$, $n \ge 2t - 1$ | $t - 1$ malicious | A quorum of $2t - 1 \le 16$ signs. |
| Threshold oblivious PRF | 2-of-5 with error correction, or $2 \le t \le n \le 64$ | 1 malicious server; $t - 1$ on the general engine (may abort) | |
| General engine (authenticated shares) | any $(t, n)$ | up to $n - 1$ malicious (may abort) | Preprocessing dominates; signing a whole stateless tree this way takes minutes. |

In the general engine every custodian holds a share of a long-lived authentication key. The standard check of an opened value reveals a multiple of that key when it fails, which is fatal if the key is kept. `qsag` multiplies the check value by a jointly random secret before opening it, so a failed check reveals a uniformly random nonzero field element and nothing about the key ([details](docs/SECURITY_AND_CT_PROOFS.md#blinded-mac-checks)).

## Performance

Measured on the hardware named in §7 of the [paper](paper/qsag.pdf), with all parties of a multi-party protocol in one process.

**Signing**

| Operation | Measured |
| --- | --- |
| Jorts, 2-of-3, prepared ahead, in memory | 1.0 ms (81 ms over a simulated WAN) |
| QS-A, 2-of-3, encrypted channels, log synced | 4.37 ms |
| QS-B, 3-of-7 with $q = 5$, encrypted channels, log synced | 5.21 ms |
| Baggy or SLH-DSA, 2-of-3, one wave of 256 hashes with its check | 54 ms |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| Oblivious PRF, 2-of-3, one evaluation after preprocessing | 4.3 ms |
| `SpongeMacaroon`, verify | 1.8 µs |

**Aggregation** (Hem over Jorts signatures, default profile)

| Statement | Prove | Verify | Proof |
| --- | --- | --- | --- |
| 128 signers, Radeon RX 6750 XT | 1.33–1.56 s | 3.0 ms | 445,566 B |
| 128 signers, CPU | 2.94–3.67 s | 3.0 ms (6.2 ms on one core) | 445,566 B |
| 512 signers, one shard, CPU | 11.1 s | 3.6 ms | 556,830 B |
| Merge root, any number of signers | see below | 11.5 ms on one core | 312–340 KiB |
| Credential presentation, 32 attributes (zero-knowledge) | 0.28 s | 19.6 ms on one core | 239,507 B |
| Private multisignature, 16 slots (zero-knowledge) | 3.48 s | 53 ms | 700,491 B |

CPU and GPU provers emit identical bytes. The GPU prover (Vulkan; ten compute shaders) commits witnesses for 256 and 512 signers entirely in 12 GiB of VRAM, and builds a $2^{20}$-leaf Poseidon2 Merkle tree in 82 ms, 58 times one CPU thread.

**Scaling.** Merge trees are modelled, not timed end to end: the model takes the measured shard and commit times, a merge time proportional to the merge relation's size, and one prover per tree node with every stage on a GPU.

| Validators | Raw signatures | Tree | Critical path (model) | Certificate | Verify |
| --- | --- | --- | --- | --- | --- |
| 1,500 | 6.8 MiB | 12 shards, 2 levels | 2.4 s | 321 KiB | 11.5 ms |
| 16,384 | 74.6 MiB | 128 shards, 4 levels | 3.1 s | 321 KiB | 11.5 ms |
| 100,000 | 455 MiB | 782 shards, 5 levels | 3.5 s | 321 KiB | 11.5 ms |
| 1,048,576 | 4.66 GiB | 8,192 shards, 7 levels | 4.3 s | 321 KiB | 11.5 ms |
| 1,048,576, fewest network hops | 4.66 GiB | 2,048 shards of 512, 3 levels | 9.5 s | 331 KiB | 11.5 ms |

[docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md) has the model, its inputs, and which numbers are measured. It also sizes two further directions: a directory of $88 \times 10^9$ principals, and a hardware verifier. Verification uses five primitives on 64-bit words and no big-integer arithmetic, which fits a logic budget of 954 thousand gates (0.08–0.19 mm² at 3–5 nm). That figure is a budget; nothing has been synthesized.

**Primitives** (one Zen 5 core, AVX-512): Keccak at 3.15 GB/s; a Merkle node hash in 111 ns, eight at a time.

## Verification

The project uses formal proof as a design tool: a construction is modelled in Lean, and the attempt to prove it secure is what finds the missing check. There are four layers.

1. **Protocol proofs** ([`lean/Qsag/`](lean/Qsag)). The library (232 modules, 105,421 declarations and 53,482 theorems at its last full audit) covers the signature schemes, threshold protocols, crash recovery under a model of POSIX and disk behaviour, quorum intersection, and the coding theory behind Hem. It is constructive: no `sorry`, no `Classical.choice`, and no `import all`, so a security reduction is a function that computes the collision or forgery it promises, and no proof depends on another module's private definitions. Most guards come with a counterexample theorem showing the attack that appears when the guard is removed. [`lean/Qsag/Spec/`](lean/Qsag/Spec) states as ideal machines what signing, custody, migration, credentials and aggregation guarantee, with hardness assumptions stated for adversaries bounded in their number of oracle queries.
2. **Proofs about the Rust** ([`aeneas/`](aeneas)). Field arithmetic, the sponge, the guards that decide whether a share may be released, and the arithmetic core of the WHIR verifier live in two small crates. Charon and Aeneas translate their MIR into Lean, where they are proved against the specification. The production crates call these exact functions.
3. **Proofs about machine code.** The 28 assembly routines (19 for x86-64, 9 for AArch64) are decoded from the compiled archive. Lean proves that their branches, addresses and variable-time operands do not depend on secrets, and for 26 of them that they compute the right function. A separate screen checks every compiled cryptographic symbol of the release archives.
4. **Differential testing** ([`validation/`](validation)). The Lean specifications are executable and run against the Rust byte for byte; both run against 17 independent crates; the assembly is single-stepped against a Zen 5 CPU.

What this does not establish: that the whole linked program refines the models; an end-to-end extractor theorem for the deployed Hem verifier (its per-round bounds are proved, their composition is not); or a full simulator for the zero-knowledge mode. [ASSURANCE.md](ASSURANCE.md) lists the open obligations and the trusted base.

## Quickstart

You need a Rust toolchain; `rust-toolchain.toml` pins the version. The workspace has no dependencies from crates.io.

```bash
# Known-answer tests, then the supported schemes and their sizes.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign   --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"
```

The CLI also drives threshold custody (`quorum keygen`, `sign`, `refresh`, `reshare`), aggregation, addresses, HD derivation, migration, credentials, and policy (`policy macaroon`, `policy biscuit`). Every command accepts `--help`.

Stateful schemes need an anchor. Pass `--anchor-dir <dir>` (ideally on another device), `--anchor-tpm-nv <index>`, or `--anchor-vmgenid`, alone or together; or `--ephemeral-unanchored` for a throwaway key.

Worked examples:

```bash
cargo run --release -p qsag-cli --example slh_dsa_quickstart
cargo run --release -p qsag-cli --example few_time_signatures
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example pq_address_and_policy
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart

# Vote-size and aggregation harnesses shaped like Solana Alpenglow and Ethereum Beam.
cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam
```

To check the proofs, run the differential tests, and reproduce the scaling model:

```bash
(cd lean && lake build)                      # long, and memory-hungry
./scripts/run_differential_validation.sh
python3 scripts/quorum_and_consensus_scaling.py --self-test
```

## Crates

The libraries are `no_std` with `alloc`. Only the CLI, the file-backed logs, and the socket transports need `std`.

| Crate | Contents |
| --- | --- |
| `qsag-core` | Threshold SLH-DSA, Baggy, Jorts, the write-ahead latch, anchors, both MPC engines, key generation and resharing, access structures |
| `qsag-quorum` | Quorum switching (QS-A, QS-B), general quorum systems, per-custodian protocol nodes, encrypted transport |
| `qsag-fts` | Few-time signatures, SIMD batch verification, the dealerless threshold key ceremony and its reservoir |
| `qsag-agg` | Hem: prover and verifier, subtree recursion, and the zero-knowledge relations |
| `qsag-accel` | Prover backends: a portable CPU reference and Vulkan compute shaders (Linux; macOS through MoltenVK) |
| `qsag-asm` | Assembly for x86-64 (AVX2, AVX-512) and AArch64 (NEON): Keccak, binary-field and Goldilocks arithmetic, the ML-DSA transform |
| `qsag-hd` | Jointly derived key hierarchies and watch-only derivation |
| `qsag-policy` | Spending policy, macaroons and biscuits |
| `qsag-addr` | Bech32m addresses and hybrid keys |
| `qsag-cred` | Threshold ML-DSA, threshold oblivious PRF, blind credentials |
| `qsag-migrate` | Zero-knowledge proof of ownership for secp256k1, Ed25519, Pallas and BLS12-381 keys |
| `qsag-cli` | The `qsag` command-line tool and the examples |

## Further reading

- [paper/qsag.pdf](paper/qsag.pdf) ([source](paper/qsag.typ)): the constructions, theorems and measurements.
- [ASSURANCE.md](ASSURANCE.md): threat models, what each proof covers, and the trusted base.
- [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md): the scaling model.
- [docs/PROOF_ARCHITECTURE.md](docs/PROOF_ARCHITECTURE.md): how the Lean library is organised.
- [docs/SECURITY_AND_CT_PROOFS.md](docs/SECURITY_AND_CT_PROOFS.md): parameters, the theorems behind them, and open obligations.

## License

Licensed under either of [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
