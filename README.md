<p align="center">
  <img src="assets/qsag-mascot.png" alt="qsag mascot" width="200" />
</p>

<h1 align="center">qsag</h1>

`qsag` is a post-quantum replacement for the signing layer that wallets, custodians and validators build on elliptic curves. It is written in Rust, verified at the protocol, MIR and assembly layers in Lean 4, and accompanied by synthesizable RTL for a hardware verifier and a 180 nm custody enclave.

| On elliptic curves you use | `qsag` gives you |
| --- | --- |
| FROST or MPC-ECDSA, to split a key among custodians | Threshold signing for hash-based signatures and ML-DSA. The key is generated jointly and never exists in one place. |
| BLS, to compress many validator signatures | One hash-based proof that $K$ signatures verify, constant-scale from a hundred signers to a million. |
| BIP-32, to derive child keys | Module-lattice hierarchies derived jointly by the custodians, with committed watch-only inventories. |
| Macaroons or biscuits, to delegate narrowed authority | Three curve-free capability forms: a sponge MAC chain, a one-time-signature chain, and a zero-knowledge presentation. |
| Nothing (you move the funds) | Local or threshold zero-knowledge proofs (`CoZK`) that you own a `secp256k1`, `Ed25519`, `Pallas` or `BLS12-381` key, bound to a post-quantum address without revealing the old secret. |

It is a signing library, not a consensus engine. The name stands for *quorum switching* (changing which custodians sign without changing the public key) and *succinct aggregation*.

**Status: research prototype, no external audit.** [ASSURANCE.md](ASSURANCE.md) says where each proof stops.

## The ideas

### Cut the hash

A hash-based signature such as SLH-DSA (FIPS 205) is a large tree of hashes grown from a secret seed. Signing with a shared key would seem to require evaluating that entire tree inside a multi-party computation.

Cut-the-Hash observes that almost every hash in the tree is applied to values the signature publishes anyway. `qsag` keeps four operations secret (the message randomizer, one-time chain values, and two kinds of few-time leaves), has the custodians check each other, opens those boundary digests, and computes the public Merkle layers in the clear. The secret computation is at most 16 hashes deep for SLH-DSA and 4 for `qsag`'s native formats, whatever the height of the tree.

The output for **standard SLH-DSA** is byte for byte what a single signer with the same key and randomness would produce. Both the bitsliced 3-party engine (`crates/qsag-core/src/rss256.rs`) and the isolated per-custodian CNF engine (`crates/qsag-quorum/src/cnf_party.rs`, Chida et al. CRYPTO 2018 over $\mathrm{GF}(2^{128})$) sign standard SLH-DSA over authenticated wire channels for `2-of-3`, `3-of-5`, and general honest-majority $2(t-1) < n$ committees without reconstructing secret shares. A separate protocol threshold-signs **ML-DSA-44/65/87** (FIPS 204) for unmodified verifiers.

`qsag` also defines hash-based formats that are cheaper to sign jointly—chains of 4 steps instead of 16, and a fixed digit sum (`WOTS+C`) in place of an explicit checksum:

- **Baggy** is stateless. Its upper layers sign public roots that never change, so they are computed once and cached. Its bottom layer is one pruned tree of 2,048 leaves (`PORS+FP`) that reveals 28 leaves per signature under a canonical multiproof of at most 128 nodes; the signature is at most 71,654 bytes. Committees with $2(t-1) < n$ sign directly through `IsolatedCnfParty` over `WireTransport`, or convert locally into an additive sharing for general $(t, n)$.
- **Jorts** is stateful: one Merkle tree of one-time keys, from $2^6$ to $2^{20}$ leaves (`Jorts` over SHAKE256, `JortsPoseidon2` for aggregation). Signatures are 4,328 to 4,776 bytes, and chain evaluation runs offline before the message arrives, leaving one online round.
- **Compact1122** (`qsag-fts`) is a single-use signature of 1,122 bytes (`w = 96`, `L = 34`, 32-byte digests) with parallel-seeded non-interactive share generation. With a 96-byte vote header it fills 1,218 of the 1,232 bytes of a minimum-MTU IPv6 UDP datagram.

### Never sign twice with one leaf

If a one-time key signs two messages, anyone can forge. With $n$ custodians, any authorized quorum of whom may sign, two quorums can each believe a leaf is unused—especially after a crash, a restored snapshot, or a partition. `qsag` prevents reuse in four layers:

1. **Write before you sign** (*BeltLatch*). Each custodian logs `(leaf, intent)` and `fsync`s before releasing anything derived from its share. A crash can burn a leaf and cannot reuse one. The log's two high-water marks sit on separate 4,096-byte pages (`4096` and `8192`), so a single sector tear cannot corrupt both.
2. **Anchor the log outside the disk.** A filesystem journal cannot detect whole-disk or VM snapshot rollback, so stateful vaults consume single-use tickets from external monotone hardware or hypervisor anchors (`crates/qsag-core/src/anti_rollback.rs`): a hardware TPM 2.0 NV counter accessed directly over `/dev/tpmrm0` (`Tpm2NvMonotoneAnchor`), the hypervisor's `VMGENID` paired with Linux `boot_id` and inode identity (`VmGenIdForkGuard`), and a `LockedRecord` directory on a disjoint device (`FsExternalMountAnchor`). Stateful CLI subcommands refuse to run without an anchor unless `--ephemeral-unanchored` is explicitly passed.
3. **Give each group its own leaves** (*QS-A*), partitioning tree capacity across committees so disjoint quorums never collide; or
4. **Agree on each leaf** (*QS-B*): before releasing a share, each custodian requires a certificate that a quorum has logged the same `(leaf, message)` pair, or binds the leaf monotonically to a local blocklace sequence (`BlocklaceLeafAnchor`, 120 bytes enforcing `seq == leaf_idx` for grassroots/blocklace protocols).

The safety condition for *QS-B* is that any two certifying quorums intersect in at least one custodian outside every tolerated fault set ($2q > n + f$ in the symmetric case). `qsag-quorum` accepts symmetric thresholds, weighted quorums, threshold trees, and Cachin–Tackmann asymmetric quorum systems ($B^3$), verifying pairwise intersection on enrollment. Secret keys are distributed via a 0/1 monotone span program (`MonotoneSpanProgram`): in `PersonalReleaseParty` (`crates/qsag-quorum/src/personal_release.rs`), each authorized set collapses its local lanes to an additive sharing by a public linear map and completes release over encrypted wire channels (`Π_MAC` + 118 `Π_pow7` tuples), opening only the Poseidon2 PRF-check digest.

When prevention is bypassed (a single-holder key or supra-threshold corruption), equivocation is publicly slashable: two distinct signatures at one leaf compress into an 8,800–9,440-byte `JortsEquivocationEvidence` frame verifiable from the 32-byte public key alone.

### Aggregation without pairings

**Hem** (`qsag-agg`) proves *"these $K$ public keys signed this message"* from public `JortsPoseidon2` signatures alone, with no trusted setup and only hash assumptions. It encodes verification over the 64-bit Goldilocks field ($p = 2^{64} - 2^{32} + 1$) and its quartic extension $\mathbb{F}_{p^4}$ ($p^4 > 2^{255.99}$), checks the trace via LogUp-GKR sumcheck, and commits multilinear witnesses with `[CWYZ26]` affine-combiner WHIR.

Reed–Solomon proximity conjectures near capacity were refuted in 2025–26 (`[CS25, KKH26]`), so Hem retires all capacity-proximity wire tags (`0, 1, 3`) and sets every query schedule strictly inside the proven $1 - \sqrt{\rho}$ Johnson bound across **8 wire-decodable `WhirSecurityRegime` profiles** (`crates/qsag-agg/src/pcs.rs`):

- **Unconditional $2^{128}$ Grover-floor regimes (`tags 4, 9`):** `BciksJohnsonQrom128` (`tag 4`, `cSHAKE256`, default) and `TurboShakeBciksJohnsonQrom128` (`tag 9`, Role-1 12-round `TurboSHAKE256` Canopy/PoW outer hash) sample $q = (258, 130, 88, 66)$ queries with 16-bit PoW, achieving 136 nominal Grover bits per round with no bound on adversary oracle queries.
- **Bounded-query `[CDHZ25]` salted-Merkle regimes (`tags 5–8, 10`):** accepted for aggregates only when explicitly named (`cSHAKE256` tags `5, 6`, `Poseidon2` tags `7, 8`, and `TurboSHAKE256` tag `10`), giving 128-bit salted-Merkle QROM accounting for adversaries bounded by $Q \le 2^{38}$ (`(202, 102, 70, 52)` + 16-bit PoW) or $Q + 1 \le 2^{40}$ (`(216, 109, 74, 56)`, zero PoW); see [docs/SECURITY_AND_CT_PROOFS.md](docs/SECURITY_AND_CT_PROOFS.md#hem-profile-and-qrom-accounting).
- **Classical-only (`tag 2`):** `BciksJohnsonClassical128` (72 Grover bits), restricted to low-level PCS callers and rejected by aggregate verifiers.

A leaf shard proof covers 128 signers in 445,566 B. Above one shard, Hem provides two recursive topologies exposing a uniform 14-word header (roster root, epoch, message, `[min_key_idx, max_key_idx]`, signer count, and total weight) whose strict index ordering prevents double-counting without bitmaps:

1. **Arity-16 hologram merge (`SuccinctSubtreeAggregate`):** verifies up to 16 child openings under a precommitted constraint hologram (`312–340 KiB`, `11.5 ms` single-core verification).
2. **Contractive binary subtree recursion (`SplitSubtreeAggregate`, `crates/qsag-agg/src/recursive/split.rs`):** verifies two child Spark/LogUp-GKR hologram IOPs in $\le 2^{20}$ rows (`1,048,576` at depth 2; `524,288` at depth 3), binds child `DeferredPcsClaim` digests into an `accumulator_root`, and folds all homogeneous claims at each tree level via `[CWYZ26]` into a single `FoldedLevelWhirProof` ($O(\text{depth})$ WHIR cascades total), verified through depth 3 on both CPU and Radeon RX 6750 XT Vulkan across dense validator sets and depth-37 sparse rosters.

The same prover supports a masked zero-knowledge mode for selective-disclosure credentials, threshold-hiding multisignatures, and capability batches.

### Capabilities

| Form | Size | Verifier holds | Delegate offline | Hides the token |
| --- | --- | --- | --- | --- |
| `SpongeMacaroon` (keyed sponge chain, third-party discharges) | 161 B with 3 caveats | root secret key | yes | no |
| `PqBiscuit` (chain of one-time signatures) | 1,154 B per hop | root public key | yes | no |
| zk capability (batched with non-revocation) | 233 KiB per batch | two Merkle roots | in delegated mode | yes |

All three compile the same caveat algebra, enforced by `qsag-policy` before any custodian releases a share.

### Wallet plumbing and key migration

- **`qsag-hd`**: dealerless module-lattice hierarchies, committed watch-only inventories, and local 2-of-3 non-hardened derivation.
- **`qsag-policy`**: stateful velocity, allowlist, and window rules evaluated across custodians; a passing check mints party-bound release tokens.
- **`qsag-addr`**: Bech32m post-quantum addresses and hybrid classical/PQ keys.
- **`qsag-migrate`**: local and threshold collaborative ZKBoo (`CoZK`) ownership proofs across **all four deployed curves**—`secp256k1` (P2PKH, P2WPKH, Taproot, Ethereum), `Ed25519` (SLIP-0010), `Pallas` (Orchard direct and rerandomized), and `BLS12-381` (`0x00` validator withdrawal credentials)—supporting both 3-custodian `2-of-3` replicated MPC (`outer_mpc`) and general `(t, n)` MAC-authenticated MPC (`threshold_mpc`) over `TurboSHAKE256` view commitments (`COZK_VIEW_MAGIC_V4`), even when the chain has only ever seen a public-key hash.
- **`qsag-cred`**: threshold `ML-DSA-44/65/87`, 5-server replicated and `(t, n)` SPDZ `TOPRF`, and `ZKBoo` / zk-Hem `BlindVC` selective disclosure.

## Committee sizes

| Path | Committees | Tolerates | Notes |
| --- | --- | --- | --- |
| SLH-DSA, Baggy, Jorts on the bitsliced 3-party engine | 2-of-3 | 1 malicious (may abort) | In-memory / LAN fast path (`rss256.rs`). |
| Isolated-party CNF (`IsolatedCnfParty`) for Baggy & SLH-DSA | `2-of-3`, `3-of-5`, any $2(t-1) < n$ | $t - 1$ malicious (may abort) | Per-custodian `WireTransport`; shares never reconstructed (`cnf_party.rs`). |
| Stateless signing, general $(t, n)$ | any $(t, n)$ | $t - 1$ malicious | Signing quorum collapses locally to $t$-of-$t$ additive shares. |
| Jorts, QS-A | any $(t, n)$ | $t - 1$ malicious | One online round; leaf space partitioned across $\binom{n}{t}$ committees. |
| Jorts, QS-B & `PersonalReleaseParty` | up to 255 custodians; symmetric, weighted, tree, or $B^3$ asymmetric quorums | any fault set admitted by $Q^2 \cap \bar{B} \neq \emptyset$ | Fixed-size MSP shares; symmetric liveness holds when $n \ge 3f + 1$. |
| Threshold ML-DSA-44/65/87 | $n \le 64$, $n \ge 2t - 1$ | $t - 1$ malicious | Active signing quorum of $2t - 1 \le 16$ custodians. |
| Threshold oblivious PRF (`TOPRF`) | 2-of-5 replicated (5 online, corrects 1 fault), or $2 \le t \le n \le 64$ SPDZ | 1 malicious (2-of-5); $t - 1$ on SPDZ (may abort) | SPDZ uses a non-cloneable monotone preprocessing reservoir. |
| Dishonest-majority authenticated engine | any $(t, n)$ | up to $n - 1$ malicious (may abort) | Preprocessing dominates; suited to Jorts leaves, policy, and `CoZK`. |

In the dishonest-majority engine every custodian holds a share of a long-lived MAC key $\alpha$. Opening a raw MAC residual $d = m - \alpha x$ on an invalid share would leak $-\alpha \Delta$. `qsag` instead multiplies residuals by disposable randomizers via oblivious linear evaluation (`crates/qsag-core/src/preprocessing/mac_blind.rs`) so an abort reveals only a uniform nonzero element independent of $\alpha$ (`Protocol/Threshold/MacBlind.lean`); retaining pre-generated Tower-field blinding triples in `OtMesh` cuts 3-party online MAC checks from `13.75 ms` to **`31 µs`** (`4.04 ms` amortized offline refill).

## Performance

Measured on the AMD Zen 5 + Radeon RX 6750 XT testbed documented in §7 of the [paper](paper/qsag.pdf).

**Signing and custody**

| Operation | Measured |
| --- | --- |
| Jorts, 2-of-3, preprocessed offline, in memory | 1.0 ms (81 ms over a simulated WAN) |
| QS-A, 2-of-3, encrypted channels, log synced | 4.37 ms |
| QS-B, 3-of-7 with $q = 5$, encrypted channels, log synced | 5.21 ms |
| Baggy or SLH-DSA, 2-of-3 bitsliced (`rss256`), one 256-hash Keccak wave | 54 ms |
| Baggy or SLH-DSA, isolated CNF over encrypted `WireTransport`, one 256-hash wave | 39.5 ms / 1.8 MiB (`2-of-3`); 96.2 ms / 5.9 MiB (`3-of-5`) |
| Pooled Tower-field blinded MAC check (`OtMesh`, 3 parties, online) | 31 µs (vs. 13.75 ms unpooled; 4.04 ms offline refill) |
| Compact1122, verify 1,200 votes | 1.23 s on one core; 158–187 ms on eight threads |
| Oblivious PRF, 2-of-3, one online evaluation | 4.3 ms |
| `SpongeMacaroon`, verify | 1.8 µs |

**Aggregation** (Hem over `JortsPoseidon2` signatures, default unconditional QROM profile unless noted)

| Statement | Prove | Verify | Proof |
| --- | --- | --- | --- |
| 128 signers, Radeon RX 6750 XT (Vulkan SPIR-V 1.5) | 1.33–1.56 s | 3.0 ms | 445,566 B |
| 128 signers, CPU | 2.94–3.67 s | 3.0 ms (6.2 ms on one core) | 445,566 B |
| 512 signers, one shard, CPU | 11.1 s | 3.6 ms | 556,830 B |
| Arity-16 hologram merge root (`SuccinctSubtreeAggregate`) | see model below | 11.5 ms on one core | 312–340 KiB |
| Binary `SplitSubtreeAggregate` + `[CWYZ26]` level fold (depths 2 & 3, CPU & GPU) | verified $\le 2^{20}$ / $524{,}288$ rows | $O(\text{depth})$ WHIR checks | 1 folded WHIR / level |
| Credential presentation, 32 attributes (zk-Hem, tag 7) | 0.28 s | 19.6 ms on one core | 239,507 B |
| Private multisignature, 16 slots (zk-Hem) | 3.48 s | 53 ms | 700,491 B |

CPU and GPU provers emit identical bytes, with Role-1 `TurboSHAKE256` cutting Canopy Merkle hashing by roughly $2\times$ relative to `cSHAKE256`. The Vulkan backend (ten SPIR-V 1.5 compute shaders with hardware-audited execution receipts) commits 256- and 512-signer witnesses inside 12 GiB of VRAM and builds a $2^{20}$-leaf Poseidon2 Merkle tree in 82 ms ($58\times$ one CPU thread). On one Zen 5 core (AVX-512), Keccak runs at 3.15 GB/s and eight-way Poseidon2 Merkle hashing takes 111 ns per node.

**Consensus scaling (analytic schedule anchored on measured shards).** [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md) combines measured shard and commit times with a pipelined GPU merge schedule:

| Validators | Raw signatures | Tree | Critical path (model) | Certificate | Verify |
| --- | --- | --- | --- | --- | --- |
| 1,500 | 6.8 MiB | 12 shards, 2 levels | 2.4 s | 321 KiB | 11.5 ms |
| 16,384 | 74.6 MiB | 128 shards, 4 levels | 3.1 s | 321 KiB | 11.5 ms |
| 100,000 | 455 MiB | 782 shards, 5 levels | 3.5 s | 321 KiB | 11.5 ms |
| 1,048,576 | 4.66 GiB | 8,192 shards, 7 levels | 4.3 s | 321 KiB | 11.5 ms |
| 1,048,576, fewest network hops | 4.66 GiB | 2,048 shards of 512, 3 levels | 9.5 s | 331 KiB | 11.5 ms |

## Hardware (`hardware/`)

Both silicon targets described in §7.6–7.7 of the [paper](paper/qsag.pdf) live as synthesizable SystemVerilog in [`hardware/`](hardware):

- **`QSAG-NI` ([`hardware/asic/`](hardware/asic), [`hardware/fpga/`](hardware/fpga)):** a co-designed hardware verifier sharing 12 Dadda carry-save adder trees, a 9-product tower Karatsuba $\mathbb{F}_{p^4}$ unit, a 4-way C-slowed Canopy batch engine, and a 2-round/clock Keccak/`TurboSHAKE256` sponge. Synthesized (SRAM black-boxed, pre-layout) across **four open ASIC PDKs**—`ASAP7` (`832.0 kGE`), `IHP130` (`832.6 kGE`), `Nangate45` (`862.9 kGE`), and `Sky130` (`908.7 kGE`)—plus **Xilinx UltraScale+** (`XCUP_RING`: `86,496` LUT / `768` `DSP48E2`; `VU9P_TURBO`) and **Lattice `ECP5-85F`** (`ECP5_COMPACT`, 16 `MULT18X18D`). Backed by `99/99` Bitwuzla/Z3 equivalence miters, `5` exact ANF and `32` CSA certificates, a `0 sorryAx` `Obend` Lean 4 proof (`QsagNi.lean`), and `8/8` Verilator top-level workloads replaying exported `QSAGSTA1` proofs.
- **`Dregg-180` ([`hardware/gf180mcu/`](hardware/gf180mcu)):** a 5.0 V physical custody enclave targeting GlobalFoundries `GF180MCU` 180 nm CMOS (`SLOT_0P5X0P5`: `1,936 × 2,531 µm` die, `1.733 mm²` core, zero hard SRAM macros). Integrates a GALS shell (glitch-free mux, 32-tap DCRO, SPI/source-sync/clockless Muller C-element link), CapTP `SpongeMacaroon` capability vat (`[12,7,4]` distance-4 Hamming FSM, `latrnq_1` zero-clock tamper wipe, non-bricking `OP_BIST`), 64-RO PUF with bit-serial `BCH(63,36,t=5)` fuzzy extraction, `13.56 MHz` prescaled NFC + 32-bit Direct-RF `NCO`, `< 5 ns` `Brands–Chaum` responder (`~2.9 ns` TT, `~4.6 ns` SS) with `PAD2CORE`-loopback Vernier TDC, 2-cycle staggered `WOTS+C` fault self-check, `Metal5` serpentine active shield, foundry `BSIM4` (`sm141064.ngspice`) transient decks, and a self-tested 4-layer `13.56 MHz` reference PCB (`pcb/planar_nfc_coil_calc.py`). Passes `593/593` Verilator vectors and Z3 datapath LEC, with baseline flat synthesis at `835,495 µm²` (`48.2%` of core, before a `> 226,000 µm²` sequential diet) and detailed placement complete; post-CTS LibreLane routing, multi-corner OpenSTA `Fmax`, and DRC/LVS remain in flight.

## Verification

Formal proof is used throughout as an engineering filter: protocols, extracted Rust functions, and decoded assembly routines are checked in Lean 4.35 with `0 sorry`, `0` custom axioms, `0 native_decide`, and `0 Classical.choice` (strictly `{propext, Quot.sound}`).

1. **Protocol and storage proofs** ([`lean/Qsag/`](lean/Qsag)). `269` layered modules (`407,223` lines) with `0 import all` enforced by [`scripts/check_lean_policy.py`](scripts/check_lean_policy.py). Covers Cut-the-Hash signing, `PORS+FP`, `PosixCrashWal` and two-slot sector-tear recovery, quorum intersection, ideal-OLE blinded MAC checks (`MacBlind.lean`), `[CWYZ26]` proximity bounds and unitary BBBV97/O2H budgets, and the ideal specifications in [`lean/Qsag/Spec/`](lean/Qsag/Spec). `127` top-level theorems in `Qsag.Top` replay cleanly across 6 independent kernels (`lean`, `leanchecker-paranoid`, `lean4lean`, `nanoda_bin`, `con-leche`, `con-ron`).
2. **Compiler-extracted Rust MIR** ([`aeneas/`](aeneas)). Charon and Aeneas translate `aeneas/qsag-verified` (`6,805` audited declarations, `71` 6-kernel theorems in `aeneas/lean`) and `aeneas/qsag-whir-verified` (`1,869` declarations, `37/37` `Funs.lean` definitions, `114/114` 6-kernel theorems in `aeneas/lean-whir`), discharging field/tower arithmetic, Keccak sponge framing (`shake256_absorb_after_squeezing_fails`), session release guards, and the WHIR verifier core. [`aeneas/qsag-verified/extraction-coverage.json`](aeneas/qsag-verified/extraction-coverage.json) records which `63` of `235` extracted functions sit on live production call paths.
3. **Machine code and ELF-to-MIR triangles** ([`lean/Qsag/Machine/`](lean/Qsag/Machine), [`aeneas/lean/QsagVerified/Proofs/ElfMirTriangles.lean`](aeneas/lean/QsagVerified/Proofs/ElfMirTriangles.lean)). All `28` `.rlib` assembly kernels (`19` x86-64, `9` AArch64; `3,355` decoded instructions) are proved secret-independent under `Spec.DitHardwareContract` (`PlatformContractInstances.lean`), composed with MIR refinements in `ElfMirTriangles.lean`, and paired with whole-archive `codegen-units=1` taint screening (`scripts/audit_elf_ct.py`).
4. **Differential and silicon gates** ([`validation/`](validation), [`hardware/`](hardware)). `74/74` standalone differential suites check Rust and executable Lean models against independent implementations, alongside native x86-64 ISA cosimulation and `99/99` SMT hardware equivalence miters.

What is not proved: whole-binary refinement of the linked Rust workspace; an unconditional 4-stage `WhirScheduleCert` QROM composition certificate for the deployed Hem verifier (per-round `[CWYZ26]` bounds and `whir_exec_closed_qrom_soundness` are proved, while `deployedSched`'s schedule certificate and sliced MCA bridge remain open); a complete zero-knowledge simulator for zk-Hem; or post-route silicon timing closure on `Dregg-180`. See [ASSURANCE.md](ASSURANCE.md) for the exact boundaries.

## Quickstart

`rust-toolchain.toml` pins Rust `1.99.1`. The core workspace builds offline with zero `crates.io` runtime dependencies.

```bash
# Known-answer tests, then the supported schemes and wire sizes.
cargo run --release -p qsag-cli -- kat
cargo run --release -p qsag-cli -- info

# Generate an SLH-DSA key, sign a file, verify it.
umask 077 && D=$(mktemp -d /tmp/qsag.XXXXXX) && printf 'hello\n' > "$D/msg"
cargo run --release -p qsag-cli -- keygen --scheme slh-dsa-shake-128f \
  --secret-out "$D/sk.json" --public-out "$D/pk.json"
cargo run --release -p qsag-cli -- sign   --secret "$D/sk.json" --in "$D/msg" --out "$D/sig.json"
cargo run --release -p qsag-cli -- verify --public "$D/pk.json" --in "$D/msg" --sig "$D/sig.json"
```

The CLI drives threshold custody (`quorum keygen`, `sign`, `refresh`, `reshare`), Hem aggregation (`aggregate`), addresses, HD derivation, 4-curve `CoZK` migration (`migrate`), credentials (`cred`), and capabilities (`policy init`, `policy macaroon`, `policy biscuit`). Stateful vaults require `--anchor-dir <dir>` (on a disjoint device), `--anchor-tpm-nv <index>`, or `--anchor-vmgenid`—or `--ephemeral-unanchored` for disposable test keys.

Worked examples:

```bash
cargo run --release -p qsag-cli --example slh_dsa_quickstart
cargo run --release -p qsag-cli --example threshold_slh_dsa_quickstart
cargo run --release -p qsag-cli --example few_time_signatures
cargo run --release -p qsag-cli --example succinct_k_to_1_aggregation
cargo run --release -p qsag-cli --example pq_address_and_policy

# Consensus vote-size and recursive aggregation harnesses.
cargo run --release -p qsag-agg --example mock_solana_alpenglow
cargo run --release -p qsag-agg --example mock_ethereum_beam
```

Policy, scaling, and differential verification scripts:

```bash
python3 scripts/check_lean_policy.py
python3 scripts/quorum_and_consensus_scaling.py --self-test
python3 hardware/gf180mcu/pcb/planar_nfc_coil_calc.py --self-test
./scripts/run_differential_validation.sh
```

## Crates

Library crates are `no_std` + `alloc`; `std` is used only for CLI entrypoints, POSIX file journals, hardware `/dev/tpmrm0` / `sysfs` anchors, and socket transports.

| Crate | Contents |
| --- | --- |
| `qsag-core` | Cut-the-Hash SLH-DSA, Baggy (`PORS+FP`), Jorts, `BeltLatch`, TPM/VMGENID/mount anchors, bitsliced RSS and authenticated MPC engines, pooled `OtMesh` MAC blinding, MSP access structures, blocklace & equivocation proofs |
| `qsag-quorum` | Quorum switching (*QS-A*, *QS-B*), general and $B^3$ asymmetric quorum systems, isolated per-custodian CNF (`IsolatedCnfParty`), wire-isolated `PersonalReleaseParty`, encrypted wire channels |
| `qsag-fts` | `Compact1122` and `Full256Bit` few-time signatures, parallel-seeded non-interactive shares, SIMD batch verification, dealerless threshold key ceremony |
| `qsag-agg` | Hem prover and verifier across all 8 `WhirSecurityRegime` profiles, arity-16 `SuccinctSubtreeAggregate`, contractive binary `SplitSubtreeAggregate` + `FoldedLevelWhirProof`, and zk-Hem relations |
| `qsag-accel` | Portable CPU backend and Vulkan SPIR-V 1.5 compute shaders (`RADV` / MoltenVK) with execution receipts |
| `qsag-asm` | Certified x86-64 (AVX2, AVX-512, VPCLMULQDQ) and AArch64 (NEON, PMULL) kernels (`19 + 9` `.rlib` symbols) and `LockedRecord` durable storage |
| `qsag-hd` | Dealerless module-lattice key hierarchies and committed watch-only inventories |
| `qsag-policy` | Stateful policy ledgers, `SpongeMacaroon` chains, and `PqBiscuit` tokens |
| `qsag-addr` | Bech32m addresses and hybrid classical/post-quantum keys |
| `qsag-cred` | Threshold `ML-DSA-44/65/87`, 5-server replicated and `(t, n)` SPDZ `TOPRF`, and `ZKBoo` / zk-Hem `BlindVC` credentials |
| `qsag-migrate` | Local and threshold (`2-of-3` replicated and `(t, n)` SPDZ) `CoZK` ownership proofs for `secp256k1`, `Ed25519`, `Pallas`, and `BLS12-381` |
| `qsag-cli` | Command-line interface and end-to-end examples |

## Further reading

- [paper/qsag.pdf](paper/qsag.pdf) ([source](paper/qsag.typ)): constructions, security theorems, measurements, and silicon architectures (`QSAG-NI` and `Dregg-180`).
- [ASSURANCE.md](ASSURANCE.md): audit gates, ideal-machine boundaries, open obligations, and trusted computing base.
- [docs/QUORUM_AND_CONSENSUS_SCALING.md](docs/QUORUM_AND_CONSENSUS_SCALING.md): analytic consensus and directory scaling model.
- [docs/PROOF_ARCHITECTURE.md](docs/PROOF_ARCHITECTURE.md): layering and theorem map of `lean/Qsag/`.
- [docs/AENEAS_VERIFICATION.md](docs/AENEAS_VERIFICATION.md): Charon/Aeneas MIR translation, `extraction-coverage.json`, and `ElfMirTriangles`.
- [docs/SECURITY_AND_CT_PROOFS.md](docs/SECURITY_AND_CT_PROOFS.md): concrete security parameters, QROM accounting, and constant-time proofs.

## License

Authored by ember arlynx (`<ember@lunar.town>`). Licensed under either of [Apache-2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your option.
