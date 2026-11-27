# Migration Security Scope (`qsag-migrate` over `zk-Hem v2`)

`qsag-migrate` lets the holder (or threshold custodian quorum) of a legacy credential
prove "this post-quantum address is mine" without revealing the legacy secret. It
comprises four subsystems.

1. **Multi-chain ownership statements and `zk-Hem v2` proofs (`hem::relations`):**
   Bitcoin (`P2PKH`, uncompressed `P2PKH`, `P2SH-P2WPKH`, `Taproot` key-path and
   script-tree), Ethereum (`Keccak256` EOA and `0x00` `BLS12-381` withdrawal credentials),
   Ed25519 (RFC 8032 seed, `SLIP-0010`, and `BIP32-Ed25519` Khovratovich–Law), `BIP-32`
   master seeds and extended keys (public or hidden derivation paths), and `BatchStatement`
   shared-prefix multi-address proofs (`QSHEMOW2`).
2. **Zcash NU7 `v2026.9.0` statements (`hem::zcash`):**
   - `ZIP-2005` Ironwood quantum-recoverable shielded note recovery (`RecoveryStatement` /
     `RecoveryProof`, `QSHEMZN2`, lead byte `0x03`, BLAKE2s rehashed tree + `RedPallas`
     `SpendAuthSig`),
   - Orchard diversified payment address ownership (`AddressStatement` / `AddressProof`,
     `QSHEMZA2`),
   - Sapling diversified payment address ownership over Jubjub (`SaplingAddressStatement` /
     `SaplingAddressProof`, `QSHEMZS2`),
   - `ZIP-2007` transparent `t1` / `tm` P2PKH ownership (`TransparentStatement` /
     `TransparentProof`, `QSHEMZT2`).
3. **Durable one-way nullifier registry (`hem::registry`):**
   Append-only authenticated turnstile (`TwoSlotHwm` + inode-bound MAC chain + optional
   hardware/TPM/filesystem `ExternalMonotoneAnchor`) enforcing at-most-once migration per
   nullifier and per on-chain legacy credential identifier.
4. **Networked PQ-hybrid threshold collaborative prover (`hem::collab` & `qsag migrate collab`):**
   Dealerless preprocessing and quorum proving over MAC-authenticated additive shares
   (`Sb`, `Sh` over `Fp5`) from `(k, n)` `GF(2^8)` Shamir or XOR custody shares without
   reconstructing the legacy secret on any host, using **9-triple Toom-3 `Fp5` Beaver
   multiplication** (nine base triples per quintic product, compared with 25 for
   schoolbook multiplication in the same field) and **pre-round-1 anti-rollback preprocessing burn**
   (`Engine::new_anchored` / `prove_ownership_party_over_wire_anchored`).

The former 438-repetition ZKBoo migration engine (`qsag-migration-proof-v1`) and the
256-bit-digest `zk-Hem v1` hiding wrapper have been retired; all single-prover and
collaborative proofs run exclusively on `zk-Hem v2` (`qsag_agg::zk_hem::v2`).

## Statement and settlement

A valid proof shows that its producer knew a valid witness behind the legacy credential and
bound the target post-quantum address, migration domain, and statement epoch.

It does not disable the legacy key on the origin chain, and two proofs targeting different
destinations are both algebraically valid unless gated by a stateful turnstile
(`NullifierRegistry` or origin/destination consensus state).

### Hidden-key vs. revealed-key statements

* **Hidden-key statements** (`Secp256k1Key`, `Bls12381Key`, `Taproot` internal key,
  Zcash `t1` hidden key) prove knowledge of a discrete-logarithm scalar hidden behind an
  on-chain hash (`HASH160`, `Keccak256`, `TapTweak`, `0x00 || SHA256`). They remain
  post-quantum sound only while the raw elliptic-curve public key has never been exposed on
  chain. Legacy 20-byte `HASH160` / `Keccak256[12..]` addresses carry an inherent 160-bit
  classical / 80-bit Grover preimage ceiling from the origin address format.
* **Revealed-key / seed-provenance statements** (`Ed25519Seed`, `Bip32` seed root,
  `Slip10`, Zcash `ZIP-2005` Ironwood `0x03`, Orchard/Sapling `sk` or `ZIP-32` seed)
  prove knowledge of a symmetric hash preimage (`SHA-512`, `HMAC-SHA512`, `BLAKE2b`,
  `BLAKE2s`), which Shor's discrete-logarithm algorithm on the public key does not invert.
  For `Bip32Root::ExtendedKey` and `Bip32Ed25519`, a valid statement admitted as
  `KeyExposure::Revealed` must prove **at least one child derivation**. Public paths
  must be nonempty. For a hidden BIP-32 path the first step must be active in the
  circuit, even when the public maximum depth is positive. At depth zero the leaf
  would be the starting scalar and the chain code would never enter the relation.
  Soundness also assumes that no extended public key at or above the start node has
  been exported. This is a wallet-history assumption outside the proof.
  [BPRR26, Proposition 6.1]

## Proof system (`zk-Hem v2`)

All single-prover (`ZkHemV2Proof`, `QSAGZKH2`) and collaborative split-share
(`ZkHemV2SplitProof`, `QSAGZKS2`) proofs run over `qsag_agg::zk_hem::v2` under
`Profile::TurboShakeJohnson400` (`[RFC9861]`, tag `17`) or `Profile::CshakeJohnson400`
(`[SP800-185]`, tag `16`):

* **Field:** `QuinticGoldilocks` (`Fp5 = F_p[X] / (X^5 - 3)`, `|Fp5| > 2^319.998`).
* **Commitments and grinding:** 400-bit (`50`-byte) Merkle digests (~133-bit QROM collision
  resistance) with a fresh 32-byte per-tree `tree_nonce` and 32-byte per-leaf salts
  absorbed into every Stage-0 leaf (`|D'|`-independent $\binom{P}{2}/2^{256}$ multi-tree
  salt collision bound), and **0 bits of proof-of-work grinding** (`grinding = none`, so
  classical and quantum round-by-round soundness errors coincide).
* **Soundness:** Dao–Kominers–Thaler (`[DKT26]`, Theorem 5.12) packed-fiber line soundness
  across `2^16..=2^28` cells with **`267` Stage-0 fiber queries** for `2^16..=2^23` cells
  and **`266` Stage-0 fiber queries** for `2^24..=2^28` cells (`STAGE0_QUERIES` in
  `qsag_agg::zk_hem::v2::params`). The transcribed rational schedule budget is below
  $2^{-128}$ at $Q \le 2^{64}$. Its application requires the proximity, root-consistency
  and ideal-oracle hypotheses of the proof-system reduction.
  [Aggregation security specification](../qsag-agg/SECURITY.md)

## Networked PQ-hybrid threshold collaborative proving (`hem::collab` & `qsag migrate collab`)

Custodians execute collaborative proving without reconstructing the legacy secret via three
CLI subcommands (`crates/qsag-cli/src/migrate_collab.rs`) backed by
`crates/qsag-migrate/src/hem/collab/{engine,net,over_wire,prep_ot,prep_wire,tape}.rs`:

1. **Custody secret splitting (`qsag migrate collab split-secret`):**
   Splits a 32-byte legacy secret over `TowerGf256` Shamir polynomials (`2 <= k <= 64`,
   `k <= n <= 255`), writing mode-`0600` share files atomically and wiping `SecretBuffer`
   intermediates on drop.
2. **PQ-hybrid forward-secret TCP mesh (`hem::collab::net::connect_tcp_stream_mesh`):**
   Both `qsag migrate collab prep` and `qsag migrate collab prove` connect $2 \le n \le 64$
   custodians over `ConfidentialWireChannel`. Each pairwise link runs an ephemeral
   **`X25519 + ML-KEM-768`** (`[FIPS203]`) key exchange authenticated by per-pair 32-byte
   pre-shared keys (`--links`) and bilateral transcript confirmation (refusing static-PSK
   downgrade via `NetError::ForwardSecrecyUnavailable`). Fragments travel inside ratcheted
   `cSHAKE256` encrypt-then-MAC `"QSWF"` frames tagged with `"QSCF"`, binding deployment ID,
   session ID, directed party indices, and strict monotonic sequence numbers.
3. **Dealerless preprocessing & encrypted tape binding (`qsag migrate collab prep`):**
   Computes exact `(triples, randoms)` circuit demand (`ownership_prep_demand`), runs
   dealerless Ring-LWE / OT preprocessing (`prepare_party`) hedged with private host
   entropy, and seals the resulting `Preprocessing` tape under a local `.migration-key`
   using `QSAG.CLI.MIGRATE.TAPE.STREAM/v1` and `QSAG.CLI.MIGRATE.TAPE.TAG/v1` bound to
   `(deployment_id, session, party, n)`.
4. **Anchored pre-round-1 burn & 9-triple Toom-3 online proving (`qsag migrate collab prove`):**
   - Evaluates `Fp5` products via **9-triple Toom-3 Beaver multiplication**
     (`collab::engine::Engine::mul_ext`) at `{0, 1, -1, 2, -2, 3, -3, 4, inf}` in a single
     batched base-field opening round, interpolating over $\mathbb{F}_p$ and reducing modulo
     $X^5 - 3$.
   - The CLI requires an anchor or the explicit `--ephemeral-unanchored` waiver.
     When consuming a stored tape it creates an exclusive burn receipt, removes
     the tape file, and syncs its parent directory. On the anchored path
     `Engine::new_anchored` reserves the tape identifier against the external
     anchor before the first online proving round. Connection setup and
     preprocessing can already have exchanged frames. Each custodian verifies
     the assembled split proof before releasing it.

### What opens during witness input

**Authenticated, one-time-padded input masks.** For $m$ base-field inputs,
`Engine::input` consumes $m$ authenticated masks $[r_i]$ and an independent
authenticated extension-field pad $[b]$. Only the owner reconstructs candidate
values $r'_i,b'$ from the private deliveries. It commits to the complete vector
before the parties draw a joint challenge $\chi$ in `Fp5`. The owner broadcasts

$$\sigma = b' + \sum_{i=0}^{m-1} \chi^{i+1} r'_i.$$

The parties pair this claimed opening with the MAC of the independently computed
sharing $[b]+\sum_i\chi^{i+1}[r_i]$ and run the SPDZ **MacCheck** (`Engine::check`).
The independent pad hides the linear combination of input masks. Only after the
check succeeds does the owner **compute** and broadcast $\varepsilon_i=x_i-r'_i$.
Adding the public delta to $[r_i]$ yields the authenticated input. Failure of this check poisons the engine before the delta is computed.

**One Booleanity opening per tested batch.** `input_secret_bits` flattens all owners’ bit vectors
and checks them together on shares. After computing and authenticating the residual
products, parties draw fresh public coefficients $c_i$ and an independent secret
`Fp5` blinder $[\rho]$. They open only
$\rho\sum_i c_i b_i(b_i-1)$, authenticate the opening, and require zero.
Thus the transcript contains zero per-bit $b_i(b_i-1)$ openings. A failed batch
yields a blinded aggregate value and aborts.

**Witness-generation order.** Statistical-mask openings and masked denominator
openings must use `checked = true`. The scheduler authenticates all preceding
openings **before** executing the round that reveals the value. Deferring this
check until the periodic MAC batch would allow an earlier incorrect multiplication
to invalidate the mask. Short decompositions use 40 bits of statistical slack.
That privacy parameter is distinct from the SPDZ authentication bound and the
public proof-system error budget.

## References

- **`[BPRR26]`** V. Botta, M. Pospieszalski, E. Ragnoli, J. Ranvier, *ZKPoSP: Post-Quantum Zero-Knowledge Proofs for Hierarchical Deterministic Wallets*, IACR ePrint 2026/1508, 2026.
- **`[DKT26]`** Q. Dao, S. D. Kominers, J. Thaler, *Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs*, [IACR ePrint 2026/2056](https://eprint.iacr.org/2026/2056), 2026.
- **`[FIPS203]`** NIST FIPS 203, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, 2024.
- **`[RFC9861]`** B. Viguier, D. Wong, G. Van Assche, Q. Dang, J. Daemen, *KangarooTwelve and TurboSHAKE*, [IETF RFC 9861](https://www.rfc-editor.org/rfc/rfc9861), 2025.
- **`[SP800-185]`** NIST SP 800-185, *SHA-3 Derived Functions: cSHAKE, KMAC, TupleHash and ParallelHash*, 2016.
