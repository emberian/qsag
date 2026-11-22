# Migration Security Scope (`qsag-migrate` over `zk-Hem v2`)

`qsag-migrate` lets the holder of a legacy credential state "this post-quantum
address is mine" in a way a verifier can check without learning the legacy secret. It
comprises four subsystems:

1. **Multi-chain ownership statements and `zk-Hem v2` proofs (`hem::relations`):**
   Bitcoin (`P2PKH`, uncompressed `P2PKH`, `P2SH-P2WPKH`, `Taproot` key-path and
   script-tree), Ethereum (`Keccak256` EOA and `0x00` `BLS12-381` withdrawal credentials),
   Ed25519 (RFC 8032 seed, `SLIP-0010`, and `BIP32-Ed25519` Khovratovich–Law), `BIP-32`
   master seeds & extended keys (public or hidden derivation paths), and `BatchStatement`
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
4. **Threshold collaborative prover (`hem::collab`):**
   Quorum proving over MAC-authenticated additive shares (`Sb`, `Sh` over `Fp5`) from
   `(k, n)` Shamir or XOR custody shares without reconstructing the legacy secret on any
   host, using **9-triple Toom-3 `Fp5` Beaver multiplication** (`9` base triples per
   quintic product — 43.75% fewer triples than `Fp4` schoolbook's 16) and **pre-round-1
   anti-rollback preprocessing burn** (`Engine::new_anchored` / `prove_ownership_party_anchored`;
   unanchored constructors are sealed to `#[cfg(test)]`) so every public collaborative MPC
   session is transcript- and monotone-counter-anchored by construction and an
   aborted ceremony can never reuse MAC key shares or Beaver triples.

The legacy 438-repetition ZKBoo migration engine (`qsag-migration-proof-v1`) and the
256-bit-digest `zk-Hem v1` hiding wrapper have been retired; all proofs use `zk-Hem v2`
(`qsag_agg::zk_hem::v2`, 400-bit digests, 32-byte per-tree `tree_nonce`, `QuinticGoldilocks`,
DKT26 `2026/2056` Theorem 5.12 line- vs-subcode soundness).

## What a proof shows, and what it does not

A valid proof shows that whoever made it knew a secret behind the legacy credential and
chose the target post-quantum address, the migration domain, and the epoch of the statement.

It does not disable the legacy key on the origin chain, and two proofs for different
targets are both valid unless recorded in a stateful turnstile (`NullifierRegistry` or
consensus state).

### Hidden-key vs. revealed-key statements

* **Hidden-key statements** (`Secp256k1Key`, `Bls12381Key`, `Taproot` internal key,
  Zcash `t1` hidden key) prove knowledge of a discrete-logarithm scalar hidden behind an
  on-chain hash (`HASH160`, `Keccak256`, `TapTweak`, `0x00 || SHA256`). They are
  post-quantum sound only while the raw public key has never been revealed on chain.
  20-byte `HASH160` / `Keccak256[12..]` addresses carry an inherent 160-bit classical /
  80-bit Grover preimage ceiling from the legacy address format itself.
* **Revealed-key / seed-provenance statements** (`Ed25519Seed`, `Bip32` seed root,
  `Slip10`, Zcash `ZIP-2005` Ironwood `0x03`, Orchard/Sapling `sk` or `ZIP-32` seed)
  prove knowledge of a hash preimage (`SHA-512`, `HMAC-SHA512`, `BLAKE2b`, `BLAKE2s`).
  Computing discrete logarithms on chain does not invert those hashes. Extended-key
  roots (`Bip32Root::ExtendedKey`, `Bip32Ed25519`) are sound only while no extended
  public key at or above the root node has been exported (ePrint 2026/1508 Prop. 6.1).

## Proof system (`zk-Hem v2`)

All single-prover (`ZkHemV2Proof`, `QSAGZKH2`) and collaborative split-share
(`ZkHemV2SplitProof`, `QSAGZKS2`) proofs run over `qsag_agg::zk_hem::v2` under
`Profile::TurboShakeJohnson400` (or `Profile::CshakeJohnson400`):

* **Field:** `QuinticGoldilocks` (`Fp5 = F_p[u] / (u^5 - 3)`, ~320-bit extension).
* **Commitments:** 400-bit Merkle digests (~133-bit QROM collision resistance) with a
  32-byte per-tree `tree_nonce` absorbed into every Stage-0 leaf (`|D'|`-independent
  multi-tree salt security) and 16-bit proof-of-work.
* **Soundness:** Dao–Kominers–Thaler (`2026/2056`) Theorem 5.12 line-point soundness
  across `N <= 2^28` with 266 Stage-0 queries (`>= 128` bits classical & quantum
  round-by-round soundness; see `crates/qsag-agg/SECURITY.md` §V2).

## Threshold collaborative proving (`hem::collab`)

* **9-triple Toom-3 `Fp5` Beaver multiplication (`collab::engine::Engine::mul_ext`):**
  Evaluates degree-4 operand polynomials locally at `{0, 1, -1, 2, -2, 3, -3, 4, inf}`,
  batches all 9 base-field Beaver products in one round, interpolates over `F_p`, and
  reduces modulo `u^5 - 3`.
* **Pre-round-1 anti-rollback burn (`collab::engine::Engine::new_anchored`):**
  Computes `tape_id = cSHAKE256("QSAG.COLLAB.TAPE.ID/v1", key_shares || lengths || triples || randoms)`
  and advances both the process-wide burned-tape set and the hardware/external
  `ExternalMonotoneAnchor` **before round 1** (`0` network bytes sent). The tape snapshot must retain its original expected generation across restarts.
  A stale generation or an in-process duplicate fails before transmission and drops
  the tape. The external checkpoint stores the latest generation and tag. Historical
  tape IDs are retained only for the lifetime of the process.
