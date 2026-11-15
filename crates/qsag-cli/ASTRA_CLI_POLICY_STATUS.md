# astra-cli-policy status

Updated 2026-11-15 by Codex. Scope: `qsag-cli` and `qsag-policy` only. This lane is **partially complete**; the remaining protocol and persistence work below is required before claiming production threshold availability.

## Implemented

- Replaced CLI plaintext correlated OT and shared Beaver pad secret with independently randomized RLWE/IKNP channels, `CommittedCorrelatedOt`, and `ParallelSeededGilboaProducts`. The transport remains an in-process endpoint-bound transport; this does not provide deployment across separate custodian hosts.
- Removed the CLI's height-four and sixteen-party FTS limits and raised the RSS CLI height limit. This does not implement a hypertree: the upstream engines still eagerly construct one tree.
- HD key generation persists encrypted `hd-custodian-P.share` bundles under `cshake256-iterated-v1`. Recovery opens only selected custodians. Each bundle contains its custodian's own entropy, private inbound deliveries, and public commitments/confirmations; recovery validates/rebuilds only that custodian's local state. It contains neither other custodians' private entropy nor their inboxes. Legacy seed vaults retain their old recovery path. Normal new enrollment requires a passphrase unless `--allow-unencrypted` is explicit; deterministic fixtures retain compatibility.
- Policy-ledger partial quorums use an authoritative shared spend/replay ledger, atomically persisted with every guard before release. Guardian requirements follow the matched tier. No all-party/guardian surrogate is imposed when the tier permits a partial quorum.
- Configurable replay capacity (default 65,536, maximum 1,048,576) and preprocessing capacity (default 64, maximum 1,048,576) replace fixed replay/slot encodings. Replay records are never evicted to make room. Per-peer slot bitmaps grow with provisioning; OT preparation is batched in groups of 256 slots. CLI policy enrollment accepts `preprocessing_slots` in its policy JSON. Larger pools still require provisioning; automatic online replenishment is not implemented.
- Added `qsag_policy::macaroon`: bounded canonical 256-bit cSHAKE256 chained tags, conjunctive first-party caveats, trusted-key third-party discharges, and `CAV_BIND_TO_PARENT`. The prepared `MacaroonVerifier` authenticates each caveat on every request. Its cached root tag is a server-side minting secret. A 161-byte/three-caveat token measured 1.1–2.1 microseconds across runs (1.31 microseconds in the final policy test run) per prepared verification on the remote host; this is not a latency guarantee for arbitrary caveat/discharge counts or cold verification. A 256-bit tag is not a claim of 256-bit quantum forgery resistance.

## Compatibility

New policy storage uses CLI root v2, committee bundle PLB2, guard checkpoint V6, and shared checkpoint V2. Earlier formats fail closed. No migration tool is implemented. Existing spent amounts, nonce burns, consumed slots and trusted generation fences must be preserved by any future migration; resetting or re-enrolling a live ledger is not a safe migration.

HD's new local bundle encoding uses the current upstream 256-bit `CustodianSet` encoding. Old seed vaults are recognized separately. Quorum and credential formats have not been redesigned by this lane.

## Outstanding dependencies / decisions

1. **RSS quorum availability:** `RssKeyShare256` in `qsag-core/src/keccak_mpc.rs` has private share components and no persistence codec. `Rss256Engine::new` and `JortsSigner` require all three parties. A real active-subset protocol and authenticated share codec must be provided by the core owner, then wired into `quorum.rs`. Merely saving three seeds or rebuilding a missing custodian would not satisfy this requirement.
2. **Credentials:** `ThresholdMlDsaSignerShare` has private fields and no persistence codec. `ThresholdVerificationPack::signing_quorum()` explicitly returns `2*t-1`. The credential owner must expose an authenticated share codec and resolve the actual signing threshold before CLI `t`-party availability can be implemented. The fixed-five-server VOPRF also lacks a persisted-server API. `cred.rs` still regenerates its full DKG and has not been fixed in this lane.
3. **HEM quorum:** persisted per-party encrypted share codecs already exist, but CLI generation transactions load and rewrite all `n` files through `HemDynamicShamirQuorum::from_persisted_shares`. Detached `sign_from_shamir_share_slice` exists, but safe integration needs a subset-aware durable burn/latch transaction and reconciliation when offline custodians return. It is not safe to emulate absent latch acknowledgements or only change the file-loading loop. The current explicit rejection of unsupported HEM policy flags is preserved.
4. **Production hypertrees:** removing front-end caps does not remove upstream FTS power-count bounds or single-tree eager work. A scalable upstream hypertree/on-demand profile is still needed. Large single-tree heights have not been tested and are not a substitute.
5. **Migration:** no changes to `migrate.rs`; no credential/quorum migration path can be implemented until their persisted share formats are available.
6. **Full Clippy:** the exact requested command currently fails in unowned `qsag-core/src/preprocessing/triple_f2.rs:406,465` on `clippy::type_complexity`. Owned crates pass with `--no-deps`; no upstream lint was suppressed or modified here.

## Remote validation

All builds use `/tmp/qsag-astra-cli` on `persvati-remote`, under `SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s`. No local builds or Git mutations were performed by this lane.

- `cargo test --release -p qsag-policy`: 32 passed, including a 300-slot algebra test spanning the 256-slot OT batch boundary (`policy-final-default.log`).
- `cargo test --release -p qsag-policy --features std`: 33 passed (`policy-final.log`), including filesystem checkpoints.
- `cargo test --release -p qsag-cli policy_ledger::tests`: eight passed (`policy-cli-tests.log`), including guardian-free partial approval, spend/replay persistence, window rotation, and rollback refusal. The guardian-free case also passed after the final root-format change (`guardian-final.log`).
- `cargo test --release -p qsag-cli --test hd_persisted_custody`: passed (`hd-custody-test-2.log`). Encrypted 2-of-3 recovery/sign/verify with the third party file physically absent; one party is refused.
- Real OT/Gilboa test passed on final sources (`production-ot-final.log`), including chunk-boundary products and replay refusal.
- `cargo clippy -p qsag-policy -p qsag-cli --all-targets --no-deps -- -D warnings`: passed (`clippy-owned-final.log`).
- Exact Clippy failure: `clippy-exact-final.log`.
