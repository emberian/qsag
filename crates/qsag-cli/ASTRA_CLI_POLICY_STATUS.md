# CLI custody status

Updated 2026-11-15 by Codex (`astra-cli-finish`; current ownership: `qsag-cli` only). Earlier policy work below was completed by `astra-cli-policy`. This lane is **partially complete**; the remaining protocol and persistence work below is required before claiming production threshold availability.

## Implemented

- ML-DSA enrollment now writes per-custodian `mldsa-party-P.share` local restoration bundles, sealed with `cshake256-iterated-v1` when a passphrase is supplied. Normal enrollment requires a passphrase unless `--allow-unencrypted` is explicit; `--deterministic` retains smoke-fixture compatibility. Each bundle holds only its own entropy, its received DKG messages, and its burn-ledger MAC key. Enrollment metadata and outgoing-round fingerprints bind local restoration; neither another party's entropy nor another party's inbox is persisted in a bundle. New signing loads/restores only selected parties, checks their enrollment/public key, and holds their vault locks through signing. This is **local transcript restoration**, not a direct upstream share codec. Old seed-only vaults retain their compatibility path.
- Encrypted ML-DSA signing with signers `0,2,4` from five enrolled custodians passes with **all share/state files for custodians 1 and 3 physically deleted**. Wrong passphrases fail without a burn. The standard FIPS verifier accepts the result. This demonstrates the current protocol's **3-of-5 availability for `--threshold 2`**, not the requested 2-of-5 availability: upstream `signing_quorum()` still returns `2*t-1`.
- Added a regression check that the CLI power-budget calculation accepts the existing height-ten single-tree profile. The height-four conditional was already absent at takeover. No Jorts hypertree API exists in `ParallelSeededFts`; this test makes no hypertree or scalable-provisioning claim.

- Replaced CLI plaintext correlated OT and shared Beaver pad secret with independently randomized RLWE/IKNP channels, `CommittedCorrelatedOt`, and `ParallelSeededGilboaProducts`. The transport remains an in-process endpoint-bound transport; this does not provide deployment across separate custodian hosts.
- Removed the CLI's height-four and sixteen-party FTS limits and raised the RSS CLI height limit. This does not implement a hypertree: the upstream engines still eagerly construct one tree.
- HD key generation persists encrypted `hd-custodian-P.share` bundles under `cshake256-iterated-v1`. Recovery opens only selected custodians. Each bundle contains its custodian's own entropy, private inbound deliveries, and public commitments/confirmations; recovery validates/rebuilds only that custodian's local state. It contains neither other custodians' private entropy nor their inboxes. Legacy seed vaults retain their old recovery path. Normal new enrollment requires a passphrase unless `--allow-unencrypted` is explicit; deterministic fixtures retain compatibility.
- Policy-ledger partial quorums use an authoritative shared spend/replay ledger, atomically persisted with every guard before release. Guardian requirements follow the matched tier. No all-party/guardian surrogate is imposed when the tier permits a partial quorum.
- Configurable replay capacity (default 65,536, maximum 1,048,576) and preprocessing capacity (default 64, maximum 1,048,576) replace fixed replay/slot encodings. Replay records are never evicted to make room. Per-peer slot bitmaps grow with provisioning; OT preparation is batched in groups of 256 slots. CLI policy enrollment accepts `preprocessing_slots` in its policy JSON. Larger pools still require provisioning; automatic online replenishment is not implemented.
- Added `qsag_policy::macaroon`: bounded canonical 256-bit cSHAKE256 chained tags, conjunctive first-party caveats, trusted-key third-party discharges, and `CAV_BIND_TO_PARENT`. The prepared `MacaroonVerifier` authenticates each caveat on every request. Its cached root tag is a server-side minting secret. A 161-byte/three-caveat token measured 1.1–2.1 microseconds across runs (1.31 microseconds in the final policy test run) per prepared verification on the remote host; this is not a latency guarantee for arbitrary caveat/discharge counts or cold verification. A 256-bit tag is not a claim of 256-bit quantum forgery resistance.

## Compatibility

New policy storage uses CLI root v2, committee bundle PLB2, guard checkpoint V6, and shared checkpoint V2. Earlier formats fail closed. No migration tool is implemented. Existing spent amounts, nonce burns, consumed slots and trusted generation fences must be preserved by any future migration; resetting or re-enrolling a live ledger is not a safe migration.

HD's new local bundle encoding uses the current upstream 256-bit `CustodianSet` encoding. Old seed vaults are recognized separately. Quorum formats are unchanged. New ML-DSA vault metadata identifies `qsag-cred-mldsa-local-share-v1`; legacy seed-only metadata is recognized separately. Local restoration rejects incompatible protocol transcripts rather than regenerating absent custodians.

## Outstanding dependencies / decisions

1. **RSS quorum availability:** `RssKeyShare256` in `qsag-core/src/keccak_mpc.rs` has private share components and no persistence codec. `Rss256Engine::new` and `JortsSigner` require all three parties. A real active-subset protocol and authenticated share codec must be provided by the core owner, then wired into `quorum.rs`. Merely saving three seeds or rebuilding a missing custodian would not satisfy this requirement.
2. **Credentials:** ML-DSA full-committee DKG reload is replaced for new vaults by the per-party local restoration path above. `ThresholdMlDsaSignerShare` still has no direct persistence codec, and `ThresholdVerificationPack::signing_quorum()` still returns `2*t-1`; exact `t` online availability requires an upstream protocol change. TOPRF has no server codec and `Server::evaluate` requires at least four start votes plus all four holders of each input component, so it cannot evaluate with only two server files. TOPRF remains on its old full-DKG reload path. There is no `cred issue` subcommand to wire yet.
3. **HEM quorum:** `HemEpochLatchAuthority::verify_certificate` requires `floor((n+t-1)/2)+1` acknowledgements (three for 2-of-3); selecting only two files cannot honestly produce that certificate. Persisted per-party encrypted share codecs already exist, but CLI generation transactions load and rewrite all `n` files through `HemDynamicShamirQuorum::from_persisted_shares`. Detached `sign_from_shamir_share_slice` exists, but safe integration needs a subset-aware durable burn/latch transaction and reconciliation when offline custodians return. It is not safe to emulate absent latch acknowledgements or only change the file-loading loop. The current explicit rejection of unsupported HEM policy flags is preserved.
4. **Production hypertrees:** removing front-end caps does not remove upstream FTS power-count bounds or single-tree eager work. A scalable upstream hypertree/on-demand profile is still needed. Large single-tree heights have not been tested and are not a substitute.
5. **Migration:** `migrate.rs` still exposes single-witness `commit/prove/verify`. The available `CoZkCustodianShare::prove` uses a fixed three-participant outer MPC and has no active two-party protocol. A persisted active-subset prover API is needed to meet the requested threshold workflow without reconstructing a central legacy witness or simulating absent custodians.
6. **Clippy resolved on the current dependency snapshot:** `cargo clippy -p qsag-cli --all-targets --no-deps -- -D warnings` passes remotely (`cli-finish-clippy.log`). No upstream source or lint suppression was changed by `astra-cli-finish`.

## Remote validation

Current `astra-cli-finish` checks on `persvati-remote:/tmp/qsag-astra-cli`, all passing:

- `cargo test --release -p qsag-cli --test cred_persisted_custody`: encrypted non-contiguous 3-of-5 signing after deleting two custodians' files; wrong-passphrase and insufficient-quorum refusals (`cli-finish-custody-final.log`, final sources).
- `cargo test --release -p qsag-cli --bin qsag local_share_tests`: two tests for hostile/truncated local transcript encodings and abort propagation to rounds not yet created (`cli-finish-local-tests.log`).
- `cargo test --release -p qsag-cli --bin qsag power_budget_accepts_production_single_tree_height`: existing height-ten budget accepted (`cli-finish-budget-test.log`).
- `cargo test --release -p qsag-cli --test cli_smoke e2e_cred_hd_and_migrate_subcommands`: existing flags, credential signing/verification, durable replay refusal, HD recovery and legacy migration proof smoke pass (`cli-finish-smoke.log`).
- `cargo clippy -p qsag-cli --all-targets --no-deps -- -D warnings`: passes (`cli-finish-clippy.log`).

Earlier `astra-cli-policy` validation follows (its exact-Clippy failure is historical):

All builds use `/tmp/qsag-astra-cli` on `persvati-remote`, under `SWARM_MEM_MAX=16G swarm-build timeout --kill-after=10s 600s`. No local builds or Git mutations were performed by this lane.

- `cargo test --release -p qsag-policy`: 32 passed, including a 300-slot algebra test spanning the 256-slot OT batch boundary (`policy-final-default.log`).
- `cargo test --release -p qsag-policy --features std`: 33 passed (`policy-final.log`), including filesystem checkpoints.
- `cargo test --release -p qsag-cli policy_ledger::tests`: eight passed (`policy-cli-tests.log`), including guardian-free partial approval, spend/replay persistence, window rotation, and rollback refusal. The guardian-free case also passed after the final root-format change (`guardian-final.log`).
- `cargo test --release -p qsag-cli --test hd_persisted_custody`: passed (`hd-custody-test-2.log`). Encrypted 2-of-3 recovery/sign/verify with the third party file physically absent; one party is refused.
- Real OT/Gilboa test passed on final sources (`production-ot-final.log`), including chunk-boundary products and replay refusal.
- `cargo clippy -p qsag-policy -p qsag-cli --all-targets --no-deps -- -D warnings`: passed (`clippy-owned-final.log`).
- Exact Clippy failure: `clippy-exact-final.log`.
