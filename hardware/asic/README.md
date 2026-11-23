# QSAG-NI ASIC (`hardware/asic/`)

The QSAG-NI coprocessor verifies serialized proofs from SRAM. Its command port supports the autonomous QSAG-NI v2 verifier and quintic arithmetic and transcript commands.

## Autonomous QSAG-NI v2 hardware proof engine

After preloading a proof and its public descriptor, the host clears sticky status, issues `OP_VERIFY_PROOF_AUTO` (`0x50`), and reads status. Proofs larger than the resident window use `OP_PAGE_CONTINUE` (`0x51`) to resume at the requested byte offset. The three-command count excludes loading the input bytes. The earlier host-sequenced live ZK run issued 2,448,220 micro-commands (about 2.45 million) across acceptance and two rejection checks.

The RV64I verifier uses a synchronous 4,096 × 64-bit ROM. Its 25,448-byte firmware image includes the verifier, protocol constants and labels. Both instructions in a fetched word can retire consecutively. Literal reads share the same port. HQM2 verification computes `compute_message_mu` on chip from each active public key and the corresponding message. The profile-specific row program in the descriptor remains trusted verification-key material. [Command and descriptor ABI](tb/AUTO_ABI.md)

IHP SG13G2 and Sky130 HD are the manufacturable 130 nm targets (superseded academic reference runs are archived in [../../history/README.md](../../history/README.md)). Foundry tapeout signoff requires characterized memories, extracted interconnect and physical verification. [Synthesis and timing results](synth/RESULTS.md)

The formal regression checks the shared arithmetic wrapper, the Fp5 sequencer, sorted insertion and its SRAM controller, the Steiner sibling decision and the shifted-coset butterfly. Both Z3 and Bitwuzla report UNSAT for the RTL mismatch queries and SAT for each planted fault in the autonomous miters. The full proof path is exercised by Verilator. [Autonomous miters](synth/logs/auto_miter.log) · [Shared wrapper](synth/logs/miter_shared.log) · [Fp5 sequencer](synth/logs/miter_fp5.log)

## Autonomous verification results

| Proof | Bytes | Checks | Resident cycles | Paged cycles | Page refills |
|---|---:|---:|---:|---:|---:|
| QSAGZKH2 | 258,104 | 107 | [54,906,892](synth/logs/auto_zk.log) | [54,954,704](synth/logs/auto_paged.log) | 7 |
| QSAGHQM2, one signer | 307,531 | 107 | [89,630,744](synth/logs/auto_hqm.log) | [89,673,674](synth/logs/auto_hqm_paged.log) | 9 |
| QSAGHQM2, multiple signers | 331,221 | 108 | [94,421,702](synth/logs/auto_multi.log) | [94,472,574](synth/logs/auto_multi_paged.log) | 10 |

The RTL rejected all 288 distinct proof-bit flips in the QSAGZKH2 manifest and all 300 in the single-signer QSAGHQM2 manifest. Separate tests rejected a noncanonical field, truncated and extended proofs, a changed message byte, and a changed committee key. The paged runs used 4,096-word windows. [QSAGZKH2 campaign](synth/logs/auto_zk.log) · [QSAGHQM2 fields](synth/logs/auto_hqm_fields.log) · [Message](synth/logs/tamper_message.log) · [Committee](synth/logs/tamper_committee.log)

## Quintic command datapath

The Goldilocks extension uses five coefficients with $X^5=3$. Commands `0x28` through `0x2b` perform multiply-add, Horner evaluation, folding, and sumcheck. The sequencer takes one base product at a time from lane zero. `GLMUL` uses that lane directly. Poseidon2-12 schedules its twelve S-boxes across nine multipliers in groups of nine and three. Canopy uses four feed-forward adders. Keccak-p, TurboSHAKE256, and the polynomial and tower GF(2¹²⁸) multipliers have dedicated commands. The seven retired opcode values take the default sticky-failure path. [Command decoder](rtl/qsag_ni_asic_top.sv)

## Foundry measurements

| Library | AUTO_VERIFY=0 (kGE) | AUTO_VERIFY=1 (kGE) | Engine (kGE) | ROM (kGE) |
|---|---:|---:|---:|---:|
| IHP SG13G2 | 660.996 | 709.610 | 22.994 | 21.068 |
| Sky130 HD | 734.229 | 784.540 | 24.718 | 21.957 |

With autonomous verification enabled, the typical-corner minimum periods are 505.88 ns on IHP and 694.02 ns on Sky130 HD. The area excludes the four SRAM macros. These are unbuffered pre-layout timing estimates. [All corners and both configurations](synth/RESULTS.md)

## Reproducing the checks

From this directory on the build host, `bash tb/verify_auto.sh lint bram command formal` runs the leaf, command-port, inference, and formal gates. `bash tb/run.sh tb_auto_v2` builds the autonomous bench and runs the proof and mutation campaigns with the supplied fixtures. `bash tb/verify_auto.sh foundry` reproduces the foundry table. The Rust fixture sources and the committed mutation manifests describe the proof bytes and flip positions. [Autonomous ABI](tb/AUTO_ABI.md)
