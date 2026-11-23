# QSAG on AWS F2

Two stateful QSAG-NI v2 engines and three ASS2-0P5 pad interfaces share an AppPF. Each NI has 512 KiB of private operand SRAM. Each ASS2 has its own Dregg-64 core, resident ROM, I-SRAM, D-SRAM and 32 KiB SPI anchor. BAR0 has no address for an ASS2 memory or key register. Software holding the AppPF can issue commands to all five engines.

**AWS deployment blocker.** AWS restricts both DNA_PORT and SYSMON in F2 customer logic. This design instantiates `DNA_PORTE2` and `SYSMONE4` for UltraScale+ synthesis and simulation. Deploying an AFI requires AWS-supported sources for device identity and private entropy. Loop checks and a successful HDK-wrapper simulation alone cannot establish AFI eligibility. [AWS AFI validation rules](https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/hdk/docs/AWS-CLI-FPGA-Commands.html)

The three vats run the ASS2-0P5 Rev 2.0 resident ROM. Each derives a private seal key and BCH response inside the FPGA. The host supplies the owner's public key at enrollment and signs lifecycle commands with one-time owner keys. Knowledge of the optional BAR seed alone is insufficient to derive either vat secret.

## HDK interface

The synthesizable wrapper is `design/cl_qsag_f2.sv`. Set `HDK_SHELL_DIR` to use the HDK small-shell port definitions and DDR stub. The fallback in `verif/hdk_stub/` contains the Apache-2.0 AWS interface files from commit `c34f88e97eaf8a9b6ea7a3516ab65ee64690ab82`. Both simulation paths exercise the same custody RTL. The DDR stub serves interface elaboration. Shell checkpoint linking, timing closure and hardware execution require separate evidence. [Pinned AWS shell interfaces](https://github.com/aws/aws-fpga/tree/c34f88e97eaf8a9b6ea7a3516ab65ee64690ab82/hdk/common/shell_stable/design/interfaces)

The stand-alone top uses the requested raw ID words `1d0f_f201` and `5153_4147`. The HDK wrapper and AFI manifest use `f021_1d0f` and `5153_4147`. The AWS field layout puts the PCI vendor in bits 15–0 and reserves F000–F0FF for customer device IDs using vendor 1D0F. [HDK PCI ID rules](https://github.com/aws/aws-fpga/blob/f2/hdk/README.md#afi-pcie-ids)

## Host access

The driver lives in the workspace package `crates/qsag-accel`. All transport-independent code builds with `alloc`. Linux I/O requires `std`.

On F2, pass the **application** PF sysfs directory from the slot description. The SDK maps the uncached resource0 and resource4 windows. It writes descriptors through byte-strobed BAR4 stores and publishes up to 256 commands with one BAR0 doorbell. Keep one process in control of an AppPF. The smoke example reads every engine and vat.

```sh
cargo run -p qsag-accel --features std --example aws_f2_smoke -- "$APP_PF_SYSFS"
```

`aws_f2::linux::Xdma::open(0)` uses positioned 32-bit BAR0 I/O and 64-byte-aligned DMA buffers on compatible drivers providing `/dev/xdma0_user`, `/dev/xdma0_h2c_0` and `/dev/xdma0_c2h_0`. AWS lists XDMA engine features as unsupported on F2. The BAR4 adapter avoids that dependency. [AWS DMA example](https://github.com/aws/aws-fpga/blob/f2/hdk/cl/examples/cl_dram_hbm_dma/README.md)

```rust
use qsag_accel::aws_f2::{AwsF2Backend, Bar0Pcis, F2Error, VerifyStatus};

fn check_auto<T: Bar0Pcis>(
    device: &mut AwsF2Backend<T>,
    descriptor: &[u8],
    proof: &[u8],
) -> Result<VerifyStatus, F2Error<T::Error>> {
    // Uploads the 258,104-byte QSAGZKH2 proof + public ZKD1/HQD1 statement over PCIS DMA,
    // clears sticky status, and runs autonomous hardware verification via 1 OP_VERIFY_PROOF_AUTO (0x50)
    // command (or paged 0x50/0x51 windowing when window_words >= 2).
    device.ni(0)?.verify_proof_auto(descriptor, proof, 0)
}
```

Both the autonomous `OP_VERIFY_PROOF_AUTO` (`0x50`) / `OP_PAGE_CONTINUE` (`0x51`) path (backed by the synchronous 32 KiB `RAMB36E2` verifier ROM and on-chip `compute_message_mu`) and the micro-command `stream` path (including `GLMUL` at `0x23` and the four Fp5 operations at `0x28..0x2b`) are supported on every NI engine. Check both the pass flag and the verifier program's expected check count (`107` for canonical `QSAGZKH2` / single-signer `QSAGHQM2`). `stream` packs lanes in increasing order, pads a trailing partial beat with RD_STATUS, and waits for the exact retirement count, including padding. A transport failure during a stateful command can leave its execution outcome unknown. Reconcile the NI counters or the vat's authenticated generation before replaying.

## BAR0 register map

All offsets are byte addresses. OCL accepts AW and W independently. Each CSR write requires a complete, aligned 32-bit word. Unsupported addresses and rejected operations return SLVERR. Integers and command lanes are little-endian.

| Global offset | Access | Meaning |
|---|---|---|
| 0x00, 0x04 | R | Magic 0x51534147 and ABI 0x00020000 |
| 0x08 | R | NI engine count, 1–4 |
| 0x0C | R | Bits 7–0 commands per beat, 15–8 vat count, 16 locked, 31 diagnostics-only image |
| 0x10, 0x14 | RW | Staged descriptor BAR4 byte address and count in 64-byte beats, 1–256 |
| 0x18 | W | Write 1 to start an idle engine at the staged base. Descriptor indices wrap modulo 256 |
| 0x1C | R | Sum of all 32-bit NI retirement counters modulo 2³² |
| 0x20, 0x24 | R | Main clock counter, low and high. Read high/low/high and retry on rollover |
| 0x28 | RW | Write 1 to zeroize when DMA is idle. Poll bit 0 through the scrub and key setup |
| 0x2C | R | Monotonic 32-bit scrub generation counter (advances on software zeroize and FLR; verified by `AwsF2Backend::zeroize()`) |
| 0x30–0x4C | W | Seed words 0–7, little-endian. Reads return zero with SLVERR |
| 0x50 | W | Write 1 to commit all eight words. Partial commits, repeated commits and provisioning after vat use return SLVERR |
| 0x54 | R | Bit 0 healthy and keys ready, 1 RCT failure, 2 APT failure, 3 fresh temperature telemetry, 4 host seed committed, bits 31–16 commit count since wipe |

Each NI uses BAR0 base `0x1000 * (engine + 1)`.

| NI offset | Access | Meaning |
|---|---|---|
| 0x00, 0x04 | W | Command data low and high |
| 0x08 | W | Address 15–0, index 20–16, opcode 28–21 |
| 0x0C | W | Write 1 to issue while idle |
| 0x10 | R | Bit 0 drained, bit 1 sticky failure, bit 2 stream credit available, bits 17–9 free descriptor slots |
| 0x14 | R | Verification check count |
| 0x18, 0x1C | R | Latest retired response, low and high |
| 0x20 | R | Retired commands modulo 2³² |

Each vat uses BAR0 base `0x10000 * (vat + 1)` for vat 0, 1 or 2.

| Vat offset | Access | Meaning |
|---|---|---|
| 0x00 | RW | Bit 0 selects chip, bit 1 asserts local reset, bit 2 asserts local tamper |
| 0x04 | W | Transfer byte in bits 7–0, width in bits 9–8 (0 SPI, 1 quad, 2 octal) |
| 0x08 | R | Bits 0–5 are transfer busy, HOST_RDY, HOST_IRQ, VERIFY, FAULT and local tamper input |
| 0x0C | R | Sampled byte from last transfer, valid until another transfer or CS change |

Hold CS throughout each frame. Send the prefix on DQ0 in SPI mode, then use the selected payload width. Read prefixes require eight dummy single-lane clocks. READ_DIAG shifts its 64 bits MSB first on DQ1. Normal headers and response words are little-endian. Local reset preserves the private SPI anchor. The SDK handles these details for arbitrary resident commands, authenticated LOAD_CODE and per-party CTH requests. `cth_sign_three` returns three independent outcomes because each accepted authorization advances that vat's generation. The resident command emits an authorized WOTS chain element.

VLED bits 0, 1, 2 and 3 are any vat verify, any NI busy, any NI sticky fail and global lock. Bits 6–4 are vat verify, 9–7 vat fault and 12–10 local tamper assertion.

## BAR4 and reset

Engine `i` owns byte base `i << 20`. All SRAM transfers access the same operands as NI WR_MEM and RD_MEM. A full beat transfers eight consecutive little-endian 64-bit words across eight parallel RAM banks. Byte strobes control individual bytes.

| Offset within engine | Access | Contents |
|---|---|---|
| 0x00000–0x7FFFF | RW | 65,536 NI words |
| 0x80000–0x83FFF | W | 256 staged descriptors for the BAR0 doorbell |
| 0xC0000–0xCFFFF | W | Direct stream. Each full-strobe beat enqueues four commands |

Each 128-bit lane stores data in bits 63–0, address in 79–64, index in 84–80 and opcode in 92–85. Write zero in bits 127–93. The issue queue respects NI ready on every lane. It reserves capacity at AW acceptance and rejects a burst that exceeds the available credit. SRAM and staging transfers require a drained engine. The SRAM read channel can issue a beat every clock and holds its output through backpressure.

PCIS echoes all 16 shell ID bits. It accepts INCR with AxSIZE 6, one outstanding burst at a time, and checks the entire 8-bit AxLEN. At 64 bytes per beat, AXI's 4 KiB boundary limits a legal page-aligned burst to 64 beats. An illegal 256-beat request is drained or answered for its announced length with SLVERR. Single-beat dword BAR4 accesses use the shell's lane strobes.

External reset and FLR immediately close command admission. A 15-bit counter drives parallel erasure of the NI SRAMs, descriptor memories, all three 32 KiB anchors (erased value FF) and both 512-byte SRAMs in each vat. FLR_DONE follows the 32,768-cycle sweep, about 131 µs at 250 MHz. The lock remains asserted while FLR is held. After release, the firmware's startup scrub runs before HOST_RDY. Because both `fpga_ephem_secret` (which mixes hardware `DNA_PORTE2` + boot/post-scrub `SYSMON`/jitter entropy into `fram_seal_key[vat]`) and the emulated 32 KiB FRAM BRAMs are session-ephemeral inside the FPGA fabric, `fram_seal_key` provides hardware-isolated per-AFI-session sealing: sealed records survive local vat resets (`ctl = 2`) within a live session, and are cryptographically invalidated and wiped on `zeroize()`, `FLR`, `rst_main_n`, or FPGA AFI reload (never claiming non-volatile persistence across AFI reloads). Durable anti-rollback across AFI reloads requires an external persistent trust anchor (such as AWS Nitro/KMS monotonic state).

## Clocking and custody

The shell clock drives `BUFGCE_DIV` with divide by two. The main and vat clocks are related. With a 4 ns primary clock constraint, Vivado automatically derives the 8 ns clock at the buffer output. Leave the paths between these two clocks timed. Local reset asserts asynchronously and releases through two vat-clock registers. The serial receiver detects SCK transitions on the vat clock. CS, SCK and DQ pass through two vat registers and each half-bit lasts eight vat clocks. The reverse path registers DQ with its output enable at the source and synchronizes it twice before the host samples it. The FRAM pins and status levels also pass through two stages. A synchronized erase level starts a local 9-bit address counter in each vat. The simulation monitor checks that both SRAMs in every vat receive zero writes at all 512 addresses. [Vivado generated clocks](https://docs.amd.com/r/en-US/ug903-vivado-using-constraints/Automatically-Derived-Clocks)

The collector records all ten OCL and PCIS ready/valid handshakes, including simultaneous channel events, and mixes the elapsed main-clock cycles, related-clock timestamp and fresh ADC codes into an unkeyed 256-bit register. Temperature, VCCINT and VCCAUX reads follow end-of-conversion and DRP ready. Only a new temperature conversion supplies a health-test sample (bit 6, the low bit of the 10-bit code). The main and derived clocks share a source. Their digital phase relationship does not establish independent entropy.

The ADC holds each conversion, its channel flag and timestamp until the next DRDY. A three-stage toggle synchronizer qualifies one bundled capture. A separate source-registered 16-bit Gray timestamp crosses two destination flops before decoding on a bus event. The DNA readout uses the 125 MHz clock to meet the DNA-port frequency limit. It loads the serial register, samples 96 bits LSB first, then signals completion on cycle 98. The main clock latches the held identifier after a two-stage ready synchronizer. Device DNA can also be read over physical JTAG. BAR0 and PCIS have no mapping for it. [AMD DNA read protocol](https://docs.amd.com/r/en-US/ug570-ultrascale-configuration/Identifier-Value-and-Operation) · [Virtex UltraScale+ timing limits](https://docs.amd.com/r/en-US/ds923-virtex-ultrascale-plus/Configuration-Switching-Characteristics)

RCT trips on the 40th identical sample. APT trips on the 820th occurrence of the first symbol in a non-overlapping 1,024-sample window. Hardware holds vat reset through initial qualification. A missing temperature source drops readiness, and test failures latch until external reset. The simulator supplies deterministic DRP conversions at an accelerated cadence. It completes the full 1,024-sample window during startup erase. On silicon, conversion rate determines the warmup time. Collecting 1,024 fresh temperature measurements in 131 µs would require about 7.8 million temperature conversions per second. Physical source characterization, min-entropy assessment, FIPS 140-3 validation and DO-254 assurance evidence remain outstanding. [AMD System Monitor guide](https://www.amd.com/content/dam/xilinx/support/documents/user_guides/ug580-ultrascale-sysmon.pdf) · [NIST SP 800-90B](https://csrc.nist.gov/pubs/sp/800/90/b/final)

Once DNA and thermal qualification are ready and the global lock has released, the anchor hashes ASCII `QSAG.F2.EPHEM/v2`, 12 DNA bytes, 32 collector bytes and four main-clock counter bytes into a private 32-byte wrapping secret. All integers are little-endian. The hash uses TurboSHAKE256 with domain byte 0x1F. The six subsequent jobs each hash a label (`QSAG.F2.PUF_KDF/v2` or `QSAG.F2.FRAM_KDF/v2`), one vat-ID byte, 32 master bytes, 12 DNA bytes and the wrapping secret. A zero master selects the unseeded epoch. The vat response uses 64 output bytes and the FRAM key uses 32. On F2 the BCH engine combines these private response bits with deterministic margin measurements for enrollment and reconstruction. Only after all six jobs finish can the vats leave reset. Periodic XOF output supplies three 64-bit nonce lanes and a separate 256-bit private ratchet. [RFC 9861](https://www.rfc-editor.org/rfc/rfc9861.html)

To provision a host seed, call `zeroize()` and `inject_nitro_seed(&seed)` before selecting a vat. Commit retains the private wrapping secret, clears the staging words and regenerates all six outputs with the new master. Global reset, zeroize and FLR clear the master, wrapping secret, derived keys and ratchet. Each fresh wrapping secret depends on the new collection window. Its unpredictability on silicon depends on private physical entropy. The deterministic simulation model exercises the protocol and cannot establish that entropy bound.

The host handles Nitro attestation and KMS policy. BAR0 transports the seed in plaintext. A process with AppPF control can erase the device and claim a blank vat. A local vat reset preserves the global private material and sealed FRAM so BOOT can recover the existing owner and generation.

### Owner ceremony

| Command | Authorization and result |
|---|---|
| BOOT (0x10) | A virgin vat reports `LC_BLANK = 1`. A committed vat reconstructs the root with its BCH helpers, checks the journal and returns the recovered generation and public enclave ID. |
| ENROL (0x11) | Supply the 32-byte initial owner public key. The 160-byte response contains a 16-byte nonce followed by the 32-byte enclave ID. |
| COMMIT / LEASE / GATE (0x12 / 0x15 / 0x16) | Each 320-byte owner frame binds the operation, public identity transcript, nonce, record, capability and next WOTS+C public key. LEASE and GATE advance the journal. |
| LOAD_CODE (0x30) | Flag 1 authenticates an image against the installed code capability. Flag 2 carries an inline owner proof and advances the record. Both the SDK and RTL accept inline loads through 812 bytes. |
| CTH_SIGN (0x20) | Supply a 120-byte request with the CTH capability token and GF(2¹²⁸) dual-MAC. For base-4 digit 2, one public Poseidon2-12 compression verifies the returned element against its endpoint. |

The reproducible test owner reuses its initial public key across both epochs and all vats to make identity comparisons meaningful. Production owners must use each WOTS signing key for one message across all devices and epochs. Test seeds in `verif/owner_fixture.hpp` belong only to the test owner.

FRAM stores a written flag alongside each ciphertext byte. A separate keyed TurboSHAKE256 invocation over ASCII `QF2.PAD1`, the vat's 32-byte FRAM key and the high eight address bits generates a 128-byte pad. The low seven address bits select the pad byte. Sequential SPI prefetch handles block boundaries and the 15-bit address wrap. Global erase overwrites the full array and clears validity. Local reset drops cached pads and preserves the ciphertext. The mask repeats for rewrites to the same address under the same key. Multiple snapshots expose plaintext differences, and the storage layer alone provides neither integrity nor rollback protection.

## Reproduce the gates

Run these commands in the project checkout on a Linux x86_64 host. The C++ tests use the same RTL and SPI protocol through the standalone top and the HDK wrapper. The SDK test uses one simulator process with three clients, one per vat. Its owner helper runs separately and accepts only public transcript words.

```sh
set -euo pipefail
cd "${QSAG_REPO_DIR:-/home/build/qsag}"
export TMPDIR="$PWD/work_tmp"
mkdir -p "$TMPDIR"
export CARGO_TARGET_DIR="$TMPDIR/cargo-target" CARGO_BUILD_JOBS=6 JOBS=6
export PATH="${OSS_CAD_BIN:-/opt/oss-cad-suite/bin}:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
logs="$PWD/hardware/aws_f2/verif/logs"
mkdir -p "$logs"
(
  cd hardware/aws_f2
  bash verif/run.sh lint 2>&1 | tee "$logs/lint.log"
  bash verif/run_hdk.sh lint 2>&1 | tee "$logs/lint-hdk.log"
  BUILD_DIR="$TMPDIR/anchor" bash verif/run_anchor.sh 2>&1 | tee "$logs/anchor.log"
  BUILD_DIR="$TMPDIR/top" bash verif/run.sh 2>&1 | tee "$logs/ceremony-top.log"
  BUILD_DIR="$TMPDIR/hdk" bash verif/run_hdk.sh 2>&1 | tee "$logs/ceremony-hdk.log"
  BUILD_DIR="$TMPDIR/xcup" bash verif/synth_xcup.sh
  cat "$TMPDIR/xcup/"cl_qsag_f2{_top,}.log | gzip -c > "$logs/xcup.log.gz"
  cp "$TMPDIR/xcup/cl_qsag_f2_top.stat.json" "$logs/xcup-stat.json"
  cp "$TMPDIR/xcup/cl_qsag_f2.stat.json" "$logs/xcup-hdk-stat.json"
)
cargo test -p qsag-accel 2>&1 | tee "$logs/cargo.log"
QSAG_F2_SIM="$TMPDIR/top/Vcl_qsag_f2_top" cargo test -p qsag-accel \
  --test aws_f2_cosim -- --ignored --nocapture 2>&1 | tee "$logs/cosim.log"
```

The RTL and headers in `design/ni/` mirror the ASIC sources. F2 builds define `QSAG_F2_NI` to select the DSP multiplier and the PCIS-accessible SRAM and page-status ports. The lint configuration covers all four NI counts and the HDK interface stub. The XCUP gate uses Slang, checks the flattened design for combinational loops before mapping, requires the native DNA, SYSMON, clock-divider and block-RAM cells, then repeats the loop check on mapped LUT logic. Remove `SYNTH_TOPS` to map both tops. See `verif/logs/` for the Rev 2.0 run. Earlier evidence in `verif/results/` predates private epoch keys.

## Quintic NI mapping

The two-engine XCUP maps include the three ASS2 vats. Each mapped top contains one BUFGCE_DIV, one DNA_PORTE2 and one SYSMONE4. LUT counts sum the LUT1 through LUT6 primitive instances. SCC counts come from flattening before mapping and again after expanding the mapped LUT logic. [Standalone statistics](verif/logs/xcup-stat.json) · [HDK statistics](verif/logs/xcup-hdk-stat.json) · [Yosys logs](verif/logs/xcup.log.gz)

| Top | LUT1–6 | DSP48E2 | RAMB36E2 | SCCs before / after mapping |
|---|---:|---:|---:|---:|
| `cl_qsag_f2_top` | 314,025 | 290 | 315 | 0 / 0 |
| `cl_qsag_f2` | 314,047 | 290 | 315 | 0 / 0 |
