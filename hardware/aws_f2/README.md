# QSAG on AWS F2

Two stateful QSAG-NI v2 engines and three ASS2-0P5 pad interfaces share an AppPF. Each NI has 512 KiB of private operand SRAM. Each ASS2 has its own Dregg-64 core, resident ROM, I-SRAM, D-SRAM and 32 KiB SPI anchor. BAR0 has no address for an ASS2 memory or key register. Software holding the AppPF can issue commands to all five engines.

**The HDK image is for NI and public enclave bring-up.** It exposes full NI verification, READ_DIAG and IDENT. The full-system cosim exercises custody commands with three independent deterministic PUF and TRNG fixtures. The physical ASS2 design relies on ring oscillators. A cloud-compatible source of signing roots and fresh entropy still needs qualification. The HDK build disables the oscillators and returns resident error 17 for custody operations. Capability bit 31 advertises this configuration. AWS documents the combinatorial-loop restriction, and its small shell exposes PCIS through BAR4. [AWS design-rule guidance](https://repost.aws/questions/QUg7tZgBpDSrS-XjbUxIZIHA/error-drc-lutlp-1-combinatorial-loop-alert-2-lut-cells-form-a-combinat) · [F2 shell specification](https://github.com/aws/aws-fpga/blob/c34f88e97eaf8a9b6ea7a3516ab65ee64690ab82/hdk/docs/AWS_Shell_Interface_Specification.md)

## Build and load

Use the F2 developer environment with the Vivado version supported by your HDK. Staging was checked against aws-fpga F2 release 2.3.5, commit `c34f88e97eaf8a9b6ea7a3516ab65ee64690ab82`. The HDK owns shell checkpoint retrieval, DDR pin termination, synthesis, partition linking, placement, routing and manifest generation. The scripts target `xcvu47p-fsvh2892-2-e`. See the project report for the gates actually completed. [AWS setup](https://github.com/aws/aws-fpga/blob/f2/hdk/README.md) · [Verification report](../../REPORT.md)

```sh
# Set PKG to this hardware/aws_f2 directory, then from the AWS checkout:
source hdk_setup.sh
"$PKG/build/scripts/stage_to_aws_hdk.sh"
export CL_DIR="$HDK_DIR/cl/examples/cl_qsag_f2"
"$CL_DIR/build/scripts/build_dcp.sh"
```

The final line of a successful build gives the specific Developer_CL tarball. The wrapper checks for a routed checkpoint with passing HDK timing. To register that artifact, supply a bucket in your F2 region and retain both IDs returned by EC2.

```sh
"$CL_DIR/build/scripts/submit_afi.sh" "$DCP_TAR" "$S3_BUCKET" "$AWS_REGION"
aws ec2 describe-fpga-images --region "$AWS_REGION" --fpga-image-ids "$AFI"
# After State.Code becomes available, on the F2 instance:
sudo fpga-load-local-image -S 0 -I "$AGFI"
sudo fpga-describe-local-image -S 0 -R -H
```

The stand-alone top uses the requested raw ID words `1d0f_f201` and `5153_4147`. The HDK wrapper and AFI manifest use `f021_1d0f` and `5153_4147`. The AWS field layout puts the PCI vendor in bits 15–0 and reserves F000–F0FF for customer device IDs using vendor 1D0F. [HDK PCI ID rules](https://github.com/aws/aws-fpga/blob/f2/hdk/README.md#afi-pcie-ids)

## Host access

Apply `rust-overlay/crates/qsag-accel` to the matching `qsag-main-staging` workspace. The normal Cargo package remains `qsag-accel`. All transport-independent code builds with `alloc`. Linux I/O requires `std`.

On F2, pass the **application** PF sysfs directory from the slot description. The SDK maps the uncached resource0 and resource4 windows. It writes descriptors through byte-strobed BAR4 stores and publishes up to 256 commands with one BAR0 doorbell. Keep one process in control of an AppPF. The smoke example reads every engine and vat.

```sh
cargo run -p qsag-accel --features std --example aws_f2_smoke -- "$APP_PF_SYSFS"
```

`aws_f2::linux::Xdma::open(0)` uses positioned 32-bit BAR0 I/O and 64-byte-aligned DMA buffers on compatible drivers providing `/dev/xdma0_user`, `/dev/xdma0_h2c_0` and `/dev/xdma0_c2h_0`. AWS lists XDMA engine features as unsupported on F2. The BAR4 adapter avoids that dependency. [AWS DMA example](https://github.com/aws/aws-fpga/blob/f2/hdk/cl/examples/cl_dram_hbm_dma/README.md)

```rust
use qsag_accel::aws_f2::{AwsF2Backend, Bar0Pcis, F2Error, NiCmd, VerifyStatus};

fn check<T: Bar0Pcis>(device: &mut AwsF2Backend<T>, proof_words: &[u64],
                       commands: &[NiCmd]) -> Result<VerifyStatus, F2Error<T::Error>> {
    let mut ni = device.ni(0)?;
    ni.upload_words(0, proof_words)?;
    ni.command(NiCmd { op: 8, idx: 1, ..NiCmd::default() })?; // clear sticky status
    ni.stream(commands)?;
    ni.status()
}
```

Check both the pass flag and the verifier program's expected check count. `stream` packs lanes in increasing order, pads a trailing partial beat with RD_STATUS, and waits for the exact retirement count, including padding. A transport failure during a stateful command can leave its execution outcome unknown. Reconcile the NI counters or the vat's authenticated generation before replaying.

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
| 0x28 | RW | Write 1 to zeroize when DMA is idle. Read bit 0 until clear |

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

External reset and FLR immediately close command admission. A 15-bit counter drives parallel erasure of the NI SRAMs, descriptor memories, all three 32 KiB anchors (erased value FF) and both 512-byte SRAMs in each vat. FLR_DONE follows the 32,768-cycle sweep, about 131 µs at 250 MHz. The lock remains asserted while FLR is held. After release, the firmware's startup scrub runs before HOST_RDY. These BRAM anchors preserve records across local chip reset and lose them on global erasure or FPGA reconfiguration. Durable anti-rollback across AFI reloads requires a separate persistent trust anchor.

## Reproduce the gates on Linux

The tested environment, oracle provenance, utilization and remaining hardware qualification are in the [report](../../REPORT.md). `BUILD_DIR` must be an absolute temporary path per build. The full-system C++ harness needs OpenSSL development headers and libcrypto.

```sh
cd hardware/aws_f2
verif/run.sh lint
BUILD_DIR="$PWD/build-sim" verif/run.sh
BUILD_DIR="$PWD/build-hdk-sim" verif/run_hdk.sh  # HDK_SHELL_DIR from hdk_setup.sh
BUILD_DIR="$PWD/build-xcup" verif/synth_xcup.sh  # sv2v and OSS CAD Suite on PATH
```

From the overlaid Cargo workspace, point the SDK integration test at the full-system executable built above. This test starts the executable as a subprocess and drives both buses through its transaction interface.

```sh
RUSTFLAGS="-D warnings" cargo test -p qsag-accel --features std
RUSTFLAGS="-D warnings" cargo test -p qsag-accel --no-default-features --features alloc --lib
QSAG_F2_SIM="$PKG/build-sim/Vcl_qsag_f2_top" RUSTFLAGS="-D warnings" \
  cargo test -p qsag-accel --features std --test aws_f2_cosim -- --ignored
```

The timing file describes the 250 MHz primary clock, a related 125 MHz enclave clock, synchronizers and both phase alignments of the gated HOST_SCK clocks. The small-shell placement file favors SLR1 for NI and SLR2 for the vats. Its PCIS interface is physically in SLR1. A placement experiment in SLR0 needs a pipeline across that boundary. Hard child pblocks must stay inside the shell's irregular `pblock_CL` ranges. [AWS F2 floorplan](https://awsdocs-fpga-f2.readthedocs-hosted.com/latest/hdk/docs/shell-floorplan.html)
