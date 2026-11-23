# ASS2 architectural cosimulation

On a Linux host, run `bash sim/run_cosim.sh` from the ASS2 directory. It runs the Python known-answer tests, generates 1,024 seeded programs plus four firmware cases, lints the enclave, builds the core with Verilator, and checks each instruction boundary. The simulated bus has an 8 KiB synchronous SRAM, registered read data and eight byte-write strobes. Each program starts from reset. A retire or trap pulse ends a step, regardless of the number of physical clocks it took.

To retain the corpus and replay the same instructions through the Rust VM, run the following on a Linux host. Set `ASS2_CRATE` to the full workspace's `crates/qsag-ass2` directory when the simulation tree is staged separately.

```bash
python3 sim/gen_cosim_vectors.py suite.vec \
  --firmware sim/firmware_kats/canopy.bin --firmware sim/firmware_kats/cth.bin \
  --firmware sim/firmware_kats/jive.bin --firmware sim/firmware_kats/sumcheck.bin
bash sim/run_cosim.sh suite.vec
bash sim/run_vm_check.sh suite.vec
```

The generator defaults to seed `0x41535332`. Each case has its own PRNG stream. Directed prefixes and terminations guarantee coverage of shift boundaries, all 16 comparison predicates, all permutation variants, aliased JALR and wide-field writes, counter overrides, enabled and disabled exceptions, ERET, and byte and word memory operations. Its header records the interpretation used for details left open in the canonical spec. Hardware faults take one architectural cycle and retire zero instructions. CSR counter reads see their pre-instruction values. Invalid CSR accesses trap.

## Replay format

The first line is `ASS2-V1 <decimal case count>`. All instruction and state numbers below are hexadecimal. Memory strings contain consecutive bytes in ascending address order.

| Record | Fields |
|---|---|
| CASE | Case name and memory size in bytes. Reset PC is zero. |
| LOAD | Byte address and initial byte string. Unspecified SRAM starts at zero. |
| STEP | Pre-PC, instruction, trap cause (zero for normal retirement), post-PC, halted, ECAUSE, INSTRET, CYCLES, 16 GPRs, 25 sponge lanes, store byte count and address/value pairs. A fetch fault records instruction zero. |
| END | Complete final SRAM byte string. The preceding STEP contains the final architectural state. |

The Python model checks both Poseidon permutation widths against their full sequence vectors. Its separate width-24 Jive test checks the seven Merkle digest limbs after feed-forward. The Fp5 known-answer test multiplies into the second source and checks all five result limbs. Keccak uses independent SHAKE256 and TurboSHAKE256 digest checks.

## Firmware inputs

The four small flat SRAM images include executable code and populated test mailboxes captured before execution from the `qsag-ass2` `firmware_kat.rs` public test vectors. They exercise the depth-four Canopy proof at leaf index 3, the dual-MAC/WOTS case at layer 13 and digit 1, the seven-limb Jive compression with tweaks 100 and 200, and the first deterministic sumcheck transcript. All four finish with R4 equal to one. Use additional `--firmware` arguments for other flat images.

## Recorded run

The 1,024 random programs completed 97,389 architectural steps. The four firmware images added 1,435. Verilator and the independent Rust VM each agreed with the model on all 98,824 steps, including PC, both register banks, trap status, counters and SRAM. Vector SHA-256 with the image order above is `29a41a0354d5f1f8fe33bc42f8b5bba2c236a6e4ad3b98ba167dcb2baf1eefa1`. The random-only SHA-256 is `a5d65e1ee887db7873ef18f9687ec284907af46ceed747e62cbde6f3fb899e72`.

A negative control changed the expected hardwired R0 to one after the first instruction. The Verilator checker stopped on that instruction and reported the expected and actual values.
