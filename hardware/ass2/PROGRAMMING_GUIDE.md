# ASS2-0P5 / Dregg-64 programming guide · Rev. 2.0

ASS2 (`ASS2-0P5`) fetches 32-bit little-endian instructions and operates on 64-bit little-endian words inside the 56-pad `wafer.space` GF180MCU `SLOT_0P5X0P5` (`1,936 × 2,531 µm` die, `[442, 442]..[1494, 2089]` = `1,732,644 µm²` core). This guide describes the unmuxed 56-pad (`48` signal/analog + `8` supply) interface, the Zero-Factory-Trust post-quantum `WOTS+C` resident ROM protocol, the 514-ring physical PUF/TRNG subsystem, and the architectural cycle model. The four callable leaf routines below run on the bundled documentation VM. Each listing shows a byte PC, the instruction word in numeric order, and the corresponding source line. For example, the word `0xf0c00000` occupies memory as `00 00 c0 f0`.

## Assemble and run

From the directory containing `hardware/` and `build/`, run the following commands. The first reassembles all four examples, compares them byte-for-byte with the shipped listings, and checks arithmetic results, encoding, timing and secret-dependent addressing. The second compares the checked listings with both documents. The Rust program exercises the host frame format with an in-memory SPI fixture.

```sh
python3 -B hardware/ass2/tools/check_examples.py
python3 -B hardware/ass2/tools/sync_listings.py build/listings --check
rustc --edition 2021 hardware/ass2/examples/host_driver.rs -o build/rust/host_driver
build/rust/host_driver
```

To assemble a flat image, import `assemble` from `tools/ass2_ref.py`. Its return values are image bytes, byte addresses by label, and per-source-line encodings. A callable leaf requires a public aligned return address in `RA`. A command-entry image must supply its own entry code, establish the arguments and stack, call its leaf, release its allowed result and terminate. The following assembles a minimal terminating command.

```python
import sys
sys.path.insert(0, "hardware/ass2/tools")
from ass2_ref import assemble
image, labels, listing = assemble("ZEROIZE\nHALT")
assert image.hex() == "0000040000000500"
```

### Registers and calls

| Register | ABI | Contract |
|---|---|---|
| PC | dedicated | 64-bit byte address, aligned to 4. Normal fall-through adds 4. |
| R0 | ZERO | Reads as zero. Writes discard the result. Memory accesses and traps still happen. |
| R1 | SP | Downward-growing stack. Keep 8-byte alignment and reserve disjoint writable data SRAM. |
| R2 | FP | Frame pointer. Preserve the caller’s frame when establishing a new one. |
| R3 | RA | Link register. A non-leaf saves its incoming RA before another call. |
| R4–R9 | A0–A5 | Arguments and results, caller-saved. |
| R10–R15 | T0–T5 | Callee-saved, including when used as arithmetic temporaries. |
| S0–S24 | shared lanes | Each routine declares the lanes it uses or clears. Overlaid names alias immediately. |

`CALL f` expands to `JAL RA,f`, `J label` to `JAL ZERO,label`, and `RET` to `JALR ZERO,RA,0`. Labels denote byte addresses. A numeric BR/JAL displacement counts instructions from the *following* instruction. A numeric JALR displacement counts words of four bytes from the register base. Memory syntax `[base±offset]` always uses **bytes**. The assembler scales aligned offsets to fit the encoded field. Labels end in a colon. The assembler accepts ABI or R-register names, lane syntax `S[i]`, field names `E0..E4` and `P0..P11`, decimal and hexadecimal immediates, and line comments starting with `;`, `#` or `//`. `.ALIGN8` pads code with a NOP when needed and `.WORD64` places an aligned LE64 literal.

### Shared sponge and field state

| View | Lane assignment | Interpretation |
|---|---|---|
| Keccak-p[1600] | S0–S24 | Lane index is x + 5y. For the 136-byte rate, S0–S16 hold the rate, S17–S24 the 512-bit capacity. |
| Poseidon2-GL-w24 | S0–S23 | S0–S15 rate, S16–S23 capacity. S0–S6 supply seven output limbs for Jive feed-forward. S24 survives the permutation. |
| Poseidon2-GL-w12 | S0–S11 | S12–S24 survive the permutation. |
| Quintics | E0 = S0–4, E1 = S5–9, E2 = S10–14, E3 = S15–19, E4 = S20–24 | Ascending powers of u in Fp[u]/(u⁵−3), with p = 2⁶⁴−2³²+1. |
| Binary polynomials | Pk = (S[2k], S[2k+1]), k = 0…11 | Low 64 bits first. Bit i is the coefficient of xⁱ, reduced modulo x¹²⁸+x⁷+x²+x+1. S24 is outside this view. |

A write to E0 changes all of P0 and P1 and the low half of P2. S24 holds both a Keccak lane and the highest coefficient of E4. FP5 and GF128 operations capture sources before writing, including when a destination aliases a source. The 15 writable GPRs and 25 S lanes together hold 2,560 bits.

## Instruction reference

Number bits from 0 (least significant). In the register format the fields from most to least significant are `op[31:28] imm8[27:20] sub[19:16] rc[15:12] rb[11:8] ra[7:4] rd[3:0]`. Field names in the following tables refer to this layout unless an alternate packing is shown. All unassigned subfunctions and nonzero reserved fields raise `IllegalInsn`. Values and addresses wrap modulo 2⁶⁴. Cycle counts are per architectural instruction, including either direction of a branch.

| op | Family | Encoding and result | Cycles |
|---|---|---|---|
| 0 | SYS | sub 0–6 as detailed below | 1 |
| 1 | LUT4 | M = sub. rc=imm8=0. For each bit, take bit `2*a+b` of M. | 1 |
| 2 | ALU | rc=imm8=0. sub 0 ADD, 1 SUB, 2 SHL, 3 SHR, 4 ASR, 5 ROL, 6 ROR, 7 MUL64, 8 MULHU64. | 1 for 0–6, 4 for 7–8 |
| 3 | ALUI | fn4 in bits 11–8, imm16 in 27–12. rd and ra in the low byte. See below. | 1 |
| 4 | IMM20 | mode in 7–4, imm20 in 27–8. 0 MOVZ20 zero-extends, 1 MOVS20 sign-extends, 2 AUIPC adds signed imm20 × 4 to this instruction’s PC. | 1 |
| 5 | CMP | Predicate in rc. sub=imm8=0. Write 0 or 1. | 1 |
| 6 | SEL / BYTE | imm8=0. sub 0 SEL, 1 BEXTU, 2 BEXTS, 3 BSWAP64. | 1 |
| 7 | LOAD | Signed offset in 27–12, mode in 11–8. Mode 0 LD64 uses base + 8×offset. Mode 1 LDBU uses base + offset, zero-extends byte. | 2 |
| 8 | STORE | Same address fields as LOAD. Source in **3–0**, base in 7–4. Mode 0 ST64 writes LE64, mode 1 STB writes low byte. | 2 |
| 9 | BR | Condition register in 3–0, bop in 7–4, signed off20 in 27–8. 0 BEQZ, 1 BNEZ, 2 BLTZ (signed), 3 BGEZ (signed). Taken target = PC+4+4×off20. | 1 |
| A | JAL | Signed off24 in 27–4, link destination in 3–0. Write PC+4 to rd and jump to PC+4+4×off24. | 1 |
| B | JALR | Signed imm16 in 27–12, bits 11–8 zero. Form target = old R[ra]+4×imm16. Check alignment before writing PC+4 to rd. rd=ra is valid. | 1 |
| C | SPG | off8 in 27–20, sidx in 19–12, **sub in 11–8**, ra and rd in the low byte. | 1 or 2 |
| D | GL64 / FP5 | sub in 19–16, imm8=0. Scalar indices address GPRs, quintic indices address E0–E4. | 1–104 by sub |
| E | GF128 | sub in 19–16, rc=imm8=0, rd/ra/rb each <12. 0 GF128.MUL (carryless product and reduction), 1 GF128.XOR (field addition). | 4, 1 respectively |
| F | PERM | All four register fields zero. sub 0 Keccak, 1 width-24 Poseidon2, 2 width-12 Poseidon2. | 12/24, 216, 120 |

**System instructions.** Only the all-zero word encodes EXC. With traps enabled it vectors as EnvCall, saving PC+4. With traps disabled it advances by 4. Sub 1 ERET resumes at EPC & ~3 and sets EXC_EN. Sub 2 CSRR rd,csr8 reads the CSR selected by imm8 and requires ra=rb=rc=0. Sub 3 CSRW ra,csr8 writes R[ra] and requires rd=rb=rc=0. Sub 4 ZEROIZE clears R1–R15 and S0–S24 and starts the full enclave D-SRAM scrub. Sub 5 HALT halts after advancing PC, sub 6 NOP advances PC. ERET, ZEROIZE, HALT and NOP require all other fields zero.

**Integer and immediate arithmetic.** ADD, SUB and MUL64 keep the low 64 bits. MULHU64 returns bits 127–64 of the unsigned product. Logical shifts by 64 or more yield zero. ASR fills with the sign bit, including for a count ≥64. Rotates use the low six count bits. Immediate functions are listed below.

| fn4 | ALUI operation | Immediate interpretation |
|---|---|---|
| 0, 1 | ADDI, ADDIU | Signed 16-bit addend, unsigned 16-bit addend respectively |
| 2, 3, 4 | XORI, ANDI, ORI | Zero-extended 16-bit mask |
| 5, 6, 7, 8 | SHLI, SHRI, ASRI, ROLI | Immediate must be in 0…63. Larger encodings are illegal. SHRI is logical, ASRI arithmetic. |
| 9 | SLK16 | Shift ra left 16, insert imm16 into the low bits |

**Boolean operations.** The truth table below is in hexadecimal selector order. CMP flags are IV:SN:GT:EQ, high to low. First OR the enabled equality and greater-than tests, using signed comparison if SN is set. IV inverts that result.

| Selector (hex) | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | A | B | C | D | E | F |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| LUT4 | 0 | NOR | ~a & b | ~a | a & ~b | ~b | XOR | NAND | AND | XNOR | b | ~a OR b | a | a OR ~b | OR | all ones |
| CMP | false | EQ | GTU | GEU | false | EQ | GTS | GES | true | NE | LEU | LTU | true | NE | LES | LTS |

**Select and bytes.** SEL rd,ra,rb,rc takes R[ra] when R[rc]=0 and R[rb] otherwise. BEXTU/BEXTS encode a byte offset 0…7 in rb and a byte count in rc (1…7 literally, 0 means 8). Bit 3 of either field must be zero. Shift the source right logically by eight times the offset, mask to the requested width, then for BEXTS sign-extend from the requested high bit when the width is below eight bytes. Bits beyond the original word shift in as zero. BSWAP64 reverses the eight bytes and requires rb=rc=0.

**Lane access.** The direct lane index is an instruction immediate. Every encoded lane transfer requires sidx <25. Word memory operations require an 8-byte-aligned effective address, including accesses to or from lanes.

| SPG sub | Operation | Required zero fields | Cycles |
|---|---|---|---|
| 0 | SGET rd,S[i] copies the lane into rd | ra, off8 | 1 |
| 1, 2 | SPUT S[i],ra replaces the lane, SXOR S[i],ra XORs into it | rd, off8 | 1 |
| 3 | SZERO clears all 25 lanes | rd, ra, sidx, off8 | 1 |
| 4, 5 | SLD64 S[i],[base+off] loads, SST64 [base+off],S[i] stores. EA = R[ra] + 8×signed(off8). | rd | 2 |

**Goldilocks and permutations.** Scalar GL arithmetic reduces inputs modulo p and produces canonical limbs. Overlap is safe for quintic and binary field operands. A Keccak instruction supplies just the permutation. Software supplies the rate, padding and domain for its hash construction.

| Family / sub | Operation | Constraints and result | Cycles |
|---|---|---|---|
| D / 0 | GL.MAC rd,ra,rb,rc | (a×b+c) mod p | 4 |
| D / 1, 2 | GL.ADD, GL.SUB | (a±b) mod p, rc=0 | 1 |
| D / 3 | GL.SBOX7 rd,ra | a⁷ mod p, rb=rc=0 | 12 |
| D / 4 | FP5.MUL ed,ea,eb | Quintic product, u⁵=3, all indices <5, rc=0 | 104 |
| D / 5, 6 | FP5.ADD, FP5.SUB | Limbwise addition or subtraction mod p, same index rules | 5 |
| F / 0 | KECCAK.F1600 12 or 24 | imm8 selects the last 12 rounds (12–23) or all 24 (0–23), over S0–S24. Other round encodings trap. | 12 or 24 |
| F / 1 | POSEIDON2.GL24 | imm8=0. S0–S23, 8 full + 44 partial rounds, external matrix M₄ ⊗ P₆, shift-based internal matrix. | 216 |
| F / 2 | POSEIDON2.GL12 | imm8=0. S0–S11, 30 rounds. | 120 |

## Traps, CSRs and MMIO

On a fault with EXC_EN[0]=1, the core records ECAUSE and the faulting PC in EPC (PC+4 for EXC), clears EXC_EN and jumps to EVEC. With EXC_EN[0]=0 a hardware fault records ECAUSE and halts. EXC has the fall-through behavior described above. Align the handler before enabling traps. Repair the fault or advance EPC as appropriate before ERET. Causes are 1 IllegalInsn, 2 EnvCall, 3 MisalignedPc, 4 MisalignedMem and 5 MemFault.

| CSR | Name | Access | Software-visible behavior |
|---|---|---|---|
| 00 | ARCH_ID | R | 0x4153_5332_0000_0001 |
| 01 | WORD_BITS | R | 64 |
| 02 | EVEC | RW | Trap target, low two bits masked on write |
| 03 | POWER | W | Bit 0 set requests halt |
| 04 | INSTRET | RW | +1 per retired non-trapping instruction. A write sets this counter directly. |
| 05 | CYCLES | RW | Adds the instruction’s architectural cost. A write sets this counter directly. |
| 06 | FEATURES | R | 0x0000_000F, bits 0…3 for LUT4, GL64_FP5, GF128 and KECCAK_POSEIDON2 |
| 08 | EPC | RW | Trap continuation address |
| 09 | ECAUSE | RW | Trap cause |
| 0A | DBG_OUT | W | Bits 7–0 enqueue a TX byte when enabled. |
| 0B | DBG_IN | R | Bit 8 valid, bits 7–0 received byte. Read acknowledges. |
| 3F | EXC_EN | RW | Bit 0 controls trap entry |
| 40 | DIT | R | Constant 1 |
| 41 | ZEROIZE | W | Bit 0 set clears R1–R15 and S0–S24 in one architectural cycle and starts the full enclave D-SRAM scrub |

Addresses above are hexadecimal. 07, 0C–3E and 42–FF are unassigned. The documentation VM traps unassigned or wrong-direction CSR accesses. CSR addresses name registers in CSRR/CSRW instructions. A memory load to the same numeric address accesses the memory map.

### Memory and system registers

| Inclusive byte addresses | Region | Access | Size | Function |
| --- | --- | --- | --- | --- |
| `0x0000_0000..0x0000_0FFF` | `I-ROM` | X R | 4 KiB | 1,024 × 32-bit instructions. Resident boot dispatcher and crypto kernels. |
| `0x0000_1000..0x0000_11FF` | `I-SRAM` | X R | 512 B | SRAM1. Up to 128 authenticated instructions. CPU stores fault. |
| `0x0001_0000..0x0001_00FF` | `D-SRAM` | R W | 256 B | SRAM0 words 0–31. Scratch and downward-growing stack. |
| `0x0001_0100..0x0001_017F` | `RX_MBOX` | R W | 128 B | SRAM0 words 32–47. Request bytes in wire order. |
| `0x0001_0180..0x0001_01FF` | `TX_MBOX` | R W | 128 B | SRAM0 words 48–63. Application response bytes. |
| `0xFFFF_0000..0xFFFF_007F` | `SYS_MMIO` | R W | 128 B | Resident-only peripherals. Applet execution locks access through I-ROM returns. |

D-SRAM spans `0x0001_0000..0x0001_01FF`. SRAM0 holds 64 little-endian 64-bit words.

Access SYS_MMIO at base `0xFFFF_0000`. Use aligned LE64 transfers. Reserved word offsets read zero and ignore writes.

| Offset | Register | Access | Fields and operation |
| --- | --- | --- | --- |
| `+0x00` | `FRAM_XFER` | RW | Read: bits 7–0 last received SPI byte. Write: bits 7–0 TX byte, bit 8 `FRAM_CS_N` level, bit 9 start 1-byte Mode-0 transfer when idle (`FRAM_SCK = CLK_IN / 8`). |
| `+0x08` | `FRAM_STATUS` / `VAULT_CAP_LO` | R / W | Read: bit 0 `fram_busy`, bit 1 synchronized `FRAM_MISO`. Write (64-bit): enclave-private `cap_commit[63:0]` (`cap_lo`). |
| `+0x10` | `CMD_CTX` / `PUF_CTRL` | RW | Read: `[7:0]` `cmd_op`, `[15:8]` `load_count`, `[25:16]` `payload_len`, `[27:26]` `cmd_flags[1:0]`, `[63:32]` `record.state`. Write (`!puf_busy`): `[2:0]` `blk_sel` (`0..3`), `[3]` `recon_mode`, `[13:8]` `margin_thresh`, starts `dregg_ro_puf_bch`. |
| `+0x18` | `VAULT_NONCE_LO` | RW | Enclave-private session `nonce[63:0]`, cleared on `srst_n`. |
| `+0x20` | `PUF_VMASK` | RW | 63-bit valid differential-pair mask (`dregg_ro_puf_bch`: read after enrollment, write before reconstruction). |
| `+0x28` | `PUF_SYN` | RW | Bits 26–0: 27-bit `BCH(63,36,5)` helper syndrome (read after enrollment, write before reconstruction). |
| `+0x30` | `PUF_WORD` / `VAULT_CAP_HI` | R / W | Read: `[35:0]` reconstructed 36-bit BCH block word when `puf_complete && !puf_err`. Write (64-bit): enclave-private `cap_commit[127:64]` (`cap_hi`). |
| `+0x38` | `PUF_STATUS` / `VAULT_RECORD` | RW | Read: `[0]` `puf_busy`, `[1]` `puf_complete`, `[2]` `puf_err`, `[8:3]` `puf_accepted`, `[12:9]` `puf_corrected`, `[63:32]` `record.gen`. Write (64-bit): committed `record_q` (`gen:u32 \|\| state:u32`). |
| `+0x40` | `TRNG_DATA` | R | Conditioned 64-bit random word from the dual 17-stage CoSO TRNG (auto-acknowledges when `trng_valid && trng_ok`). |
| `+0x48` | `TRNG_HEALTH` | R | Bits 29–0 accepted count, bit 30 `trng_valid`, bit 31 `trng_ok`, bit 32 `!uart_tx_ovf`, bit 33 `apt_fail`, bit 34 `rct_fail` (NIST SP 800-90B). |
| `+0x50, +0x58` | `VAULT_LO`, `VAULT_HI` | RW | Enclave-private 128-bit `root_secret` (`VERDICT_CTRL[16]=0`) or `cap_commit` (`VERDICT_CTRL[16]=1` on read); 64-bit writes update `key_lo` / `key_hi`. Cleared on `srst_n`. |
| `+0x60` | `VERDICT_CTRL` | RW | Bit 0 `VERIFY_OK`, bit 1 sticky `FAULT` (write-1-to-set), bits 10–8 `lc_state`, bit 16 `vault_cap_sel`. Tamper forces `VERIFY_OK=0`, `FAULT=1` combinationally. |
| `+0x68` | `GPIO_IO` | RW | Bits 7–0 output data, 15–8 output enables, 23–16 synchronized inputs. All eight pins reset to inputs with pull-downs. |
| `+0x70` | `DBG_UART_DIV` | RW | Bits 11–0 clocks per bit. Reset 25 (`1.0 Mbaud` at 25 MHz). Effective divisor is `max(4, div)`. |
| `+0x78` | `VAULT_NONCE_HI` | RW | Enclave-private session `nonce[127:64]`, cleared on `srst_n`. |

Only BOOT_MODE = 10 with lifecycle BLANK enables the 8N1 UART. DBG_OUT (CSR 0x0A, W) queues bits 7–0 in a 16-byte TX FIFO. A full FIFO drops the incoming byte and sets sticky overflow without stalling the core. DBG_IN (CSR 0x0B, R) returns rx_valid in bit 8 and rx_byte in bits 7–0. Reading acknowledges the byte. The muted transmitter idles high and DBG_IN reads zero. Divisor 25 gives 1.0 Mbaud at 25 MHz.

Core `ZEROIZE` (`0x00040000`) or a `CSRW` to `0x41` with bit 0 set clears the register banks in one architectural cycle and starts the full D-SRAM scrub. The scrubber writes bytes 0–511, including TX_MBOX, one byte per clock (20.48 µs at 25 MHz). Reset, tamper release and budget expiry also select a full scrub. Normal halt or trap selects bytes 0–383 (scratch and RX), retaining TX. HOST_RDY stays low during a sweep.

Hardware W^X restricts instruction fetch to I-ROM and authenticated I-SRAM. Any fetch outside those regions raises MemFault (ECAUSE = 5). SYS_MMIO requires an I-ROM PC and clear `applet_mode_q`. Once applet execution begins, this bit stays set for the execution, so a peripheral load or store faults with the same cause even after control returns to I-ROM.

The chip integrates 514 physical `gf180mcu_fd_sc_mcu7t5v0` ring oscillators: 512 five-stage PUF rings (`dregg_ro_puf_bch`, forming 256 strictly disjoint differential pairs with 252 active across four disjoint `BCH(63,36,5)` blocks for `4 × 36 = 144` bits of independent post-helper min-entropy) and two 17-stage Coherent-Sampling (CoSO) TRNG rings (`qsag_trng`) with continuous NIST SP 800-90B Repetition Count (`RCT`) and Adaptive Proportion (`APT`) health monitors. Resident I-ROM (`1,024 / 1,024` words = `4,096` bytes) implements full Zero-Factory-Trust post-quantum `WOTS+C` enrollment, dual-slot torn-write-safe FRAM journaling, capability/inline `WOTS+C` code authentication, and Cut-the-Hash signing without ever exporting `root_secret`.

## Constant-time firmware

1. Keep branch conditions, indirect jump targets, loop bounds, stack pointers and memory base addresses public. This applies to byte operations and SLD64/SST64 as well as LD64/ST64. A one-cycle branch can still take paths with different lengths or address traces.
2. Load both children in the same order on every execution. Select the loaded **values**. Selecting a pointer with a secret SEL and then dereferencing it exposes the choice on the bus.
3. Build constants in instructions. LI64 always emits MOVZ20 with the high 16 bits followed by three SLK16 instructions, with the chunks in descending significance. It takes 16 code bytes, four cycles and zero data reads.
4. Keep debug output, MMIO writes, command lengths, errors and published results independent of secrets except for the authorized output. A taint-clean PC/address trace says nothing about what a transmitted byte contains.
5. Treat subroutine return and command exit separately. A callee must retain enough state to deliver its result and return. For a mailbox reply, the wrapper writes the permitted result to TX_MBOX and halts. ZEROIZE also wipes TX_MBOX and erases RA and SP. SZERO clears only S. Hardware tamper is asynchronous and forces VERIFY_OK low and FAULT high even if both clocks stop.

```text
; Fixed-length load
0000  4001230a  MOVZ20 T0, 0x0123
0004  345679aa  SLK16  T0, T0, 0x4567
0008  389ab9aa  SLK16  T0, T0, 0x89ab
000c  3cdef9aa  SLK16  T0, T0, 0xcdef

; Select one word from two public locations using a secret predicate in A2
LD64 A3, [A0]
LD64 A4, [A1]
SEL  A3, A3, A4, A2
```

## Four callable leaf routines

All pointers below are public and 8-byte aligned. Provide the entire indicated buffer, including padding. The 130-word Canopy example takes 520 bytes and requires ROM placement. The other three leaf bodies fit in I-SRAM. Timings count from the entry instruction through RET, excluding the caller, initialization of register arguments and the command-exit scrub.

### Quintic Horner evaluation

Lay out canonical coefficients c₀ through c_d consecutively at 40-byte intervals. Set A0 to the address of **c_d**, A1 to the public degree and E1 to the five-limb evaluation point. Each iteration steps backward by 40 bytes and updates E0 in place. Degree zero returns the input coefficient unchanged. E0 holds the result, E1 is preserved, and the routine uses E2 and A0/A1. The cost is 12 + 122d cycles. For a constant polynomial that is 12 cycles, for degree nine it is 1,110.

<!-- @listing fp5_horner full -->
```text
                ; zk-Hem v2 challenge-field Horner evaluation over F_p[u]/(u^5 - 3).
                ;   acc = c[d];  for i = d-1 .. 0:  acc = acc * r + c[i]
                ; In : A0 -> c[d], the top coefficient. Coefficients are stored ascending, 5 limbs (40 bytes) each.
                ;      A1 =  d, the degree (public, >= 0)
                ;      E1 =  r, the evaluation point (S[5..9], loaded by the caller)
                ; Out: E0 =  p(r) (S[0..4], canonical limbs).  Clobbers E2, A0, A1.
                ; Cycles: 12 + 122 d.
                fp5_horner:
0000  c0000440      SLD64   S[0], [A0+0]        ; E0 <- c[d]
0004  c0101440      SLD64   S[1], [A0+8]
0008  c0202440      SLD64   S[2], [A0+16]
000c  c0303440      SLD64   S[3], [A0+24]
0010  c0404440      SLD64   S[4], [A0+32]
0014  90000a05      BEQZ    A1, horner_done     ; degree zero returns the leading coefficient
                horner_step:
0018  3ffd8044      ADDI    A0, A0, -40         ; step down to c[i]
001c  c000a440      SLD64   S[10], [A0+0]       ; E2 <- c[i]
0020  c010b440      SLD64   S[11], [A0+8]
0024  c020c440      SLD64   S[12], [A0+16]
0028  c030d440      SLD64   S[13], [A0+24]
002c  c040e440      SLD64   S[14], [A0+32]
0030  d0040100      FP5.MUL E0, E0, E1          ; acc <- acc * r        104 cycles, in place
0034  d0050200      FP5.ADD E0, E0, E2          ; acc <- acc + c[i]       5 cycles
0038  3ffff055      ADDI    A1, A1, -1
003c  9ffff615      BNEZ    A1, horner_step     ; the loop count is public
                horner_done:
0040  b0000030      RET
```
<!-- @end -->

### Cut-the-Hash binary-field MAC equation

Set P0 to the secret key r, A0 to an array of n records and A1 to its public count **n ≥1**. Each record contains three LE128 values a, z, m at byte offsets 0, 16 and 32. Supply the protocol’s batch coefficients a; a zero coefficient excludes that record from the equation. The routine tests whether Σa·m equals r·Σa·z. Its 0/1 verdict in A0 uses both halves of the field element. It uses A1/A2 and clears the entire lane bank, including r, before return. The cost is 13 + 25n cycles, including for a rejected batch. This listing demonstrates the MAC equation; the surrounding signing protocol supplies the records and consumes the verdict.

<!-- @listing cth_dualmac full -->
```text
                ; Cut-the-Hash dual-MAC check over GF(2^128) = F_2[x]/(x^128 + x^7 + x^2 + x + 1).
                ; Every value z_k carries a second ("dual") copy m_k = r * z_k under the MAC key r.  With public
                ; coefficients a_k the batch is accepted iff
                ;   T = sum_k a_k * m_k  +  r * sum_k a_k * z_k  ==  0.
                ; In : P0 = r (S[0..1], secret, loaded by the caller)
                ;      A0 -> n records { a_k, z_k, m_k }, 2 words each, low word first (48 bytes a record)
                ;      A1 =  n (public, >= 1)
                ; Out: A0 = 1 if T == 0, else 0.  No branch, address or cycle count depends on r, z_k or m_k.
                ; Cycles: 13 + 25 n.
                cth_dualmac:
0000  e0010444      GF128.XOR P4, P4, P4        ; w <- 0   (S[8..9])
0004  e0010555      GF128.XOR P5, P5, P5        ; u <- 0   (S[10..11])
                mac_loop:
0008  c0002440      SLD64   S[2], [A0+0]        ; P1 <- a_k
000c  c0103440      SLD64   S[3], [A0+8]
0010  c0204440      SLD64   S[4], [A0+16]       ; P2 <- z_k
0014  c0305440      SLD64   S[5], [A0+24]
0018  c0406440      SLD64   S[6], [A0+32]       ; P3 <- m_k
001c  c0507440      SLD64   S[7], [A0+40]
0020  e0000212      GF128.MUL P2, P1, P2        ; a_k * z_k               4 cycles
0024  e0000313      GF128.MUL P3, P1, P3        ; a_k * m_k               4 cycles
0028  e0010244      GF128.XOR P4, P4, P2        ; w <- w + a_k * z_k
002c  e0010355      GF128.XOR P5, P5, P3        ; u <- u + a_k * m_k
0030  30030044      ADDI    A0, A0, 48
0034  3ffff055      ADDI    A1, A1, -1
0038  9ffff315      BNEZ    A1, mac_loop        ; the record count is public
003c  e0000404      GF128.MUL P4, P0, P4        ; r * w
0040  e0010455      GF128.XOR P5, P5, P4        ; T <- u + r * w
0044  c000a005      SGET    A1, S[10]
0048  c000b006      SGET    A2, S[11]
004c  100e0655      OR      A1, A1, A2          ; T == 0  <=>  (T.lo | T.hi) == 0
0050  50001054      CMP     A0, A1, ZERO, EQ    ; verdict as a 0/1 word, never as a branch
0054  c0000300      SZERO                       ; scrub r, w, u
0058  b0000030      RET
```
<!-- @end -->

### Poseidon2-GL-w24 Jive compression

A0 and A1 address the seven canonical Goldilocks limbs in each child, A2 addresses seven output limbs, A3/A4 hold tweaks t₀/t₁. The routine constructs the following 24-limb preimage and calls POSEIDON2.GL24 once.

```text
S0..6    L[0..6]       S7..13    R[0..6]
S14..15  t0,t1         S16..18   16,8,7
S19      0x4d524b4c474c3234      S20..22  0,0,0
S23      0x504f5332474c3234
```

For i=0…6, return perm[i] + L[i] + 2R[i] + 4t[i] modulo p, where t[i]=0 for i≥2. E2/E3 reuse spent permutation lanes to add the children. Only seven output limbs are stored. Output may alias either input because the last input read precedes the first store. A3–A5 are scratch and SZERO clears all S lanes. The routine takes 347 cycles. The fixed vector L=1…7, R=8…14, t=(100,200) gives the following seven decimal limbs in order.

```text
1170443848852734659  833485916214919520   373819593114229865
2500389336842599945  2668122737528357675  15131165148025152836
573418327208874869
```

<!-- @listing p2gl24_jive full -->
```text
                ; QSAG seven-limb Merkle compression. All inputs are canonical Goldilocks elements.
                ; A0, A1 -> left and right (56 B each), A2 -> digest (56 B), A3 and A4 = tweak limbs.
                ; A5 is scratch. All inputs are consumed before the first output store. All S lanes are cleared.
                ; Feed-forward: perm[i] + left[i] + 2*right[i] + 4*tweak[i] for i < 7, tweak[i>=2] = 0.
                p2gl24_jive:
0000  c0000300      SZERO
0004  c0000440      SLD64   S[0], [A0+0]
0008  c0101440      SLD64   S[1], [A0+8]
000c  c0202440      SLD64   S[2], [A0+16]
0010  c0303440      SLD64   S[3], [A0+24]
0014  c0404440      SLD64   S[4], [A0+32]
0018  c0505440      SLD64   S[5], [A0+40]
001c  c0606440      SLD64   S[6], [A0+48]
0020  c0007450      SLD64   S[7], [A1+0]
0024  c0108450      SLD64   S[8], [A1+8]
0028  c0209450      SLD64   S[9], [A1+16]
002c  c030a450      SLD64   S[10], [A1+24]
0030  c040b450      SLD64   S[11], [A1+32]
0034  c050c450      SLD64   S[12], [A1+40]
0038  c060d450      SLD64   S[13], [A1+48]
003c  c000e170      SPUT    S[14], A3
0040  c000f180      SPUT    S[15], A4
0044  40001009      MOVZ20  A5, 16
0048  c0010190      SPUT    S[16], A5
004c  40000809      MOVZ20  A5, 8
0050  c0011190      SPUT    S[17], A5
0054  40000709      MOVZ20  A5, 7
0058  c0012190      SPUT    S[18], A5
005c  404d5209      MOVZ20  A5, 0x4d52          ; Merkle domain 0x4d524b4c474c3234
0060  34b4c999      SLK16   A5, A5, 0x4b4c
0064  3474c999      SLK16   A5, A5, 0x474c
0068  33234999      SLK16   A5, A5, 0x3234
006c  c0013190      SPUT    S[19], A5
0070  40504f09      MOVZ20  A5, 0x504f          ; permutation domain 0x504f5332474c3234
0074  35332999      SLK16   A5, A5, 0x5332
0078  3474c999      SLK16   A5, A5, 0x474c
007c  33234999      SLK16   A5, A5, 0x3234
0080  c0017190      SPUT    S[23], A5
0084  f0010000      POSEIDON2.GL24              ; 216 architectural cycles
0088  c000a440      SLD64   S[10], [A0+0]
008c  c010b440      SLD64   S[11], [A0+8]
0090  c020c440      SLD64   S[12], [A0+16]
0094  c030d440      SLD64   S[13], [A0+24]
0098  c040e440      SLD64   S[14], [A0+32]
009c  c050f440      SLD64   S[15], [A0+40]
00a0  c0610440      SLD64   S[16], [A0+48]
00a4  d0050200      FP5.ADD E0, E0, E2          ; out[0..4] += L[0..4]
00a8  d0050311      FP5.ADD E1, E1, E3          ; out[5..6] += L[5..6]
00ac  c000a450      SLD64   S[10], [A1+0]
00b0  c010b450      SLD64   S[11], [A1+8]
00b4  c020c450      SLD64   S[12], [A1+16]
00b8  c030d450      SLD64   S[13], [A1+24]
00bc  c040e450      SLD64   S[14], [A1+32]
00c0  c050f450      SLD64   S[15], [A1+40]
00c4  c0610450      SLD64   S[16], [A1+48]
00c8  d0050222      FP5.ADD E2, E2, E2          ; double right in the field
00cc  d0050333      FP5.ADD E3, E3, E3
00d0  d0050200      FP5.ADD E0, E0, E2          ; out[0..4] += 2*R[0..4]
00d4  d0050311      FP5.ADD E1, E1, E3          ; out[5..6] += 2*R[5..6]
00d8  d0010777      GL.ADD  A3, A3, A3
00dc  d0010777      GL.ADD  A3, A3, A3
00e0  c0000009      SGET    A5, S[0]
00e4  d0010799      GL.ADD  A5, A5, A3
00e8  c0000190      SPUT    S[0], A5
00ec  d0010888      GL.ADD  A4, A4, A4
00f0  d0010888      GL.ADD  A4, A4, A4
00f4  c0001009      SGET    A5, S[1]
00f8  d0010899      GL.ADD  A5, A5, A4
00fc  c0001190      SPUT    S[1], A5
0100  c0000560      SST64   [A2+0], S[0]
0104  c0101560      SST64   [A2+8], S[1]
0108  c0202560      SST64   [A2+16], S[2]
010c  c0303560      SST64   [A2+24], S[3]
0110  c0404560      SST64   [A2+32], S[4]
0114  c0505560      SST64   [A2+40], S[5]
0118  c0606560      SST64   [A2+48], S[6]
011c  c0000300      SZERO                       ; clear all sponge lanes
0120  b0000030      RET
```
<!-- @end -->

### Canopy internal node, 50-byte TurboSHAKE256 digest

A0 and A1 address current and sibling digests, each stored as 50 bytes followed by six zero bytes. A2 is zero when the current child is on the left and nonzero when it is on the right. A3 is the public unsigned 32-bit **parent heap index**, A4 addresses the 200-byte customization midstate, and A5 addresses a 56-byte output. Supply a disjoint writable word at SP−8. The routine preserves SP and T0, erases the stack spill, and uses A3/A4 and all S lanes. Digest output may reuse a child buffer.

Prepare the public midstate once. Starting from 25 zero lanes, XOR in the following 136-byte prefix, then execute KECCAK.F1600 12 and save all 25 lanes in LE order. The first six bytes encode the rate and customization lengths. The ASCII customization has 19 bytes (152 bits).

```python
custom = b"QSAG.ZKHEM2.TREE/v1"
prefix = (bytes([1, 136, 1, 0, 1, len(custom) * 8]) + custom).ljust(136, b"\0")
```

For each node, restore that state and XOR into the rate one byte 0x00, the four LE index bytes, 50 left bytes and 50 right bytes. Thus offsets 5 and 55 begin the two children. XOR 0x07 into byte 105 and 0x80 into byte 135 before the 12-round permutation. Squeeze S0–S5 and the low 16 bits of S6. The final store zero-fills output bytes 50–55. This operation computes an internal node; callers that verify a path must apply the tree’s root framing and compare all 50 digest bytes. Each child address is read in fixed order even for a secret direction. The routine takes 190 cycles for 130 instructions.

<!-- @listing canopy50_node full -->
```text
                ; zk-Hem v2 Canopy internal node, TurboSHAKE256 profile, 50-byte digests:
                ;   out = TurboSHAKE256_TREE( 0x00 || node_idx (4 bytes LE) || left (50) || right (50) )[0..49]
                ; with (left, right) = (cur, sib) if dir == 0, else (sib, cur).  The 105-byte input is one rate block.
                ; In : A0 -> cur  (7 words: 50 bytes, bytes 50..55 zero)      A1 -> sib (same layout)
                ;      A2 =  dir  (0 or non-zero; may be secret: it only ever reaches SEL)
                ;      A3 =  node_idx (heap numbering, < 2^32, public)
                ;      A4 -> midstate (25 words: the state after the customization block)   A5 -> out (7 words)
                ; Left child bytes land at message offset 5, right child bytes at offset 55, so word i of the left
                ; child is split 3 + 5 bytes across lanes i, i+1 and word i of the right child 1 + 7 across 6+i, 7+i.
                ; SP is 8-byte aligned with one writable, disjoint word below it. Cycles: 190.
                canopy50_node:
0000  3fff8011      ADDI    SP, SP, -8
0004  8000001a      ST64    [SP], T0            ; preserve the callee-saved word
0008  c0000480      SLD64   S[0], [A4+0]
000c  c0101480      SLD64   S[1], [A4+8]
0010  c0202480      SLD64   S[2], [A4+16]
0014  c0303480      SLD64   S[3], [A4+24]
0018  c0404480      SLD64   S[4], [A4+32]
001c  c0505480      SLD64   S[5], [A4+40]
0020  c0606480      SLD64   S[6], [A4+48]
0024  c0707480      SLD64   S[7], [A4+56]
0028  c0808480      SLD64   S[8], [A4+64]
002c  c0909480      SLD64   S[9], [A4+72]
0030  c0a0a480      SLD64   S[10], [A4+80]
0034  c0b0b480      SLD64   S[11], [A4+88]
0038  c0c0c480      SLD64   S[12], [A4+96]
003c  c0d0d480      SLD64   S[13], [A4+104]
0040  c0e0e480      SLD64   S[14], [A4+112]
0044  c0f0f480      SLD64   S[15], [A4+120]
0048  c1010480      SLD64   S[16], [A4+128]
004c  c1111480      SLD64   S[17], [A4+136]
0050  c1212480      SLD64   S[18], [A4+144]
0054  c1313480      SLD64   S[19], [A4+152]
0058  c1414480      SLD64   S[20], [A4+160]
005c  c1515480      SLD64   S[21], [A4+168]
0060  c1616480      SLD64   S[22], [A4+176]
0064  c1717480      SLD64   S[23], [A4+184]
0068  c1818480      SLD64   S[24], [A4+192]
006c  3000857a      SHLI    T0, A3, 8           ; header: tag 0x00 in byte 0, node_idx in bytes 1..4
0070  c00002a0      SXOR    S[0], T0
0074  70000047      LD64    A3, [A0+0]         ; word 0 of cur and of sib
0078  70000058      LD64    A4, [A1+0]
007c  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
0080  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
0084  300285a7      SHLI    A3, T0, 40
0088  c0000270      SXOR    S[0], A3
008c  300186a7      SHRI    A3, T0, 24
0090  c0001270      SXOR    S[1], A3
0094  30038587      SHLI    A3, A4, 56
0098  c0006270      SXOR    S[6], A3
009c  30008687      SHRI    A3, A4, 8
00a0  c0007270      SXOR    S[7], A3
00a4  70001047      LD64    A3, [A0+8]         ; word 1 of cur and of sib
00a8  70001058      LD64    A4, [A1+8]
00ac  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
00b0  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
00b4  300285a7      SHLI    A3, T0, 40
00b8  c0001270      SXOR    S[1], A3
00bc  300186a7      SHRI    A3, T0, 24
00c0  c0002270      SXOR    S[2], A3
00c4  30038587      SHLI    A3, A4, 56
00c8  c0007270      SXOR    S[7], A3
00cc  30008687      SHRI    A3, A4, 8
00d0  c0008270      SXOR    S[8], A3
00d4  70002047      LD64    A3, [A0+16]         ; word 2 of cur and of sib
00d8  70002058      LD64    A4, [A1+16]
00dc  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
00e0  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
00e4  300285a7      SHLI    A3, T0, 40
00e8  c0002270      SXOR    S[2], A3
00ec  300186a7      SHRI    A3, T0, 24
00f0  c0003270      SXOR    S[3], A3
00f4  30038587      SHLI    A3, A4, 56
00f8  c0008270      SXOR    S[8], A3
00fc  30008687      SHRI    A3, A4, 8
0100  c0009270      SXOR    S[9], A3
0104  70003047      LD64    A3, [A0+24]         ; word 3 of cur and of sib
0108  70003058      LD64    A4, [A1+24]
010c  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
0110  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
0114  300285a7      SHLI    A3, T0, 40
0118  c0003270      SXOR    S[3], A3
011c  300186a7      SHRI    A3, T0, 24
0120  c0004270      SXOR    S[4], A3
0124  30038587      SHLI    A3, A4, 56
0128  c0009270      SXOR    S[9], A3
012c  30008687      SHRI    A3, A4, 8
0130  c000a270      SXOR    S[10], A3
0134  70004047      LD64    A3, [A0+32]         ; word 4 of cur and of sib
0138  70004058      LD64    A4, [A1+32]
013c  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
0140  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
0144  300285a7      SHLI    A3, T0, 40
0148  c0004270      SXOR    S[4], A3
014c  300186a7      SHRI    A3, T0, 24
0150  c0005270      SXOR    S[5], A3
0154  30038587      SHLI    A3, A4, 56
0158  c000a270      SXOR    S[10], A3
015c  30008687      SHRI    A3, A4, 8
0160  c000b270      SXOR    S[11], A3
0164  70005047      LD64    A3, [A0+40]         ; word 5 of cur and of sib
0168  70005058      LD64    A4, [A1+40]
016c  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
0170  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
0174  300285a7      SHLI    A3, T0, 40
0178  c0005270      SXOR    S[5], A3
017c  300186a7      SHRI    A3, T0, 24
0180  c0006270      SXOR    S[6], A3
0184  30038587      SHLI    A3, A4, 56
0188  c000b270      SXOR    S[11], A3
018c  30008687      SHRI    A3, A4, 8
0190  c000c270      SXOR    S[12], A3
0194  70006047      LD64    A3, [A0+48]         ; word 6 of cur and of sib
0198  70006058      LD64    A4, [A1+48]
019c  6000687a      SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
01a0  60006788      SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
01a4  300285a7      SHLI    A3, T0, 40
01a8  c0006270      SXOR    S[6], A3
01ac  30038587      SHLI    A3, A4, 56
01b0  c000c270      SXOR    S[12], A3
01b4  30008687      SHRI    A3, A4, 8
01b8  c000d270      SXOR    S[13], A3
01bc  40070007      MOVZ20  A3, 0x700           ; TurboSHAKE domain byte 0x07 at message byte 105
01c0  c000d270      SXOR    S[13], A3
01c4  40008007      MOVZ20  A3, 0x80            ; final padding bit: 0x80 at rate byte 135
01c8  30038577      SHLI    A3, A3, 56
01cc  c0010270      SXOR    S[16], A3
01d0  f0c00000      KECCAK.F1600 12             ; 12 cycles, in place on S[0..24]
01d4  c0000590      SST64   [A5+0], S[0]        ; squeeze 50 bytes
01d8  c0101590      SST64   [A5+8], S[1]
01dc  c0202590      SST64   [A5+16], S[2]
01e0  c0303590      SST64   [A5+24], S[3]
01e4  c0404590      SST64   [A5+32], S[4]
01e8  c0505590      SST64   [A5+40], S[5]
01ec  c0006007      SGET    A3, S[6]
01f0  3ffff377      ANDI    A3, A3, 0xFFFF      ; bytes 48, 49
01f4  80006097      ST64    [A5+48], A3
01f8  7000001a      LD64    T0, [SP]
01fc  80000010      ST64    [SP], ZERO          ; erase the spill before releasing the slot
0200  30008011      ADDI    SP, SP, 8
0204  b0000030      RET
```
<!-- @end -->

## Board and host integration

### Die pads and straps (`SLOT_0P5X0P5`, 56 pads)

BOOT_MODE[1:0] selects 00 Mission, 01 SafeRecovery, 10 BlankBringupUART or 11 JTAG_TestWithSecretBankCleared. Hold the straps stable throughout the power session. Hardware enforces SafeRecovery (`BOOT_MODE = 01`) directly at header admission, returning `E_LOCKED = 14` on `0x20 CMD_CTH_SIGN`, `0x30 CMD_LOAD_CODE`, and applet `0x31 CMD_EXEC` (`flags = 0`) while permitting resident `I-ROM` recovery/diagnostic commands. JTAG test mode (`11`) asserts synchronous/latch secret clear (`srst_n = 0`) in 0 clocks and gates `JTAG_TDO` off outside `LC_RESET`/`LC_BLANK`. Tamper assertion (`TAMPER_ZEROIZE_N = 0`) overrides the verdict pins (`VERIFY_OK = 0`, `FAULT = 1`) and clears all 2,560 `latrnq_1` secret latches in `0.600 ns` with `CLK_IN` stopped. Clock the chip through `CLK_IN` and monitor `CLK_MON` at `CLK_IN / 16`. Host DQ uses `gf180mcu_fd_io__bi_t`, `PDRV=2'b01` (8 mA), `SL=1` (slow slew), with 33 Ω series termination per line.

Side indices follow `slot_0p5x0p5.yaml` (`11` south, `17` east, `11` north, `17` west = `56` pads total: `44` active digital signal pads, `4` unconnected `asig_5p0` pads, and `8` supply pads forming `4` 5.0 V `DVDD/DVSS` + `VDD/VSS` pairs). South and north run west to east; east runs south to north; west runs north to south in the table below.

| Pad | Side | Slot | Signal | Pad | Side | Slot | Signal |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | S0 | `clk` | `CLK_IN` | 29 | N0 | `an[3]` | `n/c` |
| 2 | S1 | `rst_n` | `RST_N` | 30 | N1 | `an[2]` | `n/c` |
| 3 | S2 | `dvss0` | `DVSS` | 31 | N2 | `dvss2` | `DVSS` |
| 4 | S3 | `dvdd0` | `DVDD` | 32 | N3 | `dvdd2` | `DVDD` |
| 5 | S4 | `b[0]` | `HOST_DQ0` | 33 | N4 | `an[1]` | `n/c` |
| 6 | S5 | `b[1]` | `HOST_DQ1` | 34 | N5 | `an[0]` | `n/c` |
| 7 | S6 | `b[2]` | `HOST_DQ2` | 35 | N6 | `b[26]` | `TAMPER_ZEROIZE_N` |
| 8 | S7 | `b[3]` | `HOST_DQ3` | 36 | N7 | `b[25]` | `FRAM_MISO` |
| 9 | S8 | `b[4]` | `HOST_DQ4` | 37 | N8 | `b[24]` | `FRAM_MOSI` |
| 10 | S9 | `b[5]` | `HOST_DQ5` | 38 | N9 | `b[23]` | `FRAM_SCK` |
| 11 | S10 | `b[6]` | `HOST_DQ6` | 39 | N10 | `b[22]` | `FRAM_CS_N` |
| 12 | E0 | `b[7]` | `HOST_DQ7` | 40 | W0 | `b[37]` | `JTAG_TCK` |
| 13 | E1 | `b[8]` | `GPIO0` | 41 | W1 | `b[36]` | `JTAG_TMS` |
| 14 | E2 | `b[9]` | `GPIO1` | 42 | W2 | `b[35]` | `JTAG_TDI` |
| 15 | E3 | `b[10]` | `GPIO2` | 43 | W3 | `b[34]` | `JTAG_TDO` |
| 16 | E4 | `b[11]` | `GPIO3` | 44 | W4 | `b[33]` | `NFC_CLK_IN` |
| 17 | E5 | `b[12]` | `GPIO4` | 45 | W5 | `b[32]` | `NFC_ASK_IN` |
| 18 | E6 | `b[13]` | `GPIO5` | 46 | W6 | `b[31]` | `NFC_LOAD_MOD` |
| 19 | E7 | `b[14]` | `GPIO6` | 47 | W7 | `b[30]` | `DB_CHAL_IN` |
| 20 | E8 | `dvss1` | `DVSS` | 48 | W8 | `b[29]` | `DB_RESP_OUT` |
| 21 | E9 | `dvdd1` | `DVDD` | 49 | W9 | `b[28]` | `DBG_UART_TX` |
| 22 | E10 | `b[15]` | `GPIO7` | 50 | W10 | `b[27]` | `DBG_UART_RX` |
| 23 | E11 | `b[16]` | `VERIFY_OK` | 51 | W11 | `in[3]` | `HOST_CS_N` |
| 24 | E12 | `b[17]` | `FAULT` | 52 | W12 | `in[2]` | `BOOT_MODE1` |
| 25 | E13 | `b[18]` | `HOST_SCK` | 53 | W13 | `vss0` | `VSS` |
| 26 | E14 | `b[19]` | `HOST_RDY` | 54 | W14 | `vdd0` | `VDD` |
| 27 | E15 | `b[20]` | `HOST_IRQ` | 55 | W15 | `in[1]` | `BOOT_MODE0` |
| 28 | E16 | `b[21]` | `CLK_MON` | 56 | W16 | `in[0]` | `CLK_EXT_EN` |

### Host link, Zero-Factory-Trust `WOTS+C` lifecycle and QSAG-Wire

The controller uses SPI mode 0 across `×1` (`0x00/0x02`), `×4` (`0x40/0x42`), and `×8` (`0x80/0x82`), plus `0x05` (`CMD_DIAG_RAW`, clocked solely by `HOST_SCK` with `CLK_IN` stopped). Send the prefix on `DQ0`, most significant bit first. For reads, release the data pins for eight dummy `SCK` periods. Wait for `HOST_RDY` to write and `HOST_IRQ` to read. Keep `HOST_CS_N` asserted across each complete transaction.

Prefix 0x05 (`CMD_DIAG_RAW`) shifts 64 bits on `DQ1` after eight dummy clocks: bits 63–56 = `0x5A`, 55–48 = `link_stat` (`{FAULT, VERIFY_OK, tampered, running, scrub_active, IRQ, RDY, halted}`), 47–32 = `PC[15:0]`, 31–24 = `lc_state`, 23–16 = `ECAUSE[7:0]`, 15–0 = `0xA552`. Lifecycle codes are 0 `RESET`, 1 `BLANK`, 2 `PROVISIONED`, 3 `LEASE_PENDING`, 4 `ORPHAN`, 5 `READY` and 6 `LOCKED_OUT`.

| LE64 header bits | Request | Response |
| --- | --- | --- |
| 7–0 | 0x51 | 0x51 |
| 15–8 | Opcode | Opcode OR 0x80 |
| 23–16 | Flags | Bit 0 OK, bit 7 error |
| 47–24 | Payload bytes | Response bytes |
| 63–48 | arg | Error code |

Payload words are little-endian, padded with zeros to a multiple of eight bytes. Length excludes the header and pad. For a five-byte `EXEC` with flags zero and budget `0x1234`, the request header bytes are `51 31 00 05 00 00 34 12`.

| Opcode | Command | State | Operation |
| --- | --- | --- | --- |
| 0x01 | `CMD_IDENT` | Any | Hardware fast-path returning 4 LE64 words: ASCII `ASS2D180`, `ARCH_ID`, packed TRNG/lifecycle status, `CYCLES`. |
| 0x10 | `CMD_BOOT` | `RESET` | Inspects dual 64B FRAM journal slots (`0x0000`/`0x0040`), recovers torn writes by highest valid MAC-authenticated `gen`, reconstructs 144b PUF `root_secret` into `VAULT_LO/HI`, emits `(16B nonce, record, 32B enclave_id)`, and enters `BLANK` or `LEASE_PENDING`. |
| 0x11 | `CMD_ENROL` | `BLANK` | Accepts Owner's 32B post-quantum `WOTS+C` root `pk_0`, enrolls 4 disjoint `BCH(63,36,5)` PUF blocks, seals `(helpers, pk_0)` to FRAM (`0x0080`), and returns `(16B session nonce \|\| 32B public enclave_id)` — zero factory trust, zero exported secret. |
| 0x12 | `CMD_COMMIT` | `BLANK` | Verifies 320B Owner `WOTS+C` capability (`24B` header + `296B` 16-chain base-256 `sum=2040` `TurboSHAKE256` signature), persists `gen=1` journal record with `next_wots_root`, and enters `PROVISIONED`. |
| 0x15 / 0x16 | `CMD_LEASE` / `CMD_GATE` | `LEASE_PENDING` / `READY` | Verifies 320B Owner `WOTS+C` capability bound to `(enclave_id, session_nonce, record)`, caches `cap_commit` in `VAULT_CAP`, rolls `(gen+1, state, next_wots_root)` into the alternate FRAM slot, and enters/updates `READY`. |
| 0x20 | `CMD_CTH_SIGN` | `READY` | Verifies 16B `cap_token` against `cap_commit`, runs constant-time `GF(2^128)` `cth_dualmac`, derives base-4 `Poseidon2-GL-w12` Jive chains in `S0..S24` (zero `root_secret` SRAM spill), and rolls FRAM `gen+1` before releasing the signature. |
| 0x30 | `CMD_LOAD_CODE` | `READY` | Streams 1–128 instruction words into `I-SRAM` with `isram_auth_valid_q = 0` and authenticates via `flags=1` (`20 + 4n` B: `H_ZK_PIN` + 16B Owner `cap_token`) or `flags=2` (`300 + 4n` B: inline 296B Owner `WOTS+C` proof rolling `gen+1`). CPU stores to `I-SRAM` always fault. |
| 0x31 | `CMD_EXEC` | `READY` (`flags=0`) / Any (`flags=1`) | Runs authenticated `I-SRAM` applet (`flags=0`, `PC=0x1000`, `applet_mode=1`) or resident `I-ROM` service (`flags=1`) under exact-edge hardware clock watchdog `arg` (`0` = `65,535` clocks). Returns 160B (`128B TX_MBOX` + `A0, ECAUSE, INSTRET, CYCLES`). |

Wire errors in decimal: 1 `E_MAGIC` · 2 `E_OPCODE` · 3 `E_LEN` · 4 `E_NOKEY` · 5 `E_MAC` · 6 `E_ANCHOR_EMPTY` · 7 `E_ROLLBACK` · 8 `E_REUSE` · 9 `E_ANCHOR_IO` · 10 `E_KEYSET` · 11 `E_TRNG` · 12 `E_PUF` · 13 `E_CAP` · 14 `E_LOCKED` · 15 `E_BUDGET` · 16 `E_TRAP`.

### Silicon closure (`GF180MCU` `SLOT_0P5X0P5`) and reference board

`qsag_ass2_enclave_top` Rev. 2.0 synthesizes to **42,485 cells** (`42,483` `gf180mcu_fd_sc_mcu7t5v0` standard cells = **1,007,069.95 µm²** + `2 × gf180mcu_fd_ip_sram__sram512x8m8wm1` = **418,800.55 µm²** -> **1,425,870.50 µm²** total) inside `SLOT_0P5X0P5` (`1,732,644 µm²` core, `[442, 442]..[1494, 2089] µm`). This area includes the `4,096 B` (`1,024`-word) synthesized `I-ROM`, the 5-octet hierarchical `2,560`-bit `latrnq_1` secret bank, `514` physical ring oscillators (`512` PUF + `2` CoSO TRNG), formally verified (`UNSAT`) Radix-16 (`4 bits/clk`) Wallace 5:2 CSA Goldilocks multiplier (`17` physical clocks; `CSR CYCLES` preserves exact architectural `4`-cycle accounting), 4-bit/clk `GF(2^128)` unit, and 1-clk barrel-rotator `Keccak-f[1600]` / `Poseidon2` engine.

| Pre-Layout 3-Corner `OpenSTA` | Core min. period | Core Fmax | `HOST_SCK` Fmax | `trng_sclk` Fmax | Setup TNS @ 25 MHz | Min. hold slack |
|---|---:|---:|---:|---:|---:|---:|
| TT · 25 °C, 5.00 V | 18.37 ns (14.18 ns reg) | 54.44 MHz (70.51 MHz reg) | 144.50 MHz | 170.55 MHz | **0.00 ns** | +0.13 ns |
| FF · −40 °C, 5.50 V | 14.83 ns (8.85 ns reg) | 67.44 MHz (113.05 MHz reg) | 232.56 MHz | 274.44 MHz | **0.00 ns** | +0.05 ns |
| SS · 125 °C, 4.50 V | **26.49 ns** | **37.75 MHz** | **77.72 MHz** | **90.37 MHz** | **0.00 ns** | +0.30 ns |

At 25 MHz (`40.00 ns`), even worst-case `125 °C, 4.50 V SS` has **+13.51 ns** positive setup margin (`Setup WNS = 0.00 ns`, `Setup TNS = 0.00 ns`, `0` unconstrained endpoints across all 44 clock domains).

<!-- PNR_SIGNOFF_TABLE_PLACEHOLDER -->

All 6 Yosys/SBY formal equivalence theorems (`gl_helpers`, `gf_step4`, `alu_equiv`, universal `2^132` `prove_radix16_step`, universal `2^192` `prove_mul_ind`, and `prove_mul_bmc`) passed `UNSAT`. Rust `qsag-ass2` passed 39/39 unit/KAT/wire tests, lockstep cosim passed `98,824` steps across `1,028` programs, pin-level Verilator passed all 9 Zero-Factory-Trust `WOTS+C` + independent crypto oracle suites across `×1/×4/×8` host widths, and 4-state `GF180MCU` specify gate-level simulation (`iverilog -gspecify -Ttyp`) passed all 4 physical gates including `0.600 ns` clockless wipe of all `2,560/2,560` `.Q` latch nodes.

| PVT | RO mean ± σ (MHz) | BCH window (µs) | Cold avg / peak (nA / µA) | Rapid (ns) | TDC (ps) | Bounce (mV), 4-pair baseline / low-L carrier |
| --- | --- | --- | --- | --- | --- | --- |
| TT / -40 °C | 850.222 ± 1.505 | 10.24 | 46.7 / 39.20 | 3.047 | 95.08 | 376.2 / 328.2 |
| TT / 27 °C | 716.484 ± 1.306 | 10.24 | 46.5 / 35.75 | 3.616 | 108.78 | 283.7 / 243.9 |
| TT / 125 °C | 579.917 ± 1.068 | 20.48 | 6.7 / 35.76 | 4.411 | 127.28 | 202.5 / 171.8 |
| SS / -40 °C | 588.111 ± 1.241 | 10.24 | 39.8 / 39.28 | 4.165 | 136.46 | 255.0 / 218.1 |
| SS / 27 °C | 493.664 ± 1.069 | 20.48 | 39.0 / 35.82 | 4.972 | 157.20 | 191.1 / 160.9 |
| SS / 125 °C | 398.984 ± 0.859 | 20.48 | 5.8 / 35.73 | 6.159 | 184.37 | 134.6 / 111.5 |
| FF / -40 °C | 1120.261 ± 1.656 | 10.24 | 40.5 / 39.02 | 2.422 | 72.77 | 516.1 / 453.9 |
| FF / 27 °C | 950.486 ± 1.484 | 10.24 | 36.3 / 35.64 | 2.853 | 82.22 | 388.8 / 338.0 |
| FF / 125 °C | 773.247 ± 1.246 | 20.48 | 6.6 / 35.87 | 3.469 | 95.78 | 274.9 / 234.9 |

TT/SS/FF supplies are 5.0/4.5/5.5 V (`ngspice 47` BSIM3v3). Rev. 2.0 scales the characterized 5-stage RO cell family to 512 physical rings (252 active disjoint differential pairs across four `BCH(63,36,5)` blocks with 20-bit counters). The carrier sweep retains 8 mA slow slew, 33 Ω series resistors, eight 15 pF loads and 125 mΩ per bond, using 0.9 nH each for south `DVSS` and `DVDD` (pads 3 and 4) to achieve `453.9 mV < 500 mV` worst south bounce across all nine corners.

### Carrier wiring

Use a 5 V host for the base population (`U4/U5` DNP). Terminate all eight `HOST_DQ` lines (`pads 5–12`) with 33 Ω and use 33 Ω at the `HOST_SCK` source (`pad 25`). Fit 10 kΩ pull-ups on `HOST_CS_N` (`pad 51`) and `FRAM_CS_N` (`pad 39`). Fit one 100 nF X7R bypass capacitor at each of the four die supply pairs, a 4.7 µF bulk capacitor at `J1/JP1`, and 100 nF each at the `TPS3839K50` supervisor and `FM25W256-G` FRAM. Supply an external clock on `pad 1` (`CLK_IN`), jumper `CLK_EXT_EN` (`pad 56`) high, strap `BOOT_MODE1/0` (`pads 52, 55`) individually, and route `DB_CHAL_IN` (`pad 47`) and `DB_RESP_OUT` (`pad 48`) to ground-referenced SMA connectors.

The RF schematic shows diode polarities and separate chip and rectifier supplies. The population schedule is on the final page of the datasheet. [RF schematic](datasheet/reference-rf.svg) · [Carrier schematic](datasheet/reference-carrier.svg) · [Datasheet and BOM](datasheet/dregg64-ass2-datasheet.pdf)

### Rust host driver

Implement the four methods of `Bus` with the adapter’s I/O deadline. The example asserts CS for one write and then for one complete reply. Its mock exercises a one-word and a two-word authenticated frame, the fixed EXEC trailer, short reads, device errors and size limits. The Python leaf-call harness returns an A0-sized result for checking the example routines. The Rust driver exposes the entire hardware mailbox and the four status words.

<!-- @rust full -->
```rust
//! QSAG-Wire host driver for ASS2-0P5, SPI ×1. Each write and each reply has its own CS-low interval.
//! A board adapter owns RDY, IRQ, chip select, clocking and its I/O deadline.
//! Layouts follow the Rev. 1.0 host interface: CMD_LOAD_CODE carries `u32 word_count`, the instruction
//! words and a 16-byte tag; a CMD_EXEC reply is the 128 mailbox bytes, then A0, ECAUSE, INSTRET and CYCLES.

use std::io::{self, Read};

pub trait Bus {
    fn ready(&mut self) -> bool;
    fn irq(&mut self) -> bool;
    fn write(&mut self, bytes: &[u8]) -> io::Result<()>;
    /// Send prefix under CS, then clock bytes from DQ1. Dropping the reader releases CS.
    fn begin_read(&mut self, prefix: &[u8]) -> io::Result<impl Read + '_>;
}

pub const CMD_IDENT: u8 = 0x01;
pub const CMD_LOAD_CODE: u8 = 0x30;
pub const CMD_EXEC: u8 = 0x31;

pub const I_SRAM_WORDS: usize = 128; // 0x0000_1000..0x0000_11FF
pub const MBOX_BYTES: usize = 128; // RX_MBOX and TX_MBOX, each
const EXEC_REPLY_BYTES: usize = MBOX_BYTES + 4 * 8;
pub const FLAG_TAG: u8 = 1; // CMD_LOAD_CODE: the tag field holds an H_ZK_PIN tag
pub const E_BUDGET: u16 = 15; // CMD_EXEC stopped at its cycle budget
pub const E_TRAP: u16 = 16; // CMD_EXEC stopped on a trap; ECAUSE is in DIAG_RAW

#[derive(Debug)]
pub enum WireError {
    Io(io::Error),
    Timeout,
    Length,
    BadMagic,
    BadOpcode,
    Status,
    Chip(u16),
}

impl From<io::Error> for WireError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

#[derive(Debug)]
pub struct ExecResult {
    pub tx_mbox: Vec<u8>,
    pub a0: u64,
    pub ecause: u64,
    pub instret: u64,
    pub cycles: u64,
}

pub fn request<B: Bus>(
    bus: &mut B,
    op: u8,
    flags: u8,
    arg: u16,
    payload: &[u8],
) -> Result<Vec<u8>, WireError> {
    if payload.len() >= 1 << 24 {
        return Err(WireError::Length);
    }
    let w0 = 0x51
        | (op as u64) << 8
        | (flags as u64) << 16
        | (payload.len() as u64) << 24
        | (arg as u64) << 48;
    let mut tx = vec![0x00]; // single-bit write
    tx.extend_from_slice(&w0.to_le_bytes());
    tx.extend_from_slice(payload);
    tx.resize(9 + payload.len().next_multiple_of(8), 0);
    if !(0..1_000_000).any(|_| bus.ready()) {
        return Err(WireError::Timeout);
    }
    bus.write(&tx)?;
    if !(0..1_000_000).any(|_| bus.irq()) {
        return Err(WireError::Timeout);
    }

    let mut rx = bus.begin_read(&[0x02, 0x00])?; // read prefix and eight dummy clocks
    let mut hdr = [0; 8];
    rx.read_exact(&mut hdr)?;
    if hdr[0] != 0x51 {
        return Err(WireError::BadMagic);
    }
    if hdr[1] != (op | 0x80) {
        return Err(WireError::BadOpcode);
    }
    let len = u32::from_le_bytes([hdr[3], hdr[4], hdr[5], 0]) as usize;
    if op == CMD_EXEC && len > EXEC_REPLY_BYTES {
        return Err(WireError::Length);
    }
    let mut body = vec![0; len.next_multiple_of(8)];
    rx.read_exact(&mut body)?;
    if hdr[2] & 0x80 != 0 {
        return Err(WireError::Chip(u16::from_le_bytes([hdr[6], hdr[7]])));
    }
    if hdr[2] & 1 == 0 {
        return Err(WireError::Status);
    }
    body.truncate(len);
    Ok(body)
}

/// Payload: `u32 word_count || u32 words[word_count] || 16-byte tag`, all little-endian.
/// The tag covers the count and the words. Frame padding follows the tag.
pub fn load_code<B: Bus>(bus: &mut B, code: &[u32], tag: [u8; 16]) -> Result<(), WireError> {
    if code.is_empty() || code.len() > I_SRAM_WORDS {
        return Err(WireError::Length);
    }
    let mut payload = (code.len() as u32).to_le_bytes().to_vec();
    payload.extend(code.iter().flat_map(|w| w.to_le_bytes()));
    payload.extend_from_slice(&tag);
    request(bus, CMD_LOAD_CODE, FLAG_TAG, 0, &payload).map(|_| ())
}

pub fn exec<B: Bus>(bus: &mut B, input: &[u8], budget: u16) -> Result<ExecResult, WireError> {
    if input.len() > MBOX_BYTES {
        return Err(WireError::Length);
    }
    let mut body = request(bus, CMD_EXEC, 0, budget, input)?;
    if body.len() != EXEC_REPLY_BYTES {
        return Err(WireError::Length);
    }
    let word = |offset: usize| {
        let start = MBOX_BYTES + 8 * offset;
        u64::from_le_bytes(body[start..start + 8].try_into().unwrap())
    };
    let (a0, ecause, instret, cycles) = (word(0), word(1), word(2), word(3));
    body.truncate(MBOX_BYTES);
    Ok(ExecResult {
        tx_mbox: body,
        a0,
        ecause,
        instret,
        cycles,
    })
}

// Transport fixture: records the request and supplies response bytes on one CS assertion.
struct MockBus {
    sent: Vec<u8>,
    reply: Vec<u8>,
}
impl Bus for MockBus {
    fn ready(&mut self) -> bool {
        true
    }
    fn irq(&mut self) -> bool {
        !self.reply.is_empty()
    }
    fn write(&mut self, tx: &[u8]) -> io::Result<()> {
        self.sent = tx.to_vec();
        Ok(())
    }
    fn begin_read(&mut self, prefix: &[u8]) -> io::Result<impl Read + '_> {
        assert_eq!(prefix, [2, 0]);
        Ok(io::Cursor::new(std::mem::take(&mut self.reply)))
    }
}

fn main() {
    let mut bus = MockBus {
        sent: vec![],
        reply: vec![0x51, 0xb0, 1, 0, 0, 0, 0, 0],
    };
    let tag = [0xa5; 16]; // fixture bytes supplied by the test
    load_code(&mut bus, &[0x0005_0000], tag).unwrap(); // HALT, LE
    assert_eq!(
        &bus.sent[..17],
        &[0, 0x51, 0x30, 1, 24, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 5, 0]
    );
    assert_eq!(&bus.sent[17..], &tag); // 24 payload bytes: no frame padding

    bus.reply = vec![0x51, 0xb0, 1, 0, 0, 0, 0, 0];
    load_code(&mut bus, &[0x0006_0000, 0x0005_0000], tag).unwrap(); // NOP, HALT
    assert_eq!(
        &bus.sent[..13],
        &[0, 0x51, 0x30, 1, 28, 0, 0, 0, 0, 2, 0, 0, 0]
    );
    assert_eq!(&bus.sent[21..37], &tag);
    assert_eq!(&bus.sent[37..], &[0; 4]); // padding follows the tag
    assert!(matches!(
        load_code(&mut bus, &[0; I_SRAM_WORDS + 1], tag),
        Err(WireError::Length)
    ));

    bus.reply = vec![0x51, 0xb1, 1, 160, 0, 0, 0, 0, b'o', b'k'];
    bus.reply.resize(8 + MBOX_BYTES, 0);
    for value in [2u64, 0, 41, 190] {
        bus.reply.extend_from_slice(&value.to_le_bytes());
    }
    let result = exec(&mut bus, b"hello", 0x1234).unwrap();
    assert_eq!(&bus.sent[..9], &[0, 0x51, 0x31, 0, 5, 0, 0, 0x34, 0x12]);
    assert_eq!(result.tx_mbox.len(), MBOX_BYTES);
    assert_eq!(&result.tx_mbox[..2], b"ok");
    assert_eq!(
        (result.a0, result.ecause, result.instret, result.cycles),
        (2, 0, 41, 190)
    );

    bus.reply = vec![0x51, 0xb1, 0x80, 0, 0, 0, 4, 0];
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Chip(4))));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 15, 0]; // budget spent: counters, no payload
    bus.reply.extend_from_slice(&41u64.to_le_bytes());
    bus.reply.extend_from_slice(&190u64.to_le_bytes());
    assert!(matches!(
        exec(&mut bus, &[], 190),
        Err(WireError::Chip(E_BUDGET))
    ));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 16, 0];
    bus.reply.resize(24, 0);
    assert!(matches!(
        exec(&mut bus, &[], 9),
        Err(WireError::Chip(E_TRAP))
    ));
    assert!(matches!(
        exec(&mut bus, &[0; MBOX_BYTES + 1], 9),
        Err(WireError::Length)
    ));
    bus.reply = vec![0x51, 0xb1, 1, 0, 0, 0, 0, 0];
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Length)));
    bus.reply = vec![0x51, 0xb1, 1, 16, 0, 0, 0, 0]; // advertised body absent
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Io(_))));
    println!("host_driver: framing checks passed");
}
```
<!-- @end -->
