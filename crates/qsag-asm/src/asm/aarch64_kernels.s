// Hand-crafted constant-time AArch64 (`ARMv8.4-A` + `NEON` + `FEAT_SHA3` + `PMULL` + `FEAT_DIT`)
// assembly kernels for `qsag-asm`.
//
// `.arch armv8.4-a+sha3+crypto` enables assembling all SHA3/PMULL/DIT instructions cleanly on
// baseline `aarch64-unknown-linux-gnu` without global `-C target-feature` flags; runtime execution
// is gated by `cpuid::probe_capabilities()` (`getauxval(AT_HWCAP)` / `sysctlbyname`).

.arch armv8.4-a+sha3+crypto
.text

// =============================================================================
// 1. qsag_asm_enable_dit_aarch64()
//    Set PSTATE.DIT = 1 (Data Independent Timing) in EL0 userspace.
// =============================================================================
.globl qsag_asm_enable_dit_aarch64
.p2align 2
.type qsag_asm_enable_dit_aarch64, %function
qsag_asm_enable_dit_aarch64:
    msr dit, #1
    isb
    ret
.size qsag_asm_enable_dit_aarch64, .-qsag_asm_enable_dit_aarch64

// =============================================================================
// 2. qsag_asm_keccak_sha3_neon(out_row16x5: *mut u8, b_row16x5: *const u8, d_row16x5: *const u8)
//    ARMv8.2-SHA3 `bcax.16b` 2-way 128-bit Keccak Chi row kernel (0 branches, 0 secret addresses!).
//    Uses strictly caller-saved NEON `v0..v7, v16..v20` (never touches callee-saved `v8..v15`)
//    and wipes all touched NEON registers before `ret`.
// =============================================================================
.globl qsag_asm_keccak_sha3_neon
.p2align 2
.type qsag_asm_keccak_sha3_neon, %function
qsag_asm_keccak_sha3_neon:
    ldr q0, [x1, #0]
    ldr q1, [x1, #16]
    ldr q2, [x1, #32]
    ldr q3, [x1, #48]
    ldr q4, [x1, #64]
    ldr q5, [x2, #0]
    ldr q6, [x2, #16]
    ldr q7, [x2, #32]
    eor v0.16b, v0.16b, v5.16b
    eor v1.16b, v1.16b, v6.16b
    eor v2.16b, v2.16b, v7.16b
    ldr q5, [x2, #48]
    ldr q6, [x2, #64]
    eor v3.16b, v3.16b, v5.16b
    eor v4.16b, v4.16b, v6.16b

    bcax v16.16b, v0.16b, v2.16b, v1.16b
    bcax v17.16b, v1.16b, v3.16b, v2.16b
    bcax v18.16b, v2.16b, v4.16b, v3.16b
    bcax v19.16b, v3.16b, v0.16b, v4.16b
    bcax v20.16b, v4.16b, v1.16b, v0.16b

    str q16, [x0, #0]
    str q17, [x0, #16]
    str q18, [x0, #32]
    str q19, [x0, #48]
    str q20, [x0, #64]

    eor v0.16b, v0.16b, v0.16b
    eor v1.16b, v1.16b, v1.16b
    eor v2.16b, v2.16b, v2.16b
    eor v3.16b, v3.16b, v3.16b
    eor v4.16b, v4.16b, v4.16b
    eor v5.16b, v5.16b, v5.16b
    eor v6.16b, v6.16b, v6.16b
    eor v7.16b, v7.16b, v7.16b
    eor v16.16b, v16.16b, v16.16b
    eor v17.16b, v17.16b, v17.16b
    eor v18.16b, v18.16b, v18.16b
    eor v19.16b, v19.16b, v19.16b
    eor v20.16b, v20.16b, v20.16b
    ret
.size qsag_asm_keccak_sha3_neon, .-qsag_asm_keccak_sha3_neon

// =============================================================================
// 3. qsag_asm_keccak_theta_rho_sha3_neon(b_out25x16: *mut u8, s_in25x16: *const u8)
//    Full 25-lane 2-sponge (`25 * 16 = 400` B) Keccak Theta + Rho + Pi step via
//    hardware ARMv8.2-SHA3 `eor3.16b` + `rax1.2d` + `xar.2d`!
//    Uses strictly caller-saved `v0..v6, v16..v20` and zeroizes all before `ret`.
// =============================================================================
.globl qsag_asm_keccak_theta_rho_sha3_neon
.p2align 2
.type qsag_asm_keccak_theta_rho_sha3_neon, %function
qsag_asm_keccak_theta_rho_sha3_neon:
    // Column parities C[0..4] in v0..v4 via 2x `eor3.16b` per column
    ldr q0, [x1, #0]
    ldr q5, [x1, #80]
    ldr q6, [x1, #160]
    eor3 v0.16b, v0.16b, v5.16b, v6.16b
    ldr q5, [x1, #240]
    ldr q6, [x1, #320]
    eor3 v0.16b, v0.16b, v5.16b, v6.16b

    ldr q1, [x1, #16]
    ldr q5, [x1, #96]
    ldr q6, [x1, #176]
    eor3 v1.16b, v1.16b, v5.16b, v6.16b
    ldr q5, [x1, #256]
    ldr q6, [x1, #336]
    eor3 v1.16b, v1.16b, v5.16b, v6.16b

    ldr q2, [x1, #32]
    ldr q5, [x1, #112]
    ldr q6, [x1, #192]
    eor3 v2.16b, v2.16b, v5.16b, v6.16b
    ldr q5, [x1, #272]
    ldr q6, [x1, #352]
    eor3 v2.16b, v2.16b, v5.16b, v6.16b

    ldr q3, [x1, #48]
    ldr q5, [x1, #128]
    ldr q6, [x1, #208]
    eor3 v3.16b, v3.16b, v5.16b, v6.16b
    ldr q5, [x1, #288]
    ldr q6, [x1, #368]
    eor3 v3.16b, v3.16b, v5.16b, v6.16b

    ldr q4, [x1, #64]
    ldr q5, [x1, #144]
    ldr q6, [x1, #224]
    eor3 v4.16b, v4.16b, v5.16b, v6.16b
    ldr q5, [x1, #304]
    ldr q6, [x1, #384]
    eor3 v4.16b, v4.16b, v5.16b, v6.16b

    // D[0..4] in v16..v20 via `rax1.2d`
    rax1 v16.2d, v4.2d, v1.2d
    rax1 v17.2d, v0.2d, v2.2d
    rax1 v18.2d, v1.2d, v3.2d
    rax1 v19.2d, v2.2d, v4.2d
    rax1 v20.2d, v3.2d, v0.2d

    // Theta-XOR + Rho-rotate + Pi-permute all 25 lanes via `xar.2d`
    ldr q0, [x1, #0]
    xar v0.2d, v0.2d, v16.2d, #0
    str q0, [x0, #0]

    ldr q0, [x1, #16]
    xar v0.2d, v0.2d, v17.2d, #63
    str q0, [x0, #160]

    ldr q0, [x1, #32]
    xar v0.2d, v0.2d, v18.2d, #2
    str q0, [x0, #320]

    ldr q0, [x1, #48]
    xar v0.2d, v0.2d, v19.2d, #36
    str q0, [x0, #80]

    ldr q0, [x1, #64]
    xar v0.2d, v0.2d, v20.2d, #37
    str q0, [x0, #240]

    ldr q0, [x1, #80]
    xar v0.2d, v0.2d, v16.2d, #28
    str q0, [x0, #256]

    ldr q0, [x1, #96]
    xar v0.2d, v0.2d, v17.2d, #20
    str q0, [x0, #16]

    ldr q0, [x1, #112]
    xar v0.2d, v0.2d, v18.2d, #58
    str q0, [x0, #176]

    ldr q0, [x1, #128]
    xar v0.2d, v0.2d, v19.2d, #9
    str q0, [x0, #336]

    ldr q0, [x1, #144]
    xar v0.2d, v0.2d, v20.2d, #44
    str q0, [x0, #96]

    ldr q0, [x1, #160]
    xar v0.2d, v0.2d, v16.2d, #61
    str q0, [x0, #112]

    ldr q0, [x1, #176]
    xar v0.2d, v0.2d, v17.2d, #54
    str q0, [x0, #272]

    ldr q0, [x1, #192]
    xar v0.2d, v0.2d, v18.2d, #21
    str q0, [x0, #32]

    ldr q0, [x1, #208]
    xar v0.2d, v0.2d, v19.2d, #39
    str q0, [x0, #192]

    ldr q0, [x1, #224]
    xar v0.2d, v0.2d, v20.2d, #25
    str q0, [x0, #352]

    ldr q0, [x1, #240]
    xar v0.2d, v0.2d, v16.2d, #23
    str q0, [x0, #368]

    ldr q0, [x1, #256]
    xar v0.2d, v0.2d, v17.2d, #19
    str q0, [x0, #128]

    ldr q0, [x1, #272]
    xar v0.2d, v0.2d, v18.2d, #49
    str q0, [x0, #288]

    ldr q0, [x1, #288]
    xar v0.2d, v0.2d, v19.2d, #43
    str q0, [x0, #48]

    ldr q0, [x1, #304]
    xar v0.2d, v0.2d, v20.2d, #56
    str q0, [x0, #208]

    ldr q0, [x1, #320]
    xar v0.2d, v0.2d, v16.2d, #46
    str q0, [x0, #224]

    ldr q0, [x1, #336]
    xar v0.2d, v0.2d, v17.2d, #62
    str q0, [x0, #384]

    ldr q0, [x1, #352]
    xar v0.2d, v0.2d, v18.2d, #3
    str q0, [x0, #144]

    ldr q0, [x1, #368]
    xar v0.2d, v0.2d, v19.2d, #8
    str q0, [x0, #304]

    ldr q0, [x1, #384]
    xar v0.2d, v0.2d, v20.2d, #50
    str q0, [x0, #64]

    eor v0.16b, v0.16b, v0.16b
    eor v1.16b, v1.16b, v1.16b
    eor v2.16b, v2.16b, v2.16b
    eor v3.16b, v3.16b, v3.16b
    eor v4.16b, v4.16b, v4.16b
    eor v5.16b, v5.16b, v5.16b
    eor v6.16b, v6.16b, v6.16b
    eor v16.16b, v16.16b, v16.16b
    eor v17.16b, v17.16b, v17.16b
    eor v18.16b, v18.16b, v18.16b
    eor v19.16b, v19.16b, v19.16b
    eor v20.16b, v20.16b, v20.16b
    ret
.size qsag_asm_keccak_theta_rho_sha3_neon, .-qsag_asm_keccak_theta_rho_sha3_neon

// =============================================================================
// 4. qsag_asm_tower128_bdoz_mac_pmull(out32, lhs32, rhs32, count)
//    2-lane 128-bit BDOZ polynomial MAC via ARMv8 `pmull` / `pmull2` + 0x87 reduction!
// =============================================================================
.globl qsag_asm_tower128_bdoz_mac_pmull
.p2align 2
.type qsag_asm_tower128_bdoz_mac_pmull, %function
qsag_asm_tower128_bdoz_mac_pmull:
    eor v0.16b, v0.16b, v0.16b
    eor v1.16b, v1.16b, v1.16b
    eor v2.16b, v2.16b, v2.16b
    eor v3.16b, v3.16b, v3.16b
    eor v22.16b, v22.16b, v22.16b
1:
    ldr q4, [x1, #0]
    ldr q5, [x2, #0]
    pmull v6.1q, v4.1d, v5.1d
    pmull2 v7.1q, v4.2d, v5.2d
    ext v16.16b, v5.16b, v5.16b, #8
    pmull v17.1q, v4.1d, v16.1d
    pmull2 v18.1q, v4.2d, v16.2d
    eor v17.16b, v17.16b, v18.16b
    ext v19.16b, v22.16b, v17.16b, #8
    ext v20.16b, v17.16b, v22.16b, #8
    eor v6.16b, v6.16b, v19.16b
    eor v7.16b, v7.16b, v20.16b
    eor v0.16b, v0.16b, v6.16b
    eor v1.16b, v1.16b, v7.16b

    ldr q4, [x1, #16]
    ldr q5, [x2, #16]
    pmull v6.1q, v4.1d, v5.1d
    pmull2 v7.1q, v4.2d, v5.2d
    ext v16.16b, v5.16b, v5.16b, #8
    pmull v17.1q, v4.1d, v16.1d
    pmull2 v18.1q, v4.2d, v16.2d
    eor v17.16b, v17.16b, v18.16b
    ext v19.16b, v22.16b, v17.16b, #8
    ext v20.16b, v17.16b, v22.16b, #8
    eor v6.16b, v6.16b, v19.16b
    eor v7.16b, v7.16b, v20.16b
    eor v2.16b, v2.16b, v6.16b
    eor v3.16b, v3.16b, v7.16b

    add x1, x1, #32
    add x2, x2, #32
    subs x3, x3, #1
    b.ne 1b

    mov x4, #0x87
    fmov d21, x4
    ext v16.16b, v1.16b, v22.16b, #8
    pmull v6.1q, v16.1d, v21.1d
    ext v19.16b, v22.16b, v6.16b, #8
    ext v20.16b, v6.16b, v22.16b, #8
    eor v0.16b, v0.16b, v19.16b
    eor v1.16b, v1.16b, v20.16b
    pmull v6.1q, v1.1d, v21.1d
    eor v0.16b, v0.16b, v6.16b
    str q0, [x0, #0]

    ext v16.16b, v3.16b, v22.16b, #8
    pmull v6.1q, v16.1d, v21.1d
    ext v19.16b, v22.16b, v6.16b, #8
    ext v20.16b, v6.16b, v22.16b, #8
    eor v2.16b, v2.16b, v19.16b
    eor v3.16b, v3.16b, v20.16b
    pmull v6.1q, v3.1d, v21.1d
    eor v2.16b, v2.16b, v6.16b
    str q2, [x0, #16]

    // Zeroize ALL touched caller-saved NEON registers `v0..v7` AND `v16..v22`!
    eor v0.16b, v0.16b, v0.16b
    eor v1.16b, v1.16b, v1.16b
    eor v2.16b, v2.16b, v2.16b
    eor v3.16b, v3.16b, v3.16b
    eor v4.16b, v4.16b, v4.16b
    eor v5.16b, v5.16b, v5.16b
    eor v6.16b, v6.16b, v6.16b
    eor v7.16b, v7.16b, v7.16b
    eor v16.16b, v16.16b, v16.16b
    eor v17.16b, v17.16b, v17.16b
    eor v18.16b, v18.16b, v18.16b
    eor v19.16b, v19.16b, v19.16b
    eor v20.16b, v20.16b, v20.16b
    eor v21.16b, v21.16b, v21.16b
    mov x4, #0
    ret
.size qsag_asm_tower128_bdoz_mac_pmull, .-qsag_asm_tower128_bdoz_mac_pmull

// =============================================================================
// 5. qsag_asm_goldilocks_mul_ct_aarch64(a: u64 /* x0 */, b: u64 /* x1 */) -> u64 /* x0 */
//    Zero-branch, zero-csel AArch64 `mul` + `umulh` + `subs`/`sbc` + `adds`/`adc`
//    Goldilocks multiply (`0` `csel`/`cset`/`csetm` instructions!).
// =============================================================================
.globl qsag_asm_goldilocks_mul_ct_aarch64
.p2align 2
.type qsag_asm_goldilocks_mul_ct_aarch64, %function
qsag_asm_goldilocks_mul_ct_aarch64:
    mul x2, x0, x1
    umulh x3, x0, x1
    lsr x4, x3, #32
    and x5, x3, #0xffffffff
    mov w6, #0xffffffff

    subs x2, x2, x4
    sbc x7, xzr, xzr
    and x7, x7, x6
    sub x2, x2, x7

    lsl x8, x5, #32
    sub x8, x8, x5
    adds x2, x2, x8
    adc x7, xzr, xzr
    sub x7, xzr, x7
    and x7, x7, x6
    add x2, x2, x7

    adds x8, x2, x6
    adc x7, xzr, xzr
    sub x7, xzr, x7
    and x7, x7, x6
    add x0, x2, x7
    mov x1, #0
    mov x2, #0
    mov x3, #0
    mov x4, #0
    mov x5, #0
    mov x6, #0
    mov x7, #0
    mov x8, #0
    ret
.size qsag_asm_goldilocks_mul_ct_aarch64, .-qsag_asm_goldilocks_mul_ct_aarch64

// =============================================================================
// 6. qsag_asm_ct_eq_32_aarch64(a: *const u8, b: *const u8) -> u64
//    Straight-line 32-byte tag comparison (`0` branches, `0` conditional selects!).
// =============================================================================
.globl qsag_asm_ct_eq_32_aarch64
.p2align 2
.type qsag_asm_ct_eq_32_aarch64, %function
qsag_asm_ct_eq_32_aarch64:
    ldp x2, x3, [x0, #0]
    ldp x4, x5, [x1, #0]
    eor x2, x2, x4
    eor x3, x3, x5
    orr x2, x2, x3
    ldp x4, x5, [x0, #16]
    ldp x6, x7, [x1, #16]
    eor x4, x4, x6
    eor x5, x5, x7
    orr x4, x4, x5
    orr x2, x2, x4
    sub x3, xzr, x2
    orr x2, x2, x3
    lsr x0, x2, #63
    eor x0, x0, #1
    mov x2, #0
    mov x3, #0
    mov x4, #0
    mov x5, #0
    mov x6, #0
    mov x7, #0
    ret
.size qsag_asm_ct_eq_32_aarch64, .-qsag_asm_ct_eq_32_aarch64

// =============================================================================
// 7. qsag_asm_ct_memzero_aarch64(ptr: *mut u8, len: usize)
//    Assembly byte-exact memory wipe (`len >= 1`) + DMB barrier.
// =============================================================================
.globl qsag_asm_ct_memzero_aarch64
.p2align 2
.type qsag_asm_ct_memzero_aarch64, %function
qsag_asm_ct_memzero_aarch64:
1:
    strb wzr, [x0], #1
    subs x1, x1, #1
    b.ne 1b
    dmb ish
    ret
.size qsag_asm_ct_memzero_aarch64, .-qsag_asm_ct_memzero_aarch64
