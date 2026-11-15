//! Constant-time hardware `SHA-256` multi-block compression (`x86_64` `SHA-NI` and `aarch64`
//! `FEAT_SHA256`), with branchless portable fallback and explicit SIMD register zeroization.

#[repr(C, align(16))]
pub(crate) struct Sha256HwConsts {
    pub(crate) k: [u32; 64],
    bswap: [u8; 16],
}

pub(crate) static SHA256_HW_CONSTS: Sha256HwConsts = Sha256HwConsts {
    k: [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ],
    bswap: [3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12],
};

/// Compress all full `64`-byte blocks at the front of `data` into `state` without copying,
/// returning the `< 64`-byte trailing remainder slice.
#[inline]
pub fn sha256_compress_bytes<'a>(state: &mut [u32; 8], data: &'a [u8]) -> &'a [u8] {
    let full_blocks = data.len() / 64;
    if full_blocks > 0 {
        // SAFETY: `[u8; 64]` has size 64 and alignment 1, and `full_blocks * 64 <= data.len()`.
        let blocks =
            unsafe { core::slice::from_raw_parts(data.as_ptr().cast::<[u8; 64]>(), full_blocks) };
        sha256_compress_blocks(state, blocks);
    }
    &data[full_blocks * 64..]
}

/// Compress `blocks` (`64` bytes each) into FIPS 180-4 `SHA-256` `state`, dispatching to
/// hardware `SHA-NI` (`x86_64`) or `FEAT_SHA256` (`aarch64`) when supported.
#[inline]
pub fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    if blocks.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        if (crate::cpuid::probe_capabilities_bits() & crate::cpuid::CAP_SHA_NI) != 0 {
            // SAFETY: `CAP_SHA_NI` verified `SSSE3 + SSE4.1 + SHA-NI`, and `blocks` is non-empty.
            unsafe {
                sha256_compress_blocks_shani(state, blocks);
            }
            return;
        }
    }
    #[cfg(target_arch = "aarch64")]
    {
        let cap_bits = crate::cpuid::probe_capabilities_bits();
        const A64_SHA2_MASK: u32 = crate::cpuid::CAP_A64_NEON | crate::cpuid::CAP_A64_SHA2;
        if (cap_bits & A64_SHA2_MASK) == A64_SHA2_MASK {
            let _dit_guard = crate::cpuid::ensure_aarch64_dit_enabled();
            // SAFETY: `probe_capabilities_bits()` verified runtime `NEON + FEAT_SHA256`, and
            // `blocks` is non-empty.
            unsafe {
                sha256_compress_blocks_aarch64_sha2(state, blocks);
            }
            return;
        }
    }
    sha256_compress_blocks_portable(state, blocks);
}

/// Branchless portable FIPS 180-4 `SHA-256` block compressor with volatile scratch wipe.
pub fn sha256_compress_blocks_portable(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    let mut w = [0u32; 64];
    for block in blocks {
        for (slot, chunk) in w.iter_mut().take(16).zip(block.chunks_exact(4)) {
            *slot = u32::from_be_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let mut a = state[0];
        let mut b = state[1];
        let mut c = state[2];
        let mut d = state[3];
        let mut e = state[4];
        let mut f = state[5];
        let mut g = state[6];
        let mut h = state[7];

        for (&k, &word) in SHA256_HW_CONSTS.k.iter().zip(&w) {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(k)
                .wrapping_add(word);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }
    crate::volatile_fill(&mut w, 0);
}

#[cfg(target_arch = "x86_64")]
macro_rules! shani_rnds4_only {
    ($msg:literal, $k_off:literal) => {
        concat!(
            "movdqa xmm0, ",
            $msg,
            "\n",
            "paddd xmm0, xmmword ptr [{k} + ",
            $k_off,
            "]\n",
            "sha256rnds2 xmm2, xmm1, xmm0\n",
            "pshufd xmm0, xmm0, 0x0e\n",
            "sha256rnds2 xmm1, xmm2, xmm0\n",
        )
    };
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "ssse3,sse4.1,sha")]
pub(crate) unsafe fn sha256_compress_blocks_shani(state: &mut [u32; 8], blocks: &[[u8; 64]]) {
    let st_ptr = state.as_mut_ptr().cast::<u8>();
    let blk_ptr = blocks.as_ptr().cast::<u8>();
    let k_ptr = (&raw const SHA256_HW_CONSTS).cast::<u8>();
    let count = blocks.len();

    // SAFETY: caller verified `SSSE3 + SSE4.1 + SHA-NI` and `count >= 1`; all touched `xmm0..xmm10`
    // registers are wiped with `pxor` prior to `ret`.
    unsafe {
        core::arch::asm!(
            // Pack `[A, B, C, D]` and `[E, F, G, H]` into Intel SHA-NI `ABEF` (`xmm1 = [F,E,B,A]`)
            // and `CDGH` (`xmm2 = [H,G,D,C]`).
            "movdqu xmm0, xmmword ptr [{st} + 0]",
            "movdqu xmm2, xmmword ptr [{st} + 16]",
            "pshufd xmm0, xmm0, 0xb1",
            "pshufd xmm2, xmm2, 0x1b",
            "movdqa xmm1, xmm0",
            "palignr xmm1, xmm2, 8",
            "pblendw xmm2, xmm0, 0xf0",
            "movdqa xmm10, xmmword ptr [{k} + 256]",

            "2:",
            "movdqa xmm8, xmm1",
            "movdqa xmm9, xmm2",

            "movdqu xmm4, xmmword ptr [{blk} + 0]",
            "movdqu xmm5, xmmword ptr [{blk} + 16]",
            "movdqu xmm6, xmmword ptr [{blk} + 32]",
            "movdqu xmm7, xmmword ptr [{blk} + 48]",
            "pshufb xmm4, xmm10",
            "pshufb xmm5, xmm10",
            "pshufb xmm6, xmm10",
            "pshufb xmm7, xmm10",

            // Rounds 0..3 + schedule W[16..19] in xmm4
            shani_rnds4_only!("xmm4", "0"),
            "sha256msg1 xmm4, xmm5",
            "movdqa xmm3, xmm7",
            "palignr xmm3, xmm6, 4",
            "paddd xmm4, xmm3",
            "sha256msg2 xmm4, xmm7",

            // Rounds 4..7 + schedule W[20..23] in xmm5
            shani_rnds4_only!("xmm5", "16"),
            "sha256msg1 xmm5, xmm6",
            "movdqa xmm3, xmm4",
            "palignr xmm3, xmm7, 4",
            "paddd xmm5, xmm3",
            "sha256msg2 xmm5, xmm4",

            // Rounds 8..11 + schedule W[24..27] in xmm6
            shani_rnds4_only!("xmm6", "32"),
            "sha256msg1 xmm6, xmm7",
            "movdqa xmm3, xmm5",
            "palignr xmm3, xmm4, 4",
            "paddd xmm6, xmm3",
            "sha256msg2 xmm6, xmm5",

            // Rounds 12..15 + schedule W[28..31] in xmm7
            shani_rnds4_only!("xmm7", "48"),
            "sha256msg1 xmm7, xmm4",
            "movdqa xmm3, xmm6",
            "palignr xmm3, xmm5, 4",
            "paddd xmm7, xmm3",
            "sha256msg2 xmm7, xmm6",

            // Rounds 16..19 + schedule W[32..35] in xmm4
            shani_rnds4_only!("xmm4", "64"),
            "sha256msg1 xmm4, xmm5",
            "movdqa xmm3, xmm7",
            "palignr xmm3, xmm6, 4",
            "paddd xmm4, xmm3",
            "sha256msg2 xmm4, xmm7",

            // Rounds 20..23 + schedule W[36..39] in xmm5
            shani_rnds4_only!("xmm5", "80"),
            "sha256msg1 xmm5, xmm6",
            "movdqa xmm3, xmm4",
            "palignr xmm3, xmm7, 4",
            "paddd xmm5, xmm3",
            "sha256msg2 xmm5, xmm4",

            // Rounds 24..27 + schedule W[40..43] in xmm6
            shani_rnds4_only!("xmm6", "96"),
            "sha256msg1 xmm6, xmm7",
            "movdqa xmm3, xmm5",
            "palignr xmm3, xmm4, 4",
            "paddd xmm6, xmm3",
            "sha256msg2 xmm6, xmm5",

            // Rounds 28..31 + schedule W[44..47] in xmm7
            shani_rnds4_only!("xmm7", "112"),
            "sha256msg1 xmm7, xmm4",
            "movdqa xmm3, xmm6",
            "palignr xmm3, xmm5, 4",
            "paddd xmm7, xmm3",
            "sha256msg2 xmm7, xmm6",

            // Rounds 32..35 + schedule W[48..51] in xmm4
            shani_rnds4_only!("xmm4", "128"),
            "sha256msg1 xmm4, xmm5",
            "movdqa xmm3, xmm7",
            "palignr xmm3, xmm6, 4",
            "paddd xmm4, xmm3",
            "sha256msg2 xmm4, xmm7",

            // Rounds 36..39 + schedule W[52..55] in xmm5
            shani_rnds4_only!("xmm5", "144"),
            "sha256msg1 xmm5, xmm6",
            "movdqa xmm3, xmm4",
            "palignr xmm3, xmm7, 4",
            "paddd xmm5, xmm3",
            "sha256msg2 xmm5, xmm4",

            // Rounds 40..43 + schedule W[56..59] in xmm6
            shani_rnds4_only!("xmm6", "160"),
            "sha256msg1 xmm6, xmm7",
            "movdqa xmm3, xmm5",
            "palignr xmm3, xmm4, 4",
            "paddd xmm6, xmm3",
            "sha256msg2 xmm6, xmm5",

            // Rounds 44..47 + schedule W[60..63] in xmm7
            shani_rnds4_only!("xmm7", "176"),
            "sha256msg1 xmm7, xmm4",
            "movdqa xmm3, xmm6",
            "palignr xmm3, xmm5, 4",
            "paddd xmm7, xmm3",
            "sha256msg2 xmm7, xmm6",

            // Final 16 rounds 48..63
            shani_rnds4_only!("xmm4", "192"),
            shani_rnds4_only!("xmm5", "208"),
            shani_rnds4_only!("xmm6", "224"),
            shani_rnds4_only!("xmm7", "240"),

            "paddd xmm1, xmm8",
            "paddd xmm2, xmm9",
            "add {blk}, 64",
            "dec rcx",
            "jnz 2b",

            // Unpack `ABEF` (`xmm1`) and `CDGH` (`xmm2`) back to `[A,B,C,D]` and `[E,F,G,H]`
            "pshufd xmm0, xmm1, 0x1b",
            "pshufd xmm2, xmm2, 0xb1",
            "movdqa xmm1, xmm0",
            "pblendw xmm0, xmm2, 0xf0",
            "palignr xmm2, xmm1, 8",
            "movdqu xmmword ptr [{st} + 0],  xmm0",
            "movdqu xmmword ptr [{st} + 16], xmm2",

            "pxor xmm0,  xmm0",
            "pxor xmm1,  xmm1",
            "pxor xmm2,  xmm2",
            "pxor xmm3,  xmm3",
            "pxor xmm4,  xmm4",
            "pxor xmm5,  xmm5",
            "pxor xmm6,  xmm6",
            "pxor xmm7,  xmm7",
            "pxor xmm8,  xmm8",
            "pxor xmm9,  xmm9",
            "pxor xmm10, xmm10",
            st = in(reg) st_ptr,
            blk = inout(reg) blk_ptr => _,
            k = in(reg) k_ptr,
            inout("rcx") count => _,
            out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
            out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
            out("xmm8") _, out("xmm9") _, out("xmm10") _,
            options(nostack),
        );
    }
}

#[cfg(target_arch = "aarch64")]
macro_rules! a64_sha256_rnds4_only {
    ($msg:literal, $k_off:literal) => {
        concat!(
            "ldr q2, [{k}, #",
            $k_off,
            "]\n",
            "add v2.4s, v2.4s, ",
            $msg,
            ".4s\n",
            "mov v3.16b, v0.16b\n",
            "sha256h q0, q1, v2.4s\n",
            "sha256h2 q1, q3, v2.4s\n",
        )
    };
}

#[cfg(target_arch = "aarch64")]
macro_rules! a64_sha256_rnds4_sched {
    ($m0:literal, $m1:literal, $m2:literal, $m3:literal, $k_off:literal) => {
        concat!(
            a64_sha256_rnds4_only!($m0, $k_off),
            "sha256su0 ",
            $m0,
            ".4s, ",
            $m1,
            ".4s\n",
            "sha256su1 ",
            $m0,
            ".4s, ",
            $m2,
            ".4s, ",
            $m3,
            ".4s\n",
        )
    };
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon,sha2")]
pub(crate) unsafe fn sha256_compress_blocks_aarch64_sha2(
    state: &mut [u32; 8],
    blocks: &[[u8; 64]],
) {
    let st_ptr = state.as_mut_ptr();
    let blk_ptr = blocks.as_ptr().cast::<u8>();
    let k_ptr = (&raw const SHA256_HW_CONSTS.k).cast::<u8>();
    let count = blocks.len();
    // SAFETY: caller verified `NEON + FEAT_SHA256` and `count >= 1`; all touched NEON registers
    // `v0..v9` are explicitly wiped with `eor` prior to `ret`.
    unsafe {
        core::arch::asm!(
            "ldp q0, q1, [{st}]",
            "2:",
            "mov v8.16b, v0.16b",
            "mov v9.16b, v1.16b",
            "ldp q4, q5, [{blk}]",
            "ldp q6, q7, [{blk}, #32]",
            "rev32 v4.16b, v4.16b",
            "rev32 v5.16b, v5.16b",
            "rev32 v6.16b, v6.16b",
            "rev32 v7.16b, v7.16b",

            a64_sha256_rnds4_sched!("v4", "v5", "v6", "v7", "0"),
            a64_sha256_rnds4_sched!("v5", "v6", "v7", "v4", "16"),
            a64_sha256_rnds4_sched!("v6", "v7", "v4", "v5", "32"),
            a64_sha256_rnds4_sched!("v7", "v4", "v5", "v6", "48"),
            a64_sha256_rnds4_sched!("v4", "v5", "v6", "v7", "64"),
            a64_sha256_rnds4_sched!("v5", "v6", "v7", "v4", "80"),
            a64_sha256_rnds4_sched!("v6", "v7", "v4", "v5", "96"),
            a64_sha256_rnds4_sched!("v7", "v4", "v5", "v6", "112"),
            a64_sha256_rnds4_sched!("v4", "v5", "v6", "v7", "128"),
            a64_sha256_rnds4_sched!("v5", "v6", "v7", "v4", "144"),
            a64_sha256_rnds4_sched!("v6", "v7", "v4", "v5", "160"),
            a64_sha256_rnds4_sched!("v7", "v4", "v5", "v6", "176"),
            a64_sha256_rnds4_only!("v4", "192"),
            a64_sha256_rnds4_only!("v5", "208"),
            a64_sha256_rnds4_only!("v6", "224"),
            a64_sha256_rnds4_only!("v7", "240"),

            "add v0.4s, v0.4s, v8.4s",
            "add v1.4s, v1.4s, v9.4s",
            "add {blk}, {blk}, #64",
            "subs x3, x3, #1",
            "b.ne 2b",

            "stp q0, q1, [{st}]",
            "eor v0.16b, v0.16b, v0.16b",
            "eor v1.16b, v1.16b, v1.16b",
            "eor v2.16b, v2.16b, v2.16b",
            "eor v3.16b, v3.16b, v3.16b",
            "eor v4.16b, v4.16b, v4.16b",
            "eor v5.16b, v5.16b, v5.16b",
            "eor v6.16b, v6.16b, v6.16b",
            "eor v7.16b, v7.16b, v7.16b",
            "eor v8.16b, v8.16b, v8.16b",
            "eor v9.16b, v9.16b, v9.16b",
            st = in(reg) st_ptr,
            blk = inout(reg) blk_ptr => _,
            k = in(reg) k_ptr,
            inout("x3") count => _,
            out("v0") _, out("v1") _, out("v2") _, out("v3") _,
            out("v4") _, out("v5") _, out("v6") _, out("v7") _,
            out("v8") _, out("v9") _,
            options(nostack),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    #[test]
    fn compress_bytes_matches_portable_on_misaligned_inputs_of_every_length() {
        let mut buf = [0u8; 4 + 64 * 5 + 63];
        let mut x = 0x5EED_u32;
        for b in buf.iter_mut() {
            x = x.wrapping_mul(1_103_515_245).wrapping_add(12_345);
            *b = (x >> 16) as u8;
        }
        for off in 0..4 {
            for len in 0..=(64 * 5 + 63) {
                let data = &buf[off..off + len];
                let mut st_hw = IV;
                let rest = sha256_compress_bytes(&mut st_hw, data);
                assert_eq!(rest.len(), len % 64, "off={off} len={len}");
                assert_eq!(rest, &data[len - len % 64..]);
                let blocks: [[u8; 64]; 5] = core::array::from_fn(|i| {
                    let mut blk = [0u8; 64];
                    if 64 * (i + 1) <= len {
                        blk.copy_from_slice(&data[64 * i..64 * (i + 1)]);
                    }
                    blk
                });
                let mut st_port = IV;
                sha256_compress_blocks_portable(&mut st_port, &blocks[..len / 64]);
                assert_eq!(st_hw, st_port, "off={off} len={len}");
            }
        }
    }

    #[test]
    fn two_block_nist_vector_through_the_dispatched_compressor() {
        // FIPS 180-4 example: "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".
        let msg = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        let mut padded = [0u8; 128];
        padded[..msg.len()].copy_from_slice(msg);
        padded[msg.len()] = 0x80;
        padded[120..].copy_from_slice(&((msg.len() as u64) * 8).to_be_bytes());
        let mut st = IV;
        assert!(sha256_compress_bytes(&mut st, &padded).is_empty());
        assert_eq!(
            st,
            [
                0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4,
                0x19db06c1,
            ]
        );
    }
}
