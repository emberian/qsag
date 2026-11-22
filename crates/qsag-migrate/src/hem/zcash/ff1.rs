//! AES-256 block encryption (FIPS 197) and FF1 format-preserving encryption (NIST SP
//! 800-38G) with the one parameter set Zcash uses: radix 2, 88 numerals, empty tweak.
//!
//! This is `d_j = FF1-AES256.Encrypt(dk, "", I2LEBSP_88(j))` of the Zcash protocol
//! specification (section 4.2.3 for Orchard, ZIP 32 for Sapling). The 11-byte interface
//! is `LEBS2OSP` of the 88-bit numeral string, the convention of
//! `fpe::ff1::BinaryNumeralString::from_bytes_le` / `to_bytes_le` (fpe 0.7.0) and of
//! `zcash_test_vectors/ff1.py`: numeral `i` is bit `i mod 8` of byte `i / 8`, and SP
//! 800-38G reads each half of the numeral string most-significant numeral first.
//!
//! The key is secret. The S-box is computed as a fixed-length inversion in GF(2^8)
//! followed by the affine map, with no table and no branch on data; round keys are
//! erased after use.

/// Multiplication by `x` in GF(2^8) modulo `x^8 + x^4 + x^3 + x + 1`.
#[inline(always)]
fn xtime(a: u8) -> u8 {
    (a << 1) ^ (0x1b & 0u8.wrapping_sub(a >> 7))
}

/// Multiplication in GF(2^8), eight masked steps.
#[inline(always)]
fn gf_mul(mut a: u8, b: u8) -> u8 {
    let mut r = 0u8;
    for i in 0..8 {
        r ^= a & 0u8.wrapping_sub((b >> i) & 1);
        a = xtime(a);
    }
    r
}

/// The AES S-box: `x^254` (the inverse, with `0 -> 0`) followed by the affine map of
/// FIPS 197 section 5.1.1.
#[inline(always)]
fn sub_byte(x: u8) -> u8 {
    let x2 = gf_mul(x, x);
    let x3 = gf_mul(x2, x);
    let x6 = gf_mul(x3, x3);
    let x12 = gf_mul(x6, x6);
    let x15 = gf_mul(x12, x3);
    let x30 = gf_mul(x15, x15);
    let x60 = gf_mul(x30, x30);
    let x120 = gf_mul(x60, x60);
    let x240 = gf_mul(x120, x120);
    let x252 = gf_mul(x240, x12);
    let inv = gf_mul(x252, x2);
    inv ^ inv.rotate_left(1) ^ inv.rotate_left(2) ^ inv.rotate_left(3) ^ inv.rotate_left(4) ^ 0x63
}

const ROUNDS: usize = 14;

/// The AES-256 key schedule. Erased on drop.
struct Aes256 {
    round_keys: [[u8; 16]; ROUNDS + 1],
}

impl Drop for Aes256 {
    fn drop(&mut self) {
        for rk in self.round_keys.iter_mut() {
            qsag_asm::volatile_fill(rk, 0);
        }
    }
}

impl Aes256 {
    fn new(key: &[u8; 32]) -> Self {
        // FIPS 197 section 5.2 with Nk = 8: 60 four-byte words.
        let mut w = [[0u8; 4]; 4 * (ROUNDS + 1)];
        for (word, chunk) in w.iter_mut().zip(key.chunks_exact(4)) {
            word.copy_from_slice(chunk);
        }
        let mut rcon = 1u8;
        for i in 8..w.len() {
            let mut t = w[i - 1];
            if i % 8 == 0 {
                t = [
                    sub_byte(t[1]) ^ rcon,
                    sub_byte(t[2]),
                    sub_byte(t[3]),
                    sub_byte(t[0]),
                ];
                rcon = xtime(rcon);
            } else if i % 8 == 4 {
                t = [
                    sub_byte(t[0]),
                    sub_byte(t[1]),
                    sub_byte(t[2]),
                    sub_byte(t[3]),
                ];
            }
            for j in 0..4 {
                w[i][j] = w[i - 8][j] ^ t[j];
            }
            qsag_asm::volatile_fill(&mut t, 0);
        }
        let mut round_keys = [[0u8; 16]; ROUNDS + 1];
        for (rk, words) in round_keys.iter_mut().zip(w.chunks_exact(4)) {
            for (dst, word) in rk.chunks_exact_mut(4).zip(words) {
                dst.copy_from_slice(word);
            }
        }
        for word in w.iter_mut() {
            qsag_asm::volatile_fill(word, 0);
        }
        Self { round_keys }
    }

    fn encrypt(&self, block: &[u8; 16]) -> [u8; 16] {
        // The state is column-major: byte `r + 4c` is row `r`, column `c`.
        let mut s = *block;
        xor_into(&mut s, &self.round_keys[0]);
        for round in 1..=ROUNDS {
            for b in s.iter_mut() {
                *b = sub_byte(*b);
            }
            let mut t = [0u8; 16];
            for c in 0..4 {
                for r in 0..4 {
                    t[r + 4 * c] = s[r + 4 * ((c + r) % 4)];
                }
            }
            if round != ROUNDS {
                for col in t.chunks_exact_mut(4) {
                    let [a0, a1, a2, a3] = [col[0], col[1], col[2], col[3]];
                    let all = a0 ^ a1 ^ a2 ^ a3;
                    col[0] = a0 ^ all ^ xtime(a0 ^ a1);
                    col[1] = a1 ^ all ^ xtime(a1 ^ a2);
                    col[2] = a2 ^ all ^ xtime(a2 ^ a3);
                    col[3] = a3 ^ all ^ xtime(a3 ^ a0);
                }
            }
            s = t;
            qsag_asm::volatile_fill(&mut t, 0);
            xor_into(&mut s, &self.round_keys[round]);
        }
        s
    }
}

#[inline(always)]
fn xor_into(dst: &mut [u8; 16], src: &[u8; 16]) {
    for (d, s) in dst.iter_mut().zip(src) {
        *d ^= s;
    }
}

/// AES-256 encryption of one block (FIPS 197).
pub fn aes256_encrypt_block(key: &[u8; 32], block: &[u8; 16]) -> [u8; 16] {
    Aes256::new(key).encrypt(block)
}

/// Half the numeral string: `u = v = 44` numerals.
const HALF_BITS: u32 = 44;
const HALF_MASK: u64 = (1 << HALF_BITS) - 1;

/// `NUM_2` of numerals `start .. start + 44`: the first numeral is the most significant.
fn half_to_num(bytes: &[u8; 11], start: usize) -> u64 {
    let mut acc = 0u64;
    for i in start..start + HALF_BITS as usize {
        acc = (acc << 1) | u64::from((bytes[i / 8] >> (i % 8)) & 1);
    }
    acc
}

/// `STR_2^44` of `num` written to numerals `start .. start + 44`.
fn num_to_half(num: u64, bytes: &mut [u8; 11], start: usize) {
    for k in 0..HALF_BITS as usize {
        let i = start + k;
        let bit = ((num >> (HALF_BITS as usize - 1 - k)) & 1) as u8;
        bytes[i / 8] |= bit << (i % 8);
    }
}

/// FF1-AES256 encryption (NIST SP 800-38G, algorithm 7) of an 88-numeral radix-2 string
/// under the empty tweak. `input` and the result are `LEBS2OSP` of the numeral string.
pub fn ff1_aes256_encrypt_88(key: &[u8; 32], input: &[u8; 11]) -> [u8; 11] {
    let aes = Aes256::new(key);
    // b = ceil(44 / 8) = 6, d = 4 * ceil(b / 4) + 4 = 12: one PRF block per round covers S.
    // P = [1, 2, 1] || [radix]^3 || [10] || [u mod 256] || [n]^4 || [t]^4.
    let p: [u8; 16] = [
        1,
        2,
        1,
        0,
        0,
        2,
        10,
        HALF_BITS as u8,
        0,
        0,
        0,
        88,
        0,
        0,
        0,
        0,
    ];
    let mut p_enc = aes.encrypt(&p);
    let mut a = half_to_num(input, 0);
    let mut b = half_to_num(input, HALF_BITS as usize);
    for round in 0..10u8 {
        // Q = [0]^((-t - b - 1) mod 16) || [i]^1 || [NUM_2(B)]^b, here 9 zero bytes.
        let mut q = [0u8; 16];
        q[9] = round;
        q[10..16].copy_from_slice(&b.to_be_bytes()[2..8]);
        xor_into(&mut q, &p_enc);
        let mut r = aes.encrypt(&q);
        // y = NUM(S[..12]); only y mod 2^44 enters c = (NUM_2(A) + y) mod 2^44.
        let y = u64::from_be_bytes([r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11]]);
        let c = a.wrapping_add(y) & HALF_MASK;
        a = b;
        b = c;
        qsag_asm::volatile_fill(&mut q, 0);
        qsag_asm::volatile_fill(&mut r, 0);
    }
    qsag_asm::volatile_fill(&mut p_enc, 0);
    let mut out = [0u8; 11];
    num_to_half(a, &mut out, 0);
    num_to_half(b, &mut out, HALF_BITS as usize);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    fn hex(s: &str) -> Vec<u8> {
        (0..s.len() / 2)
            .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
            .collect()
    }

    fn arr<const N: usize>(s: &str) -> [u8; N] {
        hex(s).try_into().unwrap()
    }

    /// `LEBS2OSP` of a numeral string written as `0`/`1` characters.
    fn bits(s: &str) -> [u8; 11] {
        let mut out = [0u8; 11];
        for (i, ch) in s.bytes().enumerate() {
            out[i / 8] |= (ch - b'0') << (i % 8);
        }
        out
    }

    #[test]
    fn sbox_matches_fips_197_figure_7() {
        // Rows 0 and f, and the worked example {53} -> {ed}, of FIPS 197 figure 7.
        let row0 = hex("637c777bf26b6fc53001672bfed7ab76");
        let rowf = hex("8ca1890dbfe6426841992d0fb054bb16");
        for i in 0..16u8 {
            assert_eq!(sub_byte(i), row0[i as usize]);
            assert_eq!(sub_byte(0xf0 | i), rowf[i as usize]);
        }
        assert_eq!(sub_byte(0x53), 0xed);
        // The S-box is a permutation.
        let mut seen = [false; 256];
        for x in 0..=255u8 {
            seen[sub_byte(x) as usize] = true;
        }
        assert!(seen.iter().all(|&s| s));
    }

    #[test]
    fn aes256_fips_197_appendix_c3() {
        let key = arr("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f");
        let pt = arr("00112233445566778899aabbccddeeff");
        assert_eq!(
            aes256_encrypt_block(&key, &pt).to_vec(),
            hex("8ea2b7ca516745bfeafc49904b496089")
        );
    }

    #[test]
    fn aes256_cavp_vectors() {
        // AESAVS ECBVarTxt256 COUNT = 0 and ECBMCT256 COUNT = 0, as checked by
        // `zcash_test_vectors/ff1.py::test_aes`.
        assert_eq!(
            aes256_encrypt_block(&[0; 32], &arr("80000000000000000000000000000000")).to_vec(),
            hex("ddc6bf790c15760d8d9aeb6f9a75fd4e")
        );
        let key = arr("f9e8389f5b80712e3886cc1fa2d28a3b8c9cd88a2d4a54c6aa86ce0fef944be0");
        let mut acc: [u8; 16] = arr("b379777f9050e2a818f2940cbbd9aba4");
        for _ in 0..1000 {
            acc = aes256_encrypt_block(&key, &acc);
        }
        assert_eq!(acc.to_vec(), hex("6893ebaf0a1fccc704326529fdfb60db"));
    }

    #[test]
    fn ff1_reference_numeral_strings() {
        // The empty-tweak vectors of `zcash_test_vectors/ff1.py::test_ff1` (consistent with
        // the Java reference implementation it cites).
        let key = arr("2b7e151628aed2a6abf7158809cf4f3cef4359d8d580aa4f7f036d6f04fc6a94");
        let c1 = "0000100100110101011101111111110011000001101100111110011101110101011010100100010011001111";
        let c2 = "1101101011010001100011110000010011001111110110011101010110100001111001000101011111011000";
        let x3 = "01".repeat(44);
        let c3 = "0000111101000001111011010111011111110001100101000000001101101110100010010111001100100110";
        assert_eq!(ff1_aes256_encrypt_88(&key, &[0; 11]), bits(c1));
        assert_eq!(ff1_aes256_encrypt_88(&key, &bits(c1)), bits(c2));
        assert_eq!(ff1_aes256_encrypt_88(&key, &bits(&x3)), bits(c3));
    }

    #[test]
    fn ff1_orchard_default_diversifiers() {
        // `dk` -> `default_d` (index 0) of orchard_key_components.json, all ten vectors.
        const V: [(&str, &str); 10] = [
            (
                "31d6a685be570f9faf3ca8b052e887840b2c9f8d67224ca82aefb9e2ee5bedaf",
                "8ff3386971cb64b8e77899",
            ),
            (
                "9d9bd44525e7ae06b03ae6d4aecde6ae0927a7c667d5d9f8176b544695dfec11",
                "7807ca650858814d5022a8",
            ),
            (
                "236bc3f3d02f960280eedede108d3685049f239aa67c48558f7c01d3fd469ecd",
                "6424f71a3ad197426498f4",
            ),
            (
                "803e348573022bf8932f23ee7a325ea283879c652412b8606be3198c4b782c47",
                "db8c305524bc0deaa85d97",
            ),
            (
                "ee19f8ddd9da0634245143c4b43afc7d78c549c82054a9d84007b56217dbfdd6",
                "aae36e094de07bc16f898e",
            ),
            (
                "d0baef6012d308efbb769a99cca2928cede8db277645a777eaf1722cd08450b3",
                "cc7ce734b075a01b92aaca",
            ),
            (
                "5e5b60c05b53d0bcd2da46a1312912515cc7cf2d974c117c8ddea9fab620c668",
                "99af6bf3f475bde889aaca",
            ),
            (
                "5d7fe396bbfd2267aca711ab5b3e1f024f4911f3a181732f1322a1592f9e0ebe",
                "2fbe4b4b1edff33123ce65",
            ),
            (
                "02f07408f33e8712e4c9ec42de5604200109861724d33eb6368b70f65e0a1621",
                "08df1d4b45c673a459ff58",
            ),
            (
                "3df583361b3338bb6815f85872e39f04df5008524884af0f8c559716fcb14958",
                "4c4064c47a5ca6e75d4644",
            ),
        ];
        for (dk, d) in V {
            assert_eq!(ff1_aes256_encrypt_88(&arr(dk), &[0; 11]).to_vec(), hex(d));
        }
    }

    #[test]
    fn ff1_sapling_zip32_diversifiers() {
        // `dk` with `d0`, `d1`, `d2`, `dmax` of sapling_zip32.json (indices 0, 1, 2 and
        // 2^88 - 1; the file has `null` where DiversifyHash rejects the diversifier).
        const V: [(&str, [Option<&str>; 4]); 4] = [
            (
                "77c17cb75b7796afb39f0f3e91c924607da56fa9a20e283509bc8a3ef996a172",
                [
                    Some("d8621b981cf300e9d4cc89"),
                    Some("48ea17a199c84bd1baa5d4"),
                    None,
                    None,
                ],
            ),
            (
                "e04de832a2d791ec129ab9002b91c9e9cdeed79241a7c4960e5178d870c1b4dc",
                [
                    Some("8b4138320dfafd7b399781"),
                    None,
                    Some("5749a13352bc223e308078"),
                    Some("6389574cde0fbbc6368131"),
                ],
            ),
            (
                "a3eda19f9eff46ca12dfa1bf10371b48d1b4a40c4d05a0d8dce0e7dc62b07b37",
                [
                    Some("e8d03793cdd2bacc9c7041"),
                    Some("020a7a6b0bf84d3e899f68"),
                    None,
                    None,
                ],
            ),
            (
                "becb50c363bb2ed9da5c3043ceb0f1a0527bf836b29a35f7c0c9f261123be56e",
                [
                    None,
                    Some("030ffb263a939e230e96dd"),
                    Some("7bbf63934c7e92670cdb55"),
                    Some("1a730feb0059cf1f5bdea8"),
                ],
            ),
        ];
        let mut one = [0u8; 11];
        one[0] = 1;
        let mut two = [0u8; 11];
        two[0] = 2;
        let indices = [[0u8; 11], one, two, [0xff; 11]];
        let mut checked = 0;
        for (dk, ds) in V {
            for (index, d) in indices.iter().zip(ds) {
                if let Some(d) = d {
                    assert_eq!(ff1_aes256_encrypt_88(&arr(dk), index).to_vec(), hex(d));
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 10);
    }

    #[test]
    fn ff1_is_a_permutation_on_distinct_inputs() {
        let key = [7u8; 32];
        let mut a = [0u8; 11];
        a[10] = 0x80;
        assert_ne!(
            ff1_aes256_encrypt_88(&key, &a),
            ff1_aes256_encrypt_88(&key, &[0; 11])
        );
        assert_ne!(
            ff1_aes256_encrypt_88(&key, &a),
            ff1_aes256_encrypt_88(&[8u8; 32], &a)
        );
    }
}
