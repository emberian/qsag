//! FIPS 203 ML-KEM-768 with canonical residues throughout the NTT.
use super::TransportError;
use qsag_core::sponge::keccak::keccak_f1600;
use qsag_core::wipe::{SecretBuffer, SecretBytes, ct_eq_bytes, ct_select_bytes32};

const Q: u16 = 3329;
pub(super) const EK_BYTES: usize = 1184;
pub(super) const CT_BYTES: usize = 1088;
type Poly = SecretBuffer<[u16; 256]>;
type Vector = [Poly; 3];

const fn ct_mod_3329(z: u32) -> u16 {
    let quotient = ((z as u64) * 20_642_679) >> 36;
    (z - quotient as u32 * 3329) as u16
}
fn add(a: u16, b: u16) -> u16 {
    ct_mod_3329(u32::from(a + b))
}
fn sub(a: u16, b: u16) -> u16 {
    ct_mod_3329(u32::from(a + Q - b))
}
const fn mul(a: u16, b: u16) -> u16 {
    ct_mod_3329(a as u32 * b as u32)
}
fn ct_compress<const D: u32>(x: u16) -> u16 {
    let quotient = (((u64::from(x) << D) + 1664) * 20_642_679) >> 36;
    (quotient as u16) & ((1 << D) - 1)
}
fn ct_decompress<const D: u32>(y: u16) -> u16 {
    ((u32::from(y) * 3329 + (1 << (D - 1))) >> D) as u16
}

// FIPS 203 uses SHA3-512 for G, SHA3-256 for H, SHAKE256 for PRF and J,
// and an unbounded SHAKE128 stream for the public matrix.
struct Sponge<const RATE: usize> {
    state: SecretBuffer<[u64; 25]>,
    offset: usize,
}
impl<const RATE: usize> Sponge<RATE> {
    fn new(parts: &[&[u8]], suffix: u8) -> Self {
        let mut state = SecretBuffer([0; 25]);
        let mut offset = 0;
        for part in parts {
            for &byte in *part {
                state[offset >> 3] ^= u64::from(byte) << ((offset & 7) * 8);
                offset += 1;
                if offset == RATE {
                    keccak_f1600(&mut state);
                    offset = 0;
                }
            }
        }
        state[offset >> 3] ^= u64::from(suffix) << ((offset & 7) * 8);
        state[(RATE - 1) >> 3] ^= 1 << 63;
        keccak_f1600(&mut state);
        Self { state, offset: 0 }
    }
    fn read(&mut self, out: &mut [u8]) {
        for byte in out {
            if self.offset == RATE {
                keccak_f1600(&mut self.state);
                self.offset = 0;
            }
            *byte = (self.state[self.offset >> 3] >> ((self.offset & 7) * 8)) as u8;
            self.offset += 1;
        }
    }
}

fn hash<const RATE: usize, const N: usize>(parts: &[&[u8]], suffix: u8) -> SecretBytes<N> {
    let mut out = SecretBuffer([0; N]);
    Sponge::<RATE>::new(parts, suffix).read(&mut out[..]);
    out
}

const ZETAS: [u16; 128] = {
    let mut roots = [0; 128];
    let mut x = 1;
    let mut i = 0u8;
    while i < 128 {
        roots[(i.reverse_bits() >> 1) as usize] = x;
        x = mul(x, 17);
        i += 1;
    }
    roots
};

fn ntt(p: &mut Poly) {
    let mut k = 1;
    for shift in (1..=7).rev() {
        let len = 1 << shift;
        for block in p.chunks_exact_mut(2 * len) {
            let (left, right) = block.split_at_mut(len);
            for (a, b) in left.iter_mut().zip(right) {
                let t = mul(ZETAS[k], *b);
                *b = sub(*a, t);
                *a = add(*a, t);
            }
            k += 1;
        }
    }
}

fn inverse(p: &mut Poly) {
    let mut k = 127;
    for shift in 1..=7 {
        let len = 1 << shift;
        for block in p.chunks_exact_mut(2 * len) {
            let (left, right) = block.split_at_mut(len);
            for (a, b) in left.iter_mut().zip(right) {
                let diff = sub(*b, *a);
                *a = add(*a, *b);
                *b = mul(ZETAS[k], diff);
            }
            k -= 1;
        }
    }
    for a in p.iter_mut() {
        *a = mul(*a, 3303);
    }
}

fn accumulate(out: &mut Poly, a: &Poly, b: &Poly) {
    for i in 0..128 {
        let root = ZETAS[64 + (i >> 1)];
        let gamma = if i & 1 == 0 { root } else { Q - root };
        let j = 2 * i;
        out[j] = add(
            out[j],
            add(mul(a[j], b[j]), mul(mul(a[j + 1], b[j + 1]), gamma)),
        );
        out[j + 1] = add(out[j + 1], add(mul(a[j], b[j + 1]), mul(a[j + 1], b[j])));
    }
}

fn matrix(rho: &[u8], row: usize, col: usize) -> Poly {
    let mut stream = Sponge::<168>::new(&[rho, &[col as u8, row as u8]], 0x1f);
    let mut out = SecretBuffer([0; 256]);
    let mut pos = 0;
    while pos < 256 {
        let mut triple = [0; 3];
        stream.read(&mut triple);
        let [a, b, c] = triple.map(u16::from);
        for d in [a + ((b & 15) << 8), (b >> 4) + (c << 4)] {
            if d < Q && pos < 256 {
                out[pos] = d;
                pos += 1;
            }
        }
    }
    out
}

fn noise(seed: &[u8], nonce: u8) -> Poly {
    let bytes = hash::<136, 128>(&[seed, &[nonce]], 0x1f);
    SecretBuffer(core::array::from_fn(|i| {
        let x = bytes[i >> 1] >> ((i & 1) * 4);
        sub(
            u16::from((x & 1) + ((x >> 1) & 1)),
            u16::from(((x >> 2) & 1) + ((x >> 3) & 1)),
        )
    }))
}

fn noise_ntt(seed: &[u8], nonce: u8) -> Poly {
    let mut p = noise(seed, nonce);
    ntt(&mut p);
    p
}

fn pack<const D: usize>(p: &Poly, out: &mut [u8], encode: fn(u16) -> u16) {
    out.fill(0);
    for (i, x) in p.iter().copied().map(encode).enumerate() {
        for bit in 0..D {
            let j = i * D + bit;
            out[j >> 3] |= (((x >> bit) & 1) as u8) << (j & 7);
        }
    }
}
fn unpack<const D: usize>(input: &[u8], decode: fn(u16) -> u16) -> Poly {
    SecretBuffer(core::array::from_fn(|i| {
        let mut x = 0;
        for bit in 0..D {
            let j = i * D + bit;
            x |= u16::from((input[j >> 3] >> (j & 7)) & 1) << bit;
        }
        decode(x)
    }))
}

pub(super) struct DecapsulationKey {
    s: Vector,
    pub(super) ek: [u8; EK_BYTES],
    z: SecretBytes<32>,
}

pub(super) fn keygen(d: &[u8; 32], z: SecretBytes<32>) -> DecapsulationKey {
    let seeds = hash::<72, 64>(&[d, &[3]], 6);
    let (rho, sigma) = seeds.split_at(32);
    let s: Vector = core::array::from_fn(|j| noise_ntt(sigma, j as u8));
    let mut ek = [0; EK_BYTES];
    for i in 0..3 {
        let mut t = noise_ntt(sigma, (i + 3) as u8);
        for (j, sj) in s.iter().enumerate() {
            accumulate(&mut t, &matrix(rho, i, j), sj);
        }
        pack::<12>(&t, &mut ek[384 * i..384 * (i + 1)], core::convert::identity);
    }
    ek[1152..].copy_from_slice(rho);
    DecapsulationKey { s, ek, z }
}

fn encrypt(
    ek: &[u8; EK_BYTES],
    message: &[u8; 32],
    coins: &[u8],
) -> Result<[u8; CT_BYTES], TransportError> {
    let rho = &ek[1152..];
    let y: Vector = core::array::from_fn(|i| noise_ntt(coins, i as u8));
    let mut ct = [0; CT_BYTES];
    let mut v = SecretBuffer([0; 256]);
    for i in 0..3 {
        let t = unpack::<12>(&ek[i * 384..(i + 1) * 384], core::convert::identity);
        // Canonical modulus check on the received public encapsulation key.
        if t.iter().any(|&x| x >= Q) {
            return Err(TransportError::AuthenticationFailed);
        }
        accumulate(&mut v, &t, &y[i]);
        let mut u = SecretBuffer([0; 256]);
        for (j, yj) in y.iter().enumerate() {
            accumulate(&mut u, &matrix(rho, j, i), yj);
        }
        inverse(&mut u);
        let e = noise(coins, (i + 3) as u8);
        for (x, y) in u.iter_mut().zip(e.iter()) {
            *x = add(*x, *y);
        }
        pack::<10>(&u, &mut ct[320 * i..320 * (i + 1)], ct_compress::<10>);
    }
    inverse(&mut v);
    let e = noise(coins, 6);
    let m = unpack::<1>(message, ct_decompress::<1>);
    for i in 0..256 {
        v[i] = add(v[i], add(e[i], m[i]));
    }
    pack::<4>(&v, &mut ct[960..], ct_compress::<4>);
    Ok(ct)
}

pub(super) fn encapsulate(
    ek: &[u8; EK_BYTES],
    m: &[u8; 32],
) -> Result<([u8; CT_BYTES], SecretBytes<32>), TransportError> {
    let h = hash::<136, 32>(&[ek], 6);
    let kr = hash::<72, 64>(&[m, &h[..]], 6);
    let ct = encrypt(ek, m, &kr[32..])?;
    Ok((ct, SecretBuffer(core::array::from_fn(|i| kr[i]))))
}

impl DecapsulationKey {
    pub(super) fn decapsulate(
        &self,
        ct: &[u8; CT_BYTES],
    ) -> Result<SecretBytes<32>, TransportError> {
        let mut dot = SecretBuffer([0; 256]);
        for (i, si) in self.s.iter().enumerate() {
            let mut u = unpack::<10>(&ct[i * 320..(i + 1) * 320], ct_decompress::<10>);
            ntt(&mut u);
            accumulate(&mut dot, si, &u);
        }
        inverse(&mut dot);
        let mut v = unpack::<4>(&ct[960..], ct_decompress::<4>);
        for i in 0..256 {
            v[i] = sub(v[i], dot[i]);
        }
        let mut m = SecretBuffer([0; 32]);
        pack::<1>(&v, &mut m[..], ct_compress::<1>);
        let (check, accept) = encapsulate(&self.ek, &m)?;
        let reject = hash::<136, 32>(&[&self.z[..], ct], 0x1f);
        Ok(SecretBuffer(ct_select_bytes32(
            ct_eq_bytes(&check, ct),
            &accept,
            &reject,
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex<const N: usize>(s: &str) -> [u8; N] {
        assert_eq!(s.len(), 2 * N);
        core::array::from_fn(|i| u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).unwrap())
    }
    // NIST ACVP-Server FIPS203 internalProjection, ML-KEM-768 first keygen
    // and encapsulation cases. The long expected byte strings are hashed.
    #[test]
    fn nist_acvp_known_answers_and_implicit_rejection() {
        let dk = keygen(
            &hex("E582B7D75E6C80B05AE392A1FC9F7153B12390FD99930368CC67A768BAEBC8A0"),
            SecretBuffer(hex(
                "1CDACB8740C0B87C4A379575F187B367CBFA3B300BF591B109F79816E9CBE8F0",
            )),
        );
        assert_eq!(
            *hash::<136, 32>(&[&dk.ek], 6),
            hex("81e66ef5a7a221619f6a64039cc369843e10df5c859f6959cc3fd8e5272330fd")
        );
        let ek = hex(concat!(
            "9C6839354086919BC7B8A547FF18B523075FD1706856400952489E4CD13ED8B17A817A3076E0947B",
            "860EC9558BD9D3C94DF5418A7A7301763999C09996715CE32AACFEF767A44969925949CC9B8120CB",
            "78953BCF6FB8282427CB3F4CBBC50AB23274493A8BA7E5C09088160FDA731B55980867912BAC5312",
            "5B27073BB502AFAC5E74973E0F3601DC50CE08CC7F3FA44CE331A43F9673BE745295E693077264A8",
            "E238F0A912C0A59C44D561E2A8BD831541FE869B3110B051100DB3517F87510ECAD8651CE4998BB6",
            "48002BA41A5351FA2A4ED94A58CB707214A59F8876176CF82FCEB99364971C7C0896E8B62C054446",
            "3FF101983C2045981CCD9173EB33BA18483ED915BD11EA950DB3A8787C105263242E3A64C748B8B1",
            "A5947880C5BF3896E08B4B9916A39FD70C2FF8BD041A2B18E251D16A276E38100A613EA96A86CB36",
            "52DCC83F2D31CD9F8B79E42541A66752D191436CF5B5D8350EE7835CDB122855392C1DA5C33FDA12",
            "AD1028F2806861A2AB9C63785FD11E220346322C250936AB819254734A8DC9241971AC90CDA6696A",
            "DB90D1E327DC977841ABA38324C8FB2092784942003A0808E5546D034592F03BACC19E3138C9070C",
            "CEA80A933D536C49E4771091AF8A70207D474574C64B9F1C8E47224174061117E98C18897A7B1B3C",
            "4478C6558C321A89A84B6C508947CB61C89204FBCA43BCAA1D688F768B02E50BABEBF0C5FB8962B2",
            "355973C4193FA92E0CE4B9F8473E154828C986BF63E1CD985C6F0462C9B4374594D226C5E99B8A84",
            "4978DB8DD2839E27138AACF75E917635CEC4B407A54F184C22F62981B9F4552FB334FF2B7FF68B47",
            "0FD61B993C32581CC0F39881A5A6A769A60297F4B0579ACBF52A8ABB143885886245CA2636E20498",
            "959E4F2857AB96706E6409C4164BA88C7193E568E4446120215A6D8499C6B4BC559628A9F481C7DB",
            "51E2E10DF1F4339A647B4CCC0405B79F70A90CA9A8AD07789222BA6E66C3AFF42B61BAA637AF1512",
            "6C88B2E210A7CAD9CB08CBB5123A7F9BB4AD63DAAEA6B43F9AABA561212823CB898A676C967B2D64",
            "F4B6333439F8993BD7B19687248926E077A9700431A59157B9668EE022B6D31343F15C08F1448887",
            "7DFB30A552C06F96A16F354B9A3F19090B32A043B43256BA5B1088B56A4125588C8746D4099EA21C",
            "4F33AD8C5C7C32286DEE2CA76FC2651D57AEE9D847824AC609B5BFD5C87316C2AFE0E153D6326AF8",
            "9987ECB70CF0A0A77FA000E0E0ACC2685E2317429C3A7513F42873CB98F669703AE9146919226DB5",
            "8D6C2B93B6F50C7CDAB677B505945A0F2523886C1B82A6A7CC7EBA9251096D88360D7EF6473ACBCD",
            "359A0D20414B95C209B2413B1483A3A061386377B28E3896BCD8C5E2692681CC803E1694EFB6CE35",
            "3082FFCA4079EA9BB7B2025BCB68990466ED2803AB11516D80325DC4CDE3DA9E020653E084C45F83",
            "7C88711DF3AA6075741C1283121C8B1C691013969A62B2563E556206CF0810848691C7C408D01861",
            "7A7300AD943E189A9B44512EF13B669831392F1329E2AC7C623AA044223079139B7F1C213E93682E",
            "D86165468377D40884310163A5539F27745E667ADF506896BA933B002E4D50B2497ECFF09D0BBCA4",
            "F7E6F9DB9E10C643D23701BD6385E163CF71C1E919A6E20A",
        ));
        let m = hex("4E77596168711E913965D8175AC3BD76AAB08B7F9385A02AE883CF6C6E17DD81");
        let (c, k) = encapsulate(&ek, &m).unwrap();
        assert_eq!(
            *k,
            hex("79D74F6C6C2D916BEC47BD828FD9B67295A37F54927FAB1263C0D122F1C6F1ED")
        );
        assert_eq!(
            *hash::<136, 32>(&[&c], 6),
            hex("684da17d93e27520cb78ae6169c020d73ef770e6fa89589cc7d653a76a8b1751")
        );
        let (mut c, k) = encapsulate(&dk.ek, &m).unwrap();
        assert_eq!(*dk.decapsulate(&c).unwrap(), *k);
        c[0] ^= 1;
        assert_eq!(
            *dk.decapsulate(&c).unwrap(),
            *hash::<136, 32>(&[&dk.z[..], &c], 0x1f)
        );
    }
}
