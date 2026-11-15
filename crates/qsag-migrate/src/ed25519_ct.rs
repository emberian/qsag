//! RFC 8032 extended Edwards arithmetic over 2^255 - 19.
//! Fixed loop bounds and masked table selection; timing needs host validation.
use crate::limbs;
use qsag_accel::ct::{ct_eq_u64, ct_zeroize_u64s};

const MASK: u64 = (1 << 51) - 1;
const PRIME: [u64; 5] = [MASK - 18, MASK, MASK, MASK, MASK];

struct Field([u64; 5]);

impl Drop for Field {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}

impl Field {
    fn reduce(mut wide: [u128; 5]) -> Self {
        // Three complete carry sweeps bound every limb, including the wrap by 19.
        for _ in 0..3 {
            let mut carry = 0;
            for limb in &mut wide {
                *limb += carry;
                carry = *limb >> 51;
                *limb &= MASK as u128;
            }
            wide[0] += carry * 19;
        }
        let value = wide.map(|x| x as u64);
        let mut diff = [0u64; 5];
        let mut borrow = 0u64;
        for ((slot, &x), &p) in diff.iter_mut().zip(&value).zip(&PRIME) {
            let d = x.wrapping_sub(p + borrow);
            borrow = d >> 63;
            *slot = d & MASK;
        }
        Self(limbs::ct_select(borrow == 0, diff, value))
    }

    fn add(&self, rhs: &Self) -> Self {
        Self::reduce(core::array::from_fn(|i| {
            self.0[i] as u128 + rhs.0[i] as u128
        }))
    }

    fn sub(&self, rhs: &Self) -> Self {
        Self::reduce(core::array::from_fn(|i| {
            self.0[i] as u128 + 2 * PRIME[i] as u128 - rhs.0[i] as u128
        }))
    }

    fn mul(&self, rhs: &Self) -> Self {
        let mut wide = [0u128; 5];
        for (i, &a) in self.0.iter().enumerate() {
            for (j, &b) in rhs.0.iter().enumerate() {
                let factor = if i + j >= 5 { 19 } else { 1 };
                wide[(i + j) % 5] += a as u128 * b as u128 * factor;
            }
        }
        Self::reduce(wide)
    }

    fn inverse(&self) -> Self {
        // Public fixed exponent p - 2 = 2^255 - 21.
        let mut acc = Self([1, 0, 0, 0, 0]);
        for bit in (0..255).rev() {
            acc = acc.mul(&acc);
            let product = acc.mul(self);
            let take = bit >= 5 || ((0x0bu8 >> bit) & 1) != 0;
            acc = Self::select(take, &product, &acc);
        }
        acc
    }

    fn select(take: bool, yes: &Self, no: &Self) -> Self {
        Self(limbs::ct_select(take, yes.0, no.0))
    }

    fn limbs(&self) -> [u64; 4] {
        let x = &self.0;
        [
            x[0] | (x[1] << 51),
            (x[1] >> 13) | (x[2] << 38),
            (x[2] >> 26) | (x[3] << 25),
            (x[3] >> 39) | (x[4] << 12),
        ]
    }

    fn bytes(&self) -> [u8; 32] {
        limbs::to_le_bytes(self.limbs())
    }
}

struct Point {
    x: Field,
    y: Field,
    z: Field,
    t: Field,
}

impl Point {
    fn identity() -> Self {
        Self {
            x: Field([0; 5]),
            y: Field([1, 0, 0, 0, 0]),
            z: Field([1, 0, 0, 0, 0]),
            t: Field([0; 5]),
        }
    }

    fn add(&self, rhs: &Self) -> Self {
        let a = self.y.sub(&self.x).mul(&rhs.y.sub(&rhs.x));
        let b = self.y.add(&self.x).mul(&rhs.y.add(&rhs.x));
        let c = self.t.mul(&rhs.t).mul(&Field(DOUBLE_D));
        let zz = self.z.mul(&rhs.z);
        let d = zz.add(&zz);
        let e = b.sub(&a);
        let f = d.sub(&c);
        let g = d.add(&c);
        let h = b.add(&a);
        Self {
            x: e.mul(&f),
            y: g.mul(&h),
            z: f.mul(&g),
            t: e.mul(&h),
        }
    }

    fn select(take: bool, yes: &Self, no: &Self) -> Self {
        Self {
            x: Field::select(take, &yes.x, &no.x),
            y: Field::select(take, &yes.y, &no.y),
            z: Field::select(take, &yes.z, &no.z),
            t: Field::select(take, &yes.t, &no.t),
        }
    }
}

/// Multiply the RFC 8032 base point by a little-endian scalar and encode y with x parity.
pub fn public_key_from_clamped_scalar(scalar: &[u8; 32]) -> [u8; 32] {
    let mut acc = Point::identity();
    for &byte in scalar.iter().rev() {
        for nibble in [byte >> 4, byte & 15] {
            for _ in 0..4 {
                acc = acc.add(&acc);
            }
            let mut selected = Point::identity();
            for (index, coords) in BASE_TABLE.iter().enumerate() {
                let candidate = Point {
                    x: Field(coords[0]),
                    y: Field(coords[1]),
                    z: Field([1, 0, 0, 0, 0]),
                    t: Field(coords[2]),
                };
                selected = Point::select(
                    ct_eq_u64(index as u64, nibble as u64),
                    &candidate,
                    &selected,
                );
            }
            acc = acc.add(&selected);
        }
    }
    let inverse = acc.z.inverse();
    let x = acc.x.mul(&inverse);
    let y = acc.y.mul(&inverse);
    let mut out = y.bytes();
    out[31] |= ((x.0[0] & 1) as u8) << 7;
    out
}

const DOUBLE_D: [u64; 5] = [
    1859910466990425,
    932731440258426,
    1072319116312658,
    1815898335770999,
    633789495995903,
];
const BASE_TABLE: [[[u64; 5]; 3]; 16] = [
    [[0, 0, 0, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
    [
        [
            1738742601995546,
            1146398526822698,
            2070867633025821,
            562264141797630,
            587772402128613,
        ],
        [
            1801439850948184,
            1351079888211148,
            450359962737049,
            900719925474099,
            1801439850948198,
        ],
        [
            1841354044333475,
            16398895984059,
            755974180946558,
            900171276175154,
            1821297809914039,
        ],
    ],
    [
        [
            1584731938606606,
            178923850428536,
            228280466683449,
            622454613327500,
            961744189650336,
        ],
        [
            2048039769908169,
            611908456202699,
            1838921828590653,
            1373353662182500,
            604786679386674,
        ],
        [
            632586093835265,
            343317749454563,
            1142187722401459,
            1246910387029049,
            643809026290422,
        ],
    ],
    [
        [
            642526368817756,
            897391692666252,
            962214031593056,
            2151263124273695,
            1823994305194280,
        ],
        [
            959085406434516,
            823416103927896,
            169856804346800,
            1360991708301104,
            323785187622630,
        ],
        [
            291346836595738,
            421537610553791,
            1939901930052822,
            712990200152534,
            744163847642585,
        ],
    ],
    [
        [
            745845847357552,
            55498538281255,
            233662937943675,
            179502033034301,
            567187168652543,
        ],
        [
            188436492456239,
            1791404585917415,
            938732500011168,
            827535094727360,
            1263401179066713,
        ],
        [
            2008766715925336,
            1080663717006321,
            546068614240140,
            851266986915171,
            606396996224818,
        ],
    ],
    [
        [
            172349289591347,
            2014045392908840,
            1326661600583783,
            1194063046802408,
            1301660503301685,
        ],
        [
            597601052707053,
            370708851696154,
            1769224146297019,
            2031829141359172,
            1676215595929578,
        ],
        [
            370247452852688,
            175926773542019,
            1366829968581946,
            1871474830157891,
            2047038905238931,
        ],
    ],
    [
        [
            690607081910845,
            85278329204487,
            1170597539714662,
            15605081464942,
            1347423509652566,
        ],
        [
            697987907550964,
            231488761894970,
            1475501116163568,
            1214474405336062,
            93313529186413,
        ],
        [
            1925007367139794,
            720797401577721,
            2145641378528840,
            43711000824999,
            1059031511767718,
        ],
    ],
    [
        [
            1574616431476999,
            1820233879956234,
            1255659963129895,
            1872970577808549,
            357789706735435,
        ],
        [
            1342184246764216,
            245145966977624,
            1366370960941229,
            729817606665326,
            875581666407549,
        ],
        [
            1483611988028699,
            1481949820256791,
            2065891370619276,
            1985503051571908,
            309956969615717,
        ],
    ],
    [
        [
            2249308877718728,
            2093526803490672,
            346613787454233,
            240935905963644,
            1816591146253687,
        ],
        [
            2071110476085684,
            2124547928253381,
            611114757251315,
            488970596615347,
            595043560496727,
        ],
        [
            1957245925085631,
            1590484463955447,
            790988240438073,
            1531117259804060,
            779509163810686,
        ],
    ],
    [
        [
            38510044475740,
            991526491691644,
            1777407289417785,
            196322847846455,
            940961149255687,
        ],
        [
            1764185014989248,
            673372631865577,
            1067952015008320,
            1964111621420203,
            2238409115184592,
        ],
        [
            906476616086629,
            1159907563785095,
            1441690873155410,
            1685472728012539,
            1626245419673724,
        ],
    ],
    [
        [
            1441606988724559,
            522297534482578,
            829142841031225,
            1894055753221993,
            1691906130250918,
        ],
        [
            128301056686892,
            184426382784337,
            671798326057626,
            628802307140196,
            1750421616435634,
        ],
        [
            2054527727158846,
            1854288320309372,
            1919051480946343,
            362032992387460,
            965396763404085,
        ],
    ],
    [
        [
            2202051752555467,
            1786373445672933,
            497601544586902,
            575986915854059,
            367591404164286,
        ],
        [
            2020642157442835,
            993492693845521,
            1121773387604324,
            1631319708561824,
            801578924896794,
        ],
        [
            1635175039233748,
            1051347747536240,
            99741981736967,
            1215084455223161,
            1599146621927666,
        ],
    ],
    [
        [
            842666022572077,
            1249836144285132,
            713752375351036,
            1858928010358790,
            1250823726175973,
        ],
        [
            705732620969209,
            1840919398377082,
            1654313513984506,
            19188013213489,
            1133651887176936,
        ],
        [
            1340384370957515,
            160027838347965,
            2027506894666691,
            1214480183317528,
            760058384458885,
        ],
    ],
    [
        [
            246787608698861,
            1426772414891760,
            198742064041871,
            957045848602644,
            289457140752182,
        ],
        [
            2218466207604608,
            1764798922780925,
            961140144014142,
            1612142334710121,
            331756173448504,
        ],
        [
            1368676840124243,
            630457475500613,
            1504736984191657,
            616151183700198,
            1146242676653030,
        ],
    ],
    [
        [
            1815653225141689,
            852977021965425,
            891619496917915,
            1503591919338670,
            569494211614852,
        ],
        [
            560306562279481,
            1410908648345709,
            1930789639758435,
            1619077536202085,
            1377698118437964,
        ],
        [
            911686843351776,
            2248280234529058,
            843952043826445,
            1978877509722014,
            1799019282446983,
        ],
    ],
    [
        [
            421380963274177,
            1845943409930764,
            1267764746882125,
            592560219454638,
            1391306851926764,
        ],
        [
            1491782486351071,
            866635604046477,
            926118541760188,
            416339927466162,
            330676827082738,
        ],
        [
            1547233456733993,
            559107513688705,
            1645107965693658,
            643032076423456,
            1657234620902263,
        ],
    ],
];

/// Canonical four-limb arithmetic adapter for the mixed-domain circuit.
pub(crate) fn multiply_limbs(a: [u64; 4], b: [u64; 4]) -> [u64; 4] {
    fn field(x: [u64; 4]) -> Field {
        Field(core::array::from_fn(|i| {
            let offset = i * 51;
            let limb = offset / 64;
            let shift = offset % 64;
            let low = x[limb] >> shift;
            let high = if shift != 0 && limb + 1 < 4 {
                x[limb + 1] << (64 - shift)
            } else {
                0
            };
            (low | high) & MASK
        }))
    }
    field(a).mul(&field(b)).limbs()
}

pub(crate) fn circuit_base_table() -> [[[u64; 4]; 4]; 16] {
    BASE_TABLE.map(|coords| {
        let x = limbs::from_le_bytes(&Field(coords[0]).bytes());
        let y = limbs::from_le_bytes(&Field(coords[1]).bytes());
        let t = limbs::from_le_bytes(&Field(coords[2]).bytes());
        [x, y, [1, 0, 0, 0], t]
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LegacyCommitmentKind, LegacyOwnershipWitness};

    fn bytes(hex: &str) -> [u8; 32] {
        let mut out = [0; 32];
        for (slot, pair) in out.iter_mut().zip(hex.as_bytes().chunks_exact(2)) {
            let digit = |c: u8| if c <= b'9' { c - b'0' } else { c - b'a' + 10 };
            *slot = (digit(pair[0]) << 4) | digit(pair[1]);
        }
        out
    }

    #[test]
    fn rfc8032_public_keys() {
        for (seed, expected) in [
            (
                "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            ),
            (
                "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            ),
        ] {
            let witness = LegacyOwnershipWitness::from_raw_secret(bytes(seed));
            assert_eq!(
                witness.compute_slip0010_commitment(),
                LegacyCommitmentKind::Slip0010Ed25519(bytes(expected))
            );
        }
    }

    #[test]
    fn field_boundaries_and_base_encoding() {
        let minus_one = Field([MASK - 19, MASK, MASK, MASK, MASK]);
        assert_eq!(minus_one.add(&Field([1, 0, 0, 0, 0])).0, [0; 5]);
        assert_eq!(minus_one.mul(&minus_one).0, [1, 0, 0, 0, 0]);
        let mut scalar = [0; 32];
        scalar[0] = 1;
        assert_eq!(
            public_key_from_clamped_scalar(&scalar),
            bytes("5866666666666666666666666666666666666666666666666666666666666666")
        );
    }
}
