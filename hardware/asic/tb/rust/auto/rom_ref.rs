// Instruction-level differential oracle. Arithmetic and sponge operations use
// qsag-agg, independent of the RTL. This is for diagnosis, not RTL evidence.
use qsag_agg::{
    field::Goldilocks as F,
    hem_quintic::QuinticFp5 as E,
    sponge::{keccak_p1600_12, turboshake256_static_midstate},
};
use std::fs;
const ROM: usize = 0x200000;
fn sext(x: u64, n: u32) -> u64 {
    (((x << (64 - n)) as i64) >> (64 - n)) as u64
}
fn load(mem: &[u8], addr: usize, n: usize) -> u64 {
    let mut b = [0; 8];
    b[..n].copy_from_slice(&mem[addr..addr + n]);
    u64::from_le_bytes(b)
}
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let proof = fs::read(&args[1]).unwrap();
    let mut desc = fs::read(&args[2]).unwrap();
    let expected = match &args[3..] {
        [] => true,
        [flag, offset] if flag == "--flip-desc" => {
            let index: usize = offset.parse().unwrap();
            desc[index] ^= 1;
            false
        }
        _ => panic!("expected proof descriptor [--flip-desc offset]"),
    };
    let rom: Vec<u8> = fs::read_to_string("rtl/auto/verifier.hex")
        .unwrap()
        .lines()
        .flat_map(|x| u64::from_str_radix(x, 16).unwrap().to_le_bytes())
        .collect();
    assert!(matches!(rom.len(), 16384 | 32768));
    let mut ram = vec![0u8; 524288];
    ram[..proof.len()].copy_from_slice(&proof);
    let d = (proof.len() + 15) / 8 * 8;
    ram[d..d + desc.len()].copy_from_slice(&desc);
    let mut g = [0u64; 32];
    g[11] = proof.len() as u64;
    g[14] = g[11];
    g[12] = d as u64;
    g[13] = ram.len() as u64;
    let mut pc = ROM;
    let mut p2 = [F::ZERO; 12];
    let mut k = [0; 25];
    let mut checks = 0;
    let mut guard = ram.len();
    let mut min_sp = ram.len();
    let mut history = [0; 16];
    let mut instructions = 0;
    let fs = |x| F::from_u64_reduced(x);
    loop {
        let ins = load(&rom, pc - ROM, 4);
        let op = ins & 127;
        let rd = (ins >> 7 & 31) as usize;
        let f = ins >> 12 & 7;
        let x = g[(ins >> 15 & 31) as usize];
        let y = g[(ins >> 20 & 31) as usize];
        let ff = ins >> 25;
        let imm = sext(ins >> 20, 12);
        let mut next = pc + 4;
        let mut value = None;
        history[instructions % 16] = pc;
        instructions += 1;
        match op {
            0x37 | 0x17 => {
                value = Some(sext(ins & 0xfffff000, 32).wrapping_add(if op == 0x17 {
                    pc as u64
                } else {
                    0
                }))
            }
            0x33 | 0x13 | 0x3b | 0x1b => {
                let b = if op & 32 != 0 { y } else { imm };
                let word = op & 8 != 0;
                let n = b & if word { 31 } else { 63 };
                let z = match f {
                    0 => {
                        if op & 32 != 0 && ff == 32 {
                            x.wrapping_sub(b)
                        } else {
                            x.wrapping_add(b)
                        }
                    }
                    1 => x << n,
                    2 => u64::from((x as i64) < (b as i64)),
                    3 => u64::from(x < b),
                    4 => x ^ b,
                    5 => {
                        if ins >> 30 & 1 == 0 {
                            (if word { x as u32 as u64 } else { x }) >> n
                        } else {
                            ((if word { x as i32 as i64 } else { x as i64 }) >> n) as u64
                        }
                    }
                    6 => x | b,
                    _ => x & b,
                };
                value = Some(if word { sext(z, 32) } else { z });
            }
            0x03 => {
                let a = x.wrapping_add(imm) as usize;
                let n = 1 << (f & 3);
                let z = if a >= ROM {
                    load(&rom, a - ROM, n)
                } else {
                    load(&ram, a, n)
                };
                value = Some(if f < 4 { sext(z, (8 * n) as u32) } else { z });
            }
            0x23 => {
                let a = x.wrapping_add(sext(ff << 5 | rd as u64, 12)) as usize;
                let n = 1 << f;
                assert!(
                    a >= guard && a + n <= ram.len(),
                    "store {a:x} pc={pc:x} guard={guard:x}"
                );
                ram[a..a + n].copy_from_slice(&y.to_le_bytes()[..n]);
            }
            0x6f => {
                value = Some(next as u64);
                next = pc.wrapping_add(sext(
                    (ins >> 31 << 20)
                        | (ins & 0xff000)
                        | (ins >> 20 & 1) << 11
                        | (ins >> 21 & 1023) << 1,
                    21,
                ) as usize);
            }
            0x67 => {
                value = Some(next as u64);
                next = (x.wrapping_add(imm) & !1) as usize;
            }
            0x63 => {
                if match f {
                    0 => x == y,
                    1 => x != y,
                    4 => (x as i64) < (y as i64),
                    5 => (x as i64) >= (y as i64),
                    6 => x < y,
                    _ => x >= y,
                } {
                    next = pc.wrapping_add(sext(
                        (ins >> 31 << 12)
                            | (ins >> 7 & 1) << 11
                            | (ff & 63) << 5
                            | (rd as u64 & 30),
                        13,
                    ) as usize);
                }
            }
            0x0b => match ff {
                0 => {
                    println!(
                        "ROM result={x} checks={checks} instructions={instructions} min_sp={min_sp:x} pc={pc:x} ra={:x} history={history:x?}",
                        g[1]
                    );
                    assert_eq!(x, u64::from(expected));
                    break;
                }
                1 => guard = x as usize,
                2 => checks += 1,
                3..=5 => {
                    let (a, b) = (fs(x), fs(y));
                    value = Some(
                        match ff {
                            3 => a + b,
                            4 => a - b,
                            _ => a * b,
                        }
                        .to_canonical_u64(),
                    );
                }
                6 => {
                    let ext = |v: u64| {
                        E::from_le_bytes_canonical(
                            ram[v as usize..v as usize + 40].try_into().unwrap(),
                        )
                        .unwrap()
                    };
                    let z = ext(x) * ext(y);
                    let dst = g[rd] as usize;
                    assert!(dst >= guard && dst + 40 <= ram.len());
                    ram[dst..dst + 40].copy_from_slice(&z.to_le_bytes());
                }
                7 => {
                    k = turboshake256_static_midstate(match x {
                        6 => b"QSAG.ZKHEM2.TREE/v1",
                        7 => b"QSAG.ZKHEM2.FS/v1",
                        8 => b"QSAG.HEM.QUINTIC.FS/v2",
                        9 => b"QSAG.HEM.QUINTIC.TREE/v2",
                        _ => panic!(),
                    });
                }
                8 => k[x as usize] ^= y,
                9 => {
                    keccak_p1600_12(&mut k);
                }
                10 => value = Some(k[x as usize]),
                11 => {
                    let a = x as usize;
                    let n = (y >> 32) as usize;
                    let mut key = y as u32 as u64;
                    let mut new = n;
                    for i in 0..=n {
                        let addr = a + 8 * i;
                        let item = load(&ram, addr, 8);
                        if i == n || key < item {
                            ram[addr..addr + 8].copy_from_slice(&key.to_le_bytes());
                        }
                        if i == n {
                            new += 1;
                            break;
                        }
                        if key == item {
                            break;
                        }
                        key = key.max(item);
                    }
                    value = Some(new as u64);
                }
                12 => {
                    let next = y as u32 as u64;
                    let pair = next != 0 && (x ^ 1) == next;
                    let bad = x <= 1 || (next != 0 && next <= x) || (!pair && y >> 32 == 0);
                    value = Some(
                        (x >> 1) << 4
                            | u64::from(bad) << 3
                            | (x & 1) << 2
                            | u64::from(!pair) << 1
                            | u64::from(pair),
                    );
                }
                13 => {
                    value = Some(
                        [
                            0x0801, 0x3887, 0x1901, 0x3667, 0x3996, 0x3555, 0x3445, 0x0334, 0x2229,
                            0x0882, 0x2838, 0x0098,
                        ][x as usize],
                    )
                }
                14 => {
                    let ext = |v: u64| {
                        E::from_le_bytes_canonical(
                            ram[v as usize..v as usize + 40].try_into().unwrap(),
                        )
                        .unwrap()
                    };
                    let ptr = g[rd] & !7;
                    let n = if g[rd] & 1 != 0 { 10 } else { 3 };
                    let coeff: Vec<_> = (0..n).map(|i| ext(ptr + i * 40)).collect();
                    assert_eq!(coeff.iter().fold(coeff[0], |a, &c| a + c), ext(x));
                    checks += 1;
                    let result = coeff.iter().rev().fold(E::ZERO, |a, &c| a * ext(y) + c);
                    ram[x as usize..x as usize + 40].copy_from_slice(&result.to_le_bytes());
                }
                15 => p2[(x & 15) as usize] = fs(y),
                16 => qsag_agg::sponge::poseidon2_perm12(&mut p2),
                17 => value = Some(p2[(x & 15) as usize].to_canonical_u64()),
                _ => panic!("custom {ff}"),
            },
            _ => panic!("invalid instruction {ins:x} at {pc:x}"),
        }
        if let Some(z) = value
            && rd != 0
        {
            g[rd] = z;
        }
        if g[2] != 0 {
            min_sp = min_sp.min(g[2] as usize);
        }
        pc = next;
        assert!(instructions < 300000000, "pc {pc:x}");
    }
}
