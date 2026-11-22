//! Execute the installed LE words, then compare their SRAM effects with the
//! live protocol implementations. Every case runs on Ass2Vm in DIT trap mode with
//! the witness, digest and digit fields tagged secret, and again on an independent
//! instruction interpreter that only implements the emitted subset. An unexpected
//! opcode, secret address/branch, misalignment, or fetch outside the image fails
//! the test. Memory the mailbox does not define and every register start as junk.
#[path = "common/fixtures.rs"]
mod fixtures;

use Taint::{Public, Secret};
use fixtures::{P, PROFILE, next};
use qsag_accel::poseidon2::{poseidon2_gl24_perm, poseidon2_perm12};
use qsag_agg::sponge::{keccak_p1600_12, turboshake256_static_midstate};
use qsag_agg::zk_hem::v2::hash::Hasher;
use qsag_ass2::firmware::{
    self, CanopyInput, CanopyOutput, CthWotsInput, CthWotsOutput, FirmwareError, JiveInput,
    SRAM_BYTES, SumcheckOutput, abi,
};
use qsag_ass2::isa::{
    AluOp, AluiOp, Ass2Insn as I, BrOp, Imm20Mode, LoadMode, StoreMode, cycle_cost, decode_insn,
};
use qsag_ass2::vm::{Ass2Vm, DitMode, DitViolationKind, RunExit, Taint, VmTrap};
use qsag_ass2::{assemble, disassemble_bytes};

#[derive(Default, Debug, PartialEq, Eq)]
struct Trace {
    cycles: u64,
    instret: u64,
    pc: Vec<usize>,
    accesses: Vec<(usize, usize, bool)>, // byte address, width, write
}
struct Run {
    mem: Vec<u8>,
    trace: Trace,
    r: [u64; 16],
    s: [u64; 25],
}
impl Run {
    fn word(&self, addr: usize) -> u64 {
        u64::from_le_bytes(self.mem[addr..addr + 8].try_into().unwrap())
    }
    fn words<const N: usize>(&self, addr: usize) -> [u64; N] {
        core::array::from_fn(|i| self.word(addr + 8 * i))
    }
    fn digest(&self, addr: usize) -> [u8; 50] {
        self.mem[addr..addr + 50].try_into().unwrap()
    }
}
fn gf_mul(mut a: u128, mut b: u128) -> u128 {
    let mut c = 0;
    for _ in 0..128 {
        if b & 1 != 0 {
            c ^= a;
        }
        a = (a << 1) ^ (0x87 * (a >> 127));
        b >>= 1;
    }
    c
}
fn fp5_op(multiply: bool, a: [u64; 5], b: [u64; 5]) -> [u64; 5] {
    let p = P as u128;
    let mut z = [0u128; 5];
    for i in 0..5 {
        if multiply {
            for j in 0..5 {
                let product = (u128::from(a[i]) * u128::from(b[j])) % p;
                z[(i + j) % 5] += product * if i + j >= 5 { 3 } else { 1 };
            }
        } else {
            z[i] = u128::from(a[i]) + u128::from(b[i]);
        }
    }
    z.map(|v| (v % p) as u64)
}

/// A machine in DIT trap mode holding `code`, with junk in every register, lane and
/// memory byte the image has to define for itself, all of it tagged secret where a tag
/// exists.
fn machine(code: &[u8]) -> Ass2Vm {
    let mut vm = Ass2Vm::new(SRAM_BYTES);
    vm.mem.fill(0xa5);
    vm.load_image(0, code).unwrap();
    vm.regs = [0xdead_beef_face_cafe; 16];
    vm.regs[0] = 0;
    vm.spg = [u64::MAX; 25];
    vm.reg_taint = [Secret; 16];
    vm.reg_taint[0] = Public;
    vm.spg_taint.fill(Secret);
    vm.dit_mode = DitMode::Trap;
    vm
}

// Conservative instruction-level taint: every wide-bank read is Secret. This
// also covers nonlinear permutations and aliased extension/polynomial lanes.
fn execute(code: &[u8], start: &Ass2Vm) -> Run {
    let mut vm = start.clone();
    assert_eq!(vm.run(16384), RunExit::Halted);
    assert!(vm.violations.is_empty());

    let mut mem = start.mem.clone();
    let mut mem_taint = start.mem_taint.clone();
    let mut pc = 0usize;
    let mut trace = Trace::default();
    let mut r = start.regs;
    let mut s = start.spg;
    let mut t = start.reg_taint;
    loop {
        assert!(
            pc % 4 == 0 && pc + 4 <= code.len() && trace.instret < 16384,
            "bad fetch {pc:#x}"
        );
        let word = u32::from_le_bytes(mem[pc..pc + 4].try_into().unwrap());
        let op = decode_insn(word).expect("illegal word");
        trace.pc.push(pc);
        trace.cycles += cycle_cost(&op);
        trace.instret += 1;
        pc += 4;
        let val = |i: u8| r[i as usize];
        let join = |regs: &[u8]| {
            if regs.iter().any(|&i| t[i as usize] == Secret) {
                Secret
            } else {
                Public
            }
        };
        let addr = |ra: u8, off: i16, width: usize| {
            assert_eq!(t[ra as usize], Public, "secret address");
            let addr = val(ra).wrapping_add_signed(i64::from(off) * width as i64) as usize;
            assert_eq!(addr % width, 0);
            addr
        };
        let load = |mem: &[u8], a: usize| u64::from_le_bytes(mem[a..a + 8].try_into().unwrap());
        let pair =
            |i: u8| u128::from(s[2 * i as usize]) | (u128::from(s[2 * i as usize + 1]) << 64);
        // Capture operands before writeback, also when the destination aliases a source.
        let dest = match op {
            I::Halt => break,
            I::Zeroize => {
                r.fill(0);
                s.fill(0);
                t.fill(Public);
                None
            }
            I::Imm20 {
                rd,
                mode: Imm20Mode::Movz20,
                imm20,
            } => Some((rd, imm20.into(), Public)),
            I::Alui { op, rd, ra, imm16 } => {
                let a = val(ra);
                let k = u64::from(imm16);
                let v = match op {
                    AluiOp::Andi => a & k,
                    AluiOp::Ori => a | k,
                    AluiOp::Shli => a << k,
                    AluiOp::Shri => a >> k,
                    AluiOp::Slk16 => (a << 16) | k,
                    AluiOp::Addiu => a.wrapping_add(k),
                    AluiOp::Addi => a.wrapping_add_signed(i64::from(imm16 as i16)),
                    _ => panic!("unexpected {op:?}"),
                };
                Some((rd, v, join(&[ra])))
            }
            I::Alu { op, rd, ra, rb } => {
                let (a, b) = (val(ra), val(rb));
                let v = match op {
                    AluOp::Add => a.wrapping_add(b),
                    AluOp::Shl => {
                        if b < 64 {
                            a << b
                        } else {
                            0
                        }
                    }
                    _ => panic!("unexpected {op:?}"),
                };
                Some((rd, v, join(&[ra, rb])))
            }
            I::Lut4 { rd, ra, rb, m } => {
                let (a, b) = (val(ra), val(rb));
                let v = match m {
                    6 => a ^ b,
                    8 => a & b,
                    14 => a | b,
                    _ => panic!("unexpected LUT {m}"),
                };
                Some((rd, v, join(&[ra, rb])))
            }
            I::Cmp { rd, ra, rb, flags } => {
                let v = match flags {
                    1 => val(ra) == val(rb),
                    2 => val(ra) > val(rb),
                    3 => val(ra) >= val(rb),
                    _ => panic!("unexpected flags"),
                };
                Some((rd, v.into(), join(&[ra, rb])))
            }
            I::Sel { rd, ra, rb, rc } => Some((
                rd,
                if val(rc) == 0 { val(ra) } else { val(rb) },
                join(&[ra, rb, rc]),
            )),
            I::Bextu { rd, ra, idx, len } => Some((
                rd,
                (val(ra) >> (idx * 8)) & (u64::MAX >> ((8 - len) * 8)),
                join(&[ra]),
            )),
            I::Br { op, cond, off20 } => {
                assert_eq!(t[cond as usize], Public, "secret branch");
                let take = match op {
                    BrOp::Beqz => val(cond) == 0,
                    BrOp::Bnez => val(cond) != 0,
                    _ => panic!("unexpected branch"),
                };
                if take {
                    pc = pc.checked_add_signed(off20 as isize * 4).unwrap();
                }
                None
            }
            I::Load {
                rd,
                ra,
                mode,
                simm16,
            } => {
                let n = if mode == LoadMode::Ld64 { 8 } else { 1 };
                let a = addr(ra, simm16, n);
                trace.accesses.push((a, n, false));
                let v = if n == 8 { load(&mem, a) } else { mem[a].into() };
                let label = if mem_taint[a..a + n].contains(&Secret) {
                    Secret
                } else {
                    Public
                };
                Some((rd, v, label))
            }
            I::Store {
                rs,
                ra,
                mode: StoreMode::St64,
                simm16,
            } => {
                let a = addr(ra, simm16, 8);
                trace.accesses.push((a, 8, true));
                assert!(a >= code.len());
                mem[a..a + 8].copy_from_slice(&val(rs).to_le_bytes());
                mem_taint[a..a + 8].fill(join(&[rs]));
                None
            }
            I::Sld64 { sidx, ra, off8 } => {
                let a = addr(ra, off8.into(), 8);
                trace.accesses.push((a, 8, false));
                s[sidx as usize] = load(&mem, a);
                None
            }
            I::Sst64 { sidx, ra, off8 } => {
                let a = addr(ra, off8.into(), 8);
                trace.accesses.push((a, 8, true));
                assert!(a >= code.len());
                mem[a..a + 8].copy_from_slice(&s[sidx as usize].to_le_bytes());
                mem_taint[a..a + 8].fill(Secret);
                None
            }
            I::Sget { rd, sidx } => Some((rd, s[sidx as usize], Secret)),
            I::Sput { sidx, ra } => {
                s[sidx as usize] = val(ra);
                None
            }
            I::Sxor { sidx, ra } => {
                s[sidx as usize] ^= val(ra);
                None
            }
            I::Szero => {
                s.fill(0);
                None
            }
            I::GlAdd { rd, ra, rb } => Some((
                rd,
                ((u128::from(val(ra)) + u128::from(val(rb))) % u128::from(P)) as u64,
                join(&[ra, rb]),
            )),
            I::Fp5Mul { ed, ea, eb } | I::Fp5Add { ed, ea, eb } => {
                let ext = |e: u8| s[5 * e as usize..][..5].try_into().unwrap();
                let z = fp5_op(matches!(op, I::Fp5Mul { .. }), ext(ea), ext(eb));
                s[5 * ed as usize..][..5].copy_from_slice(&z);
                None
            }
            I::Gf128Mul { pd, pa, pb } | I::Gf128Xor { pd, pa, pb } => {
                let (a, b) = (pair(pa), pair(pb));
                let z = if matches!(op, I::Gf128Mul { .. }) {
                    gf_mul(a, b)
                } else {
                    a ^ b
                };
                s[2 * pd as usize] = z as u64;
                s[2 * pd as usize + 1] = (z >> 64) as u64;
                None
            }
            I::KeccakF1600 { rounds: 12 } => {
                keccak_p1600_12(&mut s);
                None
            }
            I::Poseidon2Gl12 => {
                poseidon2_perm12((&mut s[..12]).try_into().unwrap());
                None
            }
            I::Poseidon2Gl24 => {
                poseidon2_gl24_perm((&mut s[..24]).try_into().unwrap());
                None
            }
            _ => panic!("unsupported firmware instruction {op:?}"),
        };
        if let Some((rd, v, label)) = dest
            && rd != 0
        {
            r[rd as usize] = v;
            t[rd as usize] = label;
        }
    }
    assert_eq!(vm.regs, r);
    assert_eq!(vm.spg, s);
    assert_eq!(vm.mem, mem);
    assert_eq!(
        (vm.csrs.cycles, vm.csrs.instret),
        (trace.cycles, trace.instret)
    );
    let events = &vm.trace.observations;
    assert!(
        events
            .iter()
            .map(|e| e.pc as usize)
            .eq(trace.pc.iter().copied())
    );
    assert!(
        events
            .iter()
            .filter_map(|e| e.mem_access)
            .map(|m| (m.addr as usize, m.size as usize, m.write))
            .eq(trace.accesses.iter().copied())
    );
    Run { mem, trace, r, s }
}

fn count(code: &[u8], op: impl Fn(I) -> bool) -> usize {
    code.as_chunks::<4>()
        .0
        .iter()
        .filter(|w| op(decode_insn(u32::from_le_bytes(**w)).unwrap()))
        .count()
}
fn report(name: &str, code: &[u8], run: &Run) {
    println!(
        "{name}: {} bytes, {} instructions, {} cycles, {} data accesses",
        code.len(),
        run.trace.instret,
        run.trace.cycles,
        run.trace.accesses.len()
    );
}

#[test]
fn images_are_legal_straight_code_below_the_mailbox() {
    for (name, code) in [
        ("sumcheck", firmware::fw_zkhem_v2_fp5_sumcheck()),
        ("canopy", firmware::fw_zkhem_v2_canopy50_verify()),
        ("jive", firmware::fw_poseidon2_gl24_jive()),
        ("cth", firmware::fw_cth_gf128_and_wots()),
    ] {
        assert!(
            code.len() % 4 == 0 && code.len() <= firmware::INPUT,
            "{name}"
        );
        let (words, _) = code.as_chunks::<4>();
        let insns: Vec<I> = words
            .iter()
            .map(|w| decode_insn(u32::from_le_bytes(*w)).unwrap_or_else(|| panic!("{name}")))
            .collect();
        assert_eq!(insns.last(), Some(&I::Halt), "{name}");
        // The only control transfers are the canopy's three branches on the public depth.
        let branches = insns.iter().filter(|i| matches!(i, I::Br { .. })).count();
        assert_eq!(branches, if name == "canopy" { 3 } else { 0 }, "{name}");
        assert!(
            !insns.iter().any(|i| matches!(
                i,
                I::Jal { .. } | I::Jalr { .. } | I::Exc | I::Eret | I::Csrr { .. } | I::Csrw { .. }
            )),
            "{name}"
        );
        // The assembler and disassembler agree with the builders on every word.
        assert_eq!(assemble(&disassemble_bytes(&code)).unwrap(), code, "{name}");
    }
}

#[test]
fn sumcheck_live_transcript_and_all_400_digest_bits() {
    use abi::sumcheck::*;
    let code = firmware::fw_zkhem_v2_fp5_sumcheck();
    assert_eq!(count(&code, |i| matches!(i, I::Fp5Mul { .. })), 9);
    assert_eq!(count(&code, |i| matches!(i, I::Fp5Add { .. })), 19);
    assert_eq!(count(&code, |i| i == I::KeccakF1600 { rounds: 12 }), 1);
    let mut rng = 0x1503_3871_aab0_cdef;
    let mut baseline: Option<Trace> = None;
    for sample in 0..8 {
        let fx = fixtures::sumcheck(sample, &mut rng);
        let digest = fx.input.expected;
        let mut vm = machine(&code);
        fx.input.install(&mut vm).unwrap();
        let valid = execute(&code, &vm);
        assert_eq!(valid.r[4], 1);
        assert_eq!(valid.digest(DIGEST), digest);
        assert_eq!(&valid.mem[DIGEST + 50..DIGEST + 56], &[0; 6]);
        assert_eq!(valid.words(VALUE), fx.value);
        assert_eq!(
            firmware::run_zkhem_v2_fp5_sumcheck(&fx.input),
            Ok(SumcheckOutput {
                accepted: true,
                value: fx.value,
                digest
            })
        );
        // Different secret polynomials and transcripts, one public trace.
        if let Some(trace) = &baseline {
            assert_eq!(&valid.trace, trace);
        }
        if sample == 0 {
            report("sumcheck", &code, &valid);
            for bit in 0..400 {
                let mut bad = vm.clone();
                bad.mem[EXPECTED + bit / 8] ^= 1 << (bit % 8);
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0, "digest bit {bit}");
                assert_eq!(got.trace, valid.trace);
                assert_eq!(got.digest(DIGEST), digest);
            }
            // The squeezed side: one flipped frame bit changes the digest and rejects.
            for bit in [0, 8 * 67 + 3, 8 * 135 + 7] {
                let mut bad = vm.clone();
                bad.mem[BLOCK + bit / 8] ^= 1 << (bit % 8);
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0, "frame bit {bit}");
                assert_ne!(got.digest(DIGEST), digest);
                assert_eq!(got.trace, valid.trace);
            }
            for limb in 0..5 {
                let mut bad = vm.clone();
                bad.mem[CLAIM + 8 * limb] ^= 1;
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0);
                assert_eq!(got.trace, valid.trace);
                assert_eq!(got.words(VALUE), fx.value);
            }
            // A coefficient bit breaks the round sum.
            for coeff in [0, 9] {
                let mut bad = vm.clone();
                bad.mem[COEFFS + 40 * coeff + 39] ^= 0x40;
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0, "coefficient {coeff}");
                assert_eq!(got.trace, valid.trace);
            }
            // The six bytes after EXPECTED's 50 are not part of the digest.
            let mut padded = vm.clone();
            padded.mem[EXPECTED + 50..EXPECTED + 56].fill(0x5a);
            assert_eq!(execute(&code, &padded).r[4], 1);
        }
