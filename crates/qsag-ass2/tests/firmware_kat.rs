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
        baseline = Some(valid.trace);
    }
}

#[test]
fn sumcheck_rejects_every_bit_of_digest_bytes_32_to_49() {
    let fx = fixtures::sumcheck(0, &mut 0x1503_3871_aab0_cdef);
    let digest = fx.input.expected;
    let rejects = |byte: usize, bit: u8| {
        let mut bad = fx.input.clone();
        bad.expected[byte] ^= 1 << bit;
        let out = firmware::run_zkhem_v2_fp5_sumcheck(&bad).unwrap();
        assert_eq!(
            out,
            SumcheckOutput {
                accepted: false,
                value: fx.value,
                digest
            },
            "byte {byte} bit {bit}"
        );
    };
    // The evaluation point is bytes 0..40. The check has to reach the ten bytes after it,
    // through the sixteen-bit tail of the seventh word.
    for byte in 32..50 {
        for bit in 0..8 {
            rejects(byte, bit);
        }
    }
    rejects(49, 0);
    rejects(49, 7);
}

#[test]
fn sumcheck_rejects_a_noncanonical_challenge_draw() {
    use abi::sumcheck::*;
    let code = firmware::fw_zkhem_v2_fp5_sumcheck();
    let input = fixtures::sumcheck_noncanonical_draw();
    let mut vm = machine(&code);
    input.install(&mut vm).unwrap();
    let got = execute(&code, &vm);
    // The round sum holds and every digest bit matches: the draw itself is the reject.
    assert_eq!(got.digest(DIGEST), input.expected);
    assert_eq!(got.r[4], 0);
    let out = firmware::run_zkhem_v2_fp5_sumcheck(&input).unwrap();
    assert!(!out.accepted && out.digest == input.expected);
    // Same public trace as an accepted run.
    let fx = fixtures::sumcheck(0, &mut 0x1503_3871_aab0_cdef);
    let mut vm = machine(&code);
    fx.input.install(&mut vm).unwrap();
    let valid = execute(&code, &vm);
    assert_eq!(valid.r[4], 1);
    assert_eq!(got.trace, valid.trace);
}

#[test]
fn sumcheck_absorb_frame_at_rate_boundary() {
    use abi::sumcheck::*;
    let code = firmware::fw_zkhem_v2_fp5_sumcheck();
    let fx = fixtures::sumcheck_rate_boundary();
    assert_eq!(fx.input.block[135], 0x87);
    let mut vm = machine(&code);
    fx.input.install(&mut vm).unwrap();
    let got = execute(&code, &vm);
    assert_eq!(got.r[4], 1);
    assert_eq!(got.digest(DIGEST), fx.input.expected);
    assert_eq!(got.words(VALUE), [0; 5]);
}

#[test]
fn canopy_real_tree_secret_paths_and_tampers() {
    use abi::canopy::*;
    let code = firmware::fw_zkhem_v2_canopy50_verify();
    assert_eq!(count(&code, |i| matches!(i, I::Sel { .. })), 14);
    let stage = 7;
    let (tree, leaves) = fixtures::canopy_tree(stage);
    let root = tree.root();
    let mut baseline = None;
    for index in 0..leaves.len() {
        let input = fixtures::canopy(&tree, &leaves, stage, index);
        let mut vm = machine(&code);
        input.install(&mut vm).unwrap();
        let good = execute(&code, &vm);
        assert_eq!(good.r[4], 1, "index {index}");
        assert_eq!(good.digest(ROOT), root);
        assert_eq!(&good.mem[ROOT + 50..ROOT + 56], &[0; 6]);
        assert_eq!(
            good.words(MIDSTATE_SCRATCH),
            turboshake256_static_midstate(fixtures::TREE_CUSTOMIZATION)
        );
        assert_eq!(
            firmware::run_zkhem_v2_canopy50_verify(&input),
            Ok(CanopyOutput {
                accepted: true,
                root
            })
        );
        // The secret index selects children by SEL only: every leaf has the same trace.
        if let Some(trace) = &baseline {
            assert_eq!(&good.trace, trace);
        }
        if index == 0 {
            report("canopy depth 4", &code, &good);
        }
        if index == 5 {
            for offset in [
                LEAF,
                LEAF + 49,
                SIBLINGS + 49,
                SIBLINGS + 3 * 56,
                STAGE,
                INDEX,
            ] {
                let mut bad = vm.clone();
                bad.mem[offset] ^= 1;
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0, "offset {offset:#x}");
                assert_eq!(got.trace, good.trace);
            }
            for bit in 0..400 {
                let mut bad = vm.clone();
                bad.mem[EXPECTED + bit / 8] ^= 1 << (bit % 8);
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0, "root bit {bit}");
                assert_eq!(got.digest(ROOT), root);
                assert_eq!(got.trace, good.trace);
            }
            let mut other_depth = vm.clone();
            other_depth.mem[DEPTH] ^= 1;
            assert_eq!(execute(&code, &other_depth).r[4], 0);
            for invalid in [16, 1 << 40, u64::MAX] {
                let mut bad = vm.clone();
                bad.load_tainted(INDEX as u64, &invalid.to_le_bytes(), Secret)
                    .unwrap();
                let got = execute(&code, &bad);
                assert_eq!(got.r[4], 0);
                assert_eq!(got.trace, good.trace);
            }
        }
        baseline = Some(good.trace);
    }
}

#[test]
fn canopy_public_depth_bounds() {
    use abi::canopy::*;
    let code = firmware::fw_zkhem_v2_canopy50_verify();
    for depth in 1..=16u8 {
        let input = fixtures::canopy_synthetic_path(depth);
        let mut vm = machine(&code);
        input.install(&mut vm).unwrap();
        let got = execute(&code, &vm);
        assert_eq!(got.r[4], 1);
        assert_eq!(got.digest(ROOT), input.expected_root);
        if depth == 16 {
            report("canopy depth 16", &code, &got);
        }
    }
    for depth in [0, 17, 255] {
        let mut vm = machine(&code);
        vm.load_tainted(DEPTH as u64, &[depth], Public).unwrap();
        let got = execute(&code, &vm);
        assert_eq!(got.r[4], 0);
        assert_eq!(got.trace.accesses, [(DEPTH, 1, false)]);
    }
    let crowded = CanopyInput {
        siblings: vec![[0; 50]; 17],
        ..fixtures::canopy_synthetic_path(1)
    };
    assert_eq!(
        firmware::run_zkhem_v2_canopy50_verify(&crowded),
        Err(FirmwareError::TooManySiblings { count: 17 })
    );
    // The hasher under test is the profile the fixtures use.
    let _ = Hasher::new(PROFILE);
}

#[test]
fn gl24_jive_known_answer_boundaries_and_random_inputs() {
    use abi::jive::*;
    let code = firmware::fw_poseidon2_gl24_jive();
    assert_eq!(count(&code, |i| i == I::Poseidon2Gl24), 1);
    let (kat, kat_digest) = fixtures::jive_kat();
    let mut rng = 0xf06c_e6b1_5294_03a1;
    let mut baseline: Option<Trace> = None;
    for case in 0..131 {
        let input = match case {
            0 => kat,
            1 => JiveInput {
                left: [P - 1; 7],
                right: [P; 7],
                tweak: [P + 1, u64::MAX],
            },
            2 => JiveInput {
                left: [u64::MAX; 7],
                right: [P + 1; 7],
                tweak: [P, u64::MAX],
            },
            _ => JiveInput {
                left: core::array::from_fn(|_| next(&mut rng)),
                right: core::array::from_fn(|_| next(&mut rng)),
                tweak: core::array::from_fn(|_| next(&mut rng)),
            },
        };
        let want = fixtures::jive_digest(&input);
        let mut vm = machine(&code);
        input.install(&mut vm).unwrap();
        let got = execute(&code, &vm);
        assert_eq!(got.r[4], 1);
        assert_eq!(got.words(DIGEST), want);
        assert!(want.iter().all(|&limb| limb < P));
        assert_eq!(firmware::run_poseidon2_gl24_jive(&input), Ok(want));
        if let Some(trace) = &baseline {
            assert_eq!(&got.trace, trace);
        }
        if case == 0 {
            assert_eq!(want, kat_digest);
            report("GL24 Jive", &code, &got);
            // Any single input bit moves the digest off the known answer.
            for word in 0..16 {
                for bit in [0, 31, 63] {
                    let mut bad = vm.clone();
                    bad.mem[LEFT + 8 * word + bit / 8] ^= 1 << (bit % 8);
                    let tampered = execute(&code, &bad);
                    assert_ne!(
                        tampered.words::<7>(DIGEST),
                        kat_digest,
                        "word {word} bit {bit}"
                    );
                    assert_eq!(tampered.trace, got.trace);
                }
            }
        }
        baseline = Some(got.trace);
    }
}

// Reconstruct products from the live FTS Gilboa sender and receiver. This
// in-process chosen-message OT fixture delivers the requested alternative for
// each bit. All field multiplication and share folding stays in qsag-fts.
fn fts_tags(values: [u128; 4], weights: [(u128, u128); 4]) -> [u128; 2] {
    use qsag_core::wipe::{SecretBuffer, SecretVec};
    use qsag_fts::{
        ParallelSeededDkgOt, ParallelSeededDkgOtPads, ParallelSeededDkgOtPeer,
        ParallelSeededDkgProducts, ParallelSeededError as Error, ParallelSeededGilboaProducts,
    };
    use std::{cell::RefCell, rc::Rc};
    type Batch = ([u8; 32], Vec<[u128; 2]>);
    #[derive(Clone, Default)]
    struct ChosenOt(Rc<RefCell<Option<Batch>>>);
    impl ParallelSeededDkgOt for ChosenOt {
        fn send(&mut self, peer: u16, ctx: [u8; 32], pairs: &[[u128; 2]]) -> Result<(), Error> {
            assert_eq!(peer, 1);
            assert!(self.0.borrow_mut().replace((ctx, pairs.to_vec())).is_none());
            Ok(())
        }
        fn receive(
            &mut self,
            peer: u16,
            ctx: [u8; 32],
            choices: &[u128],
        ) -> Result<SecretVec<u128>, Error> {
            assert_eq!(peer, 0);
            let (sent, pairs) = self.0.borrow_mut().take().unwrap();
            assert_eq!(sent, ctx);
            assert_eq!(pairs.len(), 128 * choices.len());
            Ok(SecretBuffer(
                pairs
                    .iter()
                    .enumerate()
                    .map(|(i, p)| p[((choices[i / 128] >> (i % 128)) & 1) as usize])
                    .collect(),
            ))
        }
        fn random_ots(
            &mut self,
            _: [u8; 32],
            _: &[ParallelSeededDkgOtPeer<'_>],
        ) -> Result<Vec<ParallelSeededDkgOtPads>, Error> {
            unreachable!()
        }
        fn send_words(&mut self, _: u16, _: [u8; 32], _: Vec<u128>) -> Result<(), Error> {
            unreachable!()
        }
        fn receive_words(&mut self, _: u16, _: [u8; 32], _: usize) -> Result<Vec<u128>, Error> {
            unreachable!()
        }
    }
    let ot = ChosenOt::default();
    let mut sender = ParallelSeededGilboaProducts::new(0, [0x21; 32], ot.clone());
    let mut receiver = ParallelSeededGilboaProducts::new(1, [0x37; 32], ot);
    let mut tags = [0; 2];
    for (j, tag) in tags.iter_mut().enumerate() {
        let context = [j as u8; 32];
        let column = weights.map(|(a, b)| if j == 0 { a } else { b });
        let a = sender.product_shares(context, 0, 1, &values).unwrap();
        let b = receiver.product_shares(context, 0, 1, &column).unwrap();
        assert_eq!((a.len(), b.len()), (4, 4));
        *tag = a.iter().zip(b).fold(0, |acc, (&x, y)| acc ^ x ^ y);
    }
    tags
}

#[test]
fn dual_mac_and_all_four_secret_wots_digits() {
    use abi::cth::*;
    use qsag_accel::{AcceleratorBackend, CpuReferenceBackend};
    let code = firmware::fw_cth_gf128_and_wots();
    assert_eq!(count(&code, |i| i == I::Poseidon2Gl12), 3);
    assert_eq!(count(&code, |i| matches!(i, I::Gf128Mul { .. })), 8);
    assert_eq!(count(&code, |i| matches!(i, I::Gf128Xor { .. })), 8);
    let mut rng = 0x7be6_b753_fcc8_11d4;
    let (values, weights, tags) = fixtures::cth_mac(&mut rng);
    let weight_pairs = weights.map(|w| (w[0], w[1]));
    assert_eq!(fts_tags(values, weight_pairs), tags);
    assert_eq!(
        CpuReferenceBackend::new()
            .bdoz_gf2_128_batch_dot(&values.map(|v| (v, v)), &weight_pairs)
            .unwrap(),
        (tags[0], tags[1])
    );
    let mut baseline = None;
    for (layer, tree, keypair, chain) in [
        (0, 0, 0, 0),
        (13, 0xfeab_8291_0157_aa03, 0xabcde, 127),
        (63, u64::MAX, 0xfffff, 255),
    ] {
        let seed: [u64; 4] = core::array::from_fn(|_| next(&mut rng) % P);
        let start = [P - 1, 0, next(&mut rng) % P, next(&mut rng) % P];
        let ends = fixtures::wots_chain(seed, start, layer, tree, keypair, chain);
        for digit in 0..4 {
            let input = CthWotsInput {
                values,
                weights,
                tags,
                start,
                seed,
                layer: layer.into(),
                tree,
                keypair: keypair.into(),
                chain: chain.into(),
                digit: digit as u64,
            };
            let end = ends[digit];
            let mut vm = machine(&code);
            input.install(&mut vm).unwrap();
            let got = execute(&code, &vm);
            assert_eq!(got.words(END), end);
            assert_eq!(got.word(STATUS), 1);
            let mut wiped = [0u64; 16];
            wiped[4] = 1;
            assert_eq!(got.r, wiped);
            assert_eq!(got.s, [0; 25]);
            assert_eq!(
                firmware::run_cth_gf128_and_wots(&input),
                Ok(CthWotsOutput {
                    accepted: true,
                    end
                })
            );
            // Zero variance in cycles, PCs and addresses across digits and addresses.
            if let Some(t) = &baseline {
                assert_eq!(&got.trace, t);
            } else {
                report("dual MAC + WOTS", &code, &got);
            }
            // One flipped bit in either half of either expected tag, or in an opened
            // value, rejects and releases no chain value.
            for (offset, mask) in [
                (TAGS, 0x80),
                (TAGS + 15, 0x80),
                (TAGS + 16, 0x80),
                (TAGS + 31, 0x80),
            ]
            .into_iter()
            .chain([(TAGS, 1), (TAGS + 31, 1), (VALUES, 1), (VALUES + 63, 0x80)])
            {
                let mut bad = vm.clone();
                bad.mem[offset] ^= mask;
                let reject = execute(&code, &bad);
                assert_eq!(reject.r, [0; 16], "offset {offset:#x}");
                assert_eq!(reject.s, [0; 25]);
                assert_eq!(reject.word(STATUS), 0);
                assert_eq!(reject.words(END), [0; 4]);
                assert_eq!(reject.trace, got.trace);
            }
            // A coordinate outside the injective address packing, or a digit above three,
            // would hash under another chain's tweak.
            for (field, value) in [
                (LAYER, 64),
                (KP, 1 << 20),
                (CHAIN, 256),
                (DIGIT, 4),
                (DIGIT, u64::MAX),
            ] {
                let mut bad = vm.clone();
                let tag = if field == DIGIT { Secret } else { Public };
                bad.load_tainted(field as u64, &value.to_le_bytes(), tag)
                    .unwrap();
                let reject = execute(&code, &bad);
                assert_eq!(reject.r, [0; 16], "field {field:#x}");
                assert_eq!(reject.word(STATUS), 0);
                assert_eq!(reject.words(END), [0; 4]);
                assert_eq!(reject.trace, got.trace);
            }
            baseline = Some(got.trace);
        }
    }
    // A start value given by noncanonical representatives is the same chain.
    let (canonical, end) = fixtures::cth_wots(&mut 0x51e5_7a11_0bad_c0de)[2];
    assert_eq!(canonical.start[..2], [P - 1, 0]);
    let alias = CthWotsInput {
        start: [u64::MAX, P, canonical.start[2], canonical.start[3]],
        ..canonical
    };
    assert_eq!(alias.start[0] % P, 0xffff_fffe);
    let shifted = CthWotsInput {
        start: [0xffff_fffe, 0, alias.start[2], alias.start[3]],
        ..alias
    };
    assert_eq!(
        firmware::run_cth_gf128_and_wots(&canonical),
        Ok(CthWotsOutput {
            accepted: true,
            end
        })
    );
    let via_alias = firmware::run_cth_gf128_and_wots(&alias).unwrap();
    assert_eq!(Ok(via_alias), firmware::run_cth_gf128_and_wots(&shifted));
    assert!(via_alias.accepted && via_alias.end != end);
    // Digit zero releases the start value itself, canonical.
    let unstepped = CthWotsInput { digit: 0, ..alias };
    assert_eq!(
        firmware::run_cth_gf128_and_wots(&unstepped).unwrap().end,
        [0xffff_fffe, 0, alias.start[2], alias.start[3]]
    );
}

#[test]
fn runners_report_traps_and_dit_violations() {
    // An image that faults fail-closed is an error, not a result.
    let mut vm = firmware::boot(&assemble("LD64 R1,[R0+8192]\nHALT").unwrap()).unwrap();
    assert_eq!(
        firmware::run_to_halt(&mut vm),
        Err(FirmwareError::Exit(RunExit::Trap(VmTrap::MemFault)))
    );
    // A branch on a secret mailbox byte stops the run before the branch executes.
    let mut vm = firmware::boot(&assemble("LDBU R1,[R0+4096]\nBNEZ R1,0\nHALT").unwrap()).unwrap();
    vm.load_tainted(4096, &[1], Secret).unwrap();
    match firmware::run_to_halt(&mut vm) {
        Err(FirmwareError::Exit(RunExit::DitViolation(v))) => {
            assert_eq!(
                (v.pc, v.reg, v.kind),
                (4, 1, DitViolationKind::SecretBranchCond)
            );
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(vm.pc, 4);
    // An image larger than the SRAM does not boot.
    assert!(matches!(
        firmware::boot(&vec![0; SRAM_BYTES + 4]),
        Err(FirmwareError::Mem(_))
    ));
}
