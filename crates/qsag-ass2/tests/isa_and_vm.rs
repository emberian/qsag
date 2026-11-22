use qsag_agg::{Goldilocks, zk_hem::v2::field5::Fp5};
use qsag_ass2::isa::NOP_WORD;
use qsag_ass2::*;

fn vm(src: &str, size: usize) -> Ass2Vm {
    let mut vm = Ass2Vm::new(size);
    vm.load_image(0, &assemble(src).unwrap()).unwrap();
    vm
}
fn one(src: &str, a: u64, b: u64, c: u64, cycles: u64) -> u64 {
    let mut m = vm(src, 4);
    (m.regs[1], m.regs[2], m.regs[3]) = (a, b, c);
    assert_eq!(m.step(), StepOutcome::Retired, "{src}");
    assert_eq!(
        (m.pc, m.csrs.cycles, m.csrs.instret),
        (4, cycles, 1),
        "{src}"
    );
    m.regs[4]
}
fn random(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

#[test]
fn canonical_forms_and_field_boundaries() {
    // Enumerate the legal sub-functions. Start with independent architectural
    // encodings so the encoder and decoder cannot agree on the wrong bit layout.
    let mut words = vec![
        0,
        0x10000,
        0x40000,
        0x50000,
        NOP_WORD,
        0x6000_FEDF,
        0x6003_00EF,
        0xC000_0300,
        0xD000_FEDF,
        0xD001_0EDF,
        0xD002_0EDF,
        0xD003_00EF,
        0xF0C0_0000,
        0xF180_0000,
        0xF001_0000,
        0xF002_0000,
    ];
    for addr in 0..256 {
        words.extend([addr << 20 | 0x2000F, addr << 20 | 0x300F0]);
    }
    for i in 0..16 {
        for rb in [0, 15] {
            words.push(0x1000_00EF | rb << 8 | i << 16);
        }
        words.push(0x5000_0EDF | i << 12);
    }
    for op in 0..=8 {
        words.push(0x2000_0EDF | op << 16);
    }
    for op in 0..=9 {
        let max = if (5..=8).contains(&op) { 63 } else { 65535 };
        for i in [0, max] {
            words.push(0x3000_00EF | op << 8 | i << 12);
        }
    }
    for imm in [0, 0x7FFFF, 0x80000, 0xFFFFF] {
        for mode in 0..3 {
            words.push(0x4000_000F | mode << 4 | imm << 8);
        }
        for mode in 0..4 {
            words.push(0x9000_000F | mode << 4 | imm << 8);
        }
    }
    for idx in 0..8 {
        for len in 0..8 {
            for sub in [1, 2] {
                words.push(0x6000_00EF | sub << 16 | idx << 8 | len << 12);
            }
        }
    }
    for imm in [0, 1, 0x7fff, 0x8000, 0xffff] {
        for op in [7, 8] {
            for mode in [0, 1] {
                words.push(op << 28 | imm << 12 | mode << 8 | 0xEF);
            }
        }
        words.push(0xB000_00EF | imm << 12);
    }
    for off in [0, 0x7FFFFF, 0x800000, 0xFFFFFF] {
        words.push(0xA000_000F | off << 4);
    }
    for lane in 0..25 {
        let base = 0xC000_0000 | lane << 12;
        words.extend([base | 15, base | 0x1F0, base | 0x2F0]);
        for off in [0, 127, 128, 255] {
            words.extend([base | 0x4F0 | off << 20, base | 0x5F0 | off << 20]);
        }
    }
    for (base, subs, n) in [(0xD000_0000, 4..7, 5), (0xE000_0000, 0..2, 12)] {
        for sub in subs {
            for d in 0..n {
                for a in 0..n {
                    for b in 0..n {
                        words.push(base | sub << 16 | b << 8 | a << 4 | d);
                    }
                }
            }
        }
    }
    let mut image = Vec::new();
    for word in words {
        let insn = decode_insn(word).unwrap_or_else(|| panic!("rejected {word:08X}"));
        assert_eq!(insn.major_opcode(), (word >> 28) as u8);
        assert_eq!(encode_insn(&insn), Ok(word));
        image.extend(word.to_le_bytes());
    }
    assert_eq!(assemble(&disassemble_bytes(&image)).unwrap(), image);
}

#[test]
fn random_words_and_incomplete_images_round_trip() {
    let mut seed = 0xcab0_5e00_f00d_d00d;
    let mut legal = 0;
    for batch in 0..200 {
        let mut image = Vec::new();
        for _ in 0..1000 {
            let word = random(&mut seed) as u32;
            if let Some(insn) = decode_insn(word) {
                assert_eq!(encode_insn(&insn), Ok(word));
                legal += 1;
            }
            image.extend(word.to_le_bytes());
        }
        image.extend_from_slice(&[0x00, 0x27, 0xff][..batch % 4]);
        assert_eq!(assemble(&disassemble_bytes(&image)).unwrap(), image);
    }
    assert!(legal > 20_000);
}

#[test]
fn reserved_bits_are_illegal() {
    for word in [
        1,
        0x0001_0010,
        0x0002_0100,
        0x0003_0001,
        0x0015_0000,
        0x1000_1000,
        0x1010_0000,
        0x2009_0000,
        0x2000_1000,
        0x3004_0500,
        0x3000_0A00,
        0x4000_0030,
        0x5001_0000,
        0x6001_0800,
        0x6002_8000,
        0x6003_0100,
        0x7000_0200,
        0x8000_0200,
        0x9000_0040,
        0xB000_0100,
        0xC001_9000,
        0xC000_0310,
        0xC010_0100,
        0xC000_0401,
        0xD004_0005,
        0xD003_0100,
        0xE000_00C0,
        0xE000_1000,
        0xF170_0000,
        0xF011_0000,
    ] {
        assert_eq!(decode_insn(word), None, "{word:08x}");
    }
}

#[test]
fn assembler_layout_relocation_and_padding() {
    let a = assemble_at(
        "
        start: .bytes 0xAA, 0b11, 5  // unaligned origin
        .align8
        AUIPC SP, end
        BNEZ FP, end
        LI64 A5, 0x1234_5678_9ABC_DEF0
        JAL RA, start_aligned
        start_aligned: BR ZERO, 0, start_aligned
        end: .word32 start, end ; relocations
        .word64 end, -1
        .org 0x148 # NOP then trailing data
        .bytes 0xFE
    ",
        0x101,
    )
    .unwrap();
    assert_eq!(
        (
            a.labels["start"],
            a.labels["start_aligned"],
            a.labels["end"]
        ),
        (0x101, 0x124, 0x128)
    );
    assert_eq!(&a.bytes[..3], &[0xAA, 3, 5]);
    assert_eq!(&a.bytes[3..7], &NOP_WORD.to_le_bytes());
    let word =
        |pc: u64| u32::from_le_bytes(a.bytes[(pc - a.origin) as usize..][..4].try_into().unwrap());
    assert_eq!(word(0x108), 0x4000_0821); // (0x128 - 0x108) / 4
    assert_eq!(word(0x10C), 0x9000_0612); // (0x128 - 0x110) / 4
    assert_eq!(word(0x120), 0xA000_0003);
    assert_eq!(word(0x124), 0x9FFF_FF00);
    assert_eq!(
        (word(0x128), word(0x12C), word(0x130), word(0x134)),
        (0x101, 0x128, 0x128, 0)
    );
    assert_eq!(&a.bytes[0x138 - 0x101..0x140 - 0x101], &[255; 8]);
    assert_eq!(
        (word(0x140), word(0x144), a.bytes.last()),
        (NOP_WORD, NOP_WORD, Some(&254))
    );
    assert_eq!(
        assemble(".bytes 5\n.align4\nNOP").unwrap(),
        [5, 0, 0, 0, 0, 0, 6, 0]
    );
    for (i, alias) in [
        "ZERO", "SP", "FP", "RA", "A0", "A1", "A2", "A3", "A4", "A5", "T0", "T1", "T2", "T3", "T4",
        "T5",
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            assemble(&format!("MOV {alias}, {alias}")),
            assemble(&format!("LUT4 R{i}, R{i}, R0, 12"))
        );
    }
}

#[test]
fn rejects_bad_source_at_the_source_line() {
    for source in [
        "x: NOP\nx: HALT",
        "JAL R0,missing",
        "LI64 R0,0x10000000000000000",
        "MOVZ20 R0,0x100000",
        "JAL R0,8388608",
        "AUIPC R0,-524289",
        "BEQZ R0,524288",
        "JALR R0,R1,-32769",
        "LD64 R0,[R1+4]",
        "SST64 [R2+1024],S0",
        "SGET R0,S25",
        "FP5.ADD E5,E0,E0",
        "GF128.MUL P0,P12,P1",
        "KECCAK.F1600 13",
        "BEXTS R1,R1,3,0",
        "CSRR R0,256",
        "NOT R16,R0",
        "SHLI R1,R1,64",
        "HALT 2",
        ".bytes 256",
        ".word32 0x100000000",
        "NOP\n.org 0",
        ".bytes 0\nNOP",
        "JAL R0,x\n.bytes 1\nx:",
        ".align4 2",
    ] {
        let err = assemble(source).expect_err(source);
        assert!(err.line > 0);
    }
    assert_eq!(
        assemble("; comment\n\nJAL R0,undefined").unwrap_err().line,
        3
    );
    assert!(assemble_at(".align8", u64::MAX).is_err());
}

#[test]
fn li64_fixed_four_words_and_zero_register() {
    let mut seed = 1;
    for v in [0, u64::MAX, 1 << 63, 0xdead_beef_0000_0001]
        .into_iter()
        .chain((0..256).map(|_| random(&mut seed)))
    {
        let src = format!("li64 R15,0x{v:X}\nMOV R0,R15\nADDI R1,R0,-1\nHALT");
        let mut m = vm(&src, 28);
        for (i, chunk) in m.mem[..16].chunks_exact(4).enumerate() {
            let w = u32::from_le_bytes(chunk.try_into().unwrap());
            let limb = ((v >> (48 - 16 * i)) & 0xffff) as u32;
            assert_eq!(
                w,
                if i == 0 {
                    0x4000_000F | limb << 8
                } else {
                    0x3000_09FF | limb << 12
                }
            );
        }
        m.regs[0] = 999;
        m.reg_taint[0] = Taint::Secret;
        assert_eq!(m.run(7), RunExit::Halted);
        assert_eq!(
            (m.regs[15], m.regs[1], m.regs[0], m.reg_taint[0]),
            (v, u64::MAX, 0, Taint::Public)
        );
    }
}

#[test]
fn scalar_alu_and_predicates() {
    let (a, b, c) = (0x8000_0000_0000_0081u64, 65, 1);
    for (op, want, cost) in [
        ("ADD", a + b, 1),
        ("SUB", a - b, 1),
        ("SHL", 0, 1),
        ("SHR", 0, 1),
        ("ASR", u64::MAX, 1),
        ("ROL", a.rotate_left(1), 1),
        ("ROR", a.rotate_right(1), 1),
        ("MUL64", a.wrapping_mul(b), 4),
        ("MULHU64", ((a as u128 * b as u128) >> 64) as u64, 4),
    ] {
        assert_eq!(one(&format!("{op} R4,R1,R2"), a, b, c, cost), want, "{op}");
    }
    for (op, i, want) in [
        ("ADDI", "-1", a - 1),
        ("ADDIU", "65535", a + 65535),
        ("XORI", "255", a ^ 255),
        ("ANDI", "255", a & 255),
        ("ORI", "255", a | 255),
        ("SHLI", "63", a << 63),
        ("SHRI", "63", 1),
        ("ASRI", "63", u64::MAX),
        ("ROLI", "63", a.rotate_left(63)),
        ("SLK16", "65535", (a << 16) | 65535),
    ] {
        assert_eq!(one(&format!("{op} R4,R1,{i}"), a, b, c, 1), want, "{op}");
    }
    for (op, want) in [
        ("BEXTS R4,R1,0,1", (-127i64) as u64),
        ("BEXTU R4,R1,0,1", 129),
        ("BEXTS R4,R1,7,8", 128),
        ("BSWAP64 R4,R1", a.swap_bytes()),
        ("SEL R4,R1,R2,R3", b),
        ("MOVS20 R4,-524288", (-524288i64) as u64),
        ("MOVZ20 R4,1048575", 1048575),
    ] {
        assert_eq!(one(op, a, b, c, 1), want, "{op}");
    }
    assert_eq!(one("SEL R4,R1,R2,R3", a, b, 0, 1), a);
    for mask in 0u8..16 {
        let mut want = 0;
        for bit in 0..64 {
            let idx = ((a >> bit) & 1) * 2 + ((b >> bit) & 1);
            want |= u64::from((mask >> idx) & 1) << bit;
        }
        assert_eq!(one(&format!("LUT4 R4,R1,R2,{mask}"), a, b, c, 1), want);
    }
    for (suffix, want) in [
        ("EQ", 0),
        ("NE", 1),
        ("LTU", 0),
        ("LTS", 1),
        ("GEU", 1),
        ("GES", 0),
        ("GTU", 1),
        ("GTS", 0),
        ("LEU", 0),
        ("LES", 1),
    ] {
        assert_eq!(one(&format!("CMP.{suffix} R4,R1,R2"), a, b, c, 1), want);
    }
    for flags in 0..16 {
        for (x, y) in [(a, b), (b, a), (a, a)] {
            let greater = if flags & 4 != 0 {
                (x as i64) > (y as i64)
            } else {
                x > y
            };
            let truth = (flags & 1 != 0 && x == y || flags & 2 != 0 && greater) ^ (flags & 8 != 0);
            assert_eq!(
                one(&format!("CMP R4,R1,R2,{flags}"), x, y, 0, 1),
                truth as u64
            );
        }
    }
}

#[test]
fn control_flow_uses_prestate_and_word_offsets() {
    let mut m = vm(
        "AUIPC R5, target\nJALR R5,R5,0\nHALT\ntarget: JAL RA,after\nHALT\nafter: HALT",
        24,
    );
    assert_eq!(m.run(4), RunExit::Halted);
    assert_eq!(
        (m.pc, m.regs[5], m.regs[3], m.csrs.cycles, m.csrs.instret),
        (24, 8, 16, 4, 4)
    );
    for (op, v, taken) in [
        ("BEQZ", 0, true),
        ("BEQZ", 1, false),
        ("BNEZ", 1, true),
        ("BNEZ", 0, false),
        ("BLTZ", 1 << 63, true),
        ("BLTZ", 1, false),
        ("BGEZ", 1, true),
        ("BGEZ", 1 << 63, false),
    ] {
        let mut m = vm(&format!("back: NOP\n{op} R1,back"), 8);
        m.pc = 4;
        m.regs[1] = v;
        assert_eq!(m.step(), StepOutcome::Retired);
        assert_eq!(
            (m.pc, m.csrs.cycles, m.csrs.instret),
            (if taken { 0 } else { 8 }, 1, 1)
        );
    }
}

#[test]
fn memory_byte_order_scaling_and_lane_transfers() {
    let mut m = vm(
        "ST64 [R1-8],R2\nSLD64 S24,[R1-8]\nSGET R3,S24\nSPUT S2,R2\nSXOR S2,R3\nSST64 [R1+8],S24\nLDBU R4,[R1+15]\nSTB [R1+9],R4\nLD64 R5,[R1+8]\nSZERO\nHALT",
        96,
    );
    m.regs[1] = 72;
    m.regs[2] = 0x89AB_CDEF_0123_4567;
    m.reg_taint[2] = Taint::Secret;
    assert_eq!(m.run(5), RunExit::StepLimit);
    assert_eq!((m.spg[24], m.spg[2], m.regs[3]), (m.regs[2], 0, m.regs[2]));
    assert_eq!(m.spg_taint[2], Taint::Secret);
    assert_eq!(m.run(6), RunExit::Halted);
    assert_eq!((m.regs[4], m.regs[5]), (0x89, 0x89ab_cdef_0123_8967));
    assert_eq!(m.spg, [0; 25]);
    assert_eq!(m.spg_taint, [Taint::Public; 25]);
    assert_eq!(m.csrs.cycles, 17);
    assert_eq!(m.csrs.instret, 11);
    let accesses: Vec<_> = m
        .trace
        .observations
        .iter()
        .filter_map(|o| o.mem_access.map(|a| (a.addr, a.size, a.write)))
        .collect();
    assert_eq!(
        accesses,
        [
            (64, 8, true),
            (64, 8, false),
            (80, 8, true),
            (87, 1, false),
            (81, 1, true),
            (80, 8, false)
        ]
    );
    assert_eq!(&m.mem[64..72], &m.regs[2].to_le_bytes());
    assert_eq!(&m.mem_taint[80..88], &[Taint::Secret; 8]);
    assert!(m.violations.is_empty());
}

#[test]
fn hardware_faults_dispatch_or_halt_atomically() {
    use VmTrap::*;
    for (source, pc, base, cause, word_fetched) in [
        ("NOP", 1, 0, MisalignedPc, false),
        ("NOP", 64, 0, MemFault, false),
        (".WORD32 0xFFFFFFFF", 0, 0, IllegalInsn, true),
        ("LD64 R5,[R5]", 0, 1, MisalignedMem, true),
        ("ST64 [R5],R5", 0, 57, MisalignedMem, true),
        ("ST64 [R5],R5", 0, 56, MemFault, true),
        ("SLD64 S1,[R5]", 0, 56, MemFault, true),
        ("SST64 [R5],S1", 0, 3, MisalignedMem, true),
        ("JALR R5,R5,0", 0, 5, MisalignedPc, true),
        ("LDBU R5,[R5]", 0, u64::MAX, MemFault, true),
        ("CSRR R5,0xFF", 0, 0, IllegalInsn, true),
        ("CSRW R5,DIT", 0, 0, IllegalInsn, true),
    ] {
        for enabled in [false, true] {
            let mut m = vm(source, 60);
            m.pc = pc;
            m.regs[5] = base;
            m.spg[1] = 123;
            m.csrs = Csrs {
                exc_en: enabled,
                evec: 19,
                epc: 44,
                ecause: 9,
                instret: 7,
                cycles: 29,
            };
            let before = m.mem.clone();
            assert_eq!(m.step(), StepOutcome::Trap(cause), "{source}");
            assert_eq!(m.halted, !enabled);
            assert!(!m.csrs.exc_en);
            assert_eq!(
                (m.csrs.cycles, m.csrs.instret, m.csrs.ecause),
                (30, 7, cause as u64)
            );
            assert_eq!(
                (m.pc, m.csrs.epc),
                if enabled { (16, pc) } else { (pc, 44) }
            );
            assert_eq!((m.regs[5], m.spg[1]), (base, 123));
            assert_eq!(m.mem, before);
            let o = m.trace.observations[0];
            assert_eq!(
                (o.pc, o.insn_word.is_some(), o.cycles_after, o.instret_after),
                (pc, word_fetched, 30, 7)
            );
        }
    }
}

#[test]
fn exc_eret_and_counter_write_precedence() {
    let mut m = vm("EXC\nCSRW R1,EVEC\nCSRW R2,EXC_EN\nEXC\nHALT\nERET", 24);
    m.regs[1] = 23;
    m.regs[2] = 3;
    assert_eq!(m.run(3), RunExit::StepLimit);
    assert_eq!((m.csrs.evec, m.csrs.instret, m.csrs.cycles), (20, 3, 3));
    assert_eq!(m.step(), StepOutcome::Trap(VmTrap::EnvCall));
    assert_eq!(
        (
            m.pc,
            m.csrs.epc,
            m.csrs.ecause,
            m.csrs.exc_en,
            m.csrs.instret,
            m.csrs.cycles
        ),
        (20, 16, 2, false, 3, 4)
    );
    assert_eq!(m.run(2), RunExit::Halted);
    assert_eq!(
        (m.pc, m.csrs.instret, m.csrs.cycles, m.csrs.exc_en),
        (20, 5, 6, true)
    );
    assert_eq!(m.step(), StepOutcome::Halted);
    assert_eq!(m.trace.observations.len(), 6);

    let mut m = vm(
        "CSRW R1,CYCLES\nCSRR R2,CYCLES\nCSRW R1,INSTRET\nCSRR R3,INSTRET\nCSRR R4,ARCH_ID\nCSRR R5,WORD_BITS\nCSRR R6,FEATURES\nCSRR R7,DIT\nCSRW R1,DBG_OUT\nCSRW R1,POWER",
        40,
    );
    m.regs[1] = u64::MAX;
    assert_eq!(m.run(10), RunExit::Halted);
    assert_eq!(
        &m.regs[2..8],
        &[u64::MAX, u64::MAX, 0x4153_5332_0000_0001, 64, 15, 1]
    );
    assert_eq!((m.csrs.cycles, m.csrs.instret), (8, 6));
    assert_eq!(m.debug_out, [255]);

    assert_eq!(
        (
            mem_map::IROM_BASE,
            mem_map::ISRAM_BASE,
            mem_map::DSRAM_BASE,
            mem_map::SYS_MMIO_BASE
        ),
        (0, 0x1000, 0x1_0000, 0xFFFF_0000)
    );
}

#[cfg(not(feature = "vm-debug-rx"))]
#[test]
fn base_isa_reserves_debug_input_address() {
    for source in ["CSRR R1,0x0B", "CSRW R1,0x0B"] {
        let mut m = vm(source, 4);
        assert_eq!(m.step(), StepOutcome::Trap(VmTrap::IllegalInsn));
        assert_eq!((m.csrs.instret, m.csrs.cycles), (0, 1));
    }
}

#[cfg(feature = "vm-debug-rx")]
#[test]
fn debug_rx_extension_consumes_each_byte_once() {
    let mut m = vm(
        "CSRR R0,DBG_IN\nCSRR R4,DBG_IN\nCSRR R3,DBG_IN\nCSRW R4,DBG_IN",
        16,
    );
    m.push_debug_in(0x5A);
    m.push_debug_in(0xA5);
    assert_eq!(m.run(3), RunExit::StepLimit);
    assert_eq!((m.regs[0], m.regs[4], m.regs[3]), (0, 0x1A5, 0));
    assert_eq!(m.step(), StepOutcome::Trap(VmTrap::IllegalInsn));
}

#[test]
fn both_zeroize_encodings_wipe_all_registers_and_tags() {
    for source in ["ZEROIZE", "CSRW R1,0x41"] {
        let mut m = vm(source, 8);
        m.regs.fill(u64::MAX);
        m.spg.fill(u64::MAX);
        m.spg_taint.fill(Taint::Secret);
        m.reg_taint.fill(Taint::Secret);
        m.mem[7] = 123;
        m.mem_taint[7] = Taint::Secret;
        assert_eq!(m.step(), StepOutcome::Retired);
        assert_eq!((m.regs, m.spg), ([0; 16], [0; 25]));
        assert_eq!(
            (m.reg_taint, m.spg_taint),
            ([Taint::Public; 16], [Taint::Public; 25])
        );
        assert_eq!(
            (m.mem[7], m.mem_taint[7], m.csrs.cycles, m.csrs.instret),
            (123, Taint::Secret, 1, 1)
        );
    }
    let mut m = vm("CSRW R0,ZEROIZE", 4);
    m.spg[24] = 1;
    m.step();
    assert_eq!(m.spg[24], 1);
}

#[test]
fn goldilocks_and_quintic_reference_products() {
    let p = 0xffff_ffff_0000_0001;
    let (a, b, c) = (u64::MAX, p + 1, p - 1);
    let x = Goldilocks::from_u64_reduced(a);
    let y = Goldilocks::from_u64_reduced(b);
    let z = Goldilocks::from_u64_reduced(c);
    for (src, expected, cost) in [
        ("GL.MAC R4,R1,R2,R3", x * y + z, 4),
        ("GL.ADD R4,R1,R2", x + y, 1),
        ("GL.SUB R4,R2,R1", y - x, 1),
        ("GL.SBOX7 R4,R1", x.pow(7), 12),
    ] {
        assert_eq!(one(src, a, b, c, cost), expected.to_canonical_u64());
    }
    let mut m = vm("FP5.MUL E1,E0,E1", 4);
    m.spg[..10].copy_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    m.spg[10] = 99;
    assert_eq!(m.step(), StepOutcome::Retired);
    assert_eq!(&m.spg[..11], &[1, 2, 3, 4, 5, 348, 337, 295, 220, 110, 99]);
    assert_eq!((m.csrs.cycles, m.csrs.instret), (104, 1));
    let mut seed = 0xAED4_2083;
    for (op, d, b_idx, cost) in [
        ("MUL", 0, 0, 104),
        ("MUL", 0, 4, 104),
        ("MUL", 4, 4, 104),
        ("ADD", 4, 4, 5),
        ("SUB", 0, 4, 5),
    ] {
        let mut m = vm(&format!("FP5.{op} E{d},E0,E{b_idx}"), 4);
        for _ in 0..32 {
            m.spg = core::array::from_fn(|_| random(&mut seed));
            m.spg[2] = p;
            m.spg[20] = u64::MAX;
            let fp = |start: usize| {
                Fp5::from_limbs(core::array::from_fn(|i| {
                    Goldilocks::from_u64_reduced(m.spg[start + i])
                }))
            };
            let (a, b) = (fp(0), fp(b_idx * 5));
            let result = match op {
                "MUL" => a * b,
                "ADD" => a + b,
                _ => a - b,
            };
            let mut expect = m.spg;
            expect[d * 5..d * 5 + 5]
