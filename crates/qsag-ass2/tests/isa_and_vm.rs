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
            mem_map::APPLET_CODE_BASE,
            mem_map::APPLET_DATA_BASE,
            mem_map::SYS_MMIO_BASE
        ),
        (0, 0x1_0000, 0x1_0100, 0xFFFF_0000)
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
                .copy_from_slice(&result.to_limbs().map(Goldilocks::to_canonical_u64));
            m.pc = 0;
            let before = m.csrs.cycles;
            assert_eq!(m.step(), StepOutcome::Retired);
            assert_eq!(m.spg, expect);
            assert_eq!(m.csrs.cycles - before, cost);
        }
    }
}

#[test]
fn binary_field_reduction_and_aliasing() {
    let mut m = vm(
        "GF128.MUL P11,P0,P11\nGF128.MUL P0,P0,P0\nGF128.XOR P0,P11,P0",
        12,
    );
    m.spg[0] = 2;
    m.spg[23] = 1 << 63;
    m.spg[24] = 99;
    m.step();
    assert_eq!(&m.spg[22..], &[0x87, 0, 99]);
    m.step();
    assert_eq!(&m.spg[..2], &[4, 0]);
    m.step();
    assert_eq!(&m.spg[..2], &[0x83, 0]);
    assert_eq!((m.csrs.cycles, m.csrs.instret), (9, 3));
    // A high operand limb contributes even when the destination overwrites both inputs.
    let mut m = vm("GF128.MUL P0,P0,P0", 4);
    m.spg[1] = 1; // x^64 squared = x^128
    m.step();
    assert_eq!(&m.spg[..2], &[0x87, 0]);
}

#[test]
fn keccak_last_rounds_match_independent_reference() {
    let mut seed = 42;
    for rounds in [12, 24] {
        for sample in 0..16 {
            let mut m = vm(&format!("KECCAK.F1600 {rounds}"), 4);
            if sample > 0 {
                m.spg = core::array::from_fn(|_| random(&mut seed));
            }
            let mut expected = m.spg;
            if rounds == 12 {
                qsag_agg::sponge::keccak_p1600_12(&mut expected);
            } else {
                qsag_agg::sponge::keccak_f1600(&mut expected);
            }
            assert_eq!(m.step(), StepOutcome::Retired);
            assert_eq!(m.spg, expected);
            assert_eq!((m.csrs.cycles, m.csrs.instret), (rounds, 1));
        }
    }
}

#[test]
fn poseidon_known_answers_and_bank_boundaries() {
    let mut m = vm("POSEIDON2.GL24", 4);
    m.spg = core::array::from_fn(|i| i as u64);
    m.spg_taint[0] = Taint::Secret;
    assert_eq!(m.step(), StepOutcome::Retired);
    // Sequence KAT from the lane's qsag-accel, also computed by the Python RTL model.
    assert_eq!(
        m.spg,
        [
            9262813872168818283,
            14473920968081642809,
            3132432025506878070,
            739327372316014541,
            13930273445042610257,
            9887230855574303117,
            10411529172945029295,
            2610146355123527807,
            15800955794096892263,
            126337761019280528,
            15741922631823646152,
            12261346758669164007,
            2093389069744887410,
            3165987204040455923,
            14526830091420603371,
            2537012170462392522,
            17818886402825694850,
            14929111493621950133,
            16221575831479706027,
            10965213893411960579,
            16472025002487739980,
            12534132784495569014,
            13110610053613593246,
            5468252370409873572,
            24
        ]
    );
    assert_eq!(m.csrs.cycles, 216);
    assert_eq!(m.spg_taint[..24], [Taint::Secret; 24]);
    assert_eq!(m.spg_taint[24], Taint::Public);
    let mut m = vm("POSEIDON2.GL12", 4);
    m.spg = core::array::from_fn(|i| i as u64);
    m.spg_taint[12] = Taint::Secret;
    let mut expected = m.spg;
    let mut state = core::array::from_fn(|i| Goldilocks::from_u64_reduced(i as u64));
    qsag_agg::sponge::poseidon2_perm12(&mut state);
    expected[..12].copy_from_slice(&state.map(Goldilocks::to_canonical_u64));
    assert_eq!(m.step(), StepOutcome::Retired);
    assert_eq!(m.spg, expected);
    assert_eq!(m.csrs.cycles, 120);
    assert_eq!(m.spg_taint[..12], [Taint::Public; 12]);
}

#[test]
fn dit_traces_match_across_secrets() {
    let image = assemble(
        "
        LDBU R3,[R1]
        SEL R4,R5,R6,R3
        ST64 [R1+8],R4
        SLD64 S0,[R1+8]
        FP5.MUL E0,E0,E0
        KECCAK.F1600 12
        SST64 [R1+16],S24
        LD64 R7,[R1+16]
        HALT
    ",
    )
    .unwrap();
    let execute = |secret| {
        let mut m = Ass2Vm::new(88);
        m.load_image(0, &image).unwrap();
        m.regs[1] = 64;
        m.regs[5] = 0xFEED;
        m.regs[6] = 0xFACE;
        m.mem[64] = secret;
        m.mem_taint[64] = Taint::Secret;
        m.dit_mode = DitMode::Trap;
        assert_eq!(m.run(9), RunExit::Halted);
        assert!(m.violations.is_empty());
        for i in [3, 4, 7] {
            assert_eq!(m.reg_taint[i], Taint::Secret);
        }
        assert_eq!(m.spg_taint, [Taint::Secret; 25]);
        assert_eq!(m.mem_taint[72..88], [Taint::Secret; 16]);
        assert_eq!((m.csrs.instret, m.csrs.cycles), (9, 128));
        m
    };
    let (a, b) = (execute(0), execute(255));
    assert_ne!(a.regs[4], b.regs[4]);
    assert_ne!(a.spg, b.spg);
    assert_eq!(a.trace, b.trace);
    assert_eq!(a.trace.observations.len(), 9);
    for (i, observation) in a.trace.observations.iter().enumerate() {
        assert_eq!(observation.pc, i as u64 * 4);
        assert_eq!(
            observation.insn_word,
            Some(u32::from_le_bytes(
                image[4 * i..4 * i + 4].try_into().unwrap()
            ))
        );
        assert_eq!(observation.instret_after, i as u64 + 1);
    }
    for secret_operand in [1, 2, 3] {
        let mut m = vm("SEL R1,R1,R2,R3", 4);
        m.reg_taint[secret_operand] = Taint::Secret;
        assert_eq!(m.step(), StepOutcome::Retired);
        assert_eq!(m.reg_taint[1], Taint::Secret);
        assert!(m.violations.is_empty());
    }
}

#[test]
fn dit_audit_and_stop_for_each_sensitive_operand() {
    use DitViolationKind::*;
    for (src, kind) in [
        ("BNEZ R5,0", SecretBranchCond),
        ("JALR R5,R5,0", SecretJumpTarget),
        ("LD64 R5,[R5]", SecretMemAddr),
        ("ST64 [R5],R2", SecretMemAddr),
        ("LDBU R5,[R5]", SecretMemAddr),
        ("STB [R5],R2", SecretMemAddr),
        ("SLD64 S24,[R5]", SecretMemAddr),
        ("SST64 [R5],S24", SecretMemAddr),
    ] {
        for mode in [DitMode::Audit, DitMode::Trap] {
            let mut m = vm(src, 24);
            m.regs[5] = 16;
            m.reg_taint[5] = Taint::Secret;
            m.dit_mode = mode;
            let v = DitViolation {
                pc: 0,
                reg: 5,
                kind,
            };
            let before = (m.regs, m.mem.clone(), m.spg);
            let outcome = m.step();
            assert_eq!(m.violations, [v], "{src}");
            if mode == DitMode::Trap {
                assert_eq!(outcome, StepOutcome::DitViolation(v));
                assert_eq!((m.pc, m.csrs.cycles, m.csrs.instret), (0, 0, 0));
                assert_eq!(m.trace.observations[0].mem_access, None);
                assert_eq!((m.regs, m.mem, m.spg), before);
            } else {
                assert_eq!(outcome, StepOutcome::Retired);
                assert_eq!(m.csrs.instret, 1);
            }
        }
    }
    // A CSR round trip cannot launder a branch operand.
    let mut m = vm("CSRW R1,EPC\nCSRR R2,EPC\nBEQZ R2,0", 12);
    m.reg_taint[1] = Taint::Secret;
    assert_eq!(m.run(3), RunExit::StepLimit);
    assert_eq!(
        m.violations,
        [DitViolation {
            pc: 8,
            reg: 2,
            kind: SecretBranchCond
        }]
    );
}

#[test]
fn r0_is_a_sink_for_every_writer() {
    // Every instruction with a register destination, aimed at R0 with a non-zero result.
    for (src, cost) in [
        ("CSRR R0,ARCH_ID", 1),
        ("JAL R0,0", 1),
        ("JALR R0,R1,0", 1),
        ("LD64 R0,[R2]", 2),
        ("LDBU R0,[R2+7]", 2),
        ("SGET R0,S3", 1),
        ("ADD R0,R3,R3", 1),
        ("SUB R0,R3,R4", 1),
        ("ROL R0,R3,R3", 1),
        ("MUL64 R0,R3,R3", 4),
        ("MULHU64 R0,R4,R4", 4),
        ("ADDI R0,R3,1", 1),
        ("SLK16 R0,R3,1", 1),
        ("MOVZ20 R0,5", 1),
        ("MOVS20 R0,-1", 1),
        ("AUIPC R0,1", 1),
        ("LUT4 R0,R3,R3,15", 1),
        ("CMP.EQ R0,R3,R3", 1),
        ("SEL R0,R3,R3,R3", 1),
        ("BEXTU R0,R3,0,8", 1),
        ("BEXTS R0,R4,0,1", 1),
        ("BSWAP64 R0,R3", 1),
        ("GL.MAC R0,R3,R3,R3", 4),
        ("GL.ADD R0,R3,R3", 1),
        ("GL.SUB R0,R3,R4", 1),
        ("GL.SBOX7 R0,R3", 12),
    ] {
        let mut m = vm(&format!("{src}\nADDI R6,R0,7\nHALT"), 40);
        m.regs[1] = 4;
        m.regs[2] = 32;
        m.regs[3] = 0x1234_5678_9abc_def1;
        m.regs[4] = u64::MAX;
        m.spg[3] = 77;
        m.mem[32..40].fill(0xff);
        m.mem_taint[32..40].fill(Taint::Secret);
        m.reg_taint[3] = Taint::Secret;
        m.reg_taint[4] = Taint::Secret;
        m.spg_taint[3] = Taint::Secret;
        m.dit_mode = DitMode::Trap;
        let before = m.regs;
        assert_eq!(m.step(), StepOutcome::Retired, "{src}");
        assert_eq!(m.regs, before, "{src}");
        assert_eq!((m.regs[0], m.reg_taint[0]), (0, Taint::Public), "{src}");
        // The discarded write still retires at the fixed cost and transfers control.
        assert_eq!((m.pc, m.csrs.cycles, m.csrs.instret), (4, cost, 1), "{src}");
        assert_eq!(m.run(2), RunExit::Halted, "{src}");
        assert_eq!((m.regs[6], m.reg_taint[6]), (7, Taint::Public), "{src}");
        assert!(m.violations.is_empty(), "{src}");
    }
    // A load into R0 still performs and reports its access, and still faults.
    let mut m = vm("LD64 R0,[R2]", 16);
    m.regs[2] = 8;
    m.mem[8] = 9;
    assert_eq!(m.step(), StepOutcome::Retired);
    assert_eq!(
        m.trace.observations[0].mem_access,
        Some(MemAccess {
            addr: 8,
            size: 8,
            write: false
        })
    );
    for (base, cause) in [(9, VmTrap::MisalignedMem), (16, VmTrap::MemFault)] {
        let mut m = vm("LD64 R0,[R2]", 16);
        m.regs[2] = base;
        assert_eq!(m.step(), StepOutcome::Trap(cause));
    }
    // An undefined CSR read traps even when the destination is R0.
    let mut m = vm("CSRR R0,0x07", 4);
    assert_eq!(m.step(), StepOutcome::Trap(VmTrap::IllegalInsn));
    // Stores, branches and lane writes read R0 as zero.
    let mut m = vm(
        "ST64 [R0+32],R0\nSPUT S1,R0\nSXOR S2,R0\nBEQZ R0,1\nHALT\nBNEZ R0,-2\nHALT",
        40,
    );
    m.mem[32..40].fill(0xee);
    m.spg[1] = 5;
    m.spg[2] = 6;
    assert_eq!(m.run(8), RunExit::Halted);
    assert_eq!(
        (&m.mem[32..40], m.spg[1], m.spg[2], m.pc),
        (&[0u8; 8][..], 0, 6, 28)
    );
    assert_eq!(m.csrs.instret, 6);
}

#[test]
fn counter_writes_take_the_written_value_exactly() {
    let mut m = vm(
        "CSRW R1,INSTRET\nCSRR R2,INSTRET\nCSRR R3,INSTRET\nCSRW R1,CYCLES\nMUL64 R4,R1,R1\nCSRR R5,CYCLES\nCSRW R0,CYCLES\nCSRR R6,CYCLES\nCSRR R7,INSTRET\nCSRW R0,INSTRET\nHALT",
        44,
    );
    m.regs[1] = 1000;
    // The writing instruction leaves exactly the written value and still costs its cycle.
    assert_eq!(m.step(), StepOutcome::Retired);
    assert_eq!((m.csrs.instret, m.csrs.cycles), (1000, 1));
    assert_eq!(m.run(3), RunExit::StepLimit);
    assert_eq!((m.csrs.instret, m.csrs.cycles), (1003, 1000));
    assert_eq!(m.run(5), RunExit::StepLimit);
    // A read sees the counter before its own retirement.
    assert_eq!(&m.regs[2..8], &[1000, 1001, 1_000_000, 1004, 0, 1007]);
    assert_eq!(m.step(), StepOutcome::Retired);
    assert_eq!((m.csrs.instret, m.csrs.cycles), (0, 3));
    assert_eq!(m.step(), StepOutcome::Halted);
    assert_eq!((m.csrs.instret, m.csrs.cycles), (1, 4));
    let observed: Vec<_> = m
        .trace
        .observations
        .iter()
        .map(|o| (o.instret_after, o.cycles_after))
        .collect();
    assert_eq!(observed[0], (1000, 1));
    assert_eq!(observed[3], (1003, 1000));
    assert_eq!(observed[6], (1006, 0));
}

#[test]
fn zeroize_csr_acts_on_bit_zero_only() {
    for (value, wipes) in [
        (0, false),
        (2, false),
        (u64::MAX - 1, false),
        (1, true),
        (3, true),
        (1 << 63 | 1, true),
        (u64::MAX, true),
    ] {
        let mut m = vm("CSRW R9,ZEROIZE\nHALT", 16);
        m.regs = core::array::from_fn(|i| 0x100 + i as u64);
        m.regs[9] = value;
        m.spg = core::array::from_fn(|i| 0x200 + i as u64);
        m.reg_taint.fill(Taint::Secret);
        m.spg_taint.fill(Taint::Secret);
        m.reg_taint[9] = Taint::Public;
        m.csrs.evec = 0x40;
        m.csrs.epc = 0x44;
        m.csrs.ecause = 3;
        m.mem[8] = 0x5a;
        m.mem_taint[8] = Taint::Secret;
        let (regs, spg) = (m.regs, m.spg);
        assert_eq!(m.step(), StepOutcome::Retired, "{value:#x}");
        if wipes {
            assert_eq!((m.regs, m.spg), ([0; 16], [0; 25]), "{value:#x}");
            assert_eq!(m.reg_taint, [Taint::Public; 16]);
            assert_eq!(m.spg_taint, [Taint::Public; 25]);
        } else {
            let mut expect = regs;
            expect[0] = 0;
            assert_eq!((m.regs, m.spg), (expect, spg), "{value:#x}");
            assert_eq!(m.reg_taint[1], Taint::Secret);
            assert_eq!(m.spg_taint, [Taint::Secret; 25]);
        }
        // The wipe is the register banks only.
        assert_eq!((m.csrs.evec, m.csrs.epc, m.csrs.ecause), (0x40, 0x44, 3));
        assert_eq!((m.mem[8], m.mem_taint[8]), (0x5a, Taint::Secret));
        assert_eq!(
            (m.pc, m.csrs.cycles, m.csrs.instret, m.halted),
            (4, 1, 1, false)
        );
    }
}

#[test]
fn jalr_links_after_reading_its_own_base() {
    for (base, simm, target) in [
        (24u64, -2i64, 16u64),
        (8, 2, 16),
        (16, 0, 16),
        (u64::MAX - 3, 5, 16),
        (0x2_0010, -32768, 16),
    ] {
        let mut m = vm(&format!("JALR R5,R5,{simm}\nHALT\nHALT\nHALT\nHALT"), 20);
        m.regs[5] = base;
        assert_eq!(m.step(), StepOutcome::Retired, "{base:#x} {simm}");
        assert_eq!((m.pc, m.regs[5]), (target, 4), "{base:#x} {simm}");
        assert_eq!(m.reg_taint[5], Taint::Public);
    }
    // A misaligned target traps before the link is written.
    for low in 1..4 {
        let mut m = vm("JALR R5,R5,1", 4);
        m.regs[5] = 8 + low;
        assert_eq!(m.step(), StepOutcome::Trap(VmTrap::MisalignedPc));
        assert_eq!((m.pc, m.regs[5]), (0, 8 + low));
    }
}

#[test]
fn byte_extract_every_index_and_length() {
    for a in [0x80f1_e2d3_c4b5_a697u64, 0x0123_4567_89ab_cdef, u64::MAX, 0] {
        for idx in 0..8u32 {
            for len in 1..=8u32 {
                // Bytes past the top of the word read as zero, so a field that runs off the
                // end has a clear sign bit.
                let field = (u128::from(a) >> (8 * idx)) & ((1u128 << (8 * len)) - 1);
                let unsigned = field as u64;
                let signed = if len < 8 && (field >> (8 * len - 1)) & 1 == 1 {
                    unsigned | (u64::MAX << (8 * len))
                } else {
                    unsigned
                };
                assert_eq!(
                    one(&format!("BEXTU R4,R1,{idx},{len}"), a, 0, 0, 1),
                    unsigned,
                    "BEXTU {a:#x} {idx} {len}"
                );
                assert_eq!(
                    one(&format!("BEXTS R4,R1,{idx},{len}"), a, 0, 0, 1),
                    signed,
                    "BEXTS {a:#x} {idx} {len}"
                );
            }
        }
    }
    // Length eight is the encoding with a zero length field.
    assert_eq!(
        assemble("BEXTU R4,R1,0,8").unwrap(),
        0x6001_0014u32.to_le_bytes()
    );
    assert_eq!(
        assemble("BEXTS R4,R1,7,8").unwrap(),
        0x6002_0714u32.to_le_bytes()
    );
    // Spot values: a whole word, a field that runs off the end, and one that does not.
    let a = 0x80f1_e2d3_c4b5_a697;
    assert_eq!(one("BEXTS R4,R1,0,8", a, 0, 0, 1), a);
    assert_eq!(one("BEXTS R4,R1,6,4", a, 0, 0, 1), 0x80f1);
    assert_eq!(one("BEXTU R4,R1,6,4", a, 0, 0, 1), 0x80f1);
    assert_eq!(one("BEXTS R4,R1,6,2", a, 0, 0, 1), 0xffff_ffff_ffff_80f1);
    assert_eq!(one("BEXTS R4,R1,7,1", a, 0, 0, 1), 0xffff_ffff_ffff_ff80);
}

#[test]
fn register_shifts_saturate_on_the_full_amount() {
    let amounts = [
        0,
        1,
        31,
        63,
        64,
        65,
        127,
        128,
        1 << 32,
        1 << 40,
        (1 << 40) + 1,
        (1 << 40) + 63,
        1 << 63,
        u64::MAX,
    ];
    for a in [0x8000_0000_0000_0081u64, 0x7fff_ffff_ffff_ff7e, 1, u64::MAX] {
        for b in amounts {
            // Shifts use the whole amount, in wide arithmetic. Rotates use its low six bits.
            let shl = if b >= 64 {
                0
            } else {
                ((u128::from(a) << b) & u128::from(u64::MAX)) as u64
            };
            let shr = if b >= 64 {
                0
            } else {
                (u128::from(a) >> b) as u64
            };
            let fill = if a >> 63 == 1 { u64::MAX } else { 0 };
            let asr = if b >= 64 {
                fill
            } else {
                (i128::from(a as i64) >> b) as u64
            };
            let k = b & 63;
            let rol = if k == 0 {
                a
            } else {
                (a << k) | (a >> (64 - k))
            };
            let ror = if k == 0 {
                a
            } else {
                (a >> k) | (a << (64 - k))
            };
            for (op, want) in [
                ("SHL", shl),
                ("SHR", shr),
                ("ASR", asr),
                ("ROL", rol),
                ("ROR", ror),
            ] {
                assert_eq!(
                    one(&format!("{op} R4,R1,R2"), a, b, 0, 1),
                    want,
                    "{op} {a:#x} {b:#x}"
                );
            }
        }
    }
    // An amount whose low six bits are zero is not a shift by zero.
    let a = 0x8000_0000_0000_0081;
    assert_eq!(one("SHL R4,R1,R2", a, 1 << 40, 0, 1), 0);
    assert_eq!(one("SHR R4,R1,R2", a, 1 << 40, 0, 1), 0);
    assert_eq!(one("ASR R4,R1,R2", a, 1 << 40, 0, 1), u64::MAX);
    assert_eq!(one("ASR R4,R1,R2", a >> 1, 1 << 40, 0, 1), 0);
    assert_eq!(one("ROL R4,R1,R2", a, 1 << 40, 0, 1), a);
    // Shifting a register by itself reads the operand once.
    let mut m = vm("SHL R1,R1,R1\nASR R2,R2,R2", 8);
    m.regs[1] = 3;
    m.regs[2] = 1 << 63;
    m.run(2);
    assert_eq!((m.regs[1], m.regs[2]), (24, u64::MAX));
}

#[test]
fn keccak_round_window_matches_published_vectors() {
    // Keccak-f[1600] of the zero state (the Keccak team's reference state, first lane).
    let mut m = vm("KECCAK.F1600 24", 4);
    m.step();
    assert_eq!(m.spg[0], 0xF125_8F79_40E1_DDE7);
    // RFC 9861 TurboSHAKE256 of the empty message with D = 0x1F, first 32 bytes: one block
    // through the last twelve rounds.
    let mut m = vm(
        "SZERO\nMOVZ20 R1,0x1F\nSPUT S0,R1\nLI64 R2,0x8000000000000000\nSPUT S16,R2\nKECCAK.F1600 12\nHALT",
        44,
    );
    assert_eq!(m.run(16), RunExit::Halted);
    let out: Vec<u8> = m.spg[..4].iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(
        out,
        [
            0x36, 0x7A, 0x32, 0x9D, 0xAF, 0xEA, 0x87, 0x1C, 0x78, 0x02, 0xEC, 0x67, 0xF9, 0x05,
            0xAE, 0x13, 0xC5, 0x76, 0x95, 0xDC, 0x2C, 0x66, 0x63, 0xC6, 0x10, 0x35, 0xF5, 0x9A,
            0x18, 0xF8, 0xE7, 0xDB
        ]
    );
    // Twelve rounds are the last twelve: twelve more from the first-half state is not f.
    let mut twice = vm("KECCAK.F1600 12\nKECCAK.F1600 12", 8);
    twice.spg[0] = 1;
    twice.run(2);
    let mut full = vm("KECCAK.F1600 24", 4);
    full.spg[0] = 1;
    full.step();
    assert_ne!(twice.spg, full.spg);
    assert_eq!((twice.csrs.cycles, full.csrs.cycles), (24, 24));
}

#[test]
fn dit_auditor_covers_control_csrs_eret_and_fetch() {
    use DitViolationKind::*;
    // A secret written to a CSR that steers control flow or the public counters.
    for name in ["EVEC", "POWER", "INSTRET", "CYCLES", "EXC_EN", "ZEROIZE"] {
        for mode in [DitMode::Audit, DitMode::Trap] {
            let mut m = vm(&format!("CSRW R5,{name}"), 4);
            m.regs[5] = 0x41;
            m.regs[7] = 9;
            m.reg_taint[5] = Taint::Secret;
            m.dit_mode = mode;
            let outcome = m.step();
            let v = DitViolation {
                pc: 0,
                reg: 5,
                kind: SecretControlCsr,
            };
            assert_eq!(m.violations, [v], "{name}");
            if mode == DitMode::Trap {
                assert_eq!(outcome, StepOutcome::DitViolation(v));
                assert_eq!(
                    (m.csrs, m.halted, m.pc, m.regs[7]),
                    (Csrs::default(), false, 0, 9)
                );
            }
        }
        let mut m = vm(&format!("CSRW R5,{name}"), 4);
        m.dit_mode = DitMode::Trap;
        assert!(!matches!(m.step(), StepOutcome::DitViolation(_)), "{name}");
        assert!(m.violations.is_empty());
    }
    // Secrets may pass through the data CSRs and leave through DBG_OUT.
    let mut m = vm(
        "CSRW R5,EPC\nCSRW R5,ECAUSE\nCSRW R5,DBG_OUT\nCSRR R6,ECAUSE\nERET",
        20,
    );
    m.regs[5] = 16;
    m.reg_taint[5] = Taint::Secret;
    m.dit_mode = DitMode::Trap;
    assert_eq!(m.run(4), RunExit::StepLimit);
    assert!(m.violations.is_empty());
    assert_eq!(
        (m.regs[6], m.reg_taint[6], &m.debug_out[..]),
        (16, Taint::Secret, &[16u8][..])
    );
    // Returning to that secret EPC is a secret jump.
    let v = DitViolation {
        pc: 16,
        reg: 0,
        kind: SecretJumpTarget,
    };
    assert_eq!(m.step(), StepOutcome::DitViolation(v));
    assert_eq!((m.pc, m.csrs.exc_en), (16, false));
    // A trap entry replaces EPC with the public PC, and ERET is clean again.
    let mut m = vm("CSRW R5,EPC\nCSRW R1,EXC_EN\nEXC\nHALT\nERET", 20);
    m.regs[1] = 1;
    m.reg_taint[5] = Taint::Secret;
    m.csrs.evec = 16;
    m.dit_mode = DitMode::Trap;
    assert_eq!(m.run(8), RunExit::Halted);
    assert!(m.violations.is_empty());
    assert_eq!(m.pc, 16);
    // Instruction bytes that are secret make the fetched word, and so the trace, secret.
    for mode in [DitMode::Audit, DitMode::Trap] {
        let mut m = vm("NOP\nADDI R1,R0,5\nHALT", 12);
        m.mem_taint[7] = Taint::Secret;
        m.dit_mode = mode;
        let v = DitViolation {
            pc: 4,
            reg: 0,
            kind: SecretInsnFetch,
        };
        if mode == DitMode::Trap {
            assert_eq!(m.run(3), RunExit::DitViolation(v));
            assert_eq!((m.pc, m.regs[1], m.csrs.instret), (4, 0, 1));
        } else {
            assert_eq!(m.run(3), RunExit::Halted);
            assert_eq!(m.regs[1], 5);
        }
        assert_eq!(m.violations, [v]);
    }
    // Secret data beside public operands is not a violation.
    let mut m = vm(
        "BNEZ R1,0\nLD64 R6,[R2]\nST64 [R2+8],R5\nSLD64 S0,[R2]\nSST64 [R2+16],S1\nJALR R7,R3,0\nHALT",
        56,
    );
    m.regs[2] = 32;
    m.regs[3] = 24;
    m.regs[5] = 0xdead;
    m.reg_taint[5] = Taint::Secret;
    m.reg_taint[6] = Taint::Secret;
    m.spg_taint.fill(Taint::Secret);
    m.mem_taint[32..56].fill(Taint::Secret);
    m.dit_mode = DitMode::Trap;
    assert_eq!(m.run(8), RunExit::Halted);
    assert!(m.violations.is_empty());
    assert_eq!(
        (m.reg_taint[6], m.reg_taint[7]),
        (Taint::Secret, Taint::Public)
    );
}

#[test]
fn tooth_two_ring_wx_mpu_enforces_ring0_and_ring3_permissions_and_mmio_fence() {
    use qsag_ass2::{Cause, EnclaveError, LcState};

    let k_root = [0x5Au8; 32];

    // 1. Ring 0 (`applet_exec = false`):
    //    * 0x0000..=0x0FFF (`I-ROM`): R+X, !W
    //    * 0x10000..=0x101FF (`SRAM`): R+W, !X
    //    * 0xFFFF_0000 (`SYS_MMIO`): accessible (Vault/PUF/LC_STATE R-only, FRAM_XFER R+W, !X)
    let mut r0 = Ass2Vm::new_enclave(k_root, LcState::PROVISIONED_SIGNED_APPLETS);
    r0.mmio.puf_syndrome = [0x1122_3344_5566_7788, 0x99AA_BBCC_DDEE_FF00];
    let rom_ok = assemble(
        "LD64 R1,[R0]
         MOVZ20 R2,0x10000
         ADDI R3,R0,42
         ST64 [R2],R3
         LD64 R4,[R2]
         MOVZ20 R5,0xFFFF0
         SHLI R5,R5,12
         LD64 R6,[R5+0x10]
         LD64 R7,[R5+0x30]
         LD64 R8,[R5+0x50]
         ST64 [R5],R3
         LD64 R9,[R5]
         HALT",
    )
    .unwrap();
    r0.load_image(mem_map::IROM_BASE, &rom_ok).unwrap();
    assert!(!r0.applet_exec);
    assert_eq!(r0.run(32), RunExit::Halted);
    assert_eq!(r0.regs[4], 42);
    assert_eq!(r0.regs[6], u64::from_le_bytes([0x5Au8; 8]));
    assert_eq!(r0.reg_taint[6], Taint::Secret);
    assert_eq!(r0.regs[7], 0x1122_3344_5566_7788);
    assert_eq!(r0.reg_taint[7], Taint::Secret);
    assert_eq!(
        r0.regs[8],
        LcState::PROVISIONED_SIGNED_APPLETS.to_mmio_u64()
    );
    assert_eq!(r0.regs[9], 42);

    // Ring 0 write to `I-ROM` (`0x0000..=0x0FFF`) MUST fault (`!W`).
    let mut r0_rom_write = Ass2Vm::new_enclave(k_root, LcState::Blank);
    r0_rom_write
        .load_image(0, &assemble("ST64 [R0],R0\nHALT").unwrap())
        .unwrap();
    assert_eq!(r0_rom_write.run(8), RunExit::Trap(Cause::MemFault));

    // Ring 0 jump/fetch into `SRAM` (`0x10000..=0x101FF`) MUST fault (`!X`).
    let mut r0_sram_exec = Ass2Vm::new_enclave(k_root, LcState::Blank);
    r0_sram_exec
        .load_image(
            mem_map::SRAM_BASE,
            &assemble("HALT").unwrap(),
        )
        .unwrap();
    r0_sram_exec
        .load_image(
            0,
            &assemble("MOVZ20 R1,0x10000\nJALR R0,R1,0").unwrap(),
        )
        .unwrap();
    assert_eq!(r0_sram_exec.run(8), RunExit::Trap(Cause::MemFault));

    // Ring 0 write to read-only `MMIO_VAULT_KEY` MUST fault (`!W`).
    let mut r0_vault_write = Ass2Vm::new_enclave(k_root, LcState::Blank);
    r0_vault_write
        .load_image(
            0,
            &assemble("MOVZ20 R5,0xFFFF0\nSHLI R5,R5,12\nST64 [R5+0x10],R0\nHALT").unwrap(),
        )
        .unwrap();
    assert_eq!(r0_vault_write.run(8), RunExit::Trap(Cause::MemFault));

    // 2. Ring 3 (`applet_exec = true`):
    //    * Lower 256 B (`0x10000..=0x100FF`, <= 64 insns): R+X, !W
    //    * Upper 256 B (`0x10100..=0x101FF`): R+W, !X
    //    * Any `0xFFFF_0000` MMIO or `I-ROM` access faults with `Cause::MemFault`!
    let words_from_asm = |src: &str| -> Vec<u32> {
        assemble(src)
            .unwrap()
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
            .collect()
    };

    let mut r3_ok = Ass2Vm::new_enclave(k_root, LcState::Blank);
    let ok_words = words_from_asm(
        "MOVZ20 R3,0x10000
         LD64 R4,[R3]
         MOVZ20 R5,0x10100
         ST64 [R5],R4
         LD64 R6,[R5]
         HALT",
    );
    r3_ok.load_open_applet(&ok_words).unwrap();
    assert!(r3_ok.applet_exec);
    assert_eq!(r3_ok.run(16), RunExit::Halted);
    assert_eq!(r3_ok.regs[6], r3_ok.regs[4]);
    assert_ne!(r3_ok.regs[6], 0);

    for bad_applet in [
        // Self-modifying write to lower 256 B (`0x10000..=0x100FF` is `!W`).
        "MOVZ20 R3,0x10000\nST64 [R3],R0\nHALT",
        // Byte write to `0x100FF` (end of lower 256 B code window).
        "MOVZ20 R3,0x100FF\nSTB [R3],R0\nHALT",
        // Execute from upper 256 B (`0x10100..=0x101FF` is `!X`).
        "MOVZ20 R3,0x10100\nJALR R0,R3,0",
        // Read `0xFFFF_0000` MMIO (`FRAM_XFER`) from Ring 3 -> `Cause::MemFault`.
        "MOVZ20 R5,0xFFFF0\nSHLI R5,R5,12\nLD64 R6,[R5]\nHALT",
        // Read `0xFFFF_0010` MMIO (`VAULT_KEY`) via `LDBU` from Ring 3 -> `Cause::MemFault`.
        "MOVZ20 R5,0xFFFF0\nSHLI R5,R5,12\nLDBU R6,[R5+0x10]\nHALT",
        // Misaligned access inside `0xFFFF_0000` MMIO from Ring 3 -> `Cause::MemFault` (never `MisalignedMem`).
        "MOVZ20 R5,0xFFFF0\nSHLI R5,R5,12\nADDI R5,R5,3\nLD64 R6,[R5]\nHALT",
        // Write `0xFFFF_0000` MMIO from Ring 3 -> `Cause::MemFault`.
        "MOVZ20 R5,0xFFFF0\nSHLI R5,R5,12\nST64 [R5],R0\nHALT",
        // Read `I-ROM` (`0x0000`) from Ring 3 -> `Cause::MemFault`.
        "LD64 R6,[R0]\nHALT",
        // Jump to `I-ROM` (`0x0000`) from Ring 3 -> `Cause::MemFault`.
        "JALR R0,R0,0",
    ] {
        let mut vm = Ass2Vm::new_enclave(k_root, LcState::Blank);
        vm.load_image(mem_map::APPLET_DATA_BASE, &assemble("HALT").unwrap())
            .unwrap();
        vm.load_open_applet(&words_from_asm(bad_applet)).unwrap();
        assert_eq!(vm.run(16), RunExit::Trap(Cause::MemFault), "{bad_applet}");
    }

    // 64-insn boundary: exactly 64 instructions succeeds; 65 instructions is rejected!
    let mut max64 = vec![qsag_ass2::isa::NOP_WORD; 63];
    max64.push(0x0005_0000); // HALT at 0x100FC
    let mut vm64 = Ass2Vm::new_enclave(k_root, LcState::Blank);
    vm64.load_open_applet(&max64).unwrap();
    assert_eq!(vm64.run(80), RunExit::Halted);

    let over65 = vec![qsag_ass2::isa::NOP_WORD; 65];
    assert_eq!(
        vm64.load_open_applet(&over65),
        Err(EnclaveError::AppletWordCountOutOfRange)
    );
}

#[test]
fn tooth_lifecycle_modes_enforce_signed_applet_key_injection_scrub_and_rom_lock() {
    use qsag_ass2::wire::{
        compute_code_hash, derive_applet_key, load_code_open_frame, load_code_wotsc_frame,
        owner_wotsc_pubkey,
    };
    use qsag_ass2::{EnclaveError, LcState};

    let k_root: [u8; 32] = core::array::from_fn(|i| (0xA0 + i) as u8);
    let sk0 = [0x31u8; 32];
    let sk1 = [0x42u8; 32];
    let sk2 = [0x53u8; 32];
    let pk0 = owner_wotsc_pubkey(&sk0);
    let pk1 = owner_wotsc_pubkey(&sk1);
    let pk2 = owner_wotsc_pubkey(&sk2);
    let eid = [0xE1u8; 32];
    let nonce: [u8; 16] = core::array::from_fn(|i| (i + 1) as u8);

    // Applet stores its injected (r1, r2) applet key and residual (r3, S0) into upper SRAM `0x10100..0x10120`.
    let applet_words_a: Vec<u32> = assemble(
        "MOVZ20 R10,0x10100
         ST64 [R10],R1
         ST64 [R10+8],R2
         ST64 [R10+16],R3
         SST64 [R10+24],S0
         HALT",
    )
    .unwrap()
    .chunks_exact(4)
    .map(|c| u32::from_le_bytes(c.try_into().unwrap()))
    .collect();

    let mut applet_words_b = applet_words_a.clone();
    applet_words_b.insert(0, qsag_ass2::isa::NOP_WORD);

    // Mode 1: `LcState::Provisioned { allow_signed_applets: true, rom_lock: false }`
    let mut vm = Ass2Vm::new_enclave(k_root, LcState::PROVISIONED_SIGNED_APPLETS);
    // Pre-contaminate Ring-0 registers & sponge with secret residue to prove hardware scrub!
    vm.regs.fill(0xDEAD_BEEF_CAFE_BABE);
    vm.reg_taint.fill(Taint::Secret);
    vm.spg.fill(0xBAD0_C0DE_1234_5678);
    vm.spg_taint.fill(Taint::Secret);

    let mut cur_pk = pk0;
    let mut record = (5u64 << 32) | 1;

    // Open `flags = 0` CMD_LOAD_CODE frame MUST be rejected in Provisioned mode!
    let open_frame = load_code_open_frame(0x80, &applet_words_a).unwrap();
    assert_eq!(
        vm.execute_cmd_load_code(&open_frame, &mut cur_pk, &eid, &nonce, &mut record),
        Err(EnclaveError::SignatureRequired)
    );
    assert_eq!(vm.load_open_applet(&applet_words_a), Err(EnclaveError::SignatureRequired));

    // Tampered WOTS+C signed applet frame MUST be rejected without advancing generation!
    let signed_a =
        load_code_wotsc_frame(0x80, &sk0, &eid, &nonce, record, &pk1, &applet_words_a).unwrap();
    let mut forged_a = signed_a.clone();
    forged_a[14] ^= 0x04; // mutate applet code word after signing `code_hash`
    assert!(
        vm.execute_cmd_load_code(&forged_a, &mut cur_pk, &eid, &nonce, &mut record)
            .is_err()
    );
    assert_eq!(cur_pk, pk0);
    assert_eq!(record, (5u64 << 32) | 1);

    // Authentic Owner `WOTS+C` signed applet succeeds, scrubs `r3..r15`/`spg`, and injects
    // `cSHAKE256(K_root, "ASS2.APPLET" || code_hash)` into `r1..r2`!
    let hash_a = vm
        .execute_cmd_load_code(&signed_a, &mut cur_pk, &eid, &nonce, &mut record)
        .unwrap();
    assert_eq!(hash_a, compute_code_hash(&applet_words_a));
    assert_eq!(cur_pk, pk1);
    assert_eq!(record, (6u64 << 32) | 1);
    assert!(vm.applet_exec);
    assert_eq!(&vm.regs[3..16], &[0u64; 13]);
    assert_eq!(&vm.reg_taint[3..16], &[Taint::Public; 13]);
    assert_eq!(vm.spg, [0u64; 25]);
    assert_eq!(vm.spg_taint, [Taint::Public; 25]);
    assert_eq!((vm.reg_taint[1], vm.reg_taint[2]), (Taint::Secret, Taint::Secret));

    let expected_key_a = derive_applet_key(&k_root, &hash_a);
    let exp_r1_a = u64::from_le_bytes(expected_key_a[0..8].try_into().unwrap());
    let exp_r2_a = u64::from_le_bytes(expected_key_a[8..16].try_into().unwrap());
    assert_eq!((vm.regs[1], vm.regs[2]), (exp_r1_a, exp_r2_a));

    assert_eq!(vm.run(16), RunExit::Halted);
    assert_eq!(vm.read_word(0x10100).unwrap(), exp_r1_a);
    assert_eq!(vm.read_word(0x10108).unwrap(), exp_r2_a);
    assert_eq!(vm.read_word(0x10110).unwrap(), 0);
    assert_eq!(vm.read_word(0x10118).unwrap(), 0);

    // Different applet `code_hash` derives an independent per-applet key in `r1..r2`!
    let signed_b =
        load_code_wotsc_frame(0x80, &sk1, &eid, &nonce, record, &pk2, &applet_words_b).unwrap();
    let hash_b = vm
        .execute_cmd_load_code(&signed_b, &mut cur_pk, &eid, &nonce, &mut record)
        .unwrap();
    assert_ne!(hash_a, hash_b);
    assert_ne!((vm.regs[1], vm.regs[2]), (exp_r1_a, exp_r2_a));

    // Mode 2: `LcState::Provisioned { rom_lock: true, .. }` rejects `CMD_LOAD_CODE` (`0x30`) unconditionally!
    for locked_state in [
        LcState::PROVISIONED_ROM_LOCKED,
        LcState::Provisioned {
            allow_signed_applets: true,
            rom_lock: true,
        },
    ] {
        let mut locked_vm = Ass2Vm::new_enclave(k_root, locked_state);
        let mut lpk = pk0;
        let mut lrec = (5u64 << 32) | 1;
        assert_eq!(
            locked_vm.execute_cmd_load_code(&open_frame, &mut lpk, &eid, &nonce, &mut lrec),
            Err(EnclaveError::RomLocked)
        );
        assert_eq!(
            locked_vm.execute_cmd_load_code(&signed_a, &mut lpk, &eid, &nonce, &mut lrec),
            Err(EnclaveError::RomLocked)
        );
        assert_eq!(
            locked_vm.load_open_applet(&applet_words_a),
            Err(EnclaveError::RomLocked)
        );
        assert!(!locked_vm.applet_exec);
    }
}
