// Independent replay of the Python corpus against the Rust instruction decoder and VM.
use qsag_ass2::{Ass2Vm, StepOutcome};
use std::{env, fs::File, io::{BufRead, BufReader}};

fn number(s: &str) -> u64 { u64::from_str_radix(s, 16).unwrap() }
fn bytes(s: &str) -> Vec<u8> {
    s.as_bytes().chunks_exact(2).map(|p| number(std::str::from_utf8(p).unwrap()) as u8).collect()
}

fn main() {
    let input = File::open(env::args().nth(1).expect("vector file")).unwrap();
    let mut lines = BufReader::new(input).lines().map(Result::unwrap);
    let header = lines.next().unwrap();
    let count: usize = header.strip_prefix("ASS2-V1 ").unwrap().parse().unwrap();
    let mut vm = None;
    let mut shadow = Vec::new();
    let mut name = String::new();
    let (mut cases, mut steps) = (0, 0);
    for line in lines {
        let mut row = line.split_whitespace();
        match row.next().unwrap() {
            "#" => continue,
            "CASE" => {
                assert!(vm.is_none());
                name = row.next().unwrap().to_string();
                let size = number(row.next().unwrap()) as usize;
                vm = Some(Ass2Vm::new(size));
                shadow = vec![0; size];
            }
            "LOAD" => {
                let addr = number(row.next().unwrap()) as usize;
                let data = bytes(row.next().unwrap());
                vm.as_mut().unwrap().load_image(addr as u64, &data).unwrap();
                shadow[addr..addr + data.len()].copy_from_slice(&data);
            }
            "STEP" => {
                let s = vm.as_mut().unwrap();
                let mut n = || number(row.next().unwrap());
                let (pc, word, trap) = (n(), n(), n());
                assert_eq!(s.pc, pc, "{name} pre-PC");
                let status = s.step();
                let actual_trap = match status {
                    StepOutcome::Trap(cause) => cause as u64,
                    StepOutcome::Halted | StepOutcome::Retired => 0,
                    other => panic!("{name} {pc:#x} {other:?}"),
                };
                assert_eq!(actual_trap, trap, "{name} PC={pc:#x}");
                let obs = s.trace.observations.last().unwrap();
                assert_eq!(u64::from(obs.insn_word.unwrap_or(0)), word, "{name} PC={pc:#x}");
                for (field, actual) in [("PC", s.pc), ("halted", s.halted as u64),
                    ("ECAUSE", s.csrs.ecause), ("INSTRET", s.csrs.instret), ("CYCLES", s.csrs.cycles)] {
                    assert_eq!(actual, n(), "{name} PC={pc:#x} {field}");
                }
                for (i, actual) in s.regs.iter().chain(&s.spg).enumerate() {
                    assert_eq!(*actual, n(), "{name} PC={pc:#x} bank word {i}");
                }
                for _ in 0..n() {
                    let addr = n() as usize;
                    shadow[addr] = n() as u8;
                }
                assert!(s.mem == shadow, "{name} PC={pc:#x} SRAM");
                steps += 1;
            }
            "END" => {
                let s = vm.take().unwrap();
                assert!(s.halted && s.mem == bytes(row.next().unwrap()), "{name} final state");
                cases += 1;
            }
            tag => panic!("unknown vector record {tag}"),
        }
        assert!(row.next().is_none());
    }
    assert!(vm.is_none() && cases == count && count > 0);
    println!("{cases} programs, {steps} Rust VM architectural steps passed");
}
