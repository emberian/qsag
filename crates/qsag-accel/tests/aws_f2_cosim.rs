//! Run using QSAG_F2_SIM=/absolute/path/to/Vcl_qsag_f2_top and --ignored.
#![cfg(feature = "std")]
use qsag_accel::aws_f2::{AwsF2Backend, Bar0Pcis, NiCmd, SerialWidth, VerifyStatus};
use std::{
    fmt::Write as _,
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

struct Sim {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    stage: bool,
}
impl Sim {
    fn new(stage: bool) -> Self {
        let mut child = Command::new(std::env::var_os("QSAG_F2_SIM").expect("set QSAG_F2_SIM"))
            .arg("--sdk")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        Self {
            input: child.stdin.take().unwrap(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
            stage,
        }
    }
    fn request(&mut self, line: &str) -> String {
        writeln!(self.input, "{line}").unwrap();
        self.input.flush().unwrap();
        let mut response = String::new();
        assert_ne!(
            self.output.read_line(&mut response).unwrap(),
            0,
            "simulator closed"
        );
        response
    }
}
impl Drop for Sim {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
impl Bar0Pcis for Sim {
    type Error = ();
    fn stage_commands(&self) -> bool {
        self.stage
    }
    fn read32(&mut self, a: u32) -> Result<u32, ()> {
        u32::from_str_radix(self.request(&format!("r {a:x}")).trim(), 16).map_err(|_| ())
    }
    fn write32(&mut self, a: u32, v: u32) -> Result<(), ()> {
        (self.request(&format!("w {a:x} {v:x}")).trim() == "ok")
            .then_some(())
            .ok_or(())
    }
    fn read_pcis(&mut self, a: u64, b: &mut [u8]) -> Result<(), ()> {
        let data = self.request(&format!("R {a:x} {:x}", b.len() / 64));
        let mut words = data.split_whitespace();
        for d in b.chunks_exact_mut(4) {
            let w = u32::from_str_radix(words.next().ok_or(())?, 16).map_err(|_| ())?;
            d.copy_from_slice(&w.to_le_bytes());
        }
        words.next().is_none().then_some(()).ok_or(())
    }
    fn write_pcis(&mut self, a: u64, b: &[u8]) -> Result<(), ()> {
        let mut line = format!("W {a:x} {:x}", b.len() / 64);
        for w in b.chunks_exact(4) {
            write!(line, " {:x}", u32::from_le_bytes(w.try_into().unwrap())).unwrap();
        }
        (self.request(&line).trim() == "ok").then_some(()).ok_or(())
    }
}

#[test]
#[ignore = "requires the built Verilator system simulator"]
fn sdk_drives_ocl_and_pcis() {
    for stage in [false, true] {
        let mut hw = AwsF2Backend::attach(Sim::new(stage)).unwrap();
        let mut ni = hw.ni(u8::from(stage)).unwrap();
        let mut words = [1, 2, 3, 4, 5, 6, 7];
        ni.upload_words(511, &words).unwrap();
        let mut cmds: Vec<_> = words
            .iter()
            .enumerate()
            .map(|(i, &data)| NiCmd {
                op: 1,
                idx: i as u8,
                data,
                ..Default::default()
            })
            .collect();
        let check = NiCmd {
            op: 10,
            idx: 3,
            addr: 511,
            data: 0,
        };
        cmds.push(check);
        ni.stream(&cmds).unwrap();
        assert_eq!(
            ni.status().unwrap(),
            VerifyStatus {
                pass: true,
                checks: 1
            }
        );
        words[6] ^= 1 << 15;
        ni.upload_words(511, &words).unwrap();
        let mut readback = [0; 7];
        ni.read_words(511, &mut readback).unwrap();
        assert_eq!(readback, words);
        ni.stream(&[check]).unwrap();
        assert_eq!(
            ni.status().unwrap(),
            VerifyStatus {
                pass: false,
                checks: 2
            }
        );
        for vat in 0..3 {
            assert_eq!(hw.enclaves().diag(vat).unwrap() as u16, 0xa552);
            let id = hw
                .enclaves()
                .command(vat, SerialWidth::Octal, 1, 0, 0, &[])
                .unwrap();
            assert_eq!(&id[8..16], &0x4153533200000001u64.to_le_bytes());
        }
        hw.zeroize().unwrap();
        hw.ni(u8::from(stage))
            .unwrap()
            .read_words(511, &mut readback)
            .unwrap();
        assert_eq!(readback, [0; 7]);
    }
}
