//! Run using QSAG_F2_SIM=/absolute/path/to/Vcl_qsag_f2_top and --ignored.
#![cfg(feature = "alloc")]
use qsag_accel::aws_f2::{AwsF2Backend, Bar0Pcis, NiCmd, SerialWidth, VerifyStatus};
use std::{
    fmt::Write as _,
    io::{BufRead, BufReader, Write},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::{Arc, Mutex},
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
        for d in b.as_chunks_mut::<4>().0 {
            let w = u32::from_str_radix(words.next().ok_or(())?, 16).map_err(|_| ())?;
            *d = w.to_le_bytes();
        }
        words.next().is_none().then_some(()).ok_or(())
    }
    fn write_pcis(&mut self, a: u64, b: &[u8]) -> Result<(), ()> {
        let mut line = format!("W {a:x} {:x}", b.len() / 64);
        for w in b.as_chunks::<4>().0 {
            write!(line, " {:x}", u32::from_le_bytes(*w)).unwrap();
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

fn le_words(bytes: &[u8]) -> Vec<u64> {
    bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|b| u64::from_le_bytes(*b))
        .collect()
}
fn encode(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}
// Three SDK clients address different vats through one serialized PCI link.
// Only the coordinator issues global commands.
#[derive(Clone)]
struct SharedBus(Arc<Mutex<Sim>>);
impl Bar0Pcis for SharedBus {
    type Error = ();
    fn read32(&mut self, addr: u32) -> Result<u32, ()> {
        let result = self.0.lock().unwrap().read32(addr);
        std::thread::yield_now();
        result
    }
    fn write32(&mut self, addr: u32, value: u32) -> Result<(), ()> {
        self.0.lock().unwrap().write32(addr, value)
    }
    fn read_pcis(&mut self, addr: u64, data: &mut [u8]) -> Result<(), ()> {
        self.0.lock().unwrap().read_pcis(addr, data)
    }
    fn write_pcis(&mut self, addr: u64, data: &[u8]) -> Result<(), ()> {
        self.0.lock().unwrap().write_pcis(addr, data)
    }
}
fn resident(hw: &mut AwsF2Backend<SharedBus>, vat: u8, op: u8, words: &[u64]) -> Vec<u64> {
    le_words(
        &hw.enclaves()
            .command(vat, SerialWidth::Octal, op, 0, 0, &encode(words))
            .unwrap(),
    )
}

// Invoke the same standalone owner used by the C++ bus test. This mode takes
// only the public transcript and never constructs a simulated device.
fn owner_frame(epoch: u64, vat: u8, op: u8, id: &[u64; 4], nonce: &[u64], record: u64) -> Vec<u8> {
    let args = [
        epoch,
        u64::from(vat),
        u64::from(op),
        id[0],
        id[1],
        id[2],
        id[3],
        nonce[0],
        nonce[1],
        record,
    ];
    let output = Command::new(std::env::var_os("QSAG_F2_SIM").unwrap())
        .arg("--owner")
        .args(args.map(|w| format!("{w:x}")))
        .output()
        .unwrap();
    assert!(output.status.success(), "owner failed: {:?}", output.stderr);
    std::str::from_utf8(&output.stdout)
        .unwrap()
        .split_whitespace()
        .flat_map(|word| u64::from_str_radix(word, 16).unwrap().to_le_bytes())
        .collect()
}

fn verify_chain(words: &[u64]) {
    use qsag_accel::{goldilocks::GOLDILOCKS_PRIME, poseidon2::poseidon2_perm12};
    let mut input = [0; 12];
    input[..4].copy_from_slice(&words[4..8]);
    input[4..].copy_from_slice(&[9, 10, 11, 12, 0x5153414757535450, 0x100000000012, 45, 0]);
    let mut output = input;
    poseidon2_perm12(&mut output);
    for i in 0..4 {
        let expected = u128::from(output[i])
            + u128::from(input[i])
            + 2 * u128::from(input[4 + i])
            + 4 * u128::from(input[8 + i]);
        assert_eq!(
            words[8 + i],
            (expected % u128::from(GOLDILOCKS_PRIME)) as u64
        );
    }
}

fn prepare_vat(bus: SharedBus, epoch: u64, vat: u8, pk0: &[u8]) -> ([u64; 4], [u8; 120]) {
    let mut hw = AwsF2Backend::attach(bus).unwrap();
    let width = SerialWidth::Octal;
    resident(&mut hw, vat, 0x10, &[]);
    assert_eq!(hw.enclaves().diag(vat).unwrap() >> 24 & 7, 1);
    let enrol = hw.enclaves().command(vat, width, 0x11, 0, 0, pk0).unwrap();
    assert_eq!(enrol.len(), 160);
    let enrol = le_words(&enrol);
    let id: [u64; 4] = enrol[2..6].try_into().unwrap();
    assert_ne!(id, [0; 4]);
    let proof = |op, reply: &[u64], record| owner_frame(epoch, vat, op, &id, reply, record);
    hw.enclaves()
        .command(vat, width, 0x12, 0, 0, &proof(0x12, &enrol, 0))
        .unwrap();
    hw.enclaves().reset(vat).unwrap();
    let boot = resident(&mut hw, vat, 0x10, &[]);
    assert_eq!(boot[2], 1 << 32);
    assert_eq!(&boot[4..8], &id);
    let lease = hw
        .enclaves()
        .command(vat, width, 0x15, 0, 0, &proof(0x15, &boot, boot[2]))
        .unwrap();
    let lease = le_words(&lease);
    assert_eq!(lease[2], 2 << 32);
    let image = encode(&[
        1 | (0x50000u64 << 32),
        0x1122334455667788,
        0x99aabbccddeeff00,
    ]);
    hw.enclaves()
        .command(vat, width, 0x30, 1, 0, &image)
        .unwrap();
    let gate = hw
        .enclaves()
        .command(vat, width, 0x16, 0, 0, &proof(0x16, &lease, lease[2]))
        .unwrap();
    let gate = le_words(&gate);
    assert_eq!(gate[2], (3 << 32) | (7 + u64::from(vat)));
    hw.enclaves()
        .command(vat, width, 0x30, 2, 0, &proof(0x30, &gate, gate[2]))
        .unwrap();
    (id, proof(0x20, &[0; 2], 0).try_into().unwrap())
}

#[test]
#[ignore = "requires the built Verilator custody simulator"]
fn three_party_custody_across_seed_and_flr() {
    let bus = SharedBus(Arc::new(Mutex::new(Sim::new(false))));
    let mut hw = AwsF2Backend::attach(bus.clone()).unwrap();
    assert!(!hw.diagnostics_only().unwrap());
    let mut previous_ids = [[0u64; 4]; 3];
    let mut previous_chains = [[0u64; 8]; 3];
    let pk0 = owner_frame(0, 0, 0x11, &[0; 4], &[0; 2], 0);
    for epoch in 0..2 {
        if epoch == 1 {
            hw.zeroize().unwrap();
            hw.inject_nitro_seed(&core::array::from_fn(|i| i as u8))
                .unwrap();
        }
        let status = hw.anchor_status().unwrap();
        assert!(status.ok && status.sysmon_ready && !status.rct_fail && !status.apt_fail);
        assert_eq!(status.nitro_seeded, epoch == 1);
        assert_eq!(status.epoch_cnt, epoch as u16);

        let mut requests = [[0; 120]; 3];
        let results = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..3)
                .map(|vat| {
                    let bus = bus.clone();
                    let pk0 = &pk0;
                    scope.spawn(move || prepare_vat(bus, epoch, vat, pk0))
                })
                .collect();
            workers
                .into_iter()
                .map(|w| w.join().unwrap())
                .collect::<Vec<_>>()
        });
        for (i, (id, request)) in results.into_iter().enumerate() {
            assert!(!previous_ids[..i].contains(&id));
            if epoch == 1 {
                assert_ne!(previous_ids[i], id);
            }
            previous_ids[i] = id;
            requests[i] = request;
        }
        for (i, result) in hw
            .enclaves()
            .cth_sign_three(&requests)
            .into_iter()
            .enumerate()
        {
            let sig = result.unwrap();
            assert_eq!(sig.len(), 160);
            let words = le_words(&sig);
            assert_eq!(words[2], (5 << 32) | (7 + i as u64));
            verify_chain(&words);
            if epoch == 1 {
                assert_ne!(&previous_chains[i][..4], &words[4..8]);
                assert_ne!(&previous_chains[i][4..], &words[8..12]);
            }
            previous_chains[i].copy_from_slice(&words[4..12]);
        }
    }
    assert_eq!(bus.0.lock().unwrap().request("f 0").trim(), "ok");
    let mut hw = AwsF2Backend::attach(bus).unwrap();
    let status = hw.anchor_status().unwrap();
    assert!(status.ok && status.sysmon_ready && !status.nitro_seeded);
    assert_eq!(status.epoch_cnt, 0);
    for vat in 0..3 {
        resident(&mut hw, vat, 0x10, &[]);
        assert_eq!(hw.enclaves().diag(vat).unwrap() >> 24 & 7, 1);
    }
}

#[test]
#[ignore = "requires the built Verilator simulator and ASIC live proof fixtures"]
fn autonomous_proof_verify_over_pcis_and_doorbell() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../hardware/asic/vec");
    let proof =
        std::fs::read(root.join("proof_v2.bin")).expect("missing hardware/asic/vec/proof_v2.bin");
    let desc = std::fs::read(root.join("statement_v2.bin"))
        .expect("missing hardware/asic/vec/statement_v2.bin");
    assert_eq!(proof.len(), 258_104);

    // Stage=true exercises the production AWS F2 BAR4 PCIS DMA + 1 BAR0 ring doorbell path.
    let mut hw = AwsF2Backend::attach(Sim::new(true)).unwrap();
    let status = hw
        .ni(0)
        .unwrap()
        .verify_proof_auto(&desc, &proof, 0)
        .unwrap();
    assert_eq!(
        status,
        VerifyStatus {
            pass: true,
            checks: 107
        }
    );

    // Paged window mode (0x50 + 0x51 refills) on NI engine 1.
    let paged = hw
        .ni(1)
        .unwrap()
        .verify_proof_auto(&desc, &proof, 4096)
        .unwrap();
    assert_eq!(
        paged,
        VerifyStatus {
            pass: true,
            checks: 107
        }
    );

    // Single-bit proof tamper must be rejected autonomously in hardware (both resident & paged).
    let mut tampered = proof.clone();
    tampered[258_000] ^= 1;
    let rejected = hw
        .ni(0)
        .unwrap()
        .verify_proof_auto(&desc, &tampered, 0)
        .unwrap();
    assert!(!rejected.pass);
    let rejected_paged = hw
        .ni(1)
        .unwrap()
        .verify_proof_auto(&desc, &tampered, 4096)
        .unwrap();
    assert!(!rejected_paged.pass);
}
