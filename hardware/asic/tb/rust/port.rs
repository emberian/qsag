// Installed into an isolated qsag-agg build by prepare.py. Commands use word addresses.
use crate::field::Goldilocks;
use crate::zk_hem::v2::field5::Fp5;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::sync::{Mutex, OnceLock};
use std::{fs::File, string::String, vec::Vec};

pub struct Port {
    counts: [u64; 256],
    tx: BufWriter<File>,
    rx: Option<BufReader<File>>,
}

pub fn words(bytes: &[u8]) -> Vec<u64> {
    bytes
        .chunks(8)
        .map(|b| {
            let mut lane = [0; 8];
            lane[..b.len()].copy_from_slice(b);
            u64::from_le_bytes(lane)
        })
        .collect()
}
impl Port {
    pub fn open(commands: &str, responses: Option<&str>) -> Self {
        let tx = BufWriter::new(File::create(commands).unwrap());
        let rx = responses.map(|path| BufReader::new(File::open(path).unwrap()));
        Self {
            tx,
            rx,
            counts: [0; 256],
        }
    }
    fn send(&mut self, op: u8, idx: usize, addr: usize, data: u64, mode: u8, expected: u64) {
        self.counts[op as usize] += 1;
        writeln!(
            self.tx,
            "{op:02x} {idx:02x} {addr:04x} {data:016x} {mode} {expected:016x}"
        )
        .unwrap();
    }
    pub fn cmd(&mut self, op: u8, idx: usize, addr: usize, data: u64) {
        self.send(op, idx, addr, data, 0, 0);
    }
    pub fn expect(&mut self, op: u8, idx: usize, addr: usize, data: u64, expected: u64) {
        self.send(op, idx, addr, data, 1, expected);
    }
    fn read(&mut self, op: u8, idx: usize, addr: usize) -> u64 {
        self.send(op, idx, addr, 0, 2, 0);
        self.tx.flush().unwrap();
        let mut line = String::new();
        self.rx.as_mut().unwrap().read_line(&mut line).unwrap();
        u64::from_str_radix(line.trim(), 16).expect("hardware reply")
    }
    pub fn write(&mut self, op: u8, idx: usize, addr: usize, lanes: &[u64]) {
        for (i, &v) in lanes.iter().enumerate() {
            if op == 3 {
                self.cmd(op, 0, addr + i, v)
            } else {
                self.cmd(op, idx + i, 0, v)
            }
        }
    }
    pub fn state(&mut self, idx: usize, x: Fp5) {
        self.write(1, idx, 0, &words(&x.to_le_bytes()));
    }
    pub fn mem(&mut self, addr: usize, x: Fp5) {
        self.write(3, 0, addr, &words(&x.to_le_bytes()));
    }
    pub fn polynomial(&mut self, addr: usize, coeffs: &[Fp5]) {
        for (i, &c) in coeffs.iter().enumerate() {
            self.mem(addr + i * 5, c);
        }
    }
    fn result(&mut self) -> Fp5 {
        Fp5(std::array::from_fn(|i| {
            Goldilocks::from_canonical(self.read(2, i, 0)).unwrap()
        }))
    }
    pub fn absorb(&mut self, domain: usize, msg: &[u8], nonce: Option<&[u8]>) {
        self.cmd(0x3a, domain, 0, 0);
        let mut input = msg.to_vec();
        if let Some(nonce) = nonce {
            input[6..38].fill(0);
            self.write(0x0c, 0, 0, &words(nonce));
            self.cmd(0x0d, 0, 0, 0);
        }
        input.push(7);
        input.resize(input.len().div_ceil(136) * 136, 0);
        *input.last_mut().unwrap() ^= 0x80;
        for block in input.chunks_exact(136) {
            self.write(3, 0, 0, &words(block));
            self.cmd(0x37, 2, 0, 17);
        }
    }
    pub fn hash(&mut self, domain: usize, msg: &[u8], out: &mut [u8]) {
        let nonce = if domain == 6 && msg.first() == Some(&0x10) {
            Some(&msg[6..38])
        } else {
            None
        };
        self.absorb(domain, msg, nonce);
        for (i, block) in out.chunks_mut(136).enumerate() {
            if i > 0 {
                self.cmd(0x33, 0, 0, 0);
            }
            let n = block.len().div_ceil(8);
            self.cmd(0x39, 0, 32, n as u64);
            for (lane, dst) in block.chunks_mut(8).enumerate() {
                dst.copy_from_slice(&self.read(4, 0, 32 + lane).to_le_bytes()[..dst.len()]);
            }
        }
    }
    pub fn path(
        &mut self,
        stage: u8,
        depth: usize,
        index: usize,
        leaf: &[u8; 50],
        siblings: &[[u8; 50]],
        root: &[u8; 50],
    ) -> bool {
        self.write(0x31, 0, 0, &words(leaf));
        for (i, s) in siblings.iter().enumerate() {
            self.write(3, 0, 64 + 7 * i, &words(s));
        }
        self.write(3, 0, 512, &words(root));
        self.cmd(0x16, depth, 64, ((stage as u64) << 32) | index as u64);
        self.read(0x0a, 2, 512) == 1
    }
    pub fn round(&mut self, c: &[Fp5], r: Fp5, claim: Fp5) -> Option<Fp5> {
        self.state(0, claim);
        self.state(5, r);
        self.polynomial(0, c);
        self.cmd(0x2b, 0, 0, (c.len() - 1) as u64);
        if self.status() >> 32 != 1 {
            return None;
        }
        Some(self.result())
    }
    pub fn horner(&mut self, c: &[Fp5], r: Fp5) -> Fp5 {
        self.state(0, Fp5::ZERO);
        self.state(5, r);
        for (i, &v) in c.iter().rev().enumerate() {
            self.mem(5 * i, v);
        }
        self.cmd(0x29, 0, 0, c.len() as u64);
        self.result()
    }
    pub fn muladd(&mut self, a: Fp5, b: Fp5, c: Fp5) -> Fp5 {
        self.state(0, a);
        self.state(5, b);
        self.mem(0, c);
        self.cmd(0x28, 0, 0, 0);
        self.result()
    }
    // Four parallel base add/sub or scalar products, then the fifth limb.
    pub fn linear(&mut self, op: u8, a: Fp5, b: Fp5) -> Fp5 {
        let av = words(&a.to_le_bytes());
        let bv = words(&b.to_le_bytes());
        self.write(1, 0, 0, &av[..4]);
        if op == 0x27 {
            self.cmd(1, 4, 0, bv[0]);
        } else {
            self.write(1, 8, 0, &bv[..4]);
        }
        self.cmd(op, 0, 0, 0);
        let mut out = [Goldilocks::ZERO; 5];
        for (i, slot) in out[..4].iter_mut().enumerate() {
            *slot = Goldilocks::from_canonical(self.read(2, i, 0)).unwrap();
        }
        self.cmd(1, 0, 0, av[4]);
        if op != 0x27 {
            self.cmd(1, 8, 0, bv[4]);
        }
        self.cmd(op, 0, 0, 0);
        out[4] = Goldilocks::from_canonical(self.read(2, 0, 0)).unwrap();
        Fp5(out)
    }
    pub fn fold_affine(&mut self, origin: Fp5, slope: Fp5, point: Fp5) -> Fp5 {
        // Convert monomial coefficients to values at 0 and 1 on the field engine.
        let at_one = self.linear(0x21, origin, slope);
        self.mem(0, origin);
        self.mem(5, at_one);
        self.state(5, point);
        self.cmd(0x2a, 0, 0, 1);
        self.result()
    }
    pub fn coverage(&self) {
        for op in [0x0a, 0x0c, 0x16, 0x28, 0x29, 0x2a, 0x2b, 0x39, 0x3a] {
            assert!(self.counts[op] > 0);
            std::println!("opcode {op:02x} count {}", self.counts[op]);
        }
    }
    pub fn eq(&mut self, a: Fp5, b: Fp5) -> bool {
        self.state(0, a);
        self.mem(0, b);
        self.read(0x0a, 4, 0) == 1
    }
    pub fn status(&mut self) -> u64 {
        self.read(0x0b, 0, 0)
    }
    pub fn finish(&mut self) {
        self.cmd(0xff, 0, 0, 0);
        self.tx.flush().unwrap();
    }
}
static HW: OnceLock<Mutex<Port>> = OnceLock::new();
pub fn connect(tx: &str, rx: &str) {
    HW.set(Mutex::new(Port::open(tx, Some(rx))))
        .ok()
        .expect("single live connection");
}
pub fn with<T>(f: impl FnOnce(&mut Port) -> T) -> Option<T> {
    HW.get().map(|p| f(&mut p.lock().unwrap()))
}
impl Port {
    pub fn inverse(&mut self, x: Fp5) -> Fp5 {
        // Fermat x^(p^5-2), including the Rust convention inverse(0)=0.
        const EXP: [u64; 5] = [
            0xfffffffaffffffff,
            0xffffffe20000000e,
            0xffffffcd0000002c,
            0xffffffe20000002c,
            0xfffffffb0000000e,
        ];
        let mut y = Fp5::ONE;
        for limb in EXP.into_iter().rev() {
            for bit in (0..64).rev() {
                y = self.muladd(y, y, Fp5::ZERO);
                if (limb >> bit) & 1 == 1 {
                    y = self.muladd(y, x, Fp5::ZERO);
                }
            }
        }
        y
    }
}
