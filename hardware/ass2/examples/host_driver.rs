//! QSAG-Wire host driver for ASS2-0P5, SPI ×1. Each write and each reply has its own CS-low interval.
//! A board adapter owns RDY, IRQ, chip select, clocking and its I/O deadline.
//! Layouts follow the Rev. 2.3 Two-Ring Hardware W^X host interface: Ring 0 executes from immutable
//! 4 KiB mask I-ROM while `CMD_LOAD_CODE` (`0x30`) loads <= 64-word Ring-3 applets into `0x10000..0x100FF`
//! (open in `BLANK`, Owner `WOTS+C` signed in `!rom_lock`, hard-rejected with `E_LOCKED = 14` under `rom_lock`).

use std::io::{self, Read};

pub trait Bus {
    fn ready(&mut self) -> bool;
    fn irq(&mut self) -> bool;
    fn write(&mut self, bytes: &[u8]) -> io::Result<()>;
    /// Send prefix under CS, then clock bytes from DQ1. Dropping the reader releases CS.
    fn begin_read(&mut self, prefix: &[u8]) -> io::Result<impl Read + '_>;
}

pub const CMD_IDENT: u8 = 0x01;
pub const CMD_LOAD_CODE: u8 = 0x30; // Two-Ring W^X <= 64-word Ring-3 applet loader
pub const CMD_EXEC: u8 = 0x31;

pub const MBOX_BYTES: usize = 128; // RX_MBOX and TX_MBOX, each
const EXEC_REPLY_BYTES: usize = MBOX_BYTES + 4 * 8;
pub const SERVICE_CANOPY: u8 = 0x01;
pub const SERVICE_HORNER: u8 = 0x02;
pub const SERVICE_JIVE: u8 = 0x03;
pub const SERVICE_CTH: u8 = 0x04;
pub const SERVICE_IDENT: u8 = 0x07;
pub const E_LOCKED: u16 = 14; // SafeRecovery or provisioned rom_lock blocks 0x30 / applet 0x31
pub const E_CAP: u16 = 13; // missing/invalid WOTS+C / capability or unleased session
pub const E_BUDGET: u16 = 15; // CMD_EXEC stopped at its cycle budget
pub const E_TRAP: u16 = 16; // CMD_EXEC stopped on a trap; ECAUSE & EPC in 16-byte error body

#[derive(Debug)]
pub enum WireError {
    Io(io::Error),
    Timeout,
    Length,
    BadMagic,
    BadOpcode,
    Status,
    Chip(u16),
}

impl From<io::Error> for WireError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

#[derive(Debug)]
pub struct ExecResult {
    pub tx_mbox: Vec<u8>,
    pub a0: u64,
    pub ecause: u64,
    pub instret: u64,
    pub cycles: u64,
}

pub fn request<B: Bus>(
    bus: &mut B,
    op: u8,
    flags: u8,
    arg: u16,
    payload: &[u8],
) -> Result<Vec<u8>, WireError> {
    if payload.len() >= 1 << 24 {
        return Err(WireError::Length);
    }
    let w0 = 0x51
        | (op as u64) << 8
        | (flags as u64) << 16
        | (payload.len() as u64) << 24
        | (arg as u64) << 48;
    let mut tx = vec![0x00]; // single-bit write
    tx.extend_from_slice(&w0.to_le_bytes());
    tx.extend_from_slice(payload);
    tx.resize(9 + payload.len().next_multiple_of(8), 0);
    if !(0..1_000_000).any(|_| bus.ready()) {
        return Err(WireError::Timeout);
    }
    bus.write(&tx)?;
    if !(0..1_000_000).any(|_| bus.irq()) {
        return Err(WireError::Timeout);
    }

    let mut rx = bus.begin_read(&[0x02, 0x00])?; // read prefix and eight dummy clocks
    let mut hdr = [0; 8];
    rx.read_exact(&mut hdr)?;
    if hdr[0] != 0x51 {
        return Err(WireError::BadMagic);
    }
    if hdr[1] != (op | 0x80) {
        return Err(WireError::BadOpcode);
    }
    let len = u32::from_le_bytes([hdr[3], hdr[4], hdr[5], 0]) as usize;
    if op == CMD_EXEC && len > EXEC_REPLY_BYTES {
        return Err(WireError::Length);
    }
    let mut body = vec![0; len.next_multiple_of(8)];
    rx.read_exact(&mut body)?;
    if hdr[2] & 0x80 != 0 {
        return Err(WireError::Chip(u16::from_le_bytes([hdr[6], hdr[7]])));
    }
    if hdr[2] & 1 == 0 {
        return Err(WireError::Status);
    }
    body.truncate(len);
    Ok(body)
}

pub fn ident<B: Bus>(bus: &mut B) -> Result<[u64; 4], WireError> {
    let body = request(bus, CMD_IDENT, 0, 0, &[])?;
    if body.len() != 32 {
        return Err(WireError::Length);
    }
    Ok(std::array::from_fn(|i| {
        u64::from_le_bytes(body[8 * i..8 * (i + 1)].try_into().unwrap())
    }))
}

pub fn exec<B: Bus>(
    bus: &mut B,
    service: u8,
    input: &[u8],
    budget: u16,
) -> Result<ExecResult, WireError> {
    if input.len() > MBOX_BYTES {
        return Err(WireError::Length);
    }
    let mut body = request(bus, CMD_EXEC, service, budget, input)?;
    if body.len() != EXEC_REPLY_BYTES {
        return Err(WireError::Length);
    }
    let word = |offset: usize| {
        let start = MBOX_BYTES + 8 * offset;
        u64::from_le_bytes(body[start..start + 8].try_into().unwrap())
    };
    let (a0, ecause, instret, cycles) = (word(0), word(1), word(2), word(3));
    body.truncate(MBOX_BYTES);
    Ok(ExecResult {
        tx_mbox: body,
        a0,
        ecause,
        instret,
        cycles,
    })
}

pub fn load_open_applet<B: Bus>(bus: &mut B, words: &[u32]) -> Result<ExecResult, WireError> {
    if words.is_empty() || words.len() > 64 {
        return Err(WireError::Length);
    }
    let mut payload = Vec::with_capacity(4 + 4 * words.len());
    payload.extend_from_slice(&(words.len() as u32).to_le_bytes());
    for &w in words {
        payload.extend_from_slice(&w.to_le_bytes());
    }
    let mut body = request(bus, CMD_LOAD_CODE, 0, 0, &payload)?;
    if body.len() != EXEC_REPLY_BYTES {
        return Err(WireError::Length);
    }
    let word = |offset: usize| {
        let start = MBOX_BYTES + 8 * offset;
        u64::from_le_bytes(body[start..start + 8].try_into().unwrap())
    };
    let (a0, ecause, instret, cycles) = (word(0), word(1), word(2), word(3));
    body.truncate(MBOX_BYTES);
    Ok(ExecResult {
        tx_mbox: body,
        a0,
        ecause,
        instret,
        cycles,
    })
}

// Transport fixture: records the request and supplies response bytes on one CS assertion.
struct MockBus {
    sent: Vec<u8>,
    reply: Vec<u8>,
}
impl Bus for MockBus {
    fn ready(&mut self) -> bool {
        true
    }
    fn irq(&mut self) -> bool {
        !self.reply.is_empty()
    }
    fn write(&mut self, tx: &[u8]) -> io::Result<()> {
        self.sent = tx.to_vec();
        Ok(())
    }
    fn begin_read(&mut self, prefix: &[u8]) -> io::Result<impl Read + '_> {
        assert_eq!(prefix, [2, 0]);
        Ok(io::Cursor::new(std::mem::take(&mut self.reply)))
    }
}

fn main() {
    let mut bus = MockBus {
        sent: vec![],
        reply: vec![0x51, 0x81, 1, 32, 0, 0, 0, 0],
    };
    for w in [0x3038_3144_3253_5341u64, 0x4153_5332_0000_0001, 0, 0] {
        bus.reply.extend_from_slice(&w.to_le_bytes());
    }
    let id = ident(&mut bus).unwrap();
    assert_eq!(&bus.sent, &[0, 0x51, 0x01, 0, 0, 0, 0, 0, 0]);
    assert_eq!(id[1], 0x4153_5332_0000_0001);

    // Provisioned rom_lock / SafeRecovery blocks CMD_LOAD_CODE (0x30) with E_LOCKED = 14.
    bus.reply = vec![0x51, 0xb0, 0x80, 0, 0, 0, 14, 0];
    assert!(matches!(
        load_open_applet(&mut bus, &[0x0005_0000]),
        Err(WireError::Chip(E_LOCKED))
    ));
    assert!(matches!(load_open_applet(&mut bus, &[0; 65]), Err(WireError::Length)));

    bus.reply = vec![0x51, 0xb1, 1, 160, 0, 0, 0, 0, b'o', b'k'];
    bus.reply.resize(8 + MBOX_BYTES, 0);
    for value in [2u64, 0, 41, 190] {
        bus.reply.extend_from_slice(&value.to_le_bytes());
    }
    let result = exec(&mut bus, SERVICE_CANOPY, b"hello", 0x1234).unwrap();
    assert_eq!(&bus.sent[..9], &[0, 0x51, 0x31, 1, 5, 0, 0, 0x34, 0x12]);
    assert_eq!(result.tx_mbox.len(), MBOX_BYTES);
    assert_eq!(&result.tx_mbox[..2], b"ok");
    assert_eq!(
        (result.a0, result.ecause, result.instret, result.cycles),
        (2, 0, 41, 190)
    );

    bus.reply = vec![0x51, 0xb1, 0x80, 0, 0, 0, 13, 0];
    assert!(matches!(
        exec(&mut bus, SERVICE_JIVE, &[], 0),
        Err(WireError::Chip(E_CAP))
    ));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 15, 0]; // budget spent: diagnostic words, no mailbox
    bus.reply.extend_from_slice(&0u64.to_le_bytes());
    bus.reply.extend_from_slice(&0x0200u64.to_le_bytes());
    assert!(matches!(
        exec(&mut bus, SERVICE_JIVE, &[], 190),
        Err(WireError::Chip(E_BUDGET))
    ));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 16, 0];
    bus.reply.resize(24, 0);
    assert!(matches!(
        exec(&mut bus, SERVICE_JIVE, &[], 9),
        Err(WireError::Chip(E_TRAP))
    ));
    assert!(matches!(
        exec(&mut bus, SERVICE_IDENT, &[0; MBOX_BYTES + 1], 9),
        Err(WireError::Length)
    ));
    bus.reply = vec![0x51, 0xb1, 1, 0, 0, 0, 0, 0];
    assert!(matches!(
        exec(&mut bus, SERVICE_IDENT, &[], 0),
        Err(WireError::Length)
    ));
    bus.reply = vec![0x51, 0xb1, 1, 16, 0, 0, 0, 0]; // advertised body absent
    assert!(matches!(
        exec(&mut bus, SERVICE_IDENT, &[], 0),
        Err(WireError::Io(_))
    ));
    println!("host_driver: framing checks passed");
}
