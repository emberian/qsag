//! QSAG-Wire host driver for ASS2-0P5, SPI ×1. Each write and each reply has its own CS-low interval.
//! A board adapter owns RDY, IRQ, chip select, clocking and its I/O deadline.
//! Layouts follow the Rev. 1.0 host interface: CMD_LOAD_CODE carries `u32 word_count`, the instruction
//! words and a 16-byte tag; a CMD_EXEC reply is the 128 mailbox bytes, then A0, ECAUSE, INSTRET and CYCLES.

use std::io::{self, Read};

pub trait Bus {
    fn ready(&mut self) -> bool;
    fn irq(&mut self) -> bool;
    fn write(&mut self, bytes: &[u8]) -> io::Result<()>;
    /// Send prefix under CS, then clock bytes from DQ1. Dropping the reader releases CS.
    fn begin_read(&mut self, prefix: &[u8]) -> io::Result<impl Read + '_>;
}

pub const CMD_IDENT: u8 = 0x01;
pub const CMD_LOAD_CODE: u8 = 0x30;
pub const CMD_EXEC: u8 = 0x31;

pub const I_SRAM_WORDS: usize = 128; // 0x0000_1000..0x0000_11FF
pub const MBOX_BYTES: usize = 128; // RX_MBOX and TX_MBOX, each
const EXEC_REPLY_BYTES: usize = MBOX_BYTES + 4 * 8;
pub const FLAG_TAG: u8 = 1; // CMD_LOAD_CODE: the tag field holds an H_ZK_PIN tag
pub const E_BUDGET: u16 = 15; // CMD_EXEC stopped at its cycle budget
pub const E_TRAP: u16 = 16; // CMD_EXEC stopped on a trap; ECAUSE is in DIAG_RAW

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

/// Payload: `u32 word_count || u32 words[word_count] || 16-byte tag`, all little-endian.
/// The tag covers the count and the words. Frame padding follows the tag.
pub fn load_code<B: Bus>(bus: &mut B, code: &[u32], tag: [u8; 16]) -> Result<(), WireError> {
    if code.is_empty() || code.len() > I_SRAM_WORDS {
        return Err(WireError::Length);
    }
    let mut payload = (code.len() as u32).to_le_bytes().to_vec();
    payload.extend(code.iter().flat_map(|w| w.to_le_bytes()));
    payload.extend_from_slice(&tag);
    request(bus, CMD_LOAD_CODE, FLAG_TAG, 0, &payload).map(|_| ())
}

pub fn exec<B: Bus>(bus: &mut B, input: &[u8], budget: u16) -> Result<ExecResult, WireError> {
    if input.len() > MBOX_BYTES {
        return Err(WireError::Length);
    }
    let mut body = request(bus, CMD_EXEC, 0, budget, input)?;
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
        reply: vec![0x51, 0xb0, 1, 0, 0, 0, 0, 0],
    };
    let tag = [0xa5; 16]; // fixture bytes supplied by the test
    load_code(&mut bus, &[0x0005_0000], tag).unwrap(); // HALT, LE
    assert_eq!(
        &bus.sent[..17],
        &[0, 0x51, 0x30, 1, 24, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 5, 0]
    );
    assert_eq!(&bus.sent[17..], &tag); // 24 payload bytes: no frame padding

    bus.reply = vec![0x51, 0xb0, 1, 0, 0, 0, 0, 0];
    load_code(&mut bus, &[0x0006_0000, 0x0005_0000], tag).unwrap(); // NOP, HALT
    assert_eq!(
        &bus.sent[..13],
        &[0, 0x51, 0x30, 1, 28, 0, 0, 0, 0, 2, 0, 0, 0]
    );
    assert_eq!(&bus.sent[21..37], &tag);
    assert_eq!(&bus.sent[37..], &[0; 4]); // padding follows the tag
    assert!(matches!(
        load_code(&mut bus, &[0; I_SRAM_WORDS + 1], tag),
        Err(WireError::Length)
    ));

    bus.reply = vec![0x51, 0xb1, 1, 160, 0, 0, 0, 0, b'o', b'k'];
    bus.reply.resize(8 + MBOX_BYTES, 0);
    for value in [2u64, 0, 41, 190] {
        bus.reply.extend_from_slice(&value.to_le_bytes());
    }
    let result = exec(&mut bus, b"hello", 0x1234).unwrap();
    assert_eq!(&bus.sent[..9], &[0, 0x51, 0x31, 0, 5, 0, 0, 0x34, 0x12]);
    assert_eq!(result.tx_mbox.len(), MBOX_BYTES);
    assert_eq!(&result.tx_mbox[..2], b"ok");
    assert_eq!(
        (result.a0, result.ecause, result.instret, result.cycles),
        (2, 0, 41, 190)
    );

    bus.reply = vec![0x51, 0xb1, 0x80, 0, 0, 0, 4, 0];
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Chip(4))));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 15, 0]; // budget spent: counters, no payload
    bus.reply.extend_from_slice(&41u64.to_le_bytes());
    bus.reply.extend_from_slice(&190u64.to_le_bytes());
    assert!(matches!(
        exec(&mut bus, &[], 190),
        Err(WireError::Chip(E_BUDGET))
    ));
    bus.reply = vec![0x51, 0xb1, 0x80, 16, 0, 0, 16, 0];
    bus.reply.resize(24, 0);
    assert!(matches!(
        exec(&mut bus, &[], 9),
        Err(WireError::Chip(E_TRAP))
    ));
    assert!(matches!(
        exec(&mut bus, &[0; MBOX_BYTES + 1], 9),
        Err(WireError::Length)
    ));
    bus.reply = vec![0x51, 0xb1, 1, 0, 0, 0, 0, 0];
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Length)));
    bus.reply = vec![0x51, 0xb1, 1, 16, 0, 0, 0, 0]; // advertised body absent
    assert!(matches!(exec(&mut bus, &[], 0), Err(WireError::Io(_))));
    println!("host_driver: framing checks passed");
}
