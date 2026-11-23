//! QSAG F2 shell ABI v2. A mutable backend owns the command staging registers
//! and ring doorbell. Give a single process exclusive use of the AppPF.
use alloc::vec::Vec;

const MAGIC: u32 = 0x5153_4147;
const ABI: u32 = 0x0002_0000;
const STAGING: u64 = 0x80000;
const STREAM: u64 = 0xc0000;
const PAGE: usize = 4096;
const SRAM_WORDS: usize = 65536;
const POLLS: usize = 5_000_000;
/// Autonomous on-chip `QSAG-NI v2` proof verification (`QSAGZKH2` / `QSAGHQM2`).
pub const OP_VERIFY_PROOF_AUTO: u8 = 0x50;
/// Resume autonomous verification after refilling a paged SRAM proof window.
pub const OP_PAGE_CONTINUE: u8 = 0x51;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NiCmd {
    pub op: u8,
    pub idx: u8,
    pub addr: u16,
    pub data: u64,
}

const STATUS: NiCmd = NiCmd {
    op: 11,
    idx: 0,
    addr: 0,
    data: 0,
};

/// Four little-endian lanes, in issue order. The wire index is five bits.
pub fn pack_pcis_cmd_beat(commands: [NiCmd; 4]) -> [u8; 64] {
    let mut beat = [0; 64];
    for (lane, cmd) in beat.as_chunks_mut::<16>().0.iter_mut().zip(commands) {
        lane[..8].copy_from_slice(&cmd.data.to_le_bytes());
        let control =
            u32::from(cmd.addr) | (u32::from(cmd.idx & 31) << 16) | (u32::from(cmd.op) << 21);
        lane[8..12].copy_from_slice(&control.to_le_bytes());
    }
    beat
}

#[derive(Debug, PartialEq, Eq)]
pub enum F2Error<E> {
    Transport(E),
    Identity,
    Range,
    Timeout,
    Response,
    Resident(u8),
}

pub trait Bar0Pcis {
    type Error;
    fn read32(&mut self, address: u32) -> Result<u32, Self::Error>;
    fn write32(&mut self, address: u32, value: u32) -> Result<(), Self::Error>;
    fn read_pcis(&mut self, address: u64, bytes: &mut [u8]) -> Result<(), Self::Error>;
    fn write_pcis(&mut self, address: u64, bytes: &[u8]) -> Result<(), Self::Error>;
    /// BAR4 CPU stores can arrive as partial beats. Publish their descriptors
    /// with one doorbell after all byte strobes have reached the queue RAM.
    fn stage_commands(&self) -> bool {
        false
    }
}

/// BAR0 anchor status. Health covers the hardware startup window and sticky
/// continuous-test results. The seeded flag acknowledges a host mailbox commit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AnchorStatus {
    pub ok: bool,
    pub rct_fail: bool,
    pub apt_fail: bool,
    pub sysmon_ready: bool,
    pub nitro_seeded: bool,
    pub epoch_cnt: u16,
}

pub struct AwsF2Backend<T> {
    io: T,
    engines: u8,
}
type ResultF<T, E> = Result<T, F2Error<E>>;

impl<T: Bar0Pcis> AwsF2Backend<T> {
    pub fn attach(mut io: T) -> ResultF<Self, T::Error> {
        let magic = io.read32(0).map_err(F2Error::Transport)?;
        let abi = io.read32(4).map_err(F2Error::Transport)?;
        let n = io.read32(8).map_err(F2Error::Transport)?;
        if magic != MAGIC || abi != ABI || !(1..=4).contains(&n) {
            return Err(F2Error::Identity);
        }
        let mut backend = Self {
            io,
            engines: n as u8,
        };
        backend.poll(0x28, 1, 0)?;
        Ok(backend)
    }
    pub fn engine_count(&self) -> u8 {
        self.engines
    }
    /// True when the image exposes only the public ASS2 pad diagnostics.
    pub fn diagnostics_only(&mut self) -> ResultF<bool, T::Error> {
        Ok(self.read(12)? & (1 << 31) != 0)
    }
    pub fn anchor_status(&mut self) -> ResultF<AnchorStatus, T::Error> {
        let flags = self.read(0x54)?;
        Ok(AnchorStatus {
            ok: flags & 1 != 0,
            rct_fail: flags & 2 != 0,
            apt_fail: flags & 4 != 0,
            sysmon_ready: flags & 8 != 0,
            nitro_seeded: flags & 16 != 0,
            epoch_cnt: (flags >> 16) as u16,
        })
    }

    /// Provision a globally scrubbed device before selecting any vat. The
    /// caller authenticates the recipient and obtains the seed from KMS.
    pub fn inject_nitro_seed(&mut self, seed: &[u8; 32]) -> ResultF<(), T::Error> {
        let before = self.anchor_status()?.epoch_cnt;
        for (i, word) in seed.as_chunks::<4>().0.iter().enumerate() {
            self.write(0x30 + 4 * i as u32, u32::from_le_bytes(*word))?;
        }
        self.write(0x50, 1)?;
        self.poll(0x54, 0x1f, 0x19)?;
        if self.anchor_status()?.epoch_cnt != before.wrapping_add(1) {
            return Err(F2Error::Response);
        }
        Ok(())
    }
    pub fn into_inner(self) -> T {
        self.io
    }
    pub fn ni(&mut self, index: u8) -> ResultF<F2NiSession<'_, T>, T::Error> {
        if index >= self.engines {
            return Err(F2Error::Range);
        }
        Ok(F2NiSession {
            backend: self,
            csr: 4096 * (u32::from(index) + 1),
            dma: u64::from(index) << 20,
        })
    }
    pub fn enclaves(&mut self) -> F2Ass2Cluster<'_, T> {
        F2Ass2Cluster { backend: self }
    }
    fn read(&mut self, addr: u32) -> ResultF<u32, T::Error> {
        self.io.read32(addr).map_err(F2Error::Transport)
    }
    fn write(&mut self, addr: u32, value: u32) -> ResultF<(), T::Error> {
        self.io.write32(addr, value).map_err(F2Error::Transport)
    }
    fn poll(&mut self, addr: u32, mask: u32, value: u32) -> ResultF<(), T::Error> {
        for _ in 0..POLLS {
            if self.read(addr)? & mask == value {
                return Ok(());
            }
            core::hint::spin_loop();
        }
        Err(F2Error::Timeout)
    }
    pub fn zeroize(&mut self) -> ResultF<(), T::Error> {
        for e in 0..self.engines {
            let csr = 4096 * (u32::from(e) + 1);
            self.poll(csr + 16, 1, 1)?;
        }
        let before = self.read(0x2c)?;
        for _ in 0..POLLS {
            self.write(0x28, 1)?;
            if self.read(0x2c)? != before {
                return self.poll(0x28, 1, 0);
            }
            core::hint::spin_loop();
        }
        Err(F2Error::Timeout)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyStatus {
    pub pass: bool,
    pub checks: u32,
}

pub struct F2NiSession<'a, T> {
    backend: &'a mut AwsF2Backend<T>,
    csr: u32,
    dma: u64,
}

impl<T: Bar0Pcis> F2NiSession<'_, T> {
    fn idle(&mut self) -> ResultF<(), T::Error> {
        self.backend.poll(self.csr + 16, 1, 1)
    }
    pub fn command(&mut self, cmd: NiCmd) -> ResultF<u64, T::Error> {
        if cmd.idx > 31 {
            return Err(F2Error::Range);
        }
        self.idle()?;
        let before = self.backend.read(self.csr + 32)?;
        self.backend.write(self.csr, cmd.data as u32)?;
        self.backend.write(self.csr + 4, (cmd.data >> 32) as u32)?;
        self.backend.write(
            self.csr + 8,
            (u32::from(cmd.op) << 21) | (u32::from(cmd.idx) << 16) | u32::from(cmd.addr),
        )?;
        self.backend.write(self.csr + 12, 1)?;
        self.idle()?;
        if self.backend.read(self.csr + 32)? != before.wrapping_add(1) {
            return Err(F2Error::Response);
        }
        let lo = self.backend.read(self.csr + 24)?;
        let hi = self.backend.read(self.csr + 28)?;
        Ok(u64::from(lo) | (u64::from(hi) << 32))
    }
    pub fn status(&mut self) -> ResultF<VerifyStatus, T::Error> {
        let word = self.command(STATUS)?;
        Ok(VerifyStatus {
            pass: word >> 32 == 1,
            checks: word as u32,
        })
    }
    /// Preserve neighboring words at both ends and split at each AXI page.
    pub fn upload_words(&mut self, first: u16, words: &[u64]) -> ResultF<(), T::Error> {
        let mut pos = usize::from(first);
        if words.len() > SRAM_WORDS - pos {
            return Err(F2Error::Range);
        }
        self.idle()?;
        let mut rest = words;
        let mut page = [0; PAGE];
        while !rest.is_empty() {
            let first_byte = pos * 8;
            let offset = first_byte % 64;
            let n = rest.len().min((PAGE - first_byte % PAGE) / 8);
            let len = (offset + 8 * n).next_multiple_of(64);
            let addr = self.dma + (first_byte - offset) as u64;
            if offset != 0 {
                self.backend
                    .io
                    .read_pcis(addr, &mut page[..64])
                    .map_err(F2Error::Transport)?;
            }
            if !(offset + 8 * n).is_multiple_of(64) && (len != 64 || offset == 0) {
                self.backend
                    .io
                    .read_pcis(addr + (len - 64) as u64, &mut page[len - 64..len])
                    .map_err(F2Error::Transport)?;
            }
            for (dst, word) in page[offset..offset + n * 8]
                .as_chunks_mut::<8>()
                .0
                .iter_mut()
                .zip(rest)
            {
                *dst = word.to_le_bytes();
            }
            self.backend
                .io
                .write_pcis(addr, &page[..len])
                .map_err(F2Error::Transport)?;
            pos += n;
            rest = &rest[n..];
        }
        Ok(())
    }
    /// Read arbitrary word ranges over PCIS. Reads use complete aligned
    /// beats and copy only the requested words into the caller's buffer.
    pub fn read_words(&mut self, first: u16, words: &mut [u64]) -> ResultF<(), T::Error> {
        let mut pos = usize::from(first);
        if words.len() > SRAM_WORDS - pos {
            return Err(F2Error::Range);
        }
        self.idle()?;
        let mut rest = words;
        let mut page = [0; PAGE];
        while !rest.is_empty() {
            let byte = pos * 8;
            let offset = byte % 64;
            let n = rest.len().min((PAGE - byte % PAGE) / 8);
            let len = (offset + 8 * n).next_multiple_of(64);
            self.backend
                .io
                .read_pcis(self.dma + (byte - offset) as u64, &mut page[..len])
                .map_err(F2Error::Transport)?;
            for (dst, src) in rest[..n]
                .iter_mut()
                .zip(page[offset..offset + n * 8].as_chunks::<8>().0)
            {
                *dst = u64::from_le_bytes(*src);
            }
            rest = &mut rest[n..];
            pos += n;
        }
        Ok(())
    }
    /// Wait for retirement of each page-sized batch. Padding uses RD_STATUS,
    /// which preserves the verifier state and always retires a response.
    pub fn stream(&mut self, commands: &[NiCmd]) -> ResultF<(), T::Error> {
        if commands.iter().any(|c| c.idx > 31) {
            return Err(F2Error::Range);
        }
        let mut page = [0; PAGE];
        for batch in commands.chunks(256) {
            self.idle()?;
            let before = self.backend.read(self.csr + 32)?;
            let beats = batch.len().div_ceil(4);
            for (dst, src) in page.as_chunks_mut::<64>().0.iter_mut().zip(batch.chunks(4)) {
                let mut lanes = [STATUS; 4];
                lanes[..src.len()].copy_from_slice(src);
                *dst = pack_pcis_cmd_beat(lanes);
            }
            let staged = self.backend.io.stage_commands();
            let addr = self.dma + if staged { STAGING } else { STREAM };
            self.backend
                .io
                .write_pcis(addr, &page[..beats * 64])
                .map_err(F2Error::Transport)?;
            if staged {
                self.backend.read(0)?; // Flush posted PCI writes before the doorbell.
                self.backend.write(0x10, addr as u32)?;
                self.backend.write(0x14, beats as u32)?;
                self.backend.write(0x18, 1)?;
            }
            self.idle()?;
            self.backend.poll(
                self.csr + 32,
                u32::MAX,
                before.wrapping_add((beats * 4) as u32),
            )?;
        }
        Ok(())
    }
    /// Upload an arbitrary byte slice into NI SRAM starting at `first_word`,
    /// zero-padding any trailing partial 64-bit word.
    pub fn upload_bytes(&mut self, first_word: u16, bytes: &[u8]) -> ResultF<(), T::Error> {
        let words_len = bytes.len().div_ceil(8);
        if words_len > SRAM_WORDS - usize::from(first_word) {
            return Err(F2Error::Range);
        }
        let mut words = Vec::with_capacity(words_len);
        for chunk in bytes.chunks(8) {
            let mut b = [0u8; 8];
            b[..chunk.len()].copy_from_slice(chunk);
            words.push(u64::from_le_bytes(b));
        }
        self.upload_words(first_word, &words)
    }
    /// Verify a serialized `QSAGZKH2` or `QSAGHQM2` proof autonomously on-chip
    /// via PCIS DMA + `OP_VERIFY_PROOF_AUTO` (`0x50`).
    ///
    /// Pass `window_words = 0` when `proof` + `descriptor` + verifier scratch fit
    /// in the 512 KiB NI SRAM (single `0x50` command); pass `window_words >= 8`
    /// (64-byte PCIS beat aligned, `window_words % 8 == 0`) to stream arbitrarily
    /// large proofs through a hardware-bounded SRAM window via `0x51`.
    pub fn verify_proof_auto(
        &mut self,
        descriptor: &[u8],
        proof: &[u8],
        window_words: u16,
    ) -> ResultF<VerifyStatus, T::Error> {
        if (window_words != 0 && (window_words < 8 || !window_words.is_multiple_of(8)))
            || proof.len() > 0xe000_0000
        {
            return Err(F2Error::Range);
        }
        let proof_words = proof.len().div_ceil(8);
        let desc_words = descriptor.len().div_ceil(8);
        let desc_addr_usize = if window_words == 0 {
            proof_words + 1
        } else {
            usize::from(window_words)
        };
        if desc_addr_usize
            .checked_add(desc_words)
            .is_none_or(|end| end > SRAM_WORDS)
        {
            return Err(F2Error::Range);
        }
        let desc_word = u16::try_from(desc_addr_usize).map_err(|_| F2Error::Range)?;
        let initial_bytes = if window_words == 0 {
            proof.len()
        } else {
            proof.len().min(usize::from(window_words) * 8)
        };
        self.upload_bytes(0, &proof[..initial_bytes])?;
        self.upload_bytes(desc_word, descriptor)?;
        let clear = NiCmd {
            op: 0x08,
            idx: 1,
            addr: 0,
            data: 0,
        };
        let kickoff = ((proof.len() as u64) << 32) | (u64::from(window_words) << 16);
        let launch = NiCmd {
            op: OP_VERIFY_PROOF_AUTO,
            idx: 0,
            addr: desc_word,
            data: kickoff,
        };
        if window_words == 0 {
            // Issue [SET_PTR(clear), OP_VERIFY_PROOF_AUTO, RD_STATUS, RD_STATUS] in one
            // 64-byte PCIS beat (triggered by a single BAR0 ring doorbell when staged).
            self.stream(&[clear, launch])?;
            let lo = self.backend.read(self.csr + 24)?;
            let hi = self.backend.read(self.csr + 28)?;
            let word = u64::from(lo) | (u64::from(hi) << 32);
            let checks = word as u32;
            return Ok(VerifyStatus {
                pass: (word >> 32 == 1) && checks > 0,
                checks,
            });
        }
        self.command(clear)?;
        let mut reply = self.command(launch)?;
        let mut prior_offset = 0usize;
        while (reply >> 56) as u8 == OP_PAGE_CONTINUE {
            let offset = (reply as u32) as usize;
            if window_words < 8
                || offset <= prior_offset
                || offset >= proof.len()
                || !offset.is_multiple_of(8)
            {
                return Err(F2Error::Response);
            }
            prior_offset = offset;
            let end = proof.len().min(offset + usize::from(window_words) * 8);
            self.upload_bytes(0, &proof[offset..end])?;
            reply = self.command(NiCmd {
                op: OP_PAGE_CONTINUE,
                idx: 0,
                addr: 0,
                data: offset as u64,
            })?;
        }
        if reply > 1 {
            return Err(F2Error::Response);
        }
        let mut status = self.status()?;
        status.pass = status.pass && status.checks > 0;
        if status.pass != (reply == 1) {
            return Err(F2Error::Response);
        }
        Ok(status)
    }
}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum SerialWidth {
    Spi = 0,
    Quad = 1,
    Octal = 2,
}

pub struct F2Ass2Cluster<'a, T> {
    backend: &'a mut AwsF2Backend<T>,
}
impl<T: Bar0Pcis> F2Ass2Cluster<'_, T> {
    fn base(vat: u8) -> ResultF<u32, T::Error> {
        if vat < 3 {
            Ok((u32::from(vat) + 1) << 16)
        } else {
            Err(F2Error::Range)
        }
    }
    fn shift(&mut self, base: u32, width: SerialWidth, byte: u8) -> ResultF<u8, T::Error> {
        self.backend
            .write(base + 4, ((width as u32) << 8) | u32::from(byte))?;
        self.backend.poll(base + 8, 1, 0)?;
        Ok(self.backend.read(base + 12)? as u8)
    }
    fn selected<R>(
        &mut self,
        base: u32,
        f: impl FnOnce(&mut Self) -> ResultF<R, T::Error>,
    ) -> ResultF<R, T::Error> {
        self.backend.write(base, 1)?;
        let result = f(self);
        let end = self.backend.write(base, 0);
        let val = result?;
        end?;
        Ok(val)
    }
    pub fn diag(&mut self, vat: u8) -> ResultF<u64, T::Error> {
        let base = Self::base(vat)?;
        self.selected(base, |s| {
            s.shift(base, SerialWidth::Spi, 5)?;
            s.shift(base, SerialWidth::Spi, 0)?;
            let mut bytes = [0; 8];
            for b in &mut bytes {
                *b = s.shift(base, SerialWidth::Spi, 0)?;
            }
            Ok(u64::from_be_bytes(bytes))
        })
    }
    pub fn reset(&mut self, vat: u8) -> ResultF<(), T::Error> {
        let base = Self::base(vat)?;
        self.backend.write(base, 2)?;
        self.backend.write(base, 0)?;
        self.backend.poll(base + 8, 2, 2)
    }
    /// Payload length is the unpadded ASS2 byte count, including LOAD_CODE's
    /// count, image and tag (up to 812 B for 128-word inline `WOTS+C` `CMD_LOAD_CODE`).
    /// The wire transfer ends on a 64-bit boundary.
    pub fn command(
        &mut self,
        vat: u8,
        width: SerialWidth,
        op: u8,
        flags: u8,
        arg: u16,
        payload: &[u8],
    ) -> ResultF<Vec<u8>, T::Error> {
        let base = Self::base(vat)?;
        if (op & 0x80) != 0 || payload.len() > 812 {
            return Err(F2Error::Range);
        }
        self.backend.poll(base + 8, 2, 2)?;
        let h = 0x51
            | u64::from(op) << 8
            | u64::from(flags) << 16
            | (payload.len() as u64) << 24
            | u64::from(arg) << 48;
        self.selected(base, |s| {
            s.shift(base, SerialWidth::Spi, (width as u8) << 6)?;
            for b in h.to_le_bytes() {
                s.shift(base, width, b)?;
            }
            for &b in payload {
                s.shift(base, width, b)?;
            }
            for _ in payload.len()..payload.len().next_multiple_of(8) {
                s.shift(base, width, 0)?;
            }
            Ok(())
        })?;
        self.backend.poll(base + 8, 6, 6)?;
        self.selected(base, |s| {
            s.shift(base, SerialWidth::Spi, ((width as u8) << 6) | 2)?;
            s.shift(base, SerialWidth::Spi, 0)?;
            let mut header = [0; 8];
            for b in &mut header {
                *b = s.shift(base, width, 0)?;
            }
            if header[0] != 0x51 || header[1] != (op | 0x80) {
                return Err(F2Error::Response);
            }
            if header[2] == 0x80 {
                if header[3] != 0
                    || header[4] != 0
                    || header[5] != 0
                    || header[6] == 0
                    || header[6] > 31
                    || header[7] != 0
                {
                    return Err(F2Error::Response);
                }
                return Err(F2Error::Resident(header[6]));
            }
            if header[2] != 1 || header[3] > 160 || header[4..8] != [0; 4] {
                return Err(F2Error::Response);
            }
            let mut out = Vec::with_capacity(usize::from(header[3]));
            for _ in 0..header[3] {
                out.push(s.shift(base, width, 0)?);
            }
            Ok(out)
        })
    }
    /// Assert the physical tamper input. A local reset reopens this vat.
    pub fn tamper(&mut self, vat: u8) -> ResultF<(), T::Error> {
        let base = Self::base(vat)?;
        self.backend.poll(base + 8, 1, 0)?;
        self.backend.write(base, 4)
    }
    /// Each authorization consumes an independent persistent generation.
    /// Preserve all three outcomes so callers can reconcile partial success.
    pub fn cth_sign_three(&mut self, requests: &[[u8; 120]; 3]) -> [ResultF<Vec<u8>, T::Error>; 3] {
        core::array::from_fn(|i| self.cth_sign(i as u8, &requests[i]))
    }
    pub fn cth_sign(&mut self, vat: u8, request: &[u8; 120]) -> ResultF<Vec<u8>, T::Error> {
        self.command(vat, SerialWidth::Octal, 0x20, 0, 0, request)
    }
}

#[cfg(all(feature = "std", target_os = "linux"))]
pub mod linux {
    use super::{Bar0Pcis, PAGE};
    use std::{
        fs::{File, OpenOptions},
        io::{self, ErrorKind},
        os::unix::fs::FileExt,
    };

    fn invalid() -> io::Error {
        io::Error::from(ErrorKind::InvalidInput)
    }
    fn transfer_ok(n: usize, expected: usize) -> io::Result<()> {
        if n == expected {
            Ok(())
        } else {
            Err(io::Error::from(ErrorKind::UnexpectedEof))
        }
    }
    fn dma_range(address: u64, n: usize) -> io::Result<()> {
        if !address.is_multiple_of(64)
            || !n.is_multiple_of(64)
            || n > PAGE
            || (address as usize % PAGE) + n > PAGE
        {
            return Err(invalid());
        }
        Ok(())
    }
    #[repr(align(64))]
    struct Aligned([u8; PAGE]);
    pub struct Xdma {
        bar: File,
        h2c: File,
        c2h: File,
    }
    impl Xdma {
        pub fn open(index: u32) -> io::Result<Self> {
            let dev = std::format!("/dev/xdma{index}");
            Ok(Self {
                bar: OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(std::format!("{dev}_user"))?,
                h2c: OpenOptions::new()
                    .write(true)
                    .open(std::format!("{dev}_h2c_0"))?,
                c2h: File::open(std::format!("{dev}_c2h_0"))?,
            })
        }
    }
    impl Bar0Pcis for Xdma {
        type Error = io::Error;
        fn read32(&mut self, a: u32) -> io::Result<u32> {
            if !a.is_multiple_of(4) {
                return Err(invalid());
            }
            let mut b = [0; 4];
            transfer_ok(self.bar.read_at(&mut b, u64::from(a))?, 4)?;
            Ok(u32::from_le_bytes(b))
        }
        fn write32(&mut self, a: u32, v: u32) -> io::Result<()> {
            if !a.is_multiple_of(4) {
                return Err(invalid());
            }
            transfer_ok(self.bar.write_at(&v.to_le_bytes(), u64::from(a))?, 4)
        }
        fn read_pcis(&mut self, a: u64, b: &mut [u8]) -> io::Result<()> {
            dma_range(a, b.len())?;
            let mut buf = Aligned([0; PAGE]);
            transfer_ok(self.c2h.read_at(&mut buf.0[..b.len()], a)?, b.len())?;
            b.copy_from_slice(&buf.0[..b.len()]);
            Ok(())
        }
        fn write_pcis(&mut self, a: u64, b: &[u8]) -> io::Result<()> {
            dma_range(a, b.len())?;
            let mut buf = Aligned([0; PAGE]);
            buf.0[..b.len()].copy_from_slice(b);
            transfer_ok(self.h2c.write_at(&buf.0[..b.len()], a)?, b.len())
        }
    }

    #[cfg(target_pointer_width = "64")]
    #[allow(unsafe_code)]
    mod mapping {
        use super::*;
        use core::{ffi::c_void, ptr::NonNull};
        use std::{os::fd::AsRawFd, path::Path};
        unsafe extern "C" {
            fn mmap(
                a: *mut c_void,
                len: usize,
                prot: i32,
                flags: i32,
                fd: i32,
                offset: i64,
            ) -> *mut c_void;
            fn munmap(a: *mut c_void, len: usize) -> i32;
        }
        struct Window {
            ptr: NonNull<u8>,
            len: usize,
        }
        impl Window {
            fn open(path: &Path, len: usize) -> io::Result<Self> {
                let file = OpenOptions::new().read(true).write(true).open(path)?;
                if file.metadata()?.len() < len as u64 {
                    return Err(invalid());
                }
                // MAP_SHARED, PROT_READ|PROT_WRITE. The mapping retains the file
                // after close. Use the uncached resource, never resourceN_wc.
                let raw = unsafe { mmap(core::ptr::null_mut(), len, 3, 1, file.as_raw_fd(), 0) };
                if raw.addr() == usize::MAX {
                    return Err(io::Error::last_os_error());
                }
                Ok(Self {
                    ptr: NonNull::new(raw.cast()).ok_or_else(invalid)?,
                    len,
                })
            }
            fn word(&self, a: usize) -> io::Result<*mut u32> {
                if !a.is_multiple_of(4) || a > self.len - 4 {
                    return Err(invalid());
                }
                // mmap is page aligned. Range and alignment were checked above.
                Ok(unsafe { self.ptr.as_ptr().add(a).cast() })
            }
            fn read(&self, a: usize) -> io::Result<u32> {
                let p = self.word(a)?;
                Ok(u32::from_le(unsafe { p.read_volatile() }))
            }
            fn write(&mut self, a: usize, v: u32) -> io::Result<()> {
                let p = self.word(a)?;
                unsafe { p.write_volatile(v.to_le()) };
                Ok(())
            }
        }
        impl Drop for Window {
            fn drop(&mut self) {
                unsafe { munmap(self.ptr.as_ptr().cast(), self.len) };
            }
        }
        /// AppPF sysfs directory such as /sys/bus/pci/devices/0000:35:00.0.
        pub struct PciBars {
            bar0: Window,
            bar4: Window,
        }
        impl PciBars {
            pub fn open(app_pf: &Path) -> io::Result<Self> {
                Ok(Self {
                    bar0: Window::open(&app_pf.join("resource0"), 0x40000)?,
                    bar4: Window::open(&app_pf.join("resource4"), 4 << 20)?,
                })
            }
        }
        impl Bar0Pcis for PciBars {
            type Error = io::Error;
            fn stage_commands(&self) -> bool {
                true
            }
            fn read32(&mut self, a: u32) -> io::Result<u32> {
                self.bar0.read(a as usize)
            }
            fn write32(&mut self, a: u32, v: u32) -> io::Result<()> {
                self.bar0.write(a as usize, v)
            }
            fn read_pcis(&mut self, a: u64, b: &mut [u8]) -> io::Result<()> {
                dma_range(a, b.len())?;
                if a > self.bar4.len.saturating_sub(b.len()) as u64 {
                    return Err(invalid());
                }
                for (i, d) in b.as_chunks_mut::<4>().0.iter_mut().enumerate() {
                    *d = self.bar4.read(a as usize + 4 * i)?.to_le_bytes();
                }
                Ok(())
            }
            fn write_pcis(&mut self, a: u64, b: &[u8]) -> io::Result<()> {
                dma_range(a, b.len())?;
                if a > self.bar4.len.saturating_sub(b.len()) as u64 {
                    return Err(invalid());
                }
                for (i, d) in b.as_chunks::<4>().0.iter().enumerate() {
                    self.bar4
                        .write(a as usize + 4 * i, u32::from_le_bytes(*d))?;
                }
                Ok(())
            }
        }
    }
    #[cfg(target_pointer_width = "64")]
    pub use mapping::PciBars;
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{collections::BTreeMap, vec};
    #[derive(Default)]
    struct MockF2Bar0Pcis {
        regs: BTreeMap<u32, u32>,
        rows: BTreeMap<u64, [u8; 64]>,
        cmds: Vec<(usize, NiCmd)>,
        done: [u32; 2],
        checks: [u32; 2],
        fail: [bool; 2],
        reply: [u64; 2],
        staged: bool,
        serial: Vec<(u32, u32)>,
        rx: [u8; 3],
        step: [usize; 3],
        prefix: [u8; 3],
        opcode: [u8; 3],
    }
    impl MockF2Bar0Pcis {
        fn exec(&mut self, e: usize, c: NiCmd) {
            self.cmds.push((e, c));
            self.done[e] += 1;
            if c.op == 8 && c.idx == 1 {
                self.checks[e] = 0;
                self.fail[e] = false;
            }
            if c.op == 10 {
                self.checks[e] += 1;
                self.fail[e] |= c.data != 0;
            }
            if c.op == OP_VERIFY_PROOF_AUTO {
                let win = ((c.data >> 16) & 0xffff) as usize;
                let total = (c.data >> 32) as usize;
                if win > 0 && total > win * 8 {
                    self.reply[e] = (u64::from(OP_PAGE_CONTINUE) << 56) | ((win * 8) as u64);
                } else {
                    let row0 = self.rows.get(&((e as u64) << 20)).copied().unwrap_or([0; 64]);
                    let ok = row0[0] == b'Q';
                    self.checks[e] += 107;
                    self.fail[e] |= !ok;
                    self.reply[e] = u64::from(ok);
                }
            }
            if c.op == OP_PAGE_CONTINUE {
                let row0 = self.rows.get(&((e as u64) << 20)).copied().unwrap_or([0; 64]);
                let ok = row0[0] != 0xff;
                self.checks[e] += 107;
                self.fail[e] |= !ok;
                self.reply[e] = u64::from(ok);
            }
            if c.op == 11 {
                self.reply[e] = (u64::from(!self.fail[e]) << 32) | u64::from(self.checks[e]);
            }
        }
        fn unpack(&mut self, e: usize, b: &[u8]) {
            for l in b.as_chunks::<16>().0 {
                let data = u64::from_le_bytes(l[..8].try_into().unwrap());
                let ctl = u32::from_le_bytes(l[8..12].try_into().unwrap());
                self.exec(
                    e,
                    NiCmd {
                        op: (ctl >> 21) as u8,
                        idx: ((ctl >> 16) & 31) as u8,
                        addr: ctl as u16,
                        data,
                    },
                );
            }
        }
    }
    impl Bar0Pcis for MockF2Bar0Pcis {
        type Error = ();
        fn stage_commands(&self) -> bool {
            self.staged
        }
        fn read32(&mut self, a: u32) -> Result<u32, ()> {
            Ok(match a {
                0 => MAGIC,
                4 => ABI,
                8 => 2,
                0x28 => 0,
                0x1000..=0x2fff => {
                    let e = (a / 4096 - 1) as usize;
                    match a % 4096 {
                        16 => 5,
                        20 => self.checks[e],
                        24 => self.reply[e] as u32,
                        28 => (self.reply[e] >> 32) as u32,
                        32 => self.done[e],
                        _ => return Err(()),
                    }
                }
                0x10000..=0x3ffff => match a & 65535 {
                    8 => 6,
                    12 => u32::from(self.rx[(a as usize >> 16) - 1]),
                    _ => 0,
                },
                _ => *self.regs.get(&a).unwrap_or(&0),
            })
        }
        fn write32(&mut self, a: u32, v: u32) -> Result<(), ()> {
            self.regs.insert(a, v);
            if a == 0x28 && v == 1 {
                let next = self.regs.get(&0x2c).copied().unwrap_or(0).wrapping_add(1);
                self.regs.insert(0x2c, next);
            } else if a == 0x50 && v == 1 {
                let prev = (self.regs.get(&0x54).copied().unwrap_or(0) >> 16) as u16;
                self.regs
                    .insert(0x54, (u32::from(prev.wrapping_add(1)) << 16) | 0x19);
            } else if a == 0x18 {
                let base = u64::from(self.regs[&0x10]);
                for i in 0..self.regs[&0x14] {
                    let beat = self.rows[&(base + 64 * u64::from(i))];
                    self.unpack((base >> 20) as usize, &beat);
                }
            } else if (0x1000..0x3000).contains(&a) && a % 4096 == 12 {
                let base = a - 12;
                let ctl = self.regs[&(base + 8)];
                self.exec(
                    (base / 4096 - 1) as usize,
                    NiCmd {
                        op: (ctl >> 21) as u8,
                        idx: (ctl >> 16) as u8 & 31,
                        addr: ctl as u16,
                        data: u64::from(self.regs[&base])
                            | (u64::from(self.regs[&(base + 4)]) << 32),
                    },
                );
            } else if a >= 0x10000 {
                let e = (a as usize >> 16) - 1;
                self.serial.push((a, v));
                if a.is_multiple_of(65536) {
                    self.step[e] = 0;
                } else {
                    let step = self.step[e];
                    if step == 0 {
                        self.prefix[e] = v as u8;
                    }
                    self.rx[e] = match self.prefix[e] {
                        5 => [0, 0, 0x5a, 0x03, 0, 0, e as u8, 0, 0xa5, 0x52][step],
                        0x80 => {
                            if step == 2 {
                                self.opcode[e] = v as u8;
                            }
                            0
                        }
                        0x82 if (2..10).contains(&step) => {
                            // Model an independently denied approval on vat 1.
                            let header = if e == 1 {
                                [0x51, self.opcode[e] | 0x80, 0x80, 0, 0, 0, 5, 0]
                            } else {
                                [0x51, self.opcode[e] | 0x80, 1, 8, 0, 0, 0, 0]
                            };
                            header[step - 2]
                        }
                        0x82 => e as u8,
                        _ => return Err(()),
                    };
                    self.step[e] += 1;
                }
            }
            Ok(())
        }
        fn read_pcis(&mut self, a: u64, b: &mut [u8]) -> Result<(), ()> {
            for (i, row) in b.as_chunks_mut::<64>().0.iter_mut().enumerate() {
                *row = *self.rows.get(&(a + i as u64 * 64)).unwrap_or(&[0xaa; 64]);
            }
            Ok(())
        }
        fn write_pcis(&mut self, a: u64, b: &[u8]) -> Result<(), ()> {
            assert!(a.is_multiple_of(64));
            assert!((a as usize % 4096) + b.len() <= 4096);
            for (i, row) in b.as_chunks::<64>().0.iter().enumerate() {
                if a & 0xf0000 == STREAM {
                    self.unpack((a >> 20) as usize, row);
                } else {
                    self.rows.insert(a + 64 * i as u64, *row);
                }
            }
            Ok(())
        }
    }
    #[test]
    fn seed_words_and_anchor_flags() {
        let mut hw = AwsF2Backend::attach(MockF2Bar0Pcis::default()).unwrap();
        hw.io.regs.insert(0x54, 0x1234_0006);
        let failed = hw.anchor_status().unwrap();
        assert_eq!(failed.epoch_cnt, 0x1234);
        assert!(failed.rct_fail && failed.apt_fail && !failed.ok);
        let seed = core::array::from_fn(|i| i as u8);
        hw.inject_nitro_seed(&seed).unwrap();
        for i in 0..8 {
            assert_eq!(hw.io.regs[&(0x30 + 4 * i)], 0x03020100 + i * 0x04040404);
        }
        let ready = hw.anchor_status().unwrap();
        assert!(ready.ok && ready.sysmon_ready && ready.nitro_seeded);
        assert_eq!(ready.epoch_cnt, 0x1235);
        hw.zeroize().unwrap();
        assert_eq!(hw.io.regs[&0x2c], 1);
    }

    #[test]
    fn independent_lane_encoding() {
        let c = NiCmd {
            op: 0xff,
            idx: 31,
            addr: 0xabcd,
            data: 0x0102030405060708,
        };
        let b = pack_pcis_cmd_beat([STATUS, c, NiCmd::default(), c]);
        assert_eq!(
            &b[16..32],
            &[8, 7, 6, 5, 4, 3, 2, 1, 0xcd, 0xab, 0xff, 0x1f, 0, 0, 0, 0]
        );
        assert_eq!(&b[32..48], &[0; 16]);
        assert_eq!(&b[48..], &b[16..32]);
    }
    #[test]
    fn both_transports_and_engines() {
        for staged in [false, true] {
            let mut b = AwsF2Backend::attach(MockF2Bar0Pcis {
                staged,
                ..Default::default()
            })
            .unwrap();
            assert!(matches!(b.ni(2), Err(F2Error::Range)));
            let mut s = b.ni(1).unwrap();
            s.upload_words(511, &[1, 2, 3]).unwrap();
            let mut words = [0; 3];
            s.read_words(511, &mut words).unwrap();
            assert_eq!(words, [1, 2, 3]);
            assert_eq!(s.upload_words(65535, &[3, 4]), Err(F2Error::Range));
            let mut cmds = vec![STATUS; 257];
            cmds[0] = NiCmd { op: 10, ..STATUS };
            s.stream(&cmds).unwrap();
            assert_eq!(
                s.status().unwrap(),
                VerifyStatus {
                    pass: true,
                    checks: 1
                }
            );
            s.stream(&[NiCmd {
                op: 10,
                data: 1,
                ..STATUS
            }])
            .unwrap();
            assert_eq!(
                s.status().unwrap(),
                VerifyStatus {
                    pass: false,
                    checks: 2
                }
            );
            assert_eq!(
                b.ni(0).unwrap().status().unwrap(),
                VerifyStatus {
                    pass: true,
                    checks: 0
                }
            );
            let io = b.into_inner();
            assert_eq!(&io.rows[&0x100fc0][..56], &[0xaa; 56]);
            assert_eq!(&io.rows[&0x100fc0][56..], &1u64.to_le_bytes());
            assert_eq!(&io.rows[&0x101000][8..16], &3u64.to_le_bytes());
            assert_eq!(&io.rows[&0x101000][16..], &[0xaa; 48]);
        }
    }
    #[test]
    fn three_cth_outcomes_remain_attributed() {
        let mut b = AwsF2Backend::attach(MockF2Bar0Pcis::default()).unwrap();
        let requests = [[0xa0; 120], [0xa1; 120], [0xa2; 120]];
        let results = b.enclaves().cth_sign_three(&requests);
        assert_eq!(
            results,
            [Ok(vec![0; 8]), Err(F2Error::Resident(5)), Ok(vec![2; 8])]
        );
        let io = b.into_inner();
        for (i, request) in requests.iter().enumerate() {
            let base = ((i as u32) + 1) << 16;
            let tx: Vec<u8> = io
                .serial
                .iter()
                .filter_map(|&(a, w)| (a == base + 4).then_some(w as u8))
                .collect();
            assert_eq!(&tx[..9], &[0x80, 0x51, 0x20, 0, 120, 0, 0, 0, 0]);
            assert_eq!(&tx[9..129], request);
        }
    }
    #[test]
    fn three_diagnostic_frames() {
        let mut b = AwsF2Backend::attach(MockF2Bar0Pcis::default()).unwrap();
        for e in 0..3 {
            assert_eq!(
                b.enclaves().diag(e).unwrap(),
                0x5a0300000000a552 | (u64::from(e) << 24)
            );
        }
        assert_eq!(b.enclaves().diag(3), Err(F2Error::Range));
        assert_eq!(b.into_inner().serial.len(), 36);
    }
    #[test]
    fn autonomous_verify_resident_and_paged() {
        for staged in [false, true] {
            let mut b = AwsF2Backend::attach(MockF2Bar0Pcis {
                staged,
                ..Default::default()
            })
            .unwrap();
            let desc = b"\x10\x00\x00\x00ZKD1abcdefgh";
            let mut proof = vec![0x5a; 96];
            proof[..8].copy_from_slice(b"QSAGZKH2");
            assert_eq!(
                b.ni(0).unwrap().verify_proof_auto(desc, &proof, 4),
                Err(F2Error::Range)
            );
            let ok = b.ni(0).unwrap().verify_proof_auto(desc, &proof, 0).unwrap();
            assert_eq!(
                ok,
                VerifyStatus {
                    pass: true,
                    checks: 107
                }
            );
            let paged = b.ni(1).unwrap().verify_proof_auto(desc, &proof, 8).unwrap();
            assert_eq!(
                paged,
                VerifyStatus {
                    pass: true,
                    checks: 107
                }
            );
            proof[0] ^= 1;
            let bad = b.ni(0).unwrap().verify_proof_auto(desc, &proof, 0).unwrap();
            assert!(!bad.pass);
            proof[0] ^= 1;
            proof[64] = 0xff;
            let bad_paged = b.ni(1).unwrap().verify_proof_auto(desc, &proof, 8).unwrap();
            assert!(!bad_paged.pass);
        }
    }

    #[test]
    fn tooth_f2_command_allows_812b_wotsc_load_and_rejects_response_bit_opcode() {
        // `#tooth`: Rev. 2.0 RTL (`qsag_ass2_enclave_top.sv:436`) accepts inline `WOTS+C`
        // `CMD_LOAD_CODE` (`0x30`, `flags = 2`) up to 128 words = `300 + 4 * 128 = 812` bytes,
        // whereas `aws_f2.rs` previously capped `payload.len() <= 532` and allowed `op & 0x80 != 0`.
        let mut b = AwsF2Backend::attach(MockF2Bar0Pcis::default()).unwrap();
        let max_wotsc_load = [0x5Au8; 812];
        assert_eq!(
            b.enclaves()
                .command(0, SerialWidth::Octal, 0x30, 2, 0, &max_wotsc_load),
            Ok(vec![0; 8])
        );
        assert_eq!(
            b.enclaves()
                .command(0, SerialWidth::Octal, 0x30, 2, 0, &[0u8; 813]),
            Err(F2Error::Range)
        );
        assert_eq!(
            b.enclaves()
                .command(0, SerialWidth::Octal, 0xB0, 0, 0, &[0u8; 8]),
            Err(F2Error::Range)
        );
    }

    #[test]
    fn tooth_f2_command_rejects_noncanonical_response_header_upper_bytes() {
        // `#tooth`: RTL `resp_w0` (`qsag_ass2_enclave_top.sv:91-92`) sets `header[4..8]` to
        // zero on success and `{0, 0, err_code[4:0], 0}` with `header[2] == 0x80, header[3] == 0`
        // on error. Previously `F2Ass2Cluster::command` ignored `header[4..8]` on success (turning
        // a 24-bit length `256` `[0x51, op|0x80, 1, 0, 1, 0, 0, 0]` into `Ok(vec![])`) and accepted
        // non-canonical error headers such as `header[2] = 0x81` or `header[6] = 0xFF`.
        struct CustomRespHeaderIo {
            resp_header: [u8; 8],
            rx: u8,
            step: usize,
            prefix: u8,
        }
        impl Bar0Pcis for CustomRespHeaderIo {
            type Error = ();
            fn read32(&mut self, a: u32) -> Result<u32, ()> {
                Ok(match a {
                    0 => MAGIC,
                    4 => ABI,
                    8 => 1,
                    0x28 => 0,
                    0x10008 => 6,
                    0x1000c => u32::from(self.rx),
                    _ => 0,
                })
            }
            fn write32(&mut self, a: u32, v: u32) -> Result<(), ()> {
                if a == 0x10000 {
                    self.step = 0;
                } else if a == 0x10004 {
                    if self.step == 0 {
                        self.prefix = v as u8;
                    }
                    self.rx = if self.prefix == 0x82 && (2..10).contains(&self.step) {
                        self.resp_header[self.step - 2]
                    } else {
                        0xAA
                    };
                    self.step += 1;
                }
                Ok(())
            }
            fn read_pcis(&mut self, _: u64, _: &mut [u8]) -> Result<(), ()> {
                Ok(())
            }
            fn write_pcis(&mut self, _: u64, _: &[u8]) -> Result<(), ()> {
                Ok(())
            }
        }

        for bad_header in [
            [0x51, 0xA0, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00], // 24-bit len = 256 masquerading as 0
            [0x51, 0xA0, 0x01, 0x08, 0x00, 0x00, 0x01, 0x00], // nonzero err_code on success
            [0x51, 0xA0, 0x81, 0x00, 0x00, 0x00, 0x05, 0x00], // both ok & err bits set
            [0x51, 0xA0, 0x80, 0x08, 0x00, 0x00, 0x05, 0x00], // nonzero length on error
            [0x51, 0xA0, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00], // zero resident error code
            [0x51, 0xA0, 0x80, 0x00, 0x00, 0x00, 0x20, 0x00], // out-of-range 5-bit error code (32)
            [0x51, 0xA0, 0x80, 0x00, 0x00, 0x00, 0x05, 0x01], // nonzero reserved byte 7
        ] {
            let mut b = AwsF2Backend::attach(CustomRespHeaderIo {
                resp_header: bad_header,
                rx: 0,
                step: 0,
                prefix: 0,
            })
            .unwrap();
            assert_eq!(
                b.enclaves().cth_sign(0, &[0u8; 120]),
                Err(F2Error::Response),
                "must reject malformed response header {bad_header:02x?}"
            );
        }
    }
}
