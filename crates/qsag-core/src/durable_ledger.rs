//! External monotone anchors, single-use commit tickets over them, and the key-value
//! ledger kept in a [`TwoSlotRecord`].
//! An independently retained checkpoint is a minimum generation, not an exact snapshot:
//! recovery also accepts a durable successor whose external checkpoint was not yet saved.
use crate::two_slot_record::{TwoSlotPaths, TwoSlotRecord};
use crate::{sponge::Cshake256Xof, wipe::ct_eq_bytes32};
use alloc::{collections::BTreeMap, vec::Vec};

/// Persist outside the snapshot's rollback domain before releasing reserved material.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LedgerCheckpoint {
    pub generation: u64,
    pub tag: [u8; 32],
}

/// Independently durable, per-resource rollback protection (for example a TPM or
/// remote monotonic service). The anchor must not share the WAL's rollback domain.
/// `advance` atomically rejects older generations and unequal tags at equal generation;
/// success means the checkpoint survives a crash. A fresh resource returns `None`.
///
/// Every anchor also serves single-use commit tickets through `reserve_ticket`,
/// `consume_ticket` and `reconcile` on `dyn ExternalMonotoneAnchor`; they are built on
/// `load` and `advance` and need nothing from the implementer beyond the contract above.
pub trait ExternalMonotoneAnchor: Send + Sync {
    fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>>;
    fn advance(&self, checkpoint: LedgerCheckpoint) -> std::io::Result<()>;
}

pub(crate) fn advance_anchor(
    anchor: &dyn ExternalMonotoneAnchor,
    checkpoint: LedgerCheckpoint,
) -> std::io::Result<()> {
    if let Some(old) = anchor.load()?
        && (old.generation > checkpoint.generation
            || (old.generation == checkpoint.generation
                && !ct_eq_bytes32(&old.tag, &checkpoint.tag)))
    {
        return Err(std::io::Error::other(
            "external anchor rejects rolled-back state",
        ));
    }
    anchor.advance(checkpoint)
}

/// What the holder of a ticket writes into the record it commits under it. The
/// committed record's own checkpoint (its generation and MAC, which therefore cover
/// all three fields) is what consumption leaves in the anchor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TicketSeal {
    /// Generation the committed record must carry.
    pub generation: u64,
    /// The anchor's tag while the ticket was outstanding.
    pub reservation: [u8; 32],
    /// Drawn inside `consume_ticket`, after the ticket was issued.
    pub nonce: [u8; 32],
}

impl TicketSeal {
    /// The seal of a record committed with no anchor.
    pub const fn unanchored(generation: u64) -> Self {
        Self {
            generation,
            reservation: [0; 32],
            nonce: [0; 32],
        }
    }
}

/// A single-use commit permit issued by `reserve_ticket` on an anchor
/// (the `AnchorTicket` of `Qsag.Exec.CeremonyAtomicityAndAbort`). It is not `Clone`
/// and has no constructor: the only way to spend it is to hand it back to
/// `consume_ticket`, which takes it by value. It lives in memory only, so a crash
/// forfeits it, as `AnchoredJournalStep.crash` clears `pending`.
#[derive(Debug)]
#[must_use = "an unspent ticket leaves the anchor reserved"]
pub struct AnchorTicket {
    epoch: u64,
    owner: [u8; 32],
    floor: [u8; 16],
    context: [u8; 32],
}

fn floor_mark(floor: &LedgerCheckpoint) -> [u8; 16] {
    let mut xof = Cshake256Xof::new(b"QSAG.ANCHOR.FLOOR/v1");
    xof.absorb(&floor.generation.to_le_bytes());
    xof.absorb(&floor.tag);
    let mut mark = [0; 16];
    xof.squeeze(&mut mark);
    mark
}

impl AnchorTicket {
    /// The anchor generation at which this ticket is outstanding.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn context(&self) -> &[u8; 32] {
        &self.context
    }
    /// The anchor's tag while this ticket is outstanding: the floor mark, which a
    /// reopening holder recomputes from its disk, then 16 bytes binding the epoch,
    /// the contender and the context.
    pub fn reservation(&self) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.ANCHOR.TICKET/v2");
        xof.absorb(&self.epoch.to_le_bytes());
        xof.absorb(&self.owner);
        xof.absorb(&self.floor);
        xof.absorb(&self.context);
        let mut tag = [0; 32];
        tag[..16].copy_from_slice(&self.floor);
        xof.squeeze(&mut tag[16..]);
        tag
    }
    fn issued(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: self.epoch,
            tag: self.reservation(),
        }
    }
}

fn fresh_nonce() -> std::io::Result<[u8; 32]> {
    use std::io::Read;
    let mut nonce = [0; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    Ok(nonce)
}

fn same_checkpoint(a: &LedgerCheckpoint, b: &LedgerCheckpoint) -> bool {
    a.generation == b.generation && ct_eq_bytes32(&a.tag, &b.tag)
}

/// How an anchor stands to the record a holder found on its disk.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnchorStanding {
    /// The anchor holds nothing. Only a holder still at its genesis may enrol it.
    Unenrolled,
    /// The anchor holds exactly the holder's checkpoint.
    Settled,
    /// The anchor holds this reservation, taken from the holder's checkpoint and
    /// never committed. The ticket died with its process; the holder supersedes it
    /// with `reserve_ticket(this, its checkpoint, ..)`.
    Reserved(LedgerCheckpoint),
}

/// Single-use commit tickets over any anchor: `anchorCAS` and `anchorConsume` of
/// `Qsag.Exec.CeremonyAtomicityAndAbort`, kept in the anchor's one checkpoint cell
/// together with the holder's own checkpoints.
///
/// The cell alternates between a holder checkpoint `(g, tag)` (settled) and a
/// reservation `(g + 1, floor mark || ticket binding)`; consuming the ticket settles
/// the cell on the successor checkpoint at `g + 2`. A settled cell is therefore
/// always the holder's exact durable checkpoint, and a reserved cell still pins the
/// checkpoint the reservation was taken from, so the cell is a rollback floor in
/// every state.
///
/// These are inherent methods of the trait object, not trait methods, so an
/// implementer cannot replace or omit them; they rely only on the contract of
/// `advance` (an unequal tag at an equal generation is rejected atomically). A
/// reservation carries a nonce drawn inside `reserve_ticket` and a consuming
/// checkpoint covers a nonce drawn inside `consume_ticket`, so two contenders never
/// write equal tags and the anchor admits exactly one of them, including two copies
/// of one process image that both hold the same ticket.
///
/// Differences from the Lean model, all on the refusing side except the last:
/// * the cell holds one ticket, so a later reservation voids an unspent earlier one
///   (`anchorConsume` would still accept it);
/// * `anchorCAS` also refuses a context that an earlier ticket carried
///   (`reservationValid`). One cell has no history, so that check stays with the
///   holder's journal, whose every record the cell pins;
/// * the durable write happens inside `consume_ticket`, between its nonce draw and
///   its anchor write, where the model's `release` is one step. Two copies of a
///   process image taken inside that window write the same checkpoint and are both
///   admitted.
impl dyn ExternalMonotoneAnchor + '_ {
    /// Issue the ticket to commit the successor of `floor`, the holder's durable
    /// checkpoint. Fails unless the anchor holds exactly `expected` (`floor` itself
    /// when settled, an abandoned reservation when `reconcile` said `Reserved`), or
    /// if another contender reserved first.
    pub fn reserve_ticket(
        &self,
        expected: LedgerCheckpoint,
        floor: LedgerCheckpoint,
        context: [u8; 32],
    ) -> std::io::Result<AnchorTicket> {
        if !self
            .load()?
            .is_some_and(|current| same_checkpoint(&current, &expected))
        {
            return Err(std::io::Error::other(
                "external anchor is not at the expected checkpoint",
            ));
        }
        let epoch = expected
            .generation
            .checked_add(1)
            .filter(|epoch| *epoch < u64::MAX)
            .ok_or_else(|| std::io::Error::other("anchor generations exhausted"))?;
        let ticket = AnchorTicket {
            epoch,
            owner: fresh_nonce()?,
            floor: floor_mark(&floor),
            context,
        };
        self.advance(ticket.issued())?;
        Ok(ticket)
    }

    /// Spend `ticket` on the record `commit` makes durable: `commit` receives the
    /// seal to write into that record and returns the record's checkpoint, which
    /// then replaces the reservation in the anchor. Succeeds at most once per ticket
    /// across every holder of a copy; on any error nothing may be released under it.
    pub fn consume_ticket(
        &self,
        ticket: AnchorTicket,
        commit: impl FnOnce(&TicketSeal) -> std::io::Result<LedgerCheckpoint>,
    ) -> std::io::Result<(TicketSeal, LedgerCheckpoint)> {
        let issued = ticket.issued();
        if !self
            .load()?
            .is_some_and(|current| same_checkpoint(&current, &issued))
        {
            return Err(std::io::Error::other(
                "external anchor does not hold this ticket unspent",
            ));
        }
        let seal = TicketSeal {
            generation: issued.generation + 1,
            reservation: issued.tag,
            nonce: fresh_nonce()?,
        };
        let checkpoint = commit(&seal)?;
        if checkpoint.generation != seal.generation {
            return Err(std::io::Error::other(
                "committed record does not carry the ticket's generation",
            ));
        }
        self.advance(checkpoint)?;
        Ok((seal, checkpoint))
    }

    /// Reserve from `floor` and commit under the ticket in one step.
    pub fn commit_with_ticket(
        &self,
        expected: LedgerCheckpoint,
        floor: LedgerCheckpoint,
        context: [u8; 32],
        commit: impl FnOnce(&TicketSeal) -> std::io::Result<LedgerCheckpoint>,
    ) -> std::io::Result<(TicketSeal, LedgerCheckpoint)> {
        let ticket = self.reserve_ticket(expected, floor, context)?;
        self.consume_ticket(ticket, commit)
    }

    /// Place a reopening holder, whose authenticated record on disk has `checkpoint`
    /// and was written under `reservation` (all zero if under none):
    ///
    /// * the anchor holds `checkpoint`: settled;
    /// * the anchor holds the reservation that record was written under, one
    ///   generation below it: the crash came after the durable write, and the
    ///   anchor is settled on the record here. Nothing was released under it;
    /// * the anchor holds a reservation taken from `checkpoint`: the crash came
    ///   before the durable write (`Reserved`);
    /// * anything else is a disk older than, or foreign to, what the anchor pins.
    pub fn reconcile(
        &self,
        checkpoint: LedgerCheckpoint,
        reservation: &[u8; 32],
    ) -> std::io::Result<AnchorStanding> {
        let Some(current) = self.load()? else {
            return Ok(AnchorStanding::Unenrolled);
        };
        if same_checkpoint(&current, &checkpoint) {
            return Ok(AnchorStanding::Settled);
        }
        if current.generation.checked_add(1) == Some(checkpoint.generation)
            && *reservation != [0; 32]
            && ct_eq_bytes32(&current.tag, reservation)
        {
            self.advance(checkpoint)?;
            return Ok(AnchorStanding::Settled);
        }
        if checkpoint.generation < current.generation
            && current.tag[..16] == floor_mark(&checkpoint)
        {
            return Ok(AnchorStanding::Reserved(current));
        }
        Err(std::io::Error::other(
            "external anchor rejects rolled-back state",
        ))
    }
}

const LIMIT: usize = 16 * 1024 * 1024;
type Records = BTreeMap<Vec<u8>, Vec<u8>>;

/// A key-value snapshot in one [`TwoSlotRecord`] at `path`, `path.slot_a`, `path.slot_b`.
pub(crate) struct Ledger {
    record: TwoSlotRecord,
}
fn layout(path: std::path::PathBuf) -> TwoSlotPaths {
    let slots = [".slot_a", ".slot_b"].map(|suffix| {
        let mut name = path.as_os_str().to_os_string();
        name.push(suffix);
        name.into()
    });
    TwoSlotPaths {
        genesis: path,
        slots,
    }
}
fn encode(records: &Records) -> Result<Vec<u8>, ()> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&(records.len() as u64).to_le_bytes());
    for (k, v) in records {
        let size = k
            .len()
            .checked_add(v.len())
            .and_then(|n| n.checked_add(8))
            .ok_or(())?;
        if size > LIMIT.saturating_sub(bytes.len()) {
            return Err(());
        }
        bytes.extend_from_slice(&u32::try_from(k.len()).map_err(|_| ())?.to_le_bytes());
        bytes.extend_from_slice(&u32::try_from(v.len()).map_err(|_| ())?.to_le_bytes());
        bytes.extend_from_slice(k);
        bytes.extend_from_slice(v);
    }
    Ok(bytes)
}
fn decode(bytes: &[u8]) -> Result<Records, ()> {
    let end = bytes.len();
    let count = u64::from_le_bytes(bytes.get(..8).ok_or(())?.try_into().map_err(|_| ())?);
    if count > ((end - 8) / 8) as u64 {
        return Err(());
    }
    let mut cur = 8;
    let mut records = Records::new();
    for _ in 0..count {
        if end - cur < 8 {
            return Err(());
        }
        let k = u32::from_le_bytes(bytes[cur..cur + 4].try_into().map_err(|_| ())?) as usize;
        let v = u32::from_le_bytes(bytes[cur + 4..cur + 8].try_into().map_err(|_| ())?) as usize;
        cur += 8;
        let size = k.checked_add(v).ok_or(())?;
        if size > end - cur {
            return Err(());
        }
        if records
            .insert(
                bytes[cur..cur + k].to_vec(),
                bytes[cur + k..cur + size].to_vec(),
            )
            .is_some()
        {
            return Err(());
        }
        cur += size;
    }
    if cur != end {
        return Err(());
    }
    Ok(records)
}
impl Ledger {
    pub(crate) fn create(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
    ) -> Result<Self, ()> {
        let genesis = encode(&Records::new())?;
        TwoSlotRecord::create(layout(path.into()), key, domain, LIMIT, &genesis)
            .map(|record| Self { record })
            .map_err(|_| ())
    }
    pub(crate) fn open(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
        checkpoint: LedgerCheckpoint,
    ) -> Result<Self, ()> {
        TwoSlotRecord::open(layout(path.into()), key, domain, LIMIT, Some(checkpoint))
            .map(|record| Self { record })
            .map_err(|_| ())
    }
    pub(crate) fn checkpoint(&self) -> LedgerCheckpoint {
        self.record.checkpoint()
    }
    pub(crate) fn read(&self) -> Result<Records, ()> {
        decode(&self.record.read().map_err(|_| ())?)
    }
    pub(crate) fn commit(&mut self, records: &Records) -> Result<(), ()> {
        let bytes = encode(records)?;
        self.record.commit(&bytes).map(|_| ()).map_err(|_| ())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A conforming anchor. With `stale_reads`, `load` keeps answering with the
    /// state it saw first, as a contender does that read before another one wrote.
    #[derive(Default)]
    struct MemAnchor {
        cell: std::sync::Mutex<Option<LedgerCheckpoint>>,
        stale: std::sync::Mutex<Option<Option<LedgerCheckpoint>>>,
    }
    impl MemAnchor {
        fn freeze_reads(&self) {
            *self.stale.lock().unwrap() = Some(*self.cell.lock().unwrap());
        }
        fn thaw_reads(&self) {
            *self.stale.lock().unwrap() = None;
        }
        fn stored(&self) -> Option<LedgerCheckpoint> {
            *self.cell.lock().unwrap()
        }
    }
    impl ExternalMonotoneAnchor for MemAnchor {
        fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>> {
            Ok(self.stale.lock().unwrap().unwrap_or(self.stored()))
        }
        fn advance(&self, checkpoint: LedgerCheckpoint) -> std::io::Result<()> {
            let mut cell = self.cell.lock().unwrap();
            if let Some(old) = *cell
                && (checkpoint.generation < old.generation
                    || (checkpoint.generation == old.generation && checkpoint.tag != old.tag))
            {
                return Err(std::io::Error::other("rejected"));
            }
            *cell = Some(checkpoint);
            Ok(())
        }
    }
    /// What a copy of the holder's memory contains.
    fn memory_copy(ticket: &AnchorTicket) -> AnchorTicket {
        AnchorTicket {
            epoch: ticket.epoch,
            owner: ticket.owner,
            floor: ticket.floor,
            context: ticket.context,
        }
    }
    fn ckpt(generation: u64, byte: u8) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation,
            tag: [byte; 32],
        }
    }
    /// A holder's durable record written under `seal`; its tag covers the seal.
    fn record(seal: &TicketSeal) -> std::io::Result<LedgerCheckpoint> {
        let mut xof = Cshake256Xof::new(b"QSAG.TEST.TICKET.RECORD");
        xof.absorb(&seal.generation.to_le_bytes());
        xof.absorb(&seal.reservation);
        xof.absorb(&seal.nonce);
        let mut tag = [0; 32];
        xof.squeeze(&mut tag);
        Ok(LedgerCheckpoint {
            generation: seal.generation,
            tag,
        })
    }

    #[test]
    fn a_ticket_is_consumed_once_and_a_replay_is_rejected() {
        let mem = MemAnchor::default();
        let anchor: &dyn ExternalMonotoneAnchor = &mem;
        let genesis = ckpt(1, 1);
        // An unenrolled anchor issues nothing, and neither does a wrong expectation.
        assert!(anchor.reserve_ticket(genesis, genesis, [7; 32]).is_err());
        assert_eq!(mem.stored(), None);
        anchor.advance(genesis).unwrap();
        assert!(anchor.reserve_ticket(ckpt(1, 2), genesis, [7; 32]).is_err());
        assert_eq!(mem.stored(), Some(genesis));

        let ticket = anchor.reserve_ticket(genesis, genesis, [7; 32]).unwrap();
        assert_eq!((ticket.epoch(), *ticket.context()), (2, [7; 32]));
        assert_eq!(
            mem.stored(),
            Some(LedgerCheckpoint {
                generation: 2,
                tag: ticket.reservation()
            })
        );
        let copy = memory_copy(&ticket);
        let (seal, first) = anchor.consume_ticket(ticket, record).unwrap();
        assert_eq!((seal.generation, first.generation), (3, 3));
        assert_eq!(seal.reservation, copy.reservation());
        assert_eq!(mem.stored(), Some(first));
        // A replayed ticket is refused before anything is committed under it.
        assert!(
            anchor
                .consume_ticket(copy, |_| panic!("a spent ticket reached its commit"))
                .is_err()
        );
        assert_eq!(mem.stored(), Some(first));

        // The spent floor cannot be reserved from again; the settled one can.
        assert!(anchor.reserve_ticket(genesis, genesis, [7; 32]).is_err());
        let next = anchor.reserve_ticket(first, first, [8; 32]).unwrap();
        assert_eq!(next.epoch(), 4);
        let reserved = mem.stored();
        // A record at another generation does not consume the ticket.
        let copy = memory_copy(&next);
        assert!(
            anchor
                .consume_ticket(next, |seal| Ok(ckpt(seal.generation + 1, 9)))
                .is_err()
        );
        assert_eq!(mem.stored(), reserved);
        let (_, second) = anchor.consume_ticket(copy, record).unwrap();
        assert_eq!(second.generation, 5);
    }

    #[test]
    fn two_holders_of_one_ticket_cannot_both_consume_it_even_on_stale_reads() {
        let mem = MemAnchor::default();
        let anchor: &dyn ExternalMonotoneAnchor = &mem;
        let genesis = ckpt(1, 1);
        anchor.advance(genesis).unwrap();
        let ticket = anchor.reserve_ticket(genesis, genesis, [1; 32]).unwrap();
        let copy = memory_copy(&ticket);
        // Both holders read the anchor before either writes.
        mem.freeze_reads();
        let (_, spent) = anchor.consume_ticket(ticket, record).unwrap();
        assert!(anchor.consume_ticket(copy, record).is_err());
        assert_eq!(mem.stored(), Some(spent));
    }

    #[test]
    fn two_contenders_cannot_both_reserve_one_successor_even_on_stale_reads() {
        let mem = MemAnchor::default();
        let anchor: &dyn ExternalMonotoneAnchor = &mem;
        let genesis = ckpt(1, 1);
        anchor.advance(genesis).unwrap();
        mem.freeze_reads();
        let winner = anchor.reserve_ticket(genesis, genesis, [1; 32]).unwrap();
        let issued = mem.stored();
        // Same floor and same context: only the contender identity differs.
        assert!(anchor.reserve_ticket(genesis, genesis, [1; 32]).is_err());
        assert_eq!(mem.stored(), issued);
        mem.thaw_reads();
        anchor.consume_ticket(winner, record).unwrap();
    }

    #[test]
    fn a_ticket_is_refused_by_another_anchor_and_after_a_later_reservation() {
        let (mem_a, mem_b) = (MemAnchor::default(), MemAnchor::default());
        let a: &dyn ExternalMonotoneAnchor = &mem_a;
        let b: &dyn ExternalMonotoneAnchor = &mem_b;
        let genesis = ckpt(1, 1);
        a.advance(genesis).unwrap();
        b.advance(genesis).unwrap();
        let from_a = a.reserve_ticket(genesis, genesis, [3; 32]).unwrap();
        let from_b = b.reserve_ticket(genesis, genesis, [3; 32]).unwrap();
        // Equal epoch, floor and context, issued elsewhere.
        assert!(b.consume_ticket(from_a, record).is_err());
        // Abandoned (for example by a crash), then superseded.
        let abandoned = mem_b.stored().unwrap();
        let later = b.reserve_ticket(abandoned, genesis, [4; 32]).unwrap();
        assert_eq!(later.epoch(), 3);
        assert!(b.consume_ticket(from_b, record).is_err());
        let (_, settled) = b.consume_ticket(later, record).unwrap();
        // A forged ticket for the spent epoch.
        let forged = AnchorTicket {
            epoch: 3,
            owner: [0; 32],
            floor: floor_mark(&genesis),
            context: [4; 32],
        };
        assert!(b.consume_ticket(forged, record).is_err());
        assert_eq!(mem_b.stored(), Some(settled));
    }

    #[test]
    fn reconcile_places_each_crash_state_and_refuses_everything_else() {
        let mem = MemAnchor::default();
        let anchor: &dyn ExternalMonotoneAnchor = &mem;
        let genesis = ckpt(1, 1);
        let unsealed = [0; 32];
        assert_eq!(
            anchor.reconcile(genesis, &unsealed).unwrap(),
            AnchorStanding::Unenrolled
        );
        anchor.advance(genesis).unwrap();
        assert_eq!(
            anchor.reconcile(genesis, &unsealed).unwrap(),
            AnchorStanding::Settled
        );

        // Crash after the reservation, before the durable write.
        let ticket = anchor.reserve_ticket(genesis, genesis, [5; 32]).unwrap();
        let reserved = mem.stored().unwrap();
        assert_eq!(
            anchor.reconcile(genesis, &unsealed).unwrap(),
            AnchorStanding::Reserved(reserved)
        );
        // A reservation pins the checkpoint it was taken from and no other.
        assert!(anchor.reconcile(ckpt(1, 2), &unsealed).is_err());
        assert!(anchor.reconcile(ckpt(0, 1), &unsealed).is_err());
        assert_eq!(mem.stored(), Some(reserved));

        // Crash after the durable write, before the anchor settled on it.
        let seal = TicketSeal {
            generation: 3,
            reservation: ticket.reservation(),
            nonce: [6; 32],
        };
        let successor = record(&seal).unwrap();
        assert!(anchor.reconcile(successor, &unsealed).is_err());
        assert!(anchor.reconcile(successor, &[9; 32]).is_err());
        assert!(anchor.reconcile(ckpt(4, 3), &seal.reservation).is_err());
        assert_eq!(mem.stored(), Some(reserved));
        assert_eq!(
            anchor.reconcile(successor, &seal.reservation).unwrap(),
            AnchorStanding::Settled
        );
        assert_eq!(mem.stored(), Some(successor));

        // Settled on the successor, the anchor no longer admits its predecessor,
        // nor another record at the successor's generation.
        assert!(anchor.reconcile(genesis, &unsealed).is_err());
        assert!(anchor.reconcile(ckpt(3, 3), &seal.reservation).is_err());
        assert_eq!(mem.stored(), Some(successor));
    }
    fn slot_paths(path: &std::path::Path) -> [std::path::PathBuf; 2] {
        layout(path.to_path_buf()).slots
    }
    fn directory() -> std::path::PathBuf {
        static NEXT: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
        let id = NEXT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-ledger-{}-{id}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        dir
    }
    #[test]
    fn crash_boundaries_preserve_burns_and_first_signed_records() {
        use crate::baggy::{
            FirstSignedError, FirstSignedLedger, FirstSignedRecord, FsFirstSignedLedger,
            StaticKeyId,
        };
        use crate::pcg_dense::{FsSeedBurnTracker, SeedBurnError, SeedBurnTracker};
        for boundary in 0..3 {
            let dir = directory();
            let path = dir.join("burn");
            let key = [4; 32];
            let mut ledger = FsSeedBurnTracker::provision_genesis(&path, key).unwrap();
            ledger.burn(&[1; 32]).unwrap();
            let mut anchor = ledger.checkpoint();
            if boundary == 0 {
                // Crash before inactive slot sync: a partial temporary inode is ignored.
                std::fs::write(dir.join("burn.slot_a.tmp"), b"partial").unwrap();
                // Real interrupted replacements create their temporary inode as 0600.
                use std::os::unix::fs::PermissionsExt;
                std::fs::set_permissions(
                    dir.join("burn.slot_a.tmp"),
                    std::fs::Permissions::from_mode(0o600),
                )
                .unwrap();
            } else {
                ledger.burn(&[2; 32]).unwrap();
                if boundary == 2 {
                    anchor = ledger.checkpoint();
                }
            }
            drop(ledger);
            let mut recovered = FsSeedBurnTracker::open_existing(&path, key, anchor).unwrap();
            assert_eq!(
                recovered.checkpoint().generation,
                if boundary == 0 { 1 } else { 2 }
            );
            assert_eq!(recovered.burn(&[1; 32]), Err(SeedBurnError::AlreadyBurned));
            if boundary != 0 {
                assert_eq!(recovered.burn(&[2; 32]), Err(SeedBurnError::AlreadyBurned));
            }
            recovered.burn(&[3; 32]).unwrap();
            drop(recovered);
            let path = dir.join("signed");
            let mut ledger = FsFirstSignedLedger::provision_genesis(&path, key).unwrap();
            let anchor = ledger.checkpoint();
            let id = StaticKeyId {
                identity: [1; 32],
                layer: 0,
                tree: 1,
                key_pair: 2,
            };
            ledger
                .sync_record(&[FirstSignedRecord {
                    key: id,
                    digits: alloc::vec![1, 2, 3],
                }])
                .unwrap();
            drop(ledger);
            let mut recovered = FsFirstSignedLedger::open_existing(&path, key, anchor).unwrap();
            assert_eq!(
                recovered.first_signed(&id).unwrap(),
                Some(alloc::vec![1, 2, 3])
            );
            assert_eq!(
                recovered.sync_record(&[FirstSignedRecord {
                    key: id,
                    digits: alloc::vec![2]
                }]),
                Err(FirstSignedError::Conflict)
            );
            drop(recovered);
            std::fs::remove_dir_all(dir).unwrap();
        }
    }
    #[test]
    fn both_slots_authenticate_and_minimum_anchor_rejects_rollback() {
        let dir = directory();
        let path = dir.join("ledger");
        let key = [4; 32];
        let mut ledger = Ledger::create(&path, key, b"test").unwrap();
        let genesis = ledger.checkpoint();
        assert!(Ledger::open(&path, key, b"test", genesis).is_err());
        let old = std::fs::read(&slot_paths(&path)[0]).unwrap();
        let mut records = Records::new();
        records.insert(alloc::vec![1], alloc::vec![2]);
        ledger.commit(&records).unwrap();
        ledger.commit(&records).unwrap();
        let latest = ledger.checkpoint();
        drop(ledger);
        assert!(Ledger::open(&path, [5; 32], b"test", latest).is_err());
        assert!(Ledger::open(&path, key, b"other", latest).is_err());
        // Slot A is restored to an authenticated old generation; B remains generation 1.
        std::fs::write(&slot_paths(&path)[0], old).unwrap();
        assert!(Ledger::open(&path, key, b"test", latest).is_err());
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.checkpoint().generation, 1);
        drop(recovered);
        // A missing or corrupt inactive snapshot does not strand a valid active one.
        std::fs::remove_file(&slot_paths(&path)[0]).unwrap();
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.read().unwrap(), records);
        drop(recovered);
        let mut missing_lock = slot_paths(&path)[0].as_os_str().to_os_string();
        missing_lock.push(".lock");
        std::fs::write(std::path::PathBuf::from(missing_lock), b"corrupt sidecar").unwrap();
        let recovered = Ledger::open(&path, key, b"test", genesis).unwrap();
        assert_eq!(recovered.read().unwrap(), records);
        drop(recovered);
        std::fs::write(&slot_paths(&path)[1], b"bad").unwrap();
        assert!(Ledger::open(&path, key, b"test", genesis).is_err());
        assert!(Ledger::create(&path, key, b"test").is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }
}
