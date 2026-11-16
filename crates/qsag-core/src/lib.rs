//! `qsag-core` — Zero-dependency `#![no_std]` post-quantum threshold hash-based
//! signature library implementing NIST FIPS 205 `SLH-DSA-SHAKE` (`128s`, `128f`,
//! `192s`, `192f`, `256s`, `256f`) and the pure-hash threshold suite:
//!
//! * [`baggy`] — stateless `WOTS+C` hypertree signatures over [`pors_fp`] (`PORS+FP`), on the
//!   2-of-3 256-lane replicated engine ([`rss256`]) or the `t`-of-`n` engine
//!   ([`spdz_sweep`]), with the `Waistband` top-layer cache;
//! * [`jorts`] — stateful single-tree 2-of-3 signatures gated by the durable
//!   [`belt_latch`];
//! * [`corduroy`] — the algebraic Poseidon2 hypertree custody scheme;
//!
//! together with dishonest-majority dealerless preprocessing, dynamic quorum
//! redistribution (`Π_reshare`), and identifiable abort.

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

pub mod wipe;

#[forbid(unsafe_code)]
pub mod field;

#[forbid(unsafe_code)]
pub mod sponge;

#[forbid(unsafe_code)]
pub mod fips205;

#[forbid(unsafe_code)]
pub mod tsw_baggy;

#[forbid(unsafe_code)]
pub mod preprocessing;

#[forbid(unsafe_code)]
pub mod pcg_dense;

#[forbid(unsafe_code)]
pub mod dkg;

#[forbid(unsafe_code)]
pub mod keccak_mpc;

#[forbid(unsafe_code)]
pub mod poseidon2_mpc;

#[forbid(unsafe_code)]
pub mod rss256;

#[forbid(unsafe_code)]
pub mod cnf_rss;

#[forbid(unsafe_code)]
pub mod belt_latch;

#[forbid(unsafe_code)]
pub mod wots_c;

#[forbid(unsafe_code)]
pub mod pors_fp;

#[forbid(unsafe_code)]
pub mod baggy;

#[forbid(unsafe_code)]
pub mod spdz_sweep;

#[forbid(unsafe_code)]
pub mod jorts;

#[forbid(unsafe_code)]
pub mod corduroy;

#[cfg(feature = "std")]
mod durable_ledger;
#[cfg(feature = "std")]
pub use durable_ledger::{
    AnchorStanding, AnchorTicket, ExternalMonotoneAnchor, LedgerCheckpoint, TicketSeal,
};
#[cfg(feature = "std")]
#[forbid(unsafe_code)]
mod two_slot_record;
#[cfg(feature = "std")]
pub use two_slot_record::{TwoSlotPaths, TwoSlotRecord};

/// Hardware (`TPM 2.0` NV counter) and hypervisor (`ACPI VMGENID` / `boot_id` / inode)
/// anti-rollback and fork-detection anchors.
#[cfg(feature = "std")]
#[forbid(unsafe_code)]
pub mod anti_rollback;

/// Atomic per-key ceremony resource journal.
#[cfg(feature = "std")]
pub mod ceremony_journal;
