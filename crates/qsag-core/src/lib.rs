//! `qsag-core` — Zero-dependency `#![no_std]` post-quantum threshold hash-based
//! signature library implementing NIST FIPS 205 `SLH-DSA-SHAKE` (`128s`, `128f`,
//! `192s`, `192f`, `256s`, `256f`) and the pure-hash threshold suite:
//!
//! * [`baggy`] — stateless 2-of-3 `WOTS+C` / `FORS+C` hypertree signatures on the 256-lane
//!   replicated engine ([`rss256`]), with the `Waistband` top-layer cache;
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
pub mod belt_latch;

#[forbid(unsafe_code)]
pub mod wots_c;

#[forbid(unsafe_code)]
pub mod baggy;

#[forbid(unsafe_code)]
pub mod jorts;

#[forbid(unsafe_code)]
pub mod corduroy;

#[cfg(feature = "std")]
mod durable_ledger;
#[cfg(feature = "std")]
pub use durable_ledger::{ExternalMonotoneAnchor, LedgerCheckpoint};

/// Atomic per-key ceremony resource journal.
#[cfg(feature = "std")]
pub mod ceremony_journal;
