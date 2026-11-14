#![cfg_attr(not(test), deny(clippy::unwrap_used, clippy::expect_used))]
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![forbid(unsafe_code)]
//! Generalized `(t, n)` quorum-switching `Jorts` signatures and isolated single-party
//! protocol nodes that talk over a framed wire transport.
//!
//! * [`quorum_jorts`] — the full 256-bit `WOTS+C` leaf scheme, the committee-partitioned
//!   `t`-of-`t` mode (QS-A) and the certified `(t, n)` Shamir mode (QS-B).
//! * [`wire_channel`] — the [`wire_channel::WireTransport`] trait, the canonical frame
//!   format and, with `std`, a thread-channel mesh and a loopback socket mesh.
//! * [`party_node`] — one party per value: QS-A and QS-B custodians over the wire, and a
//!   three-party replicated `Keccak-f[1600]` engine with a coin-flip barrier.
//! * [`dzk`] — the `GF(2^128)` polynomial check the barrier runs on the AND gates.
//!
//! The crate is `no_std` with `alloc`; only the transport meshes need `std`.

extern crate alloc;

pub mod dzk;
pub mod hash;
pub mod party_node;
pub mod quorum_jorts;
pub mod wire_channel;

#[cfg(feature = "std")]
pub mod poison_journal;

pub use wire_channel::{ConfidentialWireChannel, MacSealedWireChannel};
