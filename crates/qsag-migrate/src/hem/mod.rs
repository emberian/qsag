//! Ownership relations over the zk-Hem constraint system (`qsag_agg::zk_hem`).
//!
//! * [`hash`]: SHA-256, SHA-512, HMAC, RIPEMD-160 and Keccak-256 gadgets.
//! * [`curve`]: non-native secp256k1 and Ed25519 fixed-base scalar multiplication.
//! * [`collab`]: proving over a secret-shared witness.
//! * [`registry`] (`std`): the durable one-way nullifier registry.
//! * [`relations`]: the ownership statements and their proofs.

pub mod collab;
pub mod curve;
pub mod hash;
#[cfg(feature = "std")]
pub mod registry;
pub mod relations;
pub mod zcash;
