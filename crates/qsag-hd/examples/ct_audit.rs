//! Retain inventory derivation and subset-seed provisioning in the linked audit image.
use core::hint::black_box;
use qsag_hd::{SeedCeremonyRound1, derive_inventory_vault, inventory_child_public_key};

fn main() {
    black_box(qsag_core::preprocessing::PartyPrivateRng::fill_bytes as fn(_, _));
    black_box(derive_inventory_vault as fn(_, _, _) -> _);
    black_box(SeedCeremonyRound1::begin as fn(_, _, _) -> _);
    black_box(inventory_child_public_key as fn(_) -> _);
}
