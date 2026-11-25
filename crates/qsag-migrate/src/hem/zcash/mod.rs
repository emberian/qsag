//! Zcash: ownership statements for the transparent pool, for Orchard addresses and for
//! quantum-recoverable shielded notes, with the native protocol layer they need.
//!
//! # What is implemented, against which protocol
//!
//! * Zcash protocol specification **v2026.9.0 \[NU7\]** (NU6.3 active on mainnet from
//!   height 3,428,143, 28 July 2026; NU7 from 3,543,405, 6 November 2026).
//! * **ZIP 2005 "Ironwood Quantum Recoverability"** (status Final; activation with
//!   NU6.3 by ZIP 258; the Ironwood pool and its note commitment tree and nullifier set
//!   are ZIP 229). Its "Proposed Recovery Statement" is the relation of
//!   [`recovery::RecoveryStatement`].
//! * ZIP 32 (Orchard hardened-only derivation, Sapling derivation, BIP 44 transparent
//!   paths), ZIP 316 Revision 0 (unified addresses and viewing keys, F4Jumble), ZIP 224
//!   (the Orchard protocol: keys, Sinsemilla, Poseidon, note commitments, nullifiers).
//! * ZIP 244 (transaction digests) is **not** implemented: a statement here is not a
//!   Zcash transaction, and the message its spend authorization signature covers is this
//!   crate's statement encoding ([`recovery::RecoveryStatement::sighash`]).
//!
//! Normative references: `[Zcash-NU7]` (Zcash Protocol Specification v2026.9.0),
//! `[ZIP-2005]` (Ironwood Quantum Recoverability), `[ZIP-229]` (v6 Transaction Format),
//! `[ZIP-258]` (NU6.3 Deployment), `[ZIP-32]` (Shielded Hierarchical Deterministic Wallets),
//! `[ZIP-316]` (Unified Addresses and Viewing Keys), `[ZIP-224]` (Orchard Shielded Protocol),
//! and `[ZIP-2007]` (Transparent Quantum Recoverability).
//!
//! # Which funds can be migrated with a post-quantum proof, and which cannot
//!
//! The question for each pool is whether what is on chain binds the funds to a secret
//! through hash functions alone. A quantum adversary computes discrete logarithms, so a
//! public point reveals its scalar and a Pedersen or Sinsemilla commitment can be
//! reopened.
//!
//! | funds | statement | sound against a discrete-logarithm adversary |
//! |---|---|---|
//! | transparent P2PKH, key never revealed | [`transparent`], hidden key | yes: `HASH160` hides the key |
//! | transparent P2PKH from a BIP 32 seed | [`transparent`], seed provenance | yes: the witness is a hash preimage |
//! | Ironwood-pool note (lead byte `0x03`, created from NU6.3 on) | [`recovery::RecoveryStatement`] | yes, by the argument of ZIP 2005 (below) |
//! | Orchard address `d \|\| pk_d` | [`recovery::AddressStatement`] | yes for ownership of the address; it carries no funds |
//! | Sapling address `d \|\| pk_d` | [`sapling_address::SaplingAddressStatement`] | yes for ownership of the address (hash-bound `ivk = BLAKE2s(ak, nk)` over Jubjub); it carries no funds |
//! | Orchard-pool note (lead byte `0x02`) | none | no |
//! | Sapling note | none | no |
//! | Sprout note | none | not addressed here |
//! | transparent P2SH | none | not built (see [`transparent`]) |
//!
//! ## Ironwood notes
//!
//! ZIP 2005 changed one derivation: for a note with lead byte `0x03` the commitment
//! randomness is `rcm = H^rcm_rseed(g_d*, pk_d*, v, rho, psi)`, a BLAKE2b hash of every
//! note field, where before it was a hash of `rseed` and `rho` only. Nothing else in the
//! Orchard protocol moved; in particular every Orchard key is already derived from the
//! spending key `sk` through BLAKE2b (`H^ask`, `H^nk`, `H^rivk`). The Recovery Statement
//! re-derives everything from `sk` (or, for FROST and hardware wallet keys, from the
//! quantum spending key `qsk`) and checks the two Sinsemilla commitments as deterministic
//! functions:
//!
//! * `NoteCommit` is `[rcm + f(note)] R` for some function `f` of the note fields. With
//!   `rcm` a random oracle output on the same fields, a second opening of a commitment is
//!   a collision of that oracle up to sign: ZIP 2005, "Security argument for
//!   Spendability", bound `q^2 / r_P` classically and `O(q^3 / r_P)` in the QROM.
//! * `Commit^ivk` is `[rivk + h(ak, nk)] S`, and `rivk` is a hash of `sk` (or of
//!   `(qk, ak, nk)`), so an incoming viewing key has one key tuple behind it: ZIP 2005,
//!   "Security argument for key binding", same bounds.
//! * The Merkle path is opened in a tree rebuilt over the same leaves with a collapsing
//!   hash, because `MerkleCRH^Orchard` is Sinsemilla ([`rehash`]).
//!
//! Those are the ZIP's theorems, proved there in the classical random oracle model with
//! a stated lift to the QROM; this crate proves nothing about them and adds the
//! assumptions of its own instantiation: BLAKE2s collapsing for the rebuilt tree and the
//! soundness of zk-Hem under the chosen regime.
//!
//! Zcash has not deployed a Recovery Protocol. ZIP 2005 describes the statement "in
//! outline but not in detail" and leaves the proof system and the tree hash open. The
//! statement here follows the ZIP's text condition by condition; where the ZIP is open,
//! the choices are this crate's and are listed under "Differences" below.
//!
//! ## Orchard-pool and Sapling notes
//!
//! ZIP 2005: "Recovery would not be possible for funds still in the Sprout, Sapling, or
//! Orchard pools; all such funds would be inaccessible after their respective protocols
//! are disabled. They should be migrated to the Ironwood pool". The reason is in the
//! commitment, and no proof system repairs it:
//!
//! * An Orchard-pool note has `rcm = ToScalar(PRF^expand_rseed([5] || rho))` and a
//!   Sapling note `rcm = ToScalar(PRF^expand_rseed([4]))`: the randomness does not depend
//!   on the address or the value. A Sapling note from before Canopy (lead byte `0x01`)
//!   carries `rcm` itself.
//! * With the discrete logarithms between the generators known, the commitment is
//!   `[rcm + f(note)] R` with `f` a known linear function of the message bits. For a
//!   pre-Canopy note any other note opens the same commitment with
//!   `rcm' = rcm + f(note) - f(note')`. With `rcm` hashed from `rseed`, a second opening
//!   needs `H(rseed') + f(note') = H(rseed) + f(note)`, where the two sides are sums of
//!   terms the adversary chooses independently (the address, the value, `rseed`). That is
//!   a generalized birthday problem, not a preimage problem; our estimate with Wagner's
//!   k-list algorithm on the four unbounded lists is about `2^84` operations, against
//!   `2^126` for the recoverable derivation, where one oracle call covers all fields.
//!   (This estimate is ours; the ZIP states only that these commitments are not
//!   post-quantum binding.)
//! * A break of binding is a break of Balance: the adversary creates a small note and
//!   recovers a large one from the same commitment.
//!
//! So a "recovery" proof for such a note would verify and mean less than it says. None
//! is built, and the relation of [`recovery`] rejects such a note: it computes `rcm` from
//! the note fields, so a lead byte `0x02` commitment does not open
//! (`relation_of_a_note_rejects_what_the_statement_excludes`). The path for these funds is
//! the one Zcash prescribes: spend them into the Ironwood pool while the Orchard and
//! Sapling protocols are still enabled, then recover the Ironwood note.
//!
//! For Sapling the key hierarchy itself is hash-bound (`ivk = BLAKE2s(ak, nk)`), so
//! ownership of a Sapling *address* is proved soundly in [`sapling_address::SaplingAddressStatement`]
//! in the same way [`recovery::AddressStatement`] does for Orchard, with complete Jubjub
//! arithmetic over the BLS12-381 scalar field in the relation and [`sapling`] as the native
//! derivation layer.
//!
//! # The statements
//!
//! | statement | public | secret |
//! |---|---|---|
//! | [`recovery::RecoveryStatement`] | anchor of the rehashed Ironwood tree, nullifier, `rk`, value, key source | `sk` or ZIP 32 seed or `qsk`; scope; `alpha`; the note; position and path |
//! | [`recovery::AddressStatement`] | Orchard address, key source | `sk` or ZIP 32 seed or `qsk`; scope |
//! | [`sapling_address::SaplingAddressStatement`] | Sapling address `d \|\| pk_d`, key source | Sapling `sk` or ZIP 32 seed |
//! | [`transparent::TransparentStatement`] | network, P2PKH payload (and for seed provenance the public key and BIP 44 path) | secp256k1 key, or BIP 32 seed |
//!
//! Every statement also carries the post-quantum address commitment, the migration
//! domain and the epoch, bound through the proof transcript, and gives the registry a
//! binding: the nullifier of a note is its Zcash nullifier, so a note is bound once
//! whatever the domain; an address or a transparent key is bound once per domain.
//!
//! # What a verifier must check beside the proof
//!
//! A proof says "this statement has a witness". For a note, that is: a note of value `v`
//! with nullifier `nf` and a key the prover holds sits under `anchor`. Before crediting
//! `v` to the post-quantum destination, the chain or registry that accepts it must:
//!
//! 1. **Anchor**: check that `anchor` is a root of the rehashed Ironwood tree it
//!    maintains from the chain ([`rehash::Frontier`] over `leaf(cmx, nullifier)` of every
//!    Ironwood Action in block order), at a height it accepts. A proof against an anchor
//!    of the prover's making proves nothing.
//! 2. **Nullifier**: check that `nf` is not in the Ironwood nullifier set of the chain and
//!    has not been recovered before, and record it. The registry does the second part
//!    ([`recovery::RecoveryStatement::binding`]); the first needs the chain.
//! 3. **Value**: account `v` itself (the statement reveals it; there is no value
//!    commitment), and keep the Ironwood pool balance non-negative (ZIP 209).
//! 4. **Signature and regime**: [`recovery::verify_recovery`] checks the spend
//!    authorization signature under `rk` and the regime; the caller chooses the regime,
//!    the migration domain and the epochs it accepts.
//! 5. **Timing**: until the Orchard protocol is disabled on chain, an Ironwood note can
//!    still be spent the ordinary way (and a quantum adversary can forge such spends), so
//!    a recovery is final only against a chain state in which ordinary spends of the
//!    pool are closed. That is a deployment decision of Zcash; this crate cannot make it.
//!
//! For an address statement there is nothing on chain to check: it shows that the prover
//! controls the keys of an address and nothing about funds. For a transparent statement
//! the verifier checks the unspent outputs of the address and that it has not been spent
//! from (hidden key).
//!
//! # Differences from what Zcash would deploy
//!
//! * **Proof system.** zk-Hem (sumcheck and WHIR over Goldilocks, hash-based) with
//!   Pallas arithmetic emulated in a 64-bit field. Zcash has not chosen one. The relation
//!   has 2.5 to 2.8 million rows for that reason.
//! * **Tree hash.** [`rehash`]: BLAKE2s-256 with this crate's personalization. The ZIP
//!   leaves it open; any deployment by Zcash will fix its own, and an anchor of ours is
//!   not an anchor of theirs.
//! * **Key source is public.** The ZIP hides whether the `sk` or the `qk` branch is used
//!   (one circuit, multiplexed). Here the branch selects the relation and is part of the
//!   statement, as is the ZIP 32 account when the witness is a seed.
//! * **`SoK^sk` and `SoK^qsk` are inlined.** The ZIP allows the knowledge of `sk` or
//!   `qsk` to be proved by a separate signature of knowledge linked by a commitment (for
//!   hardware wallets). Here it is part of the one relation.
//! * **Value is public** and there is no output note: the destination is a post-quantum
//!   address of this project, bound through the transcript. The ZIP's primary input is
//!   `(rt, rk, nf, SigHash)`.
//! * **Exceptional additions.** Where the ZIP asks for complete additions, the relation
//!   makes the exceptional case unsatisfiable instead ([`ecc`]). For Sinsemilla that is
//!   the specified `⊥`. Elsewhere it excludes witnesses in which a commitment or scalar
//!   multiplication meets `P = ±Q` or the identity, which for an honest note happens with
//!   probability about `2^-250`; it cannot admit a false statement.
//! * **`rk` uses the unnormalized key.** As the ZIP's `BindKeys^sk` is written,
//!   `ak^P = [H^ask(sk)] G`, without the sign normalization wallets apply to `ask`; the
//!   prover signs with `H^ask(sk) + alpha`.
//!
//! # Relation dimensions
//!
//! All Zcash recovery statements target `zk_hem::v2::params::Profile::TurboShakeJohnson400`
//! (wire tag `17`, `QSAGZKH2`, Quintic `Fp5`, `[DKT26]` / `[CWYZ26]` `< 2^{-128}` QROM).
//! Reproduce live synthesis, prove, and cold/warm verification timings on the target host via
//! `cargo test --release -p qsag-migrate --features std --lib -- hem::zcash::recovery::tests::measure --ignored --nocapture --test-threads 1`:
//!
//! | Statement | Key source | Rows | Padded rows | Variables | Public inputs | Table cells |
//! | --- | --- | ---: | ---: | ---: | ---: | ---: |
//! | `orchard-address` | `SpendingKey` | `1,045,419` | `2^20` | `1,028,162` | `766` | `2^21` |
//! | `orchard-address` | `Zip32Seed` (`32 B`, coin `133`, acct `0`) | `1,244,645` | `2^21` | `1,224,334` | `766` | `2^22` |
//! | `orchard-address` | `QuantumSpendingKey` | `921,722` | `2^20` | `906,229` | `766` | `2^21` |
//! | `ironwood-note` | `SpendingKey` | `2,593,512` | `2^22` | `2,551,000` | `831` | `2^23` |
//! | `ironwood-note` | `Zip32Seed` (`32 B`, coin `133`, acct `0`) | `2,792,738` | `2^22` | `2,747,172` | `831` | `2^23` |
//! | `ironwood-note` | `QuantumSpendingKey` | `2,469,801` | `2^22` | `2,429,053` | `831` | `2^23` |
//! | `transparent-p2pkh` | `m/44'/133'/0'/0/3` | — | `2^21` | `1,091,619` | — | `2^22` |
//!
//! Cold verification includes building the relation once per key source; process high-water
//! RSS accumulates across statements in the measurement harness.
//! Rows of the note relation by part (spending-key source), approximately: seven
//! BLAKE2b compressions 357,000; the 33 BLAKE2s compressions of the leaf and path
//! 700,000; `[ivk] g_d` 611,000; the two Sinsemilla commitments (160 chunks) 470,000;
//! Poseidon 236,000; five fixed-base multiplications 214,000. The address relation with
//! a spending key is 1,045,419 rows, 0.3 % under `2^20`: a gadget that grows by a few
//! thousand rows doubles its table.
//!
//! # Modules
//!
//! * Native protocol layer, checked against the Zcash test vectors and (in
//!   `validation/zcash`) against the `orchard` 0.16.0 and `zcash_address` 0.14 crates:
//!   [`blake2`], [`blake3`], [`pallas`], [`sinsemilla`], [`poseidon`], [`ff1`],
//!   [`orchard`], [`sapling`], [`encoding`], [`rehash`].
//! * Relation layer: [`nonnative`] (arithmetic modulo the Pallas primes), [`ecc`] (curve,
//!   Sinsemilla and Poseidon gadgets), and the gadget halves of [`blake2`], [`blake3`]
//!   and [`rehash`].
//! * Statements: [`recovery`], [`transparent`].
//!
//! What could be shared with the rest of `hem`: the BLAKE2 gadgets belong beside the
//! other hash gadgets of [`super::hash`]; [`nonnative`] and [`super::curve`] implement
//! the same limb technique and could be one module if the polynomial type of
//! [`super::curve`] were exported with unreduced products.

pub mod blake2;
pub mod blake3;
pub mod ecc;
pub mod encoding;
pub mod ff1;
pub mod nonnative;
pub mod orchard;
pub mod pallas;
pub mod poseidon;
pub mod recovery;
pub mod rehash;
pub mod sapling;
pub mod sapling_address;
pub mod sinsemilla;
pub mod transparent;
#[cfg(test)]
mod vectors;
