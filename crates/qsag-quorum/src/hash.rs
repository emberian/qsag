//! `SHAKE256` helpers shared by the quorum protocols: injectively framed hashing, a
//! prefix-keyed MAC, an output expander and a seeded generator for a party's private coins.

use qsag_core::sponge::keccak::Cshake256Xof;
use qsag_core::wipe::ct_eq_bytes32;

fn absorb_framed(xof: &mut Cshake256Xof, part: &[u8]) {
    xof.absorb(&(part.len() as u64).to_be_bytes());
    xof.absorb(part);
}

fn framed_xof(domain: &[u8], parts: &[&[u8]]) -> Cshake256Xof {
    let mut xof = Cshake256Xof::new_shake256();
    absorb_framed(&mut xof, domain);
    for part in parts {
        absorb_framed(&mut xof, part);
    }
    xof
}

/// `SHAKE256` of the length-framed `domain` and `parts`, truncated to 32 bytes. Every field
/// carries its length, so distinct field lists never produce the same sponge input.
pub fn h32(domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut out = [0u8; 32];
    framed_xof(domain, parts).squeeze(&mut out);
    out
}

/// `out.len()` bytes of `SHAKE256` output over the length-framed `domain` and `parts`.
pub fn expand(domain: &[u8], parts: &[&[u8]], out: &mut [u8]) {
    framed_xof(domain, parts).squeeze(out);
}

/// Prefix-keyed sponge MAC: `SHAKE256(domain || key || parts)` with length framing.
pub fn mac32(key: &[u8; 32], domain: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut xof = Cshake256Xof::new_shake256();
    absorb_framed(&mut xof, domain);
    absorb_framed(&mut xof, key);
    for part in parts {
        absorb_framed(&mut xof, part);
    }
    let mut out = [0u8; 32];
    xof.squeeze(&mut out);
    out
}

/// Constant-time check of a [`mac32`] tag.
pub fn mac32_verify(key: &[u8; 32], domain: &[u8], parts: &[&[u8]], tag: &[u8; 32]) -> bool {
    ct_eq_bytes32(&mac32(key, domain, parts), tag)
}

/// Counter-mode `SHAKE256` generator for one party's private randomness. The seed is the
/// party's own entropy; nothing here is shared between parties.
pub struct SeedRng {
    key: [u8; 32],
    counter: u64,
}

impl Drop for SeedRng {
    fn drop(&mut self) {
        qsag_core::wipe::wipe_bytes32(&mut self.key);
    }
}

impl SeedRng {
    pub fn new(seed: &[u8; 32], label: &[u8]) -> Self {
        Self {
            key: h32(b"QSAG.QUORUM.RNG.KEY/v1", &[seed, label]),
            counter: 0,
        }
    }

    pub fn fill(&mut self, out: &mut [u8]) {
        expand(
            b"QSAG.QUORUM.RNG.BLOCK/v1",
            &[&self.key, &self.counter.to_be_bytes()],
            out,
        );
        self.counter += 1;
    }

    pub fn bytes32(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        self.fill(&mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framing_separates_field_boundaries_and_domains() {
        assert_ne!(h32(b"d", &[b"ab", b"c"]), h32(b"d", &[b"a", b"bc"]));
        assert_ne!(h32(b"d", &[b"abc"]), h32(b"d", &[b"abc", b""]));
        assert_ne!(h32(b"d1", &[b"abc"]), h32(b"d2", &[b"abc"]));
        assert_eq!(
            h32(b"d", &[b"abc"]).to_vec(),
            qsag_core::sponge::keccak::shake256_xof(
                32,
                &[
                    &1u64.to_be_bytes()[..],
                    b"d",
                    &3u64.to_be_bytes()[..],
                    b"abc"
                ]
                .concat()
            )
        );
    }

    #[test]
    fn mac_depends_on_key_and_message_and_rng_streams_are_distinct() {
        let k1 = [1u8; 32];
        let k2 = [2u8; 32];
        let tag = mac32(&k1, b"m", &[b"x"]);
        assert!(mac32_verify(&k1, b"m", &[b"x"], &tag));
        assert!(!mac32_verify(&k2, b"m", &[b"x"], &tag));
        assert!(!mac32_verify(&k1, b"m", &[b"y"], &tag));
        let mut a = SeedRng::new(&k1, b"a");
        let mut b = SeedRng::new(&k1, b"b");
        let first = a.bytes32();
        assert_ne!(first, a.bytes32());
        assert_ne!(first, b.bytes32());
    }
}
