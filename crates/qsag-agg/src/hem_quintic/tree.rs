//! Public Canopy leaves contain only the symbols on one RS fiber.
use super::*;
use crate::sponge::{
    poseidon2_gl24_compress_merkle, poseidon2_gl24_hash56, turboshake256_from_midstate_into,
    turboshake256_static_midstate,
};
use crate::zk_hem::v2::hash::CanopyHash;

const TREE: &[u8] = b"QSAG.HEM.QUINTIC.TREE/v2";
const TURBO: [u64; 25] = turboshake256_static_midstate(TREE);
const GL_DOMAIN: u64 = u64::from_le_bytes(*b"HQM2TREE");

pub(super) trait Hash<const N: usize>: CanopyHash<N> {
    fn hash(self, input: &[u8]) -> [u8; N];
    fn canonical(digest: &[u8; N]) -> bool;
    fn leaf(self, stage: usize, index: usize, symbols: &[u8]) -> [u8; N] {
        let mut frame = Vec::with_capacity(6 + symbols.len());
        frame.extend_from_slice(&[0, stage as u8]);
        frame.extend_from_slice(&(index as u32).to_le_bytes());
        frame.extend_from_slice(symbols);
        self.hash(&frame)
    }
}

#[derive(Clone, Copy)]
pub(super) struct Turbo;

impl Hash<50> for Turbo {
    fn hash(self, input: &[u8]) -> [u8; 50] {
        let mut out = [0; 50];
        turboshake256_from_midstate_into(&TURBO, input, &mut out);
        out
    }
    fn canonical(_: &[u8; 50]) -> bool {
        true
    }
}

impl CanopyHash<50> for Turbo {
    fn node(self, index: u32, left: &[u8; 50], right: &[u8; 50]) -> [u8; 50] {
        let mut buf = [0; 105];
        buf[0] = 1;
        buf[1..5].copy_from_slice(&index.to_le_bytes());
        buf[5..55].copy_from_slice(left);
        buf[55..].copy_from_slice(right);
        self.hash(&buf)
    }
    fn root(self, stage: u8, depth: u8, top: &[u8; 50]) -> [u8; 50] {
        self.hash(&[&[2, stage, depth][..], top].concat())
    }
    fn pair_order(self, u: u64, hu: [u8; 50], hs: [u8; 50]) -> Option<([u8; 50], [u8; 50])> {
        qsag_whir_verified::step_merkle_pair_order_400(u, 0, hu, hs).map(|p| (p.left, p.right))
    }
}

#[derive(Clone, Copy)]
pub(super) struct Gl24;

fn encode_gl24_digest(d: qsag_whir_verified::Gl24Digest) -> [u8; 56] {
    let limbs = [d.l0, d.l1, d.l2, d.l3, d.l4, d.l5, d.l6];
    let mut bytes = [0u8; 56];
    for (dst, limb) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(limbs) {
        *dst = limb.to_le_bytes();
    }
    bytes
}

impl Hash<56> for Gl24 {
    fn hash(self, input: &[u8]) -> [u8; 56] {
        poseidon2_gl24_hash56(GL_DOMAIN, &[TREE, input].concat())
    }
    fn canonical(digest: &[u8; 56]) -> bool {
        qsag_whir_verified::decode_canonical_gl24_digest(digest).is_some()
    }
}

impl CanopyHash<56> for Gl24 {
    fn node(self, index: u32, left: &[u8; 56], right: &[u8; 56]) -> [u8; 56] {
        let limbs = |d: &[u8; 56]| {
            core::array::from_fn(|i| {
                F::from_u64_reduced(u64::from_le_bytes(d.as_chunks::<8>().0[i]))
            })
        };
        let out = poseidon2_gl24_compress_merkle(
            &limbs(left),
            &limbs(right),
            &[
                F::from_u64_reduced(GL_DOMAIN),
                F::from_u64_reduced(index.into()),
            ],
        );
        encode_gl24_digest(qsag_whir_verified::Gl24Digest {
            l0: out[0].to_canonical_u64(),
            l1: out[1].to_canonical_u64(),
            l2: out[2].to_canonical_u64(),
            l3: out[3].to_canonical_u64(),
            l4: out[4].to_canonical_u64(),
            l5: out[5].to_canonical_u64(),
            l6: out[6].to_canonical_u64(),
        })
    }
    fn root(self, stage: u8, depth: u8, top: &[u8; 56]) -> [u8; 56] {
        self.hash(&[&[2, stage, depth][..], top].concat())
    }
    fn pair_order(self, u: u64, hu: [u8; 56], hs: [u8; 56]) -> Option<([u8; 56], [u8; 56])> {
        let hu_limbs = qsag_whir_verified::decode_canonical_gl24_digest(&hu)?;
        let hs_limbs = qsag_whir_verified::decode_canonical_gl24_digest(&hs)?;
        let ordered = qsag_whir_verified::step_merkle_pair_order_gl24(u, 0, hu_limbs, hs_limbs)?;
        Some((
            encode_gl24_digest(ordered.left),
            encode_gl24_digest(ordered.right),
        ))
    }
}
