//! Public Canopy leaves contain only the symbols on one RS fiber.
use super::*;
use crate::field::GoldilocksOps as _;
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
}

#[derive(Clone, Copy)]
pub(super) struct Gl24;

impl Hash<56> for Gl24 {
    fn hash(self, input: &[u8]) -> [u8; 56] {
        poseidon2_gl24_hash56(GL_DOMAIN, &[TREE, input].concat())
    }
    fn canonical(digest: &[u8; 56]) -> bool {
        digest
            .as_chunks::<8>()
            .0
            .iter()
            .all(|b| F::from_canonical_u64(u64::from_le_bytes(*b)).is_some())
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
        let mut bytes = [0; 56];
        for (dst, limb) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(out) {
            *dst = limb.to_le_bytes();
        }
        bytes
    }
    fn root(self, stage: u8, depth: u8, top: &[u8; 56]) -> [u8; 56] {
        self.hash(&[&[2, stage, depth][..], top].concat())
    }
}
