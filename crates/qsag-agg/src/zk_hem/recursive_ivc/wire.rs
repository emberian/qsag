//! No witness-controlled lengths. Every word has exactly one representation.
use super::*;
const MAGIC: &[u8; 8] = b"QSAGIW24";
impl FixedPathWhirW24 {
    fn visit_mut(&mut self, mut visit: impl FnMut(&mut F) -> Option<()>) -> Option<()> {
        for stage in &mut self.stages {
            for x in &mut stage.root {
                visit(x)?;
            }
            for e in stage.ood.iter_mut().chain(stage.folds.iter_mut().flatten()) {
                for x in &mut e.0 {
                    visit(x)?;
                }
            }
            for x in stage
                .fibers
                .iter_mut()
                .flatten()
                .chain(stage.siblings.iter_mut().flatten())
            {
                visit(x)?;
            }
        }
        for x in self
            .mask_claim
            .0
            .iter_mut()
            .chain(self.final_coeffs.iter_mut().flat_map(|e| &mut e.0))
        {
            visit(x)?;
        }
        Some(())
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        for s in &self.stages {
            for x in s
                .root
                .iter()
                .chain(
                    s.ood
                        .iter()
                        .chain(s.folds.iter().flatten())
                        .flat_map(|e| &e.0),
                )
                .chain(s.fibers.iter().flatten())
                .chain(s.siblings.iter().flatten())
            {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        for x in self
            .mask_claim
            .0
            .iter()
            .chain(self.final_coeffs.iter().flat_map(|e| &e.0))
        {
            out.extend_from_slice(&x.to_le_bytes());
        }
        out
    }
    pub fn from_bytes_canonical(cfg: &IvcStepConfig, bytes: &[u8]) -> Option<Self> {
        if bytes.len() != cfg.opening_bytes() || !bytes.starts_with(MAGIC) {
            return None;
        }
        let (chunks, rem) = bytes[8..].as_chunks::<8>();
        if !rem.is_empty() {
            return None;
        }
        let mut words = chunks.iter();
        let mut out = Self::blank(cfg);
        out.visit_mut(|x| {
            let raw = u64::from_le_bytes(*words.next()?);
            if raw >= crate::field::GOLDILOCKS_PRIME {
                return None;
            }
            *x = f(raw);
            Some(())
        })?;
        words.next().is_none().then_some(out)
    }
}
impl IvcStepConfig {
    pub fn opening_bytes(&self) -> usize {
        let mut words = 5 * (1 + (1 << self.schedule.early_stop_vars) + 2);
        for (i, d) in self.dims().iter().enumerate() {
            words += 7
                + 5 * (if i == 0 { 5 } else { 2 })
                + 25 * d.step_vars
                + d.queries * fiber_len(i, d)
                + 7 * octopus::frontier_len(d.fibers, d.queries);
        }
        8 + 8 * words
    }
}

const TREE_MAGIC: &[u8; 8] = b"QSAGIVC1";
const PRODUCTION_TAG: u8 = 0;

fn argument_header_bytes(log_cells: usize) -> usize {
    let accumulator_words = 5 * (2 * log_cells + 4);
    let nonce_and_root_words = 11;
    let sumcheck_words = 5 * (13 * log_cells + 5);
    9 + 8 * (accumulator_words + nonce_and_root_words + sumcheck_words)
}

impl SuccinctIvcProof {
    /// Exact byte length of the canonical `[DKT26]` `< 2^{-128}` QROM proof (`639,673` bytes).
    pub fn encoded_len() -> usize {
        let cfg = tree::profile();
        argument_header_bytes(cfg.log_cells) + cfg.opening_bytes()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        self.encode_with_tag(PRODUCTION_TAG)
    }

    pub fn from_bytes_canonical(bytes: &[u8]) -> Option<Self> {
        Self::decode_with_cfg(&tree::profile(), PRODUCTION_TAG, bytes)
    }

    fn encode_with_tag(&self, tag: u8) -> Vec<u8> {
        let p = &self.0;
        let mut out = TREE_MAGIC.to_vec();
        out.push(tag);
        for x in p
            .acc
            .point
            .iter()
            .chain(core::iter::once(&p.acc.value))
            .flat_map(|e| &e.0)
            .chain(&p.nonce)
            .chain(&p.root)
            .chain(
                p.row
                    .iter()
                    .flatten()
                    .chain(&p.abc)
                    .chain(p.col.iter().flatten())
                    .chain([&p.matrix, &p.z])
                    .flat_map(|e| &e.0),
            )
        {
            out.extend_from_slice(&x.to_le_bytes());
        }
        out.extend_from_slice(&p.opening.to_bytes());
        out
    }

    fn decode_with_cfg(cfg: &IvcStepConfig, expected_tag: u8, bytes: &[u8]) -> Option<Self> {
        let split = argument_header_bytes(cfg.log_cells);
        if bytes.len() != split + cfg.opening_bytes()
            || bytes.get(..8)? != TREE_MAGIC
            || bytes[8] != expected_tag
        {
            return None;
        }
        let mut p = r1cs::Argument::blank(cfg);
        let (chunks, rem) = bytes[9..split].as_chunks::<8>();
        if !rem.is_empty() {
            return None;
        }
        let mut raw = chunks.iter();
        for x in p
            .acc
            .point
            .iter_mut()
            .chain(core::iter::once(&mut p.acc.value))
            .flat_map(|e| &mut e.0)
            .chain(&mut p.nonce)
            .chain(&mut p.root)
            .chain(
                p.row
                    .iter_mut()
                    .flatten()
                    .chain(&mut p.abc)
                    .chain(p.col.iter_mut().flatten())
                    .chain([&mut p.matrix, &mut p.z])
                    .flat_map(|e| &mut e.0),
            )
        {
            let v = u64::from_le_bytes(*raw.next()?);
            if v >= crate::field::GOLDILOCKS_PRIME {
                return None;
            }
            *x = f(v);
        }
        if raw.next().is_some() {
            return None;
        }
        p.opening = FixedPathWhirW24::from_bytes_canonical(cfg, &bytes[split..])?;
        Some(Self(p))
    }

    #[cfg(test)]
    pub(super) fn to_bytes_test_only(&self) -> Vec<u8> {
        // Test-only tag 0xFF is never accepted by production `from_bytes_canonical`.
        self.encode_with_tag(0xFF)
    }

    #[cfg(test)]
    pub(super) fn from_bytes_test_only(cfg: &IvcStepConfig, bytes: &[u8]) -> Option<Self> {
        Self::decode_with_cfg(cfg, 0xFF, bytes)
    }
}
