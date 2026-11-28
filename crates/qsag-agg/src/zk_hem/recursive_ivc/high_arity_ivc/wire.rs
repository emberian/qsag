//! Canonical little-endian encoding. All polynomial lengths and the PCS
//! schedule follow from the fixed leaf shape and the decoded roster.
use super::*;

const RECORD_BYTES: usize = 8 + 2 + IVC_BITMAP_BYTES;
pub(super) fn roster_bytes(roster: &[Roster]) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 + RECORD_BYTES * roster.len());
    out.extend_from_slice(&(roster.len() as u32).to_le_bytes());
    for rec in roster {
        out.extend_from_slice(&rec.id.to_le_bytes());
        out.extend_from_slice(&rec.threshold.to_le_bytes());
        out.extend_from_slice(&rec.bitmap);
    }
    out
}
fn write_e(out: &mut Vec<u8>, xs: &[E]) {
    for v in xs {
        out.extend_from_slice(&v.to_le_bytes());
    }
}
fn write_rounds(out: &mut Vec<u8>, rounds: &[Vec<E>]) {
    for co in rounds {
        write_e(out, co);
    }
}
struct Reader<'a>(&'a [u8]);
impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Option<[u8; N]> {
        let (v, rest) = self.0.split_first_chunk::<N>()?;
        self.0 = rest;
        Some(*v)
    }
    fn e(&mut self) -> Option<E> {
        E::from_le_bytes_canonical(self.take()?)
    }
    fn values<const N: usize>(&mut self) -> Option<[E; N]> {
        let mut xs = [E::ZERO; N];
        for v in &mut xs {
            *v = self.e()?;
        }
        Some(xs)
    }
    fn rounds(&mut self, n: usize, degree: usize) -> Option<Vec<Vec<E>>> {
        (0..n)
            .map(|_| (0..=degree).map(|_| self.e()).collect())
            .collect()
    }
}

impl HighArityProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.push(self.profile.wire_tag());
        out.extend_from_slice(&roster_bytes(&self.roster));
        out.extend_from_slice(&self.nonce);
        out.extend_from_slice(&self.root);
        write_rounds(&mut out, &self.row);
        let f = &self.fold;
        write_rounds(&mut out, &f.product);
        write_e(&mut out, &f.at_product);
        write_rounds(&mut out, &f.powers);
        write_e(&mut out, &f.at_powers);
        write_rounds(&mut out, &f.square);
        write_e(&mut out, &[f.at_square]);
        write_rounds(&mut out, &f.reduce);
        write_e(&mut out, &f.abc);
        write_rounds(&mut out, &self.col);
        write_e(&mut out, &[self.z]);
        self.opening.push_bytes(&mut out);
        out
    }
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let mut r = Reader(bytes.strip_prefix(MAGIC)?);
        let profile = Profile::from_wire_tag(r.take::<1>()?[0])?;
        let n = u32::from_le_bytes(r.take()?) as usize;
        if n == 0 || n > r.0.len() / RECORD_BYTES {
            return None;
        }
        let shape = shape();
        Geometry::new(&shape, n)?;
        let mut roster = Vec::with_capacity(n);
        let mut count = 0usize;
        let mut next = None;
        for _ in 0..n {
            let rec = Roster {
                id: u64::from_le_bytes(r.take()?),
                threshold: u16::from_le_bytes(r.take()?),
                bitmap: r.take()?,
            };
            let members = rec.count();
            if rec.threshold == 0
                || rec.threshold as usize > members
                || next.is_some_and(|id| id != rec.id)
            {
                return None;
            }
            next = Some(rec.id.checked_add(1)?);
            count = count.checked_add(members)?;
            roster.push(rec);
        }
        let g = Geometry::new(&shape, count)?;
        let nonce = r.take()?;
        let root = r.take()?;
        let row = r.rounds(shape.log_rows, params::ROW_DEGREE)?;
        let fold = fold::Fold {
            product: r.rounds(g.instances, 3)?,
            at_product: r.values()?,
            powers: r.rounds(g.instances, 3)?,
            at_powers: r.values()?,
            square: r.rounds(g.instances, 3)?,
            at_square: r.e()?,
            reduce: r.rounds(g.instances, 2)?,
            abc: r.values()?,
        };
        let col = r.rounds(g.columns, 2)?;
        let z = r.e()?;
        let mut pos = 0;
        let opening = pcs::Opening::read_interleaved(r.0, &mut pos, g.log, &g.schedule, g.stripes)?;
        (pos == r.0.len()).then_some(Self {
            profile,
            roster,
            nonce,
            root,
            row,
            fold,
            col,
            z,
            opening,
        })
    }
}
