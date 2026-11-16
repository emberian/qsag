//! Binary monotone span programs over Goldilocks. Public elimination is variable-time;
//! secret sharing and additive collapse use fixed loops over public matrix dimensions.
//! A dealer supplies fresh uniform masks; this module does not implement a distributed dealer.
use crate::{field::goldilocks::Goldilocks as F, wipe::SecretBuffer};
use alloc::{collections::BTreeSet, vec, vec::Vec};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessError {
    InvalidMatrix,
    Unauthorized,
    InvalidShares,
    InvalidWeights,
    PolicyTooLarge,
}

/// Matrix entries are exactly zero or one, with reconstruction target `(1, 0, ...)`.
/// Private fields keep malformed matrices out of the reconstruction path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MonotoneSpanProgram {
    num_cols: usize,
    row_owner: Vec<u16>,
    matrix_rows: Vec<Vec<u8>>,
}
impl MonotoneSpanProgram {
    pub fn new(row_owner: Vec<u16>, matrix_rows: Vec<Vec<u8>>) -> Result<Self, AccessError> {
        let d = matrix_rows.first().map_or(0, Vec::len);
        if d == 0
            || row_owner.len() != matrix_rows.len()
            || matrix_rows
                .iter()
                .any(|r| r.len() != d || r.iter().any(|&x| x > 1))
        {
            return Err(AccessError::InvalidMatrix);
        }
        Ok(Self {
            num_cols: d,
            row_owner,
            matrix_rows,
        })
    }
    pub fn row_owners(&self) -> &[u16] {
        &self.row_owner
    }
    pub fn matrix_rows(&self) -> &[Vec<u8>] {
        &self.matrix_rows
    }
    pub fn num_cols(&self) -> usize {
        self.num_cols
    }

    /// Universal OR-of-ANDs compiler. Every listed set is a sufficient coalition.
    /// Each branch uses independent masks and alternating +/- reconstruction weights.
    /// Exponential policies should use a manually supplied compact binary matrix.
    pub fn from_authorized_sets(sets: &[BTreeSet<u16>]) -> Result<Self, AccessError> {
        if sets.is_empty() || sets.iter().any(BTreeSet::is_empty) {
            return Err(AccessError::InvalidMatrix);
        }
        let d = sets
            .iter()
            .try_fold(1usize, |n, s| n.checked_add(s.len() - 1))
            .ok_or(AccessError::PolicyTooLarge)?;
        let rows = sets
            .iter()
            .try_fold(0usize, |n, s| n.checked_add(s.len()))
            .ok_or(AccessError::PolicyTooLarge)?;
        if rows.checked_mul(d).is_none_or(|cells| cells > 4_194_304) {
            return Err(AccessError::PolicyTooLarge);
        }
        let mut owners = Vec::new();
        let mut rows = Vec::new();
        let mut col = 1;
        for set in sets {
            for (i, &party) in set.iter().enumerate() {
                let mut row = vec![0; d];
                if i == 0 {
                    row[0] = 1;
                } else {
                    row[col + i - 1] = 1;
                }
                if i + 1 < set.len() {
                    row[col + i] = 1;
                }
                owners.push(party);
                rows.push(row);
            }
            col += set.len() - 1;
        }
        Self::new(owners, rows)
    }

    /// Four independent field secrets, with exactly `d-1` freshly sampled mask vectors.
    /// Returned rows wipe on drop; callers must likewise protect the input masks.
    pub fn share(
        &self,
        secret: &[F; 4],
        masks: &[[F; 4]],
    ) -> Result<SecretBuffer<Vec<[F; 4]>>, AccessError> {
        if masks.len() != self.num_cols - 1 {
            return Err(AccessError::InvalidShares);
        }
        let mut out = SecretBuffer(vec![[F::ZERO; 4]; self.row_owner.len()]);
        for (row, dst) in self.matrix_rows.iter().zip(out.iter_mut()) {
            for (&coefficient, value) in row.iter().zip(core::iter::once(secret).chain(masks)) {
                for k in 0..4 {
                    dst[k] += F::from_u64_reduced(u64::from(coefficient)) * value[k];
                }
            }
        }
        Ok(out)
    }

    /// Deterministically solve `M_active^T lambda = e1`; all inactive weights are zero.
    pub fn solve_reconstruction_weights(&self, active: &BTreeSet<u16>) -> Option<Vec<F>> {
        let selected: Vec<usize> = self
            .row_owner
            .iter()
            .enumerate()
            .filter_map(|(r, p)| active.contains(p).then_some(r))
            .collect();
        let n = selected.len();
        let mut a = vec![vec![F::ZERO; n + 1]; self.num_cols];
        for (c, row) in a.iter_mut().enumerate() {
            for (i, &r) in selected.iter().enumerate() {
                row[i] = F::from_u64_reduced(u64::from(self.matrix_rows[r][c]));
            }
        }
        a[0][n] = F::ONE;
        let mut pivots = Vec::new();
        for col in 0..n {
            let rank = pivots.len();
            let Some(pivot) = (rank..self.num_cols).find(|&r| a[r][col] != F::ZERO) else {
                continue;
            };
            a.swap(rank, pivot);
            let inverse = a[rank][col].checked_inv()?;
            for entry in &mut a[rank] {
                *entry *= inverse;
            }
            let pivot_row = a[rank].clone();
            for (r, row) in a.iter_mut().enumerate() {
                if r != rank {
                    let factor = row[col];
                    for (x, &y) in row.iter_mut().zip(&pivot_row) {
                        *x -= factor * y;
                    }
                }
            }
            pivots.push(col);
        }
        if a.iter()
            .any(|row| row[..n].iter().all(|x| *x == F::ZERO) && row[n] != F::ZERO)
        {
            return None;
        }
        let mut weights = vec![F::ZERO; self.row_owner.len()];
        for (r, &col) in pivots.iter().enumerate() {
            weights[selected[col]] = a[r][n];
        }
        Some(weights)
    }

    pub fn verify_reconstruction_weights(&self, weights: &[F]) -> bool {
        weights.len() == self.row_owner.len()
            && (0..self.num_cols).all(|c| {
                self.matrix_rows
                    .iter()
                    .zip(weights)
                    .fold(F::ZERO, |s, (r, &w)| {
                        s + F::from_u64_reduced(u64::from(r[c])) * w
                    })
                    == if c == 0 { F::ONE } else { F::ZERO }
            })
    }

    /// `party_rows` contains only this party's rows, in matrix order. The returned
    /// vector is ready for the existing additive MPC input interface (no gate changes).
    pub fn collapse_to_additive_share(
        &self,
        party: u16,
        weights: &[F],
        party_rows: &[[F; 4]],
    ) -> Result<SecretBuffer<[F; 4]>, AccessError> {
        if !self.verify_reconstruction_weights(weights) {
            return Err(AccessError::InvalidWeights);
        }
        if party_rows.len() != self.row_owner.iter().filter(|&&p| p == party).count() {
            return Err(AccessError::InvalidShares);
        }
        let mut out = SecretBuffer([F::ZERO; 4]);
        for ((_, &w), row) in self
            .row_owner
            .iter()
            .zip(weights)
            .filter(|(p, _)| **p == party)
            .zip(party_rows)
        {
            for k in 0..4 {
                out[k] += w * row[k];
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn binary_hierarchy_exhaustive_authorization_and_collapse() {
        // (A AND B) OR (B AND C AND D), including repeated ownership across branches.
        let sets = [BTreeSet::from([0, 1]), BTreeSet::from([1, 2, 3])];
        let m = MonotoneSpanProgram::from_authorized_sets(&sets).unwrap();
        let secret = [F::from_u64_reduced(42); 4];
        let masks = vec![[F::from_u64_reduced(123); 4]; m.num_cols() - 1];
        let rows = m.share(&secret, &masks).unwrap();
        for bits in 0..16 {
            let active = (0..4).filter(|p| bits & (1 << p) != 0).collect();
            let weights = m.solve_reconstruction_weights(&active);
            assert_eq!(weights.is_some(), sets.iter().any(|s| s.is_subset(&active)));
            if let Some(w) = weights {
                let mut sum = [F::ZERO; 4];
                for &p in &active {
                    let local: Vec<_> = m
                        .row_owner
                        .iter()
                        .zip(rows.iter())
                        .filter_map(|(&owner, &r)| (owner == p).then_some(r))
                        .collect();
                    let share = m.collapse_to_additive_share(p, &w, &local).unwrap();
                    for k in 0..4 {
                        sum[k] += share[k];
                    }
                }
                assert_eq!(sum, secret);
                assert!(m.collapse_to_additive_share(1, &w, &[]).is_err());
            }
        }
        assert!(
            m.collapse_to_additive_share(0, &vec![F::ZERO; rows.len()], &[])
                .is_err()
        );
        assert!(MonotoneSpanProgram::new(vec![0], vec![vec![2]]).is_err());
    }
}
