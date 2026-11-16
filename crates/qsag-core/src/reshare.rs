//! Public linear-algebra checks for resharing. Freshness, honest participation and
//! authentication of contributions are protocol obligations, not facts a rank test
//! can establish. Never apply this test to secret random samples and publish the result.
use crate::field::goldilocks::Goldilocks;
use alloc::vec::Vec;

/// Check that the authenticated public mixing vectors span every required fresh
/// mask coordinate. Reject ragged/empty bases and rank-deficient refresh schedules.
/// The caller must separately verify fresh independent private masks, commitment
/// consistency, and an honest contributing core before erasing old shares.
pub fn reshare_rank_guard(required_dimensions: usize, public_basis: &[Vec<Goldilocks>]) -> bool {
    if required_dimensions == 0
        || public_basis.len() < required_dimensions
        || public_basis.iter().any(|r| r.len() != required_dimensions)
    {
        return false;
    }
    let mut matrix = public_basis.to_vec();
    let mut rank = 0;
    for column in 0..required_dimensions {
        let Some(pivot) = (rank..matrix.len()).find(|&r| matrix[r][column] != Goldilocks::ZERO)
        else {
            continue;
        };
        matrix.swap(rank, pivot);
        let Some(inverse) = matrix[rank][column].checked_inv() else {
            return false;
        };
        for x in &mut matrix[rank] {
            *x *= inverse;
        }
        let row = matrix[rank].clone();
        for other in &mut matrix[rank + 1..] {
            let factor = other[column];
            for (x, &y) in other.iter_mut().zip(&row) {
                *x -= factor * y;
            }
        }
        rank += 1;
    }
    rank == required_dimensions
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    #[test]
    fn rank_guard_rejects_reused_mask_directions() {
        let z = Goldilocks::ZERO;
        let o = Goldilocks::ONE;
        assert!(reshare_rank_guard(2, &[vec![o, z], vec![o, o]]));
        assert!(!reshare_rank_guard(2, &[vec![o, o], vec![o + o, o + o]]));
        assert!(!reshare_rank_guard(2, &[vec![o], vec![o, o]]));
        assert!(!reshare_rank_guard(0, &[]));
    }
}
