use qsag_agg::field::Goldilocks as F;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Lc, Shape};

pub const STATEMENT: &[u8] = b"QSAG-NI command-port verification";

pub fn relation() -> (Shape, Vec<F>) {
    let mut cs = ConstraintSystem::new();
    let x = F::from_u64_reduced(3);
    let xv = cs.public_input(x);
    let yv = cs.public_input(x.pow(7) * F::from_u64_reduced(5));
    let w = cs.alloc(F::from_u64_reduced(5));
    let s = cs.sbox7(&xv.into());
    let prod = cs.mul(&s.into(), &w.into());
    cs.enforce_equal(&Lc::from(prod), &yv.into());
    cs.finish_v2()
}
