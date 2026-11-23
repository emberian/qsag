// Locate regions through the Rust codec and geometry. The RTL receives only
// an offset and a bit for fault injection, never a decoded proof component.
#[path = "../proof_fixture.rs"]
mod proof_fixture;
use qsag_agg::zk_hem::v2::{
    pcs::stage_dims,
    protocol::{ZkHemV2Proof, layout_of},
};
use std::{collections::BTreeMap, fs};
struct Cases {
    pos: usize,
    entries: BTreeMap<(usize, usize), String>,
}
impl Cases {
    fn region(&mut self, name: &str, size: usize, count: usize) {
        assert!(count <= size * 8);
        for i in 0..count {
            let bit = if count == 1 {
                size * 8 - 1
            } else {
                i * (size * 8 - 1) / (count - 1)
            };
            assert!(
                self.entries
                    .insert((self.pos + bit / 8, bit % 8), name.to_owned())
                    .is_none()
            );
        }
        self.pos += size;
    }
    fn write(&self, path: &str) {
        let text: String = self
            .entries
            .iter()
            .map(|((o, b), n)| format!("{o} {b} {n}\n"))
            .collect();
        fs::write(path, text).unwrap();
        println!("{path}: {} distinct single-bit cases", self.entries.len());
    }
}
fn main() {
    let bytes = fs::read("vec/proof_v2.bin").unwrap();
    let (shape, assignment) = proof_fixture::relation();
    let p = ZkHemV2Proof::from_bytes(&bytes, &shape).unwrap();
    assert!(qsag_agg::zk_hem::v2::protocol::verify(
        &shape,
        &assignment[1..=shape.num_public],
        proof_fixture::STATEMENT,
        qsag_agg::zk_hem::v2::params::Profile::TurboShakeJohnson400,
        &p
    ));
    let layout = layout_of(&shape).unwrap();
    let dims = stage_dims(layout.log_cells, &layout.schedule).unwrap();
    let mut m = Cases {
        pos: 10,
        entries: BTreeMap::new(),
    };
    m.region("tree_nonce", 32, 40);
    m.region("root0", 50, 40);
    m.region("row_mask", 40, 24);
    for round in p.row_rounds {
        m.region("row_round", round.len() * 40, 16);
    }
    m.region("row_values", 120, 12);
    m.region("col_mask", 40, 8);
    for round in p.col_rounds {
        m.region("col_round", round.len() * 40, 6);
    }
    m.region("mask_evals", 200, 2);
    m.region("stage0_folds", 200 * dims[0].step_vars, 2);
    m.region("mask_claim", 40, 1);
    for (i, stage) in p.opening.stages.iter().enumerate() {
        m.region("stage_root", 50, 2);
        m.region("ood", 80, 2);
        let d = dims[i];
        let sib = if i == 0 {
            for j in 0..d.queries {
                for (k, n) in [("salt", 32), ("z", 8 * d.arity()), ("r", 40)] {
                    m.region(k, n, usize::from(j == d.queries - 1));
                }
            }
            p.opening.stage0_query.siblings.len()
        } else {
            m.region("ext_fiber", 40 * d.arity() * d.queries, 2);
            p.opening.stages[i - 1].query.siblings.len()
        };
        m.region("sibling_count", 4, 2);
        m.region("siblings", 50 * sib, 2);
        m.region("stage_folds", 200 * stage.folds.len(), 2);
    }
    let d = dims.last().unwrap();
    m.region("final_coeffs", 40 * p.opening.final_coeffs.len(), 2);
    m.region("final_fibers", 40 * d.arity() * d.queries, 2);
    m.region("final_count", 4, 2);
    m.region(
        "final_siblings",
        50 * p.opening.stages.last().unwrap().query.siblings.len(),
        2,
    );
    assert_eq!(m.pos, bytes.len());
    // All sixteen individual bits at the magic/profile boundary.
    for offset in [7, 8] {
        for bit in 0..8 {
            m.entries.insert((offset, bit), "envelope".to_owned());
        }
    }
    m.write("vec/tamper_v2.txt");
    let h = fs::read("vec/proof_hqm2.bin").unwrap();
    let n = u32::from_le_bytes(h[9..13].try_into().unwrap()) as usize;
    let mut m = Cases {
        pos: 9 + 4 + 8 * n.div_ceil(64) + 8,
        entries: BTreeMap::new(),
    };
    m.region("hqm_root", 50, 12);
    m.region("step_round", 360, 32);
    let log_rows = qsag_agg::trace::build_signer_program(qsag_agg::AggSigProfile::JortsPoseidon2)
        .len()
        .ilog2() as usize;
    for round in 1..log_rows {
        if round + 1 == log_rows {
            // Both endpoint evaluations participate in the final row sum test.
            m.region("last_step_endpoints", 80, 30);
            m.region("last_step_other_evaluations", 280, 1);
        } else {
            m.region("step_round", 360, 30);
        }
    }
    m.region("columns", 256 * 40, 3);
    m.region("first_ood", 5 * 40, 2);
    let schedule = qsag_agg::zk_hem::v2::params::schedule(log_rows + 8).unwrap();
    let d = stage_dims(log_rows + 8, &schedule).unwrap()[0];
    m.region("hqm_stage0_folds", d.step_vars * 200, 2);
    m.region("hqm_next_root", 50, 2);
    m.region("hqm_later_ood", 2 * 40, 2);
    m.region("hqm_base_fibers", 8 * d.queries * d.arity(), 2);
    assert!(m.pos < h.len() - 50);
    m.pos = h.len() - 50;
    m.region("hqm_sibling", 50, 2);
    m.write("vec/tamper_hqm2.txt");
}
