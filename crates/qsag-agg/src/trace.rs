//! Execution trace layout (`C = 256` columns) and shared prover/verifier algebraic row-constraint
//! evaluator for `JortsPoseidon2` (`512` rows/signer) and `CorduroyPoseidon2` (`8,192` rows/signer).

use alloc::vec::Vec;

use crate::field::{Goldilocks, GoldilocksExt4};
#[cfg(debug_assertions)]
use crate::sig::wots_step_hash_injective;
use crate::sig::{
    AggSigProfile, DOMAIN_FORS_LEAF, DOMAIN_FORS_NODE, DOMAIN_FORS_ROOTS, DOMAIN_H_MSG_DET_TREE,
    DOMAIN_H_MSG_STATEFUL, DOMAIN_H_MSG_STATELESS, DOMAIN_MERKLE_NODE, DOMAIN_WOTS_PK,
    DOMAIN_WOTS_STEP, Digest5, FORS_HEIGHT, FORS_TREES, JORTS_XMSS_HEIGHT, CORDUROY_NUM_LAYERS,
    CORDUROY_SUBTREE_HEIGHT, ValidatorPublicKey, ValidatorSignature, WOTS_CHAINS, WOTS_TARGET_SUM,
    compute_hmsg_det_tree, compute_hmsg_stateful, derive_stateless_fors_and_leaf_checked,
    extract_wots_digits_checked, pack_wots_addr_limb,
};
use crate::sponge::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXT_ROUNDS, POSEIDON2_INT_ROUNDS, poseidon2_apply_me,
    poseidon2_apply_me_ext4, poseidon2_apply_mi, poseidon2_apply_mi_ext4, poseidon2_const_at,
    poseidon2_sbox7, poseidon2_sbox7_ext4,
};

/// Number of witness columns per row (`2^8 = 256`).
pub const NUM_TRACE_COLS: usize = 256;
pub const LOG_TRACE_COLS: usize = 8;

/// Number of inter-row carried state limbs (`st[0..44]`).
pub const NUM_STATE_LIMBS: usize = 44;

// Column offsets inside `row[0..256]` (`12 + 118 + 44 + 44 + 38 = 256`):
pub const COL_ST_IN: usize = 0; // 0..12
pub const COL_SBOX_OUT: usize = 12; // 12..130
pub const COL_PREV_STATE: usize = 130; // 130..174
pub const COL_NEXT_STATE: usize = 174; // 174..218
pub const COL_AUX: usize = 218; // 218..256 (38 cols)

// State register indices inside `prev_state[0..44]` / `next_state[0..44]`:
pub const ST_CUR_ROOT: usize = 0; // 0..4
pub const ST_KP_IDX: usize = 4; // 4
pub const ST_TREE_LO: usize = 5; // 5
pub const ST_TREE_HI: usize = 6; // 6
pub const ST_REM_PACK: usize = 7; // 7..13 (6 limbs)
pub const ST_MAIN_SPONGE: usize = 13; // 13..25 (12 limbs: H_msg / T_ell / FORS_ROOTS)
pub const ST_SUB_SPONGE: usize = 25; // 25..37 (12 limbs: 2-block Merkle intermediate state; 25..29 = ep_even, 29..33 = merkle_right)
pub const ST_WORK: usize = 37; // 37..41 (4 limbs: cur WOTS chain / ep_odd / current Merkle node)
pub const ST_CURSOR_IDX: usize = 41; // 41 (Merkle walk index cursor)
pub const ST_ACC_OR_U1: usize = 42; // 42 (running digit sum in H_msg, or `u1` in WOTS)
pub const ST_WOTS_U2: usize = 43; // 43 (`u2` in WOTS)

/// Fixed row count per signer (`512` for `JortsPoseidon2`, `8,192` for `CorduroyPoseidon2`).
#[inline]
pub const fn rows_per_signer(profile: AggSigProfile) -> usize {
    match profile {
        AggSigProfile::JortsPoseidon2 => 512,
        AggSigProfile::CorduroyPoseidon2 => 8192,
    }
}

/// Deterministic step opcodes defining the per-signer state machine (`max aux = 38`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepOp {
    Idle,

    // --- Stateful `JortsPoseidon2` H_msg ---
    StatefulHmsgBlock0,
    StatefulHmsgBlock1,
    StatefulHmsgSqueeze,

    // --- Stateless `CorduroyPoseidon2` XOF & FORS (`k = 32, a = 8`) ---
    StatelessDeriveBlock0,
    StatelessDeriveBlock1,
    /// Decompose `main_sponge[limb_idx]` (`0..=6`) into 31 base-4 digits + `b62`, packing FORS idxs & `leaf_global_idx`.
    StatelessDecompLimb {
        limb_idx: u8,
    },
    ForsRootsSpongeInit,
    ForsLeafHash {
        tree_j: u8,
        pack_slot: u8,
    },
    ForsMerkleBlockA {
        tree_j: u8,
        lvl: u8,
    },
    ForsMerkleBlockB {
        lvl: u8,
        is_tree_last: bool,
        is_odd_tree: bool,
    },
    ForsRootsPairAbsorb {
        pair_idx: u8,
    },
    ForsRootsFinalSqueeze,

    // --- Deterministic Hypertree `H_msg_det_tree` (`CorduroyPoseidon2` layers `0..16`) ---
    DetTreeHmsgBlock0 {
        layer: u8,
    },
    DetTreeHmsgBlock1 {
        layer: u8,
    },

    // --- Shared 5-Limb `H_msg` Base-4 Digit Decomposition (`1` limb/row = 32 aux cols!) + TSW Sum Check ---
    HmsgDecompLimb {
        limb_idx: u8,
    },

    // --- Shared 128-Chain `WOTS+C` + Interleaved Rate-8 `T_ell` Sponge ---
    WotsTellInit {
        layer: u8,
    },
    WotsChainStep0 {
        layer: u8,
        chain: u8,
        pack_slot: u8,
    },
    WotsChainStep1 {
        layer: u8,
        chain: u8,
    },
    WotsChainStep2 {
        layer: u8,
        chain: u8,
        is_odd: bool,
    },
    WotsTellPairAbsorb {
        pair_idx: u8,
    },
    WotsTellFinalSqueeze,

    // --- Shared 2-Block Full-`pk_seed` Subtree Merkle Path ---
    XmssMerkleBlockA {
        layer: u8,
        lvl: u8,
    },
    XmssMerkleBlockB {
        is_layer_last: bool,
        is_top_final: bool,
    },
}

/// Build the exact fixed-length program (`len == rows_per_signer(profile)`) shared by prover and verifier.
pub fn build_signer_program(profile: AggSigProfile) -> Vec<StepOp> {
    let total_rows = rows_per_signer(profile);
    let mut prog = Vec::with_capacity(total_rows);

    match profile {
        AggSigProfile::JortsPoseidon2 => {
            prog.push(StepOp::StatefulHmsgBlock0);
            prog.push(StepOp::StatefulHmsgBlock1);
            prog.push(StepOp::StatefulHmsgSqueeze);
            for l in 0..5 {
                prog.push(StepOp::HmsgDecompLimb { limb_idx: l });
            }
            push_layer_wots_and_merkle(&mut prog, 0, JORTS_XMSS_HEIGHT, true);
        }
        AggSigProfile::CorduroyPoseidon2 => {
            prog.push(StepOp::StatelessDeriveBlock0);
            prog.push(StepOp::StatelessDeriveBlock1);
            for l in 0..7 {
                prog.push(StepOp::StatelessDecompLimb { limb_idx: l });
            }
            prog.push(StepOp::ForsRootsSpongeInit);
            for pair in 0..(FORS_TREES / 2) {
                for sub in 0..2 {
                    let j = 2 * pair + sub;
                    let pack_slot = (j / 6) as u8;
                    prog.push(StepOp::ForsLeafHash {
                        tree_j: j as u8,
                        pack_slot,
                    });
                    for lvl in 0..FORS_HEIGHT {
                        prog.push(StepOp::ForsMerkleBlockA {
                            tree_j: j as u8,
                            lvl: lvl as u8,
                        });
                        prog.push(StepOp::ForsMerkleBlockB {
                            lvl: lvl as u8,
                            is_tree_last: lvl + 1 == FORS_HEIGHT,
                            is_odd_tree: sub == 1,
                        });
                    }
                }
                prog.push(StepOp::ForsRootsPairAbsorb {
                    pair_idx: pair as u8,
                });
            }
            prog.push(StepOp::ForsRootsFinalSqueeze);

            for layer in 0..CORDUROY_NUM_LAYERS {
                prog.push(StepOp::DetTreeHmsgBlock0 { layer: layer as u8 });
                prog.push(StepOp::DetTreeHmsgBlock1 { layer: layer as u8 });
                for l in 0..5 {
                    prog.push(StepOp::HmsgDecompLimb { limb_idx: l });
                }
                push_layer_wots_and_merkle(
                    &mut prog,
                    layer as u8,
                    CORDUROY_SUBTREE_HEIGHT,
                    layer + 1 == CORDUROY_NUM_LAYERS,
                );
            }
        }
    }

    assert!(
        prog.len() < total_rows,
        "program len {} must be < {}",
        prog.len(),
        total_rows
    );
    prog.resize(total_rows, StepOp::Idle);
    prog
}

#[inline]
pub const fn wots_pack_slot(chain: u8) -> u8 {
    if chain < 26 {
        0
    } else if chain < 52 {
        1
    } else if chain < 78 {
        2
    } else if chain < 103 {
        3
    } else {
        4
    }
}

fn push_layer_wots_and_merkle(
    prog: &mut Vec<StepOp>,
    layer: u8,
    sub_height: usize,
    is_top_final: bool,
) {
    prog.push(StepOp::WotsTellInit { layer });
    for pair in 0..(WOTS_CHAINS / 2) {
        for sub in 0..2 {
            let chain = (2 * pair + sub) as u8;
            let is_odd = sub == 1;
            let pack_slot = wots_pack_slot(chain);
            prog.push(StepOp::WotsChainStep0 {
                layer,
                chain,
                pack_slot,
            });
            prog.push(StepOp::WotsChainStep1 { layer, chain });
            prog.push(StepOp::WotsChainStep2 {
                layer,
                chain,
                is_odd,
            });
        }
        prog.push(StepOp::WotsTellPairAbsorb {
            pair_idx: pair as u8,
        });
    }
    prog.push(StepOp::WotsTellFinalSqueeze);
    for lvl in 0..sub_height {
        prog.push(StepOp::XmssMerkleBlockA {
            layer,
            lvl: lvl as u8,
        });
        prog.push(StepOp::XmssMerkleBlockB {
            is_layer_last: lvl + 1 == sub_height,
            is_top_final: (lvl + 1 == sub_height) && is_top_final,
        });
    }
}

/// Algebraic constraint equivalence class (`21` unique classes for `JortsPoseidon2`, `45` for `CorduroyPoseidon2`),
/// factoring per-step public constants (`layer`, `chain`, `tree_j`, `lvl`) into a single multilinear scalar `step_c0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintKind {
    Idle,
    StatefulHmsgBlock0,
    StatefulHmsgBlock1,
    StatefulHmsgSqueeze,
    StatelessDeriveBlock0,
    StatelessDeriveBlock1,
    StatelessDecompLimb {
        limb_idx: u8,
    },
    ForsRootsSpongeInit,
    ForsLeafHash {
        pack_slot: u8,
    },
    ForsMerkleBlockA,
    ForsMerkleBlockB {
        is_tree_last: bool,
        is_odd_tree: bool,
    },
    ForsRootsPairAbsorb {
        is_last_pair: bool,
    },
    ForsRootsFinalSqueeze,
    DetTreeHmsgBlock0,
    DetTreeHmsgBlock1,
    HmsgDecompLimb {
        limb_idx: u8,
    },
    WotsTellInit,
    WotsChainStep0 {
        pack_slot: u8,
    },
    WotsChainStep1,
    WotsChainStep2 {
        is_odd: bool,
    },
    WotsTellPairAbsorb {
        is_last_pair: bool,
    },
    WotsTellFinalSqueeze,
    XmssMerkleBlockA,
    XmssMerkleBlockB {
        is_layer_last: bool,
        is_top_final: bool,
    },
}

#[inline]
pub fn step_op_to_kind_and_c0(op: StepOp) -> (ConstraintKind, Goldilocks) {
    match op {
        StepOp::Idle => (ConstraintKind::Idle, Goldilocks::ZERO),
        StepOp::StatefulHmsgBlock0 => (ConstraintKind::StatefulHmsgBlock0, Goldilocks::ZERO),
        StepOp::StatefulHmsgBlock1 => (ConstraintKind::StatefulHmsgBlock1, Goldilocks::ZERO),
        StepOp::StatefulHmsgSqueeze => (ConstraintKind::StatefulHmsgSqueeze, Goldilocks::ZERO),
        StepOp::StatelessDeriveBlock0 => (ConstraintKind::StatelessDeriveBlock0, Goldilocks::ZERO),
        StepOp::StatelessDeriveBlock1 => (ConstraintKind::StatelessDeriveBlock1, Goldilocks::ZERO),
        StepOp::StatelessDecompLimb { limb_idx } => (
            ConstraintKind::StatelessDecompLimb { limb_idx },
            Goldilocks::ZERO,
        ),
        StepOp::ForsRootsSpongeInit => (ConstraintKind::ForsRootsSpongeInit, Goldilocks::ZERO),
        StepOp::ForsLeafHash { tree_j, pack_slot } => (
            ConstraintKind::ForsLeafHash { pack_slot },
            Goldilocks::from_u64_reduced((tree_j as u64) << FORS_HEIGHT),
        ),
        StepOp::ForsMerkleBlockA { tree_j, lvl } => {
            let addr_base = (tree_j as u64) << (FORS_HEIGHT - 1 - (lvl as usize));
            let c0 = (((lvl as u64) + 1) << 32) + addr_base;
            (
                ConstraintKind::ForsMerkleBlockA,
                Goldilocks::from_u64_reduced(c0),
            )
        }
        StepOp::ForsMerkleBlockB {
            lvl: _,
            is_tree_last,
            is_odd_tree,
        } => (
            ConstraintKind::ForsMerkleBlockB {
                is_tree_last,
                is_odd_tree,
            },
            Goldilocks::ZERO,
        ),
        StepOp::ForsRootsPairAbsorb { pair_idx } => (
            ConstraintKind::ForsRootsPairAbsorb {
                is_last_pair: (pair_idx as usize) + 1 == FORS_TREES / 2,
            },
            Goldilocks::ZERO,
        ),
        StepOp::ForsRootsFinalSqueeze => (ConstraintKind::ForsRootsFinalSqueeze, Goldilocks::ZERO),
        StepOp::DetTreeHmsgBlock0 { layer } => (
            ConstraintKind::DetTreeHmsgBlock0,
            Goldilocks::from_u64_reduced((layer as u64) << 32),
        ),
        StepOp::DetTreeHmsgBlock1 { layer: _ } => {
            (ConstraintKind::DetTreeHmsgBlock1, Goldilocks::ZERO)
        }
        StepOp::HmsgDecompLimb { limb_idx } => (
            ConstraintKind::HmsgDecompLimb { limb_idx },
            Goldilocks::ZERO,
        ),
        StepOp::WotsTellInit { layer } => (
            ConstraintKind::WotsTellInit,
            Goldilocks::from_u64_reduced((layer as u64) << 32),
        ),
        StepOp::WotsChainStep0 {
            layer,
            chain,
            pack_slot,
        } => (
            ConstraintKind::WotsChainStep0 { pack_slot },
            Goldilocks::from_u64_reduced(((layer as u64) << 44) | ((chain as u64) << 4)),
        ),
        StepOp::WotsChainStep1 { layer, chain } => (
            ConstraintKind::WotsChainStep1,
            Goldilocks::from_u64_reduced(((layer as u64) << 44) | ((chain as u64) << 4) | 1),
        ),
        StepOp::WotsChainStep2 {
            layer,
            chain,
            is_odd,
        } => (
            ConstraintKind::WotsChainStep2 { is_odd },
            Goldilocks::from_u64_reduced(((layer as u64) << 44) | ((chain as u64) << 4) | 2),
        ),
        StepOp::WotsTellPairAbsorb { pair_idx } => (
            ConstraintKind::WotsTellPairAbsorb {
                is_last_pair: (pair_idx as usize) + 1 == WOTS_CHAINS / 2,
            },
            Goldilocks::ZERO,
        ),
        StepOp::WotsTellFinalSqueeze => (ConstraintKind::WotsTellFinalSqueeze, Goldilocks::ZERO),
        StepOp::XmssMerkleBlockA { layer, lvl } => (
            ConstraintKind::XmssMerkleBlockA,
            Goldilocks::from_u64_reduced(((layer as u64) << 48) | (((lvl as u64) + 1) << 32)),
        ),
        StepOp::XmssMerkleBlockB {
            is_layer_last,
            is_top_final,
        } => (
            ConstraintKind::XmssMerkleBlockB {
                is_layer_last,
                is_top_final,
            },
            Goldilocks::ZERO,
        ),
    }
}

/// Assign each distinct `ConstraintKind` in `program` a dense index `0..unique_ops.len()` and extract
/// the per-row public constant column `step_c0[0..program.len()]`!
pub fn index_unique_program_ops(
    program: &[StepOp],
) -> (Vec<ConstraintKind>, Vec<usize>, Vec<Goldilocks>) {
    let mut unique = Vec::new();
    let mut step_to_uid = Vec::with_capacity(program.len());
    let mut step_c0 = Vec::with_capacity(program.len());
    for &op in program {
        let (kind, c0) = step_op_to_kind_and_c0(op);
        let pos = match unique.iter().position(|&u| u == kind) {
            Some(p) => p,
            None => {
                let p = unique.len();
                unique.push(kind);
                p
            }
        };
        step_to_uid.push(pos);
        step_c0.push(c0);
    }
    (unique, step_to_uid, step_c0)
}

// ============================================================================
// 1. Prover Witness Generation
// ============================================================================

pub fn record_poseidon2_perm12(
    st_in: [Goldilocks; 12],
    sbox_out: &mut [Goldilocks; 118],
) -> [Goldilocks; 12] {
    let mut st = st_in;
    poseidon2_apply_me(&mut st);
    let mut cursor = 0usize;
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let y = poseidon2_sbox7(*lane_val + poseidon2_const_at(0, r as u64, lane as u64));
            *lane_val = y;
            sbox_out[cursor] = y;
            cursor += 1;
        }
        poseidon2_apply_me(&mut st);
    }
    for r in 0..POSEIDON2_INT_ROUNDS {
        let y = poseidon2_sbox7(st[0] + poseidon2_const_at(1, r as u64, 0));
        st[0] = y;
        sbox_out[cursor] = y;
        cursor += 1;
        poseidon2_apply_mi(&mut st);
    }
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let y = poseidon2_sbox7(*lane_val + poseidon2_const_at(2, r as u64, lane as u64));
            *lane_val = y;
            sbox_out[cursor] = y;
            cursor += 1;
        }
        poseidon2_apply_me(&mut st);
    }
    debug_assert_eq!(cursor, 118);
    st
}

#[inline]
fn fill_row_perm(
    row: &mut [Goldilocks; NUM_TRACE_COLS],
    st_in: [Goldilocks; 12],
) -> [Goldilocks; 12] {
    row[COL_ST_IN..COL_ST_IN + 12].copy_from_slice(&st_in);
    let mut sbox = [Goldilocks::ZERO; 118];
    let out = record_poseidon2_perm12(st_in, &mut sbox);
    row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&sbox);
    out
}

#[inline]
fn write_limb63_decomp_aux(row: &mut [Goldilocks; NUM_TRACE_COLS], v: u64) {
    debug_assert_eq!(v >> 63, 0);
    for i in 0..31 {
        row[COL_AUX + i] = Goldilocks::from_u64_reduced((v >> (2 * i)) & 3);
    }
    row[COL_AUX + 31] = Goldilocks::from_u64_reduced((v >> 62) & 1);
}

/// Populate an inactive / blinding signer slot (`Idle` unconstrained aux limbs randomized).
pub fn populate_inactive_signer_rows(
    rows: &mut [[Goldilocks; NUM_TRACE_COLS]],
    blinding_limbs: &[[Goldilocks; 4]],
) {
    let mut zero_sbox = [Goldilocks::ZERO; 118];
    let _ = record_poseidon2_perm12([Goldilocks::ZERO; 12], &mut zero_sbox);
    for (r_idx, row) in rows.iter_mut().enumerate() {
        row.fill(Goldilocks::ZERO);
        row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&zero_sbox);
        if r_idx < blinding_limbs.len() {
            row[COL_AUX + 34..COL_AUX + 38].copy_from_slice(&blinding_limbs[r_idx]);
        }
    }
}

/// Populate all `R = rows_per_signer(pk.profile)` rows for one valid `(pk, mu, sig)` tuple.
pub fn populate_active_signer_rows(
    program: &[StepOp],
    pk: &ValidatorPublicKey,
    mu: Digest5,
    sig: &ValidatorSignature,
    rows: &mut [[Goldilocks; NUM_TRACE_COLS]],
) {
    assert_eq!(rows.len(), program.len());
    let mut zero_sbox = [Goldilocks::ZERO; 118];
    let _ = record_poseidon2_perm12([Goldilocks::ZERO; 12], &mut zero_sbox);
    for row in rows.iter_mut() {
        row.fill(Goldilocks::ZERO);
        row[COL_SBOX_OUT..COL_SBOX_OUT + 118].copy_from_slice(&zero_sbox);
    }

    let mut state = [Goldilocks::ZERO; NUM_STATE_LIMBS];
    let mut cur_digits = [0u8; WOTS_CHAINS];
    let mut stateless_fors_idxs = [0usize; FORS_TREES];

    for (t, &op) in program.iter().enumerate() {
        let row = &mut rows[t];
        row[COL_PREV_STATE..COL_PREV_STATE + NUM_STATE_LIMBS].copy_from_slice(&state);
        let mut next = state;

        match op {
            StepOp::Idle => {
                next = [Goldilocks::ZERO; NUM_STATE_LIMBS];
            }
            StepOp::StatefulHmsgBlock0 => {
                next = [Goldilocks::ZERO; NUM_STATE_LIMBS];
                let kp_idx = sig.stateful_leaf_idx;
                let tsw_ctr = sig.layers[0].tsw_ctr;
                for i in 0..6 {
                    row[COL_AUX + i] = Goldilocks::from_u64_reduced(((kp_idx >> i) & 1) as u64);
                }
                for i in 0..32 {
                    row[COL_AUX + 6 + i] =
                        Goldilocks::from_u64_reduced(((tsw_ctr >> i) & 1) as u64);
                }
                let kp_ctr = ((kp_idx as u64) << 32) | (tsw_ctr as u64);
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    pk.pk_root[0],
                    pk.pk_root[1],
                    pk.pk_root[2],
                    pk.pk_root[3],
                    Goldilocks::from_u64_reduced(DOMAIN_H_MSG_STATEFUL),
                    Goldilocks::from_u64_reduced(kp_ctr),
                    mu[4],
                    Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_CUR_ROOT..ST_CUR_ROOT + 4].copy_from_slice(&pk.pk_root);
                next[ST_KP_IDX] = Goldilocks::from_u64_reduced(kp_idx as u64);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::StatefulHmsgBlock1 => {
                row[COL_AUX..COL_AUX + 4].copy_from_slice(&sig.r_rand);
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += sig.r_rand[i];
                    st_in[4 + i] += mu[i];
                }
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::StatefulHmsgSqueeze => {
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                st_in[0] += Goldilocks::ONE;
                let perm_out = fill_row_perm(row, st_in);
                let mut hmsg = [Goldilocks::ZERO; 5];
                hmsg.copy_from_slice(&perm_out[0..5]);
                debug_assert_eq!(
                    hmsg,
                    compute_hmsg_stateful(
                        pk.pk_seed,
                        pk.pk_root,
                        sig.r_rand,
                        mu,
                        sig.stateful_leaf_idx,
                        sig.layers[0].tsw_ctr
                    )
                );
                cur_digits = match extract_wots_digits_checked(&hmsg) {
                    Some(digits) => digits,
                    None => panic!("trace requires a valid signature hmsg"),
                };
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
                next[ST_REM_PACK..ST_REM_PACK + 6].fill(Goldilocks::ZERO);
                next[ST_ACC_OR_U1] = Goldilocks::ZERO;
            }
            StepOp::StatelessDeriveBlock0 => {
                next = [Goldilocks::ZERO; NUM_STATE_LIMBS];
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    pk.pk_root[0],
                    pk.pk_root[1],
                    pk.pk_root[2],
                    pk.pk_root[3],
                    Goldilocks::from_u64_reduced(DOMAIN_H_MSG_STATELESS),
                    mu[4],
                    Goldilocks::ZERO,
                    Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::StatelessDeriveBlock1 => {
                row[COL_AUX..COL_AUX + 4].copy_from_slice(&sig.r_rand);
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += sig.r_rand[i];
                    st_in[4 + i] += mu[i];
                }
                let perm_out = fill_row_perm(row, st_in);
                let (f_idxs, _, sq) =
                    match derive_stateless_fors_and_leaf_checked(pk.pk_seed, pk.pk_root, sig.r_rand, mu) {
                        Some(derived) => derived,
                        None => panic!("trace requires valid stateless derivation"),
                    };
                debug_assert_eq!(&perm_out[0..7], &sq);
                stateless_fors_idxs = f_idxs;
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
                next[ST_REM_PACK..ST_REM_PACK + 6].fill(Goldilocks::ZERO);
            }
            StepOp::StatelessDecompLimb { limb_idx } => {
                let l = limb_idx as usize;
                let v = state[ST_MAIN_SPONGE + l].to_canonical_u64();
                write_limb63_decomp_aux(row, v);
                if l < 4 {
                    // 7 8-bit FORS indices `7*l .. 7*l + 7`
                    for sub in 0..7 {
                        let j = 7 * l + sub;
                        let byte_val = (v >> (8 * sub)) & 0xFF;
                        let slot = j / 6;
                        let pos_in_slot = j % 6;
                        next[ST_REM_PACK + slot] +=
                            Goldilocks::from_u64_reduced(byte_val << (8 * pos_in_slot));
                    }
                } else if l == 4 {
                    for sub in 0..4 {
                        let j = 28 + sub;
                        let byte_val = (v >> (8 * sub)) & 0xFF;
                        let slot = j / 6;
                        let pos_in_slot = j % 6;
                        next[ST_REM_PACK + slot] +=
                            Goldilocks::from_u64_reduced(byte_val << (8 * pos_in_slot));
                    }
                } else if l == 5 {
                    let lo32 = v & 0xFFFF_FFFF;
                    next[ST_KP_IDX] = Goldilocks::from_u64_reduced(lo32 & 0xF);
                    next[ST_TREE_LO] = Goldilocks::from_u64_reduced(lo32 >> 4);
                } else if l == 6 {
                    let hi32 = v & 0xFFFF_FFFF;
                    next[ST_TREE_LO] += Goldilocks::from_u64_reduced((hi32 & 0xF) << 28);
                    next[ST_TREE_HI] = Goldilocks::from_u64_reduced(hi32 >> 4);
                }
            }
            StepOp::ForsRootsSpongeInit => {
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    state[ST_KP_IDX],
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                    Goldilocks::from_u64_reduced(FORS_TREES as u64),
                    Goldilocks::from_u64_reduced(DOMAIN_FORS_ROOTS),
                    Goldilocks::ZERO,
                    Goldilocks::ZERO,
                    Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::ForsLeafHash { tree_j, pack_slot } => {
                let j = tree_j as usize;
                let slot = pack_slot as usize;
                let idx_j = stateless_fors_idxs[j] as u64;
                let sec = sig.fors_openings[j].secret_val;
                row[COL_AUX..COL_AUX + 4].copy_from_slice(&sec);
                for k in 0..4 {
                    row[COL_AUX + 4 + k] = Goldilocks::from_u64_reduced((idx_j >> (2 * k)) & 3);
                }
                let prev_pack = state[ST_REM_PACK + slot].to_canonical_u64();
                debug_assert_eq!(prev_pack & 0xFF, idx_j);
                let quot = prev_pack >> 8;
                row[COL_AUX + 8] = Goldilocks::from_u64_reduced(quot);
                next[ST_REM_PACK + slot] = Goldilocks::from_u64_reduced(quot);

                let kp0 = state[ST_KP_IDX].to_canonical_u64();
                let global_fors_leaf = ((j as u64) << FORS_HEIGHT) | idx_j;
                let st_in = [
                    sec[0],
                    sec[1],
                    sec[2],
                    sec[3],
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    Goldilocks::from_u64_reduced(DOMAIN_FORS_LEAF),
                    Goldilocks::from_u64_reduced((kp0 << 24) | global_fors_leaf),
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                for i in 0..4 {
                    next[ST_WORK + i] = perm_out[i] + sec[i];
                }
                next[ST_CURSOR_IDX] = Goldilocks::from_u64_reduced(idx_j);
            }
            StepOp::ForsMerkleBlockA { tree_j, lvl } => {
                let j = tree_j as usize;
                let l = lvl as usize;
                let cur_idx = state[ST_CURSOR_IDX].to_canonical_u64() as u32;
                let bit = cur_idx & 1;
                let parent_idx = cur_idx >> 1;
                let sib = sig.fors_openings[j].auth_path[l];
                row[COL_AUX] = Goldilocks::from_u64_reduced(bit as u64);
                row[COL_AUX + 1] = Goldilocks::from_u64_reduced(parent_idx as u64);
                row[COL_AUX + 2..COL_AUX + 6].copy_from_slice(&sib);

                let mut node = [Goldilocks::ZERO; 4];
                node.copy_from_slice(&state[ST_WORK..ST_WORK + 4]);
                let (left, right) = if bit == 0 { (node, sib) } else { (sib, node) };
                let kp0 = state[ST_KP_IDX].to_canonical_u64() as u32;
                let addr_node = ((j as u32) << (FORS_HEIGHT - 1 - l)) + parent_idx;
                let node_idx_combined = (kp0 << 16) | addr_node;
                let meta0 = (((l + 1) as u64) << 32) | (node_idx_combined as u64);
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    left[0],
                    left[1],
                    left[2],
                    left[3],
                    Goldilocks::from_u64_reduced(DOMAIN_FORS_NODE),
                    Goldilocks::from_u64_reduced(meta0),
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_SUB_SPONGE..ST_SUB_SPONGE + 12].copy_from_slice(&perm_out);
                // Store `right[0..4]` in `ST_WORK` until Block B!
                next[ST_WORK..ST_WORK + 4].copy_from_slice(&right);
                next[ST_CURSOR_IDX] = Goldilocks::from_u64_reduced(parent_idx as u64);
            }
            StepOp::ForsMerkleBlockB {
                lvl: _,
                is_tree_last,
                is_odd_tree,
            } => {
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_SUB_SPONGE..ST_SUB_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += state[ST_WORK + i];
                }
                st_in[4] += Goldilocks::ONE;
                st_in[5] += Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);
                let perm_out = fill_row_perm(row, st_in);
                if is_tree_last && !is_odd_tree {
                    // Save even FORS tree root in `ST_CUR_ROOT[0..4]` while odd tree runs!
                    next[ST_CUR_ROOT..ST_CUR_ROOT + 4].copy_from_slice(&perm_out[0..4]);
                } else {
                    next[ST_WORK..ST_WORK + 4].copy_from_slice(&perm_out[0..4]);
                }
            }
            StepOp::ForsRootsPairAbsorb { pair_idx } => {
                if pair_idx as usize == (FORS_TREES / 2) - 1 {
                    for s in 0..6 {
                        debug_assert_eq!(state[ST_REM_PACK + s], Goldilocks::ZERO);
                    }
                }
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += state[ST_CUR_ROOT + i];
                    st_in[4 + i] += state[ST_WORK + i];
                }
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::ForsRootsFinalSqueeze => {
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                st_in[0] += Goldilocks::ONE;
                let perm_out = fill_row_perm(row, st_in);
                next[ST_CUR_ROOT..ST_CUR_ROOT + 4].copy_from_slice(&perm_out[0..4]);
            }
            StepOp::DetTreeHmsgBlock0 { layer } => {
                let kp_u64 = state[ST_KP_IDX].to_canonical_u64();
                let layer_kp = ((layer as u64) << 32) | kp_u64;
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    pk.pk_root[0],
                    pk.pk_root[1],
                    pk.pk_root[2],
                    pk.pk_root[3],
                    Goldilocks::from_u64_reduced(DOMAIN_H_MSG_DET_TREE),
                    Goldilocks::from_u64_reduced(layer_kp),
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::DetTreeHmsgBlock1 { layer } => {
                let lsig = &sig.layers[layer as usize];
                let tsw_ctr = lsig.tsw_ctr;
                for i in 0..32 {
                    row[COL_AUX + i] = Goldilocks::from_u64_reduced(((tsw_ctr >> i) & 1) as u64);
                }
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += state[ST_CUR_ROOT + i];
                }
                st_in[4] += Goldilocks::from_u64_reduced(tsw_ctr as u64);
                st_in[5] += Goldilocks::ONE;
                let perm_out = fill_row_perm(row, st_in);
                let mut hmsg = [Goldilocks::ZERO; 5];
                hmsg.copy_from_slice(&perm_out[0..5]);
                let tree_u64 = state[ST_TREE_LO].to_canonical_u64()
                    | (state[ST_TREE_HI].to_canonical_u64() << 32);
                let mut cur_rt = [Goldilocks::ZERO; 4];
                cur_rt.copy_from_slice(&state[ST_CUR_ROOT..ST_CUR_ROOT + 4]);
                debug_assert_eq!(
                    hmsg,
                    compute_hmsg_det_tree(
                        pk.pk_seed,
                        pk.pk_root,
                        layer as u32,
                        tree_u64,
                        state[ST_KP_IDX].to_canonical_u64() as u32,
                        tsw_ctr,
                        cur_rt
                    )
                );
                cur_digits = match extract_wots_digits_checked(&hmsg) {
                    Some(digits) => digits,
                    None => panic!("trace requires a valid signature hmsg"),
                };
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
                next[ST_REM_PACK..ST_REM_PACK + 6].fill(Goldilocks::ZERO);
                next[ST_ACC_OR_U1] = Goldilocks::ZERO;
            }
            StepOp::HmsgDecompLimb { limb_idx } => {
                let l = limb_idx as usize;
                let v = state[ST_MAIN_SPONGE + l].to_canonical_u64();
                write_limb63_decomp_aux(row, v);
                let count = if l < 4 { 31 } else { 4 };
                let base_r = 31 * l;
                let mut d_sum = 0u64;
                for i in 0..count {
                    let r = base_r + i;
                    let d_r = ((v >> (2 * i)) & 3) as u8;
                    debug_assert_eq!(d_r, cur_digits[r]);
                    d_sum += d_r as u64;
                    let slot = wots_pack_slot(r as u8) as usize;
                    let slot_start = match slot {
                        0 => 0,
                        1 => 26,
                        2 => 52,
                        3 => 78,
                        _ => 103,
                    };
                    let pos = r - slot_start;
                    next[ST_REM_PACK + slot] +=
                        Goldilocks::from_u64_reduced(((3 - d_r) as u64) << (2 * pos));
                }
                next[ST_ACC_OR_U1] = state[ST_ACC_OR_U1] + Goldilocks::from_u64_reduced(d_sum);
                if l == 4 {
                    debug_assert_eq!(
                        next[ST_ACC_OR_U1],
                        Goldilocks::from_u64_reduced(WOTS_TARGET_SUM as u64)
                    );
                }
            }
            StepOp::WotsTellInit { layer } => {
                let kp_u64 = state[ST_KP_IDX].to_canonical_u64();
                let layer_kp = ((layer as u64) << 32) | kp_u64;
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    Goldilocks::from_u64_reduced(layer_kp),
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                    Goldilocks::from_u64_reduced(WOTS_CHAINS as u64),
                    Goldilocks::from_u64_reduced(DOMAIN_WOTS_PK),
                    Goldilocks::ZERO,
                    Goldilocks::ZERO,
                    Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV),
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::WotsChainStep0 {
                layer,
                chain,
                pack_slot,
            } => {
                let r = chain as usize;
                let slot = pack_slot as usize;
                let d_r = cur_digits[r];
                let (u0, u1, u2) = match d_r {
                    0 => (0u64, 0u64, 0u64),
                    1 => (1u64, 0u64, 0u64),
                    2 => (1u64, 1u64, 0u64),
                    _ => (1u64, 1u64, 1u64),
                };
                let wots_val = sig.layers[layer as usize].wots_chains[r];
                row[COL_AUX..COL_AUX + 4].copy_from_slice(&wots_val);
                row[COL_AUX + 4] = Goldilocks::from_u64_reduced(u0);
                row[COL_AUX + 5] = Goldilocks::from_u64_reduced(u1);
                row[COL_AUX + 6] = Goldilocks::from_u64_reduced(u2);

                let prev_pack = state[ST_REM_PACK + slot].to_canonical_u64();
                debug_assert_eq!(prev_pack & 3, (3 - d_r) as u64);
                let quot = prev_pack >> 2;
                row[COL_AUX + 7] = Goldilocks::from_u64_reduced(quot);
                next[ST_REM_PACK + slot] = Goldilocks::from_u64_reduced(quot);

                let kp_u32 = state[ST_KP_IDX].to_canonical_u64() as u32;
                let addr_limb = pack_wots_addr_limb(layer as u32, kp_u32, chain as u32, 0);
                let st_in = [
                    wots_val[0],
                    wots_val[1],
                    wots_val[2],
                    wots_val[3],
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    Goldilocks::from_u64_reduced(DOMAIN_WOTS_STEP),
                    addr_limb,
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                for i in 0..4 {
                    let ff = perm_out[i] + wots_val[i];
                    next[ST_WORK + i] = if u0 == 1 { wots_val[i] } else { ff };
                }
                next[ST_ACC_OR_U1] = Goldilocks::from_u64_reduced(u1);
                next[ST_WOTS_U2] = Goldilocks::from_u64_reduced(u2);
            }
            StepOp::WotsChainStep1 { layer, chain } => {
                let u1 = state[ST_ACC_OR_U1].to_canonical_u64();
                let mut cur = [Goldilocks::ZERO; 4];
                cur.copy_from_slice(&state[ST_WORK..ST_WORK + 4]);
                let kp_u32 = state[ST_KP_IDX].to_canonical_u64() as u32;
                let addr_limb = pack_wots_addr_limb(layer as u32, kp_u32, chain as u32, 1);
                let st_in = [
                    cur[0],
                    cur[1],
                    cur[2],
                    cur[3],
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    Goldilocks::from_u64_reduced(DOMAIN_WOTS_STEP),
                    addr_limb,
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                for i in 0..4 {
                    let ff = perm_out[i] + cur[i];
                    next[ST_WORK + i] = if u1 == 1 { cur[i] } else { ff };
                }
            }
            StepOp::WotsChainStep2 {
                layer,
                chain,
                is_odd,
            } => {
                let u2 = state[ST_WOTS_U2].to_canonical_u64();
                let mut cur = [Goldilocks::ZERO; 4];
                cur.copy_from_slice(&state[ST_WORK..ST_WORK + 4]);
                let kp_u32 = state[ST_KP_IDX].to_canonical_u64() as u32;
                let addr_limb = pack_wots_addr_limb(layer as u32, kp_u32, chain as u32, 2);
                let st_in = [
                    cur[0],
                    cur[1],
                    cur[2],
                    cur[3],
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    Goldilocks::from_u64_reduced(DOMAIN_WOTS_STEP),
                    addr_limb,
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                let mut ep = [Goldilocks::ZERO; 4];
                for i in 0..4 {
                    let ff = perm_out[i] + cur[i];
                    ep[i] = if u2 == 1 { cur[i] } else { ff };
                }
                // Verify endpoint matches standalone `wots_step_hash_injective`!
                #[cfg(debug_assertions)]
                {
                    let tree_u64 = state[ST_TREE_LO].to_canonical_u64()
                        | (state[ST_TREE_HI].to_canonical_u64() << 32);
                    let mut ref_cur = sig.layers[layer as usize].wots_chains[chain as usize];
                    for step in (cur_digits[chain as usize] as u32)..3 {
                        ref_cur = wots_step_hash_injective(
                            pk.pk_seed,
                            ref_cur,
                            layer as u32,
                            tree_u64,
                            kp_u32,
                            chain as u32,
                            step,
                        );
                    }
                    debug_assert_eq!(ep, ref_cur);
                }
                if !is_odd {
                    next[ST_SUB_SPONGE..ST_SUB_SPONGE + 4].copy_from_slice(&ep);
                } else {
                    next[ST_WORK..ST_WORK + 4].copy_from_slice(&ep);
                }
            }
            StepOp::WotsTellPairAbsorb { pair_idx } => {
                if pair_idx as usize == (WOTS_CHAINS / 2) - 1 {
                    for s in 0..5 {
                        debug_assert_eq!(state[ST_REM_PACK + s], Goldilocks::ZERO);
                    }
                }
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += state[ST_SUB_SPONGE + i];
                    st_in[4 + i] += state[ST_WORK + i];
                }
                let perm_out = fill_row_perm(row, st_in);
                next[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].copy_from_slice(&perm_out);
            }
            StepOp::WotsTellFinalSqueeze => {
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12]);
                st_in[0] += Goldilocks::ONE;
                let perm_out = fill_row_perm(row, st_in);
                next[ST_WORK..ST_WORK + 4].copy_from_slice(&perm_out[0..4]);
                next[ST_CURSOR_IDX] = state[ST_KP_IDX];
            }
            StepOp::XmssMerkleBlockA { layer, lvl } => {
                let cur_idx = state[ST_CURSOR_IDX].to_canonical_u64() as u32;
                let bit = cur_idx & 1;
                let parent_idx = cur_idx >> 1;
                let sib = sig.layers[layer as usize].merkle_path[lvl as usize];
                row[COL_AUX] = Goldilocks::from_u64_reduced(bit as u64);
                row[COL_AUX + 1] = Goldilocks::from_u64_reduced(parent_idx as u64);
                row[COL_AUX + 2..COL_AUX + 6].copy_from_slice(&sib);

                let mut node = [Goldilocks::ZERO; 4];
                node.copy_from_slice(&state[ST_WORK..ST_WORK + 4]);
                let (left, right) = if bit == 0 { (node, sib) } else { (sib, node) };
                let meta0 =
                    ((layer as u64) << 48) | (((lvl as u64) + 1) << 32) | (parent_idx as u64);
                let st_in = [
                    pk.pk_seed[0],
                    pk.pk_seed[1],
                    pk.pk_seed[2],
                    pk.pk_seed[3],
                    left[0],
                    left[1],
                    left[2],
                    left[3],
                    Goldilocks::from_u64_reduced(DOMAIN_MERKLE_NODE),
                    Goldilocks::from_u64_reduced(meta0),
                    state[ST_TREE_LO],
                    state[ST_TREE_HI],
                ];
                let perm_out = fill_row_perm(row, st_in);
                next[ST_SUB_SPONGE..ST_SUB_SPONGE + 12].copy_from_slice(&perm_out);
                next[ST_WORK..ST_WORK + 4].copy_from_slice(&right);
                next[ST_CURSOR_IDX] = Goldilocks::from_u64_reduced(parent_idx as u64);
            }
            StepOp::XmssMerkleBlockB {
                is_layer_last,
                is_top_final,
            } => {
                let mut st_in = [Goldilocks::ZERO; 12];
                st_in.copy_from_slice(&state[ST_SUB_SPONGE..ST_SUB_SPONGE + 12]);
                for i in 0..4 {
                    st_in[i] += state[ST_WORK + i];
                }
                st_in[4] += Goldilocks::ONE;
                st_in[5] += Goldilocks::from_u64_reduced(POSEIDON2_CONST_IV);
                let perm_out = fill_row_perm(row, st_in);

                if !is_layer_last {
                    next[ST_WORK..ST_WORK + 4].copy_from_slice(&perm_out[0..4]);
                } else if is_top_final {
                    debug_assert_eq!(state[ST_CURSOR_IDX], Goldilocks::ZERO);
                    debug_assert_eq!(&perm_out[0..4], &pk.pk_root);
                    next = [Goldilocks::ZERO; NUM_STATE_LIMBS];
                } else {
                    // Shift `(tree_lo, tree_hi)` down by `CORDUROY_SUBTREE_HEIGHT = 4` bits for `layer + 1`!
                    debug_assert_eq!(state[ST_CURSOR_IDX], Goldilocks::ZERO);
                    let tree_lo = state[ST_TREE_LO].to_canonical_u64();
                    let tree_hi = state[ST_TREE_HI].to_canonical_u64();
                    let next_kp = tree_lo & 0xF;
                    let lo_shifted = tree_lo >> 4;
                    let hi_low4 = tree_hi & 0xF;
                    let next_tree_hi = tree_hi >> 4;

                    for i in 0..4 {
                        row[COL_AUX + i] = Goldilocks::from_u64_reduced((next_kp >> i) & 1);
                    }
                    for i in 0..14 {
                        row[COL_AUX + 4 + i] =
                            Goldilocks::from_u64_reduced((lo_shifted >> (2 * i)) & 3);
                    }
                    for i in 0..2 {
                        row[COL_AUX + 18 + i] =
                            Goldilocks::from_u64_reduced((hi_low4 >> (2 * i)) & 3);
                    }
                    for i in 0..14 {
                        row[COL_AUX + 20 + i] =
                            Goldilocks::from_u64_reduced((next_tree_hi >> (2 * i)) & 3);
                    }

                    next[ST_CUR_ROOT..ST_CUR_ROOT + 4].copy_from_slice(&perm_out[0..4]);
                    next[ST_KP_IDX] = Goldilocks::from_u64_reduced(next_kp);
                    next[ST_TREE_LO] = Goldilocks::from_u64_reduced(lo_shifted | (hi_low4 << 28));
                    next[ST_TREE_HI] = Goldilocks::from_u64_reduced(next_tree_hi);
                }
            }
        }
        row[COL_NEXT_STATE..COL_NEXT_STATE + NUM_STATE_LIMBS].copy_from_slice(&next);
        state = next;
    }
    debug_assert_eq!(state, [Goldilocks::ZERO; NUM_STATE_LIMBS]);
}

// ============================================================================
// 2. Shared Prover & Verifier Algebraic Row-Constraint Evaluators
// ============================================================================

/// Shared field abstraction across `Goldilocks` (fast 8-byte Round-0 row sumcheck),
/// `GoldilocksExt2`, and `GoldilocksExt4` (`Hem` 256-bit row & verifier constraints).
