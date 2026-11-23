//! Execution trace layout (`C = 256` columns) and shared prover/verifier algebraic row-constraint
//! evaluator for `JortsPoseidon2` (`512` rows/signer) and `CorduroyPoseidon2` (`8,192` rows/signer).

use alloc::vec::Vec;

use crate::field::Goldilocks;
#[cfg(debug_assertions)]
use crate::sig::wots_step_hash_injective;
use crate::sig::{
    AggSigProfile, CORDUROY_NUM_LAYERS, CORDUROY_SUBTREE_HEIGHT, DOMAIN_FORS_LEAF,
    DOMAIN_FORS_NODE, DOMAIN_FORS_ROOTS, DOMAIN_H_MSG_DET_TREE, DOMAIN_H_MSG_STATEFUL,
    DOMAIN_H_MSG_STATELESS, DOMAIN_MERKLE_NODE, DOMAIN_WOTS_PK, DOMAIN_WOTS_STEP, Digest5,
    FORS_HEIGHT, FORS_TREES, JORTS_XMSS_HEIGHT, ValidatorPublicKey, ValidatorSignature,
    WOTS_CHAINS, WOTS_TARGET_SUM, compute_hmsg_det_tree, compute_hmsg_stateful,
    derive_stateless_fors_and_leaf_checked, extract_wots_digits_checked, pack_wots_addr_limb,
};
use crate::sponge::{
    POSEIDON2_CONST_IV, POSEIDON2_HALF_EXT_ROUNDS, POSEIDON2_INT_ROUNDS, poseidon2_apply_me,
    poseidon2_apply_mi, poseidon2_const_at, poseidon2_sbox7,
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

/// Fixed row count per signer (`512` for all `JortsPoseidon2` heights `6..=20`, `8,192` for `CorduroyPoseidon2`).
#[inline]
pub const fn rows_per_signer(profile: AggSigProfile) -> usize {
    if profile.is_jorts() { 512 } else { 8192 }
}

/// Deterministic step opcodes defining the per-signer state machine (`max aux = 38`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepOp {
    Idle,

    // --- Stateful `JortsPoseidon2` H_msg ---
    StatefulHmsgBlock0,
    /// Variable-height `JortsPoseidon2` (`height in 7..=20`): `aux[0..height]` Boolean bits of `kp_idx`
    /// + `aux[20..36]` 16 base-4 digits of 32-bit `tsw_ctr` (`<= 36 <= 38` aux columns).
    StatefulHmsgBlock0Var {
        height: u8,
    },
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

    match profile.jorts_xmss_height() {
        Some(jorts_height) => {
            if jorts_height == JORTS_XMSS_HEIGHT {
                prog.push(StepOp::StatefulHmsgBlock0);
            } else {
                prog.push(StepOp::StatefulHmsgBlock0Var {
                    height: jorts_height as u8,
                });
            }
            prog.push(StepOp::StatefulHmsgBlock1);
            prog.push(StepOp::StatefulHmsgSqueeze);
            for l in 0..5 {
                prog.push(StepOp::HmsgDecompLimb { limb_idx: l });
            }
            push_layer_wots_and_merkle(&mut prog, 0, jorts_height, true);
        }
        None => {
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
    StatefulHmsgBlock0Var {
        height: u8,
    },
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
        StepOp::StatefulHmsgBlock0Var { height } => (
            ConstraintKind::StatefulHmsgBlock0Var { height },
            Goldilocks::ZERO,
        ),
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

/// Compact `(kind_id, kind_arg)` encoding of a [`ConstraintKind`] matching `air_row_group_b.comp`.
#[cfg(feature = "vulkan")]
#[inline]
pub(crate) fn encode_constraint_kind(kind: ConstraintKind) -> (u32, u32) {
    match kind {
        ConstraintKind::Idle => (0, 0),
        ConstraintKind::StatefulHmsgBlock0 => (1, 0),
        ConstraintKind::StatefulHmsgBlock0Var { height } => (24, u32::from(height)),
        ConstraintKind::StatefulHmsgBlock1 => (2, 0),
        ConstraintKind::StatefulHmsgSqueeze => (3, 0),
        ConstraintKind::StatelessDeriveBlock0 => (4, 0),
        ConstraintKind::StatelessDeriveBlock1 => (5, 0),
        ConstraintKind::StatelessDecompLimb { limb_idx } => (6, u32::from(limb_idx)),
        ConstraintKind::ForsRootsSpongeInit => (7, 0),
        ConstraintKind::ForsLeafHash { pack_slot } => (8, u32::from(pack_slot)),
        ConstraintKind::ForsMerkleBlockA => (9, 0),
        ConstraintKind::ForsMerkleBlockB {
            is_tree_last,
            is_odd_tree,
        } => (10, u32::from(is_tree_last) | (u32::from(is_odd_tree) << 1)),
        ConstraintKind::ForsRootsPairAbsorb { is_last_pair } => (11, u32::from(is_last_pair)),
        ConstraintKind::ForsRootsFinalSqueeze => (12, 0),
        ConstraintKind::DetTreeHmsgBlock0 => (13, 0),
        ConstraintKind::DetTreeHmsgBlock1 => (14, 0),
        ConstraintKind::HmsgDecompLimb { limb_idx } => (15, u32::from(limb_idx)),
        ConstraintKind::WotsTellInit => (16, 0),
        ConstraintKind::WotsChainStep0 { pack_slot } => (17, u32::from(pack_slot)),
        ConstraintKind::WotsChainStep1 => (18, 0),
        ConstraintKind::WotsChainStep2 { is_odd } => (19, u32::from(is_odd)),
        ConstraintKind::WotsTellPairAbsorb { is_last_pair } => (20, u32::from(is_last_pair)),
        ConstraintKind::WotsTellFinalSqueeze => (21, 0),
        ConstraintKind::XmssMerkleBlockA => (22, 0),
        ConstraintKind::XmssMerkleBlockB {
            is_layer_last,
            is_top_final,
        } => (
            23,
            u32::from(is_layer_last) | (u32::from(is_top_final) << 1),
        ),
    }
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
            StepOp::StatefulHmsgBlock0Var { height } => {
                next = [Goldilocks::ZERO; NUM_STATE_LIMBS];
                let h = height as usize;
                debug_assert!((7..=20).contains(&h));
                let kp_idx = sig.stateful_leaf_idx;
                let tsw_ctr = sig.layers[0].tsw_ctr;
                for i in 0..h {
                    row[COL_AUX + i] = Goldilocks::from_u64_reduced(((kp_idx >> i) & 1) as u64);
                }
                for j in 0..16 {
                    row[COL_AUX + 20 + j] =
                        Goldilocks::from_u64_reduced(((tsw_ctr >> (2 * j)) & 3) as u64);
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
                let (f_idxs, _, sq) = match derive_stateless_fors_and_leaf_checked(
                    pk.pk_seed, pk.pk_root, sig.r_rand, mu,
                ) {
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
                    next[ST_WORK + i] = perm_out[i]
                        + sec[i]
                        + (st_in[4 + i] + st_in[4 + i])
                        + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
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
                    let ff = perm_out[i]
                        + wots_val[i]
                        + (st_in[4 + i] + st_in[4 + i])
                        + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
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
                    let ff = perm_out[i]
                        + cur[i]
                        + (st_in[4 + i] + st_in[4 + i])
                        + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
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
                    let ff = perm_out[i]
                        + cur[i]
                        + (st_in[4 + i] + st_in[4 + i])
                        + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
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
                    let hi_low_nibble = tree_hi & 0xF;
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
                            Goldilocks::from_u64_reduced((hi_low_nibble >> (2 * i)) & 3);
                    }
                    for i in 0..14 {
                        row[COL_AUX + 20 + i] =
                            Goldilocks::from_u64_reduced((next_tree_hi >> (2 * i)) & 3);
                    }

                    next[ST_CUR_ROOT..ST_CUR_ROOT + 4].copy_from_slice(&perm_out[0..4]);
                    next[ST_KP_IDX] = Goldilocks::from_u64_reduced(next_kp);
                    next[ST_TREE_LO] =
                        Goldilocks::from_u64_reduced(lo_shifted | (hi_low_nibble << 28));
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

/// Shared field abstraction across `Goldilocks` (base-field trace generation) and
/// Quintic `Fp5` ([`crate::hem_quintic::QuinticFp5`], `HemQuintic128` row & verifier constraints).
pub trait TraceField:
    Copy
    + Default
    + PartialEq
    + Eq
    + core::ops::Add<Output = Self>
    + core::ops::AddAssign
    + core::ops::Sub<Output = Self>
    + core::ops::Mul<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    fn from_base(b: Goldilocks) -> Self;
    fn from_u64(v: u64) -> Self;
    fn mul_base_f(self, s: Goldilocks) -> Self;
    fn sbox7(self) -> Self;
    fn apply_me(st: &mut [Self; 12]);
    fn apply_mi(st: &mut [Self; 12]);
}

impl TraceField for Goldilocks {
    const ZERO: Self = Self::ZERO;
    const ONE: Self = Self::ONE;
    #[inline(always)]
    fn from_base(b: Goldilocks) -> Self {
        b
    }
    #[inline(always)]
    fn from_u64(v: u64) -> Self {
        Self::from_u64_reduced(v)
    }
    #[inline(always)]
    fn mul_base_f(self, s: Goldilocks) -> Self {
        self * s
    }
    #[inline(always)]
    fn sbox7(self) -> Self {
        poseidon2_sbox7(self)
    }
    #[inline(always)]
    fn apply_me(st: &mut [Self; 12]) {
        poseidon2_apply_me(st);
    }
    #[inline(always)]
    fn apply_mi(st: &mut [Self; 12]) {
        poseidon2_apply_mi(st);
    }
}

/// Number of unconditional Group-A + boundary constraints per row (`118 + 2 * 44 = 206`).
pub const NUM_GROUP_A_AND_BOUNDARY_CONSTRAINTS: usize = 118 + 2 * NUM_STATE_LIMBS;

#[inline(always)]
fn quartic_base4_generic<F: TraceField>(d: F) -> F {
    let d1 = d - F::ONE;
    let d2 = d - F::from_u64(2);
    let d3 = d - F::from_u64(3);
    (d * d1) * (d2 * d3)
}

#[inline(always)]
fn bool_check_generic<F: TraceField>(b: F) -> F {
    b * (F::ONE - b)
}

#[inline]
fn eval_group_a_and_boundaries_generic<F: TraceField>(
    cols: &[F; NUM_TRACE_COLS],
    is_row_first: F,
    is_row_last: F,
    mut emit_eq: impl FnMut(usize, F),
) -> [F; 12] {
    let mut c_idx = 0usize;
    let mut st = [F::ZERO; 12];
    st.copy_from_slice(&cols[COL_ST_IN..COL_ST_IN + 12]);
    F::apply_me(&mut st);
    let mut sb_idx = 0usize;
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let rc = F::from_base(poseidon2_const_at(0, r as u64, lane as u64));
            let sbox_val = cols[COL_SBOX_OUT + sb_idx];
            emit_eq(c_idx, (*lane_val + rc).sbox7() - sbox_val);
            c_idx += 1;
            *lane_val = sbox_val;
            sb_idx += 1;
        }
        F::apply_me(&mut st);
    }
    for r in 0..POSEIDON2_INT_ROUNDS {
        let rc = F::from_base(poseidon2_const_at(1, r as u64, 0));
        let sbox_val = cols[COL_SBOX_OUT + sb_idx];
        emit_eq(c_idx, (st[0] + rc).sbox7() - sbox_val);
        c_idx += 1;
        st[0] = sbox_val;
        sb_idx += 1;
        F::apply_mi(&mut st);
    }
    for r in 0..POSEIDON2_HALF_EXT_ROUNDS {
        for (lane, lane_val) in st.iter_mut().enumerate() {
            let rc = F::from_base(poseidon2_const_at(2, r as u64, lane as u64));
            let sbox_val = cols[COL_SBOX_OUT + sb_idx];
            emit_eq(c_idx, (*lane_val + rc).sbox7() - sbox_val);
            c_idx += 1;
            *lane_val = sbox_val;
            sb_idx += 1;
        }
        F::apply_me(&mut st);
    }

    eval_boundaries_generic(cols, is_row_first, is_row_last, emit_eq);
    st
}

fn eval_boundaries_generic<F: TraceField>(
    cols: &[F; NUM_TRACE_COLS],
    is_row_first: F,
    is_row_last: F,
    mut emit_eq: impl FnMut(usize, F),
) {
    let mut c_idx = 118;
    let prev = &cols[COL_PREV_STATE..COL_PREV_STATE + NUM_STATE_LIMBS];
    let next = &cols[COL_NEXT_STATE..COL_NEXT_STATE + NUM_STATE_LIMBS];
    let rf_zero = is_row_first == F::ZERO;
    let rl_zero = is_row_last == F::ZERO;
    if rf_zero && rl_zero {
        for _ in 0..(2 * NUM_STATE_LIMBS) {
            emit_eq(c_idx, F::ZERO);
            c_idx += 1;
        }
    } else {
        for j in 0..NUM_STATE_LIMBS {
            emit_eq(
                c_idx,
                if rf_zero {
                    F::ZERO
                } else {
                    is_row_first * prev[j]
                },
            );
            c_idx += 1;
            emit_eq(
                c_idx,
                if rl_zero {
                    F::ZERO
                } else {
                    is_row_last * next[j]
                },
            );
            c_idx += 1;
        }
    }
    debug_assert_eq!(c_idx, NUM_GROUP_A_AND_BOUNDARY_CONSTRAINTS);
}

/// Row values one opcode's transition constraints read: trace column groups, the recomputed
/// permutation output, and the signer's public inputs.
#[derive(Clone, Copy)]
struct OpRowInputs<'a, F: TraceField> {
    prev: &'a [F],
    next: &'a [F],
    aux: &'a [F],
    st_in: &'a [F],
    perm_out: &'a [F; 12],
    pk_seed: &'a [F; 4],
    pk_root: &'a [F; 4],
    mu: &'a [F; 5],
}

#[inline]
fn eval_single_op_constraints_generic<F: TraceField, E: FnMut(F)>(
    kind: ConstraintKind,
    step_c0: F,
    row: OpRowInputs<'_, F>,
    mut emit_op: E,
) {
    let OpRowInputs {
        prev,
        next,
        aux,
        st_in,
        perm_out,
        pk_seed,
        pk_root,
        mu,
    } = row;
    let check_carry_unchanged = |mask: &[bool; NUM_STATE_LIMBS], mut emit: E| {
        for j in 0..NUM_STATE_LIMBS {
            if mask[j] {
                emit(next[j] - prev[j]);
            }
        }
    };
    let check_zero_elsewhere = |mask: &[bool; NUM_STATE_LIMBS], mut emit: E| {
        for j in 0..NUM_STATE_LIMBS {
            if mask[j] {
                emit(next[j]);
            }
        }
    };

    match kind {
        ConstraintKind::Idle => {
            for &next_item in next.iter().take(NUM_STATE_LIMBS) {
                emit_op(next_item);
            }
        }
        ConstraintKind::StatefulHmsgBlock0 => {
            let mut kp_val = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(6) {
                emit_op(bool_check_generic(aux_i));
                kp_val += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << i));
            }
            let mut ctr_val = F::ZERO;
            for i in 0..32 {
                emit_op(bool_check_generic(aux[6 + i]));
                ctr_val += aux[6 + i].mul_base_f(Goldilocks::from_u64_reduced(1u64 << i));
            }
            let kp_ctr = kp_val.mul_base_f(Goldilocks::from_u64_reduced(1u64 << 32)) + ctr_val;
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - pk_root[i]);
                emit_op(next[ST_CUR_ROOT + i] - pk_root[i]);
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_H_MSG_STATEFUL));
            emit_op(st_in[9] - kp_ctr);
            emit_op(st_in[10] - mu[4]);
            emit_op(st_in[11] - F::from_u64(POSEIDON2_CONST_IV));
            emit_op(next[ST_KP_IDX] - kp_val);
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut zero_mask = [true; NUM_STATE_LIMBS];
            zero_mask[ST_CUR_ROOT..ST_CUR_ROOT + 4].fill(false);
            zero_mask[ST_KP_IDX] = false;
            zero_mask[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_zero_elsewhere(&zero_mask, emit_op);
        }
        ConstraintKind::StatefulHmsgBlock0Var { height } => {
            let h = height as usize;
            let mut kp_val = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(h) {
                emit_op(bool_check_generic(aux_i));
                kp_val += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << i));
            }
            let mut ctr_val = F::ZERO;
            for j in 0..16 {
                let d = aux[20 + j];
                emit_op(quartic_base4_generic(d));
                ctr_val += d.mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * j)));
            }
            let kp_ctr = kp_val.mul_base_f(Goldilocks::from_u64_reduced(1u64 << 32)) + ctr_val;
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - pk_root[i]);
                emit_op(next[ST_CUR_ROOT + i] - pk_root[i]);
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_H_MSG_STATEFUL));
            emit_op(st_in[9] - kp_ctr);
            emit_op(st_in[10] - mu[4]);
            emit_op(st_in[11] - F::from_u64(POSEIDON2_CONST_IV));
            emit_op(next[ST_KP_IDX] - kp_val);
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut zero_mask = [true; NUM_STATE_LIMBS];
            zero_mask[ST_CUR_ROOT..ST_CUR_ROOT + 4].fill(false);
            zero_mask[ST_KP_IDX] = false;
            zero_mask[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_zero_elsewhere(&zero_mask, emit_op);
        }
        ConstraintKind::StatefulHmsgBlock1 => {
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_MAIN_SPONGE + i] + aux[i]));
                emit_op(st_in[4 + i] - (prev[ST_MAIN_SPONGE + 4 + i] + mu[i]));
                emit_op(st_in[8 + i] - prev[ST_MAIN_SPONGE + 8 + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::StatefulHmsgSqueeze => {
            emit_op(st_in[0] - (prev[ST_MAIN_SPONGE] + F::ONE));
            for i in 1..12 {
                emit_op(st_in[i] - prev[ST_MAIN_SPONGE + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            for s in 0..6 {
                emit_op(next[ST_REM_PACK + s]);
            }
            emit_op(next[ST_ACC_OR_U1]);
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_REM_PACK..ST_REM_PACK + 6].fill(false);
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            carry[ST_ACC_OR_U1] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::StatelessDeriveBlock0 => {
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - pk_root[i]);
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_H_MSG_STATELESS));
            emit_op(st_in[9] - mu[4]);
            emit_op(st_in[10]);
            emit_op(st_in[11] - F::from_u64(POSEIDON2_CONST_IV));
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut zero_mask = [true; NUM_STATE_LIMBS];
            zero_mask[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_zero_elsewhere(&zero_mask, emit_op);
        }
        ConstraintKind::StatelessDeriveBlock1 => {
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_MAIN_SPONGE + i] + aux[i]));
                emit_op(st_in[4 + i] - (prev[ST_MAIN_SPONGE + 4 + i] + mu[i]));
                emit_op(st_in[8 + i] - prev[ST_MAIN_SPONGE + 8 + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            for s in 0..6 {
                emit_op(next[ST_REM_PACK + s]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            carry[ST_REM_PACK..ST_REM_PACK + 6].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::StatelessDecompLimb { limb_idx } => {
            let l = limb_idx as usize;
            let mut recon = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(31) {
                emit_op(quartic_base4_generic(aux_i));
                recon += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * i)));
            }
            emit_op(bool_check_generic(aux[31]));
            recon += aux[31].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 62));
            emit_op(prev[ST_MAIN_SPONGE + l] - recon);

            let mut expected_next = [F::ZERO; NUM_STATE_LIMBS];
            expected_next.copy_from_slice(prev);
            if l < 4 {
                for sub in 0..7 {
                    let j = 7 * l + sub;
                    let b_base = 4 * sub;
                    let byte_val = aux[b_base]
                        + aux[b_base + 1].mul_base_f(Goldilocks::from_u64_reduced(4))
                        + aux[b_base + 2].mul_base_f(Goldilocks::from_u64_reduced(16))
                        + aux[b_base + 3].mul_base_f(Goldilocks::from_u64_reduced(64));
                    let slot = j / 6;
                    let pos_in_slot = j % 6;
                    expected_next[ST_REM_PACK + slot] += byte_val
                        .mul_base_f(Goldilocks::from_u64_reduced(1u64 << (8 * pos_in_slot)));
                }
            } else if l == 4 {
                for sub in 0..4 {
                    let j = 28 + sub;
                    let b_base = 4 * sub;
                    let byte_val = aux[b_base]
                        + aux[b_base + 1].mul_base_f(Goldilocks::from_u64_reduced(4))
                        + aux[b_base + 2].mul_base_f(Goldilocks::from_u64_reduced(16))
                        + aux[b_base + 3].mul_base_f(Goldilocks::from_u64_reduced(64));
                    let slot = j / 6;
                    let pos_in_slot = j % 6;
                    expected_next[ST_REM_PACK + slot] += byte_val
                        .mul_base_f(Goldilocks::from_u64_reduced(1u64 << (8 * pos_in_slot)));
                }
            } else if l == 5 {
                expected_next[ST_KP_IDX] =
                    aux[0] + aux[1].mul_base_f(Goldilocks::from_u64_reduced(4));
                let mut hi28 = F::ZERO;
                for (i, &aux_i) in aux.iter().enumerate().take(16).skip(2) {
                    hi28 += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * (i - 2))));
                }
                expected_next[ST_TREE_LO] = hi28;
            } else if l == 6 {
                let low_nibble = aux[0] + aux[1].mul_base_f(Goldilocks::from_u64_reduced(4));
                expected_next[ST_TREE_LO] = prev[ST_TREE_LO]
                    + low_nibble.mul_base_f(Goldilocks::from_u64_reduced(1u64 << 28));
                let mut hi28 = F::ZERO;
                for (i, &aux_i) in aux.iter().enumerate().take(16).skip(2) {
                    hi28 += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * (i - 2))));
                }
                expected_next[ST_TREE_HI] = hi28;
            }
            for j in 0..NUM_STATE_LIMBS {
                emit_op(next[j] - expected_next[j]);
            }
        }
        ConstraintKind::ForsRootsSpongeInit => {
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
            }
            emit_op(st_in[4] - prev[ST_KP_IDX]);
            emit_op(st_in[5] - prev[ST_TREE_LO]);
            emit_op(st_in[6] - prev[ST_TREE_HI]);
            emit_op(st_in[7] - F::from_u64(FORS_TREES as u64));
            emit_op(st_in[8] - F::from_u64(DOMAIN_FORS_ROOTS));
            emit_op(st_in[9]);
            emit_op(st_in[10]);
            emit_op(st_in[11] - F::from_u64(POSEIDON2_CONST_IV));
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::ForsLeafHash { pack_slot } => {
            let slot = pack_slot as usize;
            let mut idx_j = F::ZERO;
            for k in 0..4 {
                emit_op(quartic_base4_generic(aux[4 + k]));
                idx_j += aux[4 + k].mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * k)));
            }
            let quot = aux[8];
            emit_op(
                prev[ST_REM_PACK + slot]
                    - (idx_j + quot.mul_base_f(Goldilocks::from_u64_reduced(256))),
            );
            emit_op(next[ST_REM_PACK + slot] - quot);

            let global_fors_leaf = step_c0 + idx_j;
            let tweak1 = prev[ST_KP_IDX].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 24))
                + global_fors_leaf;
            for i in 0..4 {
                emit_op(st_in[i] - aux[i]);
                emit_op(st_in[4 + i] - pk_seed[i]);
                emit_op(
                    next[ST_WORK + i]
                        - (perm_out[i]
                            + aux[i]
                            + (st_in[4 + i] + st_in[4 + i])
                            + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i])),
                );
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_FORS_LEAF));
            emit_op(st_in[9] - tweak1);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            emit_op(next[ST_CURSOR_IDX] - idx_j);

            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_REM_PACK + slot] = false;
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_CURSOR_IDX] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::ForsMerkleBlockA => {
            let bit = aux[0];
            let parent_idx = aux[1];
            emit_op(bool_check_generic(bit));
            emit_op(prev[ST_CURSOR_IDX] - (bit + parent_idx + parent_idx));
            let one_minus_b = F::ONE - bit;
            for i in 0..4 {
                let node_i = prev[ST_WORK + i];
                let sib_i = aux[2 + i];
                let left_i = one_minus_b * node_i + bit * sib_i;
                let right_i = bit * node_i + one_minus_b * sib_i;
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - left_i);
                emit_op(next[ST_WORK + i] - right_i);
            }
            let meta0 = step_c0
                + prev[ST_KP_IDX].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 16))
                + parent_idx;
            emit_op(st_in[8] - F::from_u64(DOMAIN_FORS_NODE));
            emit_op(st_in[9] - meta0);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            for i in 0..12 {
                emit_op(next[ST_SUB_SPONGE + i] - perm_out[i]);
            }
            emit_op(next[ST_CURSOR_IDX] - parent_idx);

            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_SUB_SPONGE..ST_SUB_SPONGE + 12].fill(false);
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_CURSOR_IDX] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::ForsMerkleBlockB {
            is_tree_last,
            is_odd_tree,
        } => {
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_SUB_SPONGE + i] + prev[ST_WORK + i]));
            }
            emit_op(st_in[4] - (prev[ST_SUB_SPONGE + 4] + F::ONE));
            emit_op(st_in[5] - (prev[ST_SUB_SPONGE + 5] + F::from_u64(POSEIDON2_CONST_IV)));
            for i in 6..12 {
                emit_op(st_in[i] - prev[ST_SUB_SPONGE + i]);
            }
            if is_tree_last {
                emit_op(prev[ST_CURSOR_IDX]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            if is_tree_last && !is_odd_tree {
                for i in 0..4 {
                    emit_op(next[ST_CUR_ROOT + i] - perm_out[i]);
                    carry[ST_CUR_ROOT + i] = false;
                }
            } else {
                for i in 0..4 {
                    emit_op(next[ST_WORK + i] - perm_out[i]);
                    carry[ST_WORK + i] = false;
                }
            }
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::ForsRootsPairAbsorb { is_last_pair } => {
            if is_last_pair {
                for s in 0..6 {
                    emit_op(prev[ST_REM_PACK + s]);
                }
            }
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_MAIN_SPONGE + i] + prev[ST_CUR_ROOT + i]));
                emit_op(st_in[4 + i] - (prev[ST_MAIN_SPONGE + 4 + i] + prev[ST_WORK + i]));
                emit_op(st_in[8 + i] - prev[ST_MAIN_SPONGE + 8 + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::ForsRootsFinalSqueeze => {
            emit_op(st_in[0] - (prev[ST_MAIN_SPONGE] + F::ONE));
            for i in 1..12 {
                emit_op(st_in[i] - prev[ST_MAIN_SPONGE + i]);
            }
            for i in 0..4 {
                emit_op(next[ST_CUR_ROOT + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            for i in 0..4 {
                carry[ST_CUR_ROOT + i] = false;
            }
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::DetTreeHmsgBlock0 => {
            let layer_kp = step_c0 + prev[ST_KP_IDX];
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - pk_root[i]);
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_H_MSG_DET_TREE));
            emit_op(st_in[9] - layer_kp);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::DetTreeHmsgBlock1 => {
            let mut ctr_val = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(32) {
                emit_op(bool_check_generic(aux_i));
                ctr_val += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << i));
            }
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_MAIN_SPONGE + i] + prev[ST_CUR_ROOT + i]));
            }
            emit_op(st_in[4] - (prev[ST_MAIN_SPONGE + 4] + ctr_val));
            emit_op(st_in[5] - (prev[ST_MAIN_SPONGE + 5] + F::ONE));
            for i in 6..12 {
                emit_op(st_in[i] - prev[ST_MAIN_SPONGE + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            for s in 0..6 {
                emit_op(next[ST_REM_PACK + s]);
            }
            emit_op(next[ST_ACC_OR_U1]);
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_REM_PACK..ST_REM_PACK + 6].fill(false);
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            carry[ST_ACC_OR_U1] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::HmsgDecompLimb { limb_idx } => {
            let l = limb_idx as usize;
            let mut recon = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(31) {
                emit_op(quartic_base4_generic(aux_i));
                recon += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * i)));
            }
            emit_op(bool_check_generic(aux[31]));
            recon += aux[31].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 62));
            emit_op(prev[ST_MAIN_SPONGE + l] - recon);

            let mut expected_next = [F::ZERO; NUM_STATE_LIMBS];
            expected_next.copy_from_slice(prev);
            let count = if l < 4 { 31 } else { 4 };
            let base_r = 31 * l;
            let three = F::from_u64(3);
            let mut d_sum = F::ZERO;
            for (i, &aux_i) in aux.iter().enumerate().take(count) {
                let r = base_r + i;
                let d_r = aux_i;
                d_sum += d_r;
                let slot = wots_pack_slot(r as u8) as usize;
                let slot_start = match slot {
                    0 => 0,
                    1 => 26,
                    2 => 52,
                    3 => 78,
                    _ => 103,
                };
                let pos = r - slot_start;
                expected_next[ST_REM_PACK + slot] +=
                    (three - d_r).mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * pos)));
            }
            expected_next[ST_ACC_OR_U1] = prev[ST_ACC_OR_U1] + d_sum;
            if l == 4 {
                emit_op(expected_next[ST_ACC_OR_U1] - F::from_u64(WOTS_TARGET_SUM as u64));
            }
            for j in 0..NUM_STATE_LIMBS {
                emit_op(next[j] - expected_next[j]);
            }
        }
        ConstraintKind::WotsTellInit => {
            let layer_kp = step_c0 + prev[ST_KP_IDX];
            for i in 0..4 {
                emit_op(st_in[i] - pk_seed[i]);
            }
            emit_op(st_in[4] - layer_kp);
            emit_op(st_in[5] - prev[ST_TREE_LO]);
            emit_op(st_in[6] - prev[ST_TREE_HI]);
            emit_op(st_in[7] - F::from_u64(WOTS_CHAINS as u64));
            emit_op(st_in[8] - F::from_u64(DOMAIN_WOTS_PK));
            emit_op(st_in[9]);
            emit_op(st_in[10]);
            emit_op(st_in[11] - F::from_u64(POSEIDON2_CONST_IV));
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::WotsChainStep0 { pack_slot } => {
            let slot = pack_slot as usize;
            let u0 = aux[4];
            let u1 = aux[5];
            let u2 = aux[6];
            let quot = aux[7];
            emit_op(bool_check_generic(u0));
            emit_op(bool_check_generic(u1));
            emit_op(bool_check_generic(u2));
            emit_op(u1 * (F::ONE - u0));
            emit_op(u2 * (F::ONE - u1));

            let rem_r = F::from_u64(3) - (u0 + u1 + u2);
            emit_op(
                prev[ST_REM_PACK + slot]
                    - (rem_r + quot.mul_base_f(Goldilocks::from_u64_reduced(4))),
            );
            emit_op(next[ST_REM_PACK + slot] - quot);

            let addr_limb =
                step_c0 + prev[ST_KP_IDX].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 16));
            let one_minus_u0 = F::ONE - u0;
            for i in 0..4 {
                let sig_i = aux[i];
                emit_op(st_in[i] - sig_i);
                emit_op(st_in[4 + i] - pk_seed[i]);
                let ff_i = perm_out[i]
                    + sig_i
                    + (st_in[4 + i] + st_in[4 + i])
                    + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
                emit_op(next[ST_WORK + i] - (u0 * sig_i + one_minus_u0 * ff_i));
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_WOTS_STEP));
            emit_op(st_in[9] - addr_limb);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            emit_op(next[ST_ACC_OR_U1] - u1);
            emit_op(next[ST_WOTS_U2] - u2);

            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_REM_PACK + slot] = false;
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_ACC_OR_U1] = false;
            carry[ST_WOTS_U2] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::WotsChainStep1 => {
            let u1 = prev[ST_ACC_OR_U1];
            let one_minus_u1 = F::ONE - u1;
            let addr_limb =
                step_c0 + prev[ST_KP_IDX].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 16));
            for i in 0..4 {
                let cur_i = prev[ST_WORK + i];
                emit_op(st_in[i] - cur_i);
                emit_op(st_in[4 + i] - pk_seed[i]);
                let ff_i = perm_out[i]
                    + cur_i
                    + (st_in[4 + i] + st_in[4 + i])
                    + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
                emit_op(next[ST_WORK + i] - (u1 * cur_i + one_minus_u1 * ff_i));
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_WOTS_STEP));
            emit_op(st_in[9] - addr_limb);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);

            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_WORK..ST_WORK + 4].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::WotsChainStep2 { is_odd } => {
            let u2 = prev[ST_WOTS_U2];
            let one_minus_u2 = F::ONE - u2;
            let addr_limb =
                step_c0 + prev[ST_KP_IDX].mul_base_f(Goldilocks::from_u64_reduced(1u64 << 16));
            let mut carry = [true; NUM_STATE_LIMBS];
            for i in 0..4 {
                let cur_i = prev[ST_WORK + i];
                emit_op(st_in[i] - cur_i);
                emit_op(st_in[4 + i] - pk_seed[i]);
                let ff_i = perm_out[i]
                    + cur_i
                    + (st_in[4 + i] + st_in[4 + i])
                    + (st_in[8 + i] + st_in[8 + i] + st_in[8 + i] + st_in[8 + i]);
                let ep_i = u2 * cur_i + one_minus_u2 * ff_i;
                if !is_odd {
                    emit_op(next[ST_SUB_SPONGE + i] - ep_i);
                    carry[ST_SUB_SPONGE + i] = false;
                } else {
                    emit_op(next[ST_WORK + i] - ep_i);
                    carry[ST_WORK + i] = false;
                }
            }
            emit_op(st_in[8] - F::from_u64(DOMAIN_WOTS_STEP));
            emit_op(st_in[9] - addr_limb);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::WotsTellPairAbsorb { is_last_pair } => {
            if is_last_pair {
                for s in 0..5 {
                    emit_op(prev[ST_REM_PACK + s]);
                }
            }
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_MAIN_SPONGE + i] + prev[ST_SUB_SPONGE + i]));
                emit_op(st_in[4 + i] - (prev[ST_MAIN_SPONGE + 4 + i] + prev[ST_WORK + i]));
                emit_op(st_in[8 + i] - prev[ST_MAIN_SPONGE + 8 + i]);
            }
            for i in 0..12 {
                emit_op(next[ST_MAIN_SPONGE + i] - perm_out[i]);
            }
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_MAIN_SPONGE..ST_MAIN_SPONGE + 12].fill(false);
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::WotsTellFinalSqueeze => {
            emit_op(st_in[0] - (prev[ST_MAIN_SPONGE] + F::ONE));
            for i in 1..12 {
                emit_op(st_in[i] - prev[ST_MAIN_SPONGE + i]);
            }
            for i in 0..4 {
                emit_op(next[ST_WORK + i] - perm_out[i]);
            }
            emit_op(next[ST_CURSOR_IDX] - prev[ST_KP_IDX]);
            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_CURSOR_IDX] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::XmssMerkleBlockA => {
            let bit = aux[0];
            let parent_idx = aux[1];
            emit_op(bool_check_generic(bit));
            emit_op(prev[ST_CURSOR_IDX] - (bit + parent_idx + parent_idx));
            let one_minus_b = F::ONE - bit;
            for i in 0..4 {
                let node_i = prev[ST_WORK + i];
                let sib_i = aux[2 + i];
                let left_i = one_minus_b * node_i + bit * sib_i;
                let right_i = bit * node_i + one_minus_b * sib_i;
                emit_op(st_in[i] - pk_seed[i]);
                emit_op(st_in[4 + i] - left_i);
                emit_op(next[ST_WORK + i] - right_i);
            }
            let meta0 = step_c0 + parent_idx;
            emit_op(st_in[8] - F::from_u64(DOMAIN_MERKLE_NODE));
            emit_op(st_in[9] - meta0);
            emit_op(st_in[10] - prev[ST_TREE_LO]);
            emit_op(st_in[11] - prev[ST_TREE_HI]);
            for i in 0..12 {
                emit_op(next[ST_SUB_SPONGE + i] - perm_out[i]);
            }
            emit_op(next[ST_CURSOR_IDX] - parent_idx);

            let mut carry = [true; NUM_STATE_LIMBS];
            carry[ST_SUB_SPONGE..ST_SUB_SPONGE + 12].fill(false);
            carry[ST_WORK..ST_WORK + 4].fill(false);
            carry[ST_CURSOR_IDX] = false;
            check_carry_unchanged(&carry, emit_op);
        }
        ConstraintKind::XmssMerkleBlockB {
            is_layer_last,
            is_top_final,
        } => {
            for i in 0..4 {
                emit_op(st_in[i] - (prev[ST_SUB_SPONGE + i] + prev[ST_WORK + i]));
            }
            emit_op(st_in[4] - (prev[ST_SUB_SPONGE + 4] + F::ONE));
            emit_op(st_in[5] - (prev[ST_SUB_SPONGE + 5] + F::from_u64(POSEIDON2_CONST_IV)));
            for i in 6..12 {
                emit_op(st_in[i] - prev[ST_SUB_SPONGE + i]);
            }
            if !is_layer_last {
                let mut carry = [true; NUM_STATE_LIMBS];
                for i in 0..4 {
                    emit_op(next[ST_WORK + i] - perm_out[i]);
                    carry[ST_WORK + i] = false;
                }
                check_carry_unchanged(&carry, emit_op);
            } else if is_top_final {
                emit_op(prev[ST_CURSOR_IDX]);
                for i in 0..4 {
                    emit_op(perm_out[i] - pk_root[i]);
                }
                for &next_item in next.iter().take(NUM_STATE_LIMBS) {
                    emit_op(next_item);
                }
            } else {
                emit_op(prev[ST_CURSOR_IDX]);
                let mut next_kp = F::ZERO;
                for (i, &aux_i) in aux.iter().enumerate().take(4) {
                    emit_op(bool_check_generic(aux_i));
                    next_kp += aux_i.mul_base_f(Goldilocks::from_u64_reduced(1u64 << i));
                }
                let mut lo_shifted = F::ZERO;
                for i in 0..14 {
                    emit_op(quartic_base4_generic(aux[4 + i]));
                    lo_shifted +=
                        aux[4 + i].mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * i)));
                }
                let mut hi_low_nibble = F::ZERO;
                for i in 0..2 {
                    emit_op(quartic_base4_generic(aux[18 + i]));
                    hi_low_nibble +=
                        aux[18 + i].mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * i)));
                }
                let mut next_tree_hi = F::ZERO;
                for i in 0..14 {
                    emit_op(quartic_base4_generic(aux[20 + i]));
                    next_tree_hi +=
                        aux[20 + i].mul_base_f(Goldilocks::from_u64_reduced(1u64 << (2 * i)));
                }

                emit_op(
                    prev[ST_TREE_LO]
                        - (next_kp + lo_shifted.mul_base_f(Goldilocks::from_u64_reduced(16))),
                );
                emit_op(
                    prev[ST_TREE_HI]
                        - (hi_low_nibble
                            + next_tree_hi.mul_base_f(Goldilocks::from_u64_reduced(16))),
                );
                for i in 0..4 {
                    emit_op(next[ST_CUR_ROOT + i] - perm_out[i]);
                }
                emit_op(next[ST_KP_IDX] - next_kp);
                emit_op(
                    next[ST_TREE_LO]
                        - (lo_shifted
                            + hi_low_nibble.mul_base_f(Goldilocks::from_u64_reduced(1u64 << 28))),
                );
                emit_op(next[ST_TREE_HI] - next_tree_hi);

                let mut carry = [true; NUM_STATE_LIMBS];
                for i in 0..4 {
                    carry[ST_CUR_ROOT + i] = false;
                }
                carry[ST_KP_IDX] = false;
                carry[ST_TREE_LO] = false;
                carry[ST_TREE_HI] = false;
                check_carry_unchanged(&carry, emit_op);
            }
        }
    }
}

fn count_op_constraints(kind: ConstraintKind) -> usize {
    let dummy_state = [Goldilocks::ZERO; NUM_STATE_LIMBS];
    let dummy_aux = [Goldilocks::ZERO; 38];
    let dummy_12 = [Goldilocks::ZERO; 12];
    let dummy_4 = [Goldilocks::ZERO; 4];
    let dummy_5 = [Goldilocks::ZERO; 5];
    let mut count = 0usize;
    eval_single_op_constraints_generic(
        kind,
        Goldilocks::ZERO,
        OpRowInputs {
            prev: &dummy_state,
            next: &dummy_state,
            aux: &dummy_aux,
            st_in: &dummy_12,
            perm_out: &dummy_12,
            pk_seed: &dummy_4,
            pk_root: &dummy_4,
            mu: &dummy_5,
        },
        &mut |_| count += 1,
    );
    count
}

/// Public inputs of one row over any [`TraceField`]: evaluated over `Goldilocks` or Quintic `Fp5`.
#[derive(Clone)]
pub struct RowPublicEval<'a, F: TraceField> {
    pub active_signer: F,
    pub pk_seed: [F; 4],
    pub pk_root: [F; 4],
    pub mu: [F; 5],
    pub gated_op_sels: &'a [F],
    pub step_c0: F,
    pub is_row_first: F,
    pub is_row_last: F,
    pub eq_tau: F,
    pub eq_not_last: F,
    pub shift_tau: F,
}

/// Dense Horner-batched evaluation of ALL row constraints at `cols[0..256]`, over any
/// [`TraceField`]. Used over `Goldilocks` and Quintic `Fp5` ([`crate::hem_quintic`]).
pub fn eval_batched_row_constraints_generic<F: TraceField>(
    unique_ops: &[ConstraintKind],
    cols: &[F; NUM_TRACE_COLS],
    pub_in: &RowPublicEval<'_, F>,
    gamma: F,
) -> F {
    eval_row_with_weights(unique_ops, cols, pub_in, gamma, None)
}

/// Cache the public constraint-batching powers once per proof. An absent selector
/// advances over the same residuals as the dense evaluator.
pub(crate) struct RowWeights<F> {
    op_sizes: Vec<usize>,
    powers: Vec<F>,
}

impl<F: TraceField> RowWeights<F> {
    pub(crate) fn new(ops: &[ConstraintKind], gamma: F) -> Self {
        let op_sizes: Vec<_> = ops.iter().map(|&op| count_op_constraints(op)).collect();
        let len =
            NUM_GROUP_A_AND_BOUNDARY_CONSTRAINTS + op_sizes.iter().sum::<usize>() + NUM_STATE_LIMBS;
        let mut power = F::ONE;
        let powers = (0..len)
            .map(|_| {
                let w = power;
                power = power * gamma;
                w
            })
            .collect();
        Self { op_sizes, powers }
    }

    pub(crate) fn count(&self) -> usize {
        self.powers.len()
    }
}

pub(crate) fn eval_row_with_weights<F: TraceField>(
    unique_ops: &[ConstraintKind],
    cols: &[F; NUM_TRACE_COLS],
    pub_in: &RowPublicEval<'_, F>,
    gamma: F,
    weights: Option<&RowWeights<F>>,
) -> F {
    let mut eq_acc = F::ZERO;
    let mut power = F::ONE;
    let mut index = 0;
    let mut next_weight = |index: &mut usize| {
        let w = if let Some(weights) = weights {
            weights.powers[*index]
        } else {
            let w = power;
            power = power * gamma;
            w
        };
        *index += 1;
        w
    };
    let perm_out = eval_group_a_and_boundaries_generic(
        cols,
        pub_in.is_row_first,
        pub_in.is_row_last,
        |_, res| {
            eq_acc += next_weight(&mut index) * res;
        },
    );
    let prev = &cols[COL_PREV_STATE..COL_PREV_STATE + NUM_STATE_LIMBS];
    let next = &cols[COL_NEXT_STATE..COL_NEXT_STATE + NUM_STATE_LIMBS];
    let aux = &cols[COL_AUX..COL_AUX + 38];
    let st_in = &cols[COL_ST_IN..COL_ST_IN + 12];

    for (op_uid, &kind) in unique_ops.iter().enumerate() {
        let sel = pub_in.gated_op_sels[op_uid];
        if let Some(weights) = weights
            && sel == F::ZERO
        {
            index += weights.op_sizes[op_uid];
            continue;
        }
        let mut op_acc = F::ZERO;
        eval_single_op_constraints_generic(
            kind,
            pub_in.step_c0,
            OpRowInputs {
                prev,
                next,
                aux,
                st_in,
                perm_out: &perm_out,
                pk_seed: &pub_in.pk_seed,
                pk_root: &pub_in.pk_root,
                mu: &pub_in.mu,
            },
            &mut |expr| {
                op_acc += next_weight(&mut index) * expr;
            },
        );
        eq_acc += sel * op_acc;
    }

    let mut total = pub_in.eq_tau * eq_acc;
    for j in 0..NUM_STATE_LIMBS {
        let shift_res = pub_in.eq_not_last * next[j] - pub_in.shift_tau * prev[j];
        total += next_weight(&mut index) * shift_res;
    }
    total
}

#[cfg(test)]
mod sponge_trace_tests {
    use super::*;
    use crate::sig::{ValidatorKeypair, compute_message_mu};

    #[test]
    fn canonical_sponge_signature_trace_satisfies_every_row_constraint() {
        let mut kp =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[42; 32], 0);
        let msg = b"canonical poseidon2 trace parity";
        let sig = kp.sign_stateful_for_unit_test(msg, 0).unwrap();
        let mu = compute_message_mu(&kp.pk, msg).1;
        let program = build_signer_program(kp.pk.profile);
        let mut rows = alloc::vec![[Goldilocks::ZERO; NUM_TRACE_COLS]; program.len()];
        populate_active_signer_rows(&program, &kp.pk, mu, &sig, &mut rows);
        for (i, (row, op)) in rows.iter().zip(program).enumerate() {
            let perm_out = eval_group_a_and_boundaries_generic(
                row,
                if i == 0 {
                    Goldilocks::ONE
                } else {
                    Goldilocks::ZERO
                },
                if i + 1 == rows.len() {
                    Goldilocks::ONE
                } else {
                    Goldilocks::ZERO
                },
                |c, r| assert_eq!(r, Goldilocks::ZERO, "permutation row {i}, constraint {c}"),
            );
            let (kind, step_c0) = step_op_to_kind_and_c0(op);
            eval_single_op_constraints_generic(
                kind,
                step_c0,
                OpRowInputs {
                    prev: &row[COL_PREV_STATE..COL_PREV_STATE + NUM_STATE_LIMBS],
                    next: &row[COL_NEXT_STATE..COL_NEXT_STATE + NUM_STATE_LIMBS],
                    aux: &row[COL_AUX..COL_AUX + 38],
                    st_in: &row[COL_ST_IN..COL_ST_IN + 12],
                    perm_out: &perm_out,
                    pk_seed: &kp.pk.pk_seed,
                    pk_root: &kp.pk.pk_root,
                    mu: &mu,
                },
                &mut |r| assert_eq!(r, Goldilocks::ZERO, "operation row {i}"),
            );
        }
    }
}
