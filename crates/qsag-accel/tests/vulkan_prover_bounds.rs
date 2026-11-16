//! Negative tests for the safe prover API of `VulkanSpirvBackend` on live hardware: every
//! out-of-range, overflowing or out-of-order call returns a clean error, and the backend then
//! still computes correct results.

#![cfg(feature = "std")]

use qsag_accel::goldilocks::{GOLDILOCKS_PRIME, gl_add, gl_mul, gl_sub};
use qsag_accel::{AccelError, VulkanError, VulkanSpirvBackend};

type Ext4 = [u64; 4];

const NUM_VARS: usize = 12;
const C_LEN: usize = 1 << NUM_VARS;
const NUM_POLYS: usize = 2;
/// Room behind the committed polynomials for one 16-row AIR shard in column-major form.
const AIR_ROWS: usize = 16;
const EXTRA_WITNESS_WORDS: usize = AIR_ROWS * 256;

fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

fn field(state: &mut u64) -> u64 {
    splitmix64(state) % GOLDILOCKS_PRIME
}

fn ext4(state: &mut u64) -> Ext4 {
    core::array::from_fn(|_| field(state))
}

fn e_add(a: Ext4, b: Ext4) -> Ext4 {
    core::array::from_fn(|i| gl_add(a[i], b[i]))
}

fn e_sub(a: Ext4, b: Ext4) -> Ext4 {
    core::array::from_fn(|i| gl_sub(a[i], b[i]))
}

fn e_scale(a: Ext4, s: u64) -> Ext4 {
    a.map(|x| gl_mul(x, s))
}

/// `Fp2 = Fp[u] / (u^2 - 7)`.
fn f2_mul(a: [u64; 2], b: [u64; 2]) -> [u64; 2] {
    [
        gl_add(gl_mul(a[0], b[0]), gl_mul(7, gl_mul(a[1], b[1]))),
        gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0])),
    ]
}

/// `Ext4 = Fp2[v] / (v^2 - u)`, the field of the prover shaders.
fn e_mul(a: Ext4, b: Ext4) -> Ext4 {
    let (a0, a1, b0, b1) = ([a[0], a[1]], [a[2], a[3]], [b[0], b[1]], [b[2], b[3]]);
    let v0 = f2_mul(a0, b0);
    let v1 = f2_mul(a1, b1);
    let cross0 = f2_mul(a0, b1);
    let cross1 = f2_mul(a1, b0);
    // u * (x, y) = (7 y, x)
    [
        gl_add(v0[0], gl_mul(7, v1[1])),
        gl_add(v0[1], v1[0]),
        gl_add(cross0[0], cross1[0]),
        gl_add(cross0[1], cross1[1]),
    ]
}

fn backend() -> Option<VulkanSpirvBackend> {
    match VulkanSpirvBackend::try_new_audited() {
        Ok(gpu) => Some(gpu),
        Err(
            VulkanError::UnsupportedPlatform
            | VulkanError::LibraryLoadFailed
            | VulkanError::NoDiscreteGpuFound,
        ) => {
            assert!(
                std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                "required hardware unavailable"
            );
            None
        }
        Err(other) => {
            assert!(
                std::env::var_os("QSAG_REQUIRE_GPU_AUDIT").is_none(),
                "Vulkan backend unavailable under QSAG_REQUIRE_GPU_AUDIT: {other}"
            );
            None
        }
    }
}

#[track_caller]
fn assert_clean<T: core::fmt::Debug>(res: Result<T, VulkanError>) {
    assert!(
        matches!(
            res,
            Err(VulkanError::Accel(
                AccelError::LengthOverflow | AccelError::LengthMismatch { .. }
            ))
        ),
        "expected a clean shape error, got {res:?}"
    );
}

struct Fixture {
    polys: Vec<Vec<u64>>,
    eq_tables: Vec<Ext4>,
    lambdas: Vec<Ext4>,
    chal: Ext4,
}

impl Fixture {
    fn new() -> Self {
        let mut st = 0x51A6_0B0D_u64;
        Self {
            polys: (0..NUM_POLYS)
                .map(|_| (0..C_LEN).map(|_| field(&mut st)).collect())
                .collect(),
            eq_tables: (0..768 * NUM_POLYS).map(|_| ext4(&mut st)).collect(),
            lambdas: (0..NUM_POLYS).map(|_| ext4(&mut st)).collect(),
            chal: ext4(&mut st),
        }
    }

    fn commit(&self, gpu: &VulkanSpirvBackend) -> [u8; 32] {
        let refs: Vec<&[u64]> = self.polys.iter().map(Vec::as_slice).collect();
        gpu.prover_whir_commit_round0(
            &refs,
            &[0x42; 32],
            NUM_VARS,
            4,
            16,
            0,
            0,
            EXTRA_WITNESS_WORDS,
        )
        .expect("round-0 commit")
    }

    /// Kernel entry `gid` of polynomial `p`: the 3-byte Kronecker product of its table.
    fn kernel(&self, p: usize, gid: usize) -> Ext4 {
        let t = &self.eq_tables[p * 768..(p + 1) * 768];
        e_mul(
            e_mul(t[gid & 255], t[256 + ((gid >> 8) & 255)]),
            t[512 + ((gid >> 16) & 255)],
        )
    }

    /// Commit, expand the kernels, fold once, read the folded tables and kernels back, and
    /// check both against the host computation.
    fn round_trip(&self, gpu: &VulkanSpirvBackend) -> [u8; 32] {
        let top = self.commit(gpu);
        gpu.prover_whir_batch_sumcheck_init(&self.eq_tables, &self.lambdas, NUM_VARS)
            .expect("sumcheck init");
        let dst_base = (NUM_POLYS * C_LEN) as u32;
        let (ev0, _ev2) = gpu
            .prover_whir_batch_sumcheck_eval(0, C_LEN, NUM_POLYS, 0)
            .expect("sumcheck eval");
        let mut want_ev0 = [0u64; 4];
        for p in 0..NUM_POLYS {
            let mut acc = [0u64; 4];
            for i in 0..C_LEN / 2 {
                acc = e_add(acc, e_scale(self.kernel(p, 2 * i), self.polys[p][2 * i]));
            }
            want_ev0 = e_add(want_ev0, e_mul(self.lambdas[p], acc));
        }
        assert_eq!(ev0, want_ev0, "round-0 evaluation at 0");
        gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, NUM_POLYS, 0, dst_base, self.chal)
            .expect("sumcheck fold");
        let half = C_LEN / 2;
        let mut tables = vec![[0u64; 4]; NUM_POLYS * half];
        let mut kernels = vec![[0u64; 4]; NUM_POLYS * half];
        gpu.prover_whir_batch_sumcheck_read_tail(
            half,
            NUM_POLYS,
            dst_base,
            &mut tables,
            &mut kernels,
        )
        .expect("read tail");
        for p in 0..NUM_POLYS {
            for i in 0..half {
                let (w0, w1) = (self.polys[p][2 * i], self.polys[p][2 * i + 1]);
                let want_t = e_add([w0, 0, 0, 0], e_scale(self.chal, gl_sub(w1, w0)));
                assert_eq!(tables[p * half + i], want_t, "table {p} entry {i}");
                let (k0, k1) = (self.kernel(p, 2 * i), self.kernel(p, 2 * i + 1));
                let want_k = e_add(k0, e_mul(self.chal, e_sub(k1, k0)));
                assert_eq!(kernels[p * half + i], want_k, "kernel {p} entry {i}");
            }
        }
        top
    }
}

/// Static AIR tables for a 16-row shard whose every row is the `Idle` opcode: 206 group-A
/// gammas, 44 shift gammas, 44 `Idle` gammas, then the identity row list for 8 rows.
fn idle_air_static(st: &mut u64) -> Vec<Ext4> {
    let mut table: Vec<Ext4> = (0..250 + 44).map(|_| ext4(st)).collect();
    table.push([0, 1, 2, 3]);
    table.push([4, 5, 6, 7]);
    table
}

const IDLE_GAMMA_BASE: u64 = 250;
const IDLE_SORTED_U64_OFF: u32 = 294 * 4;
const IDLE_DYN_EXT4_OFF: u32 = 296;

struct IdleDyn {
    words: Vec<u64>,
    signers_off: u32,
    steps_off: u32,
    op_hdr_off: u32,
    op_ent_off: u32,
}

/// Dynamic tables of the first (non-signer-folding) round over `AIR_ROWS` rows.
fn idle_air_dyn() -> IdleDyn {
    let mut words = Vec::new();
    let mut off = IDLE_DYN_EXT4_OFF;
    let signers_off = off;
    words.extend_from_slice(&[1, 0, 0, 0]); // active
    words.extend(core::iter::repeat_n(0u64, 13 * 4));
    off += 14;
    let steps_off = off;
    for loc in 0..AIR_ROWS {
        words.extend_from_slice(&[u64::from(loc == 0), 0, 0, 0]);
        words.extend_from_slice(&[u64::from(loc + 1 == AIR_ROWS), 0, 0, 0]);
        words.extend_from_slice(&[0, 0, 0, 0]);
    }
    off += (AIR_ROWS * 3) as u32;
    let op_hdr_off = off;
    for idx in 0..AIR_ROWS / 2 {
        words.extend_from_slice(&[idx as u64, 1, 0, 0]);
    }
    off += (AIR_ROWS / 2) as u32;
    let op_ent_off = off;
    for _ in 0..AIR_ROWS / 2 {
        words.extend_from_slice(&[0, 0, IDLE_GAMMA_BASE, 0]); // Idle, no argument
        words.extend_from_slice(&[1, 0, 0, 0]); // selector at the low row
        words.extend_from_slice(&[0, 0, 0, 0]); // selector difference
    }
    IdleDyn {
        words,
        signers_off,
        steps_off,
        op_hdr_off,
        op_ent_off,
    }
}

fn air_eval(
    gpu: &VulkanSpirvBackend,
    dynamic: &IdleDyn,
    cur_m: usize,
    col_src: u32,
) -> Result<[[u64; 4]; 8], VulkanError> {
    gpu.prover_air_eval_round(
        true,
        cur_m,
        AIR_ROWS,
        1,
        false,
        col_src,
        0,
        IDLE_DYN_EXT4_OFF,
        &dynamic.words,
        dynamic.signers_off,
        dynamic.steps_off,
        dynamic.op_hdr_off,
        dynamic.op_ent_off,
        IDLE_SORTED_U64_OFF,
    )
}

#[test]
fn out_of_range_prover_calls_fail_cleanly_and_leave_the_backend_correct() {
    let Some(gpu) = backend() else {
        return;
    };
    let fx = Fixture::new();
    let mut one = [[0u64; 4]; 1];
    let mut two = [[0u64; 4]; 1];
    let kron = [[1u64, 0, 0, 0]; 768];
    let kron2 = [[1u64, 0, 0, 0]; 1536];
    let cols_base = (NUM_POLYS * C_LEN) as u32;

    // No session at all.
    assert!(matches!(
        gpu.prover_whir_batch_sumcheck_read_tail(1, 1, 0, &mut one, &mut two),
        Err(VulkanError::WorkspacePoisoned)
    ));

    let session = gpu.try_acquire_prover_session().expect("acquire");

    // An acquired session that never committed: there is no arena to read.
    assert_clean(gpu.prover_whir_batch_sumcheck_read_tail(1, 1, 0, &mut one, &mut two));
    assert_clean(gpu.prover_whir_batch_sumcheck_read_tail(1, 1, u32::MAX, &mut one, &mut two));
    assert_clean(gpu.prover_whir_batch_sumcheck_init(&fx.eq_tables, &fx.lambdas, NUM_VARS));
    assert_clean(gpu.prover_whir_batch_sumcheck_eval(0, C_LEN, NUM_POLYS, 0));
    assert_clean(gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, NUM_POLYS, 0, 0, fx.chal));
    assert_clean(gpu.prover_whir_expand_monomial_and_dot(&kron, NUM_VARS, 1, &mut []));
    assert_clean(gpu.prover_whir_open_init(NUM_VARS, true, &[], &kron2));
    assert_clean(gpu.prover_whir_add_ood_claims(C_LEN + 2, 0, &kron2));
    assert_clean(gpu.prover_whir_fold_pass_a(8, 0, 0));
    assert_clean(gpu.prover_whir_fold_pass_b(8, 0, 0, 8, 64, fx.chal));
    assert_clean(gpu.prover_whir_fold_pass_c(8, 0, 64, fx.chal, fx.chal, fx.chal, false, 0));
    assert_clean(gpu.prover_whir_commit_stage(1, 16, 64, 4));
    assert_clean(gpu.prover_whir_eval_univariate_2(16, 0, &kron2));
    assert_clean(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1024, &[0], &[], &mut [0; 34]));
    assert_clean(gpu.prover_whir_accumulate_shift_claims(16, 0, &[1; 256], &[[0; 8]]));
    assert_clean(gpu.prover_whir_read_final_coeffs(0, &mut one));
    assert_clean(gpu.prover_air_read_tail(0, 0, &mut one, &mut two));
    assert_clean(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, 0, 0, 48, fx.chal));

    // Baseline: a valid round trip, checked against the host.
    let top = fx.round_trip(&gpu);

    // After release and re-acquire the previous session's buffers are not readable.
    drop(session);
    let session = gpu.try_acquire_prover_session().expect("re-acquire");
    assert_clean(gpu.prover_whir_batch_sumcheck_read_tail(1, 1, cols_base, &mut one, &mut two));

    // Each case starts from a fresh commit: a rejected call ends the session it was made on.
    macro_rules! reject {
        ($call:expr) => {{
            fx.commit(&gpu);
            assert_clean($call);
        }};
    }

    // Sumcheck read-back and rounds.
    reject!(gpu.prover_whir_batch_sumcheck_read_tail(1, 1, u32::MAX, &mut one, &mut two));
    reject!(gpu.prover_whir_batch_sumcheck_read_tail(1, 1, 1 << 27, &mut one, &mut two));
    reject!(gpu.prover_whir_batch_sumcheck_read_tail(2, 1, 0, &mut one, &mut two));
    for num_vars in [27usize, 63, 64, usize::BITS as usize, usize::MAX] {
        reject!(gpu.prover_whir_batch_sumcheck_init(&fx.eq_tables, &fx.lambdas, num_vars));
    }
    reject!(gpu.prover_whir_batch_sumcheck_init(&fx.eq_tables, &fx.lambdas, NUM_VARS - 1));
    reject!(gpu.prover_whir_batch_sumcheck_init(&fx.eq_tables, &fx.lambdas[..1], NUM_VARS));
    {
        // More polynomials than were committed, with matching table lengths.
        let lambdas = vec![[1u64, 0, 0, 0]; 3];
        let tables = vec![[1u64, 0, 0, 0]; 3 * 768];
        reject!(gpu.prover_whir_batch_sumcheck_init(&tables, &lambdas, NUM_VARS));
    }
    reject!(gpu.prover_whir_batch_sumcheck_eval(0, C_LEN, NUM_POLYS, u32::MAX));
    reject!(gpu.prover_whir_batch_sumcheck_eval(1, C_LEN, NUM_POLYS, 1 << 26));
    reject!(gpu.prover_whir_batch_sumcheck_eval(0, C_LEN, usize::MAX, 0));
    reject!(gpu.prover_whir_batch_sumcheck_eval(0, 1 << 40, NUM_POLYS, 0));
    reject!(gpu.prover_whir_batch_sumcheck_eval(0, C_LEN + 2, NUM_POLYS, 0));
    reject!(gpu.prover_whir_batch_sumcheck_eval(0, 0, NUM_POLYS, 0));
    reject!(gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, NUM_POLYS, 0, u32::MAX, fx.chal));
    reject!(gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, NUM_POLYS, u32::MAX, 0, fx.chal));
    reject!(gpu.prover_whir_batch_sumcheck_fold(0, 1 << 33, NUM_POLYS, 0, 0, fx.chal));
    reject!(gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, 1 << 40, 0, 0, fx.chal));
    // In-bounds ranges can still race if parallel invocations overwrite unread inputs.
    reject!(gpu.prover_whir_batch_sumcheck_fold(0, C_LEN, NUM_POLYS, 0, 0, fx.chal));
    reject!(gpu.prover_whir_batch_sumcheck_fold(1, C_LEN, NUM_POLYS, 0, C_LEN as u32, fx.chal));

    // Opening and fold passes.
    reject!(gpu.prover_whir_expand_monomial_and_dot(&kron, 64, 1, &mut []));
    reject!(gpu.prover_whir_expand_monomial_and_dot(&kron, NUM_VARS, u32::MAX, &mut one));
    reject!(gpu.prover_whir_expand_monomial_and_dot(&kron, 20, 0, &mut one));
    reject!(gpu.prover_whir_open_init(usize::MAX, true, &[], &kron2));
    reject!(gpu.prover_whir_open_init(20, true, &[], &kron2));
    reject!(gpu.prover_whir_add_ood_claims(usize::MAX, 0, &kron2));
    reject!(gpu.prover_whir_add_ood_claims(16, u32::MAX, &kron2));
    reject!(gpu.prover_whir_fold_pass_a(8, u32::MAX, 0));
    reject!(gpu.prover_whir_fold_pass_a(8, 0, u32::MAX));
    reject!(gpu.prover_whir_fold_pass_a(usize::MAX, 0, 0));
    reject!(gpu.prover_whir_fold_pass_b(8, 0, 0, 8, u32::MAX, fx.chal));
    reject!(gpu.prover_whir_fold_pass_b(8, 0, 0, u32::MAX, 0, fx.chal));
    reject!(gpu.prover_whir_fold_pass_b(8, u32::MAX, 0, 16, 64, fx.chal));
    reject!(gpu.prover_whir_fold_pass_b(8, 0, 0, 8, 15, fx.chal));
    reject!(gpu.prover_whir_fold_pass_c(8, 0, 15, fx.chal, fx.chal, fx.chal, false, 0));
    reject!(gpu.prover_whir_fold_pass_c(8, 0, u32::MAX, fx.chal, fx.chal, fx.chal, false, 0));
    reject!(gpu.prover_whir_fold_pass_c(8, u32::MAX, 0, fx.chal, fx.chal, fx.chal, false, 0));
    reject!(gpu.prover_whir_fold_pass_c(usize::MAX, 0, 0, fx.chal, fx.chal, fx.chal, false, 0));
    // A normalising copy longer than its offset would overlap its own source.
    reject!(gpu.prover_whir_fold_pass_c(8, 0, 4, fx.chal, fx.chal, fx.chal, true, 9));
    reject!(gpu.prover_whir_commit_stage(1, 16, 1 << 31, 4));
    reject!(gpu.prover_whir_commit_stage(1, 1 << 30, 64, 4));
    reject!(gpu.prover_whir_commit_stage(1, 16, 1 << 40, 4));
    reject!(gpu.prover_whir_commit_stage(0, 16, 64, 4));
    reject!(gpu.prover_whir_commit_stage(1, 65, 64, 4));
    reject!(gpu.prover_whir_eval_univariate_2(1 << 30, 0, &kron2));
    reject!(gpu.prover_whir_eval_univariate_2(16, u32::MAX, &kron2));
    // Stage-0 gather: 1024 groups of 16 in the committed codeword.
    reject!(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1024, &[1024], &[], &mut [0; 34]));
    reject!(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1024, &[u64::MAX], &[], &mut [0; 34]));
    reject!(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1024, &[], &[2048], &mut [0; 4]));
    reject!(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1 << 20, &[0], &[], &mut [0; 34]));
    reject!(gpu.prover_whir_gather_queries(0, 1 << 20, NUM_POLYS, 1024, &[0], &[], &mut [0; 34]));
    reject!(gpu.prover_whir_gather_queries(3, 4, 1, 16, &[], &[40], &mut [0; 4]));
    reject!(gpu.prover_whir_gather_queries(1, 4, 1, 16, &[], &[1], &mut [0; 4]));
    reject!(gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 512, &[], &[1], &mut [0; 4]));
    // Reusing a parity slot must not let an old stage read the new stage's tree.
    fx.commit(&gpu);
    gpu.prover_whir_commit_stage(1, 16, 64, 4).expect("stage 1");
    gpu.prover_whir_commit_stage(3, 16, 64, 4).expect("stage 3");
    gpu.prover_whir_gather_queries(3, 4, 1, 16, &[], &[1], &mut [0; 4])
        .expect("current stage");
    assert_clean(gpu.prover_whir_gather_queries(1, 4, 1, 16, &[], &[1], &mut [0; 4]));
    reject!(gpu.prover_whir_accumulate_shift_claims(16, u32::MAX, &[1; 256], &[[0; 8]]));
    reject!(gpu.prover_whir_accumulate_shift_claims(usize::MAX, 0, &[1; 256], &[[0; 8]]));
    reject!(gpu.prover_whir_accumulate_shift_claims(16, 0, &[1; 255], &[[0; 8]]));
    reject!(gpu.prover_whir_read_final_coeffs(u32::MAX, &mut one));

    // AIR.
    let mut st = 7u64;
    let statics = idle_air_static(&mut st);
    let shifts: Vec<Ext4> = (0..3 * AIR_ROWS).map(|_| ext4(&mut st)).collect();
    let dynamic = idle_air_dyn();
    reject!(gpu.prover_air_init_shard(u32::MAX, cols_base, AIR_ROWS, &shifts, &statics));
    reject!(gpu.prover_air_init_shard(0, u32::MAX, AIR_ROWS, &shifts, &statics));
    reject!(gpu.prover_air_init_shard(0, cols_base, AIR_ROWS, &shifts[1..], &statics));
    reject!(gpu.prover_air_init_shard(0, cols_base, 3, &shifts[..9], &statics));
    reject!(gpu.prover_air_init_shard(0, cols_base, 1 << 40, &shifts, &statics));
    reject!(gpu.prover_air_init_shard(0, cols_base, usize::MAX, &shifts, &statics));
    reject!(gpu.prover_air_init_shard(0, 0, AIR_ROWS, &shifts, &statics));
    reject!(gpu.prover_air_init_shard(0, (AIR_ROWS * 256 - 1) as u32, AIR_ROWS, &shifts, &statics));
    reject!(gpu.prover_air_read_tail(u32::MAX, 0, &mut one, &mut []));
    reject!(gpu.prover_air_read_tail(0, u32::MAX, &mut [], &mut two));
    // Rounds without an initialised shard.
    reject!(air_eval(&gpu, &dynamic, AIR_ROWS, cols_base));
    reject!(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, 0, 0, 48, fx.chal));

    macro_rules! reject_air {
        ($call:expr) => {{
            fx.commit(&gpu);
            gpu.prover_air_init_shard(0, cols_base, AIR_ROWS, &shifts, &statics)
                .expect("AIR shard init");
            assert_clean($call);
        }};
    }
    reject_air!(air_eval(&gpu, &dynamic, AIR_ROWS, u32::MAX));
    reject_air!(air_eval(&gpu, &dynamic, AIR_ROWS * 2, cols_base));
    reject_air!(air_eval(&gpu, &dynamic, 1 << 33, cols_base));
    reject_air!(air_eval(&gpu, &dynamic, 12, cols_base));
    reject_air!(gpu.prover_air_eval_round(
        true,
        AIR_ROWS,
        AIR_ROWS,
        1,
        false,
        cols_base,
        u32::MAX,
        IDLE_DYN_EXT4_OFF,
        &dynamic.words,
        dynamic.signers_off,
        dynamic.steps_off,
        dynamic.op_hdr_off,
        dynamic.op_ent_off,
        IDLE_SORTED_U64_OFF,
    ));
    for (signers, steps, hdr, ent, sorted, dyn_off) in [
        (
            u32::MAX,
            dynamic.steps_off,
            dynamic.op_hdr_off,
            dynamic.op_ent_off,
            IDLE_SORTED_U64_OFF,
            IDLE_DYN_EXT4_OFF,
        ),
        (
            dynamic.signers_off,
            u32::MAX,
            dynamic.op_hdr_off,
            dynamic.op_ent_off,
            IDLE_SORTED_U64_OFF,
            IDLE_DYN_EXT4_OFF,
        ),
        (
            dynamic.signers_off,
            dynamic.steps_off,
            u32::MAX,
            dynamic.op_ent_off,
            IDLE_SORTED_U64_OFF,
            IDLE_DYN_EXT4_OFF,
        ),
        (
            dynamic.signers_off,
            dynamic.steps_off,
            dynamic.op_hdr_off,
            u32::MAX,
            IDLE_SORTED_U64_OFF,
            IDLE_DYN_EXT4_OFF,
        ),
        (
            dynamic.signers_off,
            dynamic.steps_off,
            dynamic.op_hdr_off,
            dynamic.op_ent_off,
            u32::MAX,
            IDLE_DYN_EXT4_OFF,
        ),
        // Dynamic tables may not overwrite the static ones, nor leave the buffer.
        (
            dynamic.signers_off,
            dynamic.steps_off,
            dynamic.op_hdr_off,
            dynamic.op_ent_off,
            IDLE_SORTED_U64_OFF,
            0,
        ),
        (
            dynamic.signers_off,
            dynamic.steps_off,
            dynamic.op_hdr_off,
            dynamic.op_ent_off,
            IDLE_SORTED_U64_OFF,
            u32::MAX,
        ),
    ] {
        reject_air!(gpu.prover_air_eval_round(
            true,
            AIR_ROWS,
            AIR_ROWS,
            1,
            false,
            cols_base,
            0,
            dyn_off,
            &dynamic.words,
            signers,
            steps,
            hdr,
            ent,
            sorted,
        ));
    }
    // Table contents the shader would index with: a row index past the round, an opcode list
    // past its table, an unknown opcode, a column-selecting argument past the trace, and a
    // gamma block that starts inside the Group A gammas, ends past the static table, or lies
    // past the buffer.
    let hdr_word = ((dynamic.op_hdr_off - IDLE_DYN_EXT4_OFF) * 4) as usize;
    let ent_word = ((dynamic.op_ent_off - IDLE_DYN_EXT4_OFF) * 4) as usize;
    for (word, value) in [
        (hdr_word, u64::from(u32::MAX)),
        (hdr_word, 1 << 40),
        (hdr_word + 1, 5000),
        (hdr_word + 1, 9),
        (ent_word, 24),
        (ent_word, u64::MAX),
        (ent_word + 1, 1),
        (ent_word + 2, IDLE_GAMMA_BASE - 1),
        (ent_word + 2, IDLE_GAMMA_BASE + 3),
        (ent_word + 2, u64::from(u32::MAX)),
        (ent_word + 2, 1 << 40),
    ] {
        let mut bad = idle_air_dyn();
        bad.words[word] = value;
        reject_air!(air_eval(&gpu, &bad, AIR_ROWS, cols_base));
    }
    for bad_row in [8u64, u64::from(u32::MAX), 1 << 40] {
        let mut bad_static = statics.clone();
        bad_static[294][3] = bad_row;
        fx.commit(&gpu);
        gpu.prover_air_init_shard(0, cols_base, AIR_ROWS, &shifts, &bad_static)
            .expect("AIR shard init");
        assert_clean(air_eval(&gpu, &dynamic, AIR_ROWS, cols_base));
    }
    {
        // A pack-slot argument selects a trace column: 6 would be past the packed limbs.
        let mut bad = idle_air_dyn();
        bad.words[ent_word] = 8;
        bad.words[ent_word + 1] = 6;
        reject_air!(air_eval(&gpu, &bad, AIR_ROWS, cols_base));
    }
    reject_air!(gpu.prover_air_fold_round(true, AIR_ROWS, u32::MAX, 0, 0, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, u32::MAX, 0, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, 0, u32::MAX, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, 0, 0, u32::MAX, fx.chal));
    reject_air!(gpu.prover_air_fold_round(true, 1 << 33, cols_base, 0, 0, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(false, AIR_ROWS, 1 << 27, 0, 0, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(false, AIR_ROWS, 0, 0, 0, 48, fx.chal));
    reject_air!(gpu.prover_air_fold_round(true, AIR_ROWS, cols_base, 0, 0, 47, fx.chal));
    // A WHIR job that rewrites `vram_aux_in` invalidates the shard's tables.
    reject_air!({
        gpu.prover_whir_expand_monomial_and_dot(&kron, NUM_VARS, 1, &mut [])
            .expect("monomial table");
        air_eval(&gpu, &dynamic, AIR_ROWS, cols_base)
    });

    // The in-range AIR sequence still runs: init, evaluate, fold, read the folded shard back.
    fx.commit(&gpu);
    gpu.prover_air_init_shard(0, cols_base, AIR_ROWS, &shifts, &statics)
        .expect("AIR shard init");
    air_eval(&gpu, &dynamic, AIR_ROWS, cols_base).expect("AIR eval");
    gpu.prover_air_fold_round(
        true,
        AIR_ROWS,
        cols_base,
        0,
        0,
        (3 * AIR_ROWS) as u32,
        fx.chal,
    )
    .expect("AIR fold");
    let half = AIR_ROWS / 2;
    let mut cols = vec![[0u64; 4]; 256 * half];
    let mut folded_shifts = vec![[0u64; 4]; 3 * half];
    gpu.prover_air_read_tail(0, (3 * AIR_ROWS) as u32, &mut cols, &mut folded_shifts)
        .expect("AIR read tail");
    // Row-major shard `row * 256 + col` is the first `AIR_ROWS * 256` words of polynomial 0.
    for c in 0..256 {
        for idx in 0..half {
            let (r0, r1) = (
                fx.polys[0][idx * 256 + c],
                fx.polys[0][(idx + half) * 256 + c],
            );
            let want = e_add([r0, 0, 0, 0], e_scale(fx.chal, gl_sub(r1, r0)));
            assert_eq!(cols[c * half + idx], want, "column {c} row {idx}");
        }
    }
    for t in 0..3 {
        for idx in 0..half {
            let (v0, v1) = (
                shifts[t * AIR_ROWS + idx],
                shifts[t * AIR_ROWS + idx + half],
            );
            let want = e_add(v0, e_mul(fx.chal, e_sub(v1, v0)));
            assert_eq!(
                folded_shifts[t * half + idx],
                want,
                "shift table {t} row {idx}"
            );
        }
    }
    // One past the folded extent is refused.
    assert_clean(gpu.prover_air_read_tail(1 << 26, 0, &mut cols, &mut []));

    // Nothing above corrupted or quarantined the backend: the same round trip gives the same
    // commitment and the same host-checked data.
    assert_eq!(fx.round_trip(&gpu), top);
    assert_eq!(fx.round_trip(&gpu), top);
    drop(session);
    assert!(matches!(
        gpu.prover_whir_batch_sumcheck_read_tail(1, 1, 0, &mut one, &mut two),
        Err(VulkanError::WorkspacePoisoned)
    ));
}

#[test]
fn audit_hardening_bounds_receipts_and_turboshake_canopy() {
    let Some(gpu) = backend() else {
        return;
    };
    let fx = Fixture::new();

    // H3: Audited discrete backend exposes `is_secret_slots_audited() == true` and acquires a
    // secret prover session cleanly.
    assert!(gpu.is_secret_slots_audited());
    let session = gpu.try_acquire_secret_prover_session()
        .expect("secret prover session");

    // H1: Canopy leaf header 8-bit field bounds (`arity >= 256`, `num_polys >= 256`, `stage_idx >= 256`)
    // must be rejected cleanly on the host before any shader dispatch.
    let refs: Vec<&[u64]> = fx.polys.iter().map(Vec::as_slice).collect();
    assert_clean(gpu.prover_whir_commit_round0(
        &refs,
        &[0x42; 32],
        NUM_VARS,
        4,
        256,
        0,
        0,
        EXTRA_WITNESS_WORDS,
    ));
    let many_polys: Vec<&[u64]> = (0..256).map(|_| fx.polys[0].as_slice()).collect();
    assert_clean(gpu.prover_whir_commit_round0(
        &many_polys,
        &[0x42; 32],
        NUM_VARS,
        4,
        16,
        0,
        0,
        EXTRA_WITNESS_WORDS,
    ));
    let top_cshake = fx.commit(&gpu);
    assert_clean(gpu.prover_whir_commit_stage(256, 16, 64, 4));
    fx.commit(&gpu);
    assert_clean(gpu.prover_whir_commit_stage(1, 16, 512, 256));
    fx.commit(&gpu);
    assert_clean(gpu.prover_whir_gather_queries(256, 4, 1, 16, &[], &[1], &mut [0; 4]));

    // H2: `prover_whir_expand_monomial_and_dot` rejects 768-entry multilinear tables at `num_vars = 25`
    // (`mono_kronecker.len() == 768` only encodes 24 variables; `nv = 25..=26` requires `1536`).
    let poly25 = vec![1u64; 1 << 25];
    gpu.prover_whir_commit_round0(&[poly25.as_slice()], &[0x11; 32], 25, 4, 64, 0, 0, 0)
        .expect("nv=25 round0 commit");
    let kron768 = [[1u64, 0, 0, 0]; 768];
    assert_clean(gpu.prover_whir_expand_monomial_and_dot(&kron768, 25, 1, &mut []));
    drop(poly25);

    // H5: An out-of-range batch `run_job` call must NOT wipe or poison an active `ProverArena`!
    let top_before = fx.commit(&gpu);
    assert_eq!(top_before, top_cshake);
    let mut bad_ntt = vec![0u64; 3]; // Not a supported NTT power-of-two batch size
    assert!(gpu.goldilocks_ntt_canonical_inplace(&mut bad_ntt, false).is_err());
    gpu.prover_whir_batch_sumcheck_init(&fx.eq_tables, &fx.lambdas, NUM_VARS)
        .expect("active ProverArena must survive unrelated batch error");

    // TurboSHAKE256 Canopy GPU commitment (`turboshake_canopy = true`) succeeds and domain-separates
    // cleanly from 24-round `cSHAKE256` (`turboshake_canopy = false`).
    let top_turbo = gpu
        .prover_whir_commit_round0_with_mode(
            true,
            NUM_POLYS,
            &[0x42; 32],
            NUM_VARS,
            4,
            16,
            0,
            0,
            EXTRA_WITNESS_WORDS,
            |poly_idx, pos, dst| {
                dst.copy_from_slice(&fx.polys[poly_idx][pos..pos + dst.len()]);
            },
        )
        .expect("TurboSHAKE256 round0 commit");
    assert_ne!(top_turbo, top_cshake);
    let mut raw_q = vec![0u64; 2 + NUM_POLYS * 16 + 4];
    gpu.prover_whir_gather_queries(0, 16, NUM_POLYS, 1024, &[0], &[1], &mut raw_q)
        .expect("TurboSHAKE256 round0 gather");

    drop(session);
}

#[test]
fn fold_normalization_uses_independent_kernel_and_coefficient_offsets() {
    let Some(gpu) = backend() else { return; };
    let _session = gpu.try_acquire_prover_session().expect("session");
    let fx = Fixture::new();
    let run = |c_dst, k_dst, normalize| {
        fx.commit(&gpu);
        let mono: [[u64; 4]; 768] = fx.eq_tables[..768].try_into().unwrap();
        gpu.prover_whir_expand_monomial_and_dot(&mono, NUM_VARS, 1, &mut []).unwrap();
        let weights: Vec<_> = fx.lambdas.iter().map(|&l| [l, [0; 4]]).collect();
        gpu.prover_whir_open_init(NUM_VARS, false, &weights, &[[1, 0, 0, 0]; 1536]).unwrap();
        gpu.prover_whir_fold_pass_b(8, 0, 0, 8, k_dst, fx.chal).unwrap();
        gpu.prover_whir_fold_pass_c(8, 0, c_dst, fx.chal, fx.chal, fx.chal, normalize, 9).unwrap();
        gpu.prover_whir_fold_pass_a(4, if normalize { 0 } else { c_dst }, if normalize { 0 } else { k_dst }).unwrap()
    };
    for (c_dst, k_dst) in [(64, 64), (64, 128), (128, 64)] {
        assert_eq!(run(c_dst, k_dst, true), run(c_dst, k_dst, false), "c={c_dst}, k={k_dst}");
    }
}

#[test]
fn partial_safe_upload_callback_cannot_read_previous_witness() {
    let Some(gpu) = backend() else { return; };
    let _session = gpu.try_acquire_prover_session().expect("session");
    let fx = Fixture::new();
    fx.commit(&gpu);
    let partial = gpu.prover_whir_commit_round0_with(1, &[3; 32], NUM_VARS, 4, 16, 0, 0, 0,
        |_, _, dst| {
            assert!(dst.iter().all(|&w| w == 0), "callback saw stale staging words");
            dst[0] = 9;
        }).unwrap();
    let mut expected = vec![0u64; C_LEN]; expected[0] = 9;
    let full = gpu.prover_whir_commit_round0(&[&expected], &[3; 32], NUM_VARS, 4, 16, 0, 0, 0).unwrap();
    assert_eq!(partial, full);
}
