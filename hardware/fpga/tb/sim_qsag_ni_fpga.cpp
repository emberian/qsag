// Cycle-accurate Verilator testbench for the QSAG-NI FPGA core.
//   -DQSAG_UNITS : drives tb/qsag_units_tb.sv (every arithmetic unit, pipeline by pipeline)
//   -DQSAG_TOP   : drives rtl/qsag_ni_fpga_top.sv through its AXI4-Lite / AXI4-Stream ports
// Expected values come from tb/qsag_model.h, which is first checked against the Lean oracle
// vectors of validation/tests/fixtures/lean_external_oracle_vectors.json (build/kat_vectors.h).
#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <map>
#include <memory>
#include <string>
#include <verilated.h>
#include "qsag_model.h"
#include "kat_vectors.h"

#if defined(QSAG_UNITS)
#include "Vqsag_units_tb.h"
typedef Vqsag_units_tb Dut;
#else
#include "Vqsag_ni_fpga_top.h"
typedef Vqsag_ni_fpga_top Dut;
#endif

static const int GL_MUL_LAT = 5, RED_LAT = 2, P2_SBOX_LAT = 13, EXT5_MAC_LAT = 7, GF128_LAT = 3;
static const int P2_RING_LEN = 16, P2_PASSES = 31, P2_PIPE_LAT = 453;
#if defined(QSAG_ECP5_FULLRATE)
static constexpr bool COMPACT = true;
static const int TOP_P2_LAT = 1314, TOP_KEC_RPC = 1, CHAIN_SLOTS = 32;
static const char* PROFILE_NAME = "ECP5_FULLRATE";
#elif defined(QSAG_COMPACT)
static constexpr bool COMPACT = true;
static const int TOP_P2_LAT = 1878, TOP_KEC_RPC = 1, CHAIN_SLOTS = 32;
static const char* PROFILE_NAME = "ECP5_COMPACT";
#elif defined(QSAG_PIPE)
static constexpr bool COMPACT = false;
static const int TOP_P2_LAT = P2_PIPE_LAT - 1, TOP_KEC_RPC = 2, CHAIN_SLOTS = 256;
static const char* PROFILE_NAME = "VU9P_TURBO";
#else
static constexpr bool COMPACT = false;
static const int TOP_P2_LAT = P2_PASSES*P2_RING_LEN, TOP_KEC_RPC = 2, CHAIN_SLOTS = 32;
static const char* PROFILE_NAME = "XCUP_RING";
#endif

static std::unique_ptr<Dut> dut;
static uint64_t cyc = 0;
static long checks = 0, fails = 0, shown = 0;

static void tick() {
    dut->clk = 0; dut->eval();
    dut->clk = 1; dut->eval();
    cyc++;
}
static void check(bool ok, const char* what) {
    checks++;
    if (!ok) {
        fails++;
        if (shown++ < 8) printf("  MISMATCH: %s (cycle %llu)\n", what, (unsigned long long)cyc);
    }
}
#define CHECK_EQ64(got, want, what) do { uint64_t g_ = (got), w_ = (want); checks++; if (g_ != w_) { fails++; \
    if (shown++ < 8) printf("  MISMATCH %s: got %016llx want %016llx (cycle %llu)\n", what, \
        (unsigned long long)g_, (unsigned long long)w_, (unsigned long long)cyc); } } while (0)

template <typename W> static void set64(W& w, int lane, uint64_t v) { w[2 * lane] = (uint32_t)v; w[2 * lane + 1] = (uint32_t)(v >> 32); }
template <typename W> static uint64_t get64(const W& w, int lane) { return (uint64_t)w[2 * lane] | ((uint64_t)w[2 * lane + 1] << 32); }

static int section(const char* name, long before_checks, long before_fails) {
    shown = 0;
    printf("[%s] %s: %ld checks, %ld mismatches\n", (fails == before_fails) ? "PASS" : "FAIL", name,
           checks - before_checks, fails - before_fails);
    return fails == before_fails ? 0 : 1;
}

// The reference model must reproduce the Lean oracle vectors before it is trusted as a referee.
static void model_selfcheck() {
    long c0 = checks, f0 = fails;
    for (auto& k : KAT_GL) {
        CHECK_EQ64(gl_mul(k.a_raw, k.b_raw), k.mul, "model gl_mul");
        CHECK_EQ64(gl_pow7(k.a_raw), k.pow7_a, "model gl_pow7");
    }
    for (auto& k : KAT_P2) {
        St12 s;
        for (int i = 0; i < 12; i++) s[i] = k.in[i];
        p2_perm(s);
        for (int i = 0; i < 12; i++) CHECK_EQ64(s[i], k.out[i], "model poseidon2");
    }
    KPerm mp = [](KState& s, bool nr12) { keccak_p(s, nr12); };
    for (auto& k : KAT_SPONGE) {
        auto msg = from_hex(k.msg);
        check(to_hex(keccak_sponge(msg, 0x06, 32, false, mp)) == k.sha3_256, "model sha3-256");
        check(to_hex(keccak_sponge(msg, 0x1F, 64, false, mp)) == k.shake256_64, "model shake256");
        check(to_hex(cshake256(msg, KAT_CSHAKE_CUSTOM, 64, mp)) == k.cshake256_64, "model cshake256");
    }
    // RFC 9861 TurboSHAKE256(M = empty, D = 0x1F, 64 bytes).
    check(to_hex(keccak_sponge({}, 0x1F, 64, true, mp)) ==
          "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
          "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0", "model turboshake256 rfc9861");
    // qsag-asm pins x * x^127 = x^128 = 0x87.
    check(gf128_mul(2, (u128)1 << 127) == 0x87, "model gf128 x^128");
    // zk-Hem v2 Fp5 = F_p[X]/(X^5 - 3) KATs (crates/qsag-agg/src/zk_hem/v2/field5.rs).
    {
        E5 a = {1, 2, 3, 4, 5}, b = {6, 7, 8, 9, 10};
        E5 want_ab = {348, 337, 295, 220, 110}, want_sq = {133, 142, 130, 95, 35};
        E5 want_frob = {1ULL, 2082576518476559110ULL, 10568986813412808496ULL, 846350220555798788ULL, 6865216354783480110ULL};
        E5 ab = e5_mul(a, b), sq = e5_mul(a, a), fr = e5_frobenius(a, 1);
        for (int i = 0; i < 5; i++) {
            CHECK_EQ64(ab[i], want_ab[i], "model fp5 mul KAT");
            CHECK_EQ64(sq[i], want_sq[i], "model fp5 sq KAT");
            CHECK_EQ64(fr[i], want_frob[i], "model fp5 frobenius KAT");
        }
    }
    section("reference model vs Lean oracle vectors / RFC 9861 / zk-Hem v2 Fp5", c0, f0);
}

// =====================================================================================
#if defined(QSAG_UNITS)

template <typename T> struct Pipe {
    std::deque<std::pair<uint64_t, T>> q;
    void push(int lat, const T& v) { q.push_back({cyc + lat, v}); }
    bool due(T& v) { if (!q.empty() && q.front().first == cyc) { v = q.front().second; q.pop_front(); return true; } return false; }
};

static void test_mul_red_sbox_fp5_gf() {
    long c0 = checks, f0 = fails;
    Rng rng(0x51534147);
    std::vector<std::pair<uint64_t, uint64_t>> vec;
    for (auto& k : KAT_GL) vec.push_back({k.a_raw, k.b_raw});
    static const uint64_t E[] = {0, 1, 2, GLP - 1, GLP, GLP + 1, ~0ULL, 0xFFFFFFFFULL, 0x100000000ULL,
                                 0xFFFFFFFF00000000ULL, 0x8000000000000000ULL, 0xFFFFFFFEFFFFFFFFULL};
    for (uint64_t a : E) for (uint64_t b : E) vec.push_back({a, b});
    const size_t N = 200000;
    Pipe<uint64_t> pm, ps;
    Pipe<std::pair<uint8_t, u128>> pr;
    Pipe<E5> pe5;
    Pipe<u128> pg, pt;
    for (size_t i = 0; i < N + 64; i++) {
        bool live = i < N;
        // multiplier
        uint64_t a = i < vec.size() ? vec[i].first : rng.edge();
        uint64_t b = i < vec.size() ? vec[i].second : rng.edge();
        dut->mul_a = a; dut->mul_b = b;
        if (live) pm.push(GL_MUL_LAT, gl_mul(a, b));
        // 136-bit reducer
        uint64_t lo = rng.edge(), hi = rng.edge();
        uint8_t t = (uint8_t)rng.next();
        if (i < 4) { lo = ~0ULL; hi = ~0ULL; t = 0xFF; }
        dut->red_x[0] = (uint32_t)lo; dut->red_x[1] = (uint32_t)(lo >> 32);
        dut->red_x[2] = (uint32_t)hi; dut->red_x[3] = (uint32_t)(hi >> 32); dut->red_x[4] = t;
        if (live) pr.push(RED_LAT, {t, ((u128)hi << 64) | lo});
        // S-box
        uint64_t sx = i < 7 ? KAT_GL[i].a_raw : rng.edge();
        dut->sb_x = sx;
        if (live) ps.push(P2_SBOX_LAT, gl_pow7(sx));
        // Ext5 MAC (zk-Hem v2 F_p[X]/(X^5 - 3))
        E5 e5a = rng.e5(), e5b = rng.e5(), e5c = rng.e5();
        if (i == 0) { e5a = {1, 2, 3, 4, 5}; e5b = {6, 7, 8, 9, 10}; e5c = {0, 0, 0, 0, 0}; }
        else if (i == 1) { e5a = {1, 2, 3, 4, 5}; e5b = {1, 2, 3, 4, 5}; e5c = {0, 0, 0, 0, 0}; }
        else if (i < 40) {
            for (int j = 0; j < 5; j++) { e5a[j] = (rng.next() & 1) ? GLP - 1 : rng.gl(); e5b[j] = (rng.next() & 1) ? GLP - 1 : rng.gl(); e5c[j] = GLP - 1; }
        }
        for (int j = 0; j < 5; j++) { set64(dut->e5_a, j, e5a[j]); set64(dut->e5_b, j, e5b[j]); set64(dut->e5_c, j, e5c[j]); }
        if (live) pe5.push(EXT5_MAC_LAT, e5_mul_add(e5a, e5b, e5c));
        // GF(2^128)
        u128 ga = ((u128)rng.next() << 64) | rng.next(), gb = ((u128)rng.next() << 64) | rng.next();
        if (i == 0) { ga = 2; gb = (u128)1 << 127; }
        if (i == 1) { ga = ~(u128)0; gb = ~(u128)0; }
        if (i<8) {
            auto& t=KAT_TOWER[i%4];
            ga=(u128(t.a[1])<<64)|t.a[0];
            gb=i<4 ? (u128(t.b[1])<<64)|t.b[0] : (u128(t.inv[1])<<64)|t.inv[0];
            u128 want=i<4 ? (u128(t.mul[1])<<64)|t.mul[0] : (ga ? 1:0);
            pt.push(GF128_LAT,want);
        }
        set64(dut->gf_a, 0, (uint64_t)ga); set64(dut->gf_a, 1, (uint64_t)(ga >> 64));
        set64(dut->gf_b, 0, (uint64_t)gb); set64(dut->gf_b, 1, (uint64_t)(gb >> 64));
        if (live && i < 40000) pg.push(GF128_LAT, gf128_mul(ga, gb));

        tick();

        uint64_t w; std::pair<uint8_t, u128> rw; E5 e5w; u128 gw;
        if (pm.due(w)) { CHECK_EQ64(dut->mul_r, w, "gl64 mul 26x17"); CHECK_EQ64(dut->mul_r16, w, "gl64 mul 16x16"); }
        if (pr.due(rw)) CHECK_EQ64(dut->red_r, gl_red136(rw.first, rw.second), "gl64 reduce136");
        if (ps.due(w)) CHECK_EQ64(dut->sb_y, w, "sbox x^7");
        if (pe5.due(e5w)) for (int j = 0; j < 5; j++) CHECK_EQ64(get64(dut->e5_y, j), e5w[j], "ext5 mac");
        if (pg.due(gw)) { CHECK_EQ64(get64(dut->gf_r, 0), (uint64_t)gw, "gf128 lo"); CHECK_EQ64(get64(dut->gf_r, 1), (uint64_t)(gw >> 64), "gf128 hi"); }
        if (pt.due(gw)) { CHECK_EQ64(get64(dut->tower_r,0),(uint64_t)gw,"tower KAT lo"); CHECK_EQ64(get64(dut->tower_r,1),(uint64_t)(gw>>64),"tower KAT hi"); }
    }
    check(pm.q.empty() && pr.q.empty() && ps.q.empty() && pe5.q.empty() && pg.q.empty() && pt.q.empty(), "pipelines drained");
    section("gl64 mul (9-DSP) / reduce136 / x^7 / Ext5 MAC / GF(2^128): KATs, edges, 200k random", c0, f0);
}

struct P2Job { St12 in; bool jive; uint64_t t_in; };

static void expect_p2(const P2Job& j, const VlWide<24>& out, const char* what) {
    if (j.jive) {
        D4 d = p2_jive(j.in);
        for (int i = 0; i < 4; i++) CHECK_EQ64(get64(out, i), d[i], what);
    } else {
        St12 s = j.in;
        p2_perm(s);
        for (int i = 0; i < 12; i++) CHECK_EQ64(get64(out, i), s[i], what);
    }
}
static P2Job make_job(Rng& rng, size_t i) {
    P2Job j;
    j.jive = false;
    if (i < 4) {
        for (int l = 0; l < 12; l++) j.in[l] = KAT_P2[i].in[l];
    } else {
        for (int l = 0; l < 12; l++) j.in[l] = (i % 5 == 0) ? rng.edge() : rng.gl();
        j.jive = (i % 3 == 0);
    }
    return j;
}

static void test_p2_ring() {
    long c0 = checks, f0 = fails;
    Rng rng(0xC0FFEE);
    const size_t N = 150;
    std::map<uint16_t, P2Job> live;
    size_t sent = 0, done = 0;
    uint64_t t_start = cyc, max_inflight = 0, lat_min = ~0ULL, lat_max = 0;
    P2Job pending = make_job(rng, 0);
    while (done < N) {
        bool offer = sent < N;
        dut->ring_in_valid = offer;
        if (offer) {
            for (int l = 0; l < 12; l++) set64(dut->ring_in_state, l, pending.in[l]);
            dut->ring_in_jive = pending.jive;
            dut->ring_in_tag = (uint16_t)sent;
        }
        dut->clk = 0; dut->eval();
        bool acc = offer && dut->ring_in_ready;
        dut->clk = 1; dut->eval(); cyc++;
        if (acc) {
            pending.t_in = cyc;
            live[(uint16_t)sent] = pending;
            sent++;
            if (sent < N) pending = make_job(rng, sent);
        }
        if (dut->ring_out_valid) {
            uint16_t tag = dut->ring_out_tag;
            auto it = live.find(tag);
            check(it != live.end(), "ring tag known");
            if (it != live.end()) {
                expect_p2(it->second, dut->ring_out_state, "poseidon2 ring core");
                check((bool)dut->ring_out_jive == it->second.jive, "ring jive flag");
                uint64_t lat = cyc - it->second.t_in;
                if (lat < lat_min) lat_min = lat;
                if (lat > lat_max) lat_max = lat;
                live.erase(it);
            }
            done++;
        }
        if (live.size() > max_inflight) max_inflight = live.size();
    }
    dut->ring_in_valid = 0;
    uint64_t total = cyc - t_start;
    check(lat_min == (uint64_t)P2_PASSES * P2_RING_LEN && lat_max == lat_min, "ring latency = 31 * 21");
    check(max_inflight == (uint64_t)P2_RING_LEN, "ring holds 21 jobs");
    printf("  ring core: latency %llu clocks/permutation (min=max), %llu jobs in flight, %zu permutations in %llu clocks (%.2f clocks/perm)\n",
           (unsigned long long)lat_min, (unsigned long long)max_inflight, N, (unsigned long long)total, (double)total / N);
    section("Poseidon2 ring core: 4 Lean KATs + 146 random perms / feed-forward hashes, C-slow interleaved", c0, f0);
}

static void test_p2_pipe() {
    long c0 = checks, f0 = fails;
    Rng rng(0xBADC0DE);
    const size_t N = 1200;
    std::deque<P2Job> q;
    size_t done = 0;
    uint64_t t_first_in = 0, t_first_out = 0, t_last_out = 0;
    for (size_t i = 0; done < N; i++) {
        bool v = i < N;
        dut->pipe_in_valid = v;
        if (v) {
            P2Job j = make_job(rng, i);
            for (int l = 0; l < 12; l++) set64(dut->pipe_in_state, l, j.in[l]);
            dut->pipe_in_jive = j.jive;
            dut->pipe_in_tag = (uint16_t)i;
            j.t_in = cyc;
            q.push_back(j);
            if (i == 0) t_first_in = cyc;
        }
        tick();
        if (dut->pipe_out_valid) {
            check(dut->pipe_out_tag == (uint16_t)done, "pipe tag order");
            expect_p2(q.front(), dut->pipe_out_state, "poseidon2 pipelined core");
            check(cyc - q.front().t_in == (uint64_t)P2_PIPE_LAT, "pipe latency");
            q.pop_front();
            if (done == 0) t_first_out = cyc;
            t_last_out = cyc;
            done++;
        }
    }
    dut->pipe_in_valid = 0;
    check(t_last_out - t_first_out == N - 1, "pipe: one permutation per clock");
    printf("  pipelined core: latency %llu clocks, %zu permutations out in %llu consecutive clocks\n",
           (unsigned long long)(t_first_out - t_first_in), N, (unsigned long long)(t_last_out - t_first_out + 1));
    section("Poseidon2 pipelined core: 4 Lean KATs + 1196 random, back to back", c0, f0);
}

static uint64_t kec_cycles[2][2];
static void rtl_keccak(KState& s, bool nr12) {
    KState want = s;
    keccak_p(want, nr12);
    for (int i = 0; i < 25; i++) set64(dut->kec_state_i, i, s[i]);
    dut->kec_nr12 = nr12;
    dut->kec_start = 1;
    tick();
    dut->kec_start = 0;
    uint64_t t0 = cyc;
    bool d1 = false, d2 = false;
    for (int g = 0; g < 40 && !(d1 && d2); g++) {
        tick();
        if (dut->kec1_done && !d1) {
            d1 = true; kec_cycles[0][nr12] = cyc - t0;
            for (int i = 0; i < 25; i++) CHECK_EQ64(get64(dut->kec1_state_o, i), want[i], "keccak 1 round/clk");
        }
        if (dut->kec2_done && !d2) {
            d2 = true; kec_cycles[1][nr12] = cyc - t0;
            for (int i = 0; i < 25; i++) CHECK_EQ64(get64(dut->kec2_state_o, i), want[i], "keccak 2 rounds/clk");
        }
    }
    check(d1 && d2, "keccak done");
    for (int i = 0; i < 25; i++) s[i] = get64(dut->kec2_state_o, i);
}

static uint64_t kcmp_cycles[2];
static void kcmp_issue(uint8_t op, bool nr12, uint8_t idx, uint64_t wdata) {
    dut->kcmp_op = op; dut->kcmp_nr12 = nr12; dut->kcmp_idx = idx; dut->kcmp_wdata = wdata;
    dut->kcmp_valid = 1;
    for (;;) {
        dut->clk = 0; dut->eval();
        bool rdy = dut->kcmp_ready;
        dut->clk = 1; dut->eval(); cyc++;
        if (rdy) break;
    }
    dut->kcmp_valid = 0;
}
static void rtl_keccak_compact(KState& s, bool nr12) {
    KState want = s;
    keccak_p(want, nr12);
    for (int i = 0; i < 25; i++) kcmp_issue(0, false, (uint8_t)i, s[i]);
    kcmp_issue(2, nr12, 0, 0);
    uint64_t t0 = cyc;
    while (!dut->kcmp_done) tick();
    kcmp_cycles[nr12] = cyc - t0;
    for (int i = 0; i < 25; i++) {
        kcmp_issue(3, false, (uint8_t)i, 0);
        while (!dut->kcmp_rd_valid) tick();
        CHECK_EQ64(dut->kcmp_rd_data, want[i], "keccak_compact N^4=I 1-RAM");
        s[i] = dut->kcmp_rd_data;
    }
}

static void test_keccak() {
    long c0 = checks, f0 = fails;
    KPerm hw = rtl_keccak;
    KPerm hwc = rtl_keccak_compact;
    for (auto& k : KAT_SPONGE) {
        auto msg = from_hex(k.msg);
        check(to_hex(keccak_sponge(msg, 0x06, 32, false, hw)) == k.sha3_256, "rtl sha3-256 KAT");
        check(to_hex(keccak_sponge(msg, 0x1F, 64, false, hw)) == k.shake256_64, "rtl shake256 KAT");
        check(to_hex(cshake256(msg, KAT_CSHAKE_CUSTOM, 64, hw)) == k.cshake256_64, "rtl cshake256 KAT");
    }
    check(to_hex(keccak_sponge({}, 0x1F, 64, true, hw)) ==
          "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
          "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0", "rtl turboshake256 rfc9861");
    check(to_hex(keccak_sponge({}, 0x1F, 64, true, hwc)) ==
          "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
          "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0", "rtl compact turboshake256 rfc9861");
    check(to_hex(keccak_sponge(from_hex(KAT_SPONGE[0].msg), 0x06, 32, false, hwc)) == KAT_SPONGE[0].sha3_256, "rtl compact sha3-256 KAT");
    // qsag's Role-1 domain byte 0x07 (including 400-bit = 50-byte zk-Hem v2 commitment), against the model.
    Rng rng(7);
    std::vector<uint8_t> m(1000);
    for (auto& b : m) b = (uint8_t)rng.next();
    KPerm mp = [](KState& s, bool n) { keccak_p(s, n); };
    check(keccak_sponge(m, 0x07, 200, true, hw) == keccak_sponge(m, 0x07, 200, true, mp), "rtl turboshake256 D=07");
    check(keccak_sponge(m, 0x07, 50, true, hwc) == keccak_sponge(m, 0x07, 50, true, mp), "rtl compact turboshake256 400-bit D=07");
    check(kec_cycles[0][0] == 24 && kec_cycles[0][1] == 12 && kec_cycles[1][0] == 12 && kec_cycles[1][1] == 6, "keccak cycle counts");
    check(kcmp_cycles[0] == 746 && kcmp_cycles[1] == 386, "keccak_compact 30-clk/rnd cycle counts (26+30*nr)");
    printf("  keccak clocks per permutation: 1 round/clk %llu (f1600) / %llu (p1600,12); 2 rounds/clk %llu / %llu; compact N^4=I %llu / %llu\n",
           (unsigned long long)kec_cycles[0][0], (unsigned long long)kec_cycles[0][1],
           (unsigned long long)kec_cycles[1][0], (unsigned long long)kec_cycles[1][1],
           (unsigned long long)kcmp_cycles[0], (unsigned long long)kcmp_cycles[1]);
    section("Keccak cores (parallel 1/2-rpc + compact 1-RAM N^4=I): SHA3/SHAKE/cSHAKE, RFC 9861, 400-bit D=0x07", c0, f0);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    dut.reset(new Dut);
    model_selfcheck();
    // --x-initial unique randomises the inputs too: drive every control input before reset.
    dut->ring_in_valid = 0; dut->pipe_in_valid = 0; dut->kec_start = 0; dut->kec_nr12 = 0;
    dut->kcmp_valid = 0; dut->kcmp_op = 0; dut->kcmp_nr12 = 0; dut->kcmp_idx = 0; dut->kcmp_wdata = 0;
    dut->ring_in_jive = 0; dut->pipe_in_jive = 0; dut->ring_in_tag = 0; dut->pipe_in_tag = 0;
    dut->rst = 1;
    for (int i = 0; i < 4; i++) tick();
    dut->rst = 0;
    test_mul_red_sbox_fp5_gf();
    test_p2_ring();
    test_p2_pipe();
    test_keccak();
    printf("UNITS: %ld checks, %ld mismatches, %llu clocks simulated\n", checks, fails, (unsigned long long)cyc);
    dut->final();
    dut.reset();
    return fails ? 1 : 0;
}

// =====================================================================================
#else  // QSAG_TOP

static const uint32_t R_CMD = 0x000, R_STATUS = 0x004, R_OPCYC = 0x008, R_TOT_LO = 0x00C, R_TOT_HI = 0x010,
                      R_ARG32 = 0x014, R_CH_DONE = 0x018, R_CH_OK = 0x01C, R_STREAM = 0x020, R_CH_BUSY = 0x024,
                      R_ID = 0x028, R_PERMS = 0x02C, R_X = 0x100, R_Y = 0x200;

static uint64_t bus_writes = 0, bus_reads = 0, stream_beats = 0;

static void axil_write(uint32_t addr, uint32_t data, uint8_t strobe = 15) {
    dut->s_axil_awaddr = addr; dut->s_axil_awvalid = 1;
    dut->s_axil_wdata = data; dut->s_axil_wstrb = strobe; dut->s_axil_wvalid = 1;
    dut->s_axil_bready = 1;
    for (;;) {
        dut->clk = 0; dut->eval();
        bool fire = dut->s_axil_awready && dut->s_axil_wready;
        dut->clk = 1; dut->eval(); cyc++;
        if (fire) break;
    }
    dut->s_axil_awvalid = 0; dut->s_axil_wvalid = 0;
    while (!dut->s_axil_bvalid) tick();
    tick();
    bus_writes++;
}
static uint32_t axil_read(uint32_t addr) {
    dut->s_axil_araddr = addr; dut->s_axil_arvalid = 1; dut->s_axil_rready = 1;
    for (;;) {
        dut->clk = 0; dut->eval();
        bool fire = dut->s_axil_arready;
        dut->clk = 1; dut->eval(); cyc++;
        if (fire) break;
    }
    dut->s_axil_arvalid = 0;
    while (!dut->s_axil_rvalid) tick();
    uint32_t v = dut->s_axil_rdata;
    tick();
    bus_reads++;
    return v;
}
static void set_x(int i, uint64_t v) { axil_write(R_X + 8 * i, (uint32_t)v); axil_write(R_X + 8 * i + 4, (uint32_t)(v >> 32)); }
static uint64_t get_y(int i) { uint64_t lo = axil_read(R_Y + 8 * i); return lo | ((uint64_t)axil_read(R_Y + 8 * i + 4) << 32); }
static void set_x4(int base, const D4& e) { for (int i = 0; i < 4; i++) set_x(base + i, e[i]); }
static D4 get_y4() { return D4{get_y(0), get_y(1), get_y(2), get_y(3)}; }

struct OpRes { bool ok; uint32_t cycles; };
static uint64_t opcode_cycles[256]{};
static OpRes wait_op(uint8_t op = 0) {
    uint32_t st;
    for (long guard = 0;; guard++) {
        st = axil_read(R_STATUS);
        if (st & 2) break;
        if (guard > 50000000) { printf("timeout in op %02x\n", op); exit(2); }
    }
    uint32_t cycles=axil_read(R_OPCYC);
    opcode_cycles[op]+=cycles;
    return OpRes{(st & 4) != 0, cycles};
}
// Start an operation, poll until done, return its ok flag and the core's own cycle count.
static OpRes run_op(uint8_t op, uint8_t a0 = 0, uint16_t a1 = 0) {
    axil_write(R_CMD, (uint32_t)op | ((uint32_t)a0 << 8) | ((uint32_t)a1 << 16));
    return wait_op(op);
}
static void stream_beat(const uint64_t* lanes, int n) {
    for (int i = 0; i < 8; i++) set64(dut->s_axis_tdata, i, i < n ? lanes[i] : 0);
    dut->s_axis_tvalid = 1;
    for (;;) {
        dut->clk = 0; dut->eval();
        bool fire = dut->s_axis_tready;
        dut->clk = 1; dut->eval(); cyc++;
        if (fire) break;
    }
    dut->s_axis_tvalid = 0;
    stream_beats++;
}
static uint64_t total_cycles() { return (uint64_t)axil_read(R_TOT_LO) | ((uint64_t)axil_read(R_TOT_HI) << 32); }

// ---- Canopy tree in software: heap layout, node 1 is the top, leaves at 2^depth + i.
struct Tree {
    int depth;
    uint64_t key[3];
    std::vector<D4> node;
    Tree(int d, Rng& rng) : depth(d), node((size_t)2 << d) {
        for (auto& k : key) k = rng.gl();
        for (size_t i = (size_t)1 << d; i < ((size_t)2 << d); i++) node[i] = D4{rng.gl(), rng.gl(), rng.gl(), rng.gl()};
    }
    void build() {
        for (size_t n = ((size_t)1 << depth) - 1; n >= 1; n--) node[n] = p2_canopy_node(node[2 * n], node[2 * n + 1], (uint32_t)n, key);
    }
};
static const uint64_t LEAF_DOMAIN = 0x5153414746504741ULL % GLP;

// Load one chain into a slot: sponge blocks of the leaf data, then the siblings bottom-up.
// Returns the number of Poseidon2 permutations the chain needs.
// The chain's initial sponge state [0 x 8, cap] must already be in X[0..11] (chain_init).
static int load_chain(int slot, const Tree& t, uint32_t leaf, const std::vector<uint64_t>& leaf_limbs,
                      bool corrupt = false) {
    auto blocks = p2_sponge_blocks(LEAF_DOMAIN, leaf_limbs);
    axil_write(R_STREAM, (uint32_t)slot << 6);
    for (auto& b : blocks) stream_beat(b.data(), 8);
    uint32_t n = ((uint32_t)1 << t.depth) + leaf;
    for (int lvl = 0; lvl < t.depth; lvl++) {
        D4 sib = t.node[n ^ 1];
        if (corrupt && lvl == t.depth / 2) sib[2] = gl_add(sib[2], 1);
        stream_beat(sib.data(), 4);
        n >>= 1;
    }
    axil_write(R_ARG32, ((uint32_t)1 << t.depth) + leaf);
    OpRes r = run_op(0x04, (uint8_t)slot, (uint16_t)blocks.size());
    check(r.ok, "chain start");
    return (int)blocks.size() + t.depth;
}
// Tree key and expected top node, then the common initial sponge state of every chain.
static void chain_cfg(const Tree& t, const D4& cap) {
    for (int i = 0; i < 3; i++) set_x(i, t.key[i]);
    for (int i = 0; i < 4; i++) set_x(4 + i, t.node[1][i]);
    run_op(0x03, 1);
    for (int i = 0; i < 8; i++) set_x(i, 0);
    for (int i = 0; i < 4; i++) set_x(8 + i, cap[i]);
}

// AW and W may arrive in either order; B and R must remain stable under stalls.
static void test_axi_channels() {
    long c0=checks, f0=fails;
    uint32_t expected=0;
    axil_write(R_ARG32, expected);
    for (int n=0;n<32;n++) {
        uint32_t value=0x9e3779b9u*(n+1), mask=n&15;
        dut->s_axil_bready=0;
        dut->s_axil_awaddr=R_ARG32; dut->s_axil_wdata=value; dut->s_axil_wstrb=mask;
        dut->s_axil_awvalid=0; dut->s_axil_wvalid=0;
        bool aw=false,w=false;
        for (int t=0;t<40 && !(aw&&w);t++) {
            dut->s_axil_awvalid=!aw && t>=(n%2 ? 4:0);
            dut->s_axil_wvalid=!w && t>=(n%2 ? 0:4);
            dut->clk=0; dut->eval();
            bool aa=dut->s_axil_awvalid && dut->s_axil_awready;
            bool ww=dut->s_axil_wvalid && dut->s_axil_wready;
            tick(); aw|=aa; w|=ww;
        }
        dut->s_axil_awvalid=0; dut->s_axil_wvalid=0;
        check(aw&&w,"independent AW/W handshakes");
        for(int t=0;t<8 && !dut->s_axil_bvalid;t++) tick();
        for(int t=0;t<5;t++) { check(dut->s_axil_bvalid && dut->s_axil_bresp==0,"B stable under stall"); tick(); }
        dut->s_axil_bready=1; tick();
        for(int b=0;b<4;b++) if(mask>>b&1) expected=(expected&~(255u<<(8*b)))|(value&(255u<<(8*b)));
        CHECK_EQ64(axil_read(R_ARG32),expected,"byte strobes");
        dut->s_axil_rready=0; dut->s_axil_arvalid=1; dut->s_axil_araddr=R_ARG32;
        tick(); dut->s_axil_arvalid=0;
        for(int t=0;t<5;t++) { check(dut->s_axil_rvalid && dut->s_axil_rdata==expected && dut->s_axil_rresp==0,"R stable under stall"); tick(); }
        dut->s_axil_rready=1; tick();
    }
    // Exercise every X half-word, including byte preservation and the
    // independent read port while ARADDR changes and RREADY is held low.
    for (unsigned w = 0; w < 64; ++w) {
        uint32_t addr = R_X + 4*w, old = 0x01234567u + w, value = 0x89abcdefu - w;
        unsigned strobe = (w ^ (w >> 2)) & 15;
        axil_write(addr, old);
        axil_write(addr, value, strobe);
        uint32_t want = old;
        for (unsigned b = 0; b < 4; ++b) {
            uint32_t mask = (strobe >> b & 1) ? 255u << (8*b) : 0;
            want = (want & ~mask) | (value & mask);
        }
        dut->s_axil_rready = 0;
        dut->s_axil_arvalid = 1;
        dut->s_axil_araddr = addr;
        tick();
        dut->s_axil_arvalid = 0;
        dut->s_axil_araddr = R_ID;
        tick();
        axil_write(addr, ~want);
        check(dut->s_axil_rvalid && dut->s_axil_rresp == 0, "X response held across write");
        CHECK_EQ64(dut->s_axil_rdata, COMPACT ? 0 : want, "X stalled byte-strobed read");
        dut->s_axil_rready = 1;
        tick();
        CHECK_EQ64(axil_read(addr), COMPACT ? 0 : ~want, "X subsequent read");
    }
    // Reset discards an unmatched address rather than pairing it with future data.
    dut->s_axil_awaddr=R_CMD; dut->s_axil_awvalid=1; tick(); dut->s_axil_awvalid=0;
    dut->rst=1; tick(); dut->rst=0; tick();
    axil_write(R_ARG32,0x12345678);
    CHECK_EQ64(axil_read(R_ARG32),0x12345678,"reset flushes AW skid");
    check(!(axil_read(R_STATUS)&1),"reset did not launch stale command");
    section("AXI skew, byte enables, stalled B/R, reset flush",c0,f0);
}

static void test_basic_ops() {
    long c0 = checks, f0 = fails;
    check(axil_read(R_ID) == 0x51534E49, "ID register");
    Rng rng(0xA11CE);
    // Poseidon2 permutation KATs and a feed-forward hash.
    for (auto& k : KAT_P2) {
        for (int i = 0; i < 12; i++) set_x(i, k.in[i]);
        OpRes r = run_op(0x01);
        for (int i = 0; i < 12; i++) CHECK_EQ64(get_y(i), k.out[i], "top P2_PERM KAT");
        CHECK_EQ64(r.cycles, (uint64_t)(TOP_P2_LAT + 3), "P2_PERM cycles = 651 + offer, capture, finish");
    }
    {
        St12 in;
        for (auto& x : in) x = rng.gl();
        for (int i = 0; i < 12; i++) set_x(i, in[i]);
        run_op(0x02);
        D4 d = p2_jive(in);
        for (int i = 0; i < 4; i++) CHECK_EQ64(get_y(i), d[i], "top P2_JIVE");
    }
    check(!run_op(0x10).ok && (axil_read(R_STATUS)&16), "retired opcode fails closed");
    run_op(0x3f);
    for (auto& k : KAT_TOWER) {
        for (int i=0;i<2;++i) { set_x(i,k.a[i]); set_x(i+2,k.b[i]); set_x(i+4,0); set_x(i+6,k.mul[i]); }
        check(run_op(0x30,1).ok && get_y(0)==k.mul[0] && get_y(1)==k.mul[1],"tower GF_MAC");
        set_x(7,k.mul[1]^1);
        check(!run_op(0x30,1).ok,"tower tag tamper");
    }
    // GF(2^128) MAC check.
    for (int t = 0; t < 6; t++) {
        u128 a = ((u128)rng.next() << 64) | rng.next(), b = ((u128)rng.next() << 64) | rng.next();
        u128 k = ((u128)rng.next() << 64) | rng.next();
        if (t == 0) { a = 2; b = (u128)1 << 127; k = 0; }
        u128 m = gf128_mul(a, b) ^ k;
        u128 tag = (t == 5) ? m ^ 1 : m;
        set_x(0, (uint64_t)a); set_x(1, (uint64_t)(a >> 64)); set_x(2, (uint64_t)b); set_x(3, (uint64_t)(b >> 64));
        set_x(4, (uint64_t)k); set_x(5, (uint64_t)(k >> 64)); set_x(6, (uint64_t)tag); set_x(7, (uint64_t)(tag >> 64));
        OpRes r = run_op(0x30);
        CHECK_EQ64(get_y(0), (uint64_t)m, "top GF_MAC lo");
        CHECK_EQ64(get_y(1), (uint64_t)(m >> 64), "top GF_MAC hi");
        check(r.ok == (t != 5), "GF_MAC tag comparison");
    }
    section("top: ID, P2_PERM/P2_JIVE, GF_MAC (accept + reject)", c0, f0);
}

// Keccak sponge driven through the top's KEC_LOAD / KEC_PERMUTE operations.
static uint32_t kec_op_cycles[2];
static std::vector<uint8_t> top_sponge(const std::vector<uint8_t>& msg, uint8_t ds, size_t outlen, bool nr12) {
    const size_t rate = 136;
    std::vector<uint8_t> padded = msg;
    padded.push_back(ds);
    while (padded.size() % rate) padded.push_back(0);
    padded.back() |= 0x80;
    for (int i = 0; i < 25; i++) set_x(i, 0);
    run_op(0x20);
    for (size_t off = 0; off < padded.size(); off += rate) {
        for (int l = 0; l < 17; l++) {
            uint64_t v = 0;
            for (int b = 0; b < 8; b++) v |= (uint64_t)padded[off + 8 * l + b] << (8 * b);
            set_x(l, v);
        }
        kec_op_cycles[nr12] = run_op(0x21, nr12 ? 1 : 0).cycles;
    }
    std::vector<uint8_t> out;
    for (;;) {
        for (int l = 0; l < 12 && out.size() < outlen; l++) {
            uint64_t v = get_y(l);
            for (int b = 0; b < 8 && out.size() < outlen; b++) out.push_back((uint8_t)(v >> (8 * b)));
        }
        if (out.size() >= outlen) break;
        // Only the first 96 rate bytes are mapped to Y; tests keep outlen <= 96 per squeeze block.
        run_op(0x21, (nr12 ? 1 : 0) | 2);
    }
    return out;
}
static void test_top_keccak() {
    long c0 = checks, f0 = fails;
    KPerm mp = [](KState& s, bool n) { keccak_p(s, n); };
    for (size_t i = 0; i < sizeof(KAT_SPONGE) / sizeof(KAT_SPONGE[0]); i += 3) {
        auto msg = from_hex(KAT_SPONGE[i].msg);
        check(to_hex(top_sponge(msg, 0x1F, 64, false)) == KAT_SPONGE[i].shake256_64, "top SHAKE256 KAT");
    }
    check(to_hex(top_sponge({}, 0x1F, 64, true)) ==
          "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
          "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0", "top TurboSHAKE256 rfc9861");
    Rng rng(99);
    std::vector<uint8_t> m(300);
    for (auto& b : m) b = (uint8_t)rng.next();
    check(top_sponge(m, 0x07, 32, true) == keccak_sponge(m, 0x07, 32, true, mp), "top TurboSHAKE256 D=07");
    if (!COMPACT) {
        CHECK_EQ64(kec_op_cycles[0], 24/TOP_KEC_RPC + 3, "KEC_PERMUTE cycles (24 rounds) = 12 + start, capture, finish");
        CHECK_EQ64(kec_op_cycles[1], 12/TOP_KEC_RPC + 3, "KEC_PERMUTE cycles (12 rounds) = 6 + start, capture, finish");
    }
    section("top: SHAKE256 Lean KATs, TurboSHAKE256 (RFC 9861, D=0x07) via KEC ops", c0, f0);
}

static void set_x5(int base, const E5& e) { for (int i = 0; i < 5; i++) set_x(base + i, e[i]); }
static E5 get_y5() { return E5{get_y(0), get_y(1), get_y(2), get_y(3), get_y(4)}; }

static void test_zk_hem_v2() {
    long c0 = checks, f0 = fails;
    Rng rng(0x20260205ULL);
    // 1. EXT5_MAC (0x17): field5.rs KATs, P-1 corners, and 64 random F_{p^5} MACs.
    {
        E5 a = {1, 2, 3, 4, 5}, b = {6, 7, 8, 9, 10}, z = {0, 0, 0, 0, 0};
        set_x5(0, a); set_x5(5, b); set_x5(10, z);
        check(run_op(0x17).ok, "EXT5_MAC KAT ok");
        E5 got = get_y5(), want = e5_mul_add(a, b, z);
        for (int i = 0; i < 5; i++) CHECK_EQ64(got[i], want[i], "top EXT5_MAC KAT [348,337,295,220,110]");
    }
    for (int t = 0; t < 68; t++) {
        E5 a = rng.e5(), b = rng.e5(), c = rng.e5();
        if (t < 4) {
            for (int i = 0; i < 5; i++) {
                a[i] = (t & 1) ? GLP - 1 : rng.gl();
                b[i] = (t & 2) ? GLP - 1 : rng.gl();
                c[i] = GLP - 1;
            }
        }
        set_x5(0, a); set_x5(5, b); set_x5(10, c);
        auto mac = run_op(0x17);
        check(mac.ok, "EXT5_MAC random ok");
        if (!COMPACT) CHECK_EQ64(mac.cycles, EXT5_MAC_LAT+2, "native MAC latency");
        E5 got = get_y5(), want = e5_mul_add(a, b, c);
        for (int i = 0; i < 5; i++) CHECK_EQ64(got[i], want[i], "top EXT5_MAC random/corner");
    }
    // A sumcheck or fold may have used the working banks since the last write.
    E5 a=rng.e5(), b=rng.e5(), c=rng.e5();
    set_x5(0,a); set_x5(5,b); set_x5(10,c);
    auto direct=run_op(0x17);
    printf("  native register MAC OP_CYCLES %u\n",direct.cycles);
    check(direct.ok && get_y5()==e5_mul_add(a,b,c),"register MAC after full operand load");
    run_op(0x18,4);
    c[4]=42; set_x(14,42);
    check(run_op(0x17).ok && get_y5()==e5_mul_add(a,b,c),"register MAC after partial reload");
    set_x(14,GLP);
    check(!run_op(0x17).ok && (axil_read(R_STATUS)&8),"register operand canonicality");
    run_op(0x3f);
    // 2. EXT5_FROB (0x18): KAT, ring homomorphism phi(a*b) == phi(a)*phi(b), and phi^5(a) == a.
    {
        E5 a = {1, 2, 3, 4, 5};
        set_x5(0, a);
        check(run_op(0x18, 1).ok, "EXT5_FROB k=1 ok");
        E5 got = get_y5(), want = e5_frobenius(a, 1);
        for (int i = 0; i < 5; i++) CHECK_EQ64(got[i], want[i], "top EXT5_FROB KAT");

        E5 x = rng.e5(), y = rng.e5(), xy = e5_mul(x, y);
        for (uint8_t k = 0; k <= 6; k++) {
            set_x5(0, x); run_op(0x18, k); E5 fx = get_y5();
            set_x5(0, y); run_op(0x18, k); E5 fy = get_y5();
            set_x5(0, xy); run_op(0x18, k); E5 fxy = get_y5();
            E5 prod_f = e5_mul(fx, fy);
            for (int i = 0; i < 5; i++) {
                CHECK_EQ64(fx[i], e5_frobenius(x, k)[i], "top EXT5_FROB phi^k(x)");
                CHECK_EQ64(fxy[i], prod_f[i], "top EXT5_FROB homomorphism phi^k(x*y) == phi^k(x)*phi^k(y)");
            }
            if (k == 5) {
                for (int i = 0; i < 5; i++) CHECK_EQ64(fx[i], x[i], "top EXT5_FROB order 5");
            }
        }
    }
    // 3. 400-bit (50-byte) Role-1 TurboSHAKE256 (D = 0x07) squeeze via 0x22 KEC_STREAM_SPONGE (Y[0..7] + full 400b STATUS.ok).
    {
        KState st{};
        uint64_t lanes[17] = {};
        for (int i = 0; i < 8; i++) { lanes[i] = rng.next(); st[i] = lanes[i]; }
        lanes[8] = 0x07ULL;            st[8]  = 0x07ULL;
        lanes[16] = 1ULL << 63;        st[16] = 1ULL << 63;
        keccak_p(st, true);
        uint64_t flags400 = 1ULL | 8ULL | 16ULL | 64ULL | ((st[6] & 0xFFFFULL) << 48); // init=1, nr12=1, chk256=1, chk400=1
        // (a) Honest 400-bit digest check passes STATUS.ok
        axil_write(R_CMD, 0x22u | (1u << 16));
        stream_beat(lanes, 8);
        stream_beat(lanes + 8, 8);
        uint64_t b2[8] = {lanes[16], flags400, st[0], st[1], st[2], st[3], st[4], st[5]};
        stream_beat(b2, 8);
        OpRes r = wait_op(0x22);
        check(r.ok, "zk-Hem v2 full 400-bit Role-1 KEC_STREAM_SPONGE ok");
        for (int i = 0; i < 8; i++) CHECK_EQ64(get_y(i), st[i], "zk-Hem v2 512b/400b KEC_STREAM_SPONGE Y[0..7]");
        // (b) 1-bit tamper in byte 49 (bit 392 = st[6][8]) MUST fail STATUS.ok!
        axil_write(R_CMD, 0x22u | (1u << 16));
        stream_beat(lanes, 8);
        stream_beat(lanes + 8, 8);
        uint64_t b2_bad49[8] = {lanes[16], flags400 ^ (0x0100ULL << 48), st[0], st[1], st[2], st[3], st[4], st[5]};
        stream_beat(b2_bad49, 8);
        OpRes r_bad49 = wait_op(0x22);
        check(!r_bad49.ok, "zk-Hem v2 400-bit KEC_STREAM_SPONGE rejects byte-49 tamper via STATUS.ok");
        // (c) 1-bit tamper in byte 35 (st[4]) MUST fail STATUS.ok!
        axil_write(R_CMD, 0x22u | (1u << 16));
        stream_beat(lanes, 8);
        stream_beat(lanes + 8, 8);
        uint64_t b2_bad35[8] = {lanes[16], flags400, st[0], st[1], st[2], st[3], st[4] ^ (1ULL << 24), st[5]};
        stream_beat(b2_bad35, 8);
        OpRes r_bad35 = wait_op(0x22);
        check(!r_bad35.ok, "zk-Hem v2 400-bit KEC_STREAM_SPONGE rejects byte-35 tamper via STATUS.ok");
    }
    section("top: zk-Hem v2 F_{p^5} EXT5_MAC, EXT5_FROB homomorphism, 400-bit Role-1 KEC_STREAM_SPONGE", c0, f0);
}

// Fold a 2^n table by r.size() challenges with FOLD_MULTI (up to 6 rounds per command);
// Return the sum of the hardware fold-command cycle counters.
static uint64_t fold_table(const std::vector<E5>& table, const std::vector<E5>& r, E5& result) {
    int n = 0;
    while (((size_t)1 << n) < table.size()) n++;
    axil_write(R_STREAM, 0x80000000u);
    for (auto& e : table) stream_beat(e.data(), 5);
    uint64_t cycles = 0;
    for (size_t done = 0; done < r.size(); done += 6) {
        int m = (int)(r.size() - done < 6 ? r.size() - done : 6);
        for (int j = 0; j < m; j++) set_x5(5 * j, r[done + j]);
        if (done==0) check(run_op(0x14,n).ok,"set fold length");
        auto op = m==1 ? run_op(0x13) : run_op(0x15,m);
        check(op.ok,"fold command");
        cycles += op.cycles;
    }
    result = get_y5();
    return cycles;
}
static E5 fold_model_fp5(std::vector<E5> t, const std::vector<E5>& r) {
    for (auto& rj : r) {
        size_t half = t.size() / 2;
        for (size_t k = 0; k < half; k++) t[k] = e5_mul_add(rj, e5_sub(t[2 * k + 1], t[2 * k]), t[2 * k]);
        t.resize(half);
    }
    return t[0];
}

static void test_fold_and_chains() {
    long c0 = checks, f0 = fails;
    Rng rng(0xF01D);
    for (int n : {1, 2, 5, 9, 16}) {
        if (COMPACT && n == 16) continue;
        std::vector<E5> t((size_t)1 << n), r(n);
        for (auto& e : t) e = rng.e5();
        for (auto& e : r) e = rng.e5();
        E5 got, want = fold_model_fp5(t, r);
        uint64_t cy = fold_table(t, r, got);
        for (int i = 0; i < 5; i++) CHECK_EQ64(got[i], want[i], "fold result");
        check(cy>0,"fold counter");
    }
    section("top: BRAM fold engine, 1/2/5/9-variable tables vs fold_first_var model", c0, f0);

    c0 = checks; f0 = fails;
    Tree t(7, rng);
    D4 cap = {rng.gl(), rng.gl(), rng.gl(), rng.gl()};
    // 32 chains at once: leaf sponge (20 limbs = 3 blocks) then 7 levels; slot 13 gets a bad sibling.
    std::vector<uint32_t> leaf(32);
    Rng rng2(0x5EED);
    std::vector<std::vector<uint64_t>> data(32);
    for (int s = 0; s < 32; s++) {
        leaf[s] = (uint32_t)((s * 37 + 5) % 128);   // distinct leaves
        data[s].resize(20);
        for (auto& x : data[s]) x = rng2.gl();
        t.node[128 + leaf[s]] = p2_sponge_with_cap(LEAF_DOMAIN, cap, data[s]);
    }
    t.build();
    chain_cfg(t, cap);
    uint32_t perms0 = axil_read(R_PERMS);
    uint64_t t0 = cyc;
    int perms = 0;
    for (int s = 0; s < 32; s++) perms += load_chain(s, t, leaf[s], data[s], s == 13);
    OpRes r = run_op(0x05);
    uint64_t wall = cyc - t0;
    uint32_t done = axil_read(R_CH_DONE), okm = axil_read(R_CH_OK), busy = axil_read(R_CH_BUSY);
    check(done == 0xFFFFFFFFu && busy == 0, "all chains finished");
    check(okm == (0xFFFFFFFFu & ~(1u << 13)), "31 chains match the top node, the corrupted one does not");
    check(!r.ok, "CHAIN_WAIT reports the bad chain");
    check(axil_read(R_PERMS) - perms0 == (uint32_t)perms, "permutation count");
    run_op(0x06, 5);
    for (int i = 0; i < 4; i++) CHECK_EQ64(get_y(i), t.node[1][i], "CHAIN_READ digest = top node");
    printf("  32 chains x (3 sponge + 7 node) = %d permutations in %llu clocks wall (%.1f clocks/perm; a lone permutation takes %d)\n",
           perms, (unsigned long long)wall, (double)wall / perms, P2_PASSES * P2_RING_LEN);
    section("top: chain engine, 32 concurrent leaf-sponge + Canopy paths (depth 7), one corrupted", c0, f0);
}

struct TcOp {
    bool turbo;
    uint8_t log_leaves;
    D4 root;
    std::vector<std::pair<uint32_t, D4>> leaves;
    std::vector<D4> sibs;
};
static KState sponge_mid_host(uint8_t mid) {
    static const uint64_t M[7][25] = {
        {0},
        {0x3977c693fff5d3b5ULL,0x246ec0d2e44a2873ULL,0x365c52c274ca962dULL,0xe4c0940fe6fd66d4ULL,0xb1e4c392785511c9ULL,
         0x059cb6e43d871f0aULL,0x90cf0bb4b0f87926ULL,0x748c2b6d5ec3eb4aULL,0x21704f4eff4689b1ULL,0xada5e0392d80ff18ULL,
         0x9f46820a99b7911cULL,0x82179d62d43b4832ULL,0x62985ba50bb8c831ULL,0x373719272b20bc28ULL,0x68d0d91f23c98a74ULL,
         0xa00b662de840548fULL,0x8c8f04fc14e393a9ULL,0x47b4b6b3b7ce847fULL,0xce667e802a4096baULL,0xc7f30bf9849ae9c6ULL,
         0x47b55bcbfe7c2542ULL,0x590c6116b1c143a0ULL,0xfd8df4474c3cc6e6ULL,0x9dab998b64eacbb6ULL,0xd1fe4043d17675a6ULL},
        {0x460887f1cba4a839ULL,0x980803a3bfc02e65ULL,0x68bddb54ef8d20a8ULL,0x0b3372687f85bcafULL,0xcc2727c2077077dfULL,
         0xec41d86c9b5f8d09ULL,0xfb5f5d561424cae1ULL,0x3268a335444cad6dULL,0x1946744824d4f99bULL,0xf0cc17364abb8f7bULL,
         0x6555bd65801754f9ULL,0xfb65ea5772915117ULL,0x7abf03d078f82efaULL,0xe40b7e6f749e0f48ULL,0xa878894cf5a786fbULL,
         0xaf50e05198f19f90ULL,0xe428425cb9274f77ULL,0x7cc9afdb9d39179eULL,0x68eb6cd4b52d2c93ULL,0x777f4fb40734c256ULL,
         0xb61fe57e44cde167ULL,0x1f19e1e1f1a15293ULL,0x6ee7751ca38082bcULL,0x1790fc47c8fcf771ULL,0xd6bf84556451e94dULL},
        {0x05c2a834d12f320bULL,0x6e01f76fb298e055ULL,0xc375c2049cde73b1ULL,0x14679f4eadebc00bULL,0x42c245e14e1d0612ULL,
         0xaad978e09c60a94dULL,0x97421bfa48a78a3dULL,0x77731a35cbaaaec0ULL,0xd80e903986a24502ULL,0x56e5c86b0ad655c9ULL,
         0xd0c677d357b05118ULL,0xca8b39da2a172feaULL,0xf6722b33b1d71db7ULL,0xcd992e2dafb9cc70ULL,0xa71ff26148978892ULL,
         0x0ba73ad03b4e7b42ULL,0xf6edd8b825b1f4adULL,0x5696402b81c97ac2ULL,0x8f8cc5418a932adbULL,0xd329e076f57dd146ULL,
         0xd485ee5d60978147ULL,0x11831024d5468d79ULL,0x881ae14ada384d82ULL,0x0c8208237c8abcf0ULL,0x21390810db15896aULL},
        {0xec954fc7c2fc5381ULL,0x36020892bcb1e761ULL,0x748dc5bcea037dd5ULL,0xfc481597cf683315ULL,0x2ec2f3f44f0d3969ULL,
         0x9c0dfc53513c2627ULL,0x5415c0edffcd33b8ULL,0x403107f0fc877484ULL,0x798d84e67c6dafa6ULL,0x6e6ea3127d335e8eULL,
         0x5606ea8555392f99ULL,0xd3bac257bbe1d044ULL,0x1e5c61027d60223cULL,0x48c4972c4005a2deULL,0xe62560e08ebdd299ULL,
         0xa3c6ce028dff6b56ULL,0x14e16d5699388c63ULL,0x8d68335c54a43ae4ULL,0x74a909e5002c19f7ULL,0x48a12fac4eec8f3dULL,
         0x797c9923ea11dfb5ULL,0x2121d5b260157781ULL,0x704aa293b550c49aULL,0xddcb710a40908d75ULL,0x856c96f5dc9851aaULL},
        {0x91d7c2b5d9c349d5ULL,0x0fe9e1320d052990ULL,0xbb49dcb163df0998ULL,0x41863aed68216b69ULL,0x9b36e33d0b572914ULL,
         0x47fd0269a80e1a2fULL,0x0fd8d3b0bb052910ULL,0x777b25e68d3b55e4ULL,0xda8aea200595a598ULL,0x234b7b795b42b2f1ULL,
         0x8931ca9d1d33d881ULL,0x265565cd4ead330aULL,0xeb457d90d1f36480ULL,0xea2ba3d9236057abULL,0x03572a55d68c5e72ULL,
         0x997c789c6f5417f5ULL,0xd8fa575d2aa329b2ULL,0xa11c1a07edc22223ULL,0xee86f4bac42c763fULL,0xf9d93986d50c63f5ULL,
         0x1d88a5c7c867f955ULL,0x394442877b64831dULL,0xcba53b397e6c7084ULL,0x8ad61a49d597e2adULL,0x4918107a763c890aULL},
        {0x912cd4369f324315ULL,0x999c04d88741d72fULL,0x826e87f172a72886ULL,0x9ab34da963aec230ULL,0xe59866a9c4dee082ULL,
         0x2e0d70596264312eULL,0x1f62aa1e3894cb9eULL,0x221e18927402f5ddULL,0x52411767f8e30a27ULL,0x38ed890d9450b4bdULL,
         0xa7adc24cbbe0d095ULL,0xeb93ea9d288eb573ULL,0xa8e1b8213cc6bf0aULL,0x4f30b691a18fb10dULL,0x07d90cb270b3a2ceULL,
         0xbc3100ec6f44ddeaULL,0x36d8b62669667d1aULL,0x0cd9a4529023823cULL,0x7d70c6da8ff3dd83ULL,0x10aad610c87ac7b3ULL,
         0x288423a030b1eda5ULL,0xdc8757b91cac4cc1ULL,0x6fdc27bd98b433d0ULL,0x33985abee9b9cc90ULL,0x5f9bd4e625811719ULL}
    };
    KState s{};
    if (mid < 7) for (int i = 0; i < 25; i++) s[i] = M[mid][i];
    return s;
}

static OpRes exec_tc_op(const TcOp& tc) {
    axil_write(R_STREAM, 0x10000000u);
    for (const auto& lv : tc.leaves) {
        uint64_t b[8] = {lv.second[0], lv.second[1], lv.second[2], lv.second[3], (uint64_t)lv.first, 0, 0, 0};
        stream_beat(b, 5);
    }
    if (!tc.sibs.empty()) {
        axil_write(R_STREAM, 0x20000000u);
        for (const auto& s : tc.sibs) stream_beat(s.data(), 4);
    }
    axil_write(R_ARG32, (uint32_t)tc.sibs.size());
    set_x4(0, tc.root);
    return run_op(0x24, (uint8_t)((tc.turbo ? 1 : 0) | (tc.log_leaves << 1)), (uint16_t)tc.leaves.size());
}

static D4 canopy_hash(bool turbo, bool root, unsigned index, D4 left, D4 right = {}) {
    std::vector<uint8_t> msg{uint8_t(root)};
    for (int i=0; i<(root ? 1 : 4); ++i) msg.push_back(uint8_t(index >> (8*i)));
    auto append = [&](const D4& digest) {
        for (auto word : digest) for (int i=0; i<8; ++i) msg.push_back(uint8_t(word >> (8*i)));
    };
    append(left);
    if (!root) append(right);
    KState st = sponge_mid_host(turbo ? 2 : 4);
    msg.push_back(turbo ? 7 : 4);
    msg.resize(136);
    msg.back() |= 128;
    for (size_t i=0;i<msg.size();++i) st[i/8] ^= uint64_t(msg[i]) << (8*(i%8));
    keccak_p(st,turbo);
    return {st[0],st[1],st[2],st[3]};
}

static void test_canopy() {
    Rng rng(724);
    D4 a{},b{},sibling{};
    for (auto p : {&a,&b,&sibling}) for (auto& w : *p) w=rng.next();
    for (bool turbo : {false,true}) {
        D4 node=canopy_hash(turbo,false,2,a,b);
        D4 root=canopy_hash(turbo,true,2,canopy_hash(turbo,false,1,node,sibling));
        TcOp tc{turbo,2,root,{{4,a},{5,b}},{sibling}};
        check(exec_tc_op(tc).ok && get_y4()==root,"Steiner frontier root");
        tc.leaves[1].second[3]^=1;
        check(!exec_tc_op(tc).ok,"Steiner leaf tamper");
        tc.leaves[1].second[3]^=1;
        tc.sibs[0][0]^=1;
        check(!exec_tc_op(tc).ok,"Steiner sibling tamper");
    }
}

static void test_sumcheck_batch() {
    Rng rng(0x1235);
    for (int mode : {0,1,2,3,4,9,255}) {
        int degree=mode ? mode : 3;
        std::vector<E5> c(degree+1);
        for (auto& v:c) v=rng.e5();
        E5 r=rng.e5(), claim=c[0], want=c.back();
        for (const auto& v:c) claim=e5_add(claim,v);
        for (int j=degree-1;j>=0;--j) want=e5_mul_add(want,r,c[j]);
        for (int fault=0;fault<(mode ? 3 : 2);++fault) {
            E5 init=claim;
            if (!mode && fault) init[4]^=1;
            set_x5(0,init);
            check(run_op(0x11).ok,"sumcheck init");
            auto input=c;
            if (mode && fault==1) input[degree][4]^=1;
            if (mode && fault==2) input[0][4]=GLP;
            OpRes round;
            if (!mode) {
                for (int j=0;j<=degree;++j) set_x5(5*j,input[j]);
                set_x5(20,r);
                round=run_op(0x12);
            } else {
                axil_write(R_CMD,0x12u | (mode<<8));
                stream_beat(r.data(),5);
                for (int j=degree;j>=0;--j) stream_beat(input[j].data(),5);
                round=wait_op(0x12);
            }
            check(round.ok==(fault==0),"sumcheck acceptance");
            if (!fault) check(get_y5()==want,"Horner result");
            if (fault==2) {
                check(axil_read(R_STATUS)&8,"sumcheck fifth-limb range error");
                run_op(0x3f);
            }
        }
    }
    for (int lane=0; lane<5; ++lane) {
        E5 bad{};
        bad[lane]=GLP;
        set_x5(0,bad);
        check(!run_op(0x11).ok && (axil_read(R_STATUS)&8),"noncanonical initial claim");
        run_op(0x3f);
        axil_write(R_STREAM,0x80000000u);
        stream_beat(bad.data(),5);
        check(axil_read(R_STATUS)&8,"noncanonical passive table element");
        run_op(0x3f);
    }
    check(!run_op(0x15,7,9).ok && (axil_read(R_STATUS)&16),"seven challenges exceed X window");
    run_op(0x3f);
    check(!run_op(0x16,0,0).ok && (axil_read(R_STATUS)&16),"empty batch");
    run_op(0x3f);
    for (int fault=0;fault<4;++fault) {
        int count=fault ? 3 : 320;
        axil_write(R_CMD,0x16u | (count<<16));
        E5 tail{};
        for (int j=0;j<count;++j) {
            E5 a=rng.e5(),b=rng.e5(),c=rng.e5();
            tail=e5_mul_add(a,b,c);
            auto expected=tail;
            if (j==1 && fault==1) a[4]^=1;
            if (j==1 && fault==2) expected[4]^=1;
            if (j==1 && fault==3) c[4]=GLP;
            for (auto p:{&a,&b,&c,&expected}) {
                uint64_t beat[8]={(*p)[0],(*p)[1],(*p)[2],(*p)[3],(*p)[4],GLP,GLP,GLP};
                stream_beat(beat,8);
            }
        }
        check(wait_op(0x16).ok==(fault==0),"batch acceptance");
        check(get_y5()==tail,"last batch result");
        if (fault==3) {
            check(axil_read(R_STATUS)&8,"batch fifth-limb range error");
            run_op(0x3f);
        }
    }
}
// Deterministic connected workload for installations without a serialized proof.
// Commit gate evaluations, use the 400-bit squeeze for fold and sumcheck challenges,
// and authenticate the resulting opening through both Canopy implementations.
static void replay_fp5_workload(FILE* report) {
    long initial_checks=checks, initial_fails=fails;
    Rng rng(0x5148414d32);
    run_op(0x3f);
    std::fill_n(opcode_cycles,256,0);
    uint64_t begin=total_cycles();
    std::vector<E5> gates(16);
    axil_write(R_CMD,0x16u | (16u<<16));
    for (auto& gate:gates) {
        E5 a=rng.e5(), b=rng.e5(), c=rng.e5();
        gate=e5_mul_add(a,b,c);
        for (const auto* word:{&a,&b,&c,&gate}) stream_beat(word->data(),5);
    }
    check(wait_op(0x16).ok && get_y5()==gates.back(),"replay gate evaluations");

    // The transcript contains the eight-byte workload tag and every gate limb.
    std::vector<uint8_t> msg{'Q','S','A','G','H','Q','M','2'};
    for (const auto& gate:gates) for (uint64_t w:gate)
        for (unsigned b=0;b<8;++b) msg.push_back(uint8_t(w>>(8*b)));
    msg.push_back(7);
    msg.resize(((msg.size()+135)/136)*136);
    msg.back()|=128;
    KState host{};
    axil_write(R_CMD,0x22u | (uint32_t(msg.size()/136)<<16));
    for (size_t pos=0;pos<msg.size();pos+=136) {
        uint64_t block[17]{};
        for (int i=0;i<136;++i) block[i/8]|=uint64_t(msg[pos+i])<<(8*(i%8));
        for (int i=0;i<17;++i) host[i]^=block[i];
        keccak_p(host,true);
        bool final=pos+136==msg.size();
        uint64_t flags=(pos==0) | 8u;
        if (final) flags|=64u | ((host[6]&65535u)<<48);
        uint64_t last[8]={block[16],flags,host[0],host[1],host[2],host[3],host[4],host[5]};
        stream_beat(block,8); stream_beat(block+8,8); stream_beat(last,8);
    }
    check(wait_op(0x22).ok,"replay transcript");
    E5 challenge{};
    for (int i=0;i<5;++i) challenge[i]=gl_red(get_y(i));
    std::vector<E5> point;
    for (int i=0;i<4;++i) point.push_back(e5_frobenius(challenge,i));
    E5 want=fold_model_fp5(gates,point), claim{};
    fold_table(gates,point,claim);
    check(claim==want,"replay coset fold");
    set_x5(0,claim);
    check(run_op(0x11).ok,"replay initial claim");
    for (int degree:{2,3,4,9}) {
        std::vector<E5> c(degree+1);
        E5 sum{};
        for (int k=1;k<=degree;++k) { c[k]=rng.e5(); sum=e5_add(sum,c[k]); }
        for (int i=0;i<5;++i) c[0][i]=gl_mul(gl_sub(want[i],sum[i]),(GLP+1)/2);
        const E5 r=e5_frobenius(challenge,degree);
        axil_write(R_CMD,0x12u | (degree<<8));
        stream_beat(r.data(),5);
        for (int k=degree;k>=0;--k) stream_beat(c[k].data(),5);
        want=c.back();
        for (int k=degree-1;k>=0;--k) want=e5_mul_add(want,r,c[k]);
        check(wait_op(0x12).ok && get_y5()==want,"replay chained sumcheck");
    }
    E5 opening=get_y5();
    D4 cap{},leaf{},sib{},uncle{};
    for (int i=0;i<4;++i) {leaf[i]=want[i]; sib[i]=gates[0][i]; uncle[i]=gates[1][i];}
    D4 node=canopy_hash(true,false,2,leaf,sib);
    D4 root=canopy_hash(true,true,2,canopy_hash(true,false,1,node,uncle));
    TcOp proof{true,2,root,{{4,leaf},{5,sib}},{uncle}};
    for (int i=0;i<4;++i) proof.leaves[0].second[i]=opening[i];
    check(exec_tc_op(proof).ok && get_y4()==root,"replay Steiner root");
    Tree tree(3,rng);
    std::vector<uint64_t> words(want.begin(),want.end());
    for (auto h:root) words.push_back(gl_red(h));
    tree.node[8]=p2_sponge_with_cap(LEAF_DOMAIN,cap,words);
    tree.build(); chain_cfg(tree,cap);
    load_chain(0,tree,0,words);
    check(run_op(0x05).ok,"replay Poseidon2 opening");
    run_op(0x06,0);
    check(get_y4()==tree.node[1],"replay final root");
    section("connected QSAGHQM2-shaped Fp5 verifier workload",initial_checks,initial_fails);
    if (report) {
        fprintf(report,"%s generated workload TOTAL_CYCLES %llu\n",PROFILE_NAME,(unsigned long long)(total_cycles()-begin));
        for (int i=0;i<256;++i) if (opcode_cycles[i])
            fprintf(report,"0x%02x OP_CYCLES %llu\n",i,(unsigned long long)opcode_cycles[i]);
    }
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    dut.reset(new Dut);
    model_selfcheck();
    // --x-initial unique randomises the inputs too: drive every control input before reset.
    dut->s_axil_awvalid = 0; dut->s_axil_wvalid = 0; dut->s_axil_arvalid = 0;
    dut->s_axil_bready = 0; dut->s_axil_rready = 0; dut->s_axis_tvalid = 0;
    dut->rst = 1;
    for (int i = 0; i < 4; i++) tick();
    dut->rst = 0;
    tick();
    // First argument that is not a Verilator plusarg names the trace report.
    const char* rep_path = "trace_report.txt";
    for (int i = 1; i < argc; i++) if (argv[i][0] != '+') { rep_path = argv[i]; break; }
    FILE* rep = fopen(rep_path, "w");
    test_axi_channels();
    test_basic_ops();
    test_top_keccak();
    test_fold_and_chains();
    test_sumcheck_batch();
    test_canopy();
    test_zk_hem_v2();
    check((axil_read(R_STATUS) & 0x18) == 0, "no sticky error flags");
    replay_fp5_workload(rep);
    if (rep) fclose(rep);
    printf("TOP: %ld checks, %ld mismatches, %llu clocks simulated\n", checks, fails, (unsigned long long)cyc);
    dut->final();
    dut.reset();
    return fails ? 1 : 0;
}
#endif
