// Cycle-accurate Verilator testbench for the QSAG-NI FPGA core.
//   -DQSAG_UNITS : drives tb/qsag_units_tb.sv (every arithmetic unit, pipeline by pipeline)
//   -DQSAG_TOP   : drives rtl/qsag_ni_fpga_top.sv through its AXI4-Lite / AXI4-Stream ports
// Expected values come from tb/qsag_model.h, which is first checked against the Lean oracle
// vectors of validation/tests/fixtures/lean_external_oracle_vectors.json (build/kat_vectors.h).
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <map>
#include <memory>
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

static const int GL_MUL_LAT = 5, RED_LAT = 2, P2_SBOX_LAT = 13, EXT4_MAC_LAT = 7, GF128_LAT = 3;
static const int P2_RING_LEN = 16, P2_PASSES = 31, P2_PIPE_LAT = 453;
#if defined(QSAG_COMPACT)
static constexpr bool COMPACT = true;
static const int TOP_P2_LAT = 1314, TOP_EXT_LAT = 24, TOP_KEC_RPC = 1;
#elif defined(QSAG_PIPE)
static constexpr bool COMPACT = false;
static const int TOP_P2_LAT = P2_PIPE_LAT - 1, TOP_EXT_LAT = EXT4_MAC_LAT, TOP_KEC_RPC = 2;
#else
static constexpr bool COMPACT = false;
static const int TOP_P2_LAT = P2_PASSES*P2_RING_LEN, TOP_EXT_LAT = EXT4_MAC_LAT, TOP_KEC_RPC = 2;
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
    for (auto& k : KAT_EXT4) {
        E4 x = {k.x[0], k.x[1], k.x[2], k.x[3]}, y = {k.y[0], k.y[1], k.y[2], k.y[3]};
        E4 m = e4_mul(x, y);
        for (int i = 0; i < 4; i++) CHECK_EQ64(m[i], k.mul[i], "model ext4 mul");
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
    section("reference model vs Lean oracle vectors / RFC 9861", c0, f0);
}

// =====================================================================================
#if defined(QSAG_UNITS)

template <typename T> struct Pipe {
    std::deque<std::pair<uint64_t, T>> q;
    void push(int lat, const T& v) { q.push_back({cyc + lat, v}); }
    bool due(T& v) { if (!q.empty() && q.front().first == cyc) { v = q.front().second; q.pop_front(); return true; } return false; }
};

static void test_mul_red_sbox_ext4_gf() {
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
    Pipe<E4> pe;
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
        // Ext4 MAC
        E4 ea = rng.e4(), eb = rng.e4(), ec = rng.e4();
        if (i < 3) {
            for (int j = 0; j < 4; j++) { ea[j] = KAT_EXT4[i].x[j]; eb[j] = KAT_EXT4[i].y[j]; ec[j] = 0; }
        } else if (i < 40) {
            for (int j = 0; j < 4; j++) { ea[j] = (rng.next() & 1) ? GLP - 1 : rng.gl(); eb[j] = (rng.next() & 1) ? GLP - 1 : rng.gl(); ec[j] = GLP - 1; }
        }
        for (int j = 0; j < 4; j++) { set64(dut->e_a, j, ea[j]); set64(dut->e_b, j, eb[j]); set64(dut->e_c, j, ec[j]); }
        if (live) pe.push(EXT4_MAC_LAT, e4_mul_add(ea, eb, ec));
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

        uint64_t w; std::pair<uint8_t, u128> rw; E4 ew; u128 gw;
        if (pm.due(w)) { CHECK_EQ64(dut->mul_r, w, "gl64 mul 26x17"); CHECK_EQ64(dut->mul_r16, w, "gl64 mul 16x16"); }
        if (pr.due(rw)) CHECK_EQ64(dut->red_r, gl_red136(rw.first, rw.second), "gl64 reduce136");
        if (ps.due(w)) CHECK_EQ64(dut->sb_y, w, "sbox x^7");
        if (pe.due(ew)) for (int j = 0; j < 4; j++) CHECK_EQ64(get64(dut->e_y, j), ew[j], "ext4 mac");
        if (pg.due(gw)) { CHECK_EQ64(get64(dut->gf_r, 0), (uint64_t)gw, "gf128 lo"); CHECK_EQ64(get64(dut->gf_r, 1), (uint64_t)(gw >> 64), "gf128 hi"); }
        if (pt.due(gw)) { CHECK_EQ64(get64(dut->tower_r,0),(uint64_t)gw,"tower KAT lo"); CHECK_EQ64(get64(dut->tower_r,1),(uint64_t)(gw>>64),"tower KAT hi"); }
    }
    check(pm.q.empty() && pr.q.empty() && ps.q.empty() && pe.q.empty() && pg.q.empty(), "pipelines drained");
    section("gl64 mul (both tilings) / reduce136 / x^7 / Ext4 MAC / GF(2^128): Lean KATs, edges, 200k random", c0, f0);
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

static void test_keccak() {
    long c0 = checks, f0 = fails;
    KPerm hw = rtl_keccak;
    for (auto& k : KAT_SPONGE) {
        auto msg = from_hex(k.msg);
        check(to_hex(keccak_sponge(msg, 0x06, 32, false, hw)) == k.sha3_256, "rtl sha3-256 KAT");
        check(to_hex(keccak_sponge(msg, 0x1F, 64, false, hw)) == k.shake256_64, "rtl shake256 KAT");
        check(to_hex(cshake256(msg, KAT_CSHAKE_CUSTOM, 64, hw)) == k.cshake256_64, "rtl cshake256 KAT");
    }
    check(to_hex(keccak_sponge({}, 0x1F, 64, true, hw)) ==
          "367a329dafea871c7802ec67f905ae13c57695dc2c6663c61035f59a18f8e7db"
          "11edc0e12e91ea60eb6b32df06dd7f002fbafabb6e13ec1cc20d995547600db0", "rtl turboshake256 rfc9861");
    // qsag's Role-1 domain byte 0x07, long input, against the model.
    Rng rng(7);
    std::vector<uint8_t> m(1000);
    for (auto& b : m) b = (uint8_t)rng.next();
    KPerm mp = [](KState& s, bool n) { keccak_p(s, n); };
    check(keccak_sponge(m, 0x07, 200, true, hw) == keccak_sponge(m, 0x07, 200, true, mp), "rtl turboshake256 D=07");
    check(kec_cycles[0][0] == 24 && kec_cycles[0][1] == 12 && kec_cycles[1][0] == 12 && kec_cycles[1][1] == 6, "keccak cycle counts");
    printf("  keccak clocks per permutation: 1 round/clk %llu (f1600) / %llu (p1600,12); 2 rounds/clk %llu / %llu\n",
           (unsigned long long)kec_cycles[0][0], (unsigned long long)kec_cycles[0][1],
           (unsigned long long)kec_cycles[1][0], (unsigned long long)kec_cycles[1][1]);
    section("Keccak core: Lean SHA3-256/SHAKE256/cSHAKE256 KATs (14 lengths), RFC 9861 TurboSHAKE256, D=0x07", c0, f0);
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    dut.reset(new Dut);
    model_selfcheck();
    // --x-initial unique randomises the inputs too: drive every control input before reset.
    dut->ring_in_valid = 0; dut->pipe_in_valid = 0; dut->kec_start = 0; dut->kec_nr12 = 0;
    dut->ring_in_jive = 0; dut->pipe_in_jive = 0; dut->ring_in_tag = 0; dut->pipe_in_tag = 0;
    dut->rst = 1;
    for (int i = 0; i < 4; i++) tick();
    dut->rst = 0;
    test_mul_red_sbox_ext4_gf();
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

static void axil_write(uint32_t addr, uint32_t data) {
    dut->s_axil_awaddr = addr; dut->s_axil_awvalid = 1;
    dut->s_axil_wdata = data; dut->s_axil_wstrb = 0xF; dut->s_axil_wvalid = 1;
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
static void set_x4(int base, const E4& e) { for (int i = 0; i < 4; i++) set_x(base + i, e[i]); }
static E4 get_y4() { return E4{get_y(0), get_y(1), get_y(2), get_y(3)}; }

struct OpRes { bool ok; uint32_t cycles; };
// Start an operation, poll until done, return its ok flag and the core's own cycle count.
static OpRes run_op(uint8_t op, uint8_t a0 = 0, uint16_t a1 = 0) {
    axil_write(R_CMD, (uint32_t)op | ((uint32_t)a0 << 8) | ((uint32_t)a1 << 16));
    uint32_t st;
    for (long guard = 0;; guard++) {
        st = axil_read(R_STATUS);
        if (st & 2) break;
        if (guard > 50000000) { printf("timeout in op %02x\n", op); exit(2); }
    }
    return OpRes{(st & 4) != 0, axil_read(R_OPCYC)};
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
    // Ext4 MAC KATs.
    for (auto& k : KAT_EXT4) {
        for (int i = 0; i < 4; i++) { set_x(i, k.x[i]); set_x(4 + i, k.y[i]); set_x(8 + i, 0); }
        OpRes r = run_op(0x10);
        for (int i = 0; i < 4; i++) CHECK_EQ64(get_y(i), k.mul[i], "top EXT4_MAC KAT");
        if (!COMPACT) CHECK_EQ64(r.cycles, (uint64_t)(TOP_EXT_LAT + 2), "EXT4_MAC cycles");
    }
    // Sumcheck rounds: three honest rounds, then a wrong claim.
    {
        E4 claim = rng.e4();
        set_x4(0, claim);
        run_op(0x11);
        for (int round = 0; round < 4; round++) {
            E4 c[4] = {rng.e4(), rng.e4(), rng.e4(), rng.e4()};
            // choose c0 so that g(0) + g(1) = 2*c0 + c1 + c2 + c3 = claim (2^-1 = (p+1)/2)
            E4 rest = e4_add(e4_add(c[1], c[2]), c[3]);
            E4 twice = e4_sub(claim, rest);
            for (int i = 0; i < 4; i++) c[0][i] = gl_mul(twice[i], (GLP + 1) / 2);
            bool bad = (round == 3);
            if (bad) c[0][1] = gl_add(c[0][1], 1);
            E4 x = rng.e4();
            for (int j = 0; j < 4; j++) set_x4(4 * j, c[j]);
            set_x4(16, x);
            OpRes r = run_op(0x12);
            E4 g = e4_mul_add(e4_mul_add(e4_mul_add(c[3], x, c[2]), x, c[1]), x, c[0]);
            E4 got = get_y4();
            for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], g[i], "top SC_ROUND g(r)");
            check(r.ok == !bad, bad ? "SC_ROUND rejects a wrong claim" : "SC_ROUND accepts");
            if (!COMPACT) CHECK_EQ64(r.cycles, (uint64_t)(3 * (TOP_EXT_LAT + 1) + 2), "SC_ROUND cycles");
            claim = g;
        }
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
    section("top: ID, P2_PERM/P2_JIVE, EXT4_MAC, SC_ROUND (accept + reject), GF_MAC (accept + reject)", c0, f0);
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

// Fold a 2^n table by r.size() challenges with FOLD_MULTI (up to 8 rounds per command);
// returns the core's cycles summed over the commands. `preloaded` skips writing the challenges
// (the caller already put them in X).
static uint64_t fold_table(const std::vector<E4>& table, const std::vector<E4>& r, E4& result, bool preloaded = false) {
    int n = 0;
    while (((size_t)1 << n) < table.size()) n++;
    axil_write(R_STREAM, 0x80000000u);
    for (auto& e : table) stream_beat(e.data(), 4);
    uint64_t cycles = 0;
    for (size_t done = 0; done < r.size(); done += 8) {
        int m = (int)(r.size() - done < 8 ? r.size() - done : 8);
        if (!preloaded || done) for (int j = 0; j < m; j++) set_x4(4 * j, r[done + j]);
        cycles += run_op(0x15, (uint8_t)m, done == 0 ? (uint16_t)n : 0).cycles;
    }
    result = get_y4();
    return cycles;
}
static E4 fold_model(std::vector<E4> t, const std::vector<E4>& r) {
    for (auto& rj : r) {
        size_t half = t.size() / 2;
        for (size_t k = 0; k < half; k++) t[k] = e4_mul_add(rj, e4_sub(t[2 * k + 1], t[2 * k]), t[2 * k]);
        t.resize(half);
    }
    return t[0];
}

static void test_fold_and_chains() {
    long c0 = checks, f0 = fails;
    Rng rng(0xF01D);
    for (int n : {1, 2, 5, 9}) {
        std::vector<E4> t((size_t)1 << n), r(n);
        for (auto& e : t) e = rng.e4();
        for (auto& e : r) e = rng.e4();
        E4 got, want = fold_model(t, r);
        uint64_t cy = fold_table(t, r, got);
        for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], want[i], "fold result");
        // per round: one start clock, n/2 reads, FOLD_LAT = 9, done, hand-over; plus the final clock.
        uint64_t expect_cy = 1;
        for (int j = 0; j < n; j++) expect_cy += ((uint64_t)1 << (n - 1 - j)) + 9 + 3;
        if (!COMPACT) CHECK_EQ64(cy, expect_cy + (n > 8 ? 1 : 0), "fold cycles");
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

// ---- A QSAGSTA1-shaped root verification workload.
//
// This is a MODELLED operation mix, not a replay of verify_public_hologram on a real proof: the
// shape (stage geometry, query counts, sumcheck rounds) comes from the fixture's WHIR parameters
// for a 20-variable opening under the Poseidon2-Canopy regime with wire tag 6, and every
// operation runs on real data through the RTL and is checked against the reference model.
struct Stage { int inv_rate_log, fold_k, queries; };
static void trace_qsagsta1(FILE* rep) {
    long c0 = checks, f0 = fails;
    Rng rng(0x51534147535441ULL);
    const int NV = 20;
    const Stage stages[3] = {{2, 5, 216}, {4, 3, 109}, {6, 4, 74}};
    const int SUMCHECK_ROUNDS = 12 + 60;   // 12 WHIR folding rounds + 3 x 20 hologram sumcheck rounds (model)
    const int FINAL_VARS = 8;

    run_op(0x3F);
    uint64_t t_begin = cyc;
    uint64_t w0 = bus_writes, r0 = bus_reads, b0 = stream_beats;
    uint64_t sec_wall[4] = {0, 0, 0, 0}, core_fs = 0, core_sc = 0, core_fold = 0;
    long n_perm_fs = 0, n_perm_chain = 0, n_bfly = 0, n_mac_sc = 0;

    // 1. Fiat-Shamir transcript: one Poseidon2 permutation per sumcheck round (sequential by
    //    construction), with the round check and Horner evaluation on the Ext4 unit.
    uint64_t ts = cyc;
    St12 fs{};
    fs[8] = 0x51534147;
    E4 claim = rng.e4();
    set_x4(0, claim);
    run_op(0x11);
    for (int round = 0; round < SUMCHECK_ROUNDS; round++) {
        E4 c[4] = {rng.e4(), rng.e4(), rng.e4(), rng.e4()};
        E4 twice = e4_sub(claim, e4_add(e4_add(c[1], c[2]), c[3]));
        for (int i = 0; i < 4; i++) c[0][i] = gl_mul(twice[i], (GLP + 1) / 2);
        // absorb the first 8 coefficient limbs (rate 8), permute, squeeze the challenge
        for (int i = 0; i < 8; i++) fs[i] = gl_add(fs[i], c[i / 4][i % 4]);
        for (int i = 0; i < 12; i++) set_x(i, fs[i]);
        core_fs += run_op(0x01).cycles;
        St12 want = fs;
        p2_perm(want);
        for (int i = 0; i < 12; i++) { fs[i] = get_y(i); CHECK_EQ64(fs[i], want[i], "trace FS permutation"); }
        n_perm_fs++;
        E4 x = {fs[0], fs[1], fs[2], fs[3]};
        for (int j = 0; j < 4; j++) set_x4(4 * j, c[j]);
        set_x4(16, x);
        OpRes r = run_op(0x12);
        core_sc += r.cycles;
        n_mac_sc += 3;
        claim = e4_mul_add(e4_mul_add(e4_mul_add(c[3], x, c[2]), x, c[1]), x, c[0]);
        E4 got = get_y4();
        for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], claim[i], "trace sumcheck claim");
        check(r.ok, "trace sumcheck round");
    }
    sec_wall[0] = cyc - ts;

    // 2. Query phase per stage: leaf sponge + Canopy path on the chain engine (32 slots),
    //    then the 2^k-point fold of every opened leaf on the BRAM fold engine.
    int nv = NV;
    for (int s = 0; s < 3; s++) {
        const Stage& sg = stages[s];
        int depth = nv + sg.inv_rate_log - sg.fold_k;
        int leaf_elems = 1 << sg.fold_k;
        Tree t(depth, rng);
        D4 cap = {rng.gl(), rng.gl(), rng.gl(), rng.gl()};
        std::vector<uint32_t> leaf(sg.queries);
        std::vector<std::vector<E4>> evals(sg.queries);
        std::map<uint32_t, int> seen;
        for (int q = 0; q < sg.queries; q++) {
            do { leaf[q] = (uint32_t)(rng.next() % ((uint64_t)1 << depth)); } while (seen.count(leaf[q]));
            seen[leaf[q]] = q;
            evals[q].resize(leaf_elems);
            std::vector<uint64_t> limbs;
            for (auto& e : evals[q]) { e = rng.e4(); for (auto v : e) limbs.push_back(v); }
            t.node[((size_t)1 << depth) + leaf[q]] = p2_sponge_with_cap(LEAF_DOMAIN, cap, limbs);
        }
        t.build();
        uint64_t tq = cyc;
        chain_cfg(t, cap);
        for (int base = 0; base < sg.queries; base += 32) {
            int n = sg.queries - base < 32 ? sg.queries - base : 32;
            if (base) run_op(0x03, 3);   // clear DONE/OK only; key and top node stay
            for (int i = 0; i < n; i++) {
                std::vector<uint64_t> limbs;
                for (auto& e : evals[base + i]) for (auto v : e) limbs.push_back(v);
                n_perm_chain += load_chain(i, t, leaf[base + i], limbs);
            }
            OpRes r = run_op(0x05);
            check(r.ok, "trace: every query path reaches the committed top node");
            uint32_t want = n == 32 ? 0xFFFFFFFFu : ((1u << n) - 1);
            check(axil_read(R_CH_OK) == want, "trace: chain ok bitmap");
        }
        sec_wall[1] += cyc - tq;
        uint64_t tf = cyc;
        std::vector<E4> r(sg.fold_k);
        for (auto& e : r) e = rng.e4();
        for (int j = 0; j < sg.fold_k; j++) set_x4(4 * j, r[j]);   // one challenge set per stage
        for (int q = 0; q < sg.queries; q++) {
            E4 got, want = fold_model(evals[q], r);
            core_fold += fold_table(evals[q], r, got, true);
            n_bfly += leaf_elems - 1;
            for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], want[i], "trace query fold");
        }
        sec_wall[2] += cyc - tf;
        nv -= sg.fold_k;
    }

    // 3. Final polynomial: multilinear evaluation of 2^8 coefficients by eight folds.
    {
        uint64_t tf = cyc;
        std::vector<E4> tb((size_t)1 << FINAL_VARS), r(FINAL_VARS);
        for (auto& e : tb) e = rng.e4();
        for (auto& e : r) e = rng.e4();
        E4 got, want = fold_model(tb, r);
        core_fold += fold_table(tb, r, got);
        n_bfly += (1 << FINAL_VARS) - 1;
        for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], want[i], "trace final evaluation");
        sec_wall[3] = cyc - tf;
    }
    uint64_t wall = cyc - t_begin;
    uint64_t active = total_cycles();
    uint32_t perms = axil_read(R_PERMS);
    check(perms == (uint32_t)(n_perm_fs + n_perm_chain), "trace permutation count");

    const char* fmt =
        "QSAGSTA1-shaped root verification (modelled operation mix, real data, every result checked)\n"
        "  shape: nv=%d, stages (inv-rate log, fold k, queries) = (2,5,216) (4,3,109) (6,4,74), %d sumcheck rounds, final 2^%d\n"
        "  Poseidon2 permutations : %ld  (%ld transcript, sequential; %ld leaf-sponge + Canopy node, C-slow on the ring)\n"
        "  Ext4 MACs              : %ld  (%ld sumcheck Horner, %ld fold butterflies)\n"
        "  clocks, wall (AXI host with zero think time)  : %llu\n"
        "    transcript + sumcheck rounds                : %llu  (core-busy %llu + %llu)\n"
        "    query leaf hashes + Merkle paths            : %llu\n"
        "    query folds                                 : %llu\n"
        "    final evaluation                            : %llu\n"
        "  clocks with any engine active (TOTAL_CYCLES)  : %llu\n"
        "  fold engine core-busy clocks                  : %llu\n"
        "  bus traffic: %llu AXI4-Lite writes, %llu reads, %llu stream beats\n";
    for (FILE* f : {stdout, rep}) {
        if (!f) continue;
        fprintf(f, fmt, NV, SUMCHECK_ROUNDS, FINAL_VARS, (long)perms, n_perm_fs, n_perm_chain, n_mac_sc + n_bfly, n_mac_sc, n_bfly,
                (unsigned long long)wall, (unsigned long long)sec_wall[0], (unsigned long long)core_fs, (unsigned long long)core_sc,
                (unsigned long long)sec_wall[1], (unsigned long long)sec_wall[2], (unsigned long long)sec_wall[3],
                (unsigned long long)active, (unsigned long long)core_fold,
                (unsigned long long)(bus_writes - w0), (unsigned long long)(bus_reads - r0), (unsigned long long)(stream_beats - b0));
    }
    section("QSAGSTA1-shaped root verification trace", c0, f0);
}

// ---- Hyperweb edge fold: a 16-variable Ext4 table folded by 16 challenges (65,535 butterflies).
static void trace_edge_fold(FILE* rep) {
    long c0 = checks, f0 = fails;
    Rng rng(0xED6E);
    const int n = 16;
    std::vector<E4> t((size_t)1 << n), r(n);
    for (auto& e : t) e = rng.e4();
    for (auto& e : r) e = rng.e4();
    E4 want = fold_model(t, r), got;
    uint64_t t0 = cyc;
    uint64_t core = fold_table(t, r, got);
    uint64_t t_all = cyc - t0, t_load = ((uint64_t)1 << n) + 2, t_fold = t_all - t_load;
    for (int i = 0; i < 4; i++) CHECK_EQ64(got[i], want[i], "edge fold result");
    for (FILE* f : {stdout, rep}) {
        if (!f) continue;
        fprintf(f, "16-variable Ext4 edge fold (65,535 butterflies, in place in block RAM)\n"
                   "  table load over AXI4-Stream : %llu clocks (one entry per clock)\n"
                   "  16 fold rounds, core-busy   : %llu clocks (two FOLD_MULTI commands of 8 rounds)\n"
                   "  16 fold rounds, wall        : %llu clocks (incl. 16 challenges over AXI4-Lite)\n",
                (unsigned long long)t_load, (unsigned long long)core, (unsigned long long)t_fold);
    }
    section("16-variable hyperweb edge fold vs fold_first_var model", c0, f0);
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
    if (!COMPACT && !std::getenv("QSAG_REAL_ONLY")) { trace_qsagsta1(rep); trace_edge_fold(rep); }
    check((axil_read(R_STATUS) & 0x18) == 0, "no sticky error flags");
    if (rep) fclose(rep);
    printf("TOP: %ld checks, %ld mismatches, %llu clocks simulated\n", checks, fails, (unsigned long long)cyc);
    dut->final();
    dut.reset();
    return fails ? 1 : 0;
}
#endif
