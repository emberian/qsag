// Register-file unit bench (v2/rtl/dregg_regfile.sv, dregg_rf_slice.sv, dregg_rst.sv).
// Run with +verilator+rand+reset+2 and several seeds: storage starts random, so every check below also
// shows that reset reaches the latch it looks at.
//
//   T1 reset: every row and the hold register read zero after the pad reset, from a random start and from
//      a filled file, and already before the first clock edge
//   T2 single-row write and read-back on every lane, scratch, key, pin and state row; no other row changes
//   T3 two-phase: the row keeps the word of its own edge when the hold register changes in the next clock
//   T4 out rows: written only by out_we, never visible on the read port; Keccak work rows: written only
//      through their private data lines, never visible on the read port
//   T5 wipe: each class mask clears exactly its rows; the hold register, key, pin and state rows survive
//   T6 control-fault zeroise (zreq): one clock later every row and the hold register are zero
//   T7 stopped clock: with clk held low, and again with clk held high, a low tamper pad clears every row
//      and the hold register with no clock edge; they stay clear until the pad reset
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <memory>
#include <vector>
#include "Vunit_regfile_tb.h"
#include "verilated.h"
typedef uint64_t u64;
static std::unique_ptr<Vunit_regfile_tb> t;
static int errors = 0, checks = 0;
static int NR, KEY0, KW0, SC0, PIN0, OUT0;
static u64 rnd_state = 0x9E3779B97F4A7C15ULL;
static u64 rnd() { rnd_state ^= rnd_state << 13; rnd_state ^= rnd_state >> 7; rnd_state ^= rnd_state << 17; return rnd_state; }
#define CHECK(c, ...) do { checks++; if (!(c)) { errors++; if (errors < 30) { printf("  FAIL: "); printf(__VA_ARGS__); printf("\n"); } } } while (0)
static void idle() { t->h_en = 0; t->we = 0; t->out_we = 0; t->wipe = 0; t->kw_we = 0; t->zreq = 0; }
static void tick() { t->eval(); t->clk = 1; t->eval(); t->clk = 0; t->eval(); }
static u64 row(int r) { t->dump_row = r; t->eval(); return t->dump_data; }
static bool is_kw(int r) { return r >= KW0 && r < SC0; }
static bool is_out(int r) { return r >= OUT0; }
static void reset() { idle(); t->tamper_n = 1; t->por_n = 0; tick(); tick(); t->por_n = 1; tick(); tick(); tick(); }
// write word v to row r through the normal path
static void put(int r, u64 v) {
    idle();
    if (is_kw(r)) {
        for (int i = 0; i < 10; i++) t->kc_d[i] = 0;
        int k = r - KW0;
        if (k < 5) { t->kc_d[2 * k] = (uint32_t)v; t->kc_d[2 * k + 1] = (uint32_t)(v >> 32); } else t->kb_d = v;
        t->kw_we = 1 << k; tick(); idle(); tick();
        return;
    }
    t->h_en = 1; t->h_d = v;
    if (is_out(r)) t->out_we = 1 << (r - OUT0); else { t->we = 1; t->waddr = r; }
    tick(); idle(); tick();
}
static std::vector<u64> fill() {
    std::vector<u64> v(NR);
    for (int r = 0; r < NR; r++) { v[r] = rnd() | 1; put(r, v[r]); }
    for (int r = 0; r < NR; r++) CHECK(row(r) == v[r], "fill: row %d", r);
    return v;
}
static void all_zero(const char* what) {
    for (int r = 0; r < NR; r++) CHECK(row(r) == 0, "%s: row %d = %016llx", what, r, (unsigned long long)row(r));
    CHECK(t->h_q == 0, "%s: hold register not zero", what);
}
int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    t.reset(new Vunit_regfile_tb);
    t->clk = 0; t->por_n = 1; t->tamper_n = 1; idle();     // no reset yet: storage is whatever the simulator started with t->raddr = 0; t->waddr = 0; t->h_d = 0; t->kb_d = 0;
    for (int i = 0; i < 10; i++) t->kc_d[i] = 0;
    t->eval();
    NR = t->nrows_o; KEY0 = t->key0_o; KW0 = t->kwork0_o; SC0 = t->scratch0_o; PIN0 = t->pin0_o; OUT0 = t->out0_o;
    // T1
    int nonzero = 0;
    for (int r = 0; r < NR; r++) nonzero += row(r) != 0;
    reset();
    all_zero("T1 reset");
    printf("T1 reset: %d of %d rows held a non-zero start value before reset (secret reset started %s)\n", nonzero, NR,
           nonzero ? "released" : "asserted or the storage started at zero");
    fill();
    idle(); t->h_en = 1; t->h_d = rnd() | 1; tick(); idle();
    t->por_n = 0; t->eval();                       // asynchronous: no clock edge
    all_zero("T1 pad reset, no clock");
    reset();
    all_zero("T1 pad reset");
    // T2
    for (int r = 0; r < NR; r++) {
        if (is_kw(r) || is_out(r)) continue;
        u64 v = rnd() | 1;
        put(r, v);
        t->raddr = r; t->eval();
        CHECK(t->rdata == v, "T2: row %d reads %016llx, wrote %016llx", r, (unsigned long long)t->rdata, (unsigned long long)v);
        for (int q = 0; q < NR; q++) if (q != r) CHECK(row(q) == 0, "T2: write of row %d changed row %d", r, q);
        put(r, 0);
    }
    // T3
    {
        idle(); t->h_en = 1; t->h_d = 0x1111; t->we = 1; t->waddr = 3; tick();     // edge n: hold = 0x1111, row 3 opens
        idle(); t->h_en = 1; t->h_d = 0x2222; tick();                               // edge n + 1: hold changes, row 3 closed
        tick();
        CHECK(row(3) == 0x1111, "T3: row 3 = %llx", (unsigned long long)row(3));
        CHECK(t->h_q == 0x2222, "T3: hold");
        put(3, 0);
    }
    // T4
    reset();
    {
        std::vector<u64> v = fill();
        for (int r = 0; r < NR; r++) {
            t->raddr = r; t->eval();
            if (is_kw(r) || is_out(r)) CHECK(t->rdata == 0, "T4: row %d visible on the read port", r);
            else CHECK(t->rdata == v[r], "T4: row %d read", r);
        }
        for (int r = NR; r < 128; r++) { t->raddr = r; t->eval(); CHECK(t->rdata == 0, "T4: address %d reads non-zero", r); }
        CHECK(t->out_q[0] == (uint32_t)v[OUT0] && t->out_q[2] == (uint32_t)v[OUT0 + 1], "T4: out_q");
        // a normal write addressed at an out or work row does nothing
        for (int r = 0; r < NR; r++) if (is_kw(r) || is_out(r)) {
            idle(); t->h_en = 1; t->h_d = 0xDEAD; t->we = 1; t->waddr = r; tick(); idle(); tick();
            CHECK(row(r) == v[r], "T4: row %d written through the addressed path", r);
        }
        for (int r = NR; r < 128; r++) {
            idle(); t->h_en = 1; t->h_d = 0xBEEF; t->we = 1; t->waddr = r; tick(); idle(); tick();
        }
        for (int r = 0; r < NR; r++) CHECK(row(r) == v[r], "T4: write to an absent address changed row %d", r);
    }
    // T5
    for (int m = 1; m < 16; m++) {
        reset();
        std::vector<u64> v = fill();
        idle(); t->h_en = 1; t->h_d = 0x5A5A5A5A5A5A5A5AULL; tick();
        idle(); t->wipe = m; tick(); idle(); tick();
        for (int r = 0; r < NR; r++) {
            bool cleared = ((m & 1) && r < 8) || ((m & 2) && r >= 8 && r < SC0) || ((m & 4) && r >= SC0 && r < KEY0) || ((m & 8) && r >= OUT0);
            CHECK(row(r) == (cleared ? 0 : v[r]), "T5: mask %d row %d = %016llx", m, r, (unsigned long long)row(r));
        }
        CHECK(t->h_q == 0x5A5A5A5A5A5A5A5AULL, "T5: hold register changed by a wipe");
    }
    // T6
    reset(); fill();
    idle(); t->zreq = 1; tick(); idle(); t->eval();
    all_zero("T6 zeroise (during the pulse)");
    tick(); tick();
    all_zero("T6 zeroise");
    CHECK(t->srst_n == 1, "T6: secret reset not released");
    // T7
    for (int level = 0; level < 2; level++) {
        reset(); fill();
        idle(); t->h_en = 1; t->h_d = rnd() | 1; tick(); idle(); t->eval();
        t->clk = level; t->eval();                     // the clock stops here
        t->tamper_n = 0; t->eval();
        CHECK(t->srst_n == 0, "T7: secret reset not asserted");
        all_zero(level ? "T7 tamper, clock held high" : "T7 tamper, clock held low");
        t->tamper_n = 1; t->eval();
        CHECK(t->srst_n == 0, "T7: secret reset released without a pad reset");
        t->clk = 0; t->eval();
        tick(); tick();
        idle(); t->h_en = 1; t->h_d = 0x77; t->we = 1; t->waddr = 1; tick(); idle(); tick();
        CHECK(row(1) == 0 && t->h_q == 0, "T7: storage writable while the tamper latch is set");
    }
    reset();
    put(1, 0x77);
    CHECK(row(1) == 0x77, "after the pad reset the file works again");
    t->final();
    t.reset();
    printf("unit_regfile (%d rows): %d checks, %d errors: %s\n", NR, checks, errors, errors ? "FAIL" : "PASS");
    return errors ? 1 : 0;
}
