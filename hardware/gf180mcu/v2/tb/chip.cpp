// Chip-level co-simulation: the recorded reference script (tb/record.py, scenario "script") through
// dregg_top, that is through the SPI pins, with the generated ROM.
//
//   chip <tracedir> [half]      half: SCK half period in core clocks (default 3)
//
// Per transaction: one WRITE frame carries the request (the host waits for IRQ before each word); each
// response word is fetched with one READ frame after IRQ rises. Required, with no tolerance:
//   response words equal; cmd_active && !link_wait clocks equal the interpreter's count; no control fault;
//   FRAM transfers equal the model's; VERIFY_OK and FAULT pins equal; zero failed core checks.
// It also reads the diagnostic word with the core clock running and with it stopped.
// The trace must contain one chip, no control fault and no state placed by a test (the script has none).
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <vector>
#include "Vdregg_chip_tb.h"
#include "verilated.h"
typedef uint64_t u64;
struct Own { bool ok; u64 w[8]; };
struct Xfer { bool fault = false, poked = false; u64 cycles = 0; std::vector<u64> q, r, ent; std::vector<std::string> fram; std::vector<Own> own; u64 pins_fault = 0, pins_vok = 0; };

static std::unique_ptr<Vdregg_chip_tb> top;
static int errors = 0, HALF = 3;
static u64 ticks = 0;
static void err(const char* fmt, ...) { errors++; if (errors > 40) return; va_list ap; va_start(ap, fmt); printf("  ERROR: "); vprintf(fmt, ap); printf("\n"); va_end(ap); }
static std::vector<u64> hexwords(std::istringstream& is) { std::vector<u64> v; std::string t; while (is >> t) { if (t == "|") break; v.push_back(strtoull(t.c_str(), nullptr, 16)); } return v; }

// ---- per-transaction context for the stand-ins and counters
static const Xfer* X = nullptr;
static u64 counted = 0, raw_active = 0, t_nonce = 8, t_auth = 3900000;
static size_t ei = 0, oi = 0, f_i = 0;
static long ent_k = -1, own_k = -1;
static u64 own_w[8]; static int own_seen = 0; static bool own_reply = false, has_owner = false, faulted = false;
// FRAM slave (as in cosim.cpp)
static int f_bad = 0, f_prev_sck = 0, f_prev_cs = 1, f_bits = 0, f_bytes = 0, f_addr = 0, f_cmd = 0, f_wel = 0, f_wn = 0;
static uint8_t f_sh = 0, f_out = 0; static std::vector<uint8_t> f_rd; static size_t f_rdi = 0; static u64 f_wacc = 0;
static void fram_open(bool write) {
    char want[8]; snprintf(want, sizeof want, "s%d%c", f_addr == 32 ? 1 : 0, write ? 'w' : 'r');
    if ((f_addr != 0 && f_addr != 32) || !X || f_i >= X->fram.size() || X->fram[f_i] != want) { f_bad++; err("FRAM: frame the model did not open"); return; }
    f_i++; f_rd.clear(); f_rdi = 0; f_wacc = 0; f_wn = 0;
    if (!write) while (f_i < X->fram.size() && X->fram[f_i][0] == 'r') { u64 v = strtoull(X->fram[f_i].c_str() + 1, nullptr, 16); for (int b = 0; b < 8; b++) f_rd.push_back((uint8_t)(v >> (8 * b))); f_i++; }
}
static void fram_step() {
    int cs = top->fram_cs_n, sck = top->fram_sck, mosi = top->fram_mosi;
    if (cs) { if (!f_prev_cs && f_cmd == 0x02) f_wel = 0; f_bits = 0; f_bytes = 0; f_cmd = 0; top->fram_miso = 0; }
    else {
        if (sck && !f_prev_sck) {
            f_sh = (uint8_t)((f_sh << 1) | mosi);
            if (++f_bits == 8) {
                f_bits = 0;
                if (f_bytes == 0) { f_cmd = f_sh; if (f_cmd == 0x06) f_wel = 1; }
                else if (f_bytes == 1) f_addr = f_sh << 8;
                else if (f_bytes == 2) { f_addr |= f_sh; if (f_cmd == 0x03) fram_open(false); else if (f_cmd == 0x02 && f_wel) fram_open(true); else { f_bad++; err("FRAM: bad command"); } }
                else if (f_cmd == 0x02 && f_wel) {
                    f_wacc |= (u64)f_sh << (8 * f_wn);
                    if (++f_wn == 8) {
                        if (!X || f_i >= X->fram.size() || X->fram[f_i][0] != 'w' || strtoull(X->fram[f_i].c_str() + 1, nullptr, 16) != f_wacc) { f_bad++; err("FRAM: word written differs from the model's"); } else f_i++;
                        f_wacc = 0; f_wn = 0;
                    }
                }
                f_bytes++;
                if (f_cmd == 0x03 && f_bytes >= 3) f_out = f_rdi < f_rd.size() ? f_rd[f_rdi++] : 0;
            }
        }
        if (!sck && f_prev_sck) { if (f_cmd == 0x03 && f_bytes >= 3) { top->fram_miso = (f_out >> 7) & 1; f_out = (uint8_t)(f_out << 1); } }
    }
    f_prev_sck = sck; f_prev_cs = cs;
}
// one core clock, with the stand-ins and the clock counter
static void tick() {
    top->ent_valid = (ent_k >= 0 && (u64)ent_k == t_nonce);
    if (top->ent_valid && X) {
        u64 a = ei < X->ent.size() ? X->ent[ei] : 0, b = ei + 1 < X->ent.size() ? X->ent[ei + 1] : 0;
        ei += 2;
        top->ent_data[0] = (uint32_t)a; top->ent_data[1] = (uint32_t)(a >> 32); top->ent_data[2] = (uint32_t)b; top->ent_data[3] = (uint32_t)(b >> 32);
    }
    top->own_done = (own_k >= 0 && (u64)own_k == t_auth);
    top->own_ok = own_reply;
    top->eval();
    bool lw = top->link_wait;
    if (top->cmd_active) { raw_active++; if (!lw) counted++; }
    if (top->fault_now) faulted = true;
    if (ent_k >= 0) { if (top->ent_valid) ent_k = -1; else if (!lw) ent_k++; }
    if (own_k >= 0) {
        if (top->own_valid) { own_w[top->own_idx] = top->own_data; own_seen++; }
        if (own_seen == 8) {
            own_seen = 9;
            if (!has_owner) own_reply = false;
            else if (X && oi < X->own.size()) { const Own& o = X->own[oi++]; for (int i = 0; i < 8; i++) if (own_w[i] != o.w[i]) { err("owner statement differs from the model's"); break; } own_reply = o.ok; }
            else own_reply = true;
        }
        if (top->own_done) own_k = -1; else if (!lw) own_k++;
    }
    if (top->ent_req) ent_k = 1;
    if (top->own_start) { own_k = 1; own_seen = 0; own_reply = false; }
    top->clk = 1; top->eval(); fram_step(); top->clk = 0; top->eval();
    ticks++;
}
static void ticks_n(int n) { for (int i = 0; i < n; i++) tick(); }
// ---- SPI host (mode 0). With run_core = false only SCK moves: the core clock is stopped.
static int spi_bit(int mosi, bool run_core = true) {
    top->spi_mosi = mosi; top->eval();
    if (run_core) ticks_n(HALF);
    int miso = top->spi_miso;
    top->spi_sck = 1; top->eval();
    if (run_core) ticks_n(HALF);
    top->spi_sck = 0; top->eval();
    return miso;
}
static void spi_byte(uint8_t b, bool run_core = true) { for (int i = 7; i >= 0; i--) spi_bit((b >> i) & 1, run_core); }
static u64 spi_read_word(uint8_t cmd, bool run_core = true) {
    top->spi_cs_n = 0; top->eval(); if (run_core) ticks_n(2);
    spi_byte(cmd, run_core);
    for (int i = 0; i < 8; i++) spi_bit(0, run_core);
    u64 w = 0;
    for (int b = 0; b < 8; b++) for (int i = 7; i >= 0; i--) w |= (u64)spi_bit(0, run_core) << (8 * b + i);
    top->spi_cs_n = 1; top->eval(); if (run_core) ticks_n(4);
    return w;
}
static bool wait_irq(u64 limit) { u64 n = 0; while (!top->irq && n++ < limit) tick(); return top->irq; }

int main(int argc, char** argv) {
    if (argc < 2) { printf("usage: chip <tracedir> [half]\n"); return 2; }
    if (argc > 2) HALF = atoi(argv[2]);
    Verilated::commandArgs(argc, argv);
    top.reset(new Vdregg_chip_tb);
    std::ifstream in(std::string(argv[1]) + "/trace.txt");
    std::vector<Xfer> xs; std::string line; int nchips = 0; bool puf = false, ent = false; u64 secret[4] = {0};
    std::vector<u64> s1flags;
    while (std::getline(in, line)) {
        std::istringstream is(line); std::string tag; is >> tag;
        if (tag == "MODEL") { std::string k; u64 v; while (is >> k >> v) { if (k == "nonce_draw") t_nonce = v; if (k == "auth_verify") t_auth = v; } }
        else if (tag == "CHIP") {
            nchips++; int cid; std::string k, v; is >> cid;
            while (is >> k >> v) { if (k == "ent") ent = v == "1"; if (k == "own") has_owner = v == "1"; if (k == "puf" && v != "-") { puf = true; for (int i = 0; i < 4; i++) secret[3 - i] = strtoull(v.substr(16 * i, 16).c_str(), nullptr, 16); } }
        } else if (tag == "POR") { Xfer x; x.q.clear(); x.poked = true; x.cycles = ~0ULL; xs.push_back(x); }       // marker: pad reset
        else if (tag == "X") { Xfer x; int cid, f, p; is >> cid >> f >> x.cycles >> p; x.fault = f; x.poked = p; xs.push_back(x); }
        else if (tag == "Q") xs.back().q = hexwords(is);
        else if (tag == "R") xs.back().r = hexwords(is);
        else if (tag == "M") { std::string t; while (is >> t) xs.back().fram.push_back(t); }
        else if (tag == "E") xs.back().ent = hexwords(is);
        else if (tag == "O") { std::vector<u64> v = hexwords(is); for (size_t i = 0; i + 9 <= v.size(); i += 9) { Own o; o.ok = v[i]; for (int j = 0; j < 8; j++) o.w[j] = v[i + 1 + j]; xs.back().own.push_back(o); } }
        else if (tag == "S1") { std::vector<u64> f = hexwords(is); xs.back().pins_fault = f[2] | f[3] | f[4]; xs.back().pins_vok = f[5]; }
    }
    if (nchips != 1) { printf("the trace must hold exactly one chip (has %d)\n", nchips); return 2; }
    auto reset = [&]() {
        top->por_n = 0; top->eval(); ticks_n(3);
        top->por_n = 1; top->eval();
        int n = 0; while (!top->ready && n++ < 200) tick();
        if (!top->ready) err("no boot");
        tick();
    };
    top->clk = 0; top->tamper_n = 1; top->spi_sck = 0; top->spi_cs_n = 1; top->spi_mosi = 0; top->fram_miso = 0;
    top->puf_present = puf; top->ent_present = ent; top->ent_valid = 0; top->own_done = 0; top->own_ok = 0;
    for (int i = 0; i < 4; i++) top->puf_secret[2 * i] = (uint32_t)secret[i], top->puf_secret[2 * i + 1] = (uint32_t)(secret[i] >> 32);
    reset();
    // diagnostic word, clock running and clock stopped
    u64 d1 = spi_read_word(0x05), d2 = spi_read_word(0x05, false);
    if ((d1 & 0xFFFF) != 0xD182 || (d1 >> 56) != 0x5A) err("READ_DIAG %016llx", (unsigned long long)d1);
    if ((d2 & 0xFFFF) != 0xD182 || (d2 >> 56) != 0x5A) err("READ_DIAG with the core clock stopped %016llx", (unsigned long long)d2);
    if (((d1 >> 16) & 0xFF) == ((d1 >> 32) & 0xFF)) err("READ_DIAG: heartbeat samples equal with the clock running");
    if (((d2 >> 16) & 0xFF) != ((d2 >> 32) & 0xFF)) err("READ_DIAG: heartbeat samples differ with the clock stopped");
    if (!((d1 >> 27) & 1)) err("READ_DIAG: ready bit clear");
    printf("READ_DIAG %016llx (clock running), %016llx (clock stopped)\n", (unsigned long long)d1, (unsigned long long)d2);

    u64 n = 0, n_rsp = 0, n_cyc = 0, n_fram = 0, words_out = 0, max_raw_over = 0;
    for (const Xfer& x : xs) {
        if (x.cycles == ~0ULL) { reset(); continue; }
        n++;
        if (x.fault || x.poked) { err("transaction %llu needs a control fault or a placed state: not a chip-level trace", (unsigned long long)n); continue; }
        X = &x; counted = raw_active = 0; ei = oi = f_i = 0; f_bad = 0; faulted = false;
        // request: one WRITE frame
        top->spi_cs_n = 0; top->eval(); ticks_n(2);
        spi_byte(0x01);
        for (u64 w : x.q) {
            ticks_n(4);
            if (!wait_irq(60000000)) { err("transaction %llu: RX_FREE never rose", (unsigned long long)n); break; }
            for (int b = 0; b < 8; b++) spi_byte((uint8_t)(w >> (8 * b)));
        }
        ticks_n(2); top->spi_cs_n = 1; top->eval(); ticks_n(4);
        // response: one READ frame per word
        std::vector<u64> got;
        for (size_t i = 0; i < x.r.size(); i++) {
            if (!wait_irq(60000000)) { err("transaction %llu: no response word %zu", (unsigned long long)n, i); break; }
            got.push_back(spi_read_word(0x02));
        }
        u64 guard = 0;
        while (top->cmd_active && guard++ < 1000000) tick();
        ticks_n(8);
        if (top->irq) err("transaction %llu: more response words than the model's %zu", (unsigned long long)n, x.r.size());
        if (got == x.r) n_rsp++; else { err("transaction %llu: response differs", (unsigned long long)n); for (size_t i = 0; i < got.size() && i < x.r.size(); i++) if (got[i] != x.r[i]) { printf("    word %zu: rtl %016llx model %016llx\n", i, (unsigned long long)got[i], (unsigned long long)x.r[i]); break; } }
        if (counted == x.cycles) n_cyc++; else err("transaction %llu: clocks rtl %llu model %llu", (unsigned long long)n, (unsigned long long)counted, (unsigned long long)x.cycles);
        if (f_bad == 0 && f_i == x.fram.size()) n_fram++; else err("transaction %llu: FRAM transfers differ", (unsigned long long)n);
        if (faulted) err("transaction %llu: control fault", (unsigned long long)n);
        if (top->verify_ok != x.pins_vok || top->fault != x.pins_fault) err("transaction %llu: pins", (unsigned long long)n);
        if (ei != x.ent.size() || oi != x.own.size()) err("transaction %llu: stand-in calls differ", (unsigned long long)n);
        words_out += got.size();
        if (raw_active - counted > max_raw_over) max_raw_over = raw_active - counted;
        X = nullptr;
    }
    u64 d3 = spi_read_word(0x05);
    if ((d3 >> 46) & 3) err("link reports overrun or underrun: READ_DIAG %016llx", (unsigned long long)d3);
    u64 asserts = top->assert_count;
    top->final();
    printf("chip-level co-simulation over SPI (SCK = clk / %d)\n", 2 * HALF);
    printf("  transactions            %llu\n  responses equal         %llu (%llu words read over SPI)\n  clock counts equal      %llu\n  FRAM transfers equal    %llu\n",
           (unsigned long long)n, (unsigned long long)n_rsp, (unsigned long long)words_out, (unsigned long long)n_cyc, (unsigned long long)n_fram);
    printf("  longest link wait inside one command %llu clocks; core clocks simulated %llu\n  failed core checks      %llu\n", (unsigned long long)max_raw_over, (unsigned long long)ticks, (unsigned long long)asserts);
    bool pass = errors == 0 && asserts == 0 && n > 0;
    printf("RESULT chip: %s (%d errors)\n", pass ? "PASS" : "FAIL", errors);
    top.reset();
    return pass ? 0 : 1;
}
