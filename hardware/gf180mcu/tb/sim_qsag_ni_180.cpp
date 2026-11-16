// QSAG-NI-180 full-chip multi-clock / asynchronous testbench (Verilator --timing).
//
//   sim_qsag_ni_180 <script.txt> <config> [scenario]
//
// config   = spi | ss_023 | ss_100 | ss_370 | ss_dcro | async | async_slow
// scenario = script (default) | clkswitch | tamper | glitch | trng | loops
//
// The script (tb/gen_script.py) carries request words and the model's expected response
// words; this file only implements the three link personalities, the FRAM model and the
// physical scenarios. Time unit: picoseconds.
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <fstream>
#include <functional>
#include <sstream>
#include <string>
#include <vector>

#include "Vtb_top.h"
#include "verilated.h"

typedef uint64_t u64;

struct Cfg {
    int mode = 0;            // IO_MODE
    int bypass = 1;          // EXT_CLK_BYPASS
    u64 half_pad = 10000;    // clk_pad half period
    u64 io_half = 7300;      // SPI SCK half period / RX_CLK half period / async wire delay
    u64 csr = 0;             // written after reset when nonzero
};

static const u64 CSR_DEFAULT = 0x0268C01FULL;
static u64 csr_val(int tap, int mode, int amp, int len, int gb, int arm, int force, int trng, u64 fll = 0) {
    return (u64)tap | ((u64)mode << 7) | ((u64)amp << 9) | ((u64)len << 11) | ((u64)gb << 15) | ((u64)arm << 17) |
           ((u64)force << 18) | (1ULL << 19) | (3ULL << 21) | ((u64)trng << 25) | (fll << 32);
}

struct Sim {
    VerilatedContext* ctx;
    Vtb_top* top;
    Cfg cfg;
    u64 t = 0;
    int errors = 0;

    // pad model
    bool drv[38] = {};
    int val[38] = {};
    int cs_n = 1, bypass = 1;

    // clocks
    int clk = 0;
    u64 next_pad = 0;
    u64 glitch_half = 0;     // length of the two shortened half periods of an injected glitch
    int glitch_req = 0, glitch_cnt = 0;
    int rxclk = 0;
    u64 next_rx = 0;
    bool rx_free = false;

    // link queues
    std::deque<uint8_t> txq;         // bytes towards the chip (mode 01)
    std::deque<uint8_t> rxq;         // bytes from the chip (modes 01, 1x)
    int prev_out15 = 0;
    u64 ack_at = 0;
    int ack_val = 0;

    // FRAM model
    uint8_t fram[65536] = {};
    uint8_t fram_saved[65536] = {};
    int f_cs = 1, f_sck = 0, f_bits = 0, f_state = 0, f_wel = 0, f_miso = 0, f_obit = 0;
    unsigned f_sh = 0, f_addr = 0, f_cmd = 0;
    uint8_t f_out = 0;
    u64 fram_writes = 0;

    // core clock monitor
    int cc = 0;
    u64 cc_edge = 0, cc_min = ~0ULL, cc_cycles = 0;
    bool cc_armed = false;
    u64 contention = 0;

    int pad_out(int i) { return (top->bidir_out >> i) & 1; }
    int pad_oe(int i) { return (top->bidir_oe >> i) & 1; }

    void drive() {
        u64 in = 0;
        u64 oe = top->bidir_oe, pu = top->bidir_pu;
        for (int i = 0; i < 38; i++) {
            int v;
            if ((oe >> i) & 1) {
                v = 0;                                  // input buffer disabled while driving
                if (drv[i]) contention++;
            } else if (drv[i]) v = val[i];
            else v = (pu >> i) & 1;                     // pull-up, else pull-down / low
            in |= (u64)v << i;
        }
        if (!((oe >> 25) & 1)) in = (in & ~(1ULL << 25)) | ((u64)f_miso << 25);
        top->bidir_in = in;
        top->clk = clk;
        top->input_in = (bypass & 1) | ((cfg.mode & 3) << 1) | ((cs_n & 1) << 3);
    }

    void fram_model() {
        int cs = pad_out(22), sck = pad_out(23), mosi = pad_out(24);
        if (cs && !f_cs) {                              // CS_N rising: end of transaction
            if (f_cmd == 0x02) f_wel = 0;
            f_state = 0;
        }
        if (!cs && f_cs) {
            f_bits = 0;
            f_state = 1;
            f_sh = 0;
            f_cmd = 0;
        }
        if (!cs && sck && !f_sck) {                     // rising edge: sample MOSI
            f_sh = ((f_sh << 1) | mosi) & 0xFF;
            if (++f_bits == 8) {
                f_bits = 0;
                if (f_state == 1) {
                    f_cmd = f_sh;
                    if (f_cmd == 0x06) f_wel = 1;
                    f_state = (f_cmd == 0x02 || f_cmd == 0x03) ? 2 : 0;
                } else if (f_state == 2) {
                    f_addr = f_sh << 8;
                    f_state = 3;
                } else if (f_state == 3) {
                    f_addr |= f_sh;
                    f_state = 4;
                    f_out = fram[f_addr & 0xFFFF];
                    f_obit = 7;
                } else if (f_state == 4 && f_cmd == 0x02 && f_wel) {
                    fram[f_addr++ & 0xFFFF] = (uint8_t)f_sh;
                    fram_writes++;
                }
            }
        }
        if (!cs && !sck && f_sck && f_state == 4 && f_cmd == 0x03) {   // falling edge: next bit
            f_miso = (f_out >> f_obit) & 1;
            if (--f_obit < 0) {
                f_obit = 7;
                f_out = fram[++f_addr & 0xFFFF];
            }
        }
        f_cs = cs;
        f_sck = sck;
    }

    void monitors() {
        int c = top->clk_core_mon;
        if (c != cc) {
            if (cc_armed && cc_edge && t - cc_edge < cc_min) cc_min = t - cc_edge;
            cc_edge = t;
            cc = c;
            if (c) cc_cycles++;
        }
        fram_model();
        int o15 = pad_out(15);
        if (cfg.mode == 1) {
            if (o15 && !prev_out15 && pad_out(16)) rxq.push_back((top->bidir_out >> 7) & 0xFF);
        } else if (cfg.mode >= 2) {
            if (o15 != prev_out15) {                    // REQ_OUT toggled: take the byte, ack later
                rxq.push_back((top->bidir_out >> 7) & 0xFF);
                ack_at = t + cfg.io_half;
                ack_val = o15;
            }
        }
        prev_out15 = o15;
    }

    void rx_edge() {                                    // mode 01: drive on the falling edge
        if (rxclk) return;
        if (!txq.empty() && pad_out(35)) {
            uint8_t b = txq.front();
            txq.pop_front();
            for (int i = 0; i < 8; i++) val[27 + i] = (b >> i) & 1;
            val[36] = 1;
        } else val[36] = 0;
    }

    void run_until(u64 target) {
        while (true) {
            u64 nxt = target;
            if (next_pad < nxt) nxt = next_pad;
            if (rx_free && next_rx < nxt) nxt = next_rx;
            if (ack_at && ack_at < nxt) nxt = ack_at;
            if (top->eventsPending() && top->nextTimeSlot() < nxt) nxt = top->nextTimeSlot();
            t = nxt;
            ctx->time(t);
            if (t == next_pad) {
                clk ^= 1;
                if (glitch_req && clk == 1) {            // one short cycle, rising edge to rising edge
                    glitch_req = 0;
                    glitch_cnt = 2;
                }
                next_pad += glitch_cnt ? glitch_half : cfg.half_pad;
                if (glitch_cnt) glitch_cnt--;
            }
            if (rx_free && t == next_rx) {
                rxclk ^= 1;
                val[37] = rxclk;
                next_rx += cfg.io_half;
                rx_edge();
            }
            if (ack_at && t == ack_at) {
                val[17] = ack_val;
                ack_at = 0;
            }
            drive();
            top->eval();
            monitors();
            if (t >= target) break;
        }
    }
    void advance(u64 dt) { run_until(t + dt); }
    bool wait_for(const std::function<bool()>& pred, u64 timeout, const char* what) {
        u64 t0 = t;
        while (!pred()) {
            advance(2000);
            if (t - t0 > timeout) {
                printf("  TIMEOUT waiting for %s at t=%" PRIu64 " ps\n", what, t);
                errors++;
                return false;
            }
        }
        return true;
    }

    // ---------------------------------------------------------------- reset
    void reset() {
        memset(drv, 0, sizeof drv);
        memset(val, 0, sizeof val);
        txq.clear();
        rxq.clear();
        cs_n = 1;
        cc_armed = false;
        top->rst_n = 0;
        if (cfg.mode == 0) drv[18] = true;                               // SCK idle low
        if (cfg.mode == 1) {
            for (int i = 27; i <= 37; i++) if (i != 35) drv[i] = true;
            drv[17] = true;
            val[17] = 1;                                                 // TX_READY
            rx_free = true;
            next_rx = t + cfg.io_half;
        }
        if (cfg.mode >= 2) {
            for (int i = 27; i <= 34; i++) drv[i] = true;
            for (int i = 0; i <= 6; i++) drv[i] = true;
            drv[18] = drv[37] = drv[17] = true;
        }
        advance(10 * cfg.half_pad + 137);
        top->rst_n = 1;
        advance(40 * cfg.half_pad);
        prev_out15 = pad_out(15);
        cc_min = ~0ULL;
        cc_edge = 0;
        cc_armed = true;
    }

    // ---------------------------------------------------------------- mode 00: SPI
    int spi_w = 0;                                       // rotates through x1, x4, x8
    void sck_pulse() {
        advance(cfg.io_half);
        val[18] = 1;
        advance(cfg.io_half);
        val[18] = 0;
    }
    void spi_cmd(uint8_t cmd) {
        cs_n = 0;
        advance(cfg.io_half);
        drv[0] = true;
        for (int b = 7; b >= 0; b--) {
            val[0] = (cmd >> b) & 1;
            sck_pulse();
        }
    }
    void spi_end() {
        for (int i = 0; i < 8; i++) drv[i] = false;
        advance(cfg.io_half);
        cs_n = 1;
        advance(2 * cfg.io_half);
    }
    void spi_write(const std::vector<u64>& ws, int width) {
        spi_cmd(width == 1 ? 0x01 : width == 4 ? 0x41 : 0x81);
        for (int i = 0; i < width; i++) drv[i] = true;
        for (u64 w : ws)
            for (int by = 0; by < 8; by++) {
                uint8_t b = (w >> (8 * by)) & 0xFF;
                if (width == 1) {
                    for (int k = 7; k >= 0; k--) {
                        val[0] = (b >> k) & 1;
                        sck_pulse();
                    }
                } else if (width == 4) {
                    for (int nb = 1; nb >= 0; nb--) {
                        for (int k = 0; k < 4; k++) val[k] = (b >> (4 * nb + k)) & 1;
                        sck_pulse();
                    }
                } else {
                    for (int k = 0; k < 8; k++) val[k] = (b >> k) & 1;
                    sck_pulse();
                }
            }
        spi_end();
    }
    u64 spi_read_word(int width) {
        std::vector<u64> ws;
        spi_read(width, 1, ws);
        return ws[0];
    }
    void spi_read(int width, int nwords, std::vector<u64>& out) {
        spi_cmd(width == 1 ? 0x02 : width == 4 ? 0x42 : 0x82);
        for (int i = 0; i < 8; i++) drv[i] = false;      // bus turnaround: host releases DQ
        for (int i = 0; i < 8; i++) sck_pulse();
        for (int wd = 0; wd < nwords; wd++) {
        u64 w = 0;
        for (int by = 0; by < 8; by++) {
            unsigned b = 0;
            int beats = width == 1 ? 8 : width == 4 ? 2 : 1;
            for (int k = 0; k < beats; k++) {
                advance(cfg.io_half);
                unsigned dq = top->bidir_out & 0xFF;
                unsigned need = width == 1 ? 0x02 : width == 4 ? 0x0F : 0xFF;
                if ((top->bidir_oe & 0xFF) != need) {
                    if (errors < 20) printf("  SPI read: DQ output enables %02x, expected %02x\n", (unsigned)(top->bidir_oe & 0xFF), need);
                    errors++;
                }
                if (width == 1) b = (b << 1) | ((dq >> 1) & 1);
                else if (width == 4) b = (b << 4) | (dq & 0xF);
                else b = dq;
                val[18] = 1;
                advance(cfg.io_half);
                val[18] = 0;
            }
            w |= (u64)b << (8 * by);
        }
        out.push_back(w);
        }
        spi_end();
        if (top->bidir_oe & 0xFF) {
            printf("  SPI: DQ still driven after CS_N high\n");
            errors++;
        }
    }

    // ---------------------------------------------------------------- mode 1x: clockless
    int req_in = 0;
    void async_send16(unsigned d) {
        for (int i = 0; i < 8; i++) val[27 + i] = (d >> i) & 1;
        for (int i = 0; i < 7; i++) val[i] = (d >> (8 + i)) & 1;
        val[18] = (d >> 15) & 1;
        advance(cfg.io_half);                            // bundling: data before the request edge
        req_in ^= 1;
        val[37] = req_in;
        wait_for([&] { return pad_out(36) == req_in; }, 400000000ULL, "ACK_OUT");
        advance(cfg.io_half / 2);
    }

    // ---------------------------------------------------------------- link-independent API
    void send(const std::vector<u64>& ws) {
        if (cfg.mode == 0) {
            size_t i = 0;
            while (i < ws.size()) {
                if (!wait_for([&] { return pad_out(19) == 1; }, 2000000000ULL, "RX_CREDIT_OK")) return;
                size_t n = 1 + (i % 6);                  // bursts of 1..6 words inside the credit
                if (n > ws.size() - i) n = ws.size() - i;
                static const int widths[3] = {8, 4, 1};
                spi_write(std::vector<u64>(ws.begin() + i, ws.begin() + i + n), widths[spi_w++ % 3]);
                i += n;
            }
        } else if (cfg.mode == 1) {
            for (u64 w : ws)
                for (int by = 0; by < 8; by++) txq.push_back((w >> (8 * by)) & 0xFF);
            wait_for([&] { return txq.empty(); }, 20000000000ULL, "ingress drain");
        } else {
            for (u64 w : ws)
                for (int k = 0; k < 4; k++) async_send16((w >> (16 * k)) & 0xFFFF);
        }
    }
    bool recv(size_t n, std::vector<u64>& ws) {
        ws.clear();
        if (cfg.mode == 0) {
            for (size_t i = 0; i < n; i++) {
                if (!wait_for([&] { return pad_out(20) == 1; }, 20000000000ULL, "TX_VALID_IRQ")) return false;
                static const int widths[3] = {4, 8, 1};
                ws.push_back(spi_read_word(widths[spi_w++ % 3]));
            }
        } else {
            if (!wait_for([&] { return rxq.size() >= 8 * n; }, 20000000000ULL, "egress bytes")) return false;
            for (size_t i = 0; i < n; i++) {
                u64 w = 0;
                for (int by = 0; by < 8; by++) {
                    w |= (u64)rxq.front() << (8 * by);
                    rxq.pop_front();
                }
                ws.push_back(w);
            }
        }
        return true;
    }
    bool xfer(const std::vector<u64>& req, size_t nrsp, std::vector<u64>& rsp) {
        send(req);
        return recv(nrsp, rsp);
    }
    int pin_verify_ok() { return pad_out(cfg.mode == 1 ? 6 : 16); }
    int pin_fault() { return pad_out(cfg.mode == 0 ? 17 : cfg.mode == 1 ? 20 : 35); }
    u64 ping_tel(int word = 2) {
        std::vector<u64> r;
        if (!xfer({0x0151ULL}, 5, r)) return 0;
        return r[word];
    }
    bool write_csr(u64 v) {
        std::vector<u64> r;
        if (!xfer({0x0251ULL | (8ULL << 24), v}, 1, r)) return false;
        return r[0] == (0x51ULL | (0x82ULL << 8) | (1ULL << 16));
    }
};

static void check(Sim& s, bool ok, const char* what) {
    printf("  [%s] %s\n", ok ? "ok" : "FAIL", what);
    if (!ok) s.errors++;
}

// -------------------------------------------------------------------- script runner
static int run_script(Sim& s, const char* path) {
    std::ifstream f(path);
    if (!f) {
        printf("cannot open %s\n", path);
        return 1;
    }
    std::string line, title;
    std::vector<u64> req;
    int n_xfer = 0, n_bad = 0;
    u64 words_tx = 0, words_rx = 0;
    while (std::getline(f, line)) {
        std::istringstream ss(line);
        std::string tag, tok;
        ss >> tag;
        if (tag == "#") {
            title = line.substr(2);
        } else if (tag == "TX") {
            req.clear();
            while (ss >> tok) req.push_back(strtoull(tok.c_str(), nullptr, 16));
        } else if (tag == "RX") {
            std::vector<std::string> exp;
            while (ss >> tok) exp.push_back(tok);
            std::vector<u64> rsp;
            u64 t0 = s.t, c0 = s.cc_cycles;
            bool ok = s.xfer(req, exp.size(), rsp);
            int bad = 0;
            for (size_t i = 0; ok && i < exp.size(); i++)
                if (exp[i] != "-" && rsp[i] != strtoull(exp[i].c_str(), nullptr, 16)) {
                    if (!bad) printf("  mismatch word %zu: got %016" PRIx64 " expected %s\n", i, rsp[i], exp[i].c_str());
                    bad++;
                }
            n_xfer++;
            words_tx += req.size();
            words_rx += exp.size();
            if (!ok || bad) {
                n_bad++;
                s.errors++;
            }
            printf("  [%s] %-78s %6.2f ms %8" PRIu64 " clk\n", (!ok || bad) ? "FAIL" : "ok", title.substr(0, 78).c_str(),
                   (s.t - t0) / 1e9, s.cc_cycles - c0);
            fflush(stdout);
            if (!ok) return 1;
        } else if (tag == "PIN") {
            std::string name;
            int v;
            ss >> name >> v;
            s.advance(8 * s.cfg.half_pad);
            int got = name == "VERIFY_OK" ? s.pin_verify_ok() : s.pin_fault();
            if (got != v) {
                printf("  [FAIL] pin %s = %d, expected %d\n", name.c_str(), got, v);
                s.errors++;
            }
        } else if (tag == "FRAMCHK") {
            int slot;
            std::string hex;
            ss >> slot >> hex;
            bool ok = true;
            for (int i = 0; i < 24; i++)
                ok &= s.fram[32 * slot + i] == strtoul(hex.substr(2 * i, 2).c_str(), nullptr, 16);
            if (!ok) {
                printf("  [FAIL] FRAM slot %d record differs from the model\n", slot);
                s.errors++;
            }
        } else if (tag == "FRAMSAVE") {
            memcpy(s.fram_saved, s.fram, sizeof s.fram);
        } else if (tag == "FRAMRESTORE") {
            memcpy(s.fram, s.fram_saved, sizeof s.fram);
        }
    }
    printf("script: %d transactions (%" PRIu64 " request words, %" PRIu64 " response words), %d failed\n", n_xfer, words_tx,
           words_rx, n_bad);
    return n_bad;
}

// -------------------------------------------------------------------- physical scenarios
static const u64 KEYLOAD_HOST[] = {0x51ULL | (0x40ULL << 8) | (1ULL << 16) | (48ULL << 24),
                                   0x1111111111111111ULL, 0x2222222222222222ULL, 3, 4, 5, 6};

static void scenario_clkswitch(Sim& s) {
    printf("scenario: live EXT_CLK_BYPASS switch-over\n");
    std::vector<u64> r;
    // DCRO forced on so its frequency can be read, tap 8, dither +/-3
    check(s, s.write_csr(csr_val(8, 0, 3, 8, 1, 0, 1, 0)), "CSR write (tap 8, dither 3, DCRO on)");
    u64 dcro_half_min = 180 + (8 + 1) * 400 + 2 * 220;
    u64 floor_ps = (dcro_half_min < s.cfg.half_pad ? dcro_half_min : s.cfg.half_pad) * 9 / 10;
    s.cc_min = ~0ULL;
    for (int k = 0; k < 24; k++) {
        s.bypass ^= 1;                                   // strap changes at an arbitrary instant
        s.advance(300000 + 7919 * k);
        u64 tel = s.ping_tel(2);
        int on_pad = (tel >> 28) & 1, on_dcro = (tel >> 29) & 1;
        if (on_pad == on_dcro || on_pad != s.bypass) {
            printf("  switch %d: pad_on=%d dcro_on=%d bypass=%d\n", k, on_pad, on_dcro, s.bypass);
            s.errors++;
        }
    }
    printf("  minimum clk_core pulse width over 24 switch-overs: %" PRIu64 " ps (floor %" PRIu64 " ps)\n", s.cc_min, floor_ps);
    check(s, s.cc_min >= floor_ps, "no runt pulse on clk_core");
    check(s, s.xfer({0x0151ULL}, 5, r) && r[1] == 0x3831494E47415351ULL, "link alive after the switch-overs");
}

// SPI only: a read aborted mid-word loses nothing, and a burst read pops word by word
static void scenario_spiburst(Sim& s) {
    printf("scenario: SPI aborted read and burst read\n");
    s.send({0x0151ULL});                                 // PING: five response words
    s.wait_for([&] { return s.pad_out(20) == 1; }, 2000000000ULL, "TX_VALID_IRQ");
    s.advance(400 * s.cfg.half_pad);                     // let the four-word FIFO fill
    // abort after 3 of 8 beats (x8)
    s.spi_cmd(0x82);
    for (int i = 0; i < 8; i++) s.drv[i] = false;
    for (int i = 0; i < 8 + 3; i++) s.sck_pulse();
    s.spi_end();
    std::vector<u64> ws, tail;
    s.spi_read(4, 4, ws);                                // four words in one CS_N frame
    check(s, ws[0] == (0x51ULL | (0x81ULL << 8) | (1ULL << 16) | (32ULL << 24)), "header intact after the aborted read");
    check(s, ws[1] == 0x3831494E47415351ULL, "second word of the burst is the chip ID");
    check(s, s.recv(1, tail), "fifth word arrives after the burst");
    u64 tel = s.ping_tel(2);
    check(s, !((tel >> 37) & 3), "no overrun / underrun");
}

static bool key_valid(Sim& s) { return (s.ping_tel(2) >> 42) & 1; }

static void scenario_tamper(Sim& s) {
    printf("scenario: TAMPER_ZEROIZE_N\n");
    std::vector<u64> r;
    std::vector<u64> kl(KEYLOAD_HOST, KEYLOAD_HOST + 7);
    check(s, s.xfer(kl, 1, r) && (r[0] >> 16 & 0x81) == 1, "key load");
    check(s, key_valid(s), "key_valid set");
    s.drv[26] = true;
    s.val[26] = 0;                                       // tamper pin low for 3 ns, asynchronous
    s.advance(3000);
    s.drv[26] = false;
    s.advance(20 * s.cfg.half_pad);
    check(s, s.pin_fault() == 1, "FAULT pin raised");
    s.reset();
    check(s, !key_valid(s), "key gone after reset");
    check(s, s.xfer({0x51ULL | (0x42ULL << 8) | (8ULL << 24), 0x1234}, 1, r) && (r[0] >> 48) == 4, "PRF_msg refused (no key)");
}

static void scenario_glitch(Sim& s) {
    printf("scenario: clock-glitch canary\n");
    std::vector<u64> r;
    std::vector<u64> kl(KEYLOAD_HOST, KEYLOAD_HOST + 7);
    // replica tap 5: 24 stages * 2 * 180 ps = 8.64 ns against a 20 ns clock; canary armed
    check(s, s.write_csr(csr_val(31, 0, 0, 5, 1, 1, 0, 0)), "CSR write (canary armed)");
    check(s, s.xfer(kl, 1, r) && (r[0] >> 16 & 0x81) == 1, "key load");
    check(s, key_valid(s) && s.pin_fault() == 0, "key_valid set, no fault at nominal clock");
    s.glitch_half = 3000;                                // one 6 ns clock period
    s.glitch_req = 1;
    s.advance(40 * s.cfg.half_pad);
    check(s, s.pin_fault() == 1, "FAULT pin raised by the glitch");
    s.reset();
    u64 tel = s.ping_tel(2);
    check(s, !((tel >> 42) & 1), "key gone after reset");
}

static void scenario_trng(Sim& s) {
    printf("scenario: TRNG health and TRNG key load\n");
    std::vector<u64> r;
    check(s, s.write_csr(CSR_DEFAULT), "CSR write (TRNG on)");
    bool ok = false;
    for (int k = 0; k < 60 && !ok; k++) {
        s.advance(20000000);
        ok = (s.ping_tel(2) >> 36) & 1;
    }
    check(s, ok, "TRNG start-up window passed (RCT, APT)");
    u64 w1 = s.ping_tel(4);
    s.advance(40000000);
    u64 w2 = s.ping_tel(4);
    printf("  raw TRNG words: %016" PRIx64 " %016" PRIx64 "\n", w1, w2);
    check(s, w1 != w2 && w1 != 0 && ~w1 != 0, "raw words differ");
    // TRNG key load with two personalization words, then a keyed operation
    check(s, s.xfer({0x51ULL | (0x40ULL << 8) | (32ULL << 24), 7, 8, 0xAAAA, 0xBBBB}, 1, r) && (r[0] >> 16 & 0x81) == 1,
          "key load from the TRNG");
    check(s, key_valid(s), "key_valid set");
    check(s, s.xfer({0x51ULL | (0x42ULL << 8) | (8ULL << 24), 0x1234}, 3, r) && (r[0] >> 16 & 0x81) == 1 && (r[1] | r[2]) != 0,
          "PRF_msg answers under the generated key");
    u64 tel = s.ping_tel(2);
    check(s, !((tel >> 34) & 3), "no RCT / APT failure latched");
}

static void scenario_loops(Sim& s) {
    printf("scenario: DCRO loops (core clock = DCRO)\n");
    // replica loop: tap 5 replica 8.64 ns, guard 4 stages (+1.44 ns)
    check(s, s.write_csr(csr_val(31, 1, 0, 5, 1, 0, 0, 0)), "CSR write (replica loop)");
    s.advance(900000000);
    u64 tel = s.ping_tel(2);
    int tap = (tel >> 16) & 31;
    u64 period = 2 * (180 + (tap + 1) * 400 + 2 * 220);
    printf("  replica loop: tap %d, DCRO period %" PRIu64 " ps, late1 %d late2 %d\n", tap, period, (int)(tel >> 26 & 1), (int)(tel >> 27 & 1));
    check(s, period >= 8640 && period <= 8640 + 1440 + 800 && !((tel >> 26) & 1), "period locked inside the guard band");
    // frequency lock: 512 clk_pad cycles = 10.24 us; target 900 cycles -> 11.4 ns
    check(s, s.write_csr(csr_val(31, 2, 0, 5, 1, 0, 0, 0, 900)), "CSR write (frequency lock, target 900)");
    s.advance(900000000);
    tel = s.ping_tel(2);
    int cnt = tel & 0xFFFF;
    printf("  frequency lock: count %d, tap %d\n", cnt, (int)(tel >> 16 & 31));
    check(s, cnt > 900 - 70 && cnt < 900 + 70, "count within one tap step of the target");
    // dither: the effective tap moves, the base does not
    check(s, s.write_csr(csr_val(12, 0, 3, 5, 1, 0, 0, 0)), "CSR write (manual tap 12, dither 3)");
    int lo = 99, hi = 0;
    for (int k = 0; k < 12; k++) {
        tel = s.ping_tel(2);
        int e = (tel >> 21) & 31;
        if (e < lo) lo = e;
        if (e > hi) hi = e;
    }
    printf("  dither: effective tap %d..%d around base 12\n", lo, hi);
    check(s, lo >= 12 && hi <= 18 && hi > lo, "effective tap dithers upward only");
}

int main(int argc, char** argv) {
    if (argc < 3) {
        printf("usage: %s <script> <config> [scenario]\n", argv[0]);
        return 2;
    }
    Sim s;
    s.ctx = new VerilatedContext;
    s.ctx->commandArgs(argc, argv);
    s.top = new Vtb_top{s.ctx};
    std::string cfgname = argv[2], scen = argc > 3 ? argv[3] : "script";
    Cfg& c = s.cfg;
    c.csr = csr_val(31, 0, 0, 8, 1, 0, 0, 0);             // rings off unless a test needs them
    if (cfgname == "spi") { c.mode = 0; c.io_half = 7300; }
    else if (cfgname == "ss_023") { c.mode = 1; c.io_half = 43478; }      // RX_CLK = 0.23 x clk_core
    else if (cfgname == "ss_100") { c.mode = 1; c.io_half = 10013; }      // 1.0 x, drifting phase
    else if (cfgname == "ss_370") { c.mode = 1; c.io_half = 2703; }       // 3.7 x
    else if (cfgname == "ss_dcro") { c.mode = 1; c.bypass = 0; c.io_half = 6100; c.csr = csr_val(9, 0, 3, 8, 1, 0, 0, 0); }
    else if (cfgname == "async") { c.mode = 2; c.io_half = 900; }
    else if (cfgname == "async_slow") { c.mode = 2; c.io_half = 61000; }
    else { printf("unknown config %s\n", cfgname.c_str()); return 2; }
    if (scen == "loops") c.bypass = 0;
    s.bypass = c.bypass;
    s.next_pad = c.half_pad;
    s.drive();
    s.top->eval();
    s.reset();
    printf("config %s: IO_MODE %d, EXT_CLK_BYPASS %d, scenario %s\n", cfgname.c_str(), c.mode, c.bypass, scen.c_str());
    if (!s.write_csr(c.csr)) {
        printf("initial CSR write failed\n");
        s.errors++;
    }
    if (scen == "script") run_script(s, argv[1]);
    else if (scen == "clkswitch") scenario_clkswitch(s);
    else if (scen == "tamper") scenario_tamper(s);
    else if (scen == "glitch") scenario_glitch(s);
    else if (scen == "trng") scenario_trng(s);
    else if (scen == "loops") scenario_loops(s);
    else if (scen == "spiburst") scenario_spiburst(s);
    u64 tel = s.ping_tel(2);
    printf("final telemetry %016" PRIx64 ": rx_overrun %d tx_underrun %d; pad contention events %" PRIu64
           "; min clk_core pulse %" PRIu64 " ps; %" PRIu64 " core cycles; FRAM byte writes %" PRIu64 "\n",
           tel, (int)(tel >> 38 & 1), (int)(tel >> 37 & 1), s.contention, s.cc_min, s.cc_cycles, s.fram_writes);
    if (scen == "script" && ((tel >> 37) & 3)) {
        printf("FAIL: link overrun / underrun flagged\n");
        s.errors++;
    }
    if (s.cc_min < 1500) {                               // shortest legal DCRO half period is 2220 ps
        printf("FAIL: runt pulse on clk_core (%" PRIu64 " ps)\n", s.cc_min);
        s.errors++;
    }
    if (s.contention) {
        printf("FAIL: testbench and chip drove a pad at the same time\n");
        s.errors++;
    }
    printf("%s: %s/%s %s (%d errors)\n", argv[0], cfgname.c_str(), scen.c_str(), s.errors ? "FAILED" : "PASSED", s.errors);
    s.top->final();
    return s.errors != 0;
}
