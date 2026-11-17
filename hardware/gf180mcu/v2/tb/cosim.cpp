// Co-simulation of the Dregg-180 v2 RTL against a trace recorded from the Python model (tb/record.py).
//
//   cosim <tracedir> [--shard i n] [--verbose] [--seed s]
//
// For every recorded transaction the bench brings the RTL to the model's state before it (normally by
// simply having run the previous transactions; see "restore" below), sends the request words, and then
// requires, with no tolerance:
//   response words          equal, word for word (on a control fault: a prefix of what the model had)
//   clocks                  cmd_active && !link_wait clocks == the interpreter's cycle count
//   control fault           raised if and only if the model raised one
//   register file, flags    every row and every flag after the transaction equal to the model's
//   FRAM transfers          the SPI frames on the FRAM pins carry, in order, exactly the transfers the model's
//                           FRAM unit made: same slot and direction, same words written; words read are the
//                           words the model's (possibly faulty) memory returned
//   pins                    VERIFY_OK and FAULT
//   owner / nonce stand-ins the words the RTL presents to the owner interface equal the model's
// It also requires zero failed checks in dregg_core, and zero lockstep mismatches against the unmodified
// qsag_keccak_serial and qsag_anchor_spi.
//
// Restore. The model's tests put keys into key rows directly and build new chips mid-test. When the
// recorder marks a transaction's start state as placed by the test (poked), or the transaction belongs
// to another chip than the one last simulated, the bench resets the RTL, loads that chip's ROM, lets it
// boot, and places the state through the test-only backdoor. In every other case the RTL's state must
// already equal the model's start state, and a difference is an error.
#include <algorithm>
#include <cstdarg>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "Vdregg_cosim_tb.h"
#include "verilated.h"

typedef uint64_t u64;

struct Snap {
    u64 flags[10];              // key_valid key_attr fmac fanchor fcontrol verify_ok dev_ok nonce_valid nonce0 nonce1
    std::vector<u64> rows;
};
struct Own { bool ok; u64 w[8]; };
struct Xfer {
    int cid = 0; bool fault = false; u64 cycles = 0; bool poked = false;
    std::vector<u64> q, r, ent;
    std::vector<std::string> fram;      // the model's FRAM transfers: s<slot><r|w>, r<word>, w<word>
    Snap s0, s1;
    std::vector<Own> own;
};
struct ChipDef { int rom = 0; bool puf = false; u64 secret[4] = {0, 0, 0, 0}; bool ent = false, own = false; };
struct Rom { u64 len = 0, used = 0; std::vector<u64> words, consts; std::vector<u64> disp; };

static std::vector<u64> hexwords(std::istringstream& is) {
    std::vector<u64> v; std::string t;
    while (is >> t) { if (t == "|") break; v.push_back(strtoull(t.c_str(), nullptr, 16)); }
    return v;
}

struct Bench {
    std::unique_ptr<VerilatedContext> ctx;
    std::unique_ptr<Vdregg_cosim_tb> top;
    std::string dir;
    std::map<int, Rom> roms;
    std::map<int, ChipDef> chips;
    int cur_chip = -1, cur_rom = -1;
    bool fc_unsynced = false;
    bool verbose = false;
    u64 nrows = 0, t_nonce = 8, t_auth = 3900000;
    // FRAM slave, scripted by the model's transfers of the current transaction
    const std::vector<std::string>* f_ops = nullptr;
    size_t f_i = 0;
    int f_bad = 0;
    std::vector<uint8_t> f_rd;          // bytes this read frame serves
    size_t f_rdi = 0;
    u64 f_wacc = 0; int f_wn = 0;
    int f_prev_sck = 0, f_prev_cs = 1, f_bits = 0, f_bytes = 0, f_addr = 0, f_cmd = 0, f_wel = 0;
    uint8_t f_sh = 0, f_out = 0;
    void fram_bad(const char* what) { f_bad++; err("FRAM: %s (transfer %zu)", what, f_i); }
    void fram_open(bool write) {
        char want[8];
        snprintf(want, sizeof want, "s%d%c", f_addr == 32 ? 1 : 0, write ? 'w' : 'r');
        if ((f_addr != 0 && f_addr != 32) || !f_ops || f_i >= f_ops->size() || (*f_ops)[f_i] != want) { fram_bad("frame the model did not open"); return; }
        f_i++;
        f_rd.clear(); f_rdi = 0; f_wacc = 0; f_wn = 0;
        if (!write)
            while (f_i < f_ops->size() && (*f_ops)[f_i][0] == 'r') {
                u64 v = strtoull((*f_ops)[f_i].c_str() + 1, nullptr, 16);
                for (int b = 0; b < 8; b++) f_rd.push_back((uint8_t)(v >> (8 * b)));
                f_i++;
            }
    }
    void fram_wbyte(uint8_t b) {
        f_wacc |= (u64)b << (8 * f_wn);
        if (++f_wn == 8) {
            if (!f_ops || f_i >= f_ops->size() || (*f_ops)[f_i][0] != 'w' || strtoull((*f_ops)[f_i].c_str() + 1, nullptr, 16) != f_wacc)
                fram_bad("word written differs from the model's");
            else f_i++;
            f_wacc = 0; f_wn = 0;
        }
    }
    // statistics
    u64 n_x = 0, n_rsp_ok = 0, n_cyc_ok = 0, n_cyc_cmp = 0, n_state_ok = 0, n_fault_x = 0, n_fault_ok = 0, n_fram_ok = 0;
    u64 n_restore = 0, n_poke = 0, n_cont = 0, n_cont_bad = 0, errors = 0, total_cycles = 0, n_own = 0, n_own_bad = 0;
    u64 w_din = 0, w_other = 0, n_stall = 0, n_pin_bad = 0;

    void err(const char* fmt, ...) {
        errors++;
        if (errors > 60) return;
        va_list ap; va_start(ap, fmt); printf("  ERROR: "); vprintf(fmt, ap); printf("\n"); va_end(ap);
    }

    // ---------------------------------------------------------------- clock
    void fram_step() {
        int cs = top->fram_cs_n, sck = top->fram_sck, mosi = top->fram_mosi;
        if (cs) {
            if (!f_prev_cs && f_cmd == 0x02) f_wel = 0;      // a write frame clears the write-enable latch
            f_bits = 0; f_bytes = 0; f_cmd = 0;
            top->fram_miso = 0;
        } else {
            if (sck && !f_prev_sck) {                        // rising: sample
                f_sh = (uint8_t)((f_sh << 1) | mosi);
                if (++f_bits == 8) {
                    f_bits = 0;
                    if (f_bytes == 0) { f_cmd = f_sh; if (f_cmd == 0x06) f_wel = 1; }
                    else if (f_bytes == 1) f_addr = f_sh << 8;
                    else if (f_bytes == 2) {
                        f_addr |= f_sh;
                        if (f_cmd == 0x03) fram_open(false);
                        else if (f_cmd == 0x02 && f_wel) fram_open(true);
                        else fram_bad("unknown command or write without WREN");
                    } else if (f_cmd == 0x02 && f_wel) fram_wbyte(f_sh);
                    f_bytes++;
                    if (f_cmd == 0x03 && f_bytes >= 3) f_out = f_rdi < f_rd.size() ? f_rd[f_rdi++] : 0;
                }
            }
            if (!sck && f_prev_sck) {                        // falling: drive the next bit
                if (f_cmd == 0x03 && f_bytes >= 3) { top->fram_miso = (f_out >> 7) & 1; f_out = (uint8_t)(f_out << 1); }
            }
        }
        f_prev_sck = sck; f_prev_cs = cs;
    }
    void edge() {
        top->clk = 1; top->eval();
        fram_step();
        top->clk = 0; top->eval();
        total_cycles++;
    }
    void idle_inputs() {
        top->in_valid = 0; top->in_first = 0; top->in_data = 0; top->out_take = 1;
        top->ent_valid = 0; top->own_done = 0; top->own_ok = 0;
        top->ld_we = 0; top->bd_rf_we = 0; top->bd_fl_we = 0;
    }

    // ---------------------------------------------------------------- ROM, reset, state
    void load_rom(int k) {
        const Rom& r = roms.at(k);
        auto wr = [&](int sel, u64 addr, u64 data) {
            top->ld_we = 1; top->ld_sel = sel; top->ld_addr = addr; top->ld_data = data; top->eval(); edge();
        };
        wr(3, 0, r.len | (r.used << 12));
        for (size_t i = 0; i < r.words.size(); i++) wr(0, i, r.words[i]);
        for (size_t i = 0; i < r.consts.size(); i++) wr(1, i, r.consts[i]);
        for (u64 d : r.disp) wr(2, d >> 16, d & 0xFFFF);
        top->ld_we = 0; top->eval();
        cur_rom = k;
    }
    void por(int cid) {
        const ChipDef& c = chips.at(cid);
        idle_inputs();
        // a falling edge on the reset pad every time: the behavioural tamper latch of qsag_cells is cleared
        // by the edge (the gf180 cell by the level), and the first reset starts from random storage
        top->tamper_n = 1; top->por_n = 1; top->eval();
        top->por_n = 0; top->eval();
        for (int i = 0; i < 3; i++) edge();
        if (cur_rom != c.rom) load_rom(c.rom);
        top->puf_present = c.puf;
        for (int i = 0; i < 4; i++) top->puf_secret[2 * i] = (uint32_t)c.secret[i], top->puf_secret[2 * i + 1] = (uint32_t)(c.secret[i] >> 32);
        top->ent_present = c.ent;
        top->eval();
        top->por_n = 1; top->eval();
        int n = 0;
        while (!top->ready && n++ < 200) edge();
        if (!top->ready) err("chip %d did not boot", cid);
        edge();                                          // the last key row closes
        cur_chip = cid;
        fc_unsynced = false;
    }
    void wait_ready() {
        int n = 0;
        do { idle_inputs(); top->eval(); edge(); } while (!top->ready && n++ < 200);
        if (!top->ready) err("no reboot after a control fault");
        edge();
    }
    Snap dump() {
        Snap s;
        for (u64 r = 0; r < nrows; r++) { top->dump_row = r; top->eval(); s.rows.push_back(top->dump_data); }
        u64 f = top->dump_flags;
        s.flags[0] = f & 1; s.flags[1] = (f >> 4) & 15; s.flags[2] = (f >> 1) & 1; s.flags[3] = (f >> 2) & 1;
        s.flags[4] = 0; s.flags[5] = (f >> 3) & 1; s.flags[6] = top->dump_dev_ok; s.flags[7] = (f >> 8) & 1;
        s.flags[8] = (u64)top->dump_nonce[0] | ((u64)top->dump_nonce[1] << 32);
        s.flags[9] = (u64)top->dump_nonce[2] | ((u64)top->dump_nonce[3] << 32);
        if (!s.flags[7]) s.flags[8] = s.flags[9] = 0;    // the model reports no nonce as (0, 0)
        return s;
    }
    // differences between the RTL state and a model snapshot; flag 4 (fault_control) is compared on the pin
    int diff(const Snap& a, const Snap& m, bool print) {
        int d = 0;
        for (u64 r = 0; r < nrows; r++)
            if (a.rows[r] != m.rows[r]) { if (print && d < 6) printf("    row %llu: rtl %016llx model %016llx\n", (unsigned long long)r, (unsigned long long)a.rows[r], (unsigned long long)m.rows[r]); d++; }
        static const char* nm[10] = {"key_valid", "key_attr", "fault_mac", "fault_anchor", "fault_control", "verify_ok", "dev_ok", "nonce_valid", "nonce0", "nonce1"};
        for (int i = 0; i < 10; i++)
            if (i != 4 && a.flags[i] != m.flags[i]) { if (print && d < 12) printf("    %s: rtl %llx model %llx\n", nm[i], (unsigned long long)a.flags[i], (unsigned long long)m.flags[i]); d++; }
        return d;
    }
    void place(const Snap& m) {
        Snap a = dump();
        for (u64 r = 0; r < nrows; r++)
            if (a.rows[r] != m.rows[r]) {
                top->bd_row = r; top->bd_data = m.rows[r]; top->bd_rf_we = 1; top->eval();
                top->bd_rf_we = 0; top->eval();
            }
        top->bd_flags = (m.flags[0] & 1) | ((m.flags[2] & 1) << 1) | ((m.flags[3] & 1) << 2) | ((m.flags[5] & 1) << 3)
                      | ((m.flags[1] & 15) << 4) | ((m.flags[7] & 1) << 8);
        top->bd_nonce[0] = (uint32_t)m.flags[8]; top->bd_nonce[1] = (uint32_t)(m.flags[8] >> 32);
        top->bd_nonce[2] = (uint32_t)m.flags[9]; top->bd_nonce[3] = (uint32_t)(m.flags[9] >> 32);
        top->bd_fl_we = 1; top->eval(); edge();
        top->bd_fl_we = 0; top->eval();
        if (m.flags[4]) fc_unsynced = true;              // fault_control cannot be placed: the FAULT pin is not compared
        if (diff(dump(), m, true)) err("backdoor placement did not take");
    }

    // ---------------------------------------------------------------- one transaction
    void run(const Xfer& x, u64 index) {
        n_x++;
        if (x.cid != cur_chip) {
            por(x.cid);
            if (diff(dump(), x.s0, false)) { place(x.s0); n_restore++; }
        } else if (x.poked) {
            place(x.s0); n_poke++;
        } else {
            n_cont++;
            if (diff(dump(), x.s0, true)) { n_cont_bad++; err("transaction %llu: RTL state before it differs from the model's", (unsigned long long)index); place(x.s0); }
        }
        if (x.s0.flags[4] != 0 && !fc_unsynced && !top->fault) fc_unsynced = true;
        f_ops = &x.fram; f_i = 0; f_bad = 0;
        const ChipDef& c = chips.at(x.cid);

        std::vector<u64> got;
        size_t qi = 0, ei = 0, oi = 0;
        bool started = false, faulted = false, done = false;
        u64 counted = 0, raw = 0;
        long ent_k = -1, own_k = -1;                     // counted clocks since the request, -1: none pending
        u64 own_w[8] = {0}; int own_seen = 0;
        u64 limit = x.cycles * 2 + 45000000ULL;
        bool own_reply = false;
        while (!done) {
            top->in_valid = qi < x.q.size();
            top->in_data = qi < x.q.size() ? x.q[qi] : 0;
            top->in_first = (qi == 0);
            top->out_take = 1;
            top->ent_valid = (ent_k >= 0 && (u64)ent_k == t_nonce);
            if (top->ent_valid) {
                u64 a = ei < x.ent.size() ? x.ent[ei] : 0, b = ei + 1 < x.ent.size() ? x.ent[ei + 1] : 0;
                if (ei + 1 >= x.ent.size()) err("transaction %llu: more nonce draws than the model made", (unsigned long long)index);
                ei += 2;
                top->ent_data[0] = (uint32_t)a; top->ent_data[1] = (uint32_t)(a >> 32);
                top->ent_data[2] = (uint32_t)b; top->ent_data[3] = (uint32_t)(b >> 32);
            }
            top->own_done = (own_k >= 0 && (u64)own_k == t_auth);
            top->own_ok = own_reply;
            top->eval();
            // this clock
            if (started && !top->cmd_active && !faulted) { done = true; break; }
            if (top->cmd_active) { started = true; raw++; if (!top->link_wait) counted++; }
            if (top->stall) n_stall++;
            if (top->link_wait) { if (qi >= x.q.size() || true) w_other++; }
            if (top->fault_now) faulted = true;
            if (top->in_valid && top->in_take) qi++;
            if (top->out_valid) got.push_back(top->out_data);
            bool lw = top->link_wait;
            if (ent_k >= 0) { if (top->ent_valid) ent_k = -1; else if (!lw) ent_k++; }
            if (own_k >= 0) {
                if (top->own_valid) { own_w[top->own_idx] = top->own_data; own_seen++; }
                if (own_seen == 8) {                     // the whole statement has been presented: decide the reply
                    own_seen = 9;
                    n_own++;
                    if (!c.own) own_reply = false;
                    else if (oi < x.own.size()) {
                        const Own& o = x.own[oi++];
                        bool same = true;
                        for (int i = 0; i < 8; i++) same = same && own_w[i] == o.w[i];
                        if (!same) { n_own_bad++; err("transaction %llu: owner statement differs from the model's", (unsigned long long)index); }
                        own_reply = o.ok;
                    } else own_reply = true;             // the model refused before asking the owner: the RTL must too
                }
                if (top->own_done) own_k = -1; else if (!lw) own_k++;
            }
            if (top->ent_req) ent_k = 1;
            if (top->own_start) { own_k = 1; own_seen = 0; own_reply = false; }
            edge();
            if (faulted) { qi = x.q.size(); idle_inputs(); wait_ready(); done = true; }
            if (raw > limit) { err("transaction %llu: no end after %llu clocks (pc %u)", (unsigned long long)index, (unsigned long long)raw, (unsigned)top->pc); done = true; cur_chip = -1; }
        }
        idle_inputs(); top->eval();
        if (qi < x.q.size() && !faulted) err("transaction %llu: %zu request words not consumed", (unsigned long long)index, x.q.size() - qi);

        // ---- comparisons
        bool ok = true;
        n_fault_x += x.fault;
        if (faulted != x.fault) {
            ok = false;
            err("transaction %llu: control fault rtl %d model %d (rule term %u, pc %u)", (unsigned long long)index, faulted, x.fault, (unsigned)top->fault_why, (unsigned)top->pc);
        } else if (x.fault) n_fault_ok++;
        bool rsp_ok;
        if (x.fault) rsp_ok = got.size() <= x.r.size() && std::equal(got.begin(), got.end(), x.r.begin());
        else rsp_ok = got == x.r;
        if (rsp_ok) n_rsp_ok++;
        else {
            ok = false;
            err("transaction %llu (op %02llx): response differs: rtl %zu words, model %zu", (unsigned long long)index, (unsigned long long)((x.q[0] >> 8) & 0xFF), got.size(), x.r.size());
            for (size_t i = 0; i < got.size() && i < x.r.size(); i++)
                if (got[i] != x.r[i]) { printf("    word %zu: rtl %016llx model %016llx\n", i, (unsigned long long)got[i], (unsigned long long)x.r[i]); break; }
        }
        if (!x.fault && !faulted) {
            n_cyc_cmp++;
            if (counted == x.cycles) n_cyc_ok++;
            else { ok = false; err("transaction %llu (op %02llx): clocks rtl %llu model %llu", (unsigned long long)index, (unsigned long long)((x.q[0] >> 8) & 0xFF), (unsigned long long)counted, (unsigned long long)x.cycles); }
        }
        Snap post = dump();
        if (diff(post, x.s1, ok)) { ok = false; err("transaction %llu: state after it differs", (unsigned long long)index); }
        else n_state_ok++;
        if (f_bad == 0 && f_i == x.fram.size()) n_fram_ok++;
        else { ok = false; err("transaction %llu: FRAM transfers differ: %zu of the model's %zu seen", (unsigned long long)index, f_i, x.fram.size()); }
        f_ops = nullptr;
        if (x.s1.flags[4] && !x.s0.flags[4]) fc_unsynced = false;      // a fresh control fault: both have it now
        bool pin_fault = x.s1.flags[2] | x.s1.flags[3] | x.s1.flags[4];
        if (top->verify_ok != x.s1.flags[5] || (!fc_unsynced && top->fault != pin_fault)) {
            n_pin_bad++; ok = false;
            err("transaction %llu: pins VERIFY_OK %d/%llu FAULT %d/%d", (unsigned long long)index, top->verify_ok, (unsigned long long)x.s1.flags[5], top->fault, pin_fault);
        }
        if (ei != x.ent.size()) { ok = false; err("transaction %llu: nonce draws rtl %zu model %zu", (unsigned long long)index, ei / 2, x.ent.size() / 2); }
        if (oi != x.own.size()) { ok = false; err("transaction %llu: owner calls rtl %zu model %zu", (unsigned long long)index, oi, x.own.size()); }
        if (verbose) printf("  [%s] x%llu chip %d op %02llx: %zu words, %llu clocks (raw %llu)%s\n", ok ? "ok" : "BAD", (unsigned long long)index, x.cid,
                            (unsigned long long)((x.q[0] >> 8) & 0xFF), got.size(), (unsigned long long)counted, (unsigned long long)raw, x.fault ? ", control fault" : "");
        if (!ok) cur_chip = -1;                          // resynchronise from the model's next start state
    }
};

int main(int argc, char** argv) {
    if (argc < 2) { printf("usage: cosim <tracedir> [--shard i n] [--verbose]\n"); return 2; }
    Bench b;
    b.dir = argv[1];
    int shard = 0, nshard = 1;
    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "--shard")) { shard = atoi(argv[i + 1]); nshard = atoi(argv[i + 2]); i += 2; }
        else if (!strcmp(argv[i], "--verbose")) b.verbose = true;
    }
    b.ctx.reset(new VerilatedContext);
    b.ctx->commandArgs(argc, argv);
    b.top.reset(new Vdregg_cosim_tb(b.ctx.get()));
    b.top->clk = 0; b.top->por_n = 0; b.top->tamper_n = 1; b.top->fram_miso = 0;
    b.top->dump_row = 0; b.top->bd_row = 0; b.top->bd_data = 0; b.top->bd_flags = 0;
    b.top->puf_present = 0; b.top->ent_present = 0;
    b.idle_inputs();
    b.top->por_n = 1;                                   // no reset yet: what does the storage start as?
    b.top->eval();
    {
        int nz = 0;
        for (unsigned r = 0; r < b.top->nrows_o; r++) { b.top->dump_row = r; b.top->eval(); nz += b.top->dump_data != 0; }
        printf("before the first reset: %d of %u rows non-zero, hold register %016llx, flags %03x\n", nz, (unsigned)b.top->nrows_o,
               (unsigned long long)b.top->dump_h, (unsigned)b.top->dump_flags);
    }

    std::ifstream in(b.dir + "/trace.txt");
    if (!in) { printf("cannot open %s/trace.txt\n", b.dir.c_str()); return 2; }
    std::string line;
    Xfer x; bool have = false; u64 index = 0;
    std::string scenario = "-";
    std::map<std::string, u64> per_scen, per_scen_bad;
    auto flush = [&]() {
        if (!have) return;
        have = false;
        index++;
        if (x.cid % nshard != shard) return;
        u64 e0 = b.errors;
        b.run(x, index);
        per_scen[scenario]++;
        if (b.errors != e0) per_scen_bad[scenario]++;
    };
    while (std::getline(in, line)) {
        std::istringstream is(line);
        std::string tag; is >> tag;
        if (tag == "MODEL") {
            std::string k; u64 v;
            while (is >> k >> v) {
                if (k == "rows") b.nrows = v;
                if (k == "nonce_draw") b.t_nonce = v;
                if (k == "auth_verify") b.t_auth = v;
                if (k == "key0" && v != b.top->key0_o) { printf("row map mismatch: model key0 %llu, RTL %u\n", (unsigned long long)v, (unsigned)b.top->key0_o); return 2; }
            }
            if (b.nrows != b.top->nrows_o) { printf("row map mismatch: model %llu rows, RTL %u\n", (unsigned long long)b.nrows, (unsigned)b.top->nrows_o); return 2; }
        } else if (tag == "SCENARIO") { flush(); is >> scenario; }
        else if (tag == "CHIP") {
            flush();
            int cid; std::string k, v; ChipDef c;
            is >> cid;
            while (is >> k >> v) {
                if (k == "rom") c.rom = atoi(v.c_str());
                if (k == "ent") c.ent = v == "1";
                if (k == "own") c.own = v == "1";
                if (k == "puf" && v != "-") {
                    c.puf = true;                         // 64 hex digits, word 3 first
                    for (int i = 0; i < 4; i++) c.secret[3 - i] = strtoull(v.substr(16 * i, 16).c_str(), nullptr, 16);
                }
            }
            b.chips[cid] = c;
            if (!b.roms.count(c.rom)) {
                std::ifstream rf(b.dir + "/rom_" + std::to_string(c.rom) + ".txt");
                Rom r; std::string l;
                while (std::getline(rf, l)) {
                    std::istringstream rs(l); std::string t; rs >> t;
                    if (t == "LEN") { std::string u; rs >> r.len >> u >> r.used; }
                    else if (t == "W") r.words = hexwords(rs);
                    else if (t == "C") r.consts = hexwords(rs);
                    else if (t == "D") {
                        std::string e;
                        while (rs >> e) {
                            unsigned op, addr, cls;
                            sscanf(e.c_str(), "%x:%x:%x", &op, &addr, &cls);
                            r.disp.push_back(((u64)op << 16) | (1u << 13) | (cls << 11) | addr);
                        }
                    }
                }
                b.roms[c.rom] = r;
            }
        } else if (tag == "POR") {
            flush();
            int cid; is >> cid;
            if (cid % nshard == shard && cid == b.cur_chip) b.por(cid);     // another chip is restored when its turn comes
        } else if (tag == "X") {
            flush();
            x = Xfer(); have = true;
            int f, p; is >> x.cid >> f >> x.cycles >> p; x.fault = f; x.poked = p;
        } else if (tag == "Q") x.q = hexwords(is);
        else if (tag == "R") x.r = hexwords(is);
        else if (tag == "M") { std::string tkn; while (is >> tkn) x.fram.push_back(tkn); }
        else if (tag == "S0" || tag == "S1") {
            Snap& s = tag == "S0" ? x.s0 : x.s1;
            std::vector<u64> f = hexwords(is);
            for (int i = 0; i < 10; i++) s.flags[i] = f[i];
            s.rows = hexwords(is);
        } else if (tag == "E") x.ent = hexwords(is);
        else if (tag == "O") {
            std::vector<u64> v = hexwords(is);
            for (size_t i = 0; i + 9 <= v.size(); i += 9) { Own o; o.ok = v[i]; for (int j = 0; j < 8; j++) o.w[j] = v[i + 1 + j]; x.own.push_back(o); }
        } else if (tag == "END") flush();
    }
    flush();
    b.top->final();
    u64 asserts = b.top->assert_count;
    printf("co-simulation, shard %d of %d\n", shard, nshard);
    for (auto& kv : per_scen) printf("  scenario %-8s %6llu transactions, %llu with an error\n", kv.first.c_str(), (unsigned long long)kv.second, (unsigned long long)per_scen_bad[kv.first]);
    printf("  transactions            %llu\n", (unsigned long long)b.n_x);
    printf("  responses equal         %llu\n", (unsigned long long)b.n_rsp_ok);
    printf("  clock counts equal      %llu of %llu compared\n", (unsigned long long)b.n_cyc_ok, (unsigned long long)b.n_cyc_cmp);
    printf("  control faults agree    %llu of %llu\n", (unsigned long long)b.n_fault_ok, (unsigned long long)b.n_fault_x);
    printf("  end states equal        %llu\n", (unsigned long long)b.n_state_ok);
    printf("  FRAM transfers equal    %llu\n", (unsigned long long)b.n_fram_ok);
    printf("  start state: continued and equal %llu, continued and different %llu, placed after a test's own placement %llu, placed after a chip change %llu\n",
           (unsigned long long)(b.n_cont - b.n_cont_bad), (unsigned long long)b.n_cont_bad, (unsigned long long)b.n_poke, (unsigned long long)b.n_restore);
    printf("  owner statements        %llu presented, %llu different\n", (unsigned long long)b.n_own, (unsigned long long)b.n_own_bad);
    printf("  two-phase stalls %llu, link-wait clocks %llu, clocks simulated %llu\n", (unsigned long long)b.n_stall, (unsigned long long)b.w_other, (unsigned long long)b.total_cycles);
    printf("  failed core checks      %llu\n", (unsigned long long)asserts);
    printf("  lockstep mismatch       %d\n", (int)b.top->lock_err);
    bool pass = b.errors == 0 && asserts == 0 && !b.top->lock_err;
    printf("RESULT shard %d: %s (%llu errors)\n", shard, !pass ? "FAIL" : b.n_x ? "PASS" : "EMPTY", (unsigned long long)b.errors);
    return pass ? 0 : 1;
}
