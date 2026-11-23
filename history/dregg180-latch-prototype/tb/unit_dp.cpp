// Datapath unit test: field engine + arithmetic unit + sponge against model vectors.
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

#include "Vdp_top.h"
#include "verilated.h"

static Vdp_top* top;
static uint64_t cycles = 0;

static void tick() {
    top->clk = 0;
    top->eval();
    top->clk = 1;
    top->eval();
    cycles++;
}
static void wr(int addr, uint64_t v) {
    top->tb_we = 1;
    top->tb_addr = addr;
    top->tb_wdata = v;
    tick();
    top->tb_we = 0;
}
static uint64_t rd(int addr) {
    top->tb_addr = addr;
    top->clk = 0;
    top->eval();
    return top->tb_rdata;
}
static uint64_t run(int op, int d = 0, int s1 = 0, int s2 = 0, int n = 0, int dir = 0, uint64_t xw = 0) {
    top->op = op;
    top->d = d;
    top->s1 = s1;
    top->s2 = s2;
    top->n = n;
    top->dir = dir;
    top->xw = xw;
    top->start = 1;
    tick();
    top->start = 0;
    uint64_t c0 = cycles;
    while (!top->done) {
        tick();
        if (cycles - c0 > 100000) {
            printf("TIMEOUT op %d\n", op);
            exit(1);
        }
    }
    return cycles - c0;
}
enum { PERM = 1, ABSW, SETW, MOV, EMUL, EADD, ESUB, EEQ, FFWD, LDRES, FP5_MUL, FP5_ADD, FP5_SUB, FP5_EQ };

static std::vector<uint8_t> unhex(const std::string& h) {
    std::vector<uint8_t> b;
    if (h == "-") return b;
    for (size_t i = 0; i + 1 < h.size(); i += 2) b.push_back((uint8_t)strtoul(h.substr(i, 2).c_str(), nullptr, 16));
    return b;
}
static void xor_byte(size_t pos, uint8_t v) {             // XOR into the rate, little-endian lanes
    int lane = (int)(pos / 8);
    wr(lane, rd(lane) ^ ((uint64_t)v << (8 * (pos % 8))));
}
static uint64_t permute(int rounds) {
    top->k_turbo = rounds == 12;
    top->k_start = 1;
    tick();
    top->k_start = 0;
    uint64_t c0 = cycles;
    while (!top->k_done) tick();
    return cycles - c0;
}
// One sponge call over the register file with the RTL permutation (FIPS 202 section 4, pad10*1
// with the domain suffix in the first padding byte)
static bool sponge_kat(size_t rate, uint8_t suffix, int rounds, const std::vector<uint8_t>& msg,
                       const std::vector<uint8_t>& want) {
    for (int i = 0; i < 25; i++) wr(i, 0);
    size_t off = 0;
    for (size_t i = 0; i < msg.size(); i++) {
        xor_byte(off, msg[i]);
        if (++off == rate) {
            permute(rounds);
            off = 0;
        }
    }
    xor_byte(off, suffix);
    xor_byte(rate - 1, 0x80);
    permute(rounds);
    bool ok = true;
    off = 0;
    for (size_t i = 0; i < want.size(); i++) {
        if (off == rate) {
            permute(rounds);
            off = 0;
        }
        ok &= (uint8_t)(rd((int)(off / 8)) >> (8 * (off % 8))) == want[i];
        off++;
    }
    return ok;
}
enum { T0 = 0, CH = 12, RA = 16, RB = 20, RX = 32, RY = 36, RA5 = 17, RB5 = 22, RX5 = 32, RY5 = 37 };

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    top = new Vdp_top;
    top->rst_n = 0;
    tick();
    tick();
    top->rst_n = 1;
    tick();
    std::ifstream f(argv[1]);
    std::string line;
    int n = 0, bad = 0;
    uint64_t cyc_perm = 0, cyc_emul = 0, cyc_keccak[2] = {0, 0};
    while (std::getline(f, line)) {
        std::istringstream ss(line);
        std::string tag, tok;
        ss >> tag;
        if (tag == "H") {                                // FIPS 202 known answer: rate suffix rounds msg out
            size_t rate;
            std::string suf, msg, out;
            int rounds;
            ss >> rate >> suf >> rounds >> msg >> out;
            bool hok = sponge_kat(rate, (uint8_t)strtoul(suf.c_str(), nullptr, 16), rounds, unhex(msg), unhex(out));
            n++;
            if (!hok) {
                bad++;
                if (bad <= 10) printf("MISMATCH line %d: %s\n", n, line.substr(0, 70).c_str());
            }
            continue;
        }
        std::vector<uint64_t> w;
        while (ss >> tok) w.push_back(strtoull(tok.c_str(), nullptr, 16));
        bool ok = true;
        char t = tag[0];
        if (t == 'E' || t == '+' || t == '-') {
            for (int i = 0; i < 4; i++) wr(RX + i, w[i]);
            for (int i = 0; i < 4; i++) wr(RY + i, w[4 + i]);
            uint64_t c = run(t == 'E' ? EMUL : t == '+' ? EADD : ESUB, RA, RX, RY);
            if (t == 'E') cyc_emul = c;
            for (int i = 0; i < 4; i++) ok &= rd(RA + i) == w[8 + i];
            // aliasing: dst == src1
            run(t == 'E' ? EMUL : t == '+' ? EADD : ESUB, RX, RX, RY);
            for (int i = 0; i < 4; i++) ok &= rd(RX + i) == w[8 + i];
        } else if (t == '5' || t == 'a' || t == 's') {
            for (int i = 0; i < 5; i++) wr(RX5 + i, w[i]);
            for (int i = 0; i < 5; i++) wr(RY5 + i, w[5 + i]);
            int fop = (t == '5') ? FP5_MUL : (t == 'a') ? FP5_ADD : FP5_SUB;
            run(fop, RA5, RX5, RY5);
            for (int i = 0; i < 5; i++) ok &= rd(RA5 + i) == w[10 + i];
            // aliasing: dst == src1
            run(fop, RX5, RX5, RY5);
            for (int i = 0; i < 5; i++) ok &= rd(RX5 + i) == w[10 + i];
        } else if (t == 'q') {
            for (int i = 0; i < 5; i++) wr(RA5 + i, w[i]);
            for (int i = 0; i < 5; i++) wr(RB5 + i, w[5 + i]);
            run(FP5_EQ, 0, RA5, RB5);
            ok = top->eq == w[10];
        } else if (t == '=') {
            for (int i = 0; i < 4; i++) wr(RA + i, w[i]);
            for (int i = 0; i < 4; i++) wr(RB + i, w[4 + i]);
            run(EEQ, 0, RA, RB);
            ok = top->eq == w[8];
        } else if (t == 'S') {
            run(SETW, 24, 0, 0, 0, 0, w[0]);
            ok = rd(24) == w[1];
        } else if (t == 'A') {
            wr(5, w[0]);
            run(ABSW, 5, 0, 0, 0, 0, w[1]);
            ok = rd(5) == w[2];
            run(LDRES, 0, 5);
            ok &= top->res == w[2];
        } else if (t == 'P') {
            for (int i = 0; i < 12; i++) wr(i, w[i]);
            cyc_perm = run(PERM);
            for (int i = 0; i < 12; i++) ok &= rd(i) == w[12 + i];
        } else if (t == 'F') {
            for (int i = 0; i < 4; i++) wr(i, w[2 + i]);
            for (int i = 0; i < 4; i++) wr(RX + i, w[6 + i]);
            for (int i = 0; i < 4; i++) wr(RY + i, w[10 + i]);
            for (int i = 0; i < 3; i++) wr(RA + i, w[14 + i]);
            run(FFWD, 0, RA, 0, 0, (int)w[0], w[1]);
            for (int i = 0; i < 4; i++) ok &= rd(RX + i) == w[17 + i];
        } else if (t == 'K') {
            int rounds = (int)w[0];
            for (int i = 0; i < 25; i++) wr(i, w[1 + i]);
            top->k_turbo = rounds == 12;
            top->k_start = 1;
            tick();
            top->k_start = 0;
            uint64_t c0 = cycles;
            while (!top->k_done) tick();
            cyc_keccak[rounds == 12] = cycles - c0;
            for (int i = 0; i < 25; i++) ok &= rd(i) == w[26 + i];
        } else
            continue;
        n++;
        if (!ok) {
            bad++;
            if (bad <= 10) {
                printf("MISMATCH line %d: %s\n  regs:", n, line.substr(0, 60).c_str());
                for (int i = 0; i < 40; i++)
                    if (i < 25 || i >= 32) printf(" %d=%" PRIx64, i, rd(i));
                printf("\n");
            }
        }
    }
    if (argc > 2)
        printf("%s: %d vectors, %d mismatches\n", argv[2], n, bad);
    else
        printf("unit_dp: %d vectors, %d mismatches; PERM = %" PRIu64 " cycles, EMUL = %" PRIu64 ", Keccak-f = %" PRIu64 ", Keccak-p12 = %" PRIu64 " cycles\n",
               n, bad, cyc_perm, cyc_emul, cyc_keccak[0], cyc_keccak[1]);
    delete top;
    return bad != 0 || n == 0;
}
