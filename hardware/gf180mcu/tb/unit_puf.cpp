// Unit test of dregg_ro_puf_bch (R1 B1).
//
//   unit_puf timed    built with -DQSAG_SIM_DELAYS --timing (-DTIMED): the 64 rings really
//                     oscillate (slow: picosecond events over 2 x 64 windows of 4096 clocks).
//                     Enrol one block, then reconstruct it with 5 injected flips.
//   unit_puf model    default zero-delay build with the modelled counts: enrol, reconstruct clean,
//                     with 5 flips, and with a manipulated mask.
//   unit_puf stalled  built with -DSYNTHESIS and no delays: the rings do not oscillate and the
//                     simulation-only count model is compiled out, exactly as in silicon with dead
//                     oscillators. Every block must end with blk_err and a zero word.
#include <cinttypes>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "Vdregg_ro_puf_bch.h"
#include "verilated.h"

typedef uint64_t u64;
static VerilatedContext* ctx;
static Vdregg_ro_puf_bch* top;
static u64 t_ps = 0, cycles = 0;
static int errors = 0;
static const u64 HALF = 10000;   // 50 MHz

static void half(int level) {
    u64 target = t_ps + HALF;
#ifdef TIMED
    while (top->eventsPending() && top->nextTimeSlot() < target) {
        t_ps = top->nextTimeSlot();
        ctx->time(t_ps);
        top->eval();
    }
#endif
    t_ps = target;
    ctx->time(t_ps);
    top->clk = level;
    top->eval();
}
static void tick() {
    half(0);
    half(1);
    cycles++;
}
static void check(bool ok, const char* what) {
    printf("  [%s] %s\n", ok ? "ok" : "FAIL", what);
    if (!ok) errors++;
}
static u64 run_block(int recon, int blk, int margin, int flips, u64 vmask, unsigned syn) {
    top->recon_mode = recon;
    top->blk_sel = blk;
    top->margin_thresh = margin;
    top->noise_flips = flips;
    top->vmask_in = vmask;
    top->syn_in = syn;
    top->start_blk = 1;
    tick();
    top->start_blk = 0;
    u64 c0 = cycles;
    while (!top->done) {
        tick();
        if (cycles - c0 > 40000000ULL) {
            printf("  TIMEOUT waiting for done\n");
            errors++;
            break;
        }
    }
    return cycles - c0;
}

int main(int argc, char** argv) {
    ctx = new VerilatedContext;
    ctx->commandArgs(argc, argv);
    top = new Vdregg_ro_puf_bch{ctx};
    bool stalled = argc > 1 && !strcmp(argv[1], "stalled");
    bool timed = argc > 1 && !strcmp(argv[1], "timed");
    const char* mode = argc > 1 ? argv[1] : "model";
    top->clk = 0;
    top->rst_n = 0;
    top->srst_n = 0;
    top->mon_en = 0;
    top->mon_beat = 0;
    top->mon_idx = 0;
    top->eval();
    tick();
    tick();
    top->rst_n = 1;
    top->srst_n = 1;
    tick();
    if (stalled) {
        printf("unit_puf stalled: oscillators dead, no simulation count model\n");
        u64 c = run_block(0, 0, 4, 0, 0, 0);
        printf("  enrol: done after %" PRIu64 " clocks, blk_err %d, word %016" PRIx64 ", accepted %d\n", c, (int)top->blk_err,
               (u64)top->word_out, (int)top->accepted_in_blk);
        check(top->blk_err == 1 && top->word_out == 0, "enrolment aborts with blk_err and releases no word");
        check(c > 4096 && c < 4200, "abort happens after the first measurement window");
        c = run_block(1, 0, 4, 0, ~0xFULL, 0x1234567);
        printf("  recon: done after %" PRIu64 " clocks, blk_err %d, word %016" PRIx64 "\n", c, (int)top->blk_err, (u64)top->word_out);
        check(top->blk_err == 1 && top->word_out == 0, "reconstruction aborts with blk_err and releases no word");
    } else {
        printf("unit_puf %s: %s\n", mode, timed ? "rings oscillate (QSAG_SIM_DELAYS)" : "modelled counts (zero-delay RTL)");
        u64 c = run_block(0, 0, 4, 0, 0, 0);
        u64 e_word = top->word_out, e_mask = top->vmask_out;
        unsigned e_syn = top->syn_out;
        printf("  enrol: %" PRIu64 " clocks, blk_err %d, accepted %d, word %016" PRIx64 ", mask %016" PRIx64 ", syndrome %07x\n", c,
               (int)top->blk_err, (int)top->accepted_in_blk, e_word, e_mask, e_syn);
        check(!top->blk_err && top->accepted_in_blk == 60, "enrolment accepts exactly 60 pairs");
        check(c >= 64ULL * 4096 && c < 64ULL * (4096 + 16) + 200, "64 windows of 4096 clocks plus settle");
        check(e_word != 0 && __builtin_popcountll(e_mask) == 60, "non-trivial word, 60 mask bits");
        if (!timed) {
            c = run_block(1, 0, 4, 0, e_mask, e_syn);
            printf("  recon clean: %" PRIu64 " clocks, blk_err %d, corrected %d, word %016" PRIx64 "\n", c, (int)top->blk_err,
                   (int)top->corrected_in_blk, (u64)top->word_out);
            check(!top->blk_err && top->word_out == e_word && top->corrected_in_blk == 0,
                  "reconstruction reproduces the word, 0 corrections");
        }
        for (int flips = timed ? 5 : 1; flips <= 5; flips++) {
            c = run_block(1, 0, 4, flips, e_mask, e_syn);
            printf("  recon %d flips: blk_err %d, corrected %d, word %016" PRIx64 "\n", flips, (int)top->blk_err,
                   (int)top->corrected_in_blk, (u64)top->word_out);
            check(!top->blk_err && top->word_out == e_word && top->corrected_in_blk == flips, "injected bit flips are corrected");
        }
        if (!timed) {
            u64 bad_mask = e_mask & (e_mask - 1);        // one accepted pair removed
            c = run_block(1, 0, 4, 0, bad_mask, e_syn);
            printf("  recon manipulated mask: blk_err %d, word %016" PRIx64 "\n", (int)top->blk_err, (u64)top->word_out);
            check(top->blk_err && top->word_out == 0, "a mask with 59 pairs is rejected");
        }
    }
    printf("unit_puf %s: %s (%d errors), %" PRIu64 " clocks\n", mode, errors ? "FAILED" : "PASSED", errors, cycles);
    top->final();
    delete top;
    return errors != 0;
}
