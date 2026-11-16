// Unit test of the rapid-bit responder in dregg_distance_tdc (R1 B3).
//
// The property under test: in every round the response pad shows at most ONE of the two secret
// bits r0[i], r1[i], whatever the challenge pad does and for however long.
//   * before anything is committed the pad drives 0;
//   * a high challenge inside the window commits to r1[i]; from then on the pad equals r1[i] and
//     further challenge edges (including after the window) change nothing;
//   * with no challenge the window ends, the pad shows r0[i], and a later challenge edge cannot
//     select r1[i] any more;
//   * the logged challenge / response bits are the committed ones.
// Zero-delay model; the challenge pad is changed between clock edges (it is asynchronous).
#include <cinttypes>
#include <cstdio>
#include <cstdlib>

#include "Vdregg_distance_tdc.h"
#include "verilated.h"

typedef uint64_t u64;
static Vdregg_distance_tdc* top;
static u64 cycles = 0;
static int errors = 0;

static void tick() {
    top->clk = 0;
    top->eval();
    top->clk = 1;
    top->eval();
    cycles++;
}
static void chal(int v) {
    top->db_chal_pad_in = v;
    top->eval();
}
static void expect(bool ok, const char* what, int round) {
    if (!ok) {
        if (errors < 20) printf("  FAIL round %d: %s (resp %d)\n", round, what, (int)top->db_resp_pad_out);
        errors++;
    }
}
static u64 rnd_state = 0x180DB;
static u64 rnd() {
    rnd_state ^= rnd_state << 13;
    rnd_state ^= rnd_state >> 7;
    rnd_state ^= rnd_state << 17;
    return rnd_state;
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    top = new Vdregg_distance_tdc;
    const u64 WINDOW = 1ULL << 18;
    top->rst_n = 0;
    top->srst_n = 0;
    tick();
    tick();
    top->rst_n = 1;
    top->srst_n = 1;
    tick();
    int both_possible = 0, c1_rounds = 0, c0_rounds = 0;
    for (int session = 0; session < 2; session++) {
        u64 r0 = rnd(), r1 = rnd(), c = rnd();
        top->load_wdata = r0;
        top->load_r0 = 1;
        tick();
        top->load_r0 = 0;
        top->load_wdata = r1;
        top->load_r1 = 1;
        tick();
        top->load_r1 = 0;
        top->arm_responder = 1;
        tick();
        top->arm_responder = 0;
        u64 exp_c = 0, exp_r = 0;
        for (int i = 0; i < 64; i++) {
            int b0 = (r0 >> i) & 1, b1 = (r1 >> i) & 1, ci = (c >> i) & 1;
            if (b0 != b1) both_possible++;
            expect(top->responder_armed && top->db_resp_pad_oe, "responder armed and driving", i);
            // a challenge edge before the round has opened must be ignored: nothing committed yet
            for (int k = 0; k < 6; k++) {
                expect(top->db_resp_pad_out == 0, "pad is 0 before the round opens", i);
                tick();
            }
            for (int k = 0; k < 40; k++) {
                expect(top->db_resp_pad_out == 0, "pad is 0 while no challenge was sent", i);
                tick();
            }
            if (ci) {
                c1_rounds++;
                chal(1);                                  // asynchronous rising edge, mid-cycle
                expect(top->db_resp_pad_out == b1, "challenge 1 selects r1 without a clock edge", i);
                tick();
                chal(0);                                  // the attack of R1 B3: toggle the pad
                expect(top->db_resp_pad_out == b1, "pad keeps r1 after the challenge returns low", i);
                for (int k = 0; k < 50; k++) {
                    chal(k & 1);
                    expect(top->db_resp_pad_out == b1, "toggling the challenge does not change the response", i);
                    tick();
                }
                chal(0);
                if (i % 16 == 3) {                        // also sit out the whole window on a few rounds
                    for (u64 k = 0; k < WINDOW + 16; k++) {
                        tick();
                        if (top->db_resp_pad_out != b1) break;
                    }
                    expect(top->db_resp_pad_out == b1, "r0 never appears after a committed challenge 1", i);
                }
            } else {
                c0_rounds++;
                for (u64 k = 0; k < WINDOW - 60; k++) {
                    tick();
                    if (top->db_resp_pad_out != 0) break;
                }
                expect(top->db_resp_pad_out == 0, "pad is 0 until the window ends", i);
                for (int k = 0; k < 80; k++) tick();
                expect(top->db_resp_pad_out == b0, "after the window the pad shows r0", i);
                chal(1);                                  // late challenge: must not reach r1
                expect(top->db_resp_pad_out == b0, "a late challenge edge does not select r1", i);
                for (int k = 0; k < 50; k++) {
                    chal(k & 1);
                    tick();
                    expect(top->db_resp_pad_out == b0, "toggling after the window keeps r0", i);
                }
                chal(0);
                tick();
            }
            exp_c |= (u64)ci << i;
            exp_r |= (u64)(ci ? b1 : b0) << i;
            top->step_round = 1;
            tick();
            top->step_round = 0;
            // the clock after the step: pad back to 0 before the registers have shifted
            expect(top->db_resp_pad_out == 0 || !top->db_resp_pad_oe, "pad returns to 0 at the step", i);
        }
        for (int k = 0; k < 8; k++) tick();
        expect(!top->responder_armed && !top->db_resp_pad_oe, "responder released after 64 rounds", 64);
        expect(top->rounds_done == 64, "64 rounds counted", 64);
        if (top->chal_log_lo != exp_c || top->resp_log_lo != exp_r) {
            printf("  FAIL session %d: logs chal %016" PRIx64 " resp %016" PRIx64 ", expected %016" PRIx64 " %016" PRIx64 "\n",
                   session, (u64)top->chal_log_lo, (u64)top->resp_log_lo, exp_c, exp_r);
            errors++;
        }
    }
    printf("unit_tdc: 2 sessions, %d challenge-1 rounds, %d challenge-0 rounds, %d rounds with r0 != r1, %" PRIu64
           " clocks, %d errors\n",
           c1_rounds, c0_rounds, both_possible, cycles, errors);
    delete top;
    return errors != 0;
}
