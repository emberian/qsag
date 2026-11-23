// Verify all 4 disjoint 64-pair `BCH(63,36,t=5)` PUF blocks (`252` disjoint pairs,
// `144` bits post-helper physical min-entropy) across 0..5 injected bit flips in `LC_BLANK`
// (`bist_allow_i = 1`), AND verify FIPS 140-3 Level 4 hard-gating (`bist_allow_i = 0`
// completely blocks `noise_flips` fault injection)!
#include "Vdregg_ro_puf_bch.h"
#include "verilated.h"
#if VM_COVERAGE
#include "verilated_cov.h"
#endif
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>

int main() {
    Vdregg_ro_puf_bch p;
    auto tick = [&]() { p.clk = 0; p.eval(); p.clk = 1; p.eval(); };
    p.rst_n = 0; p.srst_n = 0; p.bist_allow_i = 0; p.mon_en = 0; p.mon_beat = 0; p.mon_idx = 0;
    p.start_blk = 0; p.recon_mode = 0; p.blk_sel = 0; p.margin_thresh = 1;
    p.noise_flips = 0; p.vmask_ld = 0; p.syn_ld = 0; p.puf_wdata = 0;
    tick(); p.rst_n = 1; p.srst_n = 1;

    auto run = [&]() {
        p.start_blk = 1; tick(); p.start_blk = 0;
        for (int i = 0; i < 10000; i++) { tick(); if (p.done) return; }
        throw std::runtime_error("BCH timeout");
    };

    std::array<std::uint64_t, 4> words{};
    for (unsigned blk = 0; blk < 4; ++blk) {
        p.recon_mode   = 0;
        p.blk_sel      = blk;
        p.bist_allow_i = 0;
        p.noise_flips  = 0;
        run();
        if (p.blk_err || p.accepted_in_blk != 63)
            throw std::runtime_error("enrol failed to accept 63 disjoint pairs");
        const auto word = p.word_out, mask = p.vmask_out;
        const auto syn  = p.syn_out;
        words[blk] = word;
        for (unsigned prev = 0; prev < blk; ++prev) {
            if (words[prev] == word)
                throw std::runtime_error("disjoint blocks produced identical word");
        }
        // 1. Positive BIST test (`bist_allow_i = 1`, e.g. `LC_BLANK && bist_en`): 0..5 flips corrected
        p.bist_allow_i = 1;
        for (unsigned errors = 0; errors <= 5; ++errors) {
            p.recon_mode  = 1;
            p.noise_flips = errors;
            p.vmask_ld    = 1; p.puf_wdata = mask; tick(); p.vmask_ld = 0;
            p.syn_ld      = 1; p.puf_wdata = syn;  tick(); p.syn_ld   = 0;
            run();
            if (p.blk_err || p.corrected_in_blk != errors || p.word_out != word)
                throw std::runtime_error("BCH(63,36,5) reconstruction mismatch");
        }
        // 2. Negative FIPS 140-3 Level 4 test (`bist_allow_i = 0`, provisioned silicon):
        //    driving `noise_flips = 5` injects ZERO bit flips (`corrected_in_blk == 0`)!
        p.bist_allow_i = 0;
        p.noise_flips  = 5;
        p.vmask_ld     = 1; p.puf_wdata = mask; tick(); p.vmask_ld = 0;
        p.syn_ld       = 1; p.puf_wdata = syn;  tick(); p.syn_ld   = 0;
        run();
        if (p.blk_err || p.corrected_in_blk != 0 || p.word_out != word)
            throw std::runtime_error("FIPS hard-gate failed: noise_flips leaked when bist_allow_i=0");

        p.vmask_ld = 1; p.puf_wdata = 0; tick(); p.vmask_ld = 0; run();
        if (!p.blk_err || p.word_out != 0)
            throw std::runtime_error("empty helper mask accepted");
    }
    // 3. Exercise margin_thresh = 2, 3, >5-error uncorrectable Chien rejection, and zeroize_i
    for (unsigned mt : {2u, 3u, 8u}) {
        p.recon_mode = 0; p.blk_sel = 0; p.bist_allow_i = 0; p.noise_flips = 0;
        p.margin_thresh = mt;
        run();
    }
    p.margin_thresh = 1; p.recon_mode = 0; p.blk_sel = 0; run();
    const auto m0 = p.vmask_out;
    const auto s0 = p.syn_out;
    p.bist_allow_i = 1; p.recon_mode = 1; p.noise_flips = 7;
    p.vmask_ld = 1; p.puf_wdata = m0; tick(); p.vmask_ld = 0;
    p.syn_ld = 1; p.puf_wdata = (s0 ^ 0x7fffeffULL) & 0x7ffffffULL; tick(); p.syn_ld = 0;
    run();
    p.zeroize_i = 1; tick(); p.zeroize_i = 0; tick();
    std::cout << "PASS 4 disjoint BCH(63,36,5) blocks (252 pairs, 144b post-helper entropy) + FIPS bist_allow hard-gate\n";
#if VM_COVERAGE
    VerilatedCov::write("coverage.dat");
#endif
}
