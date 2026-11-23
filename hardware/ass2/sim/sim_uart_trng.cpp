// Structural & fault-injection unit test for `qsag_ass2_uart` (tx_hold_q, tx_overflow, false start)
// and `qsag_trng` CoSO beat/lock detector + NIST SP 800-90B RCT (`C=41`) + APT (`C=793, W=1024`) health gates.
#include "Vuart_trng_tb.h"
#include "verilated.h"
#if VM_COVERAGE
#include "verilated_cov.h"
#endif
#include <stdexcept>
#include <iostream>

int main() {
    Vuart_trng_tb t;
    auto tick_clk = [&]() { t.clk = 0; t.eval(); t.clk = 1; t.eval(); };
    auto emit_trng_beat = [&](int sclk_cycles) {
        for (int k = 0; k < sclk_cycles; ++k) {
            t.tb_osc_f = (k >= sclk_cycles - 6) ? 1 : 0;
            t.tb_sclk = 0; t.eval();
            t.tb_sclk = 1; t.eval();
        }
        tick_clk(); tick_clk(); tick_clk();
    };

    // 1. UART reset, back-to-back TX hold + overflow, hold->shift handoff, and RX false-start rejection
    t.rst_n = 0; t.dbg_enable = 1; t.clk_div = 4; t.tx_we = 0; t.tx_byte = 0;
    t.rx = 1; t.rx_ack = 0; t.tb_osc_f = 0; t.tb_sclk = 0; t.take = 0;
    tick_clk(); t.tb_sclk = 1; t.eval(); t.tb_sclk = 0; t.eval();
    t.rst_n = 1; tick_clk();

    t.tx_we = 1; t.tx_byte = 0x55; tick_clk();
    t.tx_byte = 0xAA; tick_clk();
    t.tx_byte = 0xFF; tick_clk();
    t.tx_we = 0;
    if (!t.tx_overflow) throw std::runtime_error("expected UART tx_overflow on 3rd back-to-back write");
    for (int i = 0; i < 60; ++i) {
        t.tx_we = (i >= 35 && i <= 42) ? 1 : 0;
        t.tx_byte = 0x3C;
        tick_clk();
    }
    t.tx_we = 0;
    for (int i = 0; i < 100; ++i) tick_clk();

    // RX false start glitch: pull rx low for 1 cycle (< half_div = 1), then high!
    t.rx = 0; tick_clk(); t.rx = 1; tick_clk(); tick_clk(); tick_clk(); tick_clk();
    if (t.rx_valid) throw std::runtime_error("false start glitch should not set rx_valid");

    // 2. TRNG NIST SP 800-90B Repetition Count Test (42 beats of identical even period 16 -> rct_fail = 1, word = 0)
    t.rst_n = 0; tick_clk(); t.tb_sclk = 1; t.eval(); t.tb_sclk = 0; t.eval(); t.rst_n = 1;
    for (int b = 0; b < 45; ++b) emit_trng_beat(16);
    if (!t.rct_fail || t.ok || t.valid || t.word != 0)
        throw std::runtime_error("NIST SP 800-90B RCT failed to trip and zeroize on constant stream");

    // 3. TRNG NIST SP 800-90B Adaptive Proportion Test (>792 identical bits in 1024 window without 40-run -> apt_fail = 1)
    t.rst_n = 0; tick_clk(); t.tb_sclk = 1; t.eval(); t.tb_sclk = 0; t.eval(); t.rst_n = 1;
    for (int b = 0; b < 1100; ++b) emit_trng_beat((b % 16 == 15) ? 17 : 16);
    if (!t.apt_fail || t.rct_fail || t.ok || t.valid || t.word != 0)
        throw std::runtime_error("NIST SP 800-90B APT failed to trip and zeroize on biased stream");

    // 4. TRNG CoSO stalled/short-beat lock detector (4100 sclk cycles without beat -> cnt_max_q -> lock_bad -> rct_fail = 1)
    t.rst_n = 0; tick_clk(); t.tb_sclk = 1; t.eval(); t.tb_sclk = 0; t.eval(); t.rst_n = 1;
    t.tb_osc_f = 0;
    for (int k = 0; k < 4105; ++k) { t.tb_sclk = 0; t.eval(); t.tb_sclk = 1; t.eval(); }
    tick_clk(); tick_clk(); tick_clk(); tick_clk();
    if (!t.rct_fail)
        throw std::runtime_error("CoSO lock detector failed to trip");

    std::cout << "PASS UART hold/overflow/false-start + CoSO lock detector + NIST SP 800-90B RCT & APT zeroization\n";
#if VM_COVERAGE
    VerilatedCov::write("coverage.dat");
#endif
    return 0;
}
