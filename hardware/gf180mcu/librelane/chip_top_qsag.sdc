# Dregg-180 (QSAG-NI-180) Multi-Clock & Physical-Organ Constraints (PnR + Sign-Off).
#
# Subcarbon R0 Silicon War-Stories Hardening:
#   * T1: Only 3 full CTS trees (`clk_core` rooted post-mux at `u_clk.u_mux.u_o/Z`, `sck`, `rx_clk`)
#         plus short local `clk_pad` (stopped before `u_mux`) and `nfc_clk` (6-bit prescaler only),
#         eliminating the >600s TritonCTS multi-clock sink-clustering hang & #11349 segfault!
#   * T2: `set_false_path -hold` on async/responder `bidir_PAD` inputs + `set_max_delay 4.8`
#         on `DB_CHAL_IN -> DB_RESP_OUT` so Resizer inserts ZERO hold buffers on `< 5 ns` path!
#   * T6: `set_max_time_borrow` applied to `[get_clocks clk_core]` (OpenSTA #527 safe!).
current_design $::env(DESIGN_NAME)
set_units -time ns

set t_core $::env(CLOCK_PERIOD)
set core   i_chip_core

# 1. Clock Definitions (strictly non-overlapping sink sets for TritonCTS!)
create_clock -name clk_core -period $t_core [get_pins $core.u_clk.u_mux.u_o/Z]
create_clock -name clk_pad  -period $t_core [get_pins clk_pad/Y]
set_clock_sense -stop_propagation [get_pins $core.u_clk.u_mux.u_ga/A1]
set_clock_sense -stop_propagation [get_pins $core.u_clk.u_mux.u_gb/A1]
set_clock_sense -stop_propagation [get_pins $core.u_io.u_sck_mux.u_mux/I1]

create_clock -name sck      -period 20.0    [get_pins {bidir[18].pad/Y}]
create_clock -name rx_clk   -period 12.5    [get_pins {bidir[37].pad/Y}]
create_clock -name nfc_clk  -period 73.74   [get_pins $core.u_nfc.u_ncb.u_buf/Z]

set_clock_groups -asynchronous \
    -group clk_core -group clk_pad -group sck -group rx_clk -group nfc_clk

# 2. Transparent latch time-borrow cap ON CLOCK OBJECT (OpenSTA #527 compliant)
set_max_time_borrow [expr {0.15 * $t_core}] [get_clocks clk_core]

# 3. Cut ALL intentional combinational oscillator & Muller C-element feedback arcs
set_disable_timing -from A1 -to ZN [get_cells $core.u_clk.u_dcro.u_nand.u_nand]
set_disable_timing -from A1 -to ZN [get_cells "$core.u_trng.u_fast.g_st\[0\].u_n"]
set_disable_timing -from A1 -to ZN [get_cells "$core.u_trng.u_slow.g_st\[0\].u_n"]
set_disable_timing -from B2 -to ZN [get_cells $core.u_io.u_mp.u_c.u_maj]
set_disable_timing -from C2 -to ZN [get_cells $core.u_io.u_mp.u_c.u_maj]
set_disable_timing -from B2 -to ZN [get_cells $core.u_io.u_mptx.u_c.u_maj]
set_disable_timing -from C2 -to ZN [get_cells $core.u_io.u_mptx.u_c.u_maj]

# Cut all 64 RO-PUF 5-stage NAND2 loops at stage 0 feedback input A1 -> ZN
foreach puf_ro [get_cells -quiet "$core.u_puf.g_bank*u_ro*g_st\[0\].u_n"] {
    set_disable_timing -from A1 -to ZN $puf_ro
}

# 4. Static straps & asynchronous reset pad
set_false_path -from [get_ports {input_PAD[*]}]
set_false_path -from [get_ports rst_n_PAD]

# 5. Pad I/O Timing
# SPI (IO_MODE 00): host launches on falling edge of SCK, samples on rising edge
set dq [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7]}]
set_input_delay  -clock sck -clock_fall -max 4.0 $dq
set_input_delay  -clock sck -clock_fall -min 0.0 $dq
set_output_delay -clock sck -max 4.0 $dq
set_output_delay -clock sck -min -1.0 $dq

# Source-synchronous receive (IO_MODE 01): data and valid launched on falling edge of RX_CLK
set rxd [get_ports {bidir_PAD[27] bidir_PAD[28] bidir_PAD[29] bidir_PAD[30] bidir_PAD[31] bidir_PAD[32] bidir_PAD[33] bidir_PAD[34] bidir_PAD[36]}]
set_input_delay -clock rx_clk -clock_fall -max 2.5 $rxd
set_input_delay -clock rx_clk -clock_fall -min 0.0 $rxd

# Core-launched / status / sideband pads
set io_core [get_ports {bidir_PAD[8] bidir_PAD[9] bidir_PAD[10] bidir_PAD[11] bidir_PAD[12] bidir_PAD[13]
                        bidir_PAD[14] bidir_PAD[15] bidir_PAD[16] bidir_PAD[17] bidir_PAD[19] bidir_PAD[20]
                        bidir_PAD[21] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25] bidir_PAD[26]
                        bidir_PAD[35]}]
set io_budget [expr {$t_core * $::env(IO_DELAY_CONSTRAINT) / 100.0}]
set_input_delay  -clock clk_core -max $io_budget $io_core
set_output_delay -clock clk_core -max $io_budget $io_core
set_output_delay -clock clk_core -min 0.0 $io_core

# CRITICAL (Subcarbon R0 Trap T2): Suppress fictitious hold checks on async/responder bidir inputs
# so OpenROAD Resizer NEVER inserts hold buffers on DB_CHAL_IN, NFC_CLK_IN, NFC_ASK_IN, or TAMPER_N!
set_false_path -hold -from $io_core
set_false_path -hold -from [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3]}]

# Constrain < 5 ns Brands-Chaum rapid-bit responder pad-to-pad turnaround (Mode 00: 13->14, Mode 01: 1->0)
set_max_delay -ignore_clock_latency 4.8 -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}]
set_max_delay -ignore_clock_latency 4.8 -from [get_ports {bidir_PAD[1]}]  -to [get_ports {bidir_PAD[0]}]

# 6. Environment
set_max_fanout $::env(MAX_FANOUT_CONSTRAINT) [current_design]
if { [info exists ::env(MAX_TRANSITION_CONSTRAINT)] } {
    set_max_transition $::env(MAX_TRANSITION_CONSTRAINT) [current_design]
}
if { [info exists ::env(MAX_CAPACITANCE_CONSTRAINT)] } {
    set_max_capacitance $::env(MAX_CAPACITANCE_CONSTRAINT) [current_design]
}
set_load [expr {$::env(OUTPUT_CAP_LOAD) / 1000.0}] [all_outputs]

set_clock_uncertainty $::env(CLOCK_UNCERTAINTY_CONSTRAINT) [all_clocks]
set_clock_transition  $::env(CLOCK_TRANSITION_CONSTRAINT) [all_clocks]
set_timing_derate -early [expr {1 - $::env(TIME_DERATING_CONSTRAINT) / 100.0}]
set_timing_derate -late  [expr {1 + $::env(TIME_DERATING_CONSTRAINT) / 100.0}]

if { [info exists ::env(OPENLANE_SDC_IDEAL_CLOCKS)] && $::env(OPENLANE_SDC_IDEAL_CLOCKS) } {
    unset_propagated_clock [all_clocks]
} else {
    set_propagated_clock [all_clocks]
}
