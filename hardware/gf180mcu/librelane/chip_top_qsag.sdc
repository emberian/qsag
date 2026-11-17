# Dregg-180 (QSAG-NI-180) clocks and physical-organ constraints (PnR and sign-off).
#
# One clock root per domain (R1 B5 / R0 T1):
#   clk_core  output of the glitch-free multiplexer; every core flop, and nothing upstream of it
#   clk_pad   the clock pad; only the reference divider and the pad-side enable flops of the
#             multiplexer. Stopped at the multiplexer's AND gate.
#   osc       the DCRO output; only the DCRO tap logic, the frequency counter, the pad-clock
#             watchdog and the oscillator-side enable flops. Stopped at the multiplexer's AND gate.
#   sck, rx_clk, nfc_clk   link and NFC front-end clocks at their pad / buffer.
# The ring oscillators of the PUF and the TRNG, the Vernier taps, the PUF ripple counters and the
# Muller-pipeline strobes are not clocks for CTS: no create_clock, their flops stay unclocked.
# Every intentional combinational loop is cut at one arc with set_disable_timing.
#
# All instance paths below are the flattened names of the LibreLane netlist
# (wrapper instance, then the cell inside the qsag_cells.sv wrapper).
current_design $::env(DESIGN_NAME)
set_units -time ns

set t_core $::env(CLOCK_PERIOD)
set core   i_chip_core

proc qsag_need {what objs} {
    if { [llength $objs] == 0 } {
        puts "QSAG-SDC-ERROR: nothing matched for $what"
        error "QSAG-SDC: nothing matched for $what"
    }
    return $objs
}

# ------------------------------------------------------------------ 1. clocks
create_clock -name clk_core -period $t_core [qsag_need clk_core [get_pins $core.u_clk.u_mux.u_o.u_or/Z]]
create_clock -name clk_pad  -period $t_core [qsag_need clk_pad  [get_pins clk_pad/Y]]
create_clock -name osc      -period $t_core [qsag_need osc      [get_pins $core.u_clk.u_dcro.u_nand.u_nand/ZN]]
create_clock -name sck      -period 20.0    [qsag_need sck      [get_pins {bidir[18].pad/Y}]]
create_clock -name rx_clk   -period 12.5    [qsag_need rx_clk   [get_pins {bidir[37].pad/Y}]]
create_clock -name nfc_clk  -period 73.74   [qsag_need nfc_clk  [get_pins $core.u_nfc.u_ncb.u_buf/Z]]

# clk_pad and osc end at the multiplexer; clk_pad does not enter the SPI clock multiplexer as a
# second root of the link clock tree (CSR-selected test mode, covered by sck)
set_sense -type clock -stop_propagation -clocks [get_clocks clk_pad] \
    [qsag_need mux_ga [get_pins $core.u_clk.u_mux.u_ga.u_and/A1]]
set_sense -type clock -stop_propagation -clocks [get_clocks osc] \
    [qsag_need mux_gb [get_pins $core.u_clk.u_mux.u_gb.u_and/A1]]
set_sense -type clock -stop_propagation -clocks [get_clocks clk_pad] \
    [qsag_need sck_mux [get_pins $core.u_io.u_sck_mux.u_mux/I1]]

set_clock_groups -asynchronous \
    -group clk_core -group clk_pad -group osc -group sck -group rx_clk -group nfc_clk

# ------------------------------------------------------------------ 2. latch time borrow
# on the clock object (OpenSTA #527)
set_max_time_borrow [expr {0.15 * $t_core}] [get_clocks clk_core]

# ------------------------------------------------------------------ 3. intentional loops
# DCRO: feedback input of the gating NAND
set_disable_timing -from A1 -to ZN [qsag_need dcro [get_cells $core.u_clk.u_dcro.u_nand.u_nand]]
# TRNG rings
set_disable_timing -from A1 -to ZN [qsag_need trng_fast [get_cells "$core.u_trng.u_fast.g_st\[0\].u_n"]]
set_disable_timing -from A1 -to ZN [qsag_need trng_slow [get_cells "$core.u_trng.u_slow.g_st\[0\].u_n"]]
# 64 PUF rings
set puf_ro [qsag_need puf_rings [get_cells "$core.u_puf.g_bank\[*\].u_ro*.g_st\[0\].u_n"]]
if { [llength $puf_ro] != 64 } {
    puts "QSAG-SDC-ERROR: expected 64 PUF ring stages, matched [llength $puf_ro]"
    error "QSAG-SDC: PUF ring count"
}
foreach c $puf_ro { set_disable_timing -from A1 -to ZN $c }
# Muller C-elements (ingress and egress micropipeline): the two hold terms of the AOI222
foreach c [list $core.u_io.u_mp.u_c.u_maj $core.u_io.u_mptx.u_c.u_maj] {
    set cell [qsag_need $c [get_cells $c]]
    set_disable_timing -from B2 -to ZN $cell
    set_disable_timing -from C2 -to ZN $cell
}
# rapid-bit challenge lock: hold term of the AOI21
set_disable_timing -from B -to ZN [qsag_need chal_lock [get_cells $core.u_db.u_lock.u_set]]

# ------------------------------------------------------------------ 4. straps and reset pad
set_false_path -from [get_ports {input_PAD[*]}]
set_false_path -from [get_ports rst_n_PAD]

# ------------------------------------------------------------------ 5. pad timing
# SPI (IO_MODE 00): host launches on the falling edge of SCK, samples on the rising edge
set dq [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7]}]
set_input_delay  -clock sck -clock_fall -max 4.0 $dq
set_input_delay  -clock sck -clock_fall -min 0.0 $dq
set_output_delay -clock sck -max 4.0 $dq
set_output_delay -clock sck -min -1.0 $dq

# Source-synchronous receive (IO_MODE 01): data and valid launched on the falling edge of RX_CLK
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

# No hold repair on asynchronous / responder pad inputs (R0 T2): a hold buffer on DB_CHAL_IN,
# NFC_CLK_IN, NFC_ASK_IN or TAMPER_N would sit on a path that is asynchronous by design
set_false_path -hold -from $io_core
set_false_path -hold -from [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3]}]

# Rapid-bit responder, challenge pad -> AOI21 lock -> mux2_4 -> response pad
# (IO_MODE 00: 13 -> 14, IO_MODE 01: 1 -> 0)
set_max_delay -ignore_clock_latency 4.8 -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}]
set_max_delay -ignore_clock_latency 4.8 -from [get_ports {bidir_PAD[1]}]  -to [get_ports {bidir_PAD[0]}]

# ------------------------------------------------------------------ 6. environment
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
