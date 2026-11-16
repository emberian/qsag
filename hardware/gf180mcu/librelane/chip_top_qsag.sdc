# QSAG-NI-180 multi-clock constraints (PnR and sign-off).
#
# Clock domains
#   clk_pad    external clock pad (EXT_CLK_BYPASS = 1)            core period
#   clk_dcro   on-die ring oscillator (EXT_CLK_BYPASS = 0)        core period
#   sck        SPI clock, bidir[18] (IO_MODE 00)                  20 ns
#   rx_clk     forwarded receive clock, bidir[37] (IO_MODE 01)    12.5 ns
#   areq       C-element output of the clockless ingress stage    20 ns (width check only)
#   trng_fast, trng_slow, trng_smp   TRNG rings and sampling clock
# clk_core is clk_pad or clk_dcro through the glitch-free multiplexer; the link clocks reach
# the shell through strap-selected clock multiplexers. Every crossing between two of these
# domains goes through a two-flop synchronizer, a Gray-pointer FIFO or a toggle handshake,
# so the domains are declared asynchronous and each is timed against itself.
current_design $::env(DESIGN_NAME)
set_units -time ns

set t_core $::env(CLOCK_PERIOD)
set core   i_chip_core

create_clock -name clk_pad  -period $t_core [get_pins clk_pad/Y]
create_clock -name clk_dcro -period $t_core [get_pins $core.u_clk.u_dcro.u_nand.u_nand/ZN]
create_clock -name sck      -period 20.0    [get_pins {bidir[18].pad/Y}]
create_clock -name rx_clk   -period 12.5    [get_pins {bidir[37].pad/Y}]
create_clock -name areq     -period 20.0    [get_pins $core.u_io.u_mp.u_c.u_q/ZN]
create_clock -name trng_fast -period 4.0    [get_pins "$core.u_trng.u_fast.g_st\[0\].u_n/ZN"]
create_clock -name trng_slow -period 6.0    [get_pins "$core.u_trng.u_slow.g_st\[0\].u_n/ZN"]
create_clock -name trng_smp  -period 384.0  [get_pins $core.u_trng.u_sclk.u_buf/Z]

set_clock_groups -asynchronous \
    -group clk_pad -group clk_dcro -group sck -group rx_clk -group areq \
    -group trng_fast -group trng_slow -group trng_smp

# Intentional combinational loops: cut at the feedback input of each ring / C-element
set_disable_timing -from A1 -to ZN [get_cells $core.u_clk.u_dcro.u_nand.u_nand]
set_disable_timing -from A1 -to ZN [get_cells "$core.u_trng.u_fast.g_st\[0\].u_n"]
set_disable_timing -from A1 -to ZN [get_cells "$core.u_trng.u_slow.g_st\[0\].u_n"]
set_disable_timing -from B2 -to ZN [get_cells $core.u_io.u_mp.u_c.u_maj]
set_disable_timing -from C2 -to ZN [get_cells $core.u_io.u_mp.u_c.u_maj]

# Straps: static during operation
set_false_path -from [get_ports {input_PAD[*]}]
set_false_path -from [get_ports rst_n_PAD]

# ---------------------------------------------------------------- pads
# SPI (IO_MODE 00): the host launches on the falling edge of SCK and samples on the rising edge
set dq [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7]}]
set_input_delay  -clock sck -clock_fall -max 4.0 $dq
set_input_delay  -clock sck -clock_fall -min 0.0 $dq
set_output_delay -clock sck -max 4.0 $dq
set_output_delay -clock sck -min -1.0 $dq

# Source-synchronous receive (IO_MODE 01): data and valid launched on the falling edge of RX_CLK
set rxd [get_ports {bidir_PAD[27] bidir_PAD[28] bidir_PAD[29] bidir_PAD[30] bidir_PAD[31] bidir_PAD[32] bidir_PAD[33] bidir_PAD[34] bidir_PAD[36]}]
set_input_delay -clock rx_clk -clock_fall -max 2.5 $rxd
set_input_delay -clock rx_clk -clock_fall -min 0.0 $rxd

# Everything else at the pads is launched or sampled by the core clock with a relaxed budget:
# status pins, the forwarded transmit bank (TX_CLK is itself a registered output, so the
# data-to-clock skew is the matched pad delay), the anchor SPI master and CLK_MON.
set io_core [get_ports {bidir_PAD[8] bidir_PAD[9] bidir_PAD[10] bidir_PAD[11] bidir_PAD[12] bidir_PAD[13]
                        bidir_PAD[14] bidir_PAD[15] bidir_PAD[16] bidir_PAD[17] bidir_PAD[19] bidir_PAD[20]
                        bidir_PAD[21] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25] bidir_PAD[26]
                        bidir_PAD[35]}]
set io_budget [expr {$t_core * $::env(IO_DELAY_CONSTRAINT) / 100.0}]
set_input_delay  -clock clk_pad -max $io_budget $io_core
set_input_delay  -clock clk_pad -min 0.0 $io_core
set_output_delay -clock clk_pad -max $io_budget $io_core
set_output_delay -clock clk_pad -min 0.0 $io_core

# ---------------------------------------------------------------- environment
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
