current_design $::env(DESIGN_NAME)
set_units -time ns

# 1. Pad-level sequential clocks (`clk` 25 MHz, `host_sck` 20 MHz) for TritonCTS
create_clock -name clk      -period 40.00 [get_ports clk_PAD]
create_clock -name host_sck -period 50.00 [get_ports {bidir_PAD[18]}]
set_clock_groups -asynchronous -group {clk} -group {host_sck}

# Cut feedback arc of all 514 physical ring oscillators (512 PUF + 2 CoSO TRNG)
set rings [get_cells -hierarchical *u_gate]
if {[llength $rings] > 0} {
    set_disable_timing -from A2 -to ZN $rings
}

# Asynchronous autonomous ring-oscillator / ripple-counter CDC nets (`ass2.sdc` clocks all 44 in STAPostPNR)
foreach pat [list "*u_puf.u_cnt*" "*u_trng.samp*"] {
    set cdc_nets [get_nets -quiet -hierarchical $pat]
    if {[llength $cdc_nets] > 0} {
        set_false_path -through $cdc_nets
    }
}

set_clock_transition 0.15 [all_clocks]
set_max_time_borrow 8.0 [all_clocks]
if {[info exists ::env(CLOCK_UNCERTAINTY_CONSTRAINT)]} {
    set_clock_uncertainty $::env(CLOCK_UNCERTAINTY_CONSTRAINT) [all_clocks]
} else {
    set_clock_uncertainty 0.25 [all_clocks]
}
if {[info exists ::env(MAX_FANOUT_CONSTRAINT)]} {
    set_max_fanout $::env(MAX_FANOUT_CONSTRAINT) [current_design]
}

# 2. Pad I/O budgets across active non-clock signal pads (`SLOT_0P5X1` spare `bidir_PAD[38..43]` & `analog_PAD[*]` tied off)
set sig_pads [get_ports {rst_n_PAD input_PAD[*] bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7] \
    bidir_PAD[8] bidir_PAD[9] bidir_PAD[10] bidir_PAD[11] bidir_PAD[12] bidir_PAD[13] bidir_PAD[14] bidir_PAD[15] bidir_PAD[16] bidir_PAD[17] \
    bidir_PAD[19] bidir_PAD[20] bidir_PAD[21] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25] bidir_PAD[26] bidir_PAD[27] bidir_PAD[28] \
    bidir_PAD[29] bidir_PAD[30] bidir_PAD[31] bidir_PAD[32] bidir_PAD[33] bidir_PAD[34] bidir_PAD[35] bidir_PAD[36] bidir_PAD[37]}]
set active_bidir [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7] \
    bidir_PAD[8] bidir_PAD[9] bidir_PAD[10] bidir_PAD[11] bidir_PAD[12] bidir_PAD[13] bidir_PAD[14] bidir_PAD[15] bidir_PAD[16] bidir_PAD[17] \
    bidir_PAD[18] bidir_PAD[19] bidir_PAD[20] bidir_PAD[21] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25] bidir_PAD[26] bidir_PAD[27] \
    bidir_PAD[28] bidir_PAD[29] bidir_PAD[30] bidir_PAD[31] bidir_PAD[32] bidir_PAD[33] bidir_PAD[34] bidir_PAD[35] bidir_PAD[36] bidir_PAD[37]}]
set_input_delay  -clock clk -max 5.0 $sig_pads
set_input_delay  -clock clk -min 0.5 $sig_pads
set_output_delay -clock clk -max 5.0 $active_bidir
set_output_delay -clock clk -min 0.0 $active_bidir

set spare_pads [get_ports -quiet {bidir_PAD[38] bidir_PAD[39] bidir_PAD[40] bidir_PAD[41] bidir_PAD[42] bidir_PAD[43] analog_PAD[*]}]
if {[llength $spare_pads] > 0} {
    set_false_path -from $spare_pads
    set_false_path -to   $spare_pads
}

set dq [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7]}]
set_input_delay  -clock host_sck -max 4.0 [get_ports {input_PAD[3]}]
set_input_delay  -clock host_sck -min 0.5 [get_ports {input_PAD[3]}]
set_input_delay  -clock host_sck -clock_fall -max 4.0 $dq
set_input_delay  -clock host_sck -clock_fall -min 0.5 $dq
set_output_delay -clock host_sck -max 4.0 $dq
set_output_delay -clock host_sck -min -0.5 $dq

set_load 0.05 [all_outputs]
if {[info exists ::env(OPENLANE_SDC_IDEAL_CLOCKS)] && $::env(OPENLANE_SDC_IDEAL_CLOCKS)} {
    unset_propagated_clock [all_clocks]
} else {
    set_propagated_clock [all_clocks]
}
