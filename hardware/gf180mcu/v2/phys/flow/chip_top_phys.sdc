# Dregg-180 v2 proxy: clocks and pad timing (25 MHz core). Hierarchical instance names
# (SYNTH_HIERARCHY_MODE keep): `/` at module boundaries, `.` inside generate scopes.
current_design chip_top
set_units -time ns
if { ![info exists ::env(CLOCK_PERIOD)] } { set ::env(CLOCK_PERIOD) 40 }
set t_core $::env(CLOCK_PERIOD)
set core i_chip_core

proc px_need {what objs} {
    if { [llength $objs] == 0 } { puts "PX-SDC-ERROR: nothing matched for $what"; error "PX-SDC: $what" }
    return $objs
}
# ---- clocks: one root per domain
create_clock -name clk_core -period $t_core [px_need clk_core [get_pins $core/u_clkroot/Z]]
create_clock -name clk_pad  -period $t_core [px_need clk_pad  [get_pins clk_pad/Y]]
create_clock -name osc      -period $t_core [px_need osc      [get_pins $core/u_oscbuf/Z]]
create_clock -name sck      -period [expr {4 * $t_core}] [px_need sck [get_pins {bidir[0].pad/Y}]]
create_clock -name nfc_clk  -period 73.74   [px_need nfc_clk  [get_pins {bidir[8].pad/Y}]]
set_clock_groups -asynchronous -group clk_core -group clk_pad -group osc -group sck -group nfc_clk
# latch time borrow through a register-file row: 15 % of the period (ARCHITECTURE.md 5.2)
set_max_time_borrow [expr {0.15 * $t_core}] [get_clocks clk_core]

# ---- straps, reset, asynchronous pads
set_false_path -from [get_ports {input_PAD[*]}]
set_false_path -from [get_ports rst_n_PAD]
set_false_path -from [get_ports {bidir_PAD[26]}]          ;# tamper
set_false_path -from [get_ports {bidir_PAD[9]}]           ;# NFC ASK envelope

# ---- SPI: host launches on the falling edge of SCK, samples on the rising edge
set spi_in  [get_ports {bidir_PAD[1] bidir_PAD[3]}]
set_input_delay  -clock sck -clock_fall -max 10.0 $spi_in
set_input_delay  -clock sck -clock_fall -min 0.0  $spi_in
set_output_delay -clock sck -max 10.0 [get_ports {bidir_PAD[2]}]
set_output_delay -clock sck -min -1.0 [get_ports {bidir_PAD[2]}]

# ---- core-launched pads: FRAM master, status
set io_core [get_ports {bidir_PAD[10] bidir_PAD[16] bidir_PAD[17] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25]}]
set io_budget [expr {$t_core * 0.2}]
set_input_delay  -clock clk_core -max $io_budget [get_ports {bidir_PAD[25]}]
set_output_delay -clock clk_core -max $io_budget $io_core
set_output_delay -clock clk_core -min 0.0 $io_core
set_false_path -hold -from [get_ports {bidir_PAD[25]}]

# ---- distance-bounding responder: challenge pad -> lock -> mux -> response pad, no I/O delay on
# either port (ARCHITECTURE.md 6.3: 6.5 ns at the slow corner)
set_max_delay -ignore_clock_latency 6.5 -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}]

# ---- environment
if { [info exists ::env(MAX_FANOUT_CONSTRAINT)] } { set_max_fanout $::env(MAX_FANOUT_CONSTRAINT) [current_design] }
if { [info exists ::env(MAX_TRANSITION_CONSTRAINT)] } { set_max_transition $::env(MAX_TRANSITION_CONSTRAINT) [current_design] }
if { [info exists ::env(MAX_CAPACITANCE_CONSTRAINT)] } { set_max_capacitance $::env(MAX_CAPACITANCE_CONSTRAINT) [current_design] }
if { [info exists ::env(OUTPUT_CAP_LOAD)] } { set_load [expr {$::env(OUTPUT_CAP_LOAD) / 1000.0}] [all_outputs] }
set_clock_uncertainty 0.25 [all_clocks]
set_clock_transition  0.15 [all_clocks]
set_timing_derate -early 0.95
set_timing_derate -late  1.05
if { [info exists ::env(OPENLANE_SDC_IDEAL_CLOCKS)] && $::env(OPENLANE_SDC_IDEAL_CLOCKS) } {
    unset_propagated_clock [all_clocks]
} else {
    set_propagated_clock [all_clocks]
}
