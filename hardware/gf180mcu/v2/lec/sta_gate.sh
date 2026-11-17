#!/bin/bash
# Timing and electrical gate on a synthesized netlist (OpenSTA; no placement).
#   bash v2/lec/sta_gate.sh <sta> <liberty> <netlist.v> <top module> <out prefix>
# Wire estimate (there is no wire-load model in the gf180 liberty files): every net gets WIRE_FF fF of
# wire capacitance per load pin (default 5 fF, about 25 um of Metal2/3 per sink) [E].
# Constraints: clk 40 ns; spi_sck 100 ns, asynchronous to clk; inputs arrive and outputs are required at
# the clock edge (so a block's port paths show the logic it contributes to a stage).
# Limits: max transition and max capacitance from the liberty file. The gf180 liberty files define no
# max_fanout, so there is no fanout check; fanout is bounded through capacitance.
# Budget: 28 ns of logic per full-cycle stage (70 % of 40 ns), 14 ns for a half-cycle stage into a latch row.
STA=$1; LIB=$2; NET=$3; TOP=$4; OUT=$5
cat > $OUT.tcl <<EOF
read_liberty $LIB
read_verilog $NET
link_design $TOP
set clkp [get_ports -quiet clk]
set sckp [get_ports -quiet {spi_sck sck}]
if {[llength \$clkp]} { create_clock -name clk -period 40 \$clkp } else { create_clock -name clk -period 40 }
if {[llength \$sckp]} { create_clock -name sck -period 100 \$sckp; set_clock_groups -asynchronous -group clk -group sck }
set ins {}
foreach p [all_inputs] { if {[lsearch -exact [concat \$clkp \$sckp] \$p] < 0} { lappend ins \$p } }
if {[llength \$ins]} { set_input_delay 0 -clock clk \$ins; set_driving_cell -lib_cell gf180mcu_fd_sc_mcu7t5v0__buf_2 \$ins }
set_output_delay 0 -clock clk [all_outputs]
set_load 0.02 [all_outputs]
foreach n [get_nets *] {
    set k [llength [get_pins -quiet -of_objects \$n -filter "direction == input"]]
    if {\$k > 0} { set_load [expr {${WIRE_FF:-5} * 0.001 * \$k}] \$n }
}
# Clocks are ideal up to the flops (clock-tree synthesis balances them). The word lines of the register
# file are not clock-tree sinks: from the group clock buffers on, the clock is propagated through the
# real cells (clkbuf_4 -> icgtp_4 -> 64 latch enables).
set ckb [get_pins -quiet -hierarchical *u_ckb/I]
if {[llength \$ckb]} { set_propagated_clock \$ckb }
# Latch discipline: a row is written in the high phase and never read in that clock (dregg_seq stalls;
# proved, lec/run_formal.sh). So nothing may pass through a transparent row: the D -> Q arc is cut, a path
# into a row ends at D and must arrive before the row closes, and a path out of a row starts at its
# opening edge.
foreach c [get_cells -quiet -hierarchical -filter "ref_name =~ *latrnq*"] { set_disable_timing -from D -to Q \$c }
# clock-network pins (flop and clock-gate CLK pins and what drives them): left to clock-tree synthesis
set fh [open $OUT.clkpins w]
foreach p [concat \$clkp \$sckp] { puts \$fh [get_full_name \$p] }
foreach p [get_pins -quiet -hierarchical */CLK] {
    puts \$fh [get_full_name \$p]
    foreach d [get_pins -quiet -of_objects [get_nets -quiet -of_objects \$p] -filter "direction == output"] { puts \$fh [get_full_name \$d] }
}
close \$fh
# path groups: by where a path starts or what it passes (names kept in the netlist)
foreach {g pat} {pc u_core.u_seq.pc* ir u_core.u_seq.ir_q* pc_blk pc* ir_blk ir_q* keccak u_core.u_kec.*} {
    set nn [get_nets -quiet \$pat]
    if {[llength \$nn]} { group_path -name \$g -through \$nn }
}
puts "== setup, worst path per group"
report_checks -path_delay max -group_path_count 1 -format full -digits 2
puts "== setup endpoints"
report_checks -path_delay max -group_path_count 20000 -unique_paths_to_endpoint -format end -digits 2
# hold: register- and latch-launched paths (a port with zero input delay is not a real launch)
set regs [all_registers -clock_pins]
puts "== hold, worst path per group"
if {[llength \$regs]} { report_checks -path_delay min -from \$regs -group_path_count 1 -format full -digits 2 }
puts "== hold endpoints"
if {[llength \$regs]} { report_checks -path_delay min -from \$regs -group_path_count 20000 -unique_paths_to_endpoint -format end -digits 2 }
puts "== max slew"
report_check_types -max_slew -violators
puts "== max capacitance"
report_check_types -max_capacitance -violators
puts "== min pulse width"
report_check_types -min_pulse_width -violators
puts "== worst slew"
report_check_types -max_slew
puts "== end"
exit
EOF
$STA -no_init -no_splash $OUT.tcl > $OUT.rpt 2>&1
