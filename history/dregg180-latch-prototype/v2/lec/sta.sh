#!/bin/bash
# OpenSTA on a synthesized dregg_top netlist. No placement: cell delays into pin loads only, no wire
# parasitics, no buffering of high-fanout nets (Yosys/abc does none), so single nets with 70+ loads show
# up as 10 ns steps that a placed design would buffer. Indicative only.
#   bash v2/lec/sta.sh <sta binary> <liberty file> <netlist.v> [period ns]
# Reports: the worst path overall; the worst path that starts at the micro-PC; at the instruction register
# (IR_STAGE = 1 netlists); and the worst path through neither (the Keccak unit's own).
STA=$1; LIB=$2; NET=$3; PER=${4:-40}
cat > $NET.sta.tcl <<EOF
read_liberty $LIB
read_verilog $NET
link_design dregg_top
create_clock -name clk -period $PER [get_ports clk]
create_clock -name sck -period 100 [get_ports spi_sck]
set_clock_groups -asynchronous -group clk -group sck
proc worst {title args} {
    puts "== \$title"
    if {[catch {report_checks -path_delay max -group_path_count 1 -format full -digits 2 {*}\$args} e]} { puts "none (\$e)" }
}
worst "overall" -path_group clk
set pcn [get_nets -quiet {u_core.u_seq.pc[*]}]
if {[llength \$pcn]} { worst "from the micro-PC" -through \$pcn }
set irn [get_nets -quiet {u_core.u_seq.ir_q[*]}]
if {[llength \$irn]} { worst "from the instruction register" -through \$irn }
set stn [get_nets -quiet {u_core.u_seq.st[*]}]
if {[llength \$stn]} { worst "from the sequencer state" -through \$stn }
puts "== wns"
report_wns -digits 2
exit
EOF
$STA -no_init -no_splash $NET.sta.tcl 2>&1
