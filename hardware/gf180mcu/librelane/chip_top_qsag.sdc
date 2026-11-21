# Dregg-180 (QSAG-NI-180) unified PnR & 9-Corner OpenSTA Signoff Constraints.
#
# Zero virtual clocks: ALL five physical clock sources (`clk_pad`, `osc`, `sck`, `rx_clk`, `nfc_clk`)
# are defined on their true physical ports / oscillator root and propagated with real extracted RC
# parasitics across all 9 PVT/RC corners (`tt_025C_5v00`, `ss_125C_4v50`, `ff_n40C_5v50` x `nom/min/max`).
# Avoiding an internal overwriting `create_clock` on `u_mux.u_o/Z` preserves unbroken STA timing
# paths for both `clk_pad` and `osc` through the glitch-free mux into the core H-Tree (preventing
# OpenROAD `CTS-0179` null-path crashes while timing full pad/DCRO-to-register insertion & skew).
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

# ------------------------------------------------------------------ 1. real physical clocks (0 virtual clocks)
create_clock -name clk_pad -period $t_core [qsag_need clk_pad [get_ports clk_PAD]]
create_clock -name osc     -period $t_core [qsag_need osc     [get_pins $core.u_clk.u_dcro.u_osc_iso.u_iso/Z]]
create_clock -name sck     -period 25.0    [qsag_need sck     [get_ports {bidir_PAD[18]}]]
create_clock -name rx_clk  -period $t_core [qsag_need rx_clk  [get_ports {bidir_PAD[37]}]]
create_clock -name nfc_clk -period 73.74   [qsag_need nfc_clk [get_ports {bidir_PAD[8]}]]

set_clock_groups -asynchronous \
    -group clk_pad -group osc -group sck -group rx_clk -group nfc_clk

# ------------------------------------------------------------------ 2. latch time borrow
set_max_time_borrow [expr {0.15 * $t_core}] [all_clocks]

# ------------------------------------------------------------------ 3. intentional loops & mutually-exclusive mux arcs
# DCRO feedback
set_disable_timing -from A1 -to ZN [qsag_need dcro [get_cells $core.u_clk.u_dcro.u_nand.u_nand]]
# CoSO 17-stage TRNG rings (`u_fast` & `u_slow`)
set_disable_timing -from A1 -to ZN [qsag_need trng_fast [get_cells "$core.u_trng.u_fast.g_st\[0\].u_n"]]
set_disable_timing -from A1 -to ZN [qsag_need trng_slow [get_cells "$core.u_trng.u_slow.g_st\[0\].u_n"]]
# 32 PUF rings (16 Bank A x 16 Bank B = 256 differential pairs)
set puf_ro [qsag_need puf_rings [get_cells "$core.u_puf.g_bank\[*\].u_ro*.g_st\[0\].u_n"]]
if { [llength $puf_ro] != 32 } {
    puts "QSAG-SDC-ERROR: expected 32 PUF ring stages, matched [llength $puf_ro]"
    error "QSAG-SDC: PUF ring count"
}
foreach c $puf_ro { set_disable_timing -from A1 -to ZN $c }

# Muller C-elements (ingress and egress 2-phase clockless micropipeline)
foreach c [list $core.u_io.u_mp.u_c.u_maj $core.u_io.u_mptx.u_c.u_maj] {
    set cell [qsag_need $c [get_cells $c]]
    set_disable_timing -from B2 -to ZN $cell
    set_disable_timing -from C2 -to ZN $cell
}
# Cut false `rx_clk` propagation into Mode-1x clockless Muller-C `req_in` (gated by `& m_async == 0` whenever `rx_clk` is active)
set_disable_timing -from I -to Z [qsag_need mp_ireq [get_cells $core.u_io.u_mp.u_ireq.u_iso]]

# Rapid-bit challenge lock feedback
set_disable_timing -from B -to ZN [qsag_need chal_lock [get_cells $core.u_db.u_lock.u_set]]

# Tunable delay-line glitch sensors & asynchronous Vernier TDC / PUF / CoSO TRNG CDC nets
set_false_path -through [qsag_need trcp_launch [get_pins $core.u_clk.u_trcp.u_liso.u_iso/Z]]
set_false_path -through [qsag_need quad_launch [get_pins "$core.u_clk.u_shield.g_quad\[*\].u_qsp.u_iso_q.u_iso/Z"]]
set_false_path -through [qsag_need vernier_sta [get_pins $core.u_db.u_tdc.u_ista.u_iso/Z]]
set_false_path -through [qsag_need vernier_sto [get_pins $core.u_db.u_tdc.u_isto.u_iso/Z]]
set_false_path -through [qsag_need vernier_taps [get_nets "$core.u_db.u_tdc.g_vernier\[*\].q_tap*"]]
set_false_path -through [qsag_need puf_cnta     [get_nets "$core.u_puf.u_cnta.g_bit\[*\].u_t.q*"]]
set_false_path -through [qsag_need puf_cntb     [get_nets "$core.u_puf.u_cntb.g_bit\[*\].u_t.q*"]]
set_false_path -through [qsag_need trng_cdc     [get_nets "$core.u_trng.samp*"]]
set_false_path -through [qsag_need mpipe_rx     [get_nets "$core.u_io.u_mp.bank_*"]]
set_false_path -through [qsag_need mpipe_tx     [get_nets "$core.u_io.u_mptx.bank_*"]]
# Pre-mux (`osc` / `clk_pad`) <-> post-mux (`clk_core`) quasi-static / Gray / watchdog CDC signals
set_false_path -through [qsag_need dcro_ofreq   [get_nets "$core.u_clk.ofreq*"]]
set_false_path -through [qsag_need dcro_tapg    [get_nets "$core.u_clk.tap_gray_q*"]]
set_false_path -through [qsag_need wd_pad_alive [get_nets "$core.u_clk.pad_alive*"]]
set_false_path -through [qsag_need wd_osc_dead  [get_nets "$core.u_clk.osc_dead*"]]
set_false_path -through [qsag_need diag_hb_gray [get_nets "$core.u_io.hb_gray*"]]

# First-stage `/D` inputs of all `qsag_sync2` 2-FF CDC synchronizers (identified via their preserved
# `(* ASYNC_REG = "TRUE", keep *) logic m` output net; leaves `m -> s` resolution paths fully timed!).
set qsag_sync_d_pins [list]
foreach n [get_nets -quiet "$core.*.u_*.m"] {
    foreach p [get_pins -of_objects $n] {
        if { [get_property $p direction] == "output" } {
            set c [get_cells -of_objects $p]
            set dp [get_pins -quiet "[get_property $c full_name]/D"]
            if { [llength $dp] > 0 } { lappend qsag_sync_d_pins $dp }
        }
    }
}
if { [llength $qsag_sync_d_pins] > 0 } {
    set_false_path -to $qsag_sync_d_pins
}

# ------------------------------------------------------------------ 4. straps and reset pad
set_false_path -from [get_ports {input_PAD[*]}]
set_false_path -from [get_ports rst_n_PAD]

# ------------------------------------------------------------------ 5. pad timing
set dq [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3] bidir_PAD[4] bidir_PAD[5] bidir_PAD[6] bidir_PAD[7]}]
set_input_delay  -clock sck -clock_fall -max 4.0 $dq
set_input_delay  -clock sck -clock_fall -min 0.0 $dq
set_output_delay -clock sck -max 4.0 $dq
set_output_delay -clock sck -min -1.0 $dq

set rxd [get_ports {bidir_PAD[27] bidir_PAD[28] bidir_PAD[29] bidir_PAD[30] bidir_PAD[31] bidir_PAD[32] bidir_PAD[33] bidir_PAD[34] bidir_PAD[36]}]
set_input_delay -clock rx_clk -clock_fall -max 3.0 $rxd
set_input_delay -clock rx_clk -clock_fall -min 0.0 $rxd

set io_core [get_ports {bidir_PAD[9] bidir_PAD[10] bidir_PAD[11] bidir_PAD[12] bidir_PAD[13]
                        bidir_PAD[14] bidir_PAD[15] bidir_PAD[16] bidir_PAD[17] bidir_PAD[19] bidir_PAD[20]
                        bidir_PAD[21] bidir_PAD[22] bidir_PAD[23] bidir_PAD[24] bidir_PAD[25] bidir_PAD[26]
                        bidir_PAD[35]}]
set io_budget [expr {$t_core * $::env(IO_DELAY_CONSTRAINT) / 100.0}]
set_input_delay  -clock clk_pad -max $io_budget $io_core
set_output_delay -clock clk_pad -max $io_budget $io_core
set_output_delay -clock clk_pad -min 0.0 $io_core

set_false_path -hold -from $io_core
set_false_path -hold -from [get_ports {bidir_PAD[0] bidir_PAD[1] bidir_PAD[2] bidir_PAD[3]}]

# Rapid-bit responder: challenge pad -> AOI21 lock -> mux2_4 -> response pad (<= 8.0 ns silicon budget;
# accounts for external set_input_delay + set_output_delay already applied to these shared bidir ports)
set_max_delay -ignore_clock_latency [expr {2.0 * $io_budget + 8.0}] -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}]
set_max_delay -ignore_clock_latency 16.0 -from [get_ports {bidir_PAD[1]}]  -to [get_ports {bidir_PAD[0]}]

# ------------------------------------------------------------------ 6. environment
set_max_fanout $::env(MAX_FANOUT_CONSTRAINT) [current_design]
if { [info exists ::env(MAX_TRANSITION_CONSTRAINT)] } {
    set_max_transition $::env(MAX_TRANSITION_CONSTRAINT) [current_design]
}
if { [info exists ::env(MAX_CAPACITANCE_CONSTRAINT)] } {
    set_max_capacitance $::env(MAX_CAPACITANCE_CONSTRAINT) [current_design]
}
set_load [expr {$::env(OUTPUT_CAP_LOAD) / 1000.0}] [all_outputs]
# Dedicated 50-ohm SMA coax response pads (`pcb/README.md`: ~5 pF load, not a 33.5 pF shared bus)
set_load 0.005 [get_ports {bidir_PAD[14] bidir_PAD[0]}]

set_clock_uncertainty $::env(CLOCK_UNCERTAINTY_CONSTRAINT) [all_clocks]
set_clock_transition  $::env(CLOCK_TRANSITION_CONSTRAINT) [all_clocks]
set_timing_derate -early [expr {1 - $::env(TIME_DERATING_CONSTRAINT) / 100.0}]
set_timing_derate -late  [expr {1 + $::env(TIME_DERATING_CONSTRAINT) / 100.0}]

if { [info exists ::env(OPENLANE_SDC_IDEAL_CLOCKS)] && $::env(OPENLANE_SDC_IDEAL_CLOCKS) } {
    unset_propagated_clock [all_clocks]
} else {
    set_propagated_clock [all_clocks]
}

# OpenROAD 2026-02-17 renamed `-post_cts_disable` -> `-no_insertion_delay`. Since Dregg-180 has zero
# clocked SRAM macros and two real physical clocks (`clk_pad` & `osc`) converging on `u_clk.u_mux.u_o`,
# pass `-no_insertion_delay` to `clock_tree_synthesis` so TritonCTS builds all H-Trees cleanly without
# hanging in `CTS-0033` macro-vs-register latency balancing.
if { [info commands ::clock_tree_synthesis] != "" && [info commands ::_qsag_orig_cts] == "" } {
    rename ::clock_tree_synthesis ::_qsag_orig_cts
    proc ::clock_tree_synthesis {args} {
        if { [lsearch -exact $args "-no_insertion_delay"] == -1 } {
            lappend args -no_insertion_delay
        }
        return [uplevel 1 [linsert $args 0 ::_qsag_orig_cts]]
    }
}
