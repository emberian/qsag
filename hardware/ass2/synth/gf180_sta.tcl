if {[catch {
    read_liberty $::env(ASS2_SC_LIB)
    read_liberty $::env(ASS2_RAM_LIB)
    read_verilog mapped.v
    link_design qsag_ass2_enclave_top

    set t_core [expr {[info exists ::env(ASS2_CLK_PERIOD)] ? $::env(ASS2_CLK_PERIOD) : 50.00}]

    # 1. Primary & interface port clocks (`0` virtual clocks; all physical clocks defined!)
    create_clock -name clk      -period $t_core [get_ports clk]
    create_clock -name host_sck -period 50.00   [get_ports {bidir_in[18]}]
    create_clock -name nfc_clk  -period 73.75   [get_ports {bidir_in[33]}]
    create_clock -name jtag_tck -period 100.0   [get_ports {bidir_in[37]}]

    # 2. Internal autonomous ring-oscillator & ripple-counter clocks + tamper latch enable
    set trng_sclk_pin [get_pins -hierarchical *u_trng.u_sclk_iso/Z]
    if {[llength $trng_sclk_pin] != 1} {error "missing trng_sclk_iso/Z pin, found [llength $trng_sclk_pin]"}
    create_clock -name trng_sclk -period 15.0 $trng_sclk_pin

    set puf_a_clks {}
    set puf_b_clks {}
    for {set k 0} {$k < 20} {incr k} {
        set pa [get_pins -hierarchical *u_puf.u_cnta.g_bit\[$k\]*/CLK]
        set pb [get_pins -hierarchical *u_puf.u_cntb.g_bit\[$k\]*/CLK]
        if {[llength $pa] != 1 || [llength $pb] != 1} {error "missing PUF ripple bit $k CLK"}
        set per [expr {6.0 * (1 << $k)}]
        create_clock -name puf_cnta_$k -period $per $pa
        create_clock -name puf_cntb_$k -period $per $pb
        lappend puf_a_clks puf_cnta_$k
        lappend puf_b_clks puf_cntb_$k
    }

    set tamp_lat_e [get_pins -hierarchical *u_tamper_lat/E]
    if {[llength $tamp_lat_e] == 0} {
        set tamp_lat_e [get_pins -of_objects [get_cells -hierarchical -filter "ref_name == gf180mcu_fd_sc_mcu7t5v0__latq_1"] -filter "name == E"]
    }
    if {[llength $tamp_lat_e] != 1} {error "expected 1 tamper latch E pin, found [llength $tamp_lat_e]"}
    create_clock -name tamper_latch_clk -period $t_core $tamp_lat_e

    # Asynchronous clock groups across physically independent oscillators & serial clocks
    set group_cmd [list set_clock_groups -asynchronous \
        -group {clk} -group {host_sck} -group {nfc_clk} -group {jtag_tck} \
        -group {trng_sclk} -group {tamper_latch_clk}]
    foreach ca $puf_a_clks { lappend group_cmd -group [list $ca] }
    foreach cb $puf_b_clks { lappend group_cmd -group [list $cb] }
    eval $group_cmd

    set_propagated_clock [all_clocks]
    set_clock_transition 0.15 [all_clocks]
    # DO-254 Level A Zero-Waiver Latch Discipline: ZERO iterative latch time-borrowing!
    set_max_time_borrow 0.0 [all_clocks]

    # 3. Strictly partitioned driving-cell, load, and I/O timing budgets (`0` overwritten delays, `0` unconstrained endpoints!)
    set data_in [all_inputs -no_clocks]
    set_driving_cell -lib_cell gf180mcu_fd_sc_mcu7t5v0__buf_4 $data_in
    set_load 0.05 [all_outputs]

    # 3a. `clk` domain ports (excluding `host_sck`, `nfc_clk`, `jtag_tck` dedicated data ports)
    set host_dq  [get_ports {bidir_in[0] bidir_in[1] bidir_in[2] bidir_in[3] bidir_in[4] bidir_in[5] bidir_in[6] bidir_in[7]}]
    set host_out [get_ports {bidir_out[0] bidir_out[1] bidir_out[2] bidir_out[3] bidir_out[4] bidir_out[5] bidir_out[6] bidir_out[7] \
                             bidir_oe[0] bidir_oe[1] bidir_oe[2] bidir_oe[3] bidir_oe[4] bidir_oe[5] bidir_oe[6] bidir_oe[7]}]
    set ser_in   [get_ports {input_in[3] bidir_in[0] bidir_in[1] bidir_in[2] bidir_in[3] bidir_in[4] bidir_in[5] bidir_in[6] bidir_in[7] \
                             bidir_in[18] bidir_in[32] bidir_in[33] bidir_in[35] bidir_in[36] bidir_in[37]}]
    set ser_out  [get_ports {bidir_out[0] bidir_out[1] bidir_out[2] bidir_out[3] bidir_out[4] bidir_out[5] bidir_out[6] bidir_out[7] \
                             bidir_oe[0] bidir_oe[1] bidir_oe[2] bidir_oe[3] bidir_oe[4] bidir_oe[5] bidir_oe[6] bidir_oe[7] \
                             bidir_out[31] bidir_out[34] bidir_oe[34]}]

    set clk_in_ports {}
    foreach p $data_in {
        if {[lsearch -exact $ser_in $p] < 0} { lappend clk_in_ports $p }
    }
    set clk_out_ports {}
    foreach p [all_outputs] {
        if {[lsearch -exact $ser_out $p] < 0} { lappend clk_out_ports $p }
    }

    set_input_delay  -clock clk -max 4.0 $clk_in_ports
    set_input_delay  -clock clk -min 0.5 $clk_in_ports
    set_output_delay -clock clk -max 4.0 $clk_out_ports
    set_output_delay -clock clk -min 0.0 $clk_out_ports

    # Dual-domain async reset/mode ports (`rst_n`, `boot_mode = input_in[2:1]`, `tamper_n = bidir_in[26]`)
    set dual_rst_in [get_ports {rst_n input_in[1] input_in[2] bidir_in[26]}]
    set_input_delay -clock host_sck -max 4.0 -add_delay $dual_rst_in
    set_input_delay -clock host_sck -min 0.5 -add_delay $dual_rst_in
    set_input_delay -clock nfc_clk  -max 4.0 -add_delay $dual_rst_in
    set_input_delay -clock nfc_clk  -min 0.5 -add_delay $dual_rst_in
    set_input_delay -clock jtag_tck -max 4.0 -add_delay $dual_rst_in
    set_input_delay -clock jtag_tck -min 0.5 -add_delay $dual_rst_in

    # 3b. Host x1/x4/x8 SPI (`host_sck`, 20 MHz, mode 0)
    set_input_delay  -clock host_sck -max 4.0 [get_ports {input_in[3]}]
    set_input_delay  -clock host_sck -min 0.5 [get_ports {input_in[3]}]
    set_input_delay  -clock host_sck -clock_fall -max 4.0 $host_dq
    set_input_delay  -clock host_sck -clock_fall -min 0.5 $host_dq
    set_output_delay -clock host_sck -max 4.0 $host_out
    set_output_delay -clock host_sck -min 0.0 $host_out

    # 3c. NFC 13.56 MHz (`nfc_clk`) + `clk` `verify_pin` gating
    set_input_delay  -clock nfc_clk -max 5.0 [get_ports {bidir_in[32]}]
    set_input_delay  -clock nfc_clk -min 0.5 [get_ports {bidir_in[32]}]
    set_output_delay -clock nfc_clk -max 5.0 [get_ports {bidir_out[31]}]
    set_output_delay -clock nfc_clk -min 0.0 [get_ports {bidir_out[31]}]
    set_output_delay -clock clk     -max 5.0 -add_delay [get_ports {bidir_out[31]}]
    set_output_delay -clock clk     -min 0.0 -add_delay [get_ports {bidir_out[31]}]

    # 3d. JTAG (`jtag_tck`, 10 MHz) + `clk` `jtag_ok` gating
    set_input_delay  -clock jtag_tck -max 5.0 [get_ports {bidir_in[35] bidir_in[36]}]
    set_input_delay  -clock jtag_tck -min 0.5 [get_ports {bidir_in[35] bidir_in[36]}]
    set_output_delay -clock jtag_tck -max 5.0 [get_ports {bidir_out[34] bidir_oe[34]}]
    set_output_delay -clock jtag_tck -min 0.0 [get_ports {bidir_out[34] bidir_oe[34]}]
    set_output_delay -clock clk      -max 5.0 -add_delay [get_ports {bidir_out[34] bidir_oe[34]}]
    set_output_delay -clock clk      -min 0.0 -add_delay [get_ports {bidir_out[34] bidir_oe[34]}]

    # 4. Cut ONLY the intentional feedback input (`A2 -> ZN`) of all 514 physical ring oscillators (512 PUF + 2 CoSO TRNG)
    set rings [get_cells -hierarchical *u_gate]
    if {[llength $rings] != 514} {error "expected 514 ring gates (512 PUF + 2 CoSO), found [llength $rings]"}
    set_disable_timing -from A2 -to ZN $rings

    check_setup -verbose
    report_check_types -min_pulse_width -min_period -violators
    report_checks -path_delay max -group_path_count 6 -fields {slew cap fanout} -format full_clock_expanded
    report_checks -path_delay min -group_path_count 3 -format full_clock_expanded
    foreach domain {clk host_sck nfc_clk jtag_tck trng_sclk} {
        if {![llength [find_timing_paths -path_group $domain -path_delay max]]} {
            error "no constrained register path for $domain"
        }
    }
    foreach bank {u_dsram} {
        puts "SRAM read path: $bank"
        report_checks -through [get_pins -hierarchical "${bank}.u_macro/Q*"] -path_delay max -format full_clock_expanded
    }
    report_clock_min_period -include_port_paths
    report_clock_min_period
    report_worst_slack -max
    report_worst_slack -min
    report_tns -max

    # Fail-closed DO-254 Level A timing gate (Fable Audit M2)
    set ws_max [sta::worst_slack_cmd "max"]
    set ws_min [sta::worst_slack_cmd "min"]
    if {$ws_max < 0.0} {
        error "Negative setup/recovery worst slack: [format %.3f [expr {$ws_max * 1e9}]] ns"
    }
    if {$ws_min < 0.0} {
        error "Negative hold/removal worst slack: [format %.3f [expr {$ws_min * 1e9}]] ns"
    }
} reason]} {
    puts stderr "Error: $reason"
    exit 1
}
