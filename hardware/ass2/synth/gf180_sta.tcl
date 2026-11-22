if {[catch {
    read_liberty $::env(ASS2_SC_LIB)
    read_liberty $::env(ASS2_RAM_LIB)
    read_verilog mapped.v
    link_design qsag_ass2_enclave_top

    # 1. Primary & interface port clocks
    create_clock -name clk      -period 40.00 [get_ports clk]
    create_clock -name host_sck -period 50.00 [get_ports {bidir_in[18]}]
    create_clock -name nfc_clk  -period 73.75 [get_ports {bidir_in[33]}]
    create_clock -name jtag_tck -period 100.0 [get_ports {bidir_in[37]}]

    # 2. Internal autonomous ring-oscillator & ripple-counter clocks + tamper latch enable
    set trng_sclk_pin [get_pins -hierarchical *u_trng.u_slow.g_inv\[16\].u_inv/ZN]
    if {[llength $trng_sclk_pin] != 1} {error "missing trng_sclk pin, found [llength $trng_sclk_pin]"}
    create_clock -name trng_sclk -period 15.0 $trng_sclk_pin

    set puf_a_clks {}
    set puf_b_clks {}
    for {set k 0} {$k < 20} {incr k} {
        set pa [get_pins -hierarchical *u_puf.u_cnta.g_bit\[$k\]*/CLK]
        set pb [get_pins -hierarchical *u_puf.u_cntb.g_bit\[$k\]*/CLK]
        if {[llength $pa] != 1 || [llength $pb] != 1} {error "missing PUF ripple bit $k CLK"}
        set per [expr {4.0 * (1 << $k)}]
        create_clock -name puf_cnta_$k -period $per $pa
        create_clock -name puf_cntb_$k -period $per $pb
        lappend puf_a_clks puf_cnta_$k
        lappend puf_b_clks puf_cntb_$k
    }

    set tamp_lat_e [get_pins -of_objects [get_cells -hierarchical -filter "ref_name == gf180mcu_fd_sc_mcu7t5v0__latq_1"] -filter "name == E"]
    if {[llength $tamp_lat_e] != 1} {error "expected 1 tamper latch E pin, found [llength $tamp_lat_e]"}
    create_clock -name tamper_latch_clk -period 40.0 $tamp_lat_e

    # Asynchronous clock groups across independent oscillators and external serial clocks
    set group_cmd [list set_clock_groups -asynchronous \
        -group {clk} -group {host_sck} -group {nfc_clk} -group {jtag_tck} \
        -group {trng_sclk} -group {tamper_latch_clk}]
    foreach ca $puf_a_clks { lappend group_cmd -group [list $ca] }
    foreach cb $puf_b_clks { lappend group_cmd -group [list $cb] }
    eval $group_cmd

    set_propagated_clock [all_clocks]
    set_clock_transition 0.15 [all_clocks]
    # Bounded transparent-entry window (`u_whold` DFF -> `u_lat` latch -> `u_rdata` DFF; 0 latch-to-latch loops)
    set_max_time_borrow 8.0 [all_clocks]

    # 3. Complete driving-cell, load, and I/O timing budgets on ALL non-clock ports (`0` unconstrained endpoints!)
    set data_in [all_inputs -no_clocks]
    set_driving_cell -lib_cell gf180mcu_fd_sc_mcu7t5v0__buf_4 $data_in
    set_load 0.05 [all_outputs]

    # Default synchronous `clk`-domain budget on all data inputs & all outputs, then refine per interface
    set_input_delay  -clock clk -max 4.0 $data_in
    set_input_delay  -clock clk -min 0.5 $data_in
    set_output_delay -clock clk -max 4.0 [all_outputs]
    set_output_delay -clock clk -min 0.0 [all_outputs]

    # Host x1/x4/x8 SPI (`host_sck`, 20 MHz, mode 0: CS_N framed to rising SCK, DQ[7:0] launched on falling SCK)
    set host_dq  [get_ports {bidir_in[0] bidir_in[1] bidir_in[2] bidir_in[3] bidir_in[4] bidir_in[5] bidir_in[6] bidir_in[7]}]
    set host_out [get_ports {bidir_out[0] bidir_out[1] bidir_out[2] bidir_out[3] bidir_out[4] bidir_out[5] bidir_out[6] bidir_out[7] \
                             bidir_oe[0] bidir_oe[1] bidir_oe[2] bidir_oe[3] bidir_oe[4] bidir_oe[5] bidir_oe[6] bidir_oe[7]}]
    set_input_delay  -clock host_sck -max 4.0 [get_ports {input_in[3]}]
    set_input_delay  -clock host_sck -min 0.5 [get_ports {input_in[3]}]
    set_input_delay  -clock host_sck -clock_fall -max 4.0 $host_dq
    set_input_delay  -clock host_sck -clock_fall -min 0.5 $host_dq
    set_output_delay -clock host_sck -max 4.0 $host_out
    set_output_delay -clock host_sck -min 0.0 $host_out

    # NFC 13.56 MHz (`nfc_clk`)
    set_input_delay  -clock nfc_clk -max 5.0 [get_ports {bidir_in[32]}]
    set_input_delay  -clock nfc_clk -min 0.5 [get_ports {bidir_in[32]}]
    set_output_delay -clock nfc_clk -max 5.0 [get_ports {bidir_out[31]}]
    set_output_delay -clock nfc_clk -min 0.0 [get_ports {bidir_out[31]}]

    # JTAG (`jtag_tck`, 10 MHz)
    set_input_delay  -clock jtag_tck -max 5.0 [get_ports {bidir_in[35] bidir_in[36]}]
    set_input_delay  -clock jtag_tck -min 0.5 [get_ports {bidir_in[35] bidir_in[36]}]
    set_output_delay -clock jtag_tck -max 5.0 [get_ports {bidir_out[34] bidir_oe[34]}]
    set_output_delay -clock jtag_tck -min 0.0 [get_ports {bidir_out[34] bidir_oe[34]}]

    # 4. Cut ONLY the intentional feedback input (`A2 -> ZN`) of all 514 physical ring oscillators (512 PUF + 2 CoSO TRNG)
    set rings [get_cells -hierarchical *u_gate]
    if {[llength $rings] != 514} {error "expected 514 ring gates (512 PUF + 2 CoSO), found [llength $rings]"}
    set_disable_timing -from A2 -to ZN $rings

    check_setup -verbose
    report_checks -path_delay max -group_path_count 6 -fields {slew cap fanout} -format full_clock_expanded
    report_checks -path_delay min -group_path_count 3 -format full_clock_expanded
    foreach domain {clk host_sck trng_sclk} {
        if {![llength [find_timing_paths -path_group $domain -path_delay max]]} {
            error "no constrained register path for $domain"
        }
    }
    foreach bank {u_isram u_dsram} {
        puts "SRAM read path: $bank"
        report_checks -through [get_pins -hierarchical "${bank}.u_macro/Q*"] -path_delay max -format full_clock_expanded
    }
    report_clock_min_period -include_port_paths
    report_clock_min_period
    report_worst_slack -max
    report_worst_slack -min
    report_tns -max
} reason]} {
    puts stderr "Error: $reason"
    exit 1
}
