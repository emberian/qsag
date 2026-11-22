# Post-CTS OpenSTA-on-OpenROAD audit, single PVT per invocation.
# Read the exported stage settings for wire RC and SDC constraints.
source $::env(AUDIT_ENV)
set pvt $::env(AUDIT_PVT)
set pdk /work/ass2-pnr/pdk/gf180mcuD/libs.ref
set scl gf180mcu_fd_sc_mcu7t5v0
set ram gf180mcu_fd_ip_sram__sram512x8m8wm1
read_liberty $pdk/$scl/lib/${scl}__${pvt}.lib
read_liberty $pdk/gf180mcu_fd_io/lib/gf180mcu_fd_io__${pvt}.lib
read_liberty $pdk/gf180mcu_fd_ip_sram/lib/${ram}__${pvt}.lib
foreach lib [glob /work/ass2-pnr/ip/*/lib/*.lib] {read_liberty $lib}
read_db $::env(AUDIT_ODB)
read_sdc /work/ass2-pnr/librelane/ass2.sdc
set_propagated_clock [all_clocks]
dict for {layer rc} [dict get $::env(LAYERS_RC) *] {
    set_layer_rc -layer $layer -resistance [dict get $rc res] -capacitance [dict get $rc cap]
}
dict for {via rc} [dict get $::env(VIAS_R) nom_*] {
    set_layer_rc -via $via -resistance [dict get $rc res]
}
set_wire_rc -signal -layers $::env(SIGNAL_WIRE_RC_LAYERS)
set_wire_rc -clock -layers $::env(CLOCK_WIRE_RC_LAYERS)
if {[info exists ::env(AUDIT_SPEF)]} {
    read_spef $::env(AUDIT_SPEF)
    report_parasitic_annotation
} else {
    estimate_parasitics -placement
}
foreach check {max min} {
    foreach group {clk host_sck} {
        set paths [find_timing_paths -path_delay $check -path_group $group -group_path_count 1]
        if {![llength $paths]} {error "No $check paths for $group"}
        puts "PATH $group $check [get_property [lindex $paths 0] slack]"
    }
    report_checks -path_delay $check -group_path_count 1 -format full_clock_expanded -digits 4
    report_worst_slack -$check -digits 4
    report_tns -$check -digits 4
}
