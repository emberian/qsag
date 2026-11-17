# Dregg-180 v2 physical flow on the proxy (OpenROAD dcf3613, gf180mcuD, 7t5v0), in stages that each
# read the previous stage's database and write their own. Mirrors the LibreLane 3.1 step scripts
# (GlobalPlacement, RepairDesignPostGPL, DetailedPlacement, CTS, ResizerTimingPostCTS, GlobalRouting,
# DetailedRouting, FillInsertion) with the floorplan constraints of ../floorplan applied first.
#
#   P_IN     odb after PDN (LibreLane step Odb.AddRoutingObstructions)   P_OUT   output directory
#   P_SDC    sdc file                                                    P_FP    tcl files sourced before placement
#   P_FROM / P_TO   first / last stage of: place cts grt drt fin        P_DENSITY  gpl target density (0.62)
#   P_RX     extra don't-touch instance regex                            P_THREADS  detailed-route threads
#   P_GPL_ARGS  extra global_placement arguments                         P_RSZ  0 = skip repair_design
proc envd {k d} { if { [info exists ::env($k)] && $::env($k) ne "" } { return $::env($k) } ; return $d }
set out $::env(P_OUT)
file mkdir $out
set PDK /work/pdk/gf180mcuD
set SC  $PDK/libs.ref/gf180mcu_fd_sc_mcu7t5v0
set C   gf180mcu_fd_sc_mcu7t5v0__
proc metric {k v} { puts "METRIC $k $v" }
proc stamp {what} { puts "STAMP $what [clock seconds]" }

set CORNERS {tt tt_025C_5v00 ss ss_125C_4v50 ff ff_n40C_5v50}
define_corners tt ss ff
foreach {c tag} $CORNERS {
    read_liberty -corner $c $SC/lib/gf180mcu_fd_sc_mcu7t5v0__$tag.lib
    read_liberty -corner $c $PDK/libs.ref/gf180mcu_fd_io/lib/gf180mcu_fd_io__$tag.lib
    foreach ip {qrcode_id shuttle_id project_id marker logo} {
        read_liberty -corner $c /work/proj/ip/gf180mcu_ws_ip__$ip/lib/gf180mcu_ws_ip__$ip.lib
    }
}
set stages {place cts grt drt fin}
set from [envd P_FROM place]
set to   [envd P_TO grt]
set prev {place "" cts placed grt cts drt grt fin drt}
if { $from eq "place" } { read_db $::env(P_IN) } else { read_db $out/[dict get $prev $from].odb }
set block [ord::get_db_block]
set dbu [[ord::get_db_tech] getDbUnitsPerMicron]

array set ::env {DESIGN_NAME chip_top CLOCK_PERIOD 40 MAX_FANOUT_CONSTRAINT 40
    MAX_TRANSITION_CONSTRAINT 3 MAX_CAPACITANCE_CONSTRAINT 0.2 OUTPUT_CAP_LOAD 72.91}
read_sdc $::env(P_SDC)
set_dont_use [list ${C}dly*]

proc set_rc {} {
    foreach {l r c} {Metal2 0.000225636 0.000135357 Metal3 0.000225636 0.000146141
                     Metal4 0.000225636 0.000150688 Metal5 0.0000585545 0.000155595} {
        set_layer_rc -layer $l -resistance $r -capacitance $c
    }
    foreach v {Via1 Via2 Via3 Via4} { set_layer_rc -via $v -resistance 4.5 }
    set_wire_rc -signal -layers {Metal2 Metal3 Metal4}
    set_wire_rc -clock  -layers {Metal2 Metal3 Metal4}
}

# ---- protected cells -------------------------------------------------------------------------------
# Hand-sized or hand-placed instances are don't-touch for the resizer. Signal nets that feed an input
# of a protected instance are frozen while the resizer runs (it must never buffer in front of a
# don't-touch load, RSZ-3006) and released from the saved list afterwards, so CTS still owns the clocks.
set RX_BASE {u_ring/g_st|u_trng/u_(fast|slow)/g_st|u_puf/g_bank\[[0-9]+\]\.u_ro[ab]/g_st|u_pufarr/g_r|u_db/u_tdc/g_vernier|u_db/u_rapid_mux/u_fast_mux|u_db/u_lock/u_(set|hold)|u_shield/g_quad\[[0-9]+\]\.u_qsp/g_sp|u_shield/u_m5_loop/(g_m5|u_ant_end)|u_rf/(g_row|g_grp|g_col)|u_clkroot|u_oscbuf}
set ::rx $RX_BASE
if { [envd P_RX ""] ne "" } { set ::rx "$RX_BASE|[envd P_RX ""]" }
# P_RF_FREE=1: baseline in which the register file is ordinary logic (placer, resizer and CTS own it)
set ::rf_free [envd P_RF_FREE 0]
if { $::rf_free } { regsub {\|u_rf/\(g_row\|g_grp\|g_col\)} $::rx "" ::rx }
set ::dt_nets [dict create]
proc nn {name} { return [string map [list "\\" ""] $name] }
proc dont_touch {on} {
    # odb flags directly: names with escaped brackets do not survive set_dont_touch's pattern matching
    if {$on} { set ::dt_nets [dict create] }
    set n 0
    foreach inst [$::block getInsts] {
        if { ![regexp $::rx [nn [$inst getName]]] } { continue }
        incr n
        $inst setDoNotTouch $on
        if {$on} {
            foreach it [$inst getITerms] {
                if { [$it isInputSignal] && [$it getNet] ne "NULL" } {
                    set net [$it getNet]
                    if { [$net getSigType] eq "SIGNAL" } { dict set ::dt_nets [$net getName] $net }
                }
            }
        }
    }
    dict for {nm net} $::dt_nets { $net setDoNotTouch $on }
    metric dont_touch_insts $n
    metric dont_touch_nets [dict size $::dt_nets]
}
# nets wholly inside the register-file array stay frozen through CTS and routing-driven repair
proc rf_nets {on} {
    if { $::rf_free } { return }
    set n 0
    foreach net [$::block getNets] {
        set nm [nn [$net getName]]
        if { [regexp {u_rf/(g_row\[[0-9]+\]\.(gate|sel|wen|g_bit\[[0-9]+\]\.q)|wbl\[|rn\[|rnh\[|gck\[|n\[|gn\[|g_grp\[[0-9]+\]\.g_bit\[[0-9]+\]\.(a|bb)|g_col\[[0-9]+\]\.f[012])} $nm] } {
            $net setDoNotTouch $on
            incr n
        }
    }
    metric rf_frozen_nets $n
}
# After a restart the regions and groups are in the database but the Tcl-side list is not: rebuild it.
proc regroup {} {
    set groups {}
    foreach g [$::block getGroups] {
        set r [$g getRegion]
        if { $r eq "NULL" } { continue }
        foreach b [$r getBoundaries] { lappend groups [list $g [$b xMin] [$b yMin] [$b xMax] [$b yMax]] }
    }
    if { [llength $groups] == 0 } { return }
    set n 0
    foreach inst [$::block getInsts] {
        if { [$inst isFixed] || [$inst getGroup] ne "NULL" } { continue }
        if { [[$inst getMaster] getType] ne "CORE" } { continue }
        lassign [$inst getLocation] x y
        foreach g $groups {
            lassign $g grp x1 y1 x2 y2
            if { $x >= $x1 && $x < $x2 && $y >= $y1 && $y < $y2 } { $grp addInst $inst; incr n; break }
        }
    }
    metric regrouped_insts $n
}
proc dpl {} {
    regroup
    remove_fillers
    detailed_placement -max_displacement {800 800}
    optimize_mirroring
    if { [catch {check_placement -verbose} err] } { puts "DPL_CHECK $err"; metric dpl_check_failed 1 }
}
proc area_metrics {tag} {
    set a 0.0; set n 0; set nbuf 0; set abuf 0.0
    array set byblk {}
    foreach inst [$::block getInsts] {
        set m [$inst getMaster]
        if { [$m getType] ne "CORE" } { continue }
        set mn [$m getName]
        if { [regexp {__(fill|endcap|filltie)} $mn] } { continue }
        set ar [expr {double([$m getWidth]) * [$m getHeight] / ($::dbu * $::dbu)}]
        set a [expr {$a + $ar}]
        incr n
        set nm [nn [$inst getName]]
        set isbuf [regexp {__(clk)?(buf|inv)_} $mn]
        set auto [regexp {(^|/)(fanout|place|wire|rebuffer|split|clkbuf_|clkload|hold|input|output|max_cap|max_length|load_slew|use|gain|clone|delaybuf|ANTENNA|antenna)[0-9a-zA-Z_]*$} $nm]
        if { $auto } { incr nbuf; set abuf [expr {$abuf + $ar}] }
        if { [regexp {^i_chip_core/(u_[a-z0-9]+)} $nm -> blk] } { } else { set blk top }
        if { $auto } { set blk "added" }
        if { ![info exists byblk($blk)] } { set byblk($blk) 0.0 }
        set byblk($blk) [expr {$byblk($blk) + $ar}]
    }
    metric ${tag}_stdcell_area_um2 [format %.0f $a]
    metric ${tag}_stdcells $n
    metric ${tag}_added_cells $nbuf
    metric ${tag}_added_area_um2 [format %.0f $abuf]
    foreach b [lsort [array names byblk]] { metric ${tag}_blk_$b [format %.0f $byblk($b)] }
}
proc timing_report {tag} {
    puts "==== timing $tag"
    foreach c {tt ss ff} {
        foreach mm {max min} {
            if { [catch {
                set ws [sta::worst_slack_cmd $mm]
            }] } { set ws "" }
        }
        puts "---- corner $c setup"
        catch { report_checks -corner $c -path_delay max -group_path_count 1 -format summary }
        puts "---- corner $c hold"
        catch { report_checks -corner $c -path_delay min -group_path_count 1 -format summary }
        puts "---- corner $c responder"
        catch { report_checks -corner $c -path_delay max -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}] -format summary }
    }
    puts "---- all corners"
    catch { report_tns }
    catch { report_wns }
    catch { report_worst_slack -max }
    catch { report_worst_slack -min }
    catch { report_check_types -max_slew -max_capacitance -max_fanout -violators > $::out/violators_$tag.rpt }
    catch { report_checks -corner ss -path_delay max -path_group clk_core -group_path_count 1 -format full > $::out/worst_core_ss_$tag.rpt }
    catch { report_checks -corner ss -path_delay min -group_path_count 1 -format full_clock_expanded > $::out/worst_hold_ss_$tag.rpt }
    catch { report_checks -corner ss -path_delay min -group_path_count 3000 -unique_paths_to_endpoint -slack_max 0 -format summary > $::out/hold_viol_ss_$tag.rpt }
    catch { report_checks -corner ss -path_delay max -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}] -format full > $::out/responder_ss_$tag.rpt }
    catch { report_checks -corner tt -path_delay max -from [get_ports {bidir_PAD[13]}] -to [get_ports {bidir_PAD[14]}] -format full > $::out/responder_tt_$tag.rpt }
    puts "==== end timing $tag"
}
proc clock_nets {} {
    # clock roots of the SDC as odb net names (escaped brackets and all) for TritonCTS -clk_nets,
    # which avoids trees on derived nets
    set l {}
    # sck (bidir[0]) and the NFC carrier (bidir[8]) are left ideal: TritonCTS -clk_nets cannot find net
    # names with escaped brackets (CTS-0056), and without -clk_nets it builds trees on derived nets
    foreach spec {{i_chip_core/u_clkroot Z} {clk_pad Y} {i_chip_core/u_oscbuf Z}} {
        lassign $spec nm pin
        set inst [$::block findInst $nm]
        if { $inst eq "NULL" } { set inst [$::block findInst [string map [list "\[" "\\\[" "\]" "\\\]"] $nm]] }
        if { $inst eq "NULL" } { puts "CLOCK_NET_MISSING $nm"; continue }
        lappend l [[[$inst findITerm $pin] getNet] getName]
    }
    return $l
}

set_rc
set_routing_layers -signal Metal2-Metal5 -clock Metal2-Metal5
set_global_routing_layer_adjustment * 0.3
foreach l {Metal1 Metal2 Metal3 Metal4 Metal5} { set_global_routing_layer_adjustment $l 0.0 }
set_macro_extension 0
set run 0
foreach st $stages {
    if { $st eq $from } { set run 1 }
    if { !$run } { continue }
    stamp ${st}_start

    # ================================================================ place
    if { $st eq "place" } {
        foreach f [envd P_FP ""] { puts "FLOORPLAN $f"; source /work/proj/v2/phys/floorplan/$f.tcl }
        if { [namespace exists fp] } { fp::dump_regions $out/regions.json }
        area_metrics synth
        dont_touch 1
        if { [catch {global_placement -density [envd P_DENSITY 0.62] -routability_driven \
                -pad_left 0 -pad_right 0 -init_wirelength_coef 0.25 {*}[envd P_GPL_ARGS ""]} err] } {
            puts "GPL_ERROR $err"; metric gpl_failed 1
            dont_touch 0
            write_db $out/gpl_failed.odb
            exit 0
        }
        dont_touch 0
        estimate_parasitics -placement
        stamp gpl_done
        write_db $out/gpl.odb
        write_def $out/gpl.def
        unset_propagated_clock [all_clocks]
        timing_report gpl
        if { [envd P_RSZ 1] } {
            dont_touch 1
            catch { buffer_ports -inputs  -buffer_cell ${C}buf_1 }
            catch { buffer_ports -outputs -buffer_cell ${C}buf_1 }
            if { [catch {repair_design -verbose -max_wire_length 0 -slew_margin 20 -cap_margin 20} err] } {
                puts "RSZ_ERROR $err"; metric rsz_failed 1
            }
            catch {repair_tie_fanout -verbose ${C}tiel/ZN}
            catch {repair_tie_fanout -verbose ${C}tieh/Z}
            dont_touch 0
        }
        stamp rsz_done
        if { [catch {dpl} err] } { puts "DPL_ERROR $err"; metric dpl_failed 1 }
        estimate_parasitics -placement
        area_metrics placed
        timing_report placed
        write_def $out/placed.def
        write_db $out/placed.odb
    }

    # ================================================================ cts
    if { $st eq "cts" } {
        rf_nets 1
        repair_clock_inverters
        configure_cts_characterization
        set cn [clock_nets]
        puts "CTS clock nets: $cn"
        if { [catch {clock_tree_synthesis -buf_list [list ${C}clkbuf_2 ${C}clkbuf_4 ${C}clkbuf_8] \
                -root_buf ${C}clkbuf_16 -sink_clustering_enable -clk_nets $cn} err] } {
            puts "CTS_ERROR $err"; metric cts_failed 1
        }
        set_propagated_clock [all_clocks]
        estimate_parasitics -placement
        catch { repair_clock_nets -max_wire_length 0 }
        if { [catch {dpl} err] } { puts "DPL2_ERROR $err"; metric dpl2_failed 1 }
        estimate_parasitics -placement
        area_metrics cts
        report_cts
        timing_report cts
        # timing repair after CTS (setup, then hold), as LibreLane's ResizerTimingPostCTS
        dont_touch 1
        rf_nets 1
        # Setup repair is bounded: the proxy's micro-instruction path (PC -> ROM -> row address -> read ->
        # word unit) is 2.2 periods long at the slow corner and no buffering closes it; an unbounded
        # repair_timing works on 5,200 endpoints for hours. Worst endpoint only, 20 passes (10 passes take 3 minutes here).
        # Default: no setup repair (P_SETUP=1 enables it). In the 14 minutes it was given it moved the slow
        # corner's worst slack from -49.1 to -40.8 ns with 20 cells and was still running.
        if { [envd P_SETUP 0] } {
            if { [catch {repair_timing -setup -setup_margin 0.05 -max_buffer_percent 20 -repair_tns 0 -max_passes [envd P_SETUP_PASSES 20] -verbose} err] } { puts "RT_SETUP_ERROR $err" }
        }
        # Hold repair is off by default (P_HOLD=1 enables it): run g1 found 1,774 violating endpoints, nearly
        # all flop/latch -> latch paths behind clock gates (up to -19 ns at the slow corner), and answered
        # with 19,592 hold buffers (+258,000 um2), after which placement could not be legalised (DPL-0016).
        if { [envd P_HOLD 0] } {
    if { [catch {repair_timing -hold -hold_margin 0.35 -setup_margin 0.05 -max_buffer_percent 50 -allow_setup_violations -verbose} err] } { puts "RT_HOLD_ERROR $err" }
        }
        dont_touch 0
        rf_nets 1
        if { [catch {dpl} err] } { puts "DPL3_ERROR $err"; metric dpl3_failed 1 }
        estimate_parasitics -placement
        area_metrics ctsrt
        timing_report ctsrt
        write_def $out/cts.def
        write_db $out/cts.odb
    }

    # ================================================================ global route
    if { $st eq "grt" } {
        set_propagated_clock [all_clocks]
        set gargs {}
        if { [envd P_GRT_ALLOW 0] } { lappend gargs -allow_congestion }
        if { [catch {global_route -congestion_iterations [envd P_GRT_ITERS 50] -verbose {*}$gargs \
                -congestion_report_file $out/congestion.rpt} err] } {
            puts "GRT_ERROR $err"; metric grt_failed 1
            catch {global_route -congestion_iterations 30 -verbose -allow_congestion -congestion_report_file $out/congestion.rpt}
        }
        estimate_parasitics -global_routing
        catch { write_guides $out/route.guide }
        area_metrics grt
        timing_report grt
        write_db $out/grt.odb
    }

    # ================================================================ detailed route
    if { $st eq "drt" } {
        set_propagated_clock [all_clocks]
        set_thread_count [envd P_THREADS 12]
        if { [catch {detailed_route \
                -output_drc $out/drt_drc.rpt -droute_end_iter [envd P_DRT_ITERS 24] -or_seed 42 -verbose 1} err] } {
            puts "DRT_ERROR $err"; metric drt_failed 1
        }
        write_db $out/drt.odb
        write_def $out/drt.def
        catch { check_antennas -verbose -report_file $out/antenna.rpt }
    }

    # ================================================================ fill, extraction-free reports
    if { $st eq "fin" } {
        set_propagated_clock [all_clocks]
        # decap first (fillcap_*), then plain fill: decap goes wherever a gap is at least 4 sites wide
        filler_placement [list ${C}fillcap_64 ${C}fillcap_32 ${C}fillcap_16 ${C}fillcap_8 ${C}fillcap_4 \
                               ${C}fill_64 ${C}fill_32 ${C}fill_16 ${C}fill_8 ${C}fill_4 ${C}fill_2 ${C}fill_1]
        set nf 0; set af 0.0
        foreach inst [$block getInsts] {
            set mn [[$inst getMaster] getName]
            if { [regexp {__fillcap_([0-9]+)} $mn -> w] } { incr nf; set af [expr {$af + $w * 0.56 * 3.92}] }
        }
        metric fillcap_cells $nf
        metric fillcap_area_um2 [format %.0f $af]
        catch { estimate_parasitics -global_routing }
        timing_report fin
        puts "==== power (default activity)"
        catch { report_power -corner tt }
        puts "==== static IR drop"
        foreach n {VDD VSS} {
            if { [catch { analyze_power_grid -net $n -corner tt } err] } { puts "PSM_ERROR $n $err" }
        }
        puts "==== end IR"
        write_db $out/fin.odb
        write_def $out/fin.def
    }
    stamp ${st}_done
    if { $st eq $to } { break }
}
stamp done
exit 0
