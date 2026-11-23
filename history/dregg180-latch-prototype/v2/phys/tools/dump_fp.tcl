# Dump what the floorplan scripts need from the post-PDN database: pads, rows, tap pattern, name checks.
read_db $::env(P_IN)
set block [ord::get_db_block]
set dbu [[ord::get_db_tech] getDbUnitsPerMicron]
puts "DIE [[$block getDieArea] xMin] [[$block getDieArea] yMin] [[$block getDieArea] xMax] [[$block getDieArea] yMax]"
puts "CORE [[$block getCoreArea] xMin] [[$block getCoreArea] yMin] [[$block getCoreArea] xMax] [[$block getCoreArea] yMax]"
set n 0
foreach r [$block getRows] { if { $n < 3 } { puts "ROW [$r getName] [$r getOrigin] [$r getSiteCount] [$r getOrient] [[$r getSite] getName]" } ; incr n }
puts "ROWS $n"
foreach inst [$block getInsts] {
    set m [[$inst getMaster] getName]
    if { [string match gf180mcu_fd_io* $m] || [string match gf180mcu_ws_ip* $m] } {
        set bb [$inst getBBox]
        puts [format "PAD %-22s %-28s %8.1f %8.1f %8.1f %8.1f %s" [$inst getName] $m [expr {[$bb xMin]/double($dbu)}] [expr {[$bb yMin]/double($dbu)}] [expr {[$bb xMax]/double($dbu)}] [expr {[$bb yMax]/double($dbu)}] [$inst getOrient]]
    }
}
array set types {}
set taps {}
foreach inst [$block getInsts] {
    set m [$inst getMaster]
    set k "[$m getName] [$m getType] [$inst getPlacementStatus]"
    if { ![string match gf180mcu_fd_sc* [$m getName]] } { continue }
    if { [$inst isFixed] } {
        if { ![info exists types($k)] } { set types($k) 0 }
        incr types($k)
        set bb [$inst getBBox]
        if { [$bb yMin] == 885920 || [$bb yMin] == 893760 } { lappend taps "[$bb yMin]:[expr {[$bb xMin]/double($dbu)}]" }
    }
}
foreach k [array names types] { puts "FIXED $k $types($k)" }
puts "TAPS_ROW01 [lrange [lsort $taps] 0 70]"
foreach nm {i_chip_core/u_rf/g_row[0].g_bit[0].u_lat i_chip_core/u_rf/g_row[71].u_cg i_chip_core/u_rf/g_grp[8].g_bit[63].u_gn i_chip_core/u_rf/g_col[5].u_wd i_chip_core/u_clkroot i_chip_core/u_rf/g_half[0].u_rnh} {
    set i [$block findInst $nm]
    puts "FIND $nm [expr {$i eq "NULL" ? "MISSING" : [[$i getMaster] getName]}]"
}
set cnt 0
foreach inst [$block getInsts] { set nm [$inst getName]; if { [string match *u_rf* $nm] && $cnt < 12 } { puts "RFNAME $nm"; incr cnt } }
set cnt 0
foreach inst [$block getInsts] { set nm [$inst getName]; if { [regexp {u_db/(u_rapid|u_lock|u_c|u_m|u_i|u_e)} $nm] && $cnt < 40 } { puts "DBNAME $nm [[$inst getMaster] getName]"; incr cnt } }
set cnt 0
foreach net [$block getNets] { set nm [$net getName]; if { [string match *u_rf* $nm] && $cnt < 25 } { puts "RFNET $nm"; incr cnt } }
foreach l [[ord::get_db_tech] getLayers] { if { [$l getRoutingLevel] > 0 } { puts "LAYER [$l getName] [$l getDirection] pitch [$l getPitch] width [$l getWidth]" } }
# PDN shapes summary
foreach net [$block getNets] {
    if { [$net getSigType] ne "POWER" && [$net getSigType] ne "GROUND" } { continue }
    array unset cntl
    foreach sw [$net getSWires] { foreach sb [$sw getWires] { if { [$sb isVia] } { continue } ; set k "[[$sb getTechLayer] getName] [expr {[$sb getDX] > [$sb getDY] ? "H" : "V"}] w=[expr {min([$sb getDX],[$sb getDY])/double($dbu)}]"; if { ![info exists cntl($k)] } { set cntl($k) 0 } ; incr cntl($k) } }
    foreach k [lsort [array names cntl]] { puts "PDN [$net getName] $k n=$cntl($k)" }
}
exit 0
