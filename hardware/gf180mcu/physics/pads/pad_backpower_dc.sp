* Back-powering of an unpowered chip through one bidirectional pad (gf180mcu_fd_io__bi_24t).
* The chip's rails are not driven: DVDD and VDD are tied together (the pad library shorts them in this
* design) and see only a board load RLOAD to ground.  A signal source drives the pad through RSER.
* DC only: the forward path is the pad's upper ESD diode / PMOS driver body diode into DVDD.
* Models: foundry IO cell netlist + sm141064 (typical MOS, diode_typical, res_typical).
* Assumed: RLOAD (what else hangs on the rail), RSER (board series resistor), all control inputs at 0 V.
.include "/spice/pdk/ngspice/design.ngspice"
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.param cap_nmos_06v0_corner=1
.temp 27
* deck-local MOSCAP from ../../spice (the foundry moscap section collides with the MOS libs)
.include "moscap_with_esr.inc"
.include "/spice/pdk/gf180mcu_fd_io.spice"
.options klu gmin=1e-12
VSRC src 0 0
RSER src pad 1
VMP pad padx 0
* pins: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y
XPAD 0 0 rail 0 0 0 padx 0 0 0 rail 0 y gf180mcu_fd_io__bi_24t
RY y 0 10meg
RLOAD rail 0 10k
.control
foreach rl 1meg 10k 1k 100
  foreach rs 1 330 2.2k
    alter rload $rl
    alter rser $rs
    dc VSRC -1.5 5.5 0.5
    echo "CASE rload=$rl rser=$rs"
    print v(src) v(padx) v(rail) i(vmp)
  end
end
.endc
.end
