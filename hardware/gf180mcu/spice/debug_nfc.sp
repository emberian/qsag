* 13.56 MHz NFC survival / cold-tap characterization, not an energy harvester.
* Coil calculator: 1.4662uH, Rac=0.988 ohm, Ctotal=93.95pF at 25C.
* 7.5Vpk induced series EMF gives ~134Vpk unloaded linear tank (Q~18).
* Nonlinear rectifier loading is included; do not assume unloaded Q after clamping.
.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.param cap_nmos_06v0_corner=1
.param vdd_val=5.0
.temp 27
* __CORNER_END__
.include "moscap_with_esr.inc"
.include "/spice/pdk/gf180mcu_fd_io.spice"
.options klu method=gear reltol=1e-4
* Board device engineering models, NOT vendor-qualified models. Bounds documented
* in pcb/README.md; replace with selected vendor models before fabrication.
.model SCH D(IS=100n N=1.08 RS=2 CJO=2p VJ=0.4 M=0.33 BV=70 IBV=10u TT=100p)
.model Z47 D(IS=1p N=1.1 RS=5 BV=4.7 IBV=5m CJO=80p)
.model ISO_N NMOS(LEVEL=1 VTO=1.3 KP=0.15 LAMBDA=0.02 RD=2 RS=2)
.model BODY D(IS=1n RS=2 CJO=10p BV=50 IBV=10u)
V_MAIN MAIN 0 {vdd_val}
V_HOT MAIN VDD_HOT 0
* Cold rail held at 0V: worst-case injection into a discharged board bypass.
* Separate senses distinguish foundry upper ESD current from external pullup.
V_COLD 0 VDD_COLD 0
V_BAD 0 VDD_BAD 0
V_EMF EMF 0 SIN(0 7.5 13.56meg)
R_CU EMF LR {0.988*(1+0.00393*(temper-25))}
L_COIL LR LD 1.4662u
R_DAMP LD TANK 4.7
C_SELF TANK 0 1.865p
C_FIXED TANK 0 80p
C_TRIM TANK 0 8.885p
C_STRAY TANK 0 3.2p
R_BLEED TANK 0 12k
* Rectifier is independent of ASIC VDD. Never join RECT to chip 5V directly.
R_RECT TANK RECT_IN 220
D_RECT RECT_IN RECT SCH
D_NEG 0 RECT_IN SCH
C_RECT RECT 0 4.7n
R_RECT_LOAD RECT 0 10k
D_LIMIT 0 RECT Z47
* The RF gate has no conductive path to chip power. Gate-drain capacitance and
* the MOS body diode are explicit, so cold isolation is not an ideal switch.
.subckt isolated_rx tank pullrail pad rect
R_LIMIT tank GATE 2.2k
D_GHI GATE RECT SCH
D_GLO 0 GATE SCH
R_GATE GATE 0 1meg
M_ISO pad GATE 0 0 ISO_N W=1u L=1u
C_GS GATE 0 20p
C_GD GATE pad 2p
D_BODY 0 pad BODY
R_PULL pullrail pad 470
.ends isolated_rx
X_HOT TANK MAIN PAD_HOT RECT isolated_rx
X_COLD TANK 0 PAD_COLD RECT isolated_rx
* Unprotected witness retains the same 2.2k resistor: it alone cannot isolate.
R_BAD TANK PAD_BAD 2.2k
X_PAD_HOT 0 MAIN VDD_HOT 0 MAIN 0 PAD_HOT 0 0 MAIN MAIN 0 Y_HOT gf180mcu_fd_io__bi_24t
X_PAD_COLD 0 0 VDD_COLD 0 0 0 PAD_COLD 0 0 0 0 0 Y_COLD gf180mcu_fd_io__bi_24t
X_PAD_BAD 0 0 VDD_BAD 0 0 0 PAD_BAD 0 0 0 0 0 Y_BAD gf180mcu_fd_io__bi_24t
.save v(TANK) v(RECT) v(PAD_HOT) v(PAD_COLD) v(PAD_BAD) v(Y_HOT) i(V_COLD) i(V_BAD) v(X_HOT.GATE)
.tran 1n 55n 0 100p
.meas tran tank_pk MAX v(TANK) FROM=2u TO=4u
.meas tran rect_max MAX v(RECT) FROM=2u TO=4u
.meas tran gate_max MAX v(X_HOT.GATE) FROM=2u TO=4u
.meas tran hot_max MAX v(PAD_HOT) FROM=2u TO=4u
.meas tran hot_min MIN v(PAD_HOT) FROM=2u TO=4u
.meas tran cold_max MAX v(PAD_COLD) FROM=2u TO=4u
.meas tran cold_min MIN v(PAD_COLD) FROM=2u TO=4u
.meas tran cold_inject_avg AVG par('-i(V_COLD)') FROM=2u TO=4u
.meas tran cold_inject_pk MAX par('-i(V_COLD)') FROM=2u TO=4u
.meas tran bad_inject_avg AVG par('-i(V_BAD)') FROM=2u TO=4u
.meas tran bad_inject_pk MAX par('-i(V_BAD)') FROM=2u TO=4u
.meas tran logic_high MAX v(Y_HOT) FROM=2u TO=4u
.meas tran logic_low MIN v(Y_HOT) FROM=2u TO=4u
.meas tran clk_period TRIG v(Y_HOT) VAL='vdd_val/2' RISE=1 TD=2u TARG v(Y_HOT) VAL='vdd_val/2' RISE=11 TD=2u
.meas tran clk_hz PARAM='10/clk_period'
* Project limits: <1uA average, <100uA peak cold ESD injection, pad within
* [-0.3,VDD+0.3]. These are design goals, not foundry injection-current ratings.
.meas tran pass_cold PARAM='(cold_inject_avg<1u)*(cold_inject_pk<100u)*(cold_max<0.3)*(cold_min> -0.3)'
.meas tran pass_hot PARAM='(hot_max<vdd_val+0.3)*(hot_min> -0.3)*(logic_high>0.8*vdd_val)*(logic_low<0.2*vdd_val)*(clk_hz>13.4e6)*(clk_hz<13.7e6)'
.meas tran pass_rect PARAM='(rect_max<5.5)*(gate_max<10)'
.control
run
wrdata nfc_debug.dat v(TANK) v(PAD_BAD) v(PAD_COLD) v(X_HOT.GATE) v(RECT)
quit
.endc
.end
