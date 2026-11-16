* ==============================================================================
* Dregg-180 Foundry BSIM4 Characterization Deck 4:
*   Simultaneous Switching Noise (SSN / L*di/dt Ground Bounce & VDD Droop) on
*   wafer.space GF180MCU SLOT_0P5X0P5 (4 VDD + 4 VSS Bondwires + On-Die fillcap_16
*   + 4 x 100nF 0402 X7R ESL=0.4nH + 8 Simultaneous bi_24t Drivers + Victim in_s!)
*
* Foundry PDK: GlobalFoundries 180nm (gf180mcuD, 5.0V 7-track mcu7t5v0 + fd_io)
* Parameters swept by run_all_spice.py:
*   - Corner: SS (125 C, 4.50 V), TT (25 C, 5.00 V), FF (-40 C, 5.50 V)
*   - Slew:   slew_sel = 1 (SL=1 Slow Slew, Production Default) vs
*             slew_sel = 0 (SL=0 Fast Slew, Worst-Case SSN Stress)
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.param vdd_val=5.00
.param slew_sel=1
.param cap_nmos_06v0_corner=1
.temp 27
* __CORNER_END__

.include "moscap_with_esr.inc"
.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.include "/spice/pdk/gf180mcu_fd_io.spice"

.options klu method=gear reltol=1e-4

* ------------------------------------------------------------------------------
* 1. External PCB 5V0 Plane + 4 x 100 nF 0402 X7R Decoupling Ring (ESL=0.4nH, ESR=30mOhm)
* ------------------------------------------------------------------------------
VVDD_REG VDD_REG 0 {vdd_val}
R_PLANE  VDD_REG VDD_PCB 15m
L_PLANE  VDD_PCB VDD_RING_PCB 0.6n

* 4 local 0402 100nF X7R caps placed < 1.5mm from South, East, North, West VDD/VSS pin pairs
R_C0402_S VDD_RING_PCB C_S1 30m
L_C0402_S C_S1         C_S2 0.4n
C_0402_S  C_S2         0    100n

R_C0402_E VDD_RING_PCB C_E1 30m
L_C0402_E C_E1         C_E2 0.4n
C_0402_E  C_E2         0    100n

R_C0402_N VDD_RING_PCB C_N1 30m
L_C0402_N C_N1         C_N2 0.4n
C_0402_N  C_N2         0    100n

R_C0402_W VDD_RING_PCB C_W1 30m
L_C0402_W C_W1         C_W2 0.4n
C_0402_W  C_W2         0    100n

* ------------------------------------------------------------------------------
* 2. Exact SLOT_0P5X0P5 4 VDD + 4 VSS Bondwires (1.8 nH, 125 mOhm each) & Padring
*    South: dvdd_pads[0] / dvss_pads[0]
*    East:  dvdd_pads[1] / dvss_pads[1]
*    North: dvdd_pads[2] / dvss_pads[2]
*    West:  vdd_pads[0]  / vss_pads[0]
*    Note: In gf180mcu_fd_io, DVDD==VDD and DVSS==VSS on the padring!
* ------------------------------------------------------------------------------
* Zero-volt current ammeters on the 4 VSS bondwires to measure total di/dt!
V_IS_S 0 GND_S0 0
R_BWS_VSS GND_S0 BWS_VSS1 125m
L_BWS_VSS BWS_VSS1 VSS_SOUTH 1.8n

V_IS_E 0 GND_E0 0
R_BWE_VSS GND_E0 BWE_VSS1 125m
L_BWE_VSS BWE_VSS1 VSS_EAST 1.8n

V_IS_N 0 GND_N0 0
R_BWN_VSS GND_N0 BWN_VSS1 125m
L_BWN_VSS BWN_VSS1 VSS_NORTH 1.8n

V_IS_W 0 GND_W0 0
R_BWW_VSS GND_W0 BWW_VSS1 125m
L_BWW_VSS BWW_VSS1 VSS_WEST 1.8n

* 4 VDD bondwires (1.8 nH, 125 mOhm each)
R_BWS_VDD VDD_RING_PCB BWS_VDD1 125m
L_BWS_VDD BWS_VDD1 VDD_SOUTH 1.8n

R_BWE_VDD VDD_RING_PCB BWE_VDD1 125m
L_BWE_VDD BWE_VDD1 VDD_EAST 1.8n

R_BWN_VDD VDD_RING_PCB BWN_VDD1 125m
L_BWN_VDD BWN_VDD1 VDD_NORTH 1.8n

R_BWW_VDD VDD_RING_PCB BWW_VDD1 125m
L_BWW_VDD BWW_VDD1 VDD_WEST 1.8n

* Padring rail sheet resistance segments (~0.15 Ohm per side) + core PDN grid (~0.08 Ohm)
R_RING_SE_VDD VDD_SOUTH VDD_EAST  0.15
R_RING_EN_VDD VDD_EAST  VDD_NORTH 0.15
R_RING_NW_VDD VDD_NORTH VDD_WEST  0.15
R_RING_WS_VDD VDD_WEST  VDD_SOUTH 0.15

R_RING_SE_VSS VSS_SOUTH VSS_EAST  0.15
R_RING_EN_VSS VSS_EAST  VSS_NORTH 0.15
R_RING_NW_VSS VSS_NORTH VSS_WEST  0.15
R_RING_WS_VSS VSS_WEST  VSS_SOUTH 0.15

* Core power grid tied to all 4 sides via Metal4/Metal5 PDN straps
R_GRID_S_VDD VDD_SOUTH VDD_CORE 0.12
R_GRID_E_VDD VDD_EAST  VDD_CORE 0.12
R_GRID_N_VDD VDD_NORTH VDD_CORE 0.12
R_GRID_W_VDD VDD_WEST  VDD_CORE 0.12

R_GRID_S_VSS VSS_SOUTH VSS_CORE 0.12
R_GRID_E_VSS VSS_EAST  VSS_CORE 0.12
R_GRID_N_VSS VSS_NORTH VSS_CORE 0.12
R_GRID_W_VSS VSS_WEST  VSS_CORE 0.12

* QFN-64 Die Backside Substrate Capacitance to Grounded EPAD (~12 pF across 25um epoxy)
C_SUB_EPAD VSS_CORE 0 12.0p

* Foundry IO ESD rail clamps (separated by 20 mOhm padring segments)
R_CL_SD VDD_SOUTH DVDD_CLS 20m
R_CL_SS VSS_SOUTH DVSS_CLS 20m
X_DVDD_S DVDD_CLS DVSS_CLS VSS_CORE gf180mcu_fd_io__dvdd
R_CL_SD2 VDD_SOUTH DVDD_CLS2 20m
R_CL_SS2 VSS_SOUTH DVSS_CLS2 20m
X_DVSS_S DVDD_CLS2 DVSS_CLS2 VDD_CORE gf180mcu_fd_io__dvss
R_CL_ED VDD_EAST  DVDD_CLE 20m
R_CL_ES VSS_EAST  DVSS_CLE 20m
X_DVDD_E DVDD_CLE DVSS_CLE VSS_CORE gf180mcu_fd_io__dvdd
R_CL_ED2 VDD_EAST  DVDD_CLE2 20m
R_CL_ES2 VSS_EAST  DVSS_CLE2 20m
X_DVSS_E DVDD_CLE2 DVSS_CLE2 VDD_CORE gf180mcu_fd_io__dvss

* ------------------------------------------------------------------------------
* 3. Real Foundry On-Die MOS Decoupling: gf180mcu_fd_sc_mcu7t5v0__fillcap_16
*    1.8 nF design allocation (lumped 450 pF/quadrant) plus four foundry
*    fillcap_16 witnesses. Final extracted capacitance/area must replace allocation.
* ------------------------------------------------------------------------------
X_FCAP_Q0 VDD_CORE VDD_CORE VSS_CORE VSS_CORE gf180mcu_fd_sc_mcu7t5v0__fillcap_16
X_FCAP_Q1 VDD_SOUTH VDD_SOUTH VSS_SOUTH VSS_SOUTH gf180mcu_fd_sc_mcu7t5v0__fillcap_16
X_FCAP_Q2 VDD_EAST  VDD_EAST  VSS_EAST  VSS_EAST  gf180mcu_fd_sc_mcu7t5v0__fillcap_16
X_FCAP_Q3 VDD_WEST  VDD_WEST  VSS_WEST  VSS_WEST  gf180mcu_fd_sc_mcu7t5v0__fillcap_16

* 1.8 nF fillcap budget, finite 50 mOhm local access ESR per quadrant.
R_DC0 VDD_CORE DC0 50m
C_DC0 DC0 VSS_CORE 450p
R_DC1 VDD_SOUTH DC1 50m
C_DC1 DC1 VSS_SOUTH 450p
R_DC2 VDD_EAST DC2 50m
C_DC2 DC2 VSS_EAST 450p
R_DC3 VDD_WEST DC3 50m
C_DC3 DC3 VSS_WEST 450p
* Third DVDD/DVSS pair (north); west is the core VDD/VSS bond pair.
X_DVDD_N VDD_NORTH VSS_NORTH VSS_CORE gf180mcu_fd_io__dvdd
X_DVSS_N VDD_NORTH VSS_NORTH VDD_CORE gf180mcu_fd_io__dvss
* 20 -> 120 mA core switching burst, 1ns edges, in addition to actual pad loads.
I_CORE VDD_CORE VSS_CORE PULSE(20m 120m 6n 1n 1n 10n 30n)
C_PKG_VDD VDD_CORE 0 2p
C_PKG_VSS VSS_CORE 0 2p

* ------------------------------------------------------------------------------
* 4. 8 Simultaneous OSPI DQ[7:0] / TX_DATA[7:0] bi_24t Drivers (South/East Bank!)
*    All 8 switch HIGH -> LOW at t = 6.0 ns (Ground Bounce!) and LOW -> HIGH at t = 18.0 ns
* ------------------------------------------------------------------------------
V_DRV_DATA DRV_RAW 0 PULSE({vdd_val} 0 6.0n 0.20n 0.20n 12.0n 30.0n)
* Real CMOS core buffer driving bidir_sl on VDD_CORE / VSS_CORE rails!
V_SL_DC    SL_DC_IN 0 {slew_sel * vdd_val}
X_SL_BUF   SL_DC_IN SL_NET VDD_CORE VDD_CORE VSS_CORE VSS_CORE gf180mcu_fd_sc_mcu7t5v0__buf_4

.subckt ssn_bi24t_lane a_in sl_in dvdd_bank dvss_bank vdd_c vss_c pcb_load_node
X_DRV_BUF a_in a_buf vdd_c vdd_c vss_c vss_c gf180mcu_fd_sc_mcu7t5v0__buf_4
R_PR_D    dvdd_bank dvdd_loc 15m
R_PR_S    dvss_bank dvss_loc 15m
* bi_24t: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y
X_BI24T   a_buf vss_c dvdd_loc dvss_loc vss_c vdd_c pad_die vss_c vss_c sl_in vdd_c vss_c y_unused gf180mcu_fd_io__bi_24t
L_BW      pad_die bw_mid 1.8n
R_BW      bw_mid  pcb_pin 125m
C_PKG_PAD pcb_pin 0 0.5p
* PCB source termination, also specified by the reference SPI schematic.
R_PCB_SER pcb_pin pcb_load_node 33
C_PCB     pcb_load_node 0 15.0p
.ends ssn_bi24t_lane

* bidir[0..6] on PAD_SOUTH + bidir[7] on PAD_EAST (exact OSPI DQ[7:0] physical placement!)
X_DQ0 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB0 ssn_bi24t_lane
X_DQ1 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB1 ssn_bi24t_lane
X_DQ2 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB2 ssn_bi24t_lane
X_DQ3 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB3 ssn_bi24t_lane
X_DQ4 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB4 ssn_bi24t_lane
X_DQ5 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB5 ssn_bi24t_lane
X_DQ6 DRV_RAW SL_NET VDD_SOUTH VSS_SOUTH VDD_CORE VSS_CORE DQ_PCB6 ssn_bi24t_lane
X_DQ7 DRV_RAW SL_NET VDD_EAST  VSS_EAST  VDD_CORE VSS_CORE DQ_PCB7 ssn_bi24t_lane

* ------------------------------------------------------------------------------
* 5. Quiet Victim Clock Inputs right on PAD_SOUTH (clk_pad = gf180mcu_fd_io__in_s!)
*    Notice in slot_0p5x0p5.yaml: clk_pad sits on PAD_SOUTH right next to bidir[0..6]!
* ------------------------------------------------------------------------------
* Victim A: clk_pad held IDLE LOW (0.0 V external PCB GND) during 8-lane SSN blast
R_CLK_LO 0        CLK_LO_BW 125m
L_CLK_LO CLK_LO_BW CLK_LO_PAD 1.8n
R_PR_VLO_D VDD_SOUTH DVDD_VLO 20m
R_PR_VLO_S VSS_SOUTH DVSS_VLO 20m
* gf180mcu_fd_io__in_s: DVDD DVSS PAD PD PU VDD VSS Y
X_VIC_CLK_LO DVDD_VLO DVSS_VLO CLK_LO_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_LO_Y gf180mcu_fd_io__in_s
X_VIC_LOAD0  CLK_LO_Y  CLK_LO_BUF VDD_CORE VDD_CORE VSS_CORE VSS_CORE gf180mcu_fd_sc_mcu7t5v0__clkbuf_2

* Victim B: clk_pad held at worst-case noisy V_IL = 0.55 V external DC bias!
V_BIAS_600M  V_600M 0 0.55
R_CLK_600M   V_600M CLK_600M_BW 125m
L_CLK_600M   CLK_600M_BW CLK_600M_PAD 1.8n
R_PR_V60_D   VDD_SOUTH DVDD_V60 20m
R_PR_V60_S   VSS_SOUTH DVSS_V60 20m
X_VIC_CLK_600M DVDD_V60 DVSS_V60 CLK_600M_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_600M_Y gf180mcu_fd_io__in_s

* Victim C: clk_pad held IDLE HIGH (VDD_REG) during 8-lane 0->1 VDD droop blast!
R_CLK_HI VDD_REG   CLK_HI_BW 125m
L_CLK_HI CLK_HI_BW CLK_HI_PAD 1.8n
R_PR_VHI_D VDD_SOUTH DVDD_VHI 20m
R_PR_VHI_S VSS_SOUTH DVSS_VHI 20m
X_VIC_CLK_HI DVDD_VHI DVSS_VHI CLK_HI_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_HI_Y gf180mcu_fd_io__in_s

* Initial DC guesses only; nodes remain solved by KCL (not forced voltages).
.nodeset v(VDD_CORE)={vdd_val} v(VDD_SOUTH)={vdd_val}
+ v(VDD_EAST)={vdd_val} v(VDD_NORTH)={vdd_val} v(VDD_WEST)={vdd_val}
+ v(VSS_CORE)=0 v(VSS_SOUTH)=0 v(VSS_EAST)=0 v(VSS_NORTH)=0 v(VSS_WEST)=0
* Seed the powered, settled ESD RC ladder; .nodeset is released for the
* actual operating-point solve and transient. No node is voltage-clamped.
.nodeset v(X_DVDD_S.n8)={vdd_val}
.nodeset v(X_DVDD_S.n11)={vdd_val}
.nodeset v(X_DVDD_S.n10)={vdd_val}
.nodeset v(X_DVDD_S.n19)={vdd_val}
.nodeset v(X_DVDD_S.n21)={vdd_val}
.nodeset v(X_DVDD_S.n17)={vdd_val}
.nodeset v(X_DVDD_S.n20)={vdd_val}
.nodeset v(X_DVDD_S.n22)={vdd_val}
.nodeset v(X_DVDD_S.n18)={vdd_val}
.nodeset v(X_DVDD_S.n13)={vdd_val}
.nodeset v(X_DVDD_S.n12)={vdd_val}
.nodeset v(X_DVDD_S.n15)={vdd_val}
.nodeset v(X_DVDD_S.n6)={vdd_val}
.nodeset v(X_DVDD_S.n7)=0
.nodeset v(X_DVDD_S.n4)=0
.nodeset v(X_DVSS_S.n8)={vdd_val}
.nodeset v(X_DVSS_S.n11)={vdd_val}
.nodeset v(X_DVSS_S.n10)={vdd_val}
.nodeset v(X_DVSS_S.n19)={vdd_val}
.nodeset v(X_DVSS_S.n21)={vdd_val}
.nodeset v(X_DVSS_S.n17)={vdd_val}
.nodeset v(X_DVSS_S.n20)={vdd_val}
.nodeset v(X_DVSS_S.n22)={vdd_val}
.nodeset v(X_DVSS_S.n18)={vdd_val}
.nodeset v(X_DVSS_S.n13)={vdd_val}
.nodeset v(X_DVSS_S.n12)={vdd_val}
.nodeset v(X_DVSS_S.n15)={vdd_val}
.nodeset v(X_DVSS_S.n6)={vdd_val}
.nodeset v(X_DVSS_S.n7)=0
.nodeset v(X_DVSS_S.n4)=0
.nodeset v(X_DVDD_E.n8)={vdd_val}
.nodeset v(X_DVDD_E.n11)={vdd_val}
.nodeset v(X_DVDD_E.n10)={vdd_val}
.nodeset v(X_DVDD_E.n19)={vdd_val}
.nodeset v(X_DVDD_E.n21)={vdd_val}
.nodeset v(X_DVDD_E.n17)={vdd_val}
.nodeset v(X_DVDD_E.n20)={vdd_val}
.nodeset v(X_DVDD_E.n22)={vdd_val}
.nodeset v(X_DVDD_E.n18)={vdd_val}
.nodeset v(X_DVDD_E.n13)={vdd_val}
.nodeset v(X_DVDD_E.n12)={vdd_val}
.nodeset v(X_DVDD_E.n15)={vdd_val}
.nodeset v(X_DVDD_E.n6)={vdd_val}
.nodeset v(X_DVDD_E.n7)=0
.nodeset v(X_DVDD_E.n4)=0
.nodeset v(X_DVSS_E.n8)={vdd_val}
.nodeset v(X_DVSS_E.n11)={vdd_val}
.nodeset v(X_DVSS_E.n10)={vdd_val}
.nodeset v(X_DVSS_E.n19)={vdd_val}
.nodeset v(X_DVSS_E.n21)={vdd_val}
.nodeset v(X_DVSS_E.n17)={vdd_val}
.nodeset v(X_DVSS_E.n20)={vdd_val}
.nodeset v(X_DVSS_E.n22)={vdd_val}
.nodeset v(X_DVSS_E.n18)={vdd_val}
.nodeset v(X_DVSS_E.n13)={vdd_val}
.nodeset v(X_DVSS_E.n12)={vdd_val}
.nodeset v(X_DVSS_E.n15)={vdd_val}
.nodeset v(X_DVSS_E.n6)={vdd_val}
.nodeset v(X_DVSS_E.n7)=0
.nodeset v(X_DVSS_E.n4)=0
.nodeset v(X_DVDD_N.n8)={vdd_val}
.nodeset v(X_DVDD_N.n11)={vdd_val}
.nodeset v(X_DVDD_N.n10)={vdd_val}
.nodeset v(X_DVDD_N.n19)={vdd_val}
.nodeset v(X_DVDD_N.n21)={vdd_val}
.nodeset v(X_DVDD_N.n17)={vdd_val}
.nodeset v(X_DVDD_N.n20)={vdd_val}
.nodeset v(X_DVDD_N.n22)={vdd_val}
.nodeset v(X_DVDD_N.n18)={vdd_val}
.nodeset v(X_DVDD_N.n13)={vdd_val}
.nodeset v(X_DVDD_N.n12)={vdd_val}
.nodeset v(X_DVDD_N.n15)={vdd_val}
.nodeset v(X_DVDD_N.n6)={vdd_val}
.nodeset v(X_DVDD_N.n7)=0
.nodeset v(X_DVDD_N.n4)=0
.nodeset v(X_DVSS_N.n8)={vdd_val}
.nodeset v(X_DVSS_N.n11)={vdd_val}
.nodeset v(X_DVSS_N.n10)={vdd_val}
.nodeset v(X_DVSS_N.n19)={vdd_val}
.nodeset v(X_DVSS_N.n21)={vdd_val}
.nodeset v(X_DVSS_N.n17)={vdd_val}
.nodeset v(X_DVSS_N.n20)={vdd_val}
.nodeset v(X_DVSS_N.n22)={vdd_val}
.nodeset v(X_DVSS_N.n18)={vdd_val}
.nodeset v(X_DVSS_N.n13)={vdd_val}
.nodeset v(X_DVSS_N.n12)={vdd_val}
.nodeset v(X_DVSS_N.n15)={vdd_val}
.nodeset v(X_DVSS_N.n6)={vdd_val}
.nodeset v(X_DVSS_N.n7)=0
.nodeset v(X_DVSS_N.n4)=0
.tran 10p 25n

.param vmid='0.5*vdd_val'

* --- Exact Core & Bank Bounce / Droop Measurements ---
.meas tran vss_core_pk     MAX v(VSS_CORE)  FROM=4n TO=15n
.meas tran vss_core_neg    MIN v(VSS_CORE)  FROM=4n TO=15n
.meas tran vss_south_pk    MAX v(VSS_SOUTH) FROM=4n TO=15n
.meas tran vdd_core_min    MIN v(VDD_CORE)  FROM=16n TO=24n
.meas tran vdd_droop_pk    PARAM='vdd_val - vdd_core_min'
.meas tran rail_collapse_min MIN par('v(VDD_CORE) - v(VSS_CORE)') FROM=4n TO=24n

* --- Peak Total Ground Return Current & Output Slew ---
.meas tran i_gnd_tot_pk    MAX par('abs(i(V_IS_S) + i(V_IS_E) + i(V_IS_N) + i(V_IS_W))') FROM=4n TO=15n
.meas tran t_dq0_fall_80_20 TRIG v(DQ_PCB0) VAL='0.8*vdd_val' FALL=1 TARG v(DQ_PCB0) VAL='0.2*vdd_val' FALL=1

* --- Victim Clock Glitch Check (CLK_LO_Y must stay << vmid; CLK_HI_Y must stay >> vmid!) ---
.meas tran vic_clk_lo_max  MAX par('v(CLK_LO_Y) - v(VSS_CORE)')   FROM=2n TO=24n
.meas tran vic_clk_600_max MAX par('v(CLK_600M_Y) - v(VSS_CORE)') FROM=2n TO=24n
.meas tran vic_clk_hi_min  MIN par('v(CLK_HI_Y) - v(VSS_CORE)')   FROM=2n TO=24n

.meas tran pass_bounce PARAM='(vss_south_pk<0.5)*(vss_core_pk<0.5)*(vss_core_neg> -0.5)*(vdd_droop_pk<0.5)'
.meas tran pass_rail PARAM='rail_collapse_min>0.9*vdd_val'
.meas tran pass_victims PARAM='(vic_clk_lo_max<0.2*vdd_val)*(vic_clk_600_max<0.2*vdd_val)*(vic_clk_hi_min>0.8*vdd_val)'
.control
run
quit
.endc
.end
