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
.temp 25
* __CORNER_END__

* Exact physical BSIM4 6V NMOS gate-oxide capacitor for gf180mcu_fd_io internal rail decaps
.subckt cap_nmos_06v0 1 2 c_length=3e-6 c_width=3e-6 dtemp=0
X_MCAP 2 1 2 2 nfet_06v0 w=c_width l=c_length dtemp=dtemp
.ends cap_nmos_06v0

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.include "/spice/pdk/gf180mcu_fd_io.spice"

.options method=gear reltol=2e-3 vntol=1e-4 abstol=1e-11 gmin=1e-12 cshunt=5e-15

* ------------------------------------------------------------------------------
* 1. External PCB 5V0 Plane + 4 x 100 nF 0402 X7R Decoupling Ring (ESL=0.4nH, ESR=30mOhm)
* ------------------------------------------------------------------------------
VVDD_REG VDD_REG 0 {vdd_val}
R_PLANE  VDD_REG VDD_PCB 15m
L_PLANE  VDD_PCB VDD_RING_PCB 0.6n
RP_PLANE VDD_PCB VDD_RING_PCB 80

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
* 2. Exact SLOT_0P5X0P5 4 VDD + 4 VSS Bondwires (1.8 nH, 80 mOhm each) & Padring
*    South: dvdd_pads[0] / dvss_pads[0]
*    East:  dvdd_pads[1] / dvss_pads[1]
*    North: dvdd_pads[2] / dvss_pads[2]
*    West:  vdd_pads[0]  / vss_pads[0]
*    Note: In gf180mcu_fd_io, DVDD==VDD and DVSS==VSS on the padring!
* ------------------------------------------------------------------------------
* Zero-volt current ammeters on the 4 VSS bondwires to measure total di/dt!
V_IS_S 0 GND_S0 0
R_BWS_VSS GND_S0 BWS_VSS1 80m
L_BWS_VSS BWS_VSS1 VSS_SOUTH 1.8n
RP_BWS_VSS BWS_VSS1 VSS_SOUTH 150

V_IS_E 0 GND_E0 0
R_BWE_VSS GND_E0 BWE_VSS1 80m
L_BWE_VSS BWE_VSS1 VSS_EAST 1.8n
RP_BWE_VSS BWE_VSS1 VSS_EAST 150

V_IS_N 0 GND_N0 0
R_BWN_VSS GND_N0 BWN_VSS1 80m
L_BWN_VSS BWN_VSS1 VSS_NORTH 1.8n
RP_BWN_VSS BWN_VSS1 VSS_NORTH 150

V_IS_W 0 GND_W0 0
R_BWW_VSS GND_W0 BWW_VSS1 80m
L_BWW_VSS BWW_VSS1 VSS_WEST 1.8n
RP_BWW_VSS BWW_VSS1 VSS_WEST 150

* 4 VDD bondwires (1.8 nH, 80 mOhm each)
R_BWS_VDD VDD_RING_PCB BWS_VDD1 80m
L_BWS_VDD BWS_VDD1 VDD_SOUTH 1.8n
RP_BWS_VDD BWS_VDD1 VDD_SOUTH 150

R_BWE_VDD VDD_RING_PCB BWE_VDD1 80m
L_BWE_VDD BWE_VDD1 VDD_EAST 1.8n
RP_BWE_VDD BWE_VDD1 VDD_EAST 150

R_BWN_VDD VDD_RING_PCB BWN_VDD1 80m
L_BWN_VDD BWN_VDD1 VDD_NORTH 1.8n
RP_BWN_VDD BWN_VDD1 VDD_NORTH 150

R_BWW_VDD VDD_RING_PCB BWW_VDD1 80m
L_BWW_VDD BWW_VDD1 VDD_WEST 1.8n
RP_BWW_VDD BWW_VDD1 VDD_WEST 150

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

* Foundry IO ESD rail clamps (1 pair per side)
X_DVDD_S VDD_SOUTH VSS_SOUTH VSS_CORE gf180mcu_fd_io__dvdd
X_DVSS_S VDD_SOUTH VSS_SOUTH VDD_CORE gf180mcu_fd_io__dvss
X_DVDD_E VDD_EAST  VSS_EAST  VSS_CORE gf180mcu_fd_io__dvdd
X_DVSS_E VDD_EAST  VSS_EAST  VDD_CORE gf180mcu_fd_io__dvss

* ------------------------------------------------------------------------------
* 3. Real Foundry On-Die MOS Decoupling: gf180mcu_fd_sc_mcu7t5v0__fillcap_16
*    15,000 x fillcap_16 (~420 pF total in spare core area across 4 quadrants!)
* ------------------------------------------------------------------------------
X_FCAP_Q0 VDD_CORE VDD_CORE VSS_CORE VSS_CORE gf180mcu_fd_sc_mcu7t5v0__fillcap_16 m=3750
X_FCAP_Q1 VDD_SOUTH VDD_SOUTH VSS_SOUTH VSS_SOUTH gf180mcu_fd_sc_mcu7t5v0__fillcap_16 m=3750
X_FCAP_Q2 VDD_EAST  VDD_EAST  VSS_EAST  VSS_EAST  gf180mcu_fd_sc_mcu7t5v0__fillcap_16 m=3750
X_FCAP_Q3 VDD_WEST  VDD_WEST  VSS_WEST  VSS_WEST  gf180mcu_fd_sc_mcu7t5v0__fillcap_16 m=3750

* ------------------------------------------------------------------------------
* 4. 8 Simultaneous OSPI DQ[7:0] / TX_DATA[7:0] bi_24t Drivers (South/East Bank!)
*    All 8 switch HIGH -> LOW at t = 6.0 ns (Ground Bounce!) and LOW -> HIGH at t = 18.0 ns
* ------------------------------------------------------------------------------
V_DRV_DATA DRV_RAW 0 PULSE({vdd_val} 0 6.0n 0.20n 0.20n 12.0n 30.0n)
* Slew control voltage referenced to core rails: slew_sel=1 -> VDD_CORE (slow), 0 -> VSS_CORE (fast)
B_SL_CTRL  SL_NET  0 V = v(VSS_CORE) + {slew_sel} * (v(VDD_CORE) - v(VSS_CORE))

.subckt ssn_bi24t_lane a_in sl_in dvdd_bank dvss_bank vdd_c vss_c pcb_load_node
X_DRV_BUF a_in a_buf vdd_c vdd_c vss_c vss_c gf180mcu_fd_sc_mcu7t5v0__buf_4
R_PR_D    dvdd_bank dvdd_loc 15m
R_PR_S    dvss_bank dvss_loc 15m
* bi_24t: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y
X_BI24T   a_buf vss_c dvdd_loc dvss_loc vss_c vdd_c pad_die vss_c vss_c sl_in vdd_c vss_c y_unused gf180mcu_fd_io__bi_24t
L_BW      pad_die bw_mid 1.8n
RP_BW     pad_die bw_mid 150
R_BW      bw_mid  pcb_load_node 80m
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
R_CLK_LO 0        CLK_LO_BW 80m
L_CLK_LO CLK_LO_BW CLK_LO_PAD 1.8n
RP_CLK_LO CLK_LO_BW CLK_LO_PAD 150
* gf180mcu_fd_io__in_s: DVDD DVSS PAD PD PU VDD VSS Y
X_VIC_CLK_LO VDD_SOUTH VSS_SOUTH CLK_LO_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_LO_Y gf180mcu_fd_io__in_s
X_VIC_LOAD0  CLK_LO_Y  CLK_LO_BUF VDD_CORE VDD_CORE VSS_CORE VSS_CORE gf180mcu_fd_sc_mcu7t5v0__clkbuf_2

* Victim B: clk_pad held at worst-case noisy V_IL = 0.60 V external DC bias!
V_BIAS_600M  V_600M 0 0.60
R_CLK_600M   V_600M CLK_600M_BW 80m
L_CLK_600M   CLK_600M_BW CLK_600M_PAD 1.8n
RP_CLK_600M  CLK_600M_BW CLK_600M_PAD 150
X_VIC_CLK_600M VDD_SOUTH VSS_SOUTH CLK_600M_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_600M_Y gf180mcu_fd_io__in_s

* Victim C: clk_pad held IDLE HIGH (VDD_REG) during 8-lane 0->1 VDD droop blast!
R_CLK_HI VDD_REG   CLK_HI_BW 80m
L_CLK_HI CLK_HI_BW CLK_HI_PAD 1.8n
RP_CLK_HI CLK_HI_BW CLK_HI_PAD 150
X_VIC_CLK_HI VDD_SOUTH VSS_SOUTH CLK_HI_PAD VSS_CORE VSS_CORE VDD_CORE VSS_CORE CLK_HI_Y gf180mcu_fd_io__in_s

* Reference Schmitt Hysteresis Characterizer (isolated clean rail, triangle 0 -> VDD -> 0)
VVDD_REF VDD_REF 0 {vdd_val}
VVSS_REF VSS_REF 0 0.0
V_TRI    PAD_TRI 0 PWL(0 0 15n {vdd_val} 30n 0)
X_SCH_REF VDD_REF VSS_REF PAD_TRI VSS_REF VSS_REF VDD_REF VSS_REF SCH_REF_Y gf180mcu_fd_io__in_s

.tran 10p 30n

.param vmid='0.5*vdd_val'

* --- Exact Core & Bank Bounce / Droop Measurements ---
.meas tran vss_core_pk     MAX v(VSS_CORE)  FROM=4n TO=16n
.meas tran vss_core_neg    MIN v(VSS_CORE)  FROM=4n TO=16n
.meas tran vss_south_pk    MAX v(VSS_SOUTH) FROM=4n TO=16n
.meas tran vdd_core_min    MIN v(VDD_CORE)  FROM=16n TO=28n
.meas tran vdd_droop_pk    PARAM='vdd_val - vdd_core_min'
.meas tran rail_collapse_min MIN par('v(VDD_CORE) - v(VSS_CORE)') FROM=4n TO=28n

* --- Peak Total Ground Return Current & Output Slew ---
.meas tran i_gnd_tot_pk    MAX par('abs(i(V_IS_S) + i(V_IS_E) + i(V_IS_N) + i(V_IS_W))') FROM=4n TO=16n
.meas tran t_dq0_fall_80_20 TRIG v(DQ_PCB0) VAL='0.8*vdd_val' FALL=1 TARG v(DQ_PCB0) VAL='0.2*vdd_val' FALL=1

* --- Foundry in_s Schmitt Trigger Hysteresis Thresholds (VT+, VT-, VH) ---
.meas tran vt_plus         FIND v(PAD_TRI) WHEN v(SCH_REF_Y)=vmid RISE=1
.meas tran vt_minus        FIND v(PAD_TRI) WHEN v(SCH_REF_Y)=vmid FALL=1
.meas tran v_hyst          PARAM='vt_plus - vt_minus'

* --- Victim Clock Glitch Check (CLK_LO_Y must stay << vmid; CLK_HI_Y must stay >> vmid!) ---
.meas tran vic_clk_lo_max  MAX par('v(CLK_LO_Y) - v(VSS_CORE)')   FROM=2n TO=29n
.meas tran vic_clk_600_max MAX par('v(CLK_600M_Y) - v(VSS_CORE)') FROM=2n TO=29n
.meas tran vic_clk_hi_min  MIN par('v(CLK_HI_Y) - v(VSS_CORE)')   FROM=2n TO=29n

.end
