* ==============================================================================
* Dregg-180 Foundry BSIM4 Characterization Deck 2:
*   1) < 5 ns Speed-of-Light Brands-Chaum Rapid-Bit Pad-to-Pad Turnaround
*      (gf180mcu_fd_io__bi_24t CS=0 + 1.8nH QFN-64 bondwire + mux2_4 + bi_24t SL=0 + 15pF)
*   2) Standard-Cell Vernier TDC (dlya_1 slow vs buf_2 + clkbuf_2 + dffrsnq_1 fast)
*
* Foundry PDK: GlobalFoundries 180nm (gf180mcuD, 5.0V 7-track mcu7t5v0 + fd_io)
* Default Corner: TT (25 C, 5.00 V). Swept across SS/TT/FF by run_all_spice.py.
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.param vdd_val=5.00
.temp 25
* __CORNER_END__

* Exact physical BSIM4 6V NMOS gate-oxide capacitor for gf180mcu_fd_io internal rail decaps
* (Avoids ngspice-45 bug where m=xx on behavioral tanh C-expr scales internal E-source voltage by m!)
.subckt cap_nmos_06v0 1 2 c_length=3e-6 c_width=3e-6 dtemp=0
X_MCAP 2 1 2 2 nfet_06v0 w=c_width l=c_length dtemp=dtemp
.ends cap_nmos_06v0

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.include "/spice/pdk/gf180mcu_fd_io.spice"

.options method=gear reltol=2e-3 vntol=1e-4 abstol=1e-11 gmin=1e-12 cshunt=5e-15

* ------------------------------------------------------------------------------
* Power Supplies + Adjacent PAD_EAST (dvdd_pads[1] / dvss_pads[1]) Bondwires
*   Note: Production channel has dedicated physical East-bank PDN (1.8 nH + 80 mOhm
*   bondwires + 150 Ohm high-freq bondwire skin/eddy loss + 120 pF core fillcap
*   with 0.15 Ohm poly/channel ESR). Parallel testbench witness channels (inverting
*   polarity & CS=1 Schmitt trap witness) use independent identical PDN rails so
*   testbench-only copies do not artificially triple SSN on the production pad!
* ------------------------------------------------------------------------------
VVDD_EXT VDD_EXT 0 {vdd_val}
VVSS_EXT VSS_EXT 0 0.0

* Production Channel PDN
RL_VDD  VDD_EXT  VDD_N1   80m
LL_VDD  VDD_N1   VDD_CHIP 1.8n
RP_VDD  VDD_N1   VDD_CHIP 150
RL_VSS  VSS_EXT  VSS_N1   80m
LL_VSS  VSS_N1   VSS_CHIP 1.8n
RP_VSS  VSS_N1   VSS_CHIP 150
R_DEC1  VDD_CHIP DEC1_INT 0.15
C_LOCAL_DECAP DEC1_INT VSS_CHIP 120p

* Independent identical PDN for Inverting-Polarity Channel (R0=1, R1=0)
RL_VDDI VDD_EXT   VDDI_N1   80m
LL_VDDI VDDI_N1   VDD_CHIPI 1.8n
RP_VDDI VDDI_N1   VDD_CHIPI 150
RL_VSSI VSS_EXT   VSSI_N1   80m
LL_VSSI VSSI_N1   VSS_CHIPI 1.8n
RP_VSSI VSSI_N1   VSS_CHIPI 150
R_DECI  VDD_CHIPI DECI_INT  0.15
C_DECAPI DECI_INT VSS_CHIPI 120p

* Independent identical PDN for CS=1 Schmitt Trap-Witness Channel
RL_VDDS VDD_EXT   VDDS_N1   80m
LL_VDDS VDDS_N1   VDD_CHIPS 1.8n
RP_VDDS VDDS_N1   VDD_CHIPS 150
RL_VSSS VSS_EXT   VSSS_N1   80m
LL_VSSS VSSS_N1   VSS_CHIPS 1.8n
RP_VSSS VSSS_N1   VSS_CHIPS 150
R_DECS  VDD_CHIPS DECS_INT  0.15
C_DECAPS DECS_INT VSS_CHIPS 120p

* ==============================================================================
* PART A: Brands-Chaum Rapid-Bit Responder (dregg_distance_tdc.sv + qsag_io_shell.sv)
*   Channel 1 (Production): CS=0 CMOS input -> mux2_4 (R0=0, R1=1 & R0=1, R1=0) -> SL=0 24mA out
*   Channel 2 (Trap Witness): CS=1 Schmitt input -> mux2_4 -> SL=0 24mA out
* ==============================================================================

* External Verifier Challenge Pulse on 50-ohm / SMA port (0 -> VDD -> 0, tr=tf=250ps)
V_CHAL_SRC CHAL_SRC 0 PULSE(0 {vdd_val} 4.0n 0.25n 0.25n 12.0n 30.0n)
R_SRC_MATCH CHAL_SRC PCB_CHAL 15
C_SMA_IN    PCB_CHAL 0        1.2p

* Inbound QFN-64 bondwire (1.8 nH + 80 mOhm) to bidir[13] (DB_CHAL_IN, CS=0)
R_BW_CIN   PCB_CHAL BW_CIN1 80m
L_BW_CIN   BW_CIN1  PAD_CHAL_DIE 1.8n
RP_BW_CIN  BW_CIN1  PAD_CHAL_DIE 150
* 75 um padring rail resistance from dvdd[1]/dvss[1] to bidir[13]
R_PR_VDD13 VDD_CHIP DVDD_P13 30m
R_PR_VSS13 VSS_CHIP DVSS_P13 30m

*gf180mcu_fd_io__bi_24t pin order: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y
X_PAD_CHAL VSS_CHIP VSS_CHIP DVDD_P13 DVSS_P13 VDD_CHIP VSS_CHIP PAD_CHAL_DIE VDD_CHIP VSS_CHIP VDD_CHIP VDD_CHIP VSS_CHIP DB_CHAL_Y gf180mcu_fd_io__bi_24t

* Short 30 um Metal2 wire from PAD_EAST[13] to adjacent u_rapid_mux + u_csiso side-tap
R_W_IN   DB_CHAL_Y CHAL_CORE 9.0
C_W_IN   CHAL_CORE VSS_CHIP  6.0f

* Side-tap isolation buffer u_csiso (prevents RSZ-3006 and models real load on S!)
X_CSISO  CHAL_CORE CHAL_SIDE_ISO VDD_CHIP VDD_CHIP VSS_CHIP VSS_CHIP gf180mcu_fd_sc_mcu7t5v0__buf_2
C_SYNC_LOAD CHAL_SIDE_ISO VSS_CHIP 8.0f

* Pre-staged R0=0, R1=1 isolation buffers (u_mi0, u_mi1) + u_rapid_mux (mux2_4)
X_MI0    VSS_CHIP MUX_I0 VDD_CHIP VDD_CHIP VSS_CHIP VSS_CHIP gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MI1    VDD_CHIP MUX_I1 VDD_CHIP VDD_CHIP VSS_CHIP VSS_CHIP gf180mcu_fd_sc_mcu7t5v0__buf_2
X_RAPID_MUX MUX_I0 MUX_I1 CHAL_CORE MUX_Y_RAW VDD_CHIP VDD_CHIP VSS_CHIP VSS_CHIP gf180mcu_fd_sc_mcu7t5v0__mux2_4

R_W_OUT  MUX_Y_RAW DB_RESP_A 9.0
C_W_OUT  DB_RESP_A VSS_CHIP  6.0f

* Outbound bidir[14] (DB_RESP_OUT, SL=0 fast slew, OE=1, IE=1 loopback active)
R_PR_VDD14 VDD_CHIP DVDD_P14 20m
R_PR_VSS14 VSS_CHIP DVSS_P14 20m
X_PAD_RESP DB_RESP_A VSS_CHIP DVDD_P14 DVSS_P14 VDD_CHIP VDD_CHIP PAD_RESP_DIE VSS_CHIP VSS_CHIP VSS_CHIP VDD_CHIP VSS_CHIP DB_RESP_LB_Y gf180mcu_fd_io__bi_24t

* Outbound QFN-64 bondwire (1.8 nH + 80 mOhm) + 15 pF PCB/probe load!
L_BW_ROUT  PAD_RESP_DIE BW_ROUT1 1.8n
RP_BW_ROUT PAD_RESP_DIE BW_ROUT1 150
R_BW_ROUT  BW_ROUT1     PCB_RESP 80m
C_PCB_RESP PCB_RESP     0        15.0p

* --- Second Responder Channel: Inverting Data Polarity (R0=1, R1=0) ---
R_BW_CINI   PCB_CHAL BW_CINI1 80m
L_BW_CINI   BW_CINI1 PAD_CHAL_DIEI 1.8n
RP_BW_CINI  BW_CINI1 PAD_CHAL_DIEI 150
R_PR_VDD13I VDD_CHIPI DVDD_P13I 30m
R_PR_VSS13I VSS_CHIPI DVSS_P13I 30m
X_PAD_CHALI VSS_CHIPI VSS_CHIPI DVDD_P13I DVSS_P13I VDD_CHIPI VSS_CHIPI PAD_CHAL_DIEI VDD_CHIPI VSS_CHIPI VDD_CHIPI VDD_CHIPI VSS_CHIPI DB_CHAL_YI gf180mcu_fd_io__bi_24t
X_MI0I VSS_CHIPI MUX_I0I VDD_CHIPI VDD_CHIPI VSS_CHIPI VSS_CHIPI gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MI1I VDD_CHIPI MUX_I1I VDD_CHIPI VDD_CHIPI VSS_CHIPI VSS_CHIPI gf180mcu_fd_sc_mcu7t5v0__buf_2
X_RAPID_MUX_INV MUX_I1I MUX_I0I DB_CHAL_YI MUX_Y_INV VDD_CHIPI VDD_CHIPI VSS_CHIPI VSS_CHIPI gf180mcu_fd_sc_mcu7t5v0__mux2_4
R_W_OUT_I MUX_Y_INV DB_RESP_A_I 9.0
C_W_OUT_I DB_RESP_A_I VSS_CHIPI 6.0f
R_PR_VDD14I VDD_CHIPI DVDD_P14I 20m
R_PR_VSS14I VSS_CHIPI DVSS_P14I 20m
X_PAD_RESP_INV DB_RESP_A_I VSS_CHIPI DVDD_P14I DVSS_P14I VDD_CHIPI VDD_CHIPI PAD_RESP_DIE_I VSS_CHIPI VSS_CHIPI VSS_CHIPI VDD_CHIPI VSS_CHIPI DB_RESP_LB_YI gf180mcu_fd_io__bi_24t
L_BW_ROUT_I  PAD_RESP_DIE_I BW_ROUT1_I 1.8n
RP_BW_ROUT_I PAD_RESP_DIE_I BW_ROUT1_I 150
R_BW_ROUT_I  BW_ROUT1_I     PCB_RESP_INV 80m
C_PCB_RESP_I PCB_RESP_INV   0            15.0p

* --- Trap Witness Channel: CS=1 Schmitt Trigger Input Penalty ---
R_BW_CINS   PCB_CHAL BW_CINS1 80m
L_BW_CINS   BW_CINS1 PAD_CHAL_SCH 1.8n
RP_BW_CINS  BW_CINS1 PAD_CHAL_SCH 150
R_PR_VDD13S VDD_CHIPS DVDD_P13S 30m
R_PR_VSS13S VSS_CHIPS DVSS_P13S 30m
X_PAD_CHAL_SCH VSS_CHIPS VDD_CHIPS DVDD_P13S DVSS_P13S VDD_CHIPS VSS_CHIPS PAD_CHAL_SCH VDD_CHIPS VSS_CHIPS VDD_CHIPS VDD_CHIPS VSS_CHIPS DB_CHAL_Y_SCH gf180mcu_fd_io__bi_24t
X_MI0S VSS_CHIPS MUX_I0S VDD_CHIPS VDD_CHIPS VSS_CHIPS VSS_CHIPS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MI1S VDD_CHIPS MUX_I1S VDD_CHIPS VDD_CHIPS VSS_CHIPS VSS_CHIPS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_RAPID_MUX_SCH MUX_I0S MUX_I1S DB_CHAL_Y_SCH DB_RESP_A_SCH VDD_CHIPS VDD_CHIPS VSS_CHIPS VSS_CHIPS gf180mcu_fd_sc_mcu7t5v0__mux2_4
R_PR_VDD14S VDD_CHIPS DVDD_P14S 20m
R_PR_VSS14S VSS_CHIPS DVSS_P14S 20m
X_PAD_RESP_SCH DB_RESP_A_SCH VSS_CHIPS DVDD_P14S DVSS_P14S VDD_CHIPS VDD_CHIPS PAD_RESP_SCH VSS_CHIPS VSS_CHIPS VSS_CHIPS VDD_CHIPS VSS_CHIPS DB_RESP_LBS gf180mcu_fd_io__bi_24t
L_BW_ROUTS  PAD_RESP_SCH BW_ROUTS1 1.8n
RP_BW_ROUTS PAD_RESP_SCH BW_ROUTS1 150
R_BW_ROUTS  BW_ROUTS1    PCB_RESP_SCH 80m
C_PCB_RESPS PCB_RESP_SCH 0            15.0p

* ==============================================================================
* PART B: 16-Stage Vernier Delay Line Slice (dregg_vernier_tdc32 exact cell load)
*   Slow line: dlya_1 + 3fF row wire + dffrsnq_1.D pin load
*   Fast line: buf_2  + 3fF row wire + clkbuf_2 -> dffrsnq_1.CLK pin load
* ==============================================================================
.subckt vernier_tap s_in s_out f_in f_out q_out tap_rn vdd vss
X_SLOW s_in  s_int vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
R_WS   s_int s_out 4.5
C_WS   s_out vss   3.0f
X_FAST f_in  f_int vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_2
R_WF   f_int f_out 4.5
C_WF   f_out vss   3.0f
X_FC   f_out f_clk vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__clkbuf_2
* dffrsnq_1: D RN SETN CLK Q VDD VNW VPW VSS
X_FF   s_out tap_rn vdd f_clk q_out vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dffrsnq_1
.ends vernier_tap

* Clean VDD supply for core TDC characterization (isolating from simultaneous pad switching)
VVDD_TDC VDD_TDC 0 {vdd_val}
VVSS_TDC VSS_TDC 0 0.0
V_ARM_N  TAP_RN  0 PWL(0 0 1.5n 0 1.8n {vdd_val})

* Launch START at t=5.00 ns, STOP at t=6.50 ns (Delta_T_in = 1.500 ns)
V_TDC_START TDC_START_RAW 0 PULSE(0 {vdd_val} 5.00n 0.15n 0.15n 20n 50n)
V_TDC_STOP  TDC_STOP_RAW  0 PULSE(0 {vdd_val} 6.50n 0.15n 0.15n 20n 50n)

X_ISTA TDC_START_RAW S0 VDD_TDC VDD_TDC VSS_TDC VSS_TDC gf180mcu_fd_sc_mcu7t5v0__buf_2
X_ISTO TDC_STOP_RAW  F0 VDD_TDC VDD_TDC VSS_TDC VSS_TDC gf180mcu_fd_sc_mcu7t5v0__buf_2

X_VT0  S0  S1  F0  F1  QT0  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT1  S1  S2  F1  F2  QT1  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT2  S2  S3  F2  F3  QT2  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT3  S3  S4  F3  F4  QT3  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT4  S4  S5  F4  F5  QT4  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT5  S5  S6  F5  F6  QT5  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT6  S6  S7  F6  F7  QT6  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT7  S7  S8  F7  F8  QT7  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT8  S8  S9  F8  F9  QT8  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT9  S9  S10 F9  F10 QT9  TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT10 S10 S11 F10 F11 QT10 TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT11 S11 S12 F11 F12 QT11 TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT12 S12 S13 F12 F13 QT12 TAP_RN VDD_TDC VSS_TDC vernier_tap
X_VT13 S13 S14 F13 F14 QT13 TAP_RN VDD_TDC VSS_TDC vernier_tap

.tran 5p 26n

* --- Brands-Chaum 50% -> 50% Pad-to-Pad Measurements (PCB Pin to PCB Pin w/ 1.8nH + 15pF!) ---
.param vmid='0.5*vdd_val'
.meas tran t_in_pad_rise    TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(DB_CHAL_Y)    VAL=vmid RISE=1
.meas tran t_mux_core_rise  TRIG v(DB_CHAL_Y)    VAL=vmid RISE=1 TARG v(DB_RESP_A)    VAL=vmid RISE=1
.meas tran t_out_pad_rise   TRIG v(DB_RESP_A)    VAL=vmid RISE=1 TARG v(PCB_RESP)     VAL=vmid RISE=1
.meas tran t_db_rr_total    TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP)     VAL=vmid RISE=1
.meas tran t_db_ff_total    TRIG v(PCB_CHAL)     VAL=vmid FALL=1 TARG v(PCB_RESP)     VAL=vmid FALL=1
.meas tran t_db_rf_inv      TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP_INV) VAL=vmid FALL=1
.meas tran t_db_fr_inv      TRIG v(PCB_CHAL)     VAL=vmid FALL=1 TARG v(PCB_RESP_INV) VAL=vmid RISE=1
.meas tran t_db_schmitt_rr  TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP_SCH) VAL=vmid RISE=1
.meas tran t_loopback_start TRIG v(DB_RESP_A)    VAL=vmid RISE=1 TARG v(DB_RESP_LB_Y) VAL=vmid RISE=1

* --- Vernier TDC Stage Delay & Differential Resolution Measurements (stages 2..12 = 10 uniform stages) ---
.meas tran t_slow_10        TRIG v(S2)           VAL=vmid RISE=1 TARG v(S12)          VAL=vmid RISE=1
.meas tran t_fast_10        TRIG v(F2)           VAL=vmid RISE=1 TARG v(F12)          VAL=vmid RISE=1
.meas tran tau_slow         PARAM='t_slow_10/10.0'
.meas tran tau_fast         PARAM='t_fast_10/10.0'
.meas tran delta_tau        PARAM='(t_slow_10 - t_fast_10)/10.0'

* Thermometer capture readout at t = 24 ns (settled)
.meas tran q0_v  FIND v(QT0)  AT=24n
.meas tran q1_v  FIND v(QT1)  AT=24n
.meas tran q2_v  FIND v(QT2)  AT=24n
.meas tran q3_v  FIND v(QT3)  AT=24n
.meas tran q4_v  FIND v(QT4)  AT=24n
.meas tran q5_v  FIND v(QT5)  AT=24n
.meas tran q6_v  FIND v(QT6)  AT=24n
.meas tran q7_v  FIND v(QT7)  AT=24n
.meas tran q8_v  FIND v(QT8)  AT=24n
.meas tran q9_v  FIND v(QT9)  AT=24n
.meas tran q10_v FIND v(QT10) AT=24n
.meas tran q11_v FIND v(QT11) AT=24n

.end
