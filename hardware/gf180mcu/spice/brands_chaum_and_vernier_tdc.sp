* ==============================================================================
* Dregg-180 Foundry BSIM4 Characterization Deck 2:
*   1) < 5 ns Speed-of-Light Brands-Chaum Rapid-Bit Pad-to-Pad Turnaround
*      (gf180mcu_fd_io__bi_24t CS=0 + 1.8nH QFN-64 bondwire + mux2_4 + bi_24t SL=0 + 15pF)
*   2) Standard-Cell Vernier TDC (dlya_1 slow vs buf_2 + clkbuf_2 + dffrnq_1 fast)
*   3) Schmitt Input Penalty Witness (CS=1 vs CS=0 on bi_24t) + in_s Thresholds (VT+, VT-)
*
* Foundry PDK: GlobalFoundries 180nm (gf180mcuD, 5.0V 7-track mcu7t5v0 + fd_io)
* Swept across SS (4.5V, 125C), TT (5.0V, 25C), FF (5.5V, -40C) by run_all_spice.py.
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" moscap_typical
.param vdd_val=5.00
.temp 25
* __CORNER_END__

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.include "/spice/pdk/gf180mcu_fd_io.spice"

VVDD VDD 0 {vdd_val}
VVSS VSS 0 0.0

* ==============================================================================
* PART A: Brands-Chaum Rapid-Bit Responder (dregg_distance_tdc.sv + qsag_io_shell.sv)
*   Channel 1 (Non-inverting R0=0, R1=1): CS=0 CMOS input -> mux2_4 -> SL=0 24mA out
*   Channel 2 (Inverting     R0=1, R1=0): CS=0 CMOS input -> mux2_4 -> SL=0 24mA out
*   Channel 3 (Trap Witness  CS=1):       CS=1 Schmitt in -> mux2_4 -> SL=0 24mA out
* ==============================================================================

* External Verifier Challenge Pulse on 50-ohm / SMA port (0 -> VDD -> 0, tr=tf=250ps)
V_CHAL_SRC  CHAL_SRC 0 PULSE(0 {vdd_val} 2.0n 0.25n 0.25n 10.0n 24.0n)
R_SRC_MATCH CHAL_SRC PCB_CHAL 15.0
C_SMA_IN    PCB_CHAL 0        1.2p

* Inbound QFN-64 bondwire (1.8 nH + 80 mOhm) to bidir[13] (DB_CHAL_IN, CS=0, IE=1, OE=0)
R_BW_CIN  PCB_CHAL BW_CIN1 80m
L_BW_CIN  BW_CIN1  PAD_CHAL_DIE 1.8n

* gf180mcu_fd_io__bi_24t pin order: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y
X_PAD_CHAL VSS VSS VDD VSS VDD VSS PAD_CHAL_DIE VSS VSS VDD VDD VSS DB_CHAL_Y gf180mcu_fd_io__bi_24t

* Short 30 um Metal2 wire from PAD_EAST[13] to adjacent u_rapid_mux + u_csiso side-tap
R_W_IN   DB_CHAL_Y CHAL_CORE 9.0
C_W_IN   CHAL_CORE VSS       6.0f

* Side-tap isolation buffer u_csiso (exact load on S in dregg_distance_tdc.sv:126!)
X_CSISO     CHAL_CORE     CHAL_SIDE_ISO VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
C_SYNC_LOAD CHAL_SIDE_ISO VSS           8.0f

* Pre-staged R0=0, R1=1 isolation buffers (u_mi0, u_mi1) + u_rapid_mux (mux2_4)
X_MI0       VSS    MUX_I0    VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_MI1       VDD    MUX_I1    VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_RAPID_MUX MUX_I0 MUX_I1 CHAL_CORE MUX_Y_RAW VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__mux2_4

R_W_OUT  MUX_Y_RAW DB_RESP_A 9.0
C_W_OUT  DB_RESP_A VSS       6.0f

* Outbound bidir[14] (DB_RESP_OUT, SL=0 fast slew, OE=1, IE=0 during responder round)
X_PAD_RESP DB_RESP_A VSS VDD VSS VSS VDD PAD_RESP_DIE VSS VSS VSS VDD VSS DB_RESP_Y_UN gf180mcu_fd_io__bi_24t

* Outbound QFN-64 bondwire (1.8 nH + 80 mOhm) + 15 pF PCB/probe load!
L_BW_ROUT  PAD_RESP_DIE BW_ROUT1 1.8n
R_BW_ROUT  BW_ROUT1     PCB_RESP 80m
C_PCB_RESP PCB_RESP     0        15.0p

* --- Channel 2: Inverting Data Polarity (R0=1, R1=0) ---
X_RAPID_MUX_INV MUX_I1 MUX_I0 CHAL_CORE MUX_Y_INV VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__mux2_4
R_W_OUT_I  MUX_Y_INV DB_RESP_A_I 9.0
C_W_OUT_I  DB_RESP_A_I VSS       6.0f
X_PAD_RESP_INV DB_RESP_A_I VSS VDD VSS VSS VDD PAD_RESP_DIE_I VSS VSS VSS VDD VSS DB_RESP_YI_UN gf180mcu_fd_io__bi_24t
L_BW_ROUT_I  PAD_RESP_DIE_I BW_ROUT1_I   1.8n
R_BW_ROUT_I  BW_ROUT1_I     PCB_RESP_INV 80m
C_PCB_RESP_I PCB_RESP_INV   0            15.0p

* --- Channel 3: Trap Witness (CS=1 Schmitt Input Penalty on DB_CHAL_IN) ---
R_BW_CINS  PCB_CHAL BW_CINS1     80m
L_BW_CINS  BW_CINS1 PAD_CHAL_SCH 1.8n
X_PAD_CHAL_SCH VSS VDD VDD VSS VDD VSS PAD_CHAL_SCH VSS VSS VDD VDD VSS DB_CHAL_Y_SCH gf180mcu_fd_io__bi_24t
X_RAPID_MUX_SCH MUX_I0 MUX_I1 DB_CHAL_Y_SCH DB_RESP_A_SCH VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__mux2_4
X_PAD_RESP_SCH DB_RESP_A_SCH VSS VDD VSS VSS VDD PAD_RESP_SCH VSS VSS VSS VDD VSS DB_RESP_YS_UN gf180mcu_fd_io__bi_24t
L_BW_ROUTS  PAD_RESP_SCH BW_ROUTS1    1.8n
R_BW_ROUTS  BW_ROUTS1    PCB_RESP_SCH 80m
C_PCB_RESPS PCB_RESP_SCH 0            15.0p

* --- Reference Schmitt Trigger Threshold Characterizer (gf180mcu_fd_io__in_s) ---
V_TRI     PAD_TRI 0 PWL(0 0 11n {vdd_val} 22n 0)
X_SCH_REF VDD VSS PAD_TRI VSS VSS VDD VSS SCH_REF_Y gf180mcu_fd_io__in_s

* ==============================================================================
* PART B: 14-Stage Vernier Delay Line Slice (dregg_vernier_tdc32 exact cell load)
*   Slow line: dlya_1 + 3fF row wire + dffrnq_1.D pin load
*   Fast line: buf_2  + 3fF row wire + clkbuf_2 -> dffrnq_1.CLK pin load
* ==============================================================================
.subckt vernier_tap s_in s_out f_in f_out q_out tap_rn vdd vss
X_SLOW s_in  s_int vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dlya_1
R_WS   s_int s_out 4.5
C_WS   s_out vss   3.0f
X_FAST f_in  f_int vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_2
R_WF   f_int f_out 4.5
C_WF   f_out vss   3.0f
X_FC   f_out f_clk vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__clkbuf_2
* dffrnq_1: D RN CLK Q VDD VNW VPW VSS
X_FF   s_out tap_rn f_clk q_out vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__dffrnq_1
.ends vernier_tap

V_ARM_RAW TAP_RN_RAW 0 PWL(0 0 1.0n 0 1.3n {vdd_val})
X_RN_BUF  TAP_RN_RAW TAP_RN VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__clkbuf_2

* Launch START at t=3.00 ns, STOP at t=3.65 ns (Delta_T_in = 0.650 ns -> mid-array thermometer transition!)
V_TDC_START TDC_START_RAW 0 PULSE(0 {vdd_val} 3.00n 0.15n 0.15n 18n 40n)
V_TDC_STOP  TDC_STOP_RAW  0 PULSE(0 {vdd_val} 3.65n 0.15n 0.15n 18n 40n)

X_ISTA TDC_START_RAW S0 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2
X_ISTO TDC_STOP_RAW  F0 VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__buf_2

X_VT0  S0  S1  F0  F1  QT0  TAP_RN VDD VSS vernier_tap
X_VT1  S1  S2  F1  F2  QT1  TAP_RN VDD VSS vernier_tap
X_VT2  S2  S3  F2  F3  QT2  TAP_RN VDD VSS vernier_tap
X_VT3  S3  S4  F3  F4  QT3  TAP_RN VDD VSS vernier_tap
X_VT4  S4  S5  F4  F5  QT4  TAP_RN VDD VSS vernier_tap
X_VT5  S5  S6  F5  F6  QT5  TAP_RN VDD VSS vernier_tap
X_VT6  S6  S7  F6  F7  QT6  TAP_RN VDD VSS vernier_tap
X_VT7  S7  S8  F7  F8  QT7  TAP_RN VDD VSS vernier_tap
X_VT8  S8  S9  F8  F9  QT8  TAP_RN VDD VSS vernier_tap
X_VT9  S9  S10 F9  F10 QT9  TAP_RN VDD VSS vernier_tap
X_VT10 S10 S11 F10 F11 QT10 TAP_RN VDD VSS vernier_tap
X_VT11 S11 S12 F11 F12 QT11 TAP_RN VDD VSS vernier_tap
X_VT12 S12 S13 F12 F13 QT12 TAP_RN VDD VSS vernier_tap
X_VT13 S13 S14 F13 F14 QT13 TAP_RN VDD VSS vernier_tap

.tran 10p 22n

.param vmid='0.5*vdd_val'

* --- Brands-Chaum 50% -> 50% Pad-to-Pad Measurements (PCB Pin to PCB Pin w/ 1.8nH + 15pF!) ---
.meas tran t_in_pad_rise    TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(DB_CHAL_Y)    VAL=vmid RISE=1
.meas tran t_mux_core_rise  TRIG v(DB_CHAL_Y)    VAL=vmid RISE=1 TARG v(DB_RESP_A)    VAL=vmid RISE=1
.meas tran t_out_pad_rise   TRIG v(DB_RESP_A)    VAL=vmid RISE=1 TARG v(PCB_RESP)     VAL=vmid RISE=1
.meas tran t_db_rr_total    TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP)     VAL=vmid RISE=1
.meas tran t_db_ff_total    TRIG v(PCB_CHAL)     VAL=vmid FALL=1 TARG v(PCB_RESP)     VAL=vmid FALL=1
.meas tran t_db_rf_inv      TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP_INV) VAL=vmid FALL=1
.meas tran t_db_fr_inv      TRIG v(PCB_CHAL)     VAL=vmid FALL=1 TARG v(PCB_RESP_INV) VAL=vmid RISE=1
.meas tran t_db_schmitt_rr  TRIG v(PCB_CHAL)     VAL=vmid RISE=1 TARG v(PCB_RESP_SCH) VAL=vmid RISE=1

* --- Schmitt Trigger Hysteresis Thresholds (gf180mcu_fd_io__in_s) ---
.meas tran vt_plus          FIND v(PAD_TRI) WHEN v(SCH_REF_Y)=vmid RISE=1
.meas tran vt_minus         FIND v(PAD_TRI) WHEN v(SCH_REF_Y)=vmid FALL=1
.meas tran v_hyst           PARAM='vt_plus - vt_minus'

* --- Vernier TDC Stage Delay & Differential Resolution (stages 2..12 = 10 uniform stages) ---
.meas tran t_slow_10        TRIG v(S2)           VAL=vmid RISE=1 TARG v(S12)          VAL=vmid RISE=1
.meas tran t_fast_10        TRIG v(F2)           VAL=vmid RISE=1 TARG v(F12)          VAL=vmid RISE=1
.meas tran tau_slow         PARAM='t_slow_10/10.0'
.meas tran tau_fast         PARAM='t_fast_10/10.0'
.meas tran delta_tau        PARAM='(t_slow_10 - t_fast_10)/10.0'

* Thermometer capture readout at t = 20 ns (settled)
.meas tran q0_v  FIND v(QT0)  AT=20n
.meas tran q1_v  FIND v(QT1)  AT=20n
.meas tran q2_v  FIND v(QT2)  AT=20n
.meas tran q3_v  FIND v(QT3)  AT=20n
.meas tran q4_v  FIND v(QT4)  AT=20n
.meas tran q5_v  FIND v(QT5)  AT=20n
.meas tran q6_v  FIND v(QT6)  AT=20n
.meas tran q7_v  FIND v(QT7)  AT=20n
.meas tran q8_v  FIND v(QT8)  AT=20n
.meas tran q9_v  FIND v(QT9)  AT=20n
.meas tran q10_v FIND v(QT10) AT=20n
.meas tran q11_v FIND v(QT11) AT=20n

.end
