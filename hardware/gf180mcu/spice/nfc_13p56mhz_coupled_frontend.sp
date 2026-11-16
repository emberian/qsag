* ==============================================================================
* Dregg-180 Foundry BSIM4 Characterization Deck 1:
*   End-to-End Coupled 13.56 MHz Smartphone/Reader (L1 = 1.00 uH) <->
*   40x40 mm Planar PCB Spiral (L2 = 1.466 uH, Rac = 1.08 Ohm, Q_loaded ~ 18) <->
*   Oxide-Safe Schottky/Zener Limiter + AC-Biased Clock + Envelope Slicer + FDV301N <->
*   Foundry gf180mcu_fd_io__bi_24t Silicon Pads (NFC_CLK_IN, NFC_ASK_IN, NFC_LOAD_MOD)
*
* Swept by run_all_spice.py across:
*   - Coupling k_val in {0.02 (~4.5 cm), 0.08 (~2.0 cm), 0.22 (0.0 cm flush phone tap!)}
*   - Corners: SS (125 C, 4.50 V), TT (25 C, 5.00 V), FF (-40 C, 5.50 V)
* ==============================================================================

.include "/spice/pdk/ngspice/design.ngspice"
* __CORNER_BEGIN__
.lib "/spice/pdk/ngspice/sm141064.ngspice" typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_typical
.lib "/spice/pdk/ngspice/sm141064.ngspice" moscap_typical
.param vdd_val=5.00
.param k_val=0.08
.temp 25
* __CORNER_END__

.include "/spice/pdk/gf180mcu_fd_sc_mcu7t5v0.spice"
.include "/spice/pdk/gf180mcu_fd_io.spice"

* ------------------------------------------------------------------------------
* Discrete Semiconductor Models (PCB BOM Components)
* ------------------------------------------------------------------------------
* Nexperia BAT54 / BAT54S 30V 200mA Schottky Barrier Diode
.model D_BAT54 D(IS=180n RS=2.8 N=1.08 CJO=4.5p VJ=0.38 M=0.36 BV=30 IBV=10u TT=80p)

* Diodes Inc BZT52C5V1 5.1V 500mW Zener Tank Limiter
.model D_ZENER_5V1 D(IS=1.5p RS=1.4 N=1.05 BV=4.95 IBV=5m CJO=38p VJ=0.75 M=0.33)

* Diodes Inc BZT52C4V7 4.7V Clamp Reference Zener (guarantees PAD < 5.4V even at VDD=5.5V FF!)
.model D_ZENER_4V7 D(IS=1.5p RS=1.6 N=1.05 BV=4.55 IBV=5m CJO=40p VJ=0.75 M=0.33)

* Onsemi FDV301N 25V Logic-Level N-Channel Trench MOSFET (isolates bi_24t from RF tank!)
.model M_FDV301N NMOS(LEVEL=1 VTO=0.85 KP=0.38 LAMBDA=0.02 RD=1.1 RS=0.7 CBD=4.5p CBS=4.5p CGSO=10n CGDO=3n)

* Ideal lossless diode for reader testbench RF peak envelope measurement only
.model D_IDEAL_PK D(IS=1e-12 RS=0.1 N=0.15 CJO=0.05p)

* ------------------------------------------------------------------------------
* Chip Power Rails & Dedicated 4.7V Overvoltage Clamp Rail (BZT52C4V7 + 100nF)
* ------------------------------------------------------------------------------
VVDD VDD 0 {vdd_val}
VVSS VSS 0 0.0

* Dedicated 4.7V RF clamp rail biased from VDD via 2.2k + BZT52C4V7 + 100nF bypass:
* Even if VDD = 5.50V (FF corner) and phone blasts k = 0.22 at 0 mm, V_CLAMP_4V7 ~ 4.65V
* so BAT54S clamps PAD_NFC_CLK strictly <= 5.20V (< 5.40V oxide safety ceiling)!
R_ZBIAS   VDD         V_CLAMP_4V7 2.2k
V_IZ4V7   V_CLAMP_4V7 Z4V7_K      0
D_ZCLAMP  0           Z4V7_K      D_ZENER_4V7
C_ZBYP    V_CLAMP_4V7 0           100n

* ==============================================================================
* PART A: Secondary Loaded Tank Resonance & Q_loaded Bandwidth Check (8..20 MHz)
*   Intrinsic loaded Dregg-180 secondary tank (weak loose-probe excitation k=0.005
*   matching VNA S11/S21 bench ring-probe test per NXP AN1445):
*   L2 = 1.4662 uH, Rac = 1.08 Ohm, Cself = 1.87 pF, Rdamp = 4.70 Ohm,
*   Ctune = 80.0 pF (68pF + 12pF C0G ±1%) + Ctrim = 8.89 pF + Cpar = 3.20 pF,
*   R_load_eq = 12 kOhm -> f0 = 13.56 MHz, Q_loaded = 17.8 in [15, 22], BW = 762 kHz!
* ==============================================================================
V_AC_SRC  AC_RDR_SRC 0 DC 0 AC 1.0
R_AC_PA   AC_RDR_SRC AC_RDR_L1 50.0
L1_AC     AC_RDR_L1  0         1.00u
L2_AC     AC_SEC_RAW 0         1.4662u
K_AC      L1_AC      L2_AC     0.005
C_SELF_AC AC_SEC_RAW 0         1.87p
R_COIL_AC AC_SEC_RAW AC_SEC_D  1.08
R_DAMP_AC AC_SEC_D   AC_TANK   4.70
C_TUNE_AC AC_TANK    0         80.0p
C_TRIM_AC AC_TANK    0         8.89p
C_PAR_AC  AC_TANK    0         3.20p
R_LOAD_AC AC_TANK    0         12.0k

* ==============================================================================
* PART B: Full Nonlinear Coupled Transient Front-End + 3x Foundry bi_24t Pads
*   Timeline (0 .. 17.5 us = 237 RF cycles @ 13.56 MHz):
*     0.0 ..  4.8 us : Full CW carrier & adaptive slicer organic settle + k=0.22 OV check
*     5.0 ..  9.72 us: ASK 10% modulation dip (m=10%, env=0.818) — Manchester half-bit (4.72 us)
*     9.72.. 11.5 us : ASK high recovery
*    11.8 .. 17.2 us : Chip -> Reader 847.5 kHz (13.56 MHz / 16) resistive load modulation!
* ==============================================================================
.param f_rf=13.56e6
V_ASK_ENV ASK_ENV 0 PWL(0 1.0 4.95u 1.0 5.05u 0.818 9.67u 0.818 9.77u 1.0 18u 1.0)
B_RDR_PA  RDR_PA  0 V = 18.0 * v(ASK_ENV) * sin(2.0 * 3.141592653589793 * {f_rf} * time)

R_RDR_OUT RDR_PA     RDR_C1_IN  15.0
C_RDR_T1  RDR_C1_IN  RDR_L1_TOP 136.5p
R_RDR_L1  RDR_L1_TOP RDR_L1_INT 1.20
L1        RDR_L1_INT 0          1.00u

* Secondary Dregg-180 40x40mm Planar Spiral Tank
L2        SEC_COIL_RAW 0          1.4662u
K_NFC     L1           L2         {k_val}
C_SELF    SEC_COIL_RAW 0          1.87p
R_RAC     SEC_COIL_RAW SEC_DAMP1  1.08
R_DAMP    SEC_DAMP1    AC1        4.70

* Tuning Capacitor Bank (80 pF C0G ±1% + 5.5 pF trimmer accounting for Schottky/FET Cj)
C_TUNE    AC1          0          80.0p
C_TRIM    AC1          0          5.5p
R_BLEED   AC1          0          12.0k

* Half-wave Tank Overvoltage Limiter (BAT54 + BZT52C5V1 + reverse BAT54 substrate guard)
* High-frequency bypass C_RECT_BUF = 4.7nF holds V_RECT smoothly at 5.1V during flush tap!
V_ICLAMP_TANK AC1       AC1_LIM   0
D_TANK_POS    AC1_LIM   V_RECT    D_BAT54
D_TANK_NEG    0         AC1_LIM   D_BAT54
C_RECT_BUF    V_RECT    0         4.7n
R_RECT_BLD    V_RECT    0         10k
D_ZENER_TANK  0         V_RECT    D_ZENER_5V1

* ------------------------------------------------------------------------------
* Path 1: 13.56 MHz Carrier Clock Recovery -> gf180mcu_fd_io__bi_24t[NFC_CLK_IN] (CS=1 Schmitt!)
*   AC-coupled + DC-biased at 0.32 * VDD (~1.60 V = exact center of [VT-=0.74V, VT+=2.43V]!)
*   with 680 Ohm series current limiter + BAT54S clamp to 4.7V Zener rail & GND!
* ------------------------------------------------------------------------------
C_CLK_AC  AC1          CLK_AC_MID  150p
R_CLK_LIM CLK_AC_MID   PAD_NFC_CLK 680.0
R_CLK_BHI VDD          PAD_NFC_CLK 150k
R_CLK_BLO PAD_NFC_CLK  0           70k
C_CLK_RF  PAD_NFC_CLK  0           2.2p
V_ICLK_HI PAD_NFC_CLK  CLK_CLP_HI  0
D_CLK_HI  CLK_CLP_HI   V_CLAMP_4V7 D_BAT54
D_CLK_LO  0            PAD_NFC_CLK D_BAT54

* Foundry bi_24t[NFC_CLK_IN]: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y (CS=1 Schmitt!)
X_PAD_NFC_CLK VSS VDD VDD VSS VDD VSS PAD_NFC_CLK VSS VSS VDD VDD VSS NFC_CLK_Y gf180mcu_fd_io__bi_24t
X_CLK_CORE_BUF NFC_CLK_Y NFC_CLK_CORE VDD VDD VSS VSS gf180mcu_fd_sc_mcu7t5v0__clkbuf_2

* ------------------------------------------------------------------------------
* Path 2: ASK 10% / 100% Envelope Detector (tau = 4.7k * 220pF = 1.034 us) +
*         TLV3201 5V 40ns Slicer -> gf180mcu_fd_io__bi_24t[NFC_ASK_IN] (CS=1 Schmitt!)
* ------------------------------------------------------------------------------
D_ENV     AC1       V_ENV     D_BAT54
R_ENV     V_ENV     0         4.7k
C_ENV     V_ENV     0         220p

* Peak-tracking adaptive slicer reference (D_PK + R_PK=180k || C_PK=150pF -> tau_hold=27us,
* divided by 95.5% resistor ratio R_S1=15k / R_S2=330k -> sits cleanly at -4.3% below CW peak,
* slicing BOTH 10% ASK and 100% ASK right through the eye center from k=0.02 to k=0.22!)
D_REF_PK  AC1       V_PK_HOLD D_BAT54
C_REF_PK  V_PK_HOLD 0         100p
R_REF_S1  V_PK_HOLD V_REF_RAW 18k
R_REF_S2  V_REF_RAW 0         390k
C_REF_FLT V_REF_RAW 0         22p

* TLV3201 5V rail-to-rail comparator (gain=3000, 40 ns propagation delay + 35 Ohm output)
B_CMP_RAW CMP_INT   0 V = {vdd_val} * 0.5 * (1.0 + tanh(400.0 * (v(V_ENV) - v(V_REF_RAW))))
R_CMP_DLY CMP_INT   CMP_DLY   4.0k
C_CMP_DLY CMP_DLY   0         10p
B_CMP_OUT CMP_OUT_V 0 V = {vdd_val} * 0.5 * (1.0 + tanh(40.0 * (v(CMP_DLY) - 0.5*{vdd_val})))
R_CMP_ROUT CMP_OUT_V PAD_NFC_ASK 35.0

* Foundry bi_24t[NFC_ASK_IN]: IE=1, OE=0, CS=1 Schmitt, PU=1
X_PAD_NFC_ASK VSS VDD VDD VSS VDD VSS PAD_NFC_ASK VSS VDD VDD VDD VSS NFC_ASK_Y gf180mcu_fd_io__bi_24t

* ------------------------------------------------------------------------------
* Path 3: Chip -> Reader 847.5 kHz (13.56 MHz / 16, T = 1.17994 us) Load Modulation
*         Core drives bi_24t[NFC_LOAD_MOD] (OE=1, SL=1 slow slew!) -> FDV301N + 220 Ohm shunt
* ------------------------------------------------------------------------------
V_LMOD_CORE LMOD_CORE_A 0 PULSE(0 {vdd_val} 11.8u 2n 2n 0.58997u 1.17994u)

* Foundry bi_24t[NFC_LOAD_MOD]: A CS DVDD DVSS IE OE PAD PD PU SL VDD VSS Y (OE=1, SL=1!)
X_PAD_LMOD LMOD_CORE_A VSS VDD VSS VSS VDD PAD_NFC_LMOD VSS VSS VDD VDD VSS LMOD_Y_UN gf180mcu_fd_io__bi_24t
R_LMOD_PD  PAD_NFC_LMOD 0 100k

* External FDV301N NMOS isolates PAD_NFC_LMOD from AC1 tank voltage completely!
D_SHUNT    AC1            LMOD_SHUNT_TOP D_BAT54
R_MOD      LMOD_SHUNT_TOP LMOD_DRAIN     220.0
M_LMOD     LMOD_DRAIN     PAD_NFC_LMOD 0 0 M_FDV301N

* ------------------------------------------------------------------------------
* Reader Receiver Envelope Probe on Primary Coil Node RDR_L1_TOP (measures backscatter mVpp!)
* ------------------------------------------------------------------------------
D_RDR_PK   RDR_L1_TOP RDR_ENV_PK D_IDEAL_PK
R_RDR_PK   RDR_ENV_PK 0          10k
C_RDR_PK   RDR_ENV_PK 0          22p

.control
* 1. Small-signal AC secondary tank resonance & Q_loaded check
ac lin 2401 8.0e6 20.0e6
meas ac v_ac_pk MAX vm(AC_TANK)
let v_3db = v_ac_pk / sqrt(2.0)
meas ac f_lo_hz  WHEN vm(AC_TANK)=v_3db RISE=1
meas ac f_hi_hz  WHEN vm(AC_TANK)=v_3db FALL=1
let f_res_hz = sqrt(f_lo_hz * f_hi_hz)
let bw_khz = (f_hi_hz - f_lo_hz) * 1e-3
let q_loaded_meas = f_res_hz / (f_hi_hz - f_lo_hz)
let f_res_mhz = f_res_hz * 1e-6
echo "NFC_AC_RES" "$&f_res_mhz" "$&q_loaded_meas" "$&bw_khz"

* 2. Full 17.4 us nonlinear coupled RF + BSIM4 silicon pad transient
tran 5.0n 17.4u
let vmid_v = 0.5 * v(VDD)[10]

* Overvoltage survival on all 3 silicon pads + clamp currents
meas tran v_ac1_pk       MAX v(AC1)           FROM=2.8u TO=4.8u
meas tran v_pad_clk_max  MAX v(PAD_NFC_CLK)   FROM=2.8u TO=17.2u
meas tran v_pad_clk_min  MIN v(PAD_NFC_CLK)   FROM=2.8u TO=17.2u
meas tran v_pad_lmod_max MAX v(PAD_NFC_LMOD)  FROM=2.8u TO=17.2u
meas tran v_pad_ask_max  MAX v(PAD_NFC_ASK)   FROM=2.8u TO=17.2u
meas tran i_clk_clamp_ma MAX i(V_ICLK_HI)     FROM=2.8u TO=4.8u
meas tran i_tank_lim_ma  MAX i(V_ICLAMP_TANK) FROM=2.8u TO=4.8u
let iclk_ma = i_clk_clamp_ma * 1e3
let itank_ma = i_tank_lim_ma * 1e3

* Recovered 13.56 MHz digital clock frequency & duty cycle on bi_24t[NFC_CLK_IN].Y (around t=3..4.8us)
meas tran t_clk_r1  WHEN v(NFC_CLK_Y)=vmid_v RISE=1 TD=3.0u
meas tran t_clk_f1  WHEN v(NFC_CLK_Y)=vmid_v FALL=1 TD=3.0u
meas tran t_clk_r2  WHEN v(NFC_CLK_Y)=vmid_v RISE=2 TD=3.0u
meas tran t_clk_r11 WHEN v(NFC_CLK_Y)=vmid_v RISE=11 TD=3.0u
let f_clk_rec_mhz = 10.0 / (t_clk_r11 - t_clk_r1) * 1e-6
let dt_hi = t_clk_f1 - t_clk_r1
if dt_hi < 0
  meas tran t_clk_f2 WHEN v(NFC_CLK_Y)=vmid_v FALL=2 TD=3.0u
  let dt_hi = t_clk_f2 - t_clk_r1
end
let duty_clk_pct = 100.0 * (dt_hi / (t_clk_r2 - t_clk_r1))

* ASK 10% 105.9 kbps Manchester envelope swing, slicer eye margin & recovered pulse width (target ~4.72 us)
meas tran venv_hi  MAX v(V_ENV)      FROM=3.6u TO=4.8u
meas tran venv_dip MIN v(V_ENV)      FROM=6.8u TO=9.5u
meas tran vref_mid FIND v(V_REF_RAW) AT=8.0u
let ask_env_drop_mv = (venv_hi - venv_dip) * 1e3
let ask_eye_open_mv = min(venv_hi - vref_mid, vref_mid - venv_dip) * 1e3
meas tran t_ask_fall WHEN v(NFC_ASK_Y)=vmid_v FALL=1 TD=4.8u
meas tran t_ask_rise WHEN v(NFC_ASK_Y)=vmid_v RISE=1 TD=6.0u
let ask_pw_us = (t_ask_rise - t_ask_fall) * 1e6

* Chip -> Reader 847.5 kHz load-modulation backscattered amplitude at reader coil (mVpp)
meas tran vrdr_mod_max    MAX v(RDR_ENV_PK) FROM=13.2u TO=17.2u
meas tran vrdr_mod_min    MIN v(RDR_ENV_PK) FROM=13.2u TO=17.2u
meas tran vrdr_cw_rip_max MAX v(RDR_ENV_PK) FROM=3.4u  TO=4.8u
meas tran vrdr_cw_rip_min MIN v(RDR_ENV_PK) FROM=3.4u  TO=4.8u
let bscat_mvpp = ((vrdr_mod_max - vrdr_mod_min) - (vrdr_cw_rip_max - vrdr_cw_rip_min)) * 1e3

echo "NFC_TRAN_OV"   "$&v_ac1_pk" "$&v_pad_clk_max" "$&v_pad_clk_min" "$&v_pad_lmod_max" "$&iclk_ma" "$&itank_ma"
echo "NFC_TRAN_SIG"  "$&f_clk_rec_mhz" "$&duty_clk_pct" "$&ask_env_drop_mv" "$&ask_eye_open_mv" "$&ask_pw_us" "$&bscat_mvpp"
quit
.endc
.end
