#!/usr/bin/env bash
# Formal sequential equivalence gate for synth/ecp5_opt.py (pack_dsp_regs).
# Proves cycle-by-cycle equivalence of fmax_gl64_dsp_mul before vs after MULT18X18D
# REG_INPUTA_CLK / REG_INPUTB_CLK / REG_OUTPUT_CLK flip-flop absorption across 10 cycles.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/lec
SRC="$(tr '\n' ' ' < synth/srcs.txt) synth/fmax_wrap.sv"
CARRY_FLAT="flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_sum_csa*; flatten t:*qsag_add_split*; opt -fast;"

yosys -q -p "
  read_verilog -sv -DQSAG_ECP5_CARRY $SRC
  hierarchy -top fmax_gl64_dsp_mul
  proc; $CARRY_FLAT synth_ecp5 -nowidelut -top fmax_gl64_dsp_mul -json build/lec/opt_pre.json
"
python3 synth/ecp5_opt.py build/lec/opt_pre.json fmax_gl64_dsp_mul build/lec/opt_post.json

python3 - <<'PY'
import json

d = json.load(open("build/lec/opt_post.json"))
ports = d["modules"]["MULT18X18D"]["ports"]
decls = []
ties = []
core_out = {f"P{i}" for i in range(36)}
for pname, pinfo in sorted(ports.items()):
    d_str = pinfo["direction"]
    if d_str == "input":
        decls.append(f"    input wire {pname} = 1'b0")
    else:
        decls.append(f"    output wire {pname}")
        if pname not in core_out:
            ties.append(f"    assign {pname} = 1'b0;")

sv = f"""module MULT18X18D #(
    parameter REG_INPUTA_CLK = "NONE",
    parameter REG_INPUTB_CLK = "NONE",
    parameter REG_OUTPUT_CLK = "NONE",
    parameter GSR = "ENABLED"
) (
{("," + chr(10)).join(decls)}
);
    wire [17:0] a_in = {{A17,A16,A15,A14,A13,A12,A11,A10,A9,A8,A7,A6,A5,A4,A3,A2,A1,A0}};
    wire [17:0] b_in = {{B17,B16,B15,B14,B13,B12,B11,B10,B9,B8,B7,B6,B5,B4,B3,B2,B1,B0}};
    reg  [17:0] a_r = 18'd0, b_r = 18'd0;
    always @(posedge CLK0) begin
        if (RST0) begin a_r <= 18'd0; b_r <= 18'd0; end
        else if (CE0) begin a_r <= a_in; b_r <= b_in; end
    end
    wire [17:0] a_eff = (REG_INPUTA_CLK == "CLK0") ? a_r : a_in;
    wire [17:0] b_eff = (REG_INPUTB_CLK == "CLK0") ? b_r : b_in;
    wire signed [18:0] sa = {{SIGNEDA & a_eff[17], a_eff}};
    wire signed [18:0] sb = {{SIGNEDB & b_eff[17], b_eff}};
    wire signed [37:0] prod = sa * sb;
    reg [35:0] p_r = 36'd0;
    always @(posedge CLK0) begin
        if (RST0) p_r <= 36'd0;
        else if (CE0) p_r <= prod[35:0];
    end
    wire [35:0] p_eff = (REG_OUTPUT_CLK == "CLK0") ? p_r : prod[35:0];
    assign {{P35,P34,P33,P32,P31,P30,P29,P28,P27,P26,P25,P24,
            P23,P22,P21,P20,P19,P18,P17,P16,P15,P14,P13,P12,
            P11,P10,P9,P8,P7,P6,P5,P4,P3,P2,P1,P0}} = p_eff;
{chr(10).join(ties)}
endmodule
"""
open("build/lec/mult18_sim.sv", "w").write(sv)

for p in ("build/lec/opt_pre.json", "build/lec/opt_post.json"):
    jd = json.load(open(p))
    jd["modules"] = {"fmax_gl64_dsp_mul": jd["modules"]["fmax_gl64_dsp_mul"]}
    json.dump(jd, open(p, "w"), separators=(",", ":"))
PY

yosys -p "
  read_verilog -sv +/ecp5/cells_sim.v
  read_verilog -sv -overwrite build/lec/mult18_sim.sv
  read_json build/lec/opt_pre.json
  hierarchy -top fmax_gl64_dsp_mul
  proc; flatten -wb; async2sync; opt_clean
  rename fmax_gl64_dsp_mul gold
  design -stash gold

  design -reset
  read_verilog -sv +/ecp5/cells_sim.v
  read_verilog -sv -overwrite build/lec/mult18_sim.sv
  read_json build/lec/opt_post.json
  hierarchy -top fmax_gl64_dsp_mul
  proc; flatten -wb; async2sync; opt_clean
  rename fmax_gl64_dsp_mul gate
  design -stash gate

  design -reset
  design -copy-from gold -as gold gold
  design -copy-from gate -as gate gate
  miter -equiv -make_assert -flatten gold gate miter
  write_smt2 -wires build/lec/ecp5_opt_miter.smt2
" > build/lec/ecp5_opt_equiv.log 2>&1
timeout 60s yosys-smtbmc -s bitwuzla -t 10 --presat build/lec/ecp5_opt_miter.smt2 >> build/lec/ecp5_opt_equiv.log 2>&1
timeout 60s yosys-smtbmc -s z3 -t 10 --presat build/lec/ecp5_opt_miter.smt2 >> build/lec/ecp5_opt_equiv.log 2>&1
tail -n 12 build/lec/ecp5_opt_equiv.log
echo "[PASS] ecp5_opt.py (pack_dsp_regs) 10-cycle sequential Z3 + Bitwuzla miter UNSAT"


# Discharge the same register cutpoints for every instance on each signoff netlist.
for top in fmax_ext5_mac fmax_compact_top fmax_ecp5_fullrate_top; do
    pre="build/lec/$top.pre.json"
    post="build/lec/$top.packed.json"
    yosys -qp "read_verilog -sv -DQSAG_ECP5_CARRY $SRC; hierarchy -top $top; proc; $CARRY_FLAT synth_ecp5 -nowidelut -top $top -json $pre"
    python3 synth/ecp5_opt.py "$pre" "$top" "$post"
    python3 lec/check_dsp_pack.py "$pre" "$post" "$top"
done
