// One Poseidon2 round stage: S-box layer, then linear layer plus addend.
//   KIND 0 : per-cycle selectable (ring core). 12 S-box units; `mid_sel` picks, per token,
//            no S-box (0, the initial M_E), lane 0 only (1, internal round) or all lanes (2).
//   KIND 1 : linear layer M_E only, no S-box, latency P2_LIN_LAT.
//   KIND 2 : external round: 12 S-box units, M_E.
//   KIND 3 : internal round: one S-box unit on lane 0, eleven delay lines, M_I.
// Latency is P2_ROUND_LAT except for KIND 1. `mid_sel`, `lin_mi` and `lin_addend` belong to the
// token that entered P2_SBOX_LAT cycles earlier (KIND 1: the same cycle).
module qsag_p2_round #(
    parameter int KIND = 0,
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic             clk,
    input  logic [767:0]     in_state,
    input  logic [1:0]       mid_sel,
    input  logic             lin_mi,
    input  logic [12*67-1:0] lin_addend,
    output logic [767:0]     out_state
);
    localparam int P2_SBOX_LAT = qsag_ni_pkg::P2_SBOX_LAT;

    logic unused_ok;
    assign unused_ok = &{1'b0, mid_sel, lin_mi};

    logic [767:0] mid;

    if (KIND == 1) begin : g_lin_only
        assign mid = in_state;
    end else begin : g_sbox
        for (genvar i = 0; i < 12; i++) begin : g_lane
            localparam bit USE_SB = (KIND == 0) || (KIND == 2) || (i == 0);
            localparam bit USE_DL = (KIND == 0) || (KIND == 3 && i != 0);
            if (USE_SB) begin : g_sb
                logic [63:0] sb;
                qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (
                    .clk(clk), .x(in_state[64*i +: 64]), .y(sb));
            end
            if (USE_DL) begin : g_dl
                logic [P2_SBOX_LAT*64-1:0] sr;
                logic [63:0]               dl;
                always_ff @(posedge clk)
                    sr <= {sr[(P2_SBOX_LAT-1)*64-1:0], in_state[64*i +: 64]};
                assign dl = sr[(P2_SBOX_LAT-1)*64 +: 64];
            end
            if (USE_SB && USE_DL) begin : g_mux
                if (i == 0) begin : g_l0
                    assign mid[64*i +: 64] = (mid_sel != 2'd0) ? g_sb.sb : g_dl.dl;
                end else begin : g_ln
                    assign mid[64*i +: 64] = (mid_sel == 2'd2) ? g_sb.sb : g_dl.dl;
                end
            end else if (USE_SB) begin : g_fix_sb
                assign mid[64*i +: 64] = g_sb.sb;
            end else begin : g_fix_dl
                assign mid[64*i +: 64] = g_dl.dl;
            end
        end
    end

    qsag_p2_linear #(.FIXED(KIND == 0 ? -1 : (KIND == 3 ? 1 : 0))) u_lin (
        .clk(clk), .x(mid), .mi(lin_mi), .addend(lin_addend), .y(out_state));
endmodule
