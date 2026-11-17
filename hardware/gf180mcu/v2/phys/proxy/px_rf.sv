// Dregg-180 v2 register file, 72 rows x 64 bits, written as the array the floorplan places.
// Area proxy and physical-structure proposal (not simulated). Same function as the architecture
// lane's `exp_rf` (one hold register, one ICG per row, one read port); the difference is that every
// cell of the array is instantiated by name so that `floorplan/rf_array.tcl` can put it on a site:
//
//   word row r   (one standard-cell row, full core width):
//       bits 0..31 | u_wen u_cg u_sel (centre column) | bits 32..63
//       bit b = u_lat (latrnq_1, 22 sites) + u_rd (nand2_1, 5 sites): q & row select
//       word lines (horizontal): `gate` (ICG output, 64 latch enables), `sel` (64 nand2 inputs)
//   group k = rows 8k..8k+7, with one combiner row between rows 8k+3 and 8k+4:
//       per column: u_na, u_nb (nand4_1 over four rows each), u_gn (nor2_1) -> gn[k][b], active low
//       centre: u_ckb (clkbuf_4) feeding the eight ICGs of the group
//   column b (vertical, one write bit line and one reset line per column):
//       u_wd (buf_8) drives the write bit line from the hold register,
//       u_rn (buf_4) drives the asynchronous clear of the 72 latches of the column,
//       u_f0..u_f2 (nand3_1) + u_or (or3_1) combine the nine group lines into rd_data[b]
//
// Zeroisation: `srst_n` reaches every latch through u_rnh -> u_rn only; no clock is involved.
`default_nettype none
(* keep_hierarchy *)
module px_rf (
    input  wire        clk,
    input  wire        srst_n,
    input  wire        wr_en,
    input  wire [6:0]  wr_addr,
    input  wire [63:0] wr_data,
    input  wire [6:0]  rd_addr,
    output wire [63:0] rd_data
);
    localparam int ROWS = 72;
    localparam int NG   = 9;

    wire [63:0] hold;
    qsag_ereg #(.W(64)) u_hold (.clk(clk), .rst_n(srst_n), .en(wr_en), .d(wr_data), .q(hold));

    // predecode (ordinary logic, placed by the tool in the centre column's neighbourhood)
    logic [NG-1:0] whi, rhi;
    logic [7:0]    wlo, rlo;
    always_comb begin
        for (int k = 0; k < NG; k++) begin
            whi[k] = wr_en && (wr_addr[6:3] == 4'(k));
            rhi[k] = (rd_addr[6:3] == 4'(k));
        end
        for (int j = 0; j < 8; j++) begin
            wlo[j] = (wr_addr[2:0] == 3'(j));
            rlo[j] = (rd_addr[2:0] == 3'(j));
        end
    end

    wire [63:0]   wbl;                 // write bit lines
    wire [63:0]   rn;                  // per-column clear
    wire [1:0]    rnh;                 // clear, one driver per half
    wire [63:0]   n  [ROWS];           // row-local read gates, active low
    wire [63:0]   gn [NG];             // group lines, active low
    wire [NG-1:0] gck;

    genvar r, b, k, h;
    generate
        for (h = 0; h < 2; h++) begin : g_half
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_8 u_rnh (.I(srst_n), .Z(rnh[h]));
        end
        for (b = 0; b < 64; b++) begin : g_col
            wire f0, f1, f2;
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_8   u_wd (.I(hold[b]), .Z(wbl[b]));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4   u_rn (.I(rnh[b / 32]), .Z(rn[b]));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f0 (.A1(gn[0][b]), .A2(gn[1][b]), .A3(gn[2][b]), .ZN(f0));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f1 (.A1(gn[3][b]), .A2(gn[4][b]), .A3(gn[5][b]), .ZN(f1));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand3_1 u_f2 (.A1(gn[6][b]), .A2(gn[7][b]), .A3(gn[8][b]), .ZN(f2));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__or3_1   u_or (.A1(f0), .A2(f1), .A3(f2), .Z(rd_data[b]));
        end
        for (k = 0; k < NG; k++) begin : g_grp
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_ckb (.I(clk), .Z(gck[k]));
            for (b = 0; b < 64; b++) begin : g_bit
                wire a, bb;
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand4_1 u_na (.A1(n[8*k+0][b]), .A2(n[8*k+1][b]),
                                                                  .A3(n[8*k+2][b]), .A4(n[8*k+3][b]), .ZN(a));
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand4_1 u_nb (.A1(n[8*k+4][b]), .A2(n[8*k+5][b]),
                                                                  .A3(n[8*k+6][b]), .A4(n[8*k+7][b]), .ZN(bb));
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_1  u_gn (.A1(a), .A2(bb), .ZN(gn[k][b]));
            end
        end
        for (r = 0; r < ROWS; r++) begin : g_row
            wire wen, gate, sel;
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_1  u_wen (.A1(whi[r / 8]), .A2(wlo[r % 8]), .Z(wen));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_4 u_cg  (.CLK(gck[r / 8]), .E(wen), .TE(1'b0), .Q(gate));
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__and2_4  u_sel (.A1(rhi[r / 8]), .A2(rlo[r % 8]), .Z(sel));
            for (b = 0; b < 64; b++) begin : g_bit
                wire q;
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (.D(wbl[b]), .E(gate), .RN(rn[b]), .Q(q));
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1  u_rd  (.A1(q), .A2(sel), .ZN(n[r][b]));
            end
        end
    endgenerate
endmodule
`default_nettype wire
