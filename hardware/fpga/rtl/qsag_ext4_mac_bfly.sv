// GoldilocksExt4 MAC and radix-2 fold butterfly over a block-RAM table.
//
// Fold (WHIR fold / sumcheck table halving, crates/qsag-agg fold_first_var_in_place_ext4):
//     table[k] <- table[2k] + r * (table[2k+1] - table[2k]),   k = 0 .. n/2 - 1
// The table of 2^TAW entries lives in two simple dual-port block RAMs (even and odd indices),
// both read synchronously, so one butterfly enters the pipeline every clock and the fold is
// in place: result k is written FOLD_LAT clocks after entries 2k, 2k+1 were read, and address
// k/2 of either bank is read before any result that lands on it is written. A round over n
// entries takes n/2 + FOLD_LAT clocks. The last result (n = 2) is also latched in `fold_res`.
//
// The same MAC is offered to the surrounding logic on the `mac_*` port (Horner evaluation of
// sumcheck round polynomials, single products) whenever no fold is running.
// Table entries and operands must be canonical.
module qsag_ext4_mac_bfly #(
    parameter int TAW = 10,
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic           clk,
    input  logic           rst,
    // table load
    input  logic           tw_en,
    input  logic [TAW-1:0] tw_idx,
    input  logic [255:0]   tw_data,
    // fold round
    input  logic           fold_start,
    input  logic [5:0]     fold_log2n,
    input  logic [255:0]   fold_r,
    output logic           fold_busy,
    output logic           fold_done,
    output logic [255:0]   fold_res,
    // shared MAC port: y = a*b + c
    input  logic           mac_valid,
    input  logic [255:0]   mac_a,
    input  logic [255:0]   mac_b,
    input  logic [255:0]   mac_c,
    output logic           mac_done,
    output logic [255:0]   mac_y
);
    localparam logic [63:0] GL_P = qsag_ni_pkg::GL_P;
    localparam int EXT4_MAC_LAT = qsag_ni_pkg::EXT4_MAC_LAT;
    localparam int BAW      = TAW - 1;
    localparam int FOLD_LAT = 2 + EXT4_MAC_LAT;   // RAM read, subtract, MAC

    // Fold control.
    logic [TAW-1:0] k, k_last;
    logic           rd_act;
    logic [255:0]   r_q;

    logic [FOLD_LAT-1:0]     fv_sr;      // butterfly valid
    logic [FOLD_LAT-1:0]     fl_sr;      // last butterfly of the round
    logic [FOLD_LAT*TAW-1:0] fk_sr;      // butterfly index

    always_ff @(posedge clk) begin
        if (rst) begin
            rd_act    <= 1'b0;
            fold_busy <= 1'b0;
            fv_sr     <= '0;
        end else begin
            fv_sr <= {fv_sr[FOLD_LAT-2:0], rd_act};
            if (fold_start && !fold_busy) begin
                rd_act    <= 1'b1;
                fold_busy <= 1'b1;
            end else if (rd_act && k == k_last) begin
                rd_act <= 1'b0;
            end
            if (fold_done) fold_busy <= 1'b0;
        end
        fl_sr <= {fl_sr[FOLD_LAT-2:0], rd_act && (k == k_last)};
        fk_sr <= {fk_sr[(FOLD_LAT-1)*TAW-1:0], k};
        if (fold_start && !fold_busy) begin
            k      <= '0;
            k_last <= TAW'((64'd1 << (fold_log2n - 6'd1)) - 64'd1);
            r_q    <= fold_r;
        end else if (rd_act) begin
            k <= k + TAW'(1);
        end
    end

    // Table banks.
    logic            wr_v;
    logic [TAW-1:0]  wr_k;
    logic [255:0]    ev_rd, od_rd, wr_data;
    logic            bw_en;
    logic [TAW-1:0]  bw_idx;
    assign wr_v   = fv_sr[FOLD_LAT-1];
    assign wr_k   = fk_sr[(FOLD_LAT-1)*TAW +: TAW];
    assign bw_en  = wr_v || tw_en;
    assign bw_idx = wr_v ? wr_k : tw_idx;

    qsag_sdp_bram #(.AW(BAW), .DW(256)) u_even (
        .clk(clk), .we(bw_en && !bw_idx[0]), .wa(bw_idx[TAW-1:1]), .wd(wr_data),
        .ra(k[BAW-1:0]), .rd(ev_rd));
    qsag_sdp_bram #(.AW(BAW), .DW(256)) u_odd (
        .clk(clk), .we(bw_en && bw_idx[0]), .wa(bw_idx[TAW-1:1]), .wd(wr_data),
        .ra(k[BAW-1:0]), .rd(od_rd));

    // d = odd - even (mod p), one stage.
    logic [255:0] d_q, e_q;
    for (genvar i = 0; i < 4; i++) begin : g_sub
        logic [64:0] df;
        assign df = {1'b0, od_rd[64*i +: 64]} - {1'b0, ev_rd[64*i +: 64]};
        always_ff @(posedge clk) d_q[64*i +: 64] <= df[64] ? (df[63:0] + GL_P) : df[63:0];
    end
    always_ff @(posedge clk) e_q <= ev_rd;

    // Shared MAC.
    logic                    f_in;
    logic [EXT4_MAC_LAT-1:0] mv_sr;
    logic [255:0]            ma, mb, mc, my;
    assign f_in = fv_sr[1];
    assign ma = f_in ? r_q : mac_a;
    assign mb = f_in ? d_q : mac_b;
    assign mc = f_in ? e_q : mac_c;
    qsag_ext4_mac #(.AW(AW), .BW(BW)) u_mac (.clk(clk), .a(ma), .b(mb), .c(mc), .y(my));
    always_ff @(posedge clk) begin
        if (rst) mv_sr <= '0;
        else     mv_sr <= {mv_sr[EXT4_MAC_LAT-2:0], mac_valid && !fold_busy};
    end
    assign mac_done = mv_sr[EXT4_MAC_LAT-1];
    assign mac_y    = my;
    assign wr_data  = wr_v ? my : tw_data;

    always_ff @(posedge clk) begin
        if (rst) fold_done <= 1'b0;
        else     fold_done <= wr_v && fl_sr[FOLD_LAT-1];
        if (wr_v) fold_res <= my;
    end
endmodule
