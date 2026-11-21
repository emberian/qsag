// Hardware Steiner-deduplicated TurboSHAKE256 / cSHAKE256 Merkle-Canopy MultiProof verifier
// (`crates/qsag-agg/src/pcs.rs::verify_canopy_multiproof_byte`).
//
// Enforces in hardware:
//   1. Strict ascending leaf indices within [2^log_leaves, 2^(log_leaves+1) - 1];
//   2. Bottom-up Steiner sibling coalescing (`active[k+1].u == active[k].u ^ 1`);
//   3. Exact authentication sibling consumption (`sib_cursor == num_sibs`, no underflow/surplus);
//   4. Domain-separated internal node framing (`0x00 || parent_u32_le || left || right`) and
//      root commitment framing (`0x01 || log_leaves_u8 || top`) from precomputed static midstates;
//   5. Bit-exact equality against `in_exp_root`.
//
// Profiles:
//   PIPE_12=1, COMPACT_KEC=0 : internal 12-stage pipelined Keccak-p[1600,12] (VU9P_TURBO)
//   PIPE_12=0, COMPACT_KEC=0 : shares top's parallel qsag_keccak_turboshake (XCUP_RING)
//   PIPE_12=0, COMPACT_KEC=1 : shares top's 64-bit lane-sliced qsag_keccak_compact (ECP5_COMPACT)
module qsag_ts_canopy_engine #(
    parameter bit PIPE_12     = 1'b0,
    parameter bit COMPACT_KEC = 1'b0,
    parameter int FRONT_AW    = COMPACT_KEC ? 8 : 9,
    parameter int SIB_AW      = 11
) (
    input  logic                 clk,
    input  logic                 rst,
    // Frontier leaf stream load: {heap_u[31:0], leaf_digest[255:0]}
    input  logic                 tw_front_en,
    input  logic [FRONT_AW-1:0]  tw_front_idx,
    input  logic [31:0]          tw_front_u,
    input  logic [255:0]         tw_front_dig,
    // Auth sibling stream load: 256-bit digest
    input  logic                 tw_sib_en,
    input  logic [SIB_AW-1:0]    tw_sib_idx,
    input  logic [255:0]         tw_sib_dig,
    // Verify command
    input  logic                 start,
    input  logic                 in_turbo,
    input  logic [5:0]           in_log_leaves,
    input  logic [FRONT_AW:0]    in_num_leaves,
    input  logic [SIB_AW:0]      in_num_sibs,
    input  logic [255:0]         in_exp_root,
    output logic                 busy,
    output logic                 done,
    output logic                 ok,
    output logic [255:0]         out_root,
    // Shared parallel Keccak port (used when !COMPACT_KEC && (!PIPE_12 || !turbo || is_root))
    output logic                 kec_start,
    output logic                 kec_nr12,
    output logic [1599:0]        kec_state_o,
    input  logic                 kec_done,
    input  logic [255:0]         kec_digest_i,
    // Shared compact 64-bit Keccak port (used when COMPACT_KEC)
    output logic                 kcmd_valid,
    input  logic                 kcmd_ready,
    output logic [1:0]           kcmd_op,
    output logic                 kcmd_nr12,
    output logic [4:0]           kcmd_idx,
    output logic [63:0]          kcmd_wdata,
    input  logic                 kcmd_done,
    input  logic                 kcmd_rd_valid,
    input  logic [63:0]          kcmd_rd_data
);
    localparam int BAW   = FRONT_AW - 1;
    localparam int PTAGW = FRONT_AW + 32;

    function automatic logic [63:0] canopy_mid(input logic turbo, input logic [4:0] lane);
        if (turbo) begin
            case (lane)
                5'd0:  canopy_mid = 64'h460887f1cba4a839;
                5'd1:  canopy_mid = 64'h980803a3bfc02e65;
                5'd2:  canopy_mid = 64'h68bddb54ef8d20a8;
                5'd3:  canopy_mid = 64'h0b3372687f85bcaf;
                5'd4:  canopy_mid = 64'hcc2727c2077077df;
                5'd5:  canopy_mid = 64'hec41d86c9b5f8d09;
                5'd6:  canopy_mid = 64'hfb5f5d561424cae1;
                5'd7:  canopy_mid = 64'h3268a335444cad6d;
                5'd8:  canopy_mid = 64'h1946744824d4f99b;
                5'd9:  canopy_mid = 64'hf0cc17364abb8f7b;
                5'd10: canopy_mid = 64'h6555bd65801754f9;
                5'd11: canopy_mid = 64'hfb65ea5772915117;
                5'd12: canopy_mid = 64'h7abf03d078f82efa;
                5'd13: canopy_mid = 64'he40b7e6f749e0f48;
                5'd14: canopy_mid = 64'ha878894cf5a786fb;
                5'd15: canopy_mid = 64'haf50e05198f19f90;
                5'd16: canopy_mid = 64'he428425cb9274f77;
                5'd17: canopy_mid = 64'h7cc9afdb9d39179e;
                5'd18: canopy_mid = 64'h68eb6cd4b52d2c93;
                5'd19: canopy_mid = 64'h777f4fb40734c256;
                5'd20: canopy_mid = 64'hb61fe57e44cde167;
                5'd21: canopy_mid = 64'h1f19e1e1f1a15293;
                5'd22: canopy_mid = 64'h6ee7751ca38082bc;
                5'd23: canopy_mid = 64'h1790fc47c8fcf771;
                5'd24: canopy_mid = 64'hd6bf84556451e94d;
                default: canopy_mid = 64'd0;
            endcase
        end else begin
            case (lane)
                5'd0:  canopy_mid = 64'hec954fc7c2fc5381;
                5'd1:  canopy_mid = 64'h36020892bcb1e761;
                5'd2:  canopy_mid = 64'h748dc5bcea037dd5;
                5'd3:  canopy_mid = 64'hfc481597cf683315;
                5'd4:  canopy_mid = 64'h2ec2f3f44f0d3969;
                5'd5:  canopy_mid = 64'h9c0dfc53513c2627;
                5'd6:  canopy_mid = 64'h5415c0edffcd33b8;
                5'd7:  canopy_mid = 64'h403107f0fc877484;
                5'd8:  canopy_mid = 64'h798d84e67c6dafa6;
                5'd9:  canopy_mid = 64'h6e6ea3127d335e8e;
                5'd10: canopy_mid = 64'h5606ea8555392f99;
                5'd11: canopy_mid = 64'hd3bac257bbe1d044;
                5'd12: canopy_mid = 64'h1e5c61027d60223c;
                5'd13: canopy_mid = 64'h48c4972c4005a2de;
                5'd14: canopy_mid = 64'he62560e08ebdd299;
                5'd15: canopy_mid = 64'ha3c6ce028dff6b56;
                5'd16: canopy_mid = 64'h14e16d5699388c63;
                5'd17: canopy_mid = 64'h8d68335c54a43ae4;
                5'd18: canopy_mid = 64'h74a909e5002c19f7;
                5'd19: canopy_mid = 64'h48a12fac4eec8f3d;
                5'd20: canopy_mid = 64'h797c9923ea11dfb5;
                5'd21: canopy_mid = 64'h2121d5b260157781;
                5'd22: canopy_mid = 64'h704aa293b550c49a;
                5'd23: canopy_mid = 64'hddcb710a40908d75;
                5'd24: canopy_mid = 64'h856c96f5dc9851aa;
                default: canopy_mid = 64'd0;
            endcase
        end
    endfunction

    function automatic logic [63:0] frame_lane(
        input logic         is_root,
        input logic         turbo,
        input logic [31:0]  node_idx,
        input logic [7:0]   log_leaves,
        input logic [255:0] left,
        input logic [255:0] right,
        input logic [4:0]   lane
    );
        logic [7:0]  sfx;
        logic [63:0] blk;
        sfx = turbo ? 8'h07 : 8'h04;
        if (is_root) begin
            case (lane)
                5'd0:  blk = {left[47:0], log_leaves, 8'h01};
                5'd1:  blk = left[111:48];
                5'd2:  blk = left[175:112];
                5'd3:  blk = left[239:176];
                5'd4:  blk = {40'd0, sfx, left[255:240]};
                5'd16: blk = 64'h8000_0000_0000_0000;
                default: blk = 64'd0;
            endcase
        end else begin
            case (lane)
                5'd0:  blk = {left[23:0], node_idx, 8'h00};
                5'd1:  blk = left[87:24];
                5'd2:  blk = left[151:88];
                5'd3:  blk = left[215:152];
                5'd4:  blk = {right[23:0], left[255:216]};
                5'd5:  blk = right[87:24];
                5'd6:  blk = right[151:88];
                5'd7:  blk = right[215:152];
                5'd8:  blk = {16'd0, sfx, right[255:216]};
                5'd16: blk = 64'h8000_0000_0000_0000;
                default: blk = 64'd0;
            endcase
        end
        frame_lane = canopy_mid(turbo, lane) ^ blk;
    endfunction

    typedef enum logic [3:0] {
        TS_IDLE, TS_RD_WAIT, TS_DECIDE, TS_PIPE_DRAIN,
        TS_WAIT_KEC, TS_CMP_LOAD, TS_CMP_PERM, TS_CMP_WAIT, TS_CMP_RD,
        TS_ROOT_WAIT, TS_ROOT_LAUNCH
    } ts_state_e;
    ts_state_e st;

    logic               turbo_q, order_bad, fail_q, k_lsb_q, is_root_q;
    logic [5:0]         log_q, cur_depth;
    logic [FRONT_AW:0]  active_len, k, wr_issue;
    logic [SIB_AW:0]    sib_len, sib_cur;
    logic [31:0]        first_u, last_u, node_u_q;
    logic [255:0]       exp_root_q, left_q, right_q;
    logic [191:0]       cmp_dig_q;
    logic [FRONT_AW-1:0] wr_slot_q;
    logic [4:0]         lane_cnt, pipe_inflight;

    // Internal 12-stage Keccak-p[1600,12] pipeline (instantiated only when PIPE_12 && !COMPACT_KEC).
    logic               p12_in_valid, p12_out_valid;
    logic [PTAGW-1:0]   p12_in_tag, p12_out_tag;
    logic [1599:0]      p12_in_state;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [1599:0]      p12_out_state;
    /* verilator lint_on UNUSEDSIGNAL */
    if (PIPE_12 && !COMPACT_KEC) begin : g_p12
        qsag_keccak_p12_pipe #(.TAGW(PTAGW)) u_p12 (
            .clk(clk), .rst(rst),
            .in_valid(p12_in_valid), .in_tag(p12_in_tag), .in_state(p12_in_state),
            .out_valid(p12_out_valid), .out_tag(p12_out_tag), .out_state(p12_out_state));
    end else begin : g_no_p12
        assign p12_out_valid = 1'b0;
        assign p12_out_tag   = '0;
        assign p12_out_state = '0;
        logic unused_p12;
        assign unused_p12 = &{1'b0, p12_in_valid, p12_in_tag, p12_in_state};
    end

    // Frontier even/odd BRAMs (read active[k] and active[k+1] simultaneously).
    logic              f_int_we;
    logic [FRONT_AW-1:0] f_int_wa;
    logic [287:0]      f_int_wd;
    logic              f_we;
    logic [FRONT_AW-1:0] f_wa;
    logic [287:0]      f_wd, fev_rd, fod_rd;
    logic [BAW-1:0]    fev_ra, fod_ra;

    assign f_we = f_int_we || (tw_front_en && st == TS_IDLE);
    assign f_wa = f_int_we ? f_int_wa : tw_front_idx;
    assign f_wd = f_int_we ? f_int_wd : {tw_front_u, tw_front_dig};

    wire [FRONT_AW-1:0] k_idx = k[FRONT_AW-1:0];
    assign fev_ra = (st == TS_ROOT_WAIT || (st == TS_IDLE && start && in_log_leaves == 6'd0))
                  ? '0 : (k_idx[FRONT_AW-1:1] + BAW'(k_idx[0]));
    assign fod_ra = k_idx[FRONT_AW-1:1];

    qsag_sdp_bram #(.AW(BAW), .DW(288)) u_fev (
        .clk(clk), .we(f_we && !f_wa[0]), .wa(f_wa[FRONT_AW-1:1]), .wd(f_wd),
        .ra(fev_ra), .rd(fev_rd));
    qsag_sdp_bram #(.AW(BAW), .DW(288)) u_fod (
        .clk(clk), .we(f_we &&  f_wa[0]), .wa(f_wa[FRONT_AW-1:1]), .wd(f_wd),
        .ra(fod_ra), .rd(fod_rd));

    logic [255:0] sib_rd;
    qsag_sdp_bram #(.AW(SIB_AW), .DW(256)) u_sib (
        .clk(clk), .we(tw_sib_en && st == TS_IDLE), .wa(tw_sib_idx), .wd(tw_sib_dig),
        .ra(sib_cur[SIB_AW-1:0]), .rd(sib_rd));

    wire [287:0] cur_entry = k_lsb_q ? fod_rd : fev_rd;
    wire [287:0] nxt_entry = k_lsb_q ? fev_rd : fod_rd;
    wire [31:0]  cur_u     = cur_entry[287:256];
    wire [255:0] cur_h     = cur_entry[255:0];
    wire [31:0]  nxt_u     = nxt_entry[287:256];
    wire [255:0] nxt_h     = nxt_entry[255:0];
    wire         has_next  = (k + (FRONT_AW+1)'(1) < active_len);
    wire         coal      = has_next && (nxt_u == (cur_u ^ 32'd1));
    wire [255:0] hsib      = coal ? nxt_h : sib_rd;
    wire [255:0] pair_l    = cur_u[0] ? hsib  : cur_h;
    wire [255:0] pair_r    = cur_u[0] ? cur_h : hsib;
    wire [31:0]  parent_u  = {1'b0, cur_u[31:1]};
    wire [FRONT_AW:0] k_after = coal ? (k + (FRONT_AW+1)'(2)) : (k + (FRONT_AW+1)'(1));

    // Combinational write port for internal parent updates.
    logic        local_wr_en;
    logic [FRONT_AW-1:0] local_wr_idx;
    logic [287:0] local_wr_dat;
    always_comb begin
        f_int_we = 1'b0;
        f_int_wa = '0;
        f_int_wd = '0;
        if (p12_out_valid) begin
            f_int_we = 1'b1;
            f_int_wa = p12_out_tag[32 +: FRONT_AW];
            f_int_wd = {p12_out_tag[31:0], p12_out_state[255:0]};
        end else if (local_wr_en) begin
            f_int_we = 1'b1;
            f_int_wa = local_wr_idx;
            f_int_wd = local_wr_dat;
        end
    end

    // Parallel Keccak state assembly (only elaborated when !COMPACT_KEC).
    if (!COMPACT_KEC) begin : g_par_frame
        always_comb begin
            for (int l = 0; l < 25; l++) begin
                kec_state_o[64*l +: 64] = frame_lane(
                    is_root_q, turbo_q, node_u_q, {2'b0, log_q}, left_q, right_q, 5'(l));
                p12_in_state[64*l +: 64] = frame_lane(
                    1'b0, 1'b1, parent_u, {2'b0, log_q}, pair_l, pair_r, 5'(l));
            end
        end
    end else begin : g_no_par_frame
        assign kec_state_o  = '0;
        assign p12_in_state = '0;
    end

    assign busy      = (st != TS_IDLE);
    assign kec_nr12  = turbo_q;
    assign kcmd_nr12 = turbo_q;
    assign kcmd_wdata = frame_lane(is_root_q, turbo_q, node_u_q, {2'b0, log_q}, left_q, right_q, lane_cnt);

    always_comb begin
        kcmd_valid = 1'b0;
        kcmd_op    = 2'd0;
        kcmd_idx   = lane_cnt;
        if (COMPACT_KEC && !rst) begin
            if (st == TS_CMP_LOAD) begin
                kcmd_valid = 1'b1;
                kcmd_op    = 2'd0;
                kcmd_idx   = lane_cnt;
            end else if (st == TS_CMP_PERM) begin
                kcmd_valid = 1'b1;
                kcmd_op    = 2'd2;
            end else if (st == TS_CMP_RD && lane_cnt < 5'd4) begin
                kcmd_valid = 1'b1;
                kcmd_op    = 2'd3;
                kcmd_idx   = lane_cnt;
            end
        end
    end

    wire launch_p12 = PIPE_12 && !COMPACT_KEC && (st == TS_DECIDE) && turbo_q;
    assign p12_in_valid = launch_p12 && !rst;
    assign p12_in_tag   = {wr_issue[FRONT_AW-1:0], parent_u};
    wire [255:0] cmp_full_dig = {kcmd_rd_data, cmp_dig_q};

    always_ff @(posedge clk) begin
        done         <= 1'b0;
        kec_start    <= 1'b0;
        local_wr_en  <= 1'b0;
        if (rst) begin
            st            <= TS_IDLE;
            ok            <= 1'b0;
            order_bad     <= 1'b0;
            fail_q        <= 1'b0;
            pipe_inflight <= 5'd0;
            first_u       <= 32'd0;
            last_u        <= 32'd0;
        end else begin
            case ({launch_p12, p12_out_valid})
                2'b10: pipe_inflight <= pipe_inflight + 5'd1;
                2'b01: pipe_inflight <= pipe_inflight - 5'd1;
                default: ;
            endcase

            case (st)
                TS_IDLE: begin
                    if (tw_front_en) begin
                        if (tw_front_idx == '0) begin
                            order_bad <= 1'b0;
                            first_u   <= tw_front_u;
                        end else if (tw_front_u <= last_u) begin
                            order_bad <= 1'b1;
                        end
                        last_u <= tw_front_u;
                    end
                    if (start) begin
                        turbo_q    <= in_turbo;
                        log_q      <= in_log_leaves;
                        active_len <= in_num_leaves;
                        sib_len    <= in_num_sibs;
                        exp_root_q <= in_exp_root;
                        cur_depth  <= in_log_leaves;
                        k          <= '0;
                        wr_issue   <= '0;
                        sib_cur    <= '0;
                        fail_q     <= order_bad
                                   || (in_log_leaves > 6'd28)
                                   || (in_num_leaves == '0)
                                   || ((first_u >> in_log_leaves) != 32'd1)
                                   || ((last_u  >> in_log_leaves) != 32'd1);
                        if (in_log_leaves > 6'd28 || in_num_leaves == '0) begin
                            ok   <= 1'b0;
                            done <= 1'b1;
                            st   <= TS_IDLE;
                        end else if (in_log_leaves == 6'd0) begin
                            st <= TS_ROOT_WAIT;
                        end else begin
                            st <= TS_RD_WAIT;
                        end
                    end
                end
                TS_RD_WAIT: begin
                    k_lsb_q <= k[0];
                    st      <= TS_DECIDE;
                end
                TS_DECIDE: begin
                    if (!coal && (sib_cur >= sib_len)) fail_q <= 1'b1;
                    k        <= k_after;
                    sib_cur  <= coal ? sib_cur : (sib_cur + (SIB_AW+1)'(1));
                    wr_issue <= wr_issue + (FRONT_AW+1)'(1);

                    if (PIPE_12 && !COMPACT_KEC && turbo_q) begin
                        if (k_after >= active_len) st <= TS_PIPE_DRAIN;
                        else                       st <= TS_RD_WAIT;
                    end else begin
                        is_root_q <= 1'b0;
                        node_u_q  <= parent_u;
                        left_q    <= pair_l;
                        right_q   <= pair_r;
                        wr_slot_q <= wr_issue[FRONT_AW-1:0];
                        if (COMPACT_KEC) begin
                            lane_cnt <= 5'd0;
                            st       <= TS_CMP_LOAD;
                        end else begin
                            kec_start <= 1'b1;
                            st        <= TS_WAIT_KEC;
                        end
                    end
                end
                TS_PIPE_DRAIN: begin
                    if (pipe_inflight == 5'd0 && !p12_out_valid && !local_wr_en) begin
                        active_len <= wr_issue;
                        wr_issue   <= '0;
                        k          <= '0;
                        cur_depth  <= cur_depth - 6'd1;
                        if (cur_depth == 6'd1) st <= TS_ROOT_WAIT;
                        else                   st <= TS_RD_WAIT;
                    end
                end
                TS_WAIT_KEC: begin
                    if (kec_done) begin
                        if (is_root_q) begin
                            out_root <= kec_digest_i;
                            ok       <= !fail_q && (kec_digest_i == exp_root_q);
                            done     <= 1'b1;
                            st       <= TS_IDLE;
                        end else begin
                            local_wr_en  <= 1'b1;
                            local_wr_idx <= wr_slot_q;
                            local_wr_dat <= {node_u_q, kec_digest_i};
                            if (k >= active_len) st <= TS_PIPE_DRAIN;
                            else                 st <= TS_RD_WAIT;
                        end
                    end
                end
                TS_CMP_LOAD: begin
                    if (kcmd_ready) begin
                        if (lane_cnt == 5'd24) st <= TS_CMP_PERM;
                        else                   lane_cnt <= lane_cnt + 5'd1;
                    end
                end
                TS_CMP_PERM: begin
                    if (kcmd_ready) st <= TS_CMP_WAIT;
                end
                TS_CMP_WAIT: begin
                    if (kcmd_done) begin
                        lane_cnt <= 5'd0;
                        st       <= TS_CMP_RD;
                    end
                end
                TS_CMP_RD: begin
                    if (kcmd_ready && lane_cnt < 5'd4) lane_cnt <= lane_cnt + 5'd1;
                    if (kcmd_rd_valid) begin
                        cmp_dig_q <= cmp_full_dig[255:64];
                        if (lane_cnt == 5'd4) begin
                            if (is_root_q) begin
                                out_root <= cmp_full_dig;
                                ok       <= !fail_q && (cmp_full_dig == exp_root_q);
                                done     <= 1'b1;
                                st       <= TS_IDLE;
                            end else begin
                                local_wr_en  <= 1'b1;
                                local_wr_idx <= wr_slot_q;
                                local_wr_dat <= {node_u_q, cmp_full_dig};
                                if (k >= active_len) st <= TS_PIPE_DRAIN;
                                else                 st <= TS_RD_WAIT;
                            end
                        end
                    end
                end
                TS_ROOT_WAIT: st <= TS_ROOT_LAUNCH;
                TS_ROOT_LAUNCH: begin
                    if (active_len != (FRONT_AW+1)'(1)
                        || fev_rd[287:256] != 32'd1
                        || sib_cur != sib_len) begin
                        fail_q <= 1'b1;
                    end
                    is_root_q <= 1'b1;
                    left_q    <= fev_rd[255:0];
                    right_q   <= '0;
                    node_u_q  <= 32'd1;
                    if (COMPACT_KEC) begin
                        lane_cnt <= 5'd0;
                        st       <= TS_CMP_LOAD;
                    end else begin
                        kec_start <= 1'b1;
                        st        <= TS_WAIT_KEC;
                    end
                end
                default: st <= TS_IDLE;
            endcase
        end
    end

    logic unused_ok;
    assign unused_ok = &{1'b0, kec_digest_i, kcmd_ready, kcmd_done, kcmd_rd_valid, kcmd_rd_data};
endmodule
