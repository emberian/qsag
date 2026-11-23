// Batched Poseidon2 chain engine: up to SLOTS independent hash chains share the Poseidon2 engine
// (C-slow ring, unrolled 1-perm/clk VU9P pipeline, or compact core).
//
// Modes:
//   - COMPACT_64 = 0 (`XCUP_RING`, `VU9P_TURBO`): full 768-bit parallel state & 8-lane modular
//     rate absorption feeding 1-job/clk C-slow ring or unrolled pipeline;
//   - COMPACT_64 = 1 (`ECP5_COMPACT`, `ECP5_FULLRATE`): 64-bit `DP16KD`-backed slot state,
//     single-lane modular rate absorption, and 64-bit streamed start / read / Poseidon2 ports,
//     eliminating four 768-bit cross-chip buses, 768 `job_state` FFs, 192 `DPR16X4`s, and 7 of 8
//     64-bit modular adders.
module qsag_p2_chain_engine #(
    parameter int SLOTW      = 5,
    parameter int STEPW      = 6,
    parameter int AW         = 26,
    parameter bit COMPACT_64 = (AW <= 16)
) (
    input  logic                   clk,
    input  logic                   rst,
    input  logic [191:0]           tree_key,
    input  logic [255:0]           exp_root,
    input  logic                   clr_maps,
    // step memory load: address {slot, step}
    input  logic                   bw_en,
    input  logic [SLOTW+STEPW-1:0] bw_addr,
    input  logic [511:0]           bw_data,
    // start a chain (parallel when !COMPACT_64; streamed via start_lane_* when COMPACT_64)
    input  logic                   start_valid,
    output logic                   start_ready,
    input  logic [SLOTW-1:0]       start_slot,
    input  logic [5:0]             start_nsponge,
    input  logic [31:0]            start_heap,
    input  logic [767:0]           start_state,
    input  logic                   start_lane_valid,
    output logic                   start_lane_ready,
    input  logic [3:0]             start_lane_idx,
    input  logic [63:0]            start_lane_data,
    // read a slot's state
    input  logic                   rd_valid,
    input  logic [SLOTW-1:0]       rd_slot,
    output logic                   rd_done,
    output logic [767:0]           rd_state,
    output logic                   rd_lane_valid,
    output logic [3:0]             rd_lane_idx,
    output logic [63:0]            rd_lane_data,
    // jobs to the Poseidon2 core
    output logic                   job_valid,
    input  logic                   job_ready,
    output logic [767:0]           job_state,
    output logic                   job_jive,
    output logic                   job_last,
    output logic [SLOTW-1:0]       job_slot,
    output logic                   job_active,
    output logic                   job_lane_valid,
    output logic                   job_lane_last,
    output logic [63:0]            job_lane_data,
    // results from the Poseidon2 core
    input  logic                   res_valid,
    input  logic                   res_last,
    input  logic [SLOTW-1:0]       res_slot,
    input  logic [767:0]           res_state,
    input  logic                   res_lane_valid,
    input  logic [3:0]             res_lane_idx,
    input  logic [63:0]            res_lane_data,
    // status
    output logic [(1<<SLOTW)-1:0]  busy_map,
    output logic [(1<<SLOTW)-1:0]  done_map,
    output logic [(1<<SLOTW)-1:0]  ok_map
);
    localparam logic [65:0] NEG_1P = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P
    localparam int SLOTS = 1 << SLOTW;
    localparam int METAW = 6 + STEPW + 32;
    localparam logic [31:0] CANOPY_NODE_HI = 32'h5032_4E44;

    logic [SLOTS-1:0] pend;
    logic [METAW-1:0] meta [SLOTS];
    logic [SLOTW-1:0] rr;

    // Balanced binary-tree find-first-one over pend_hi (slots >= rr) and pend (all slots).
    logic [SLOTS-1:0] pend_hi;
    for (genvar i = 0; i < SLOTS; i++) begin : g_mask
        if (i == 0) begin : g_zero_slot
            assign pend_hi[i] = pend[i] && (rr == '0);
        end else if (i == SLOTS - 1) begin : g_top_slot
            assign pend_hi[i] = pend[i];
        end else begin : g_lo_slot
            assign pend_hi[i] = pend[i] && (SLOTW'(i) >= rr);
        end
    end

    logic [2*SLOTS-1:0]        v_lo, v_hi;
    logic [2*SLOTS*SLOTW-1:0]  idx_lo, idx_hi;
    assign v_lo[0]              = 1'b0;
    assign v_hi[0]              = 1'b0;
    assign idx_lo[SLOTW-1:0]    = '0;
    assign idx_hi[SLOTW-1:0]    = '0;
    for (genvar i = 0; i < SLOTS; i++) begin : g_leaf
        assign v_lo[SLOTS + i]                    = pend[i];
        assign idx_lo[(SLOTS + i)*SLOTW +: SLOTW] = SLOTW'(i);
        assign v_hi[SLOTS + i]                    = pend_hi[i];
        assign idx_hi[(SLOTS + i)*SLOTW +: SLOTW] = SLOTW'(i);
    end
    for (genvar n = SLOTS - 1; n >= 1; n--) begin : g_tree
        assign v_lo[n]                  = v_lo[2*n] | v_lo[2*n + 1];
        assign idx_lo[n*SLOTW +: SLOTW] = v_lo[2*n] ? idx_lo[(2*n)*SLOTW +: SLOTW]
                                                    : idx_lo[(2*n+1)*SLOTW +: SLOTW];
        assign v_hi[n]                  = v_hi[2*n] | v_hi[2*n + 1];
        assign idx_hi[n*SLOTW +: SLOTW] = v_hi[2*n] ? idx_hi[(2*n)*SLOTW +: SLOTW]
                                                    : idx_hi[(2*n+1)*SLOTW +: SLOTW];
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_tree0 = v_lo[0] ^ v_hi[0] ^ (|idx_lo[SLOTW-1:0]) ^ (|idx_hi[SLOTW-1:0]);
    /* verilator lint_on UNUSEDSIGNAL */

    logic [SLOTW-1:0] pick;
    assign pick = v_hi[1] ? idx_hi[SLOTW +: SLOTW] : idx_lo[SLOTW +: SLOTW];

    logic [SLOTW-1:0] a_s;
    logic [METAW-1:0] a_m, meta_pick;
    logic [5:0]       m_ns, p_ns;
    logic [STEPW-1:0] m_step, p_step;
    logic [31:0]      m_heap, p_heap;
    assign meta_pick = meta[pick];
    assign {m_ns, m_step, m_heap} = a_m;
    assign {p_ns, p_step, p_heap} = meta_pick;

    logic        sponge;
    logic [31:0] parent;
    assign sponge = (m_ns != 6'd0);
    assign parent = m_heap[31] ? {2'b0, m_heap[30:1]} : {1'b0, m_heap[31:1]};

    /* verilator lint_off UNUSEDPARAM */
    localparam int UNUSED_AW = AW;
    /* verilator lint_on UNUSEDPARAM */

    if (COMPACT_64) begin : g_compact_64
        typedef enum logic [2:0] {
            CH_IDLE, CH_SEND_JOB, CH_SEND_LAST, CH_READ_SLOT, CH_READ_LAST, CH_READ_WAIT
        } ch_st_e;
        ch_st_e ch_st;

        logic [3:0] c_idx, c_idx_q;
        logic       c_pipe_v, res_bad_q;

        assign start_ready    = 1'b0;
        assign rd_state       = '0;
        assign job_valid      = 1'b0;
        assign job_state      = '0;

        assign start_lane_ready = !rst && !res_lane_valid && !busy_map[start_slot];
        wire   start_beat       = start_lane_valid && start_lane_ready;
        wire   do_start         = start_beat && (start_lane_idx == 4'd11);
        wire   do_read          = (ch_st == CH_IDLE) && rd_valid && !start_lane_valid;
        wire   do_pick          = (ch_st == CH_IDLE) && !rd_valid && !start_lane_valid && !start_valid && job_ready && v_lo[1];

        wire             meta_we = do_start || do_pick;
        wire [SLOTW-1:0] meta_wa = do_start ? start_slot : pick;
        wire [METAW-1:0] meta_wd = do_start
                                 ? {start_nsponge, {STEPW{1'b0}}, start_heap}
                                 : ((p_ns != 6'd0) ? {p_ns - 6'd1, p_step + STEPW'(1), p_heap}
                                                   : {6'd0, p_step + STEPW'(1), 1'b0, p_heap[31:1]});

        (* ram_style = "block", no_rw_check *) logic [63:0] cur_mem [0:511];
        logic [63:0] cur_rd64;
        wire         cur_we   = res_lane_valid || start_beat;
        wire [8:0]   cur_wa   = res_lane_valid
                              ? ((9'(res_slot) << 4) | 9'(res_lane_idx))
                              : ((9'(start_slot) << 4) | 9'(start_lane_idx));
        wire [63:0]  cur_wd   = res_lane_valid ? res_lane_data : start_lane_data;
        wire [3:0]   cur_ra_l = (ch_st == CH_SEND_JOB && !sponge) ? {2'b00, c_idx[1:0]} : c_idx;
        wire [8:0]   cur_ra   = (9'(a_s) << 4) | 9'(cur_ra_l);

        always_ff @(posedge clk) begin
            if (cur_we) cur_mem[cur_wa] <= cur_wd;
            cur_rd64 <= cur_mem[cur_ra];
        end

        logic [511:0] blk_rd;
        qsag_sdp_bram #(.AW(SLOTW + STEPW), .DW(512), .NO_RW_CHECK(1'b1)) u_blk (
            .clk(clk), .we(bw_en), .wa(bw_addr), .wd(bw_data),
            .ra({a_s, m_step}), .rd(blk_rd));

        wire [2:0]  blk_sel    = sponge ? c_idx_q[2:0] : {1'b0, c_idx_q[1:0]};
        wire [63:0] blk_lane64 = blk_rd[64*blk_sel +: 64];
        /* verilator lint_off UNUSEDSIGNAL */
        wire [64:0] s0_64      = {1'b0, cur_rd64} + {1'b0, blk_lane64};
        wire [65:0] s1_64      = {1'b0, s0_64} + NEG_1P;
        /* verilator lint_on UNUSEDSIGNAL */
        wire [63:0] abs_64     = !s1_64[65] ? s1_64[63:0] : s0_64[63:0];

        always_comb begin
            if (sponge) begin
                job_lane_data = (c_idx_q < 4'd8) ? abs_64 : cur_rd64;
            end else begin
                case (c_idx_q)
                    4'd0, 4'd1, 4'd2, 4'd3: job_lane_data = m_heap[0] ? blk_lane64 : cur_rd64;
                    4'd4, 4'd5, 4'd6, 4'd7: job_lane_data = m_heap[0] ? cur_rd64   : blk_lane64;
                    4'd8:                   job_lane_data = {CANOPY_NODE_HI, parent};
                    4'd9:                   job_lane_data = tree_key[63:0];
                    4'd10:                  job_lane_data = tree_key[127:64];
                    default:                job_lane_data = tree_key[191:128];
                endcase
            end
        end

        assign job_active     = (ch_st == CH_SEND_JOB) || (ch_st == CH_SEND_LAST);
        assign job_lane_valid = c_pipe_v && job_active;
        assign job_lane_last  = (ch_st == CH_SEND_LAST);
        assign job_jive       = !sponge;
        assign job_last       = sponge ? ((m_ns == 6'd1) && (m_heap <= 32'd1))
                                       : (m_heap[31] || (parent == 32'd1));
        assign job_slot       = a_s;

        assign rd_lane_valid  = c_pipe_v && ((ch_st == CH_READ_SLOT) || (ch_st == CH_READ_LAST));
        assign rd_lane_idx    = c_idx_q;
        assign rd_lane_data   = cur_rd64;

        wire res_lane_bad = (res_lane_data != exp_root[64*res_lane_idx[1:0] +: 64]);

        always_ff @(posedge clk) begin
            rd_done <= 1'b0;
            if (rst) begin
                ch_st    <= CH_IDLE;
                pend     <= '0;
                busy_map <= '0;
                done_map <= '0;
                ok_map   <= '0;
                rr       <= '0;
                c_idx    <= 4'd0;
                c_idx_q  <= 4'd0;
                c_pipe_v <= 1'b0;
                res_bad_q <= 1'b0;
            end else begin
                if (clr_maps) begin
                    done_map <= '0;
                    ok_map   <= '0;
                end
                if (meta_we) meta[meta_wa] <= meta_wd;

                case (ch_st)
                    CH_IDLE: begin
                        c_pipe_v <= 1'b0;
                        if (do_read) begin
                            a_s   <= rd_slot;
                            c_idx <= 4'd0;
                            ch_st <= CH_READ_SLOT;
                        end else if (do_pick) begin
                            a_s        <= pick;
                            a_m        <= meta_pick;
                            rr         <= pick + SLOTW'(1);
                            pend[pick] <= 1'b0;
                            c_idx      <= 4'd0;
                            ch_st      <= CH_SEND_JOB;
                        end
                    end
                    CH_SEND_JOB: begin
                        c_pipe_v <= 1'b1;
                        c_idx_q  <= c_idx;
                        if (c_idx == 4'd11) ch_st <= CH_SEND_LAST;
                        else                c_idx <= c_idx + 4'd1;
                    end
                    CH_SEND_LAST: begin
                        c_pipe_v <= 1'b0;
                        ch_st    <= CH_IDLE;
                    end
                    CH_READ_SLOT: begin
                        c_pipe_v <= 1'b1;
                        c_idx_q  <= c_idx;
                        if (c_idx == 4'd11) ch_st <= CH_READ_LAST;
                        else                c_idx <= c_idx + 4'd1;
                    end
                    CH_READ_LAST: begin
                        c_pipe_v <= 1'b0;
                        rd_done  <= 1'b1;
                        ch_st    <= CH_READ_WAIT;
                    end
                    CH_READ_WAIT: begin
                        if (!rd_valid) ch_st <= CH_IDLE;
                    end
                    default: ch_st <= CH_IDLE;
                endcase

                if (do_start) begin
                    pend[start_slot]     <= 1'b1;
                    busy_map[start_slot] <= 1'b1;
                    done_map[start_slot] <= 1'b0;
                    ok_map[start_slot]   <= 1'b0;
                end
                if (res_lane_valid) begin
                    if (res_lane_idx == 4'd0)
                        res_bad_q <= res_lane_bad;
                    else if (res_lane_idx < 4'd4)
                        res_bad_q <= res_bad_q || res_lane_bad;

                    if (res_lane_idx == 4'd11) begin
                        if (res_last) begin
                            busy_map[res_slot] <= 1'b0;
                            done_map[res_slot] <= 1'b1;
                            ok_map[res_slot]   <= !res_bad_q;
                        end else begin
                            pend[res_slot] <= 1'b1;
                        end
                    end
                end
            end
        end

        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_par = &{1'b0, start_state, res_valid, res_state};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_parallel_768
        assign start_lane_ready = 1'b0;
        assign rd_lane_valid    = 1'b0;
        assign rd_lane_idx      = 4'd0;
        assign rd_lane_data     = 64'd0;
        assign job_active       = 1'b0;
        assign job_lane_valid   = 1'b0;
        assign job_lane_last    = 1'b0;
        assign job_lane_data    = 64'd0;

        logic a_valid, en, rd_busy, rd_q, do_start, do_read, do_pick;
        assign en          = !(job_valid && !job_ready);
        assign start_ready = !rst && en && !res_valid && !busy_map[start_slot];
        assign do_start    = start_valid && start_ready;
        assign do_read     = !job_valid && !a_valid && !start_valid && rd_valid && !rd_busy;
        assign do_pick     = en && !start_valid && !rd_valid && !rd_busy && v_lo[1];

        wire             meta_we = do_start || do_pick;
        wire [SLOTW-1:0] meta_wa = do_start ? start_slot : pick;
        wire [METAW-1:0] meta_wd = do_start
                                 ? {start_nsponge, {STEPW{1'b0}}, start_heap}
                                 : ((p_ns != 6'd0) ? {p_ns - 6'd1, p_step + STEPW'(1), p_heap}
                                                   : {6'd0, p_step + STEPW'(1), 1'b0, p_heap[31:1]});

        logic [767:0] cur_rd;
        logic [511:0] blk_rd;
        qsag_sdp_bram #(.AW(SLOTW), .DW(768), .NO_RW_CHECK(1'b1), .FORCE_BRAM(SLOTW > 4)) u_cur (
            .clk(clk), .we(res_valid || do_start),
            .wa(res_valid ? res_slot : start_slot),
            .wd(res_valid ? res_state : start_state),
            .ra(!en ? a_s : (do_read ? rd_slot : pick)), .rd(cur_rd));
        qsag_sdp_bram #(.AW(SLOTW + STEPW), .DW(512), .NO_RW_CHECK(1'b1)) u_blk (
            .clk(clk), .we(bw_en), .wa(bw_addr), .wd(bw_data),
            .ra(!en ? {a_s, m_step} : {pick, p_step}), .rd(blk_rd));

        logic [511:0] absorbed;
        for (genvar i = 0; i < 8; i++) begin : g_abs
            wire [63:0] c_i = cur_rd[64*i +: 64];
            wire [63:0] b_i = blk_rd[64*i +: 64];
            /* verilator lint_off UNUSEDSIGNAL */
            logic [64:0] s0;
            logic [65:0] s1;
            /* verilator lint_on UNUSEDSIGNAL */
            qsag_add_split #(.W(65), .CHUNK(24)) u_s0 (
                .a({1'b0, c_i}), .b({1'b0, b_i}), .y(s0));
            qsag_sum_csa #(.W(66), .N(3), .CHUNK(24)) u_s1 (
                .x({NEG_1P, {2'b0, b_i}, {2'b0, c_i}}), .y(s1));
            assign absorbed[64*i +: 64] = !s1[65] ? s1[63:0] : s0[63:0];
        end

        logic [255:0] dg, sib;
        assign dg       = cur_rd[255:0];
        assign sib      = blk_rd[255:0];
        assign rd_state = job_state;

        always_ff @(posedge clk) begin
            rd_done <= 1'b0;
            rd_q    <= do_read;
            if (rd_q) rd_done <= 1'b1;
            if (rst) begin
                pend      <= '0;
                busy_map  <= '0;
                done_map  <= '0;
                ok_map    <= '0;
                job_valid <= 1'b0;
                a_valid   <= 1'b0;
                rd_busy   <= 1'b0;
                rd_q      <= 1'b0;
                rr        <= '0;
            end else begin
                if (clr_maps) begin
                    done_map <= '0;
                    ok_map   <= '0;
                end
                if (do_read)                 rd_busy <= 1'b1;
                else if (!rd_valid && !rd_q) rd_busy <= 1'b0;
                if (rd_q) begin
                    job_state <= cur_rd;
                    job_valid <= 1'b0;
                end else if (en) begin
                    job_valid <= a_valid;
                    if (a_valid) begin
                        job_slot <= a_s;
                        job_jive <= !sponge;
                        if (sponge) begin
                            job_state <= {cur_rd[767:512], absorbed};
                            job_last  <= (m_ns == 6'd1) && (m_heap <= 32'd1);
                        end else begin
                            job_state <= {tree_key, CANOPY_NODE_HI, parent,
                                          m_heap[0] ? dg : sib, m_heap[0] ? sib : dg};
                            job_last  <= m_heap[31] || (parent == 32'd1);
                        end
                    end
                    a_valid <= do_pick;
                    a_s     <= pick;
                    a_m     <= meta_pick;
                end
                if (meta_we) meta[meta_wa] <= meta_wd;
                if (do_pick) begin
                    rr         <= pick + SLOTW'(1);
                    pend[pick] <= 1'b0;
                end
                if (do_start) begin
                    pend[start_slot]     <= 1'b1;
                    busy_map[start_slot] <= 1'b1;
                    done_map[start_slot] <= 1'b0;
                    ok_map[start_slot]   <= 1'b0;
                end
                if (res_valid) begin
                    if (res_last) begin
                        busy_map[res_slot] <= 1'b0;
                        done_map[res_slot] <= 1'b1;
                        ok_map[res_slot]   <= (res_state[255:0] == exp_root);
                    end else begin
                        pend[res_slot] <= 1'b1;
                    end
                end
            end
        end

        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_cmp = &{1'b0, start_lane_valid, start_lane_idx, start_lane_data,
                            res_lane_valid, res_lane_idx, res_lane_data};
        /* verilator lint_on UNUSEDSIGNAL */
    end
endmodule
