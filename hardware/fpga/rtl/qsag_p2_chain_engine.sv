// Batched Poseidon2 chain engine: up to SLOTS independent hash chains share the Poseidon2 engine
// (C-slow ring, unrolled 1-perm/clk VU9P pipeline, or compact core).
//
// Upgraded with:
//   1. Logarithmic binary-tree round-robin priority encoder ($clog2(SLOTS) mux levels vs SLOTS);
//   2. Parallel speculative modular rate absorption (<= 12 LUT+CARRY4 levels vs 32 cascaded).
module qsag_p2_chain_engine #(
    parameter int SLOTW = 5,
    parameter int STEPW = 6
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
    // start a chain
    input  logic                   start_valid,
    output logic                   start_ready,
    input  logic [SLOTW-1:0]       start_slot,
    input  logic [5:0]             start_nsponge,
    input  logic [31:0]            start_heap,
    input  logic [767:0]           start_state,
    // read a slot's state
    input  logic                   rd_valid,
    input  logic [SLOTW-1:0]       rd_slot,
    output logic                   rd_done,
    output logic [767:0]           rd_state,
    // jobs to the Poseidon2 core
    output logic                   job_valid,
    input  logic                   job_ready,
    output logic [767:0]           job_state,
    output logic                   job_jive,
    output logic                   job_last,
    output logic [SLOTW-1:0]       job_slot,
    // results from the Poseidon2 core
    input  logic                   res_valid,
    input  logic                   res_last,
    input  logic [SLOTW-1:0]       res_slot,
    input  logic [767:0]           res_state,
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
        assign v_lo[SLOTS + i]                   = pend[i];
        assign idx_lo[(SLOTS + i)*SLOTW +: SLOTW] = SLOTW'(i);
        assign v_hi[SLOTS + i]                   = pend_hi[i];
        assign idx_hi[(SLOTS + i)*SLOTW +: SLOTW] = SLOTW'(i);
    end
    for (genvar n = SLOTS - 1; n >= 1; n--) begin : g_tree
        assign v_lo[n]                = v_lo[2*n] | v_lo[2*n + 1];
        assign idx_lo[n*SLOTW +: SLOTW] = v_lo[2*n] ? idx_lo[(2*n)*SLOTW +: SLOTW]
                                                    : idx_lo[(2*n+1)*SLOTW +: SLOTW];
        assign v_hi[n]                = v_hi[2*n] | v_hi[2*n + 1];
        assign idx_hi[n*SLOTW +: SLOTW] = v_hi[2*n] ? idx_hi[(2*n)*SLOTW +: SLOTW]
                                                    : idx_hi[(2*n+1)*SLOTW +: SLOTW];
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_tree0 = v_lo[0] ^ v_hi[0] ^ (|idx_lo[SLOTW-1:0]) ^ (|idx_hi[SLOTW-1:0]);
    /* verilator lint_on UNUSEDSIGNAL */

    logic [SLOTW-1:0] pick;
    assign pick = v_hi[1] ? idx_hi[SLOTW +: SLOTW] : idx_lo[SLOTW +: SLOTW];

    // Injector pipeline (A -> B -> C).
    logic             a_valid, en;
    logic [SLOTW-1:0] a_s;
    logic [METAW-1:0] a_m, meta_pick;
    logic [5:0]       m_ns, p_ns;
    logic [STEPW-1:0] m_step, p_step;
    logic [31:0]      m_heap, p_heap;
    assign en        = !(job_valid && !job_ready);
    assign meta_pick = meta[pick];
    assign {m_ns, m_step, m_heap} = a_m;
    assign {p_ns, p_step, p_heap} = meta_pick;

    logic rd_busy, rd_q, do_start, do_read, do_pick;
    assign do_start    = !rst && en && start_valid && !res_valid && !busy_map[start_slot];
    assign do_read     = en && !start_valid && rd_valid && !rd_busy;
    assign do_pick     = en && !start_valid && !do_read && v_lo[1];
    assign start_ready = do_start;

    logic [767:0] cur_rd;
    logic [511:0] blk_rd;
    qsag_sdp_bram #(.AW(SLOTW), .DW(768)) u_cur (
        .clk(clk), .we(res_valid || do_start),
        .wa(res_valid ? res_slot : start_slot),
        .wd(res_valid ? res_state : start_state),
        .ra(!en ? a_s : (do_read ? rd_slot : pick)), .rd(cur_rd));
    qsag_sdp_bram #(.AW(SLOTW + STEPW), .DW(512)) u_blk (
        .clk(clk), .we(bw_en), .wa(bw_addr), .wd(bw_data),
        .ra(!en ? {a_s, m_step} : {pick, p_step}), .rd(blk_rd));

    // Stage B: parallel speculative modular rate absorption (<= 11 levels).
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

    logic         sponge;
    logic [31:0]  parent;
    logic [255:0] dg, sib;
    assign sponge = (m_ns != 6'd0);
    assign parent = m_heap[31] ? {2'b0, m_heap[30:1]} : {1'b0, m_heap[31:1]};
    assign dg     = cur_rd[255:0];
    assign sib    = blk_rd[255:0];

    always_ff @(posedge clk) begin
        rd_done <= 1'b0;
        rd_q    <= do_read;
        if (rd_q) begin
            rd_state <= cur_rd;
            rd_done  <= 1'b1;
        end
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
            if (do_read) rd_busy <= 1'b1;
            if (rd_q)    rd_busy <= 1'b0;
            if (en) begin
                job_valid <= a_valid;
                job_slot  <= a_s;
                job_jive  <= !sponge;
                if (sponge) begin
                    job_state <= {cur_rd[767:512], absorbed};
                    job_last  <= (m_ns == 6'd1) && (m_heap <= 32'd1);
                end else begin
                    job_state <= {tree_key, CANOPY_NODE_HI, parent,
                                  m_heap[0] ? dg : sib, m_heap[0] ? sib : dg};
                    job_last  <= m_heap[31] || (parent == 32'd1);
                end
                a_valid <= do_pick;
                a_s     <= pick;
                a_m     <= meta_pick;
            end
            if (do_pick) begin
                rr         <= pick + SLOTW'(1);
                pend[pick] <= 1'b0;
                meta[pick] <= (p_ns != 6'd0) ? {p_ns - 6'd1, p_step + STEPW'(1), p_heap}
                                             : {6'd0, p_step + STEPW'(1), 1'b0, p_heap[31:1]};
            end
            if (do_start) begin
                meta[start_slot]     <= {start_nsponge, {STEPW{1'b0}}, start_heap};
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
endmodule
