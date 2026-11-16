// Batched Poseidon2 chain engine: up to SLOTS independent hash chains share the C-slow ring core.
//
// A chain is the verification of one WHIR query against a Poseidon2 Canopy tree:
//   1. `nsponge` rate-8 sponge steps  state[0..7] += block (mod p); state <- perm(state)
//      (crates/qsag-accel poseidon2_sponge_hash_limbs_with_cap; the host frames the blocks);
//   2. Canopy internal nodes up the tree from heap index `heap` (leaf = 2^depth + index):
//      digest <- Jive(left, right, [0x50324E44_00000000 | parent, k0, k1, k2]) with
//      (left, right) ordered by the low bit of the child index, until the parent is node 1
//      (crates/qsag-accel merkle_layer_poseidon2_canopy_at_cpu).
// The final digest is compared with `exp_root` (the tree's top node). Per-step data (sponge
// blocks, then siblings, in order) and the running state live in block RAM, both read
// synchronously. Results coming back from the ring are stored at once and a three-stage
// injector re-offers pending chains at up to one job per clock, so nothing ever stalls the ring.
// Block and sibling limbs must be canonical.
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
    // jobs to the ring core
    output logic                   job_valid,
    input  logic                   job_ready,
    output logic [767:0]           job_state,
    output logic                   job_jive,
    output logic                   job_last,
    output logic [SLOTW-1:0]       job_slot,
    // results from the ring core
    input  logic                   res_valid,
    input  logic                   res_last,
    input  logic [SLOTW-1:0]       res_slot,
    input  logic [767:0]           res_state,
    // status
    output logic [(1<<SLOTW)-1:0]  busy_map,
    output logic [(1<<SLOTW)-1:0]  done_map,
    output logic [(1<<SLOTW)-1:0]  ok_map
);
    localparam logic [63:0] GL_P = qsag_ni_pkg::GL_P;
    localparam int SLOTS = 1 << SLOTW;
    localparam int METAW = 6 + STEPW + 32;
    localparam logic [31:0] CANOPY_NODE_HI = 32'h5032_4E44;

    logic [SLOTS-1:0] pend;
    logic [METAW-1:0] meta [SLOTS];

    // Round-robin choice among the pending slots: first pending slot at or after `rr`,
    // so no chain waits behind lower-numbered ones when the ring is full.
    logic [SLOTW-1:0] pick, pick_lo, pick_hi, rr;
    logic [SLOTS-1:0] pend_hi;
    always_comb begin
        pick_lo = '0;
        pick_hi = '0;
        for (int i = 0; i < SLOTS; i++) pend_hi[i] = pend[i] && (SLOTW'(i) >= rr);
        for (int i = SLOTS - 1; i >= 0; i--) begin
            if (pend[i])    pick_lo = SLOTW'(i);
            if (pend_hi[i]) pick_hi = SLOTW'(i);
        end
    end
    assign pick = (|pend_hi) ? pick_hi : pick_lo;

    // Injector pipeline, one job per clock when the ring accepts:
    //   A  pick a pending slot, read its state and step data, advance its step counters
    //   B  RAM outputs -> next ring job
    //   C  job register offered to the ring
    // `en` moves all three together; while the ring refuses the job in C the RAM read
    // addresses are held, so stage B keeps its data.
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
    assign do_start    = en && start_valid && !res_valid;
    assign do_read     = en && !start_valid && rd_valid && !rd_busy;
    assign do_pick     = en && !start_valid && !do_read && (|pend);
    assign start_ready = do_start;

    // Running state RAM and step data RAM.
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

    // Stage B: next job from the RAM outputs.
    logic [511:0] absorbed;
    for (genvar i = 0; i < 8; i++) begin : g_abs
        logic [64:0] s;
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] sm;
        /* verilator lint_on UNUSEDSIGNAL */
        assign s  = {1'b0, cur_rd[64*i +: 64]} + {1'b0, blk_rd[64*i +: 64]};
        assign sm = {1'b0, s} - {2'b0, GL_P};
        assign absorbed[64*i +: 64] = sm[65] ? s[63:0] : sm[63:0];
    end

    logic         sponge;
    logic [31:0]  parent;
    logic [255:0] dg, sib;
    assign sponge = (m_ns != 6'd0);
    assign parent = {1'b0, m_heap[31:1]};
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
                // C <= B
                job_valid <= a_valid;
                job_slot  <= a_s;
                job_jive  <= !sponge;
                if (sponge) begin
                    job_state <= {cur_rd[767:512], absorbed};
                    job_last  <= (m_ns == 6'd1) && (m_heap <= 32'd1);
                end else begin
                    job_state <= {tree_key, CANOPY_NODE_HI, parent,
                                  m_heap[0] ? dg : sib, m_heap[0] ? sib : dg};
                    job_last  <= (parent == 32'd1);
                end
                // A
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
