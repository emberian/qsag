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
// synchronously. Results coming back from the ring are stored at once, a single injector
// re-offers pending chains to the ring, so nothing ever stalls the ring.
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

    typedef enum logic [2:0] {S_IDLE, S_RD, S_OFFER, S_READ} state_e;
    state_e st;

    logic [SLOTS-1:0] pend;
    logic [METAW-1:0] meta [SLOTS];

    // Lowest pending slot.
    logic [SLOTW-1:0] pick;
    logic             any_pend;
    always_comb begin
        pick = '0;
        for (int i = SLOTS - 1; i >= 0; i--) if (pend[i]) pick = SLOTW'(i);
    end
    assign any_pend = |pend;

    logic [SLOTW-1:0] s_q;
    logic [METAW-1:0] m_q;
    logic [5:0]       m_ns;
    logic [STEPW-1:0] m_step;
    logic [31:0]      m_heap;
    assign {m_ns, m_step, m_heap} = m_q;

    // Start is served in S_IDLE in a cycle with no result write.
    logic do_start, do_read, do_pick;
    assign do_start    = (st == S_IDLE) && start_valid && !res_valid;
    assign do_read     = (st == S_IDLE) && !start_valid && rd_valid;
    assign do_pick     = (st == S_IDLE) && !start_valid && !rd_valid && any_pend;
    assign start_ready = do_start;

    // Running state RAM.
    logic [SLOTW-1:0] cur_ra;
    logic [767:0]     cur_rd;
    assign cur_ra = (st == S_IDLE) ? (do_read ? rd_slot : pick) : s_q;
    qsag_sdp_bram #(.AW(SLOTW), .DW(768)) u_cur (
        .clk(clk), .we(res_valid || do_start),
        .wa(res_valid ? res_slot : start_slot),
        .wd(res_valid ? res_state : start_state),
        .ra(cur_ra), .rd(cur_rd));

    // Step data RAM.
    logic [METAW-1:0] meta_pick;
    logic [STEPW-1:0] pick_step;
    logic [511:0]     blk_rd;
    assign meta_pick = meta[pick];
    assign pick_step = meta_pick[32 +: STEPW];
    qsag_sdp_bram #(.AW(SLOTW + STEPW), .DW(512)) u_blk (
        .clk(clk), .we(bw_en), .wa(bw_addr), .wd(bw_data),
        .ra((st == S_IDLE) ? {pick, pick_step} : {s_q, m_step}), .rd(blk_rd));

    // Next job from the RAM outputs.
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

    logic [767:0] nxt_state;
    logic         nxt_last;
    always_comb begin
        if (sponge) begin
            nxt_state = {cur_rd[767:512], absorbed};
            nxt_last  = (m_ns == 6'd1) && (m_heap <= 32'd1);
        end else begin
            nxt_state = {tree_key, CANOPY_NODE_HI, parent,
                         m_heap[0] ? dg : sib, m_heap[0] ? sib : dg};
            nxt_last  = (parent == 32'd1);
        end
    end

    always_ff @(posedge clk) begin
        rd_done <= 1'b0;
        if (rst) begin
            st        <= S_IDLE;
            pend      <= '0;
            busy_map  <= '0;
            done_map  <= '0;
            ok_map    <= '0;
            job_valid <= 1'b0;
        end else begin
            if (clr_maps) begin
                done_map <= '0;
                ok_map   <= '0;
            end
            case (st)
                S_IDLE: begin
                    if (do_start) begin
                        meta[start_slot]     <= {start_nsponge, {STEPW{1'b0}}, start_heap};
                        pend[start_slot]     <= 1'b1;
                        busy_map[start_slot] <= 1'b1;
                        done_map[start_slot] <= 1'b0;
                        ok_map[start_slot]   <= 1'b0;
                    end else if (do_read) begin
                        st <= S_READ;
                    end else if (do_pick) begin
                        s_q <= pick;
                        m_q <= meta_pick;
                        st  <= S_RD;
                    end
                end
                S_RD: begin
                    job_valid <= 1'b1;
                    job_state <= nxt_state;
                    job_jive  <= !sponge;
                    job_last  <= nxt_last;
                    job_slot  <= s_q;
                    st        <= S_OFFER;
                end
                S_OFFER: begin
                    if (job_ready) begin
                        job_valid <= 1'b0;
                        pend[s_q] <= 1'b0;
                        meta[s_q] <= sponge ? {m_ns - 6'd1, m_step + STEPW'(1), m_heap}
                                            : {6'd0, m_step + STEPW'(1), parent};
                        st        <= S_IDLE;
                    end
                end
                S_READ: begin
                    rd_done  <= 1'b1;
                    rd_state <= cur_rd;
                    st       <= S_IDLE;
                end
                default: st <= S_IDLE;
            endcase
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
