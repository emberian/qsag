// QSAG-NI v2 coprocessor for QSAGZKH2 / QSAGHQM2. The autonomous verifier
// combines quintic Goldilocks Fp5 (X^5 = 3), Poseidon2-12, Keccak/TurboSHAKE256
// and GF(2^128). Opcodes 0x50/0x51 start verification and resume a proof page.
//
// Single-cycle commands accept back-to-back valid beats (II = 1, zero handshake bubble); multi-cycle
// commands deassert `cmd_ready` until completion and pulse `rsp_valid` for one cycle.
//
//   op    name              operands                      effect
//   0x01  WR_ST             idx, data                     st[0][idx] <- data
//   0x02  RD_ST             idx                           rsp <- st[0][idx]
//   0x03  WR_MEM            addr, data                    mem[addr] <- data
//   0x04  RD_MEM            addr                          rsp <- mem[addr]
//   0x05  WR_KEY            idx (0..2), data              Canopy tree key word
//   0x06  LD4               idx (0/4/8), addr             st[0][idx..idx+3] <- mem[addr..addr+3]
//   0x07  SV4               addr                          mem[addr..addr+3] <- st[0][0..3]
//   0x08  SET_PTR           idx=0: wptr<-addr; idx=1: clear verify status
//   0x09  WR_MEM_INC        data                          mem[wptr] <- data; wptr <- wptr + 1
//   0x0A  CHECK_EQ4         idx (0=st, 1=keccak), addr    assert digest == mem[addr..addr+3] (sticky fail)
//   0x0B  RD_STATUS                                       rsp <- {31'd0, ~verify_fail, verify_checks}
//   0x10  P2_PERM                                         st[0] <- Poseidon2(st[0])
//   0x11  P2_CANOPY                                       st[0][0..3] <- Canopy(l, r, c)
//   0x12  MERKLE_PATH       idx=depth, addr=base, data=i  Canopy Merkle path from st[0][0..3]
//   0x13  P2_ABSORB8        addr                          st[0][0..7] += mem[addr..addr+7]; Poseidon2
//   0x14  P2_CANOPY4_BATCH  addr=desc, data=quads         4-way C-slowed Canopy batch -> mem[wptr..]
//   0x15  P2_SPONGE_M       addr=base, data=blocks        multi-block rate-8 Poseidon2 sponge from SRAM
//   0x23  GLMUL                                           st[0][0] <- st[0][0] * st[0][1]
//   0x28..0x2B FP5_MULADD / HORNER / FOLD / SUMCHECK
//   0x30  K_XOR / 0x31 K_SET / 0x32 K_RD                  Keccak lane absorb / load / read
//   0x33  K_P12 / 0x34 K_P24                              Keccak-p[1600,12] / Keccak-f[1600]
//   0x35  K_SAVE / 0x36 K_RESTORE                         snapshot / restore customization midstate
//   0x37  K_ABSORB_MEM      idx={r12,pad}, addr, data=nw  dual-port SRAM Keccak block absorb + permute
//   0x38  TS_CANOPY_BATCH   addr=desc, data=nodes         69B TurboSHAKE256 Canopy node batch -> mem[wptr..]
//   0x40  GF_TOWER_MUL / 0x41 GF_POLY_MUL                 {st[1],st[0]} <- {st[1],st[0]} * {st[3],st[2]}
`default_nettype none

module qsag_ni_asic_top #(
  parameter int AW = 16,
  parameter bit AUTO_VERIFY = 1
) (
  input  wire        clk,
  input  wire        rst,
  input  wire        cmd_valid,
  output wire        cmd_ready,
  input  wire [7:0]  cmd_op,
  input  wire [4:0]  cmd_idx,
  input  wire [23:0] cmd_addr,
  input  wire [63:0] cmd_data,
`ifdef QSAG_F2_NI
  input wire host_en,
  input wire [12:0] host_row,
  input wire [63:0] host_strb,
  input wire [511:0] host_data,
  output wire [511:0] host_q,
  output wire fail,
  output wire [31:0] checks,
  output wire page_paused,
  output wire [15:0] page_window_base,
  output wire [16:0] page_window_end,
`endif
  output logic       rsp_valid,
  output logic [63:0] rsp_data
);
  localparam logic [63:0] CANOPY_NODE_HI = 64'h5032_4E44_0000_0000;

  typedef enum logic [5:0] {
    T_IDLE, T_RSP, T_RDMEM, T_WAITF, T_WAITK,
    T_LD0, T_LD1, T_LD2, T_SV0, T_SV1,
    T_CHK0, T_CHK1, T_CHK2,
    T_M0, T_M1, T_M2, T_M3, T_MWAIT,
    T_C4_LD, T_C4_GO, T_C4_WAIT, T_C4_WB,
    T_KA_RD, T_KA_GO,
    T_TS_LD, T_TS_GO, T_TS_WAIT, T_TS_WB0, T_TS_WB1,
    T_GF, T_A0, T_ABS, T_A5,
    T_CHK3, T_CHK4, T_SQUEEZE, T_DOMAIN, T_DOMAIN_GO, T_DOMAIN_WAIT,
    T_PATH_LD, T_PATH_XOR, T_PATH_GO, T_PATH_WAIT, T_NONCE, T_FP5, T_AUTO, T_PAGE
  } tstate_t;
  tstate_t ts;

  logic [63:0] key [3];
  logic [4:0]  r_idx;
  logic [15:0] r_base;
  logic [15:0] r_wbase;
  logic [15:0] r_wptr;
  logic [31:0] r_node;
  logic [4:0]  r_left;
  logic [31:0] r_pairs;
  logic        r_poly;
  logic [1:0]  r_cnt;
  logic [1:0]  r_slot;
  logic [4:0]  r_sub;
  logic        chk_bad;
  logic        verify_fail;
  logic [31:0] verify_checks;

  logic [255:0] nonce;
  logic [7:0] path_stage;
  logic path_load;
  logic [399:0] path_child;

  wire [63:0] fp_mul_a, fp_mul_b, fp_product;

  wire [2047:0] auto_regs;
  wire auto_rf_we, auto_p2_write, auto_p2_start;
  wire [4:0] auto_rf_index;
  wire [63:0] auto_rf_value;
  wire autonomous = AUTO_VERIFY && ts == T_AUTO;
  wire auto_done, auto_bad, auto_ae, auto_be, auto_aw, auto_bw, auto_sub, auto_fp_go;
  wire [31:0] auto_checks;
  wire [15:0] auto_aa, auto_ba;
  wire [63:0] auto_ad, auto_bd, auto_x, auto_y;
  wire auto_fp_latch, auto_fp_feedback;
  wire [2:0] auto_fp_lane;
  wire auto_kwe, auto_kxor, auto_kstart, auto_r12;
  wire [4:0] auto_klane, auto_dlane;
  wire [3:0] auto_domain;
  wire [63:0] auto_kword;
  logic auto_fp_busy;
  wire auto_sumcheck;
  wire [15:0] auto_coeff;
  wire [31:0] auto_degree;
  wire fp_done;
  always_ff @(posedge clk) begin
    if (rst || fp_done) auto_fp_busy <= 0;
    else if (auto_fp_go) auto_fp_busy <= 1;
  end

  // ------------------------------------------------------------ Shared field & 4-slot Poseidon2 engine
  logic         op_perm, op_canopy, op_perm4, op_canopy4, op_glmul;
  logic [1:0]   wr_slot, rd_slot;
  logic [11:0]  wr_en;
  logic [767:0] wr_data;
  wire  [767:0] st, st_rd;
  wire          f_busy, f_done;
  qsag_asic_p2_shared u_field (
    .clk        (clk),
    .rst        (rst),
    .op_perm    (op_perm),
    .op_canopy  (op_canopy),
    .op_perm4   (op_perm4),
    .op_canopy4 (op_canopy4),
    .op_glmul   (op_glmul),
    .fp5_active (ts == T_FP5 || autonomous),
    .fp5_a      (autonomous && !auto_fp_busy ? auto_x : fp_mul_a),
    .fp5_b      (autonomous && !auto_fp_busy ? auto_y : fp_mul_b),
    .fp5_product(fp_product),
    .wr_slot    (wr_slot),
    .wr_en      (wr_en),
    .wr_data    (wr_data),
    .rd_slot    (rd_slot),
    .auto_regs  (auto_regs),
    .st_o       (st),
    .st_rd_o    (st_rd),
    .busy       (f_busy),
    .done       (f_done)
  );

  // ------------------------------------------------------------ 4-Bank 512 KiB Dual-Port SRAM signals
  logic        a_en, a_we, b_en, b_we;
  logic [15:0] a_addr, b_addr;
  logic [63:0] a_wdata, b_wdata;
  wire  [63:0] a_rdata, b_rdata;

  wire fp_checked, fp_bad, fp_rd_a, fp_rd_b, fp_store;
  wire [15:0] fp_addr_a, fp_addr_b, fp_next;
  wire [63:0] fp_data;
  wire [4:0] fp_we;
  wire [319:0] fp_lanes;
  qsag_fp5_seq u_fp5 (
    .clk(clk), .rst(rst), .start((AUTO_VERIFY && auto_fp_go) || (ts == T_IDLE && cmd_valid && cmd_op[7:2] == 6'h0a)),
    .op(autonomous ? {2{auto_sumcheck}} : cmd_op[1:0]), .count(autonomous ? auto_degree : cmd_data[31:0]),
    .base(autonomous ? auto_coeff : cmd_addr[15:0]),
    .dest(cmd_idx[0] ? r_wptr : cmd_addr[15:0]), .a(st[319:0]), .r(st[639:320]),
    .mul_a(fp_mul_a), .mul_b(fp_mul_b), .product(fp_product),
    .rd_a(fp_rd_a), .rd_b(fp_rd_b), .write_a(fp_store),
    .addr_a(fp_addr_a), .addr_b(fp_addr_b), .qa(autonomous && !auto_sumcheck ? 64'd0 : a_rdata), .qb(b_rdata),
    .store_data(fp_data), .lane_we(fp_we), .lane_data(fp_lanes), .done(fp_done),
    .checked(fp_checked), .bad(fp_bad), .next_dest(fp_next)
  );

  // ------------------------------------------------------------ Keccak + Canopy framing
  logic         k_start, k_r12, k_we, k_xor, k_save, k_restore;
  logic         k_pair_en, k_pair_single, k_pad_end, k_cn_go;
  logic [4:0]   k_pair_idx;
  wire  [63:0]  k_rdata;
  wire  [255:0] k_digest;
  wire [399:0] k_digest400;
  wire [1087:0] k_rate;
  wire          k_busy;
  logic [4:0]   k_lane;
  logic [63:0]  k_word;
  wire [63:0] domain_word;
  qsag_v2_domain u_domain (.domain(autonomous ? auto_domain : path_load ? 4'd6 : {1'b0,r_idx[2:0]}), .lane(autonomous ? auto_dlane : r_sub), .word_o(domain_word));

  // Rust hash.rs node and root frames, including TurboSHAKE suffix and final rate bit.
  wire [399:0] sibling = st_rd[399:0];
  wire [399:0] path_left = r_node[0] ? sibling : path_child;
  wire [399:0] path_right = r_node[0] ? path_child : sibling;
  wire [1087:0] node_frame = {8'h80,232'b0,8'h07,path_right,path_left,1'b0,r_node[31:1],8'h00};
  wire [1087:0] root_frame = {8'h80,648'b0,8'h07,path_child,3'b0,r_idx,path_stage,8'h01};
  wire [1087:0] path_frame = r_left == 0 ? root_frame : node_frame;
  wire [319:0] salt_frame = {16'b0,nonce,48'b0};
  qsag_keccak_2rpc u_keccak (
    .clk            (clk),
    .rst            (rst),
    .start          (k_start),
    .rounds12       (k_r12),
    .lane_we        (k_we),
    .lane_xor       (k_xor),
    .lane_idx       (k_lane),
    .lane_wdata     (k_word),
    .pair_xor_en    (k_pair_en),
    .pair_idx       (k_pair_idx),
    .pair_single    (k_pair_single),
    .pair_w0        (a_rdata),
    .pair_w1        (b_rdata),
    .pad_end_en     (k_pad_end),
    .canopy_node_go (k_cn_go),
    .canopy_node_idx(st_rd[31:0]),
    .canopy_left    (st_rd[319:64]),
    .canopy_right   (st_rd[575:320]),
    .save           (k_save),
    .restore        (k_restore),
    .lane_rdata     (k_rdata),
    .digest_o       (k_digest),
    .digest400_o    (k_digest400),
    .rate136_o      (k_rate),
    .busy           (k_busy)
  );

  // ------------------------------------------------------------ GF(2^128)
  wire [127:0] gf_a = {st[127:64], st[63:0]};
  wire [127:0] gf_b = {st[255:192], st[191:128]};
  wire [127:0] gf_poly, gf_tower, gf_pa, gf_pb;
  qsag_tower128_to_poly u_gfa (.x(gf_a), .y(gf_pa));
  qsag_tower128_to_poly u_gfb (.x(gf_b), .y(gf_pb));
  qsag_gf128_mul        u_gf  (.a(r_poly ? gf_a : gf_pa), .b(r_poly ? gf_b : gf_pb), .r(gf_poly));
  qsag_poly_to_tower128 u_gfr (.x(gf_poly), .y(gf_tower));

  // ------------------------------------------------------------ 4-Bank 512 KiB Dual-Port SRAM
`ifdef QSAG_F2_NI
  assign fail = verify_fail;
  assign checks = verify_checks;
  qsag_f2_sram u_sram (
    .host_en, .host_row, .host_strb, .host_data, .host_q,
`else
  qsag_sram_512k_4bank u_sram (
`endif
    .clk    (clk),
    .rst    (rst),
    .a_en   (a_en),
    .a_we   (a_we),
    .a_addr (a_addr),
    .a_wdata(a_wdata),
    .a_rdata(a_rdata),
    .b_en   (b_en),
    .b_we   (b_we),
    .b_addr (b_addr),
    .b_wdata(b_wdata),
    .b_rdata(b_rdata)
  );

  // Absorb adders: st[2c], st[2c+1] += the two SRAM read ports
  wire [63:0] ab_a0 = st[128*r_cnt +: 64];
  wire [63:0] ab_a1 = st[128*r_cnt + 64 +: 64];
  wire [63:0] ab_r0, ab_r1;
  qsag_gl64_addsub u_ab0 (.a(autonomous ? auto_x : ab_a0), .b(autonomous ? auto_y : a_rdata), .sub(autonomous && auto_sub), .r(ab_r0));
  qsag_gl64_addsub u_ab1 (.a(ab_a1), .b(b_rdata), .sub(1'b0), .r(ab_r1));

  wire page_needed, page_write_ok;
  wire [31:0] page_offset;
  wire page_cont = AUTO_VERIFY && ts == T_PAGE && cmd_valid && cmd_op == 8'h51 && cmd_data == {32'd0,page_offset};
  wire page_write = AUTO_VERIFY && ts == T_PAGE && cmd_valid && cmd_op == 8'h03 && page_write_ok;
  wire page_abort = AUTO_VERIFY && ts == T_PAGE && cmd_valid && !(page_write || page_cont);
  qsag_v2_auto_engine #(.AW(AW)) u_auto (
    .clk(clk), .rst(rst), .start_i(AUTO_VERIFY && ts == T_IDLE && cmd_valid && cmd_op == 8'h50),
    .desc_word(cmd_addr), .proof_word(cmd_data[15:0]), .window_words(cmd_data[31:16]),
    .p2_state(st), .p2_done(f_done), .p2_write(auto_p2_write), .p2_start(auto_p2_start),
    .rf_lanes(auto_regs), .rf_write(auto_rf_we), .rf_index(auto_rf_index), .rf_value(auto_rf_value),
    .page_continue(page_cont), .page_abort(page_abort), .page_needed(page_needed),
    .page_write_ok(page_write_ok), .page_offset(page_offset), .proof_size(cmd_data[63:32]),
    .done(auto_done), .failed(auto_bad), .checks(auto_checks),
    .ae(auto_ae), .be(auto_be), .aw(auto_aw), .bw(auto_bw), .aa(auto_aa), .ba(auto_ba),
    .ad(auto_ad), .bd(auto_bd), .aq(a_rdata), .bq(b_rdata),
    .field_a(auto_x), .field_b(auto_y), .field_product(fp_product), .field_sum(ab_r0), .field_sub(auto_sub),
    .fp_sumcheck(auto_sumcheck), .fp_coeff(auto_coeff), .fp_degree(auto_degree),
    .fp_bad(fp_bad), .fp_read(fp_rd_a), .fp_addr(fp_addr_a),
    .fp_start(auto_fp_go), .fp_latch(auto_fp_latch), .fp_feedback(auto_fp_feedback),
    .fp_lane(auto_fp_lane), .fp_done(fp_done),
    .k_we(auto_kwe), .k_xor(auto_kxor), .k_start(auto_kstart), .k_r12(auto_r12),
    .k_lane(auto_klane), .k_word(auto_kword), .k_q(k_rdata), .k_busy(k_busy),
    .domain(auto_domain), .domain_lane(auto_dlane), .domain_word(domain_word)
  );

  // Comparison targets for CHECK_EQ4
  wire chk_keccak = r_idx == 1 || r_idx == 2;
  wire [255:0] chk_vec = chk_keccak ? k_digest : st[255:0];
  wire [143:0] chk_upper = chk_keccak ? k_digest400[399:256] : st[399:256];

`ifdef QSAG_F2_NI
  logic [15:0] r_page_base, r_page_win;
  assign page_paused = AUTO_VERIFY && (ts == T_PAGE);
  assign page_window_base = r_page_base;
  assign page_window_end = {1'b0, r_page_base} + {1'b0, r_page_win};
`endif
  assign cmd_ready = (ts == T_IDLE || (AUTO_VERIFY && ts == T_PAGE));

  task automatic wr_pair(input logic [1:0] sl, input int lane);
    wr_slot         = sl;
    wr_en[lane]     = 1'b1;
    wr_en[lane + 1] = 1'b1;
    wr_data[64*lane +: 64]     = a_rdata;
    wr_data[64*(lane+1) +: 64] = b_rdata;
  endtask

  task automatic rd_pair(input logic [15:0] addr);
    a_en = 1'b1; a_addr = addr;
    b_en = 1'b1; b_addr = addr + 16'd1;
  endtask

  task automatic wr_mem_pair(input logic [15:0] addr, input logic [63:0] w0, input logic [63:0] w1);
    a_en = 1'b1; a_we = 1'b1; a_addr = addr;         a_wdata = w0;
    b_en = 1'b1; b_we = 1'b1; b_addr = addr + 16'd1; b_wdata = w1;
  endtask

  always_comb begin
    k_lane = cmd_idx; k_word = cmd_data;
    op_perm = 1'b0; op_canopy = 1'b0; op_perm4 = 1'b0; op_canopy4 = 1'b0;
    op_glmul = 1'b0;
    wr_slot = 2'd0; rd_slot = 2'd0; wr_en = '0; wr_data = '0;
    k_start = 1'b0; k_r12 = 1'b0; k_we = 1'b0; k_xor = 1'b0; k_save = 1'b0; k_restore = 1'b0;
    k_pair_en = 1'b0; k_pair_single = 1'b0; k_pad_end = 1'b0; k_cn_go = 1'b0; k_pair_idx = '0;
    a_en = 1'b0; a_we = 1'b0; a_addr = '0; a_wdata = '0;
    b_en = 1'b0; b_we = 1'b0; b_addr = '0; b_wdata = '0;

    unique case (ts)
      T_IDLE: if (cmd_valid) begin
        unique case (cmd_op)
          8'h01: begin wr_en[cmd_idx[3:0]] = 1'b1; wr_data[64*cmd_idx[3:0] +: 64] = cmd_data; end
          8'h03: begin a_en = 1'b1; a_we = 1'b1; a_addr = cmd_addr[15:0]; a_wdata = cmd_data; end
          8'h04: begin a_en = 1'b1; a_addr = cmd_addr[15:0]; end
          8'h09: begin a_en = 1'b1; a_we = 1'b1; a_addr = r_wptr; a_wdata = cmd_data; end
          8'h10: op_perm     = 1'b1;
          8'h11: op_canopy   = 1'b1;
          8'h23: op_glmul    = 1'b1;
          8'h30: begin k_we = 1'b1; k_xor = 1'b1; end
          8'h31: k_we      = 1'b1;
          8'h33: begin k_start = 1'b1; k_r12 = 1'b1; end
          8'h34: k_start   = 1'b1;
          8'h35: k_save    = 1'b1;
          8'h36: k_restore = 1'b1;
          default: ;
        endcase
      end

      T_PAGE: if (page_write) begin a_en=1; a_we=1; a_addr=cmd_addr[15:0]; a_wdata=cmd_data; end
      T_AUTO: if(AUTO_VERIFY) begin
        op_perm=auto_p2_start;
        if(auto_fp_latch) begin
          wr_en[{1'b0,auto_fp_lane}]=1;
          wr_en[4'd5+4'(auto_fp_lane)]=1;
          wr_data[319:0]={5{a_rdata}};
          wr_data[639:320]={5{b_rdata}};
        end else if(auto_fp_feedback) begin
          wr_en[4:0]=fp_we;
          wr_data[319:0]=fp_lanes;
        end else if(auto_p2_write || (auto_rf_we && auto_rf_index!=0)) begin
          if(auto_rf_index<12) begin wr_slot=auto_p2_write ? 0 : 1; wr_en[auto_rf_index[3:0]]=1; end
          else if(auto_rf_index<24) begin wr_slot=2; wr_en[4'(auto_rf_index-12)]=1; end
          else begin wr_slot=3; wr_en[4'(auto_rf_index-24)]=1; end
          wr_data={12{auto_rf_value}};
        end
        a_en=auto_ae; b_en=auto_be; a_we=auto_aw; b_we=auto_bw;
        a_addr=auto_aa; b_addr=auto_ba; a_wdata=auto_ad; b_wdata=auto_bd;
        k_we=auto_kwe; k_xor=auto_kxor; k_start=auto_kstart; k_r12=auto_r12;
        k_lane=auto_klane; k_word=auto_kword;
      end

      // LD4 / SV4
      T_LD0: rd_pair(r_base);
      T_LD1: begin rd_pair(r_base + 16'd2); wr_pair(2'd0, int'(r_idx)); end
      T_LD2: wr_pair(2'd0, int'(r_idx) + 2);
      T_SV0: wr_mem_pair(r_base,         st[63:0],   st[127:64]);
      T_SV1: wr_mem_pair(r_base + 16'd2, st[191:128], st[255:192]);

      // CHECK_EQ4
      T_CHK0: rd_pair(r_base);
      T_CHK1: rd_pair(r_base + 16'd2);

      T_CHK2: if (r_idx >= 2) rd_pair(r_base + 16'd4);
      T_CHK3: if (r_idx != 4) begin a_en = 1; a_addr = r_base + 16'd6; end
      T_SQUEEZE: begin
        wr_mem_pair(r_wbase, k_rate[64*r_sub +: 64], k_rate[64*(int'(r_sub)+1) +: 64]);
        b_en = r_pairs != 1; b_we = b_en;
      end
      T_DOMAIN: begin k_lane = r_sub; k_word = domain_word; k_we = 1; end
      T_DOMAIN_GO, T_PATH_GO: begin k_start = 1; k_r12 = 1; end
      T_PATH_LD: begin
        if (r_sub < 4) rd_pair(r_base + {10'd0,r_sub,1'b0});
        if (r_sub >= 1 && r_sub <= 3) wr_pair(3, 2*(int'(r_sub)-1));
        if (r_sub == 4) begin wr_slot = 3; wr_en[6] = 1; wr_data[447:384] = a_rdata; end
      end
      T_PATH_XOR: begin
        rd_slot = 3; k_lane = r_sub; k_word = path_frame[64*r_sub +: 64];
        k_we = 1; k_xor = 1;
      end
      T_NONCE: begin
        k_lane = r_sub; k_word = salt_frame[64*r_sub +: 64]; k_we = 1; k_xor = 1;
      end
      T_FP5: begin
        a_en = fp_rd_a; a_we = fp_store; a_addr = fp_addr_a; a_wdata = fp_data;
        b_en = fp_rd_b; b_addr = fp_addr_b; wr_en[4:0] = fp_we; wr_data[319:0] = fp_lanes;
      end

      // Single Canopy Merkle path
      T_M0: begin
        rd_pair(r_base);
        if (r_node[0]) begin wr_en[7:4] = 4'hF; wr_data[511:256] = st[255:0]; end
      end
      T_M1: begin rd_pair(r_base + 16'd2); wr_pair(2'd0, r_node[0] ? 0 : 4); end
      T_M2: begin
        wr_pair(2'd0, r_node[0] ? 2 : 6);
        wr_en[11:8] = 4'hF;
        wr_data[575:512] = CANOPY_NODE_HI | {32'b0, 1'b0, r_node[31:1]};
        wr_data[639:576] = key[0]; wr_data[703:640] = key[1]; wr_data[767:704] = key[2];
      end
      T_M3: op_canopy = 1'b1;

      // 4-Way C-slowed Canopy batch: each slot descriptor is 9 words [node_idx, left0..3, right0..3]
      T_C4_LD: begin
        wr_slot = r_slot;
        unique case (r_sub)
          5'd0: rd_pair(r_base);
          5'd1: begin
            rd_pair(r_base + 16'd2);
            wr_en[0]    = 1'b1; wr_data[63:0]    = b_rdata;
            wr_en[11:8] = 4'hF;
            wr_data[575:512] = CANOPY_NODE_HI | {32'b0, a_rdata[31:0]};
            wr_data[639:576] = key[0]; wr_data[703:640] = key[1]; wr_data[767:704] = key[2];
          end
          5'd2: begin rd_pair(r_base + 16'd4); wr_pair(r_slot, 1); end
          5'd3: begin rd_pair(r_base + 16'd6); wr_pair(r_slot, 3); end
          5'd4: begin a_en = 1'b1; a_addr = r_base + 16'd8; wr_pair(r_slot, 5); end
          5'd5: begin wr_en[7] = 1'b1; wr_data[511:448] = a_rdata; end
          default: ;
        endcase
      end
      T_C4_GO: op_canopy4 = 1'b1;
      T_C4_WB: begin
        rd_slot = r_slot;
        if (r_sub[0] == 1'b0) wr_mem_pair(r_wptr, st_rd[63:0], st_rd[127:64]);
        else                  wr_mem_pair(r_wptr + 16'd2, st_rd[191:128], st_rd[255:192]);
      end

      // Dual-port SRAM Keccak absorb
      T_KA_RD: begin
        if ({27'd0, r_sub} * 32'd2 < r_pairs) rd_pair(r_base + {10'd0, r_sub, 1'b0});
        if (r_sub >= 5'd1) begin
          k_pair_en     = 1'b1;
          k_pair_idx    = {r_sub[3:0] - 4'd1, 1'b0};
          k_pair_single = ({27'd0, r_sub} * 32'd2 > r_pairs);
        end
      end
      T_KA_GO: begin
        k_pad_end = r_idx[0];
        k_start   = 1'b1;
        k_r12     = r_idx[1];
      end

      // 69-byte TurboSHAKE256 Canopy internal node batch (stages 9 words in st_b[3][0..8])
      T_TS_LD: begin
        wr_slot = 2'd3;
        unique case (r_sub)
          5'd0: rd_pair(r_base);
          5'd1: begin rd_pair(r_base + 16'd2); wr_pair(2'd3, 0); end
          5'd2: begin rd_pair(r_base + 16'd4); wr_pair(2'd3, 2); end
          5'd3: begin rd_pair(r_base + 16'd6); wr_pair(2'd3, 4); end
          5'd4: begin a_en = 1'b1; a_addr = r_base + 16'd8; wr_pair(2'd3, 6); end
          5'd5: begin wr_en[8] = 1'b1; wr_data[575:512] = a_rdata; end
          default: ;
        endcase
      end
      T_TS_GO: begin rd_slot = 2'd3; k_cn_go = 1'b1; end
      T_TS_WB0: wr_mem_pair(r_wptr,         k_digest[63:0],   k_digest[127:64]);
      T_TS_WB1: wr_mem_pair(r_wptr + 16'd2, k_digest[191:128], k_digest[255:192]);

      // Rate-8 Poseidon2 sponge absorb
      T_A0: rd_pair(r_base);
      T_ABS: begin
        if (r_cnt != 2'd3) rd_pair(r_base + 16'd2 + {13'd0, r_cnt, 1'b0});
        wr_en[4'({r_cnt, 1'b0})] = 1'b1;
        wr_en[4'({r_cnt, 1'b1})] = 1'b1;
        wr_data[128*r_cnt +: 64]      = ab_r0;
        wr_data[128*r_cnt + 64 +: 64] = ab_r1;
      end
      T_A5: op_perm = 1'b1;

      T_GF: begin
        wr_en[1:0]     = 2'b11;
        wr_data[127:0] = r_poly ? gf_poly : gf_tower;
      end
      default: ;
    endcase
  end

  always_ff @(posedge clk) begin
    rsp_valid <= 1'b0;
    if (rst) begin
      for (int i=0; i<3; i++) key[i] <= '0;
      rsp_data <= '0; path_child <= '0; r_node <= '0; path_stage <= '0;
      r_pairs <= '0; r_base <= '0; r_idx <= '0; r_left <= '0; r_poly <= '0;
      r_slot <= '0; r_sub <= '0; r_wbase <= '0; r_cnt <= '0; path_load <= 0;
`ifdef QSAG_F2_NI
      r_page_base <= '0; r_page_win <= '0;
`endif
      nonce         <= '0;
      ts            <= T_IDLE;
      r_wptr        <= '0;
      verify_fail   <= 1'b0;
      verify_checks <= '0;
      chk_bad       <= 1'b0;
    end else begin
      unique case (ts)
        T_IDLE: if (cmd_valid) begin
          r_idx  <= cmd_idx;
          r_base <= cmd_addr[15:0];
          unique case (cmd_op)
            8'h50: begin
              if (AUTO_VERIFY) begin
`ifdef QSAG_F2_NI
                r_page_base <= cmd_data[15:0];
                r_page_win  <= cmd_data[31:16];
`endif
                ts <= T_AUTO;
              end else begin
                verify_fail <= 1'b1; rsp_data <= 64'd0; ts <= T_RSP;
              end
            end
            8'h02: begin rsp_data <= st[64*cmd_idx[3:0] +: 64]; rsp_valid <= 1'b1; end
            8'h32: begin rsp_data <= k_rdata; rsp_valid <= 1'b1; end
            8'h04: ts <= T_RDMEM;
            8'h05: begin key[cmd_idx[1:0]] <= cmd_data; rsp_valid <= 1'b1; end
            8'h08: begin
              if (cmd_idx == 5'd0) r_wptr <= cmd_addr[15:0];
              if (cmd_idx == 5'd1) begin verify_fail <= 1'b0; verify_checks <= 32'd0; end
              rsp_valid <= 1'b1;
            end
            8'h09: begin r_wptr <= r_wptr + 16'd1; rsp_valid <= 1'b1; end
            8'h0A: ts <= T_CHK0;
            8'h0C: begin nonce[64*cmd_idx[1:0] +: 64] <= cmd_data; rsp_valid <= 1; end
            8'h0D: begin r_sub <= 0; ts <= T_NONCE; end
            8'h16: begin
              path_child <= k_digest400; path_stage <= cmd_data[39:32];
              r_node <= (32'd1 << cmd_idx) | cmd_data[31:0];
              r_left <= cmd_idx; r_sub <= 0; path_load <= 1;
              if (cmd_idx > 28 || cmd_data[31:0] >= (32'd1 << cmd_idx)) begin
                verify_fail <= 1; ts <= T_RSP;
              end else ts <= cmd_idx == 0 ? T_DOMAIN : T_PATH_LD;
            end
            8'h28, 8'h29, 8'h2A, 8'h2B: begin
              ts <= T_FP5; r_poly <= cmd_op == 8'h2A && cmd_idx[0];
            end
            8'h39: begin
              r_wbase <= cmd_idx[0] ? r_wptr : cmd_addr[15:0];
              r_sub <= 0; r_pairs <= cmd_data[31:0];
              if (cmd_data < 1 || cmd_data > 17) begin verify_fail <= 1; ts <= T_RSP; end
              else ts <= T_SQUEEZE;
            end
            8'h3A: begin
              path_load <= 0; r_sub <= 0;
              if (cmd_idx > 7) begin verify_fail <= 1; ts <= T_RSP; end
              else ts <= T_DOMAIN;
            end
            8'h0B: begin rsp_data <= {31'd0, ~verify_fail, verify_checks}; rsp_valid <= 1'b1; end
            8'h01, 8'h03, 8'h23,
            8'h30, 8'h31, 8'h35, 8'h36: rsp_valid <= 1'b1;
            8'h06: ts <= T_LD0;
            8'h07: ts <= T_SV0;
            8'h10, 8'h11: begin r_pairs <= 32'd1; ts <= T_WAITF; end
            8'h12: begin
              r_node <= (32'd1 << cmd_idx) | cmd_data[31:0];
              r_left <= cmd_idx;
              ts     <= (cmd_idx == 5'd0) ? T_RSP : T_M0;
            end
            8'h13: begin r_cnt <= 2'd0; r_pairs <= 32'd1; ts <= T_A0; end
            8'h14: begin
              r_pairs <= cmd_data[31:0];
              r_slot  <= 2'd0;
              r_sub   <= 5'd0;
              ts      <= (cmd_data[31:0] == 32'd0) ? T_RSP : T_C4_LD;
            end
            8'h15: begin
              r_cnt   <= 2'd0;
              r_pairs <= cmd_data[31:0];
              ts      <= (cmd_data[31:0] == 32'd0) ? T_RSP : T_A0;
            end
            8'h33, 8'h34: ts <= T_WAITK;
            8'h37: begin
              r_pairs <= cmd_data[31:0];
              r_sub   <= 5'd0;
              ts      <= (cmd_data[31:0] == 32'd0) ? T_KA_GO : T_KA_RD;
            end
            8'h38: begin
              r_pairs <= cmd_data[31:0];
              r_sub   <= 5'd0;
              ts      <= (cmd_data[31:0] == 32'd0) ? T_RSP : T_TS_LD;
            end
            8'h40, 8'h41: begin r_poly <= cmd_op[0]; ts <= T_GF; end
            default: begin verify_fail <= 1'b1; rsp_data <= 64'd0; ts <= T_RSP; end
          endcase
        end

        T_PAGE: if (cmd_valid) begin
          if (page_write) rsp_valid <= 1'b1;
          else ts <= T_AUTO;
        end
        T_AUTO: if (AUTO_VERIFY && page_needed) begin
          rsp_data <= {8'h51,24'd0,page_offset}; rsp_valid <= 1'b1; ts <= T_PAGE;
        end else if (AUTO_VERIFY && auto_done) begin
          verify_fail <= verify_fail || auto_bad;
          verify_checks <= verify_checks + auto_checks;
          rsp_data <= {63'd0,!auto_bad}; rsp_valid <= 1'b1; ts <= T_IDLE;
        end
        T_RSP:   begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_RDMEM: begin rsp_data <= a_rdata; rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_WAITF: if (f_done) begin
          if (r_pairs <= 32'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
          else begin
            r_pairs <= r_pairs - 32'd1;
            r_base  <= r_base + 16'd8;
            r_cnt   <= 2'd0;
            ts      <= T_A0;
          end
        end
        T_WAITK: if (!k_busy) begin rsp_valid <= 1'b1; ts <= T_IDLE; end

        T_LD0: ts <= T_LD1;
        T_LD1: ts <= T_LD2;
        T_LD2: begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_SV0: ts <= T_SV1;
        T_SV1: begin rsp_valid <= 1'b1; ts <= T_IDLE; end

        T_CHK0: ts <= T_CHK1;
        T_CHK1: begin
          chk_bad <= (a_rdata != chk_vec[63:0]) || (b_rdata != chk_vec[127:64]);
          ts      <= T_CHK2;
        end
        T_CHK2: begin
          automatic bit mism = chk_bad || (a_rdata != chk_vec[191:128]) || (b_rdata != chk_vec[255:192]);
          if (r_idx >= 2) begin chk_bad <= mism; ts <= T_CHK3; end
          else begin
            if (mism) verify_fail <= 1'b1;
            verify_checks <= verify_checks + 32'd1;
            rsp_data <= {63'd0, ~mism};
            rsp_valid <= 1'b1;
            ts <= T_IDLE;
          end
        end
        T_CHK3: begin
          if (r_idx == 4) begin
            automatic bit mism = chk_bad || a_rdata != chk_upper[63:0];
            if (mism) verify_fail <= 1;
            rsp_data <= {63'b0,~mism}; verify_checks <= verify_checks + 1;
            rsp_valid <= 1; ts <= T_IDLE;
          end else begin
            chk_bad <= chk_bad || a_rdata != chk_upper[63:0] || b_rdata != chk_upper[127:64];
            ts <= T_CHK4;
          end
        end
        T_CHK4: begin
          automatic bit mism = chk_bad || (r_idx == 2 ? a_rdata[15:0] != chk_upper[143:128] :
                                          (r_idx != 3 || a_rdata != st[447:384]));
          if (mism) verify_fail <= 1;
          rsp_data <= {63'b0,~mism}; verify_checks <= verify_checks + 1;
          rsp_valid <= 1; ts <= T_IDLE;
        end
        T_SQUEEZE: begin
          if (r_pairs <= 2) begin
            if (r_idx[0]) r_wptr <= r_wbase + r_pairs[15:0];
            rsp_valid <= 1; ts <= T_IDLE;
          end else begin r_pairs <= r_pairs - 2; r_wbase <= r_wbase + 2; r_sub <= r_sub + 2; end
        end
        T_DOMAIN: begin
          if (r_sub == 24) ts <= T_DOMAIN_GO;
          else r_sub <= r_sub + 1'b1;
        end
        T_DOMAIN_GO: ts <= T_DOMAIN_WAIT;
        T_DOMAIN_WAIT: if (!k_busy) begin
          if (path_load) begin r_sub <= 0; ts <= T_PATH_XOR; end
          else begin rsp_valid <= 1; ts <= T_IDLE; end
        end
        T_PATH_LD: begin
          if (r_sub == 4) begin r_sub <= 0; ts <= T_DOMAIN; end
          else r_sub <= r_sub + 1'b1;
        end
        T_PATH_XOR: begin
          if (r_sub == 16) ts <= T_PATH_GO;
          else r_sub <= r_sub + 1'b1;
        end
        T_PATH_GO: ts <= T_PATH_WAIT;
        T_PATH_WAIT: if (!k_busy) begin
          if (r_left == 0) begin rsp_valid <= 1; ts <= T_IDLE; end
          else begin
            path_child <= k_digest400; r_node <= r_node >> 1;
            r_base <= r_base + 7; r_left <= r_left - 1'b1; r_sub <= 0;
            ts <= r_left == 1 ? T_DOMAIN : T_PATH_LD;
          end
        end
        T_NONCE: begin
          if (r_sub == 4) begin rsp_valid <= 1; ts <= T_IDLE; end
          else r_sub <= r_sub + 1'b1;
        end
        T_FP5: if (fp_done) begin
          if (fp_checked) begin
            if (fp_bad) verify_fail <= 1;
            verify_checks <= verify_checks + 1;
          end
          if (r_poly) r_wptr <= fp_next;
          rsp_valid <= 1; ts <= T_IDLE;
        end

        // Single Canopy Merkle path
        T_M0: ts <= T_M1;
        T_M1: ts <= T_M2;
        T_M2: ts <= T_M3;
        T_M3: ts <= T_MWAIT;
        T_MWAIT: if (f_done) begin
          r_node <= {1'b0, r_node[31:1]};
          r_base <= r_base + 16'd4;
          r_left <= r_left - 5'd1;
          if (r_left == 5'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
          else ts <= T_M0;
        end

        // 4-Way C-slowed Canopy batch
        T_C4_LD: begin
          if (r_sub == 5'd5) begin
            r_base <= r_base + 16'd9;
            r_sub  <= 5'd0;
            if (r_slot == 2'd3) ts <= T_C4_GO;
            else r_slot <= r_slot + 2'd1;
          end else begin
            r_sub <= r_sub + 5'd1;
          end
        end
        T_C4_GO:   ts <= T_C4_WAIT;
        T_C4_WAIT: if (f_done) begin r_slot <= 2'd0; r_sub <= 5'd0; ts <= T_C4_WB; end
        T_C4_WB: begin
          if (r_sub[0] == 1'b0) begin
            r_sub <= 5'd1;
          end else begin
            r_sub  <= 5'd0;
            r_wptr <= r_wptr + 16'd4;
            if (r_slot == 2'd3) begin
              if (r_pairs == 32'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
              else begin r_pairs <= r_pairs - 32'd1; r_slot <= 2'd0; ts <= T_C4_LD; end
            end else begin
              r_slot <= r_slot + 2'd1;
            end
          end
        end

        // Dual-port SRAM Keccak absorb
        T_KA_RD: begin
          if ({27'd0, r_sub} * 32'd2 >= r_pairs) ts <= T_KA_GO;
          else r_sub <= r_sub + 5'd1;
        end
        T_KA_GO: ts <= T_WAITK;

        // TurboSHAKE256 Canopy internal node batch
        T_TS_LD: begin
          if (r_sub == 5'd5) begin r_sub <= 5'd0; ts <= T_TS_GO; end
          else r_sub <= r_sub + 5'd1;
        end
        T_TS_GO:   ts <= T_TS_WAIT;
        T_TS_WAIT: if (!k_busy) ts <= T_TS_WB0;
        T_TS_WB0:  ts <= T_TS_WB1;
        T_TS_WB1: begin
          r_base <= r_base + 16'd9;
          r_wptr <= r_wptr + 16'd4;
          if (r_pairs == 32'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
          else begin r_pairs <= r_pairs - 32'd1; ts <= T_TS_LD; end
        end

        T_GF: begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_A0: ts <= T_ABS;
        T_ABS: begin r_cnt <= r_cnt + 2'd1; if (r_cnt == 2'd3) ts <= T_A5; end
        T_A5: ts <= T_WAITF;
        default: ts <= T_IDLE;
      endcase
    end
  end

  wire unused_ok = &{1'b0, f_busy, st_rd[767:576], cmd_addr[23:16], AW[0]};
endmodule
`default_nettype wire
