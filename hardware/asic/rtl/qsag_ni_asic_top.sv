// QSAG-NI coprocessor top: command-driven (RoCC-style valid/ready) macro for the QSAG verifier and
// edge-prover kernels. Single-cycle commands accept consecutive valid beats; `cmd_ready` is low while a command runs and
// `rsp_valid` pulses for one cycle when it completes (`rsp_data` carries read results).
//
//   op    name         operands                      effect
//   0x01  WR_ST        idx, data                     st[idx] <- data
//   0x02  RD_ST        idx                           rsp <- st[idx]
//   0x03  WR_MEM       addr, data                    mem[addr] <- data
//   0x04  RD_MEM       addr                          rsp <- mem[addr]
//   0x05  WR_KEY       idx (0..2), data              Canopy tree key word
//   0x06  LD4          idx (0/4/8), addr             st[idx..idx+3] <- mem[addr..addr+3]
//   0x07  SV4          addr                          mem[addr..addr+3] <- st[0..3]
//   0x13  P2_ABSORB8   addr                          st[0..7] += mem[addr..addr+7] (mod p); st <- Poseidon2(st)
//   0x10  P2_PERM                                    st <- Poseidon2(st)
//   0x11  P2_CANOPY                                  st[0..3] <- Canopy node of (l=st[0..3], r=st[4..7], c=st[8..11])
//   0x12  MERKLE_PATH  idx = depth, addr = base,     st[0..3] <- top node of the Canopy path from leaf digest
//                      data = leaf index             st[0..3]; sibling of level i at mem[base + 4i ..]
//   0x20  EMULADD                                    E0 <- E0 * E1 + E2   (GoldilocksExt4)
//   0x21  EADD / 0x22 ESUB                           E0 <- E0 +/- E2
//   0x23  GLMUL                                      st[0] <- st[0] * st[1]
//   0x24  FOLD         addr = base, data = pairs     for i < pairs: mem[base+4i..] <- lo + r * (hi - lo), lo =
//                                                    mem[base+8i..], hi = mem[base+8i+4..], r = E1 (in place)
//   0x30  K_XOR idx,data / 0x31 K_SET idx,data / 0x32 K_RD idx     Keccak lane absorb / load / read
//   0x33  K_P12 / 0x34 K_P24                         Keccak-p[1600,12] / Keccak-f[1600]
//   0x35  K_SAVE / 0x36 K_RESTORE                    snapshot / restore the Keccak state (customization midstate)
// Field words in st and mem must be canonical (< p); the multipliers accept any 64-bit word.
//   0x40  GF_TOWER_MUL / 0x41 GF_POLY_MUL            {st[1],st[0]} <- {st[1],st[0]} * {st[3],st[2]}
`default_nettype none

module qsag_ni_asic_top #(
  parameter int AW = 14,
  parameter bit FAST_PARTIAL = 1'b1
) (
  input  wire        clk,
  input  wire        rst,
  input  wire        cmd_valid,
  output wire        cmd_ready,
  input  wire [7:0]  cmd_op,
  input  wire [4:0]  cmd_idx,
  input  wire [23:0] cmd_addr,
  input  wire [63:0] cmd_data,
  output logic       rsp_valid,
  output logic [63:0] rsp_data
);
  localparam logic [63:0] CANOPY_NODE_HI = 64'h5032_4E44_0000_0000;

  typedef enum logic [4:0] {
    T_IDLE, T_RSP, T_RDMEM, T_WAITF, T_WAITK,
    T_LD0, T_LD1, T_LD2, T_SV0, T_SV1,
    T_M0, T_M1, T_M2, T_M3, T_MWAIT,
    T_F0, T_F1, T_F2, T_F3, T_F4, T_FSUB, T_FMUL, T_FW0, T_FW1, T_GF,
    T_A0, T_ABS, T_A5
  } tstate_t;
  tstate_t ts;

  logic [63:0]   key [3];
  logic [4:0]    r_idx;
  logic [AW-1:0] r_base;      // current read base (LD4 / path level / fold pair)
  logic [AW-1:0] r_wbase;     // fold write base
  logic [31:0]   r_node;      // heap index of the current path node
  logic [4:0]    r_left;      // path levels left
  logic [31:0]   r_pairs;     // fold pairs left
  logic          r_poly;
  logic [1:0]    r_cnt;

  // ------------------------------------------------------------ field datapath
  logic        op_perm, op_canopy, op_emuladd, op_eadd, op_esub, op_glmul;
  logic [11:0] wr_en;
  logic [767:0] wr_data;
  wire  [767:0] st;
  wire          f_busy, f_done;
  qsag_asic_ext4_p2_shared #(.FAST_PARTIAL(FAST_PARTIAL)) u_field (
    .clk(clk), .rst(rst), .op_perm(op_perm), .op_canopy(op_canopy), .op_emuladd(op_emuladd),
    .op_eadd(op_eadd), .op_esub(op_esub), .op_glmul(op_glmul), .wr_en(wr_en), .wr_data(wr_data),
    .st_o(st), .busy(f_busy), .done(f_done));

  // ------------------------------------------------------------ Keccak
  logic        k_start, k_r12, k_we, k_xor, k_save, k_restore;
  wire  [63:0] k_rdata;
  wire         k_busy;
  qsag_keccak_2rpc u_keccak (
    .clk(clk), .rst(rst), .start(k_start), .rounds12(k_r12), .lane_we(k_we), .lane_xor(k_xor),
    .lane_idx(cmd_idx), .lane_wdata(cmd_data), .save(k_save), .restore(k_restore),
    .lane_rdata(k_rdata), .busy(k_busy));

  // ------------------------------------------------------------ GF(2^128)
  wire [127:0] gf_a = {st[127:64], st[63:0]};
  wire [127:0] gf_b = {st[255:192], st[191:128]};
  wire [127:0] gf_poly, gf_tower, gf_pa, gf_pb;
  qsag_tower128_to_poly u_gfa (.x(gf_a), .y(gf_pa));
  qsag_tower128_to_poly u_gfb (.x(gf_b), .y(gf_pb));
  qsag_gf128_mul u_gf (.a(r_poly ? gf_a : gf_pa), .b(r_poly ? gf_b : gf_pb), .r(gf_poly));
  qsag_poly_to_tower128 u_gfr (.x(gf_poly), .y(gf_tower));

  // ------------------------------------------------------------ SRAM macro
  logic          a_en, a_we, b_en, b_we;
  logic [AW-1:0] a_addr, b_addr;
  logic [63:0]   a_wdata, b_wdata;
  wire  [63:0]   a_rdata, b_rdata;
  sram_dp_64x16384 #(.AW(AW)) u_sram (
    .clk(clk), .a_en(a_en), .a_we(a_we), .a_addr(a_addr), .a_wdata(a_wdata), .a_rdata(a_rdata),
    .b_en(b_en), .b_we(b_we), .b_addr(b_addr), .b_wdata(b_wdata), .b_rdata(b_rdata));

  // absorb adders: st[2c], st[2c+1] += the two SRAM read ports
  wire [63:0] ab_a0 = st[128*r_cnt +: 64];
  wire [63:0] ab_a1 = st[128*r_cnt + 64 +: 64];
  wire [63:0] ab_r0, ab_r1;
  qsag_gl64_addsub u_ab0 (.a(ab_a0), .b(a_rdata), .sub(1'b0), .r(ab_r0));
  qsag_gl64_addsub u_ab1 (.a(ab_a1), .b(b_rdata), .sub(1'b0), .r(ab_r1));

  assign cmd_ready = (ts == T_IDLE);
  wire   accept    = cmd_valid && cmd_ready;

  // lane pair written from the two SRAM read ports
  task automatic wr_pair(input int lane);
    wr_en[lane]     = 1'b1;
    wr_en[lane + 1] = 1'b1;
    wr_data[64*lane +: 64]     = a_rdata;
    wr_data[64*(lane+1) +: 64] = b_rdata;
  endtask
  task automatic rd_pair(input logic [AW-1:0] addr);
    a_en = 1'b1; a_addr = addr;
    b_en = 1'b1; b_addr = addr + AW'(1);
  endtask

  always_comb begin
    op_perm = 1'b0; op_canopy = 1'b0; op_emuladd = 1'b0; op_eadd = 1'b0; op_esub = 1'b0; op_glmul = 1'b0;
    wr_en = '0; wr_data = '0;
    k_start = 1'b0; k_r12 = 1'b0; k_we = 1'b0; k_xor = 1'b0; k_save = 1'b0; k_restore = 1'b0;
    a_en = 1'b0; a_we = 1'b0; a_addr = '0; a_wdata = '0;
    b_en = 1'b0; b_we = 1'b0; b_addr = '0; b_wdata = '0;
    unique case (ts)
      T_IDLE: if (cmd_valid) begin
        unique case (cmd_op)
          8'h01: begin wr_en[cmd_idx[3:0]] = 1'b1; wr_data[64*cmd_idx[3:0] +: 64] = cmd_data; end
          8'h03: begin a_en = 1'b1; a_we = 1'b1; a_addr = cmd_addr[AW-1:0]; a_wdata = cmd_data; end
          8'h04: begin a_en = 1'b1; a_addr = cmd_addr[AW-1:0]; end
          8'h10: op_perm = 1'b1;
          8'h11: op_canopy = 1'b1;
          8'h20: op_emuladd = 1'b1;
          8'h21: op_eadd = 1'b1;
          8'h22: op_esub = 1'b1;
          8'h23: op_glmul = 1'b1;
          8'h30: begin k_we = 1'b1; k_xor = 1'b1; end
          8'h31: k_we = 1'b1;
          8'h33: begin k_start = 1'b1; k_r12 = 1'b1; end
          8'h34: k_start = 1'b1;
          8'h35: k_save = 1'b1;
          8'h36: k_restore = 1'b1;
          default: ;
        endcase
      end
      // LD4: two reads, lanes r_idx .. r_idx + 3
      T_LD0: rd_pair(r_base);
      T_LD1: begin rd_pair(r_base + AW'(2)); wr_pair(int'(r_idx)); end
      T_LD2: wr_pair(int'(r_idx) + 2);
      T_SV0: begin
        a_en = 1'b1; a_we = 1'b1; a_addr = r_base;          a_wdata = st[63:0];
        b_en = 1'b1; b_we = 1'b1; b_addr = r_base + AW'(1); b_wdata = st[127:64];
      end
      T_SV1: begin
        a_en = 1'b1; a_we = 1'b1; a_addr = r_base + AW'(2); a_wdata = st[191:128];
        b_en = 1'b1; b_we = 1'b1; b_addr = r_base + AW'(3); b_wdata = st[255:192];
      end
      // Merkle path level: the current node moves to the right slot when it is a right child
      T_M0: begin
        rd_pair(r_base);
        if (r_node[0]) begin wr_en[7:4] = 4'hF; wr_data[511:256] = st[255:0]; end
      end
      T_M1: begin rd_pair(r_base + AW'(2)); wr_pair(r_node[0] ? 0 : 4); end
      T_M2: begin
        wr_pair(r_node[0] ? 2 : 6);
        wr_en[11:8] = 4'hF;
        wr_data[575:512] = CANOPY_NODE_HI | {32'b0, 1'b0, r_node[31:1]};
        wr_data[639:576] = key[0]; wr_data[703:640] = key[1]; wr_data[767:704] = key[2];
      end
      T_M3: op_canopy = 1'b1;
      // fold pair: lo -> E2, hi -> E0, E0 <- E0 - E2, E0 <- E0 * E1 + E2, write E0
      T_F0: rd_pair(r_base);
      T_F1: begin rd_pair(r_base + AW'(2)); wr_pair(8); end
      T_F2: begin rd_pair(r_base + AW'(4)); wr_pair(10); end
      T_F3: begin rd_pair(r_base + AW'(6)); wr_pair(0); end
      T_F4: wr_pair(2);
      T_FSUB: op_esub = 1'b1;
      T_FMUL: op_emuladd = 1'b1;
      T_FW0: begin
        a_en = 1'b1; a_we = 1'b1; a_addr = r_wbase;          a_wdata = st[63:0];
        b_en = 1'b1; b_we = 1'b1; b_addr = r_wbase + AW'(1); b_wdata = st[127:64];
      end
      T_FW1: begin
        a_en = 1'b1; a_we = 1'b1; a_addr = r_wbase + AW'(2); a_wdata = st[191:128];
        b_en = 1'b1; b_we = 1'b1; b_addr = r_wbase + AW'(3); b_wdata = st[255:192];
      end
      T_A0: rd_pair(r_base);
      T_ABS: begin
        if (r_cnt != 2'd3) rd_pair(r_base + AW'(2) + AW'({r_cnt, 1'b0}));
        wr_en[4'({r_cnt, 1'b0})] = 1'b1;
        wr_en[4'({r_cnt, 1'b1})] = 1'b1;
        wr_data[128*r_cnt +: 64]      = ab_r0;
        wr_data[128*r_cnt + 64 +: 64] = ab_r1;
      end
      T_A5: op_perm = 1'b1;
      T_GF: begin
        wr_en[1:0] = 2'b11;
        wr_data[127:0] = r_poly ? gf_poly : gf_tower;
      end
      default: ;
    endcase
  end

  always_ff @(posedge clk) begin
    rsp_valid <= 1'b0;
    if (rst) begin
      ts <= T_IDLE;
    end else begin
      unique case (ts)
        T_IDLE: if (cmd_valid) begin
          r_idx  <= cmd_idx;
          r_base <= cmd_addr[AW-1:0];
          unique case (cmd_op)
            8'h13: begin r_cnt <= 2'd0; ts <= T_A0; end
            8'h02: begin rsp_data <= st[64*cmd_idx[3:0] +: 64]; rsp_valid <= 1'b1; end
            8'h32: begin rsp_data <= k_rdata; rsp_valid <= 1'b1; end
            8'h04: ts <= T_RDMEM;
            8'h05: begin key[cmd_idx[1:0]] <= cmd_data; rsp_valid <= 1'b1; end
            8'h01, 8'h03, 8'h20, 8'h21, 8'h22, 8'h23,
            8'h30, 8'h31, 8'h35, 8'h36: rsp_valid <= 1'b1;
            8'h06: ts <= T_LD0;
            8'h07: ts <= T_SV0;
            8'h10, 8'h11: ts <= T_WAITF;
            8'h12: begin
              r_node <= (32'd1 << cmd_idx) | cmd_data[31:0];
              r_left <= cmd_idx;
              ts <= (cmd_idx == 5'd0) ? T_RSP : T_M0;
            end
            8'h24: begin
              r_wbase <= cmd_addr[AW-1:0];
              r_pairs <= cmd_data[31:0];
              ts <= (cmd_data[31:0] == 32'd0) ? T_RSP : T_F0;
            end
            8'h33, 8'h34: ts <= T_WAITK;
            8'h40, 8'h41: begin r_poly <= cmd_op[0]; ts <= T_GF; end
            default: ts <= T_RSP;
          endcase
        end
        T_RSP:   begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_RDMEM: begin rsp_data <= a_rdata; rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_WAITF: if (f_done) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_WAITK: if (!k_busy) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_LD0: ts <= T_LD1;
        T_LD1: ts <= T_LD2;
        T_LD2: begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_SV0: ts <= T_SV1;
        T_SV1: begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_M0: ts <= T_M1;
        T_M1: ts <= T_M2;
        T_M2: ts <= T_M3;
        T_M3: ts <= T_MWAIT;
        T_MWAIT: if (f_done) begin
          r_node <= {1'b0, r_node[31:1]};
          r_base <= r_base + AW'(4);
          r_left <= r_left - 5'd1;
          if (r_left == 5'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
          else ts <= T_M0;
        end
        T_F0: ts <= T_F1;
        T_F1: ts <= T_F2;
        T_F2: ts <= T_F3;
        T_F3: ts <= T_F4;
        T_F4: ts <= T_FSUB;
        T_FSUB: ts <= T_FMUL;
        T_FMUL: ts <= T_FW0;
        T_FW0: ts <= T_FW1;
        T_FW1: begin
          r_base  <= r_base + AW'(8);
          r_wbase <= r_wbase + AW'(4);
          r_pairs <= r_pairs - 32'd1;
          if (r_pairs == 32'd1) begin rsp_valid <= 1'b1; ts <= T_IDLE; end
          else ts <= T_F0;
        end
        T_GF: begin rsp_valid <= 1'b1; ts <= T_IDLE; end
        T_A0: ts <= T_ABS;
        T_ABS: begin r_cnt <= r_cnt + 2'd1; if (r_cnt == 2'd3) ts <= T_A5; end
        T_A5: ts <= T_WAITF;
        default: ts <= T_IDLE;
      endcase
    end
  end
  wire unused = &{1'b0, accept, f_busy, cmd_addr[23:AW]};
endmodule
`default_nettype wire
