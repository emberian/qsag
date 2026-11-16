// QSAG-NI shared field datapath: one array of 12 Goldilocks partial-product trees serves
//   * GoldilocksExt4 multiply-add  E0 <- E0 * E1 + E2   (9 Karatsuba products, one cycle), and
//   * the width-12 Poseidon2 x^7 S-boxes (12 trees in full rounds, 2 in partial rounds).
// The linear layers M_E and M_I are carry-save adder networks (no multipliers); round constants
// are added inside them. The lane-0 partial-round product enters M_I in carry-save form.
//
// State: st[0..11] (E0 = st[0..3], E1 = st[4..7], E2 = st[8..11]; Ext4 limb order
// [c0.c0, c0.c1, c1.c0, c1.c1], i.e. polynomial coefficients [v^0, v^2, v^1, v^3]).
//
// Poseidon2: 1 + 8*4 + 22*(FAST_PARTIAL ? 2 : 3) = 77 / 99 clocks.
// Full rounds fuse x^7 with M_E. FAST_PARTIAL uses two SERIAL multiplier levels
// in its second clock: (x^3 | x^4) -> x^7 -> M_I. This is a timing tradeoff,
// not a three-multiply addition chain. Canopy adds one feed-forward clock.
`default_nettype none
`include "qsag_asic_gen_params.svh"

module qsag_asic_ext4_p2_shared #(parameter bit FAST_PARTIAL = 1'b1) (
  input  wire         clk,
  input  wire         rst,
  // one-cycle operations (ignored while busy)
  input  wire         op_perm,     // start Poseidon2 permutation of st
  input  wire         op_canopy,   // start Canopy node: st[0..3] <- perm(st)[0..3] + l + 2r + 4c
  input  wire         op_emuladd,  // E0 <- E0 * E1 + E2
  input  wire         op_eadd,     // E0 <- E0 + E2
  input  wire         op_esub,     // E0 <- E0 - E2
  input  wire         op_glmul,    // st[0] <- st[0] * st[1]
  // external lane writes
  input  wire [11:0]  wr_en,
  input  wire [767:0] wr_data,
  output wire [767:0] st_o,
  output wire         busy,
  output logic        done         // pulses in the last cycle of perm / canopy
);
  localparam int FW = `QSAG_FOLD_W;
  localparam int NJ = `QSAG_FOLD_NJ;

  typedef enum logic [3:0] {S_IDLE, S_INIT, S_F1, S_F2, S_F3, S_F4, S_P1, S_P2, S_P3, S_FF} state_t;
  state_t state;
  logic [63:0] st [12];
  logic [63:0] t  [12];
  logic [63:0] ff [4];
  logic [4:0]  rnd;       // S-box layer index 0..29
  logic        canopy_q;

  for (genvar l = 0; l < 12; l++) begin : g_st
    assign st_o[64*l +: 64] = st[l];
  end
  assign busy = (state != S_IDLE);

  // ---------------------------------------------------------------- multiplier array
  wire in_perm = (state != S_IDLE);
  logic [63:0] ma [12];
  logic [63:0] mb [12];
  wire [575:0] ka, kb;
  qsag_ext4_kara_inputs u_ka (.a(st_o[255:0]), .q(ka));
  qsag_ext4_kara_inputs u_kb (.a(st_o[511:256]), .q(kb));
  always_comb begin
    for (int m = 0; m < 12; m++) begin
      ma[m] = (m < 9) ? ka[64*m +: 64] : 64'b0;
      mb[m] = (m < 9) ? kb[64*m +: 64] : 64'b0;
    end
    if (in_perm) begin
      for (int m = 0; m < 12; m++) begin
        ma[m] = (state == S_F1) ? st[m] : t[m];
        mb[m] = (state == S_F3) ? t[m] : st[m];
      end
      if (state == S_P1) begin ma[0] = st[0]; mb[0] = st[0]; end
      if (state == S_P2) begin
        ma[0] = t[0]; mb[0] = st[0]; ma[1] = t[0]; mb[1] = t[0];
        if (FAST_PARTIAL) begin ma[2] = pr[0]; mb[2] = pr[1]; end
      end
      if (state == S_P3) begin ma[0] = t[0];  mb[0] = t[1]; end
    end else if (op_glmul) begin
      ma[0] = st[0]; mb[0] = st[1];
    end
  end

  wire [127:0] ps [12];
  wire [127:0] pc [12];
  wire [FW-1:0] fx [12];
  wire [FW-1:0] fy [12];
  wire [63:0]  pr [12];
  for (genvar m = 0; m < 12; m++) begin : g_mul
    qsag_gl64_mul_tree u_tree (.a(ma[m]), .b(mb[m]), .s(ps[m]), .c(pc[m]));
  end
  for (genvar m = 0; m < 12; m++) begin : g_red
    qsag_gl64_fold u_fold (.s(ps[m]), .c(pc[m]), .x(fx[m]), .y(fy[m]));
    qsag_gl64_final_par #(.W(FW), .NJ(NJ)) u_final (.x(fx[m]), .y(fy[m]), .r(pr[m]));
  end

  // Nine canonical base products reconstruct the tower product in limb order.
  wire [63:0] ec [4];
  wire [575:0] kp;
  wire [255:0] kr;
  for (genvar m = 0; m < 9; m++) begin : g_kp
    assign kp[64*m +: 64] = pr[m];
  end
  qsag_ext4_kara_combine u_kc (.p(kp), .z(st_o[767:512]), .r(kr));
  for (genvar m = 0; m < 4; m++) begin : g_ec
    assign ec[m] = kr[64*m +: 64];
  end

  // ---------------------------------------------------------------- Poseidon2 linear layers
  wire [767:0] rc;
  wire [4:0]   slot = (state == S_INIT) ? 5'd0 : rnd + 5'd1;
  qsag_p2_rc u_rc (.slot(slot), .rc(rc));

  logic [767:0] me_in;
  wire  [767:0] me_out, mi_out, st_flat;
  wire  [255:0] ff_w;
  always_comb for (int l = 0; l < 12; l++) me_in[64*l +: 64] = (state == S_INIT) ? st[l] : pr[l];
  assign st_flat = st_o;
  qsag_p2_me u_me (.x(me_in), .rc(rc), .y(me_out));
  qsag_p2_mi_fused u_mi (.sx(fx[FAST_PARTIAL ? 2 : 0]), .sy(fy[FAST_PARTIAL ? 2 : 0]), .x(st_flat), .rc(rc), .y(mi_out));
  qsag_p2_canopy_ff u_ff (.x(st_flat), .ff(ff_w));

  // ---------------------------------------------------------------- four modular adders (Ext4 add/sub, Canopy feed-forward)
  wire [63:0] as_r [4];
  for (genvar i = 0; i < 4; i++) begin : g_as
    qsag_gl64_addsub u_as (.a(st[i]), .b((state == S_FF) ? ff[i] : st[8 + i]), .sub(op_esub && state == S_IDLE), .r(as_r[i]));
  end

  // ---------------------------------------------------------------- control
  wire full_round = (rnd < 5'd4) || (rnd >= 5'd26);
  always_ff @(posedge clk) begin
    done <= 1'b0;
    if (rst) begin
      state <= S_IDLE;
      rnd <= '0;
      canopy_q <= 1'b0;
    end else begin
      unique case (state)
        S_IDLE: begin
          for (int l = 0; l < 12; l++) if (wr_en[l]) st[l] <= wr_data[64*l +: 64];
          if (op_perm || op_canopy) begin
            state <= S_INIT;
            canopy_q <= op_canopy;
          end else if (op_emuladd) begin
            for (int i = 0; i < 4; i++) st[i] <= ec[i];
          end else if (op_eadd || op_esub) begin
            for (int i = 0; i < 4; i++) st[i] <= as_r[i];
          end else if (op_glmul) begin
            st[0] <= pr[0];
          end
        end
        S_INIT: begin
          for (int l = 0; l < 12; l++) st[l] <= me_out[64*l +: 64];
          for (int i = 0; i < 4; i++) ff[i] <= ff_w[64*i +: 64];
          rnd <= '0;
          state <= S_F1;
        end
        S_F1, S_F2, S_F3: begin
          for (int l = 0; l < 12; l++) t[l] <= pr[l];
          state <= state_t'(state + 4'd1);
        end
        S_F4: begin
          for (int l = 0; l < 12; l++) st[l] <= me_out[64*l +: 64];
          rnd <= rnd + 5'd1;
          if (rnd == 5'd29) begin
            if (canopy_q) state <= S_FF;
            else begin state <= S_IDLE; done <= 1'b1; end
          end else state <= (rnd == 5'd3) ? S_P1 : S_F1;
        end
        S_P1: begin t[0] <= pr[0]; state <= S_P2; end
        S_P2: begin
          if (FAST_PARTIAL) begin
            for (int l = 0; l < 12; l++) st[l] <= mi_out[64*l +: 64];
            rnd <= rnd + 5'd1;
            state <= (rnd == 5'd25) ? S_F1 : S_P1;
          end else begin t[0] <= pr[0]; t[1] <= pr[1]; state <= S_P3; end
        end
        S_P3: begin
          for (int l = 0; l < 12; l++) st[l] <= mi_out[64*l +: 64];
          rnd <= rnd + 5'd1;
          state <= (rnd == 5'd25) ? S_F1 : S_P1;
        end
        S_FF: begin
          for (int i = 0; i < 4; i++) st[i] <= as_r[i];
          state <= S_IDLE;
          done <= 1'b1;
        end
        default: state <= S_IDLE;
      endcase
    end
  end
  wire unused = &{1'b0, full_round, pr[2], pr[3], pr[4], pr[5], pr[6], pr[7], pr[8], pr[9], pr[10], pr[11]};
endmodule
`default_nettype wire
