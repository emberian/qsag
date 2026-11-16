// QSAG-NI shared field & 4-way C-slowed Poseidon2/Canopy datapath:
//   * Twelve shared 64x64 Goldilocks Dadda-CSA partial-product trees serve:
//       - 1-clock GoldilocksExt4 multiply-add  E0 <- E0 * E1 + E2  (9 Tower Karatsuba products)
//       - 1-clock GoldilocksExt4 base-scalar multiply  E0 <- E0 * st[4]  (4 products)
//       - 1-clock Goldilocks base multiply  st[0] <- st[0] * st[1]  (1 product)
//       - Width-12 Poseidon2 S-boxes in both 1-slot sequential mode (`op_perm` / `op_canopy`)
//         and 4-way C-slowed batch mode (`op_perm4` / `op_canopy4`), overlapping the decoupled
//         hierarchical-CSE linear layers (`qsag_p2_me`, `qsag_p2_mi_tail`, `qsag_p2_mi_apply`)
//         across 4 independent 12-lane state slots (`st_b[0..3]`) with zero multi-stage CPA chains.
`default_nettype none
`include "qsag_asic_gen_params.svh"

module qsag_asic_ext4_p2_shared (
  input  wire         clk,
  input  wire         rst,
  // Operations (accepted in S_IDLE)
  input  wire         op_perm,      // 1-slot Poseidon2-12 on slot 0
  input  wire         op_canopy,    // 1-slot Canopy node on slot 0
  input  wire         op_perm4,     // 4-way C-slowed Poseidon2-12 across slots 0..3
  input  wire         op_canopy4,   // 4-way C-slowed Canopy node across slots 0..3
  input  wire         op_emuladd,   // slot 0: E0 <- E0 * E1 + E2  (1 clock, 9 trees)
  input  wire         op_emulbase,  // slot 0: E0 <- E0 * st[4]    (1 clock, 4 trees)
  input  wire         op_eadd,      // slot 0: E0 <- E0 + E2       (1 clock)
  input  wire         op_esub,      // slot 0: E0 <- E0 - E2       (1 clock)
  input  wire         op_glmul,     // slot 0: st[0] <- st[0]*st[1](1 clock)
  // Slot-addressed register bank read/write
  input  wire [1:0]   wr_slot,
  input  wire [11:0]  wr_en,
  input  wire [767:0] wr_data,
  input  wire [1:0]   rd_slot,
  output wire [767:0] st_o,         // slot 0 flat view
  output wire [767:0] st_rd_o,      // rd_slot flat view
  output wire         busy,
  output logic        done
);
  localparam int FW = `QSAG_FOLD_W;
  localparam int NJ = `QSAG_FOLD_NJ;

  typedef enum logic [3:0] {
    S_IDLE,
    // 1-slot states
    S1_INIT, S1_F1, S1_F2, S1_F3, S1_F4, S1_FM,
    S1_P1, S1_P2, S1_P3, S1_PM, S1_FF,
    // 4-slot C-slowed states
    S4_INIT, S4_FULL, S4_PART, S4_FF
  } state_t;

  state_t      state;
  logic [63:0] st_b     [4][12];
  logic [63:0] t_b      [12];
  logic [63:0] me_pipe  [12];
  logic [63:0] ff_b     [4][4];
  logic [63:0] p_sq     [4];
  logic [63:0] p_p3     [4];
  logic [63:0] p_p4     [4];
  logic [63:0] p_p7     [4];
  logic [63:0] s_tail_q [4];
  logic [4:0]  rnd;
  logic [4:0]  sub;
  logic [6:0]  pcyc;
  logic        canopy_q;

  for (genvar l = 0; l < 12; l++) begin : g_st_out
    assign st_o[64*l +: 64]    = st_b[0][l];
    assign st_rd_o[64*l +: 64] = st_b[rd_slot][l];
  end
  assign busy = (state != S_IDLE);

  // 4-slot partial-round pipeline indices
  wire [6:0] pm1   = pcyc - 7'd1;
  wire [6:0] pm2   = pcyc - 7'd2;
  wire [6:0] pm3   = pcyc - 7'd3;
  wire       act_a = (pcyc < 7'd88);
  wire       act_b = (pcyc >= 7'd1) && (pcyc < 7'd89);
  wire       act_c = (pcyc >= 7'd2) && (pcyc < 7'd90);
  wire       act_m = (pcyc >= 7'd3);
  wire [1:0] sA    = pcyc[1:0];
  wire [1:0] sB    = pm1[1:0];
  wire [1:0] sC    = pm2[1:0];
  wire [1:0] sM    = pm3[1:0];
  wire [4:0] rM    = 5'd4 + pm3[6:2];

  // 4-slot full-round sub-indices: sub = 0..15 drives trees for slot sub[3:2], step sub[1:0];
  // sub = 4, 8, 12, 16 drives M_E writeback for slot ((sub >> 2) - 1).
  wire [1:0] f4_slot = sub[3:2];
  wire [1:0] f4_step = sub[1:0];
  wire       f4_me_en = (sub == 5'd4) || (sub == 5'd8) || (sub == 5'd12) || (sub == 5'd16);
  wire [2:0] f4_me_q  = sub[4:2] - 3'd1;
  wire [1:0] f4_me_s  = f4_me_q[1:0];

  // ---------------------------------------------------------------- 9-product Karatsuba inputs
  wire [575:0] ka, kb;
  qsag_ext4_kara_inputs u_ka (.a(st_o[255:0]),   .q(ka));
  qsag_ext4_kara_inputs u_kb (.a(st_o[511:256]), .q(kb));

  // ---------------------------------------------------------------- 12 shared multiplier trees
  logic [63:0] ma [12];
  logic [63:0] mb [12];
  wire [127:0]  ps [12];
  wire [127:0]  pc [12];
  wire [FW-1:0] fx [12];
  wire [FW-1:0] fy [12];
  wire [63:0]   pr [12];

  always_comb begin
    for (int m = 0; m < 12; m++) begin
      ma[m] = (m < 9) ? ka[64*m +: 64] : 64'd0;
      mb[m] = (m < 9) ? kb[64*m +: 64] : 64'd0;
    end
    unique case (state)
      S_IDLE: begin
        if (op_emulbase) begin
          for (int i = 0; i < 4; i++) begin
            ma[i] = st_b[0][i];
            mb[i] = st_b[0][4];
          end
        end else if (op_glmul) begin
          ma[0] = st_b[0][0];
          mb[0] = st_b[0][1];
        end
      end
      S1_F1: for (int m = 0; m < 12; m++) begin ma[m] = st_b[0][m]; mb[m] = st_b[0][m]; end
      S1_F2: for (int m = 0; m < 12; m++) begin ma[m] = t_b[m];     mb[m] = st_b[0][m]; end
      S1_F3: for (int m = 0; m < 12; m++) begin ma[m] = t_b[m];     mb[m] = t_b[m];     end
      S1_F4: for (int m = 0; m < 12; m++) begin ma[m] = t_b[m];     mb[m] = st_b[0][m]; end
      S1_P1: begin ma[0] = st_b[0][0]; mb[0] = st_b[0][0]; end
      S1_P2: begin
        ma[0] = p_sq[0]; mb[0] = st_b[0][0];
        ma[1] = p_sq[0]; mb[1] = p_sq[0];
      end
      S1_P3: begin ma[0] = p_p3[0]; mb[0] = p_p4[0]; end
      S4_FULL: if (!sub[4]) begin
        for (int m = 0; m < 12; m++) begin
          ma[m] = (f4_step == 2'd0) ? st_b[f4_slot][m] : t_b[m];
          mb[m] = (f4_step == 2'd2) ? t_b[m]           : st_b[f4_slot][m];
        end
      end
      S4_PART: begin
        ma[0] = st_b[sA][0]; mb[0] = st_b[sA][0];
        ma[1] = p_sq[sB];    mb[1] = st_b[sB][0];
        ma[2] = p_sq[sB];    mb[2] = p_sq[sB];
        ma[3] = p_p3[sC];    mb[3] = p_p4[sC];
      end
      default: ;
    endcase
  end

  for (genvar m = 0; m < 12; m++) begin : g_mul
    qsag_gl64_mul_tree u_tree (.a(ma[m]), .b(mb[m]), .s(ps[m]), .c(pc[m]));
    qsag_gl64_fold     u_fold (.s(ps[m]), .c(pc[m]), .x(fx[m]), .y(fy[m]));
    qsag_gl64_final_par #(.W(FW), .NJ(NJ)) u_final (.x(fx[m]), .y(fy[m]), .r(pr[m]));
  end

  // 9-product Karatsuba reconstruction
  wire [575:0] kp;
  wire [255:0] kr;
  for (genvar m = 0; m < 9; m++) begin : g_kp
    assign kp[64*m +: 64] = pr[m];
  end
  qsag_ext4_kara_combine u_kc (.p(kp), .z(st_o[767:512]), .r(kr));

  // ---------------------------------------------------------------- Poseidon2 linear layers
  logic [4:0] rc_slot;
  always_comb begin
    if (state == S1_INIT || state == S4_INIT) rc_slot = 5'd0;
    else if (state == S4_PART)                rc_slot = rM + 5'd1;
    else                                      rc_slot = rnd + 5'd1;
  end
  wire [767:0] rc;
  qsag_p2_rc u_rc (.slot(rc_slot), .rc(rc));

  logic [767:0] me_in, ff_in;
  wire  [767:0] me_out;
  wire  [255:0] ff_w;
  always_comb begin
    for (int l = 0; l < 12; l++) begin
      if (state == S1_INIT)      me_in[64*l +: 64] = st_b[0][l];
      else if (state == S4_INIT) me_in[64*l +: 64] = st_b[sub[1:0]][l];
      else if (state == S1_FM)   me_in[64*l +: 64] = t_b[l];
      else                       me_in[64*l +: 64] = me_pipe[l];
      ff_in[64*l +: 64] = (state == S4_INIT) ? st_b[sub[1:0]][l] : st_b[0][l];
    end
  end
  qsag_p2_me        u_me (.x(me_in), .rc(rc), .y(me_out));
  qsag_p2_canopy_ff u_ff (.x(ff_in), .ff(ff_w));

  // Split M_I: early tail sum on lanes 1..11 + fast 4-input lane apply
  logic [703:0] tail_in, mi_xhi;
  logic [63:0]  mi_x0, mi_stail;
  wire  [63:0]  mi_s_tail;
  wire  [767:0] mi_out;
  always_comb begin
    for (int l = 1; l < 12; l++) begin
      tail_in[64*(l-1) +: 64] = (state == S4_PART) ? st_b[sA][l] : st_b[0][l];
      mi_xhi[64*(l-1) +: 64]  = (state == S4_PART) ? st_b[sM][l] : st_b[0][l];
    end
    mi_x0    = (state == S4_PART) ? p_p7[sM]     : p_p7[0];
    mi_stail = (state == S4_PART) ? s_tail_q[sM] : s_tail_q[0];
  end
  qsag_p2_mi_tail  u_mi_tail  (.x_hi(tail_in), .s_tail(mi_s_tail));
  qsag_p2_mi_apply u_mi_apply (.x0(mi_x0), .x_hi(mi_xhi), .s_tail(mi_stail), .rc(rc), .y(mi_out));

  // ---------------------------------------------------------------- Four modular adders (Ext4 +/- and Canopy FF)
  wire [1:0]  ff_s = (state == S4_FF) ? sub[1:0] : 2'd0;
  wire [63:0] as_r [4];
  for (genvar i = 0; i < 4; i++) begin : g_as
    wire [63:0] as_a = st_b[ff_s][i];
    wire [63:0] as_b = (state == S1_FF || state == S4_FF) ? ff_b[ff_s][i] : st_b[0][8 + i];
    qsag_gl64_addsub u_as (.a(as_a), .b(as_b), .sub(op_esub && state == S_IDLE), .r(as_r[i]));
  end

  // ---------------------------------------------------------------- Sequential control
  always_ff @(posedge clk) begin
    done <= 1'b0;
    if (rst) begin
      state    <= S_IDLE;
      rnd      <= '0;
      sub      <= '0;
      pcyc     <= '0;
      canopy_q <= 1'b0;
    end else begin
      unique case (state)
        S_IDLE: begin
          for (int l = 0; l < 12; l++) begin
            if (wr_en[l]) st_b[wr_slot][l] <= wr_data[64*l +: 64];
          end
          if (op_perm || op_canopy) begin
            state    <= S1_INIT;
            canopy_q <= op_canopy;
          end else if (op_perm4 || op_canopy4) begin
            state    <= S4_INIT;
            sub      <= 5'd0;
            canopy_q <= op_canopy4;
          end else if (op_emuladd) begin
            for (int i = 0; i < 4; i++) st_b[0][i] <= kr[64*i +: 64];
          end else if (op_emulbase) begin
            for (int i = 0; i < 4; i++) st_b[0][i] <= pr[i];
          end else if (op_eadd || op_esub) begin
            for (int i = 0; i < 4; i++) st_b[0][i] <= as_r[i];
          end else if (op_glmul) begin
            st_b[0][0] <= pr[0];
          end
        end

        // ---------------- 1-slot Poseidon2 / Canopy
        S1_INIT: begin
          for (int l = 0; l < 12; l++) st_b[0][l] <= me_out[64*l +: 64];
          for (int i = 0; i < 4; i++)  ff_b[0][i] <= ff_w[64*i +: 64];
          rnd   <= 5'd0;
          state <= S1_F1;
        end
        S1_F1, S1_F2, S1_F3, S1_F4: begin
          for (int l = 0; l < 12; l++) t_b[l] <= pr[l];
          state <= state_t'(state + 4'd1);
        end
        S1_FM: begin
          for (int l = 0; l < 12; l++) st_b[0][l] <= me_out[64*l +: 64];
          rnd <= rnd + 5'd1;
          if (rnd == 5'd29) begin
            if (canopy_q) state <= S1_FF;
            else begin state <= S_IDLE; done <= 1'b1; end
          end else begin
            state <= (rnd == 5'd3) ? S1_P1 : S1_F1;
          end
        end
        S1_P1: begin
          p_sq[0]     <= pr[0];
          s_tail_q[0] <= mi_s_tail;
          state       <= S1_P2;
        end
        S1_P2: begin
          p_p3[0] <= pr[0];
          p_p4[0] <= pr[1];
          state   <= S1_P3;
        end
        S1_P3: begin
          p_p7[0] <= pr[0];
          state   <= S1_PM;
        end
        S1_PM: begin
          for (int l = 0; l < 12; l++) st_b[0][l] <= mi_out[64*l +: 64];
          rnd   <= rnd + 5'd1;
          state <= (rnd == 5'd25) ? S1_F1 : S1_P1;
        end
        S1_FF: begin
          for (int i = 0; i < 4; i++) st_b[0][i] <= as_r[i];
          state <= S_IDLE;
          done  <= 1'b1;
        end

        // ---------------- 4-slot C-slowed Poseidon2 / Canopy
        S4_INIT: begin
          for (int l = 0; l < 12; l++) st_b[sub[1:0]][l] <= me_out[64*l +: 64];
          for (int i = 0; i < 4; i++)  ff_b[sub[1:0]][i] <= ff_w[64*i +: 64];
          if (sub == 5'd3) begin
            sub   <= 5'd0;
            rnd   <= 5'd0;
            state <= S4_FULL;
          end else begin
            sub <= sub + 5'd1;
          end
        end
        S4_FULL: begin
          if (!sub[4]) begin
            if (f4_step == 2'd3) begin
              for (int l = 0; l < 12; l++) me_pipe[l] <= pr[l];
            end else begin
              for (int l = 0; l < 12; l++) t_b[l] <= pr[l];
            end
          end
          if (f4_me_en) begin
            for (int l = 0; l < 12; l++) st_b[f4_me_s][l] <= me_out[64*l +: 64];
          end
          if (sub == 5'd16) begin
            sub <= 5'd0;
            rnd <= rnd + 5'd1;
            if (rnd == 5'd29) begin
              if (canopy_q) state <= S4_FF;
              else begin state <= S_IDLE; done <= 1'b1; end
            end else if (rnd == 5'd3) begin
              pcyc  <= 7'd0;
              state <= S4_PART;
            end
          end else begin
            sub <= sub + 5'd1;
          end
        end
        S4_PART: begin
          if (act_a) begin
            p_sq[sA]     <= pr[0];
            s_tail_q[sA] <= mi_s_tail;
          end
          if (act_b) begin
            p_p3[sB] <= pr[1];
            p_p4[sB] <= pr[2];
          end
          if (act_c) begin
            p_p7[sC] <= pr[3];
          end
          if (act_m) begin
            for (int l = 0; l < 12; l++) st_b[sM][l] <= mi_out[64*l +: 64];
          end
          if (pcyc == 7'd90) begin
            rnd   <= 5'd26;
            sub   <= 5'd0;
            state <= S4_FULL;
          end else begin
            pcyc <= pcyc + 7'd1;
          end
        end
        S4_FF: begin
          for (int i = 0; i < 4; i++) st_b[sub[1:0]][i] <= as_r[i];
          if (sub == 5'd3) begin
            state <= S_IDLE;
            done  <= 1'b1;
          end else begin
            sub <= sub + 5'd1;
          end
        end

        default: state <= S_IDLE;
      endcase
    end
  end

  wire unused_ok = &{1'b0, f4_me_q[2], pm1[6:2], pm2[6:2]};
endmodule
`default_nettype wire
