// Stateful schoolbook multiply-add in Fp[u]/(u^5-3). One shared base
// product and one add/sub datapath. External state A and R stay live for
// all 25 terms; the five output coefficients are committed together.
`default_nettype none
module qsag_fp5_seq (
  input wire clk, rst, start,
  input wire [1:0] op,            // MULADD, HORNER, FOLD, SUMCHECK
  input wire [31:0] count,        // Horner terms, fold pairs, or polynomial degree
  input wire [15:0] base, dest,
  input wire [319:0] a, r,
  output wire [63:0] mul_a, mul_b,
  input wire [63:0] product,
  output logic rd_a, rd_b, write_a,
  output logic [15:0] addr_a, addr_b,
  input wire [63:0] qa, qb,
  output logic [63:0] store_data,
  output logic [4:0] lane_we,
  output logic [319:0] lane_data,
  output wire done, checked,
  output logic bad,
  output wire [15:0] next_dest
);
  localparam logic [1:0] MULADD=0, HORNER=1, FOLD=2, SUMCHECK=3;
  typedef enum logic [3:0] {IDLE, CHECK_RD, CHECK_ADD, CHECK_EXTRA,
    ZERO_A, DIFF_RD, DIFF_WRITE, COEFF_RD, COEFF_INIT, TERM,
    COMMIT, STORE, FINISH} state_t;
  state_t state;
  logic [1:0] mode;
  logic [31:0] remaining;
  logic [15:0] src, dst, check_ptr, origin;
  logic [2:0] k, i;
  logic [1:0] repetition;
  logic [63:0] acc;
  logic [63:0] result [5];
  // j is the unique R index producing output k with A[i]. Each
  // term that crosses degree five contributes three copies.
  wire wrap_term = i > k;
  wire [2:0] j = k - i + (wrap_term ? 3'd5 : 3'd0);
  assign mul_a = a[64*i +: 64];
  assign mul_b = r[64*j +: 64];
  logic [63:0] add_a, add_b;
  wire [63:0] sum;
  qsag_gl64_addsub u_acc (.a(add_a), .b(add_b), .sub(state == DIFF_WRITE), .r(sum));
  assign done = state == FINISH;
  assign checked = done && mode == SUMCHECK;
  assign next_dest = dst;
  always_comb begin
    rd_a = 0; rd_b = 0; write_a = 0;
    addr_a = src + {13'd0,k}; addr_b = addr_a + 16'd5;
    store_data = result[k];
    lane_we = 0; lane_data = 0;
    add_a = acc; add_b = product;
    case (state)
      CHECK_RD: begin rd_a = 1; addr_a = check_ptr; end
      CHECK_ADD, CHECK_EXTRA: add_b = qa;
      ZERO_A: lane_we = 5'b11111;
      DIFF_RD: begin rd_a = 1; rd_b = 1; end
      DIFF_WRITE: begin
        add_a = qb; add_b = qa;
        lane_we[k] = 1; lane_data[64*k +: 64] = sum;
      end
      COEFF_RD: rd_a = 1;
      COMMIT: begin
        lane_we = 5'b11111;
        for (int l=0; l<5; l++) lane_data[64*l +: 64] = result[l];
      end
      STORE: begin rd_a = 1; write_a = 1; addr_a = dst + {13'd0,k}; end
      default: ;
    endcase
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      state <= IDLE; bad <= 0; mode <= 0; remaining <= 0; acc <= 0;
      src <= 0; dst <= 0; check_ptr <= 0; origin <= 0; k <= 0; i <= 0; repetition <= 0;
      for (int n=0; n<5; n++) result[n] <= 0;
    end
    else case (state)
      IDLE: if (start) begin
        mode <= op; remaining <= count; src <= base; origin <= base; dst <= dest;
        k <= 0; acc <= 0; bad <= 0;
        case (op)
          MULADD: state <= COEFF_RD;
          HORNER: state <= count == 0 ? FINISH : COEFF_RD;
          FOLD: state <= count == 0 ? FINISH : DIFF_RD;
          SUMCHECK: begin
            // Coefficients are in ascending power order as in verify_sumcheck.
            if (count == 2 || count == 3 || count == 4 || count == 9) begin
              check_ptr <= base + 16'(count * 5);
              src <= base + 16'(count * 5);
              state <= CHECK_RD;
            end else begin bad <= 1; state <= FINISH; end
          end
        endcase
      end
      CHECK_RD: state <= CHECK_ADD;
      CHECK_ADD: begin
        acc <= sum;
        if (check_ptr == origin + {13'd0,k}) state <= CHECK_EXTRA;
        else begin check_ptr <= check_ptr - 5; state <= CHECK_RD; end
      end
      CHECK_EXTRA: begin // qa holds c0 across this extra cycle
        if (sum != a[64*k +: 64]) bad <= 1;
        acc <= 0;
        if (k == 4) begin k <= 0; state <= ZERO_A; end
        else begin k <= k+1'b1; check_ptr <= src + {13'd0,k} + 1'b1; state <= CHECK_RD; end
      end
      ZERO_A: begin remaining <= remaining + 1; state <= COEFF_RD; end
      DIFF_RD: state <= DIFF_WRITE;
      DIFF_WRITE: begin
        if (k == 4) begin k <= 0; state <= COEFF_RD; end
        else begin k <= k+1'b1; state <= DIFF_RD; end
      end
      COEFF_RD: state <= COEFF_INIT;
      COEFF_INIT: begin acc <= qa; i <= 0; repetition <= 0; state <= TERM; end
      TERM: begin
        acc <= sum;
        if (wrap_term && repetition != 2) repetition <= repetition + 1'b1;
        else begin
          repetition <= 0;
          if (i == 4) begin
            result[k] <= sum;
            if (k == 4) begin k <= 0; state <= COMMIT; end
            else begin k <= k+1'b1; state <= COEFF_RD; end
          end else i <= i+1'b1;
        end
      end
      COMMIT: begin
        if (mode == FOLD) state <= STORE;
        else if (mode == MULADD || remaining == 1) state <= FINISH;
        else begin
          remaining <= remaining - 1;
          src <= mode == SUMCHECK ? src - 16'd5 : src + 16'd5;
          state <= COEFF_RD;
        end
      end
      STORE: begin
        if (k == 4) begin
          k <= 0; dst <= dst + 5; src <= src + 10; remaining <= remaining - 1;
          state <= remaining == 1 ? FINISH : DIFF_RD;
        end else k <= k+1'b1;
      end
      FINISH: state <= IDLE;
      default: state <= IDLE;
    endcase
  end
endmodule
`default_nettype wire
