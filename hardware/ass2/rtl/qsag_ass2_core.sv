// Pipelined constant-time ASS2-0P5 / Dregg-64 core (`DIT = 1`, FIPS 140-3 Level 4):
//   - ZERO `post_fast_i` round-reduction shortcuts!
//   - Shares `qsag_ass2_alu`'s single `qsag_ass2_add64` across ALU, effective-address, `crypto`, and `mul`.
//   - Folds `CSR`, `JAL/JALR` link (`pc + 4`), and `ALU` into `alu_q` (`a_q`), and uses sparse CSR read muxing.
module qsag_ass2_core #(
    parameter bit WITH_DEBUG_RX   = 1'b0,
    parameter int PC_BITS         = 64,
    parameter int ECAUSE_BITS     = 64,
    parameter bit MPU_FAULT_FIRST = 1'b0
) (
    input  logic        clk, rst_n, tamper_zeroize_n,
    input  logic        jtag_test_mode_i,
    input  logic        start_i, zeroize_first_i, dbg_halt_i,
    input  logic [63:0] start_pc_i,
    input  logic        arg_regs_we_i,
    input  logic [3:0]  arg_reg_addr_i,
    input  logic [63:0] arg_reg_data_i,
    output logic        mem_en_o, mem_we_o,
    output logic [7:0]  mem_wstrb_o,
    output logic [63:0] mem_addr_o, mem_wdata_o,
    input  logic [63:0] mem_rdata_i,
    input  logic        mem_ready_i,
    input  logic        mem_fault_i,
    output logic        insn_retire_o, halted_o, tampered_o, trap_o, zeroize_pulse_o,
    output logic [63:0] pc_o, ecause_o, instret_o, cycles_o, phys_cycles_o, r4_o,
    output logic        dbg_we_o,
    output logic [7:0]  dbg_byte_o,
    input  logic [63:0] dbg_in_i,
    output logic        dbg_rd_o,
    input  logic        post_clear_i  = 1'b0,
    input  logic        applet_exec_i = 1'b0,
    input  logic        ring3_enter_i = 1'b0,
    output logic        mem_fetch_o,
    output logic        mem_byte_o
);
    import qsag_ass2_pkg::*;
`ifndef SYNTHESIS
    word_t regs [16] /* verilator public_flat_rd */;
    word_t spg  [25] /* verilator public_flat_rd */;
`endif
    typedef enum logic [3:0] {
        STOP, FETCH, CAPTURE, CAP_A, CAP_B, CAP_C, CAP_D, EXECUTE, MEMORY, CRYPTO
    } phase_t;
    phase_t phase;

`ifdef GF180_SRAM_MACRO
    wire tamper_set = ~tamper_zeroize_n;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_tamper_lat (
        .D(1'b1), .E(tamper_set), .RN(rst_n), .Q(tampered_o)
    );
`else
    always_ff @(negedge rst_n or negedge tamper_zeroize_n)
        if (!tamper_zeroize_n) tampered_o <= 1'b1;
        else tampered_o <= 1'b0;
`endif

    wire srst_raw = rst_n && tamper_zeroize_n && !tampered_o && !jtag_test_mode_i && !post_clear_i;
    wire srst_n;
`ifdef GF180_SRAM_MACRO
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_srst_drv (.I(srst_raw), .Z(srst_n));
`else
    assign srst_n = srst_raw;
`endif
    word_t va_q, vb_q, vc_q, alu_q;
    logic exc_en, crypto_kicked_q, legal_q, take_branch_q;
    logic [7:0] cost_q;

    logic [31:0] ir;
    word_t       epc, evec;

    wire [3:0] op=ir[31:28], rd=ir[3:0], ra=ir[7:4], rb=ir[11:8], rc=ir[15:12], sub=ir[19:16];
    wire [7:0] imm8=ir[27:20], sidx=ir[19:12];
    wire [15:0] imm16=ir[27:12];
    wire [19:0] imm20=ir[27:8];
    assign phys_cycles_o = cycles_o;
    assign halted_o      = (phase == STOP);

    wire is_mem     = (op inside {LOAD, STORE}) || (op == SPG && rb >= 4'd4);
    wire byte_mem   = (op != SPG) && (rb == 4'd1);
    wire is_store   = (op == STORE) || (op == SPG && rb == 4'd5);
    wire is_crypto  = (op == ALU && sub >= 4'd7) || (op == GL64)
                    || (op == GF128) || (op == PERM);

    logic [63:0] pc_plus_4;
    generate
        if (PC_BITS == 64) begin : g_pcp4_64
            qsag_ass2_u8add64 u_add_pc4 (.x(pc_o), .inc(8'd4), .sum(pc_plus_4));
        end else begin : g_pcp4_narrow
            assign pc_plus_4 = {{(63 - PC_BITS){1'b0}}, (pc_o[PC_BITS:0] + {{(PC_BITS - 2){1'b0}}, 3'd4})};
        end
    endgenerate
    word_t offset, base, address;
    always_comb begin
        base   = va_q;
        offset = {{48{imm16[15]}}, imm16};
        if (phase == CAP_C) begin
            case (op)
                BR:      begin base = pc_plus_4; offset = {{42{imm20[19]}}, imm20, 2'd0}; end
                JAL:     begin base = pc_plus_4; offset = {{38{ir[27]}}, ir[27:4], 2'd0}; end
                JALR:    offset = offset << 2;
                SPG:     offset = {{53{imm8[7]}}, imm8, 3'd0};
                default: if (!byte_mem) offset = offset << 3;
            endcase
        end
    end

    word_t bank_rdata, alu_result, effective_address, crypto_rot_res;
    logic        ext_add_en, ext_add_cin, alu_cout;
    logic [63:0] ext_add_a, ext_add_b;
    logic [5:0]  crypto_rot_amt;
    qsag_ass2_alu alu(
        .addr_mode_i(phase == CAP_C),
        .addr_base_i(base),
        .addr_offset_i(offset),
        .ext_add_en_i(ext_add_en),
        .ext_add_a_i(ext_add_a),
        .ext_add_b_i(ext_add_b),
        .ext_add_cin_i(ext_add_cin),
        .crypto_rot_en_i(phase == CRYPTO),
        .crypto_rot_amt_i(crypto_rot_amt),
        .op(op),
        .fn(op == ALUI ? rb : op == IMM20 ? ra : sub),
        .flags(rc),
        .byte_idx(rb),
        .imm(op == ALUI ? {4'd0, imm16} : imm20),
        .ra(va_q),
        .rb(vb_q),
        .rc(bank_rdata),
        .pc(pc_o),
        .sum_o(effective_address),
        .cout_o(alu_cout),
        .rot_o(crypto_rot_res),
        .result(alu_result)
    );

    wire csr_read  = (op == SYS && sub == 4'd2);
    wire csr_write = (op == SYS && sub == 4'd3);
    wire unused_dbg_hi = ^dbg_in_i[63:9];

    // Sparse CSR read mux: separate the 5 full 64-bit CSRs from narrow/constant CSRs!
    wire [63:0] csr_wide = (imm8 == EVEC)    ? evec
                         : (imm8 == INSTRET) ? instret_o
                         : (imm8 == CYCLES)  ? cycles_o
                         : (imm8 == EPC)     ? epc
                         :                     ecause_o;
    word_t csr_value;
    logic  csr_read_ok;
    always_comb begin
        csr_read_ok = 1'b1;
        case (imm8)
            ARCH_ID:   csr_value = ID;
            WORD_BITS: csr_value = 64'd64;
            EVEC, INSTRET, CYCLES, EPC, ECAUSE: csr_value = csr_wide;
            FEATURES:  csr_value = 64'd15;
            DBG_IN:    begin
                csr_read_ok = WITH_DEBUG_RX;
                csr_value   = dbg_in_i[8] ? {55'd0, dbg_in_i[8:0]} : 64'd0;
            end
            EXC_EN:    csr_value = {63'd0, exc_en};
            DIT:       csr_value = 64'd1;
            default:   begin csr_read_ok = 1'b0; csr_value = 64'd0; end
        endcase
    end
    wire csr_write_ok = (imm8 inside {EVEC, POWER, INSTRET, CYCLES, EPC, ECAUSE, DBG_OUT, EXC_EN, ZEROIZE})
                      && !(applet_exec_i && (imm8 == EVEC || imm8 == EXC_EN));

    logic legal;
    always_comb case (op)
        SYS: case (sub)
            0,1,4,5,6: legal = ({imm8, ir[15:0]} == 24'd0);
            2:         legal = (ir[15:4] == 12'd0) && csr_read_ok;
            3:         legal = ({ir[15:8], rd} == 12'd0) && csr_write_ok;
            default:   legal = 1'b0;
        endcase
        LUT4:    legal = ({imm8, rc} == 12'd0);
        ALU:     legal = ({imm8, rc} == 12'd0) && (sub <= 4'd8);
        ALUI:    legal = (rb <= 4'd9) && (!(rb inside {[4'd5:4'd8]}) || imm16[15:6] == 10'd0);
        IMM20:   legal = (ra <= 4'd2);
        CMP:     legal = ({imm8, sub} == 12'd0);
        BYTE_OP: legal = (imm8 == 8'd0) && (sub == 4'd0 || ((sub == 4'd1 || sub == 4'd2) && !rb[3] && !rc[3])
                                            || (sub == 4'd3 && {rb, rc} == 8'd0));
        LOAD, STORE: legal = (rb <= 4'd1);
        BR:      legal = (ra <= 4'd3);
        JAL:     legal = 1'b1;
        JALR:    legal = (rb == 4'd0);
        SPG: case (rb)
            0:   legal = (sidx < 8'd25) && ({ra, imm8} == 12'd0);
            1,2: legal = (sidx < 8'd25) && ({rd, imm8} == 12'd0);
            3:   legal = ({sidx, rd, ra, imm8} == 24'd0);
            4,5: legal = (sidx < 8'd25) && (rd == 4'd0);
            default: legal = 1'b0;
        endcase
        GL64:  legal = (imm8 == 8'd0) && (sub == 4'd0 || (rc == 4'd0 && (sub inside {4'd1, 4'd2} ||
                        (sub == 4'd3 && rb == 4'd0) || (sub inside {[4'd4:4'd6]} && rd < 4'd5 && ra < 4'd5 && rb < 4'd5))));
        GF128: legal = ({imm8, rc} == 12'd0) && (rd < 4'd12) && (ra < 4'd12) && (rb < 4'd12) && (sub <= 4'd1);
        PERM:  legal = (ir[15:0] == 16'd0) && ((sub == 4'd0 && (imm8 == 8'd12 || imm8 == 8'd24)) ||
                        ((sub == 4'd1 || sub == 4'd2) && imm8 == 8'd0));
        default: legal = 1'b0;
    endcase

    wire take_branch_d = (ra == 4'd0) ? (vb_q == 64'd0) : (ra == 4'd1) ? (vb_q != 64'd0)
                       : (ra == 4'd2) ? vb_q[63] : !vb_q[63];

    wire       mem_aligned = byte_mem || (address[2:0] == 3'd0);
    wire [7:0] load_byte   = mem_rdata_i[{address[2:0], 3'b000} +: 8];

    assign mem_fetch_o = (phase == FETCH);
    assign mem_byte_o  = byte_mem;

    // Hold `pc_o` on `mem_addr_o` through `CAPTURE` so combinational `qsag_ass2_irom` needs 0 FFs!
    assign mem_addr_o  = (phase == FETCH || phase == CAPTURE) ? pc_o : address;
    assign mem_en_o    = (phase == FETCH && pc_o[1:0] == 2'd0 && !dbg_halt_i)
                       || (phase == EXECUTE && legal_q && is_mem && (MPU_FAULT_FIRST || mem_aligned));
    assign mem_we_o    = (phase == EXECUTE) && legal_q && is_mem && (MPU_FAULT_FIRST || mem_aligned) && is_store;
    assign mem_wstrb_o = !mem_we_o ? 8'd0 : byte_mem ? (8'b1 << address[2:0]) : 8'hff;
    assign mem_wdata_o = (op == SPG) ? vc_q : byte_mem ? {8{vb_q[7:0]}} : vb_q;

    logic kick, c_done, c_we, c_re;
    logic [4:0] c_a, c_w;
    word_t c_data, c_result;
    logic [5:0] bank_raddr;
    always_comb begin
        case (phase)
            CAP_A:   bank_raddr = {2'b00, ra};
            CAP_B:   bank_raddr = {2'b00, (op == STORE || op == BR) ? rd : rb};
            CAP_C:   bank_raddr = (op == SPG)
                                ? ((sidx < 8'd25) ? {1'b1, sidx[4:0]} : 6'd0)
                                : {2'b00, rc};
            default: bank_raddr = {1'b1, c_a};
        endcase
    end
    wire bank_re = (phase == CAP_A) || (phase == CAP_B) || (phase == CAP_C)
                 || (phase == CRYPTO && c_re);

    wire       cap_we  = (phase == CAP_B) || (phase == CAP_C) || (phase == CAP_D);
    wire [1:0] cap_idx = (phase == CAP_B) ? 2'd0 : (phase == CAP_C) ? 2'd1 : 2'd2;
    assign kick = (phase == EXECUTE) && !crypto_kicked_q && legal_q && is_crypto;

    wire [63:0] cap_alu_in = (op == SYS) ? csr_value
                           : (op == JAL || op == JALR) ? pc_plus_4
                           : alu_result;

    wire zeroize, ring3_scrub;
    qsag_ass2_crypto crypto(
        .clk(clk), .srst_n(srst_n), .cancel_i(zeroize || ring3_scrub),
        .cap_we_i(cap_we), .cap_idx_i(cap_idx), .cap_data_i(bank_rdata),
        .alu_i(cap_alu_in),
        .address_o(address), .va_o(va_q), .vb_o(vb_q), .vc_o(vc_q), .alu_o(alu_q),
        .ext_add_en_o(ext_add_en), .ext_add_a_o(ext_add_a),
        .ext_add_b_o(ext_add_b), .ext_add_cin_o(ext_add_cin),
        .ext_add_sum_i(effective_address), .ext_add_cout_i(alu_cout),
        .rot_amt_o(crypto_rot_amt), .rot_res_i(crypto_rot_res),
        .kick(kick),
        .op(op), .sub(sub), .rd(rd), .ra(ra), .rb(rb),
        .keccak_12_i(imm8 == 8'd12),
        .re_o(c_re), .addr_a(c_a), .waddr(c_w), .lane_a(bank_rdata),
        .we(c_we), .wdata(c_data), .scalar(c_result), .done(c_done)
    );

    logic [2:0] mem_cause_q;
    logic [2:0] trap_cause;
    always_comb begin
        trap_cause = 3'd0;
        if (phase == FETCH && !dbg_halt_i) begin
            if (pc_o[1:0] != 2'd0) trap_cause = MIS_PC;
            else if (mem_fault_i)  trap_cause = MEM_FAULT;
        end else if (phase == EXECUTE) begin
            if (!legal_q) trap_cause = ILLEGAL;
            else if (op == SYS && sub == 4'd0 && exc_en) trap_cause = ENVCALL;
            else if (op == JALR && address[1:0] != 2'd0) trap_cause = MIS_PC;
        end else if (phase == MEMORY) begin
            trap_cause = mem_cause_q;
        end
    end

    wire retire  = !dbg_halt_i && ((phase == EXECUTE && trap_cause == 3'd0 && !is_mem && !is_crypto)
                 || (phase == MEMORY && trap_cause == 3'd0)
                 || (phase == CRYPTO && c_done));
    wire start   = halted_o && start_i;
    assign ring3_scrub     = start && ring3_enter_i;
    assign zeroize_pulse_o = retire && !(trap_cause != 3'd0) && (op == SYS)
                           && (sub == 4'd4 || (csr_write && imm8 == ZEROIZE && va_q[0]));
    assign zeroize = dbg_halt_i || (start && zeroize_first_i) || zeroize_pulse_o;
    wire s_clear = zeroize || ring3_scrub || (retire && op == SPG && rb == 4'd3);
    wire s_we    = (phase == CRYPTO && c_we)
                 || (retire && op == SPG && (rb == 4'd1 || rb == 4'd2 || rb == 4'd4));
    wire [4:0]  s_waddr = (phase == CRYPTO) ? c_w : sidx[4:0];
    wire [63:0] s_wdata = (phase == CRYPTO) ? c_data
                        : (rb == 4'd4) ? mem_rdata_i
                        : (rb == 4'd2) ? (vc_q ^ va_q) : va_q;

    logic r_we_inst;
    word_t r_wdata_inst;
    always_comb begin
        r_we_inst    = 1'b1;
        r_wdata_inst = alu_q;
        case (op)
            SYS:  r_we_inst = (sub == 4'd2);
            ALU:  if (sub >= 4'd7) r_wdata_inst = c_result;
            LOAD: r_wdata_inst = byte_mem ? {56'd0, load_byte} : mem_rdata_i;
            SPG:  begin r_we_inst = (rb == 4'd0); r_wdata_inst = vc_q; end
            GL64: begin r_we_inst = (sub < 4'd4); r_wdata_inst = c_result; end
            STORE, BR, GF128, PERM: r_we_inst = 1'b0;
            default: ;
        endcase
    end

    wire reg_arg_we = halted_o && !start && arg_regs_we_i;
    wire reg_we     = reg_arg_we || (retire && r_we_inst);
    wire [3:0]  reg_waddr = reg_arg_we ? arg_reg_addr_i : rd;
    wire [63:0] reg_wdata = reg_arg_we ? arg_reg_data_i : r_wdata_inst;

    qsag_ass2_regbank u_regbank (
        .clk(clk), .srst_n(srst_n),
        .zeroize_i(zeroize), .s_clear_i(s_clear), .zeroize_r3_spg_i(ring3_scrub),
        .r_we_i(reg_we), .r_waddr_i(reg_waddr), .r_wdata_i(reg_wdata),
        .s_we_i(s_we), .s_waddr_i(s_waddr), .s_wdata_i(s_wdata),
        .bank_re_i(bank_re), .bank_raddr_i(bank_raddr), .bank_rdata_o(bank_rdata),
        .r4_o(r4_o)
`ifndef SYNTHESIS
        , .dbg_regs_o(regs), .dbg_spg_o(spg)
`endif
    );

    logic [7:0] cost;
    always_comb begin
        cost = 8'd1;
        case (op)
            LOAD, STORE: cost = 8'd2;
            SPG:  if (rb >= 4'd4) cost = 8'd2;
            ALU:  if (sub >= 4'd7) cost = 8'd4;
            GL64: case (sub)
                4'd0: cost = 8'd4;
                4'd3: cost = 8'd12;
                4'd4: cost = 8'd104;
                4'd5, 4'd6: cost = 8'd5;
                default: ;
            endcase
            GF128: if (sub == 4'd0) cost = 8'd4;
            PERM:  cost = (sub == 4'd0) ? imm8 : (sub == 4'd1) ? 8'd216 : 8'd120;
            default: ;
        endcase
    end

    wire trapping = (trap_cause != 3'd0);
    qsag_ass2_cg_dff #(.W(32)) u_ir (
        .clk(clk), .rst_n(srst_n), .en(phase == CAPTURE),
        .d(pc_o[2] ? mem_rdata_i[63:32] : mem_rdata_i[31:0]), .q(ir)
    );
    wire [63:0] next_pc = (trapping && exc_en) ? evec
                        : (phase == STOP && start) ? start_pc_i
                        : (op == SYS && sub == 4'd1) ? {epc[63:2], 2'd0}
                        : ((op == BR && take_branch_q) || op == JAL || op == JALR) ? address
                        : pc_plus_4;

    generate
        if (PC_BITS == 64) begin : g_csr_pc64
            logic [61:0] evec_hi;
            assign evec = {evec_hi, 2'b00};
            qsag_ass2_cg_dff #(.W(62)) u_evec (
                .clk(clk), .rst_n(srst_n), .en(retire && !trapping && csr_write && imm8 == EVEC),
                .d(va_q[63:2]), .q(evec_hi)
            );
            qsag_ass2_cg_dff #(.W(64)) u_epc (
                .clk(clk), .rst_n(srst_n),
                .en((trapping && exc_en) || (retire && !trapping && csr_write && imm8 == EPC)),
                .d(trapping ? ((trap_cause == ENVCALL) ? pc_plus_4 : pc_o) : va_q), .q(epc)
            );
            qsag_ass2_cg_dff #(.W(64)) u_pc (
                .clk(clk), .rst_n(srst_n),
                .en((trapping && exc_en) || (!trapping && retire) || (phase == STOP && start)),
                .d(next_pc), .q(pc_o)
            );
        end else begin : g_csr_pc_narrow
            logic [PC_BITS-3:0] evec_hi_n;
            logic [PC_BITS-1:0] epc_n;
            logic [PC_BITS:0]   pc_n;
            wire  [PC_BITS-1:0] epc_d_n = trapping ? ((trap_cause == ENVCALL) ? pc_plus_4[PC_BITS-1:0] : pc_o[PC_BITS-1:0]) : va_q[PC_BITS-1:0];
            assign evec = {{(64 - PC_BITS){1'b0}}, evec_hi_n, 2'b00};
            assign epc  = {{(64 - PC_BITS){1'b0}}, epc_n};
            assign pc_o = {{(63 - PC_BITS){1'b0}}, pc_n};
            qsag_ass2_cg_dff #(.W(PC_BITS - 2)) u_evec (
                .clk(clk), .rst_n(srst_n), .en(ring3_scrub || (retire && !trapping && csr_write && imm8 == EVEC)),
                .d(ring3_scrub ? '0 : va_q[PC_BITS-1:2]), .q(evec_hi_n)
            );
            qsag_ass2_cg_dff #(.W(PC_BITS)) u_epc (
                .clk(clk), .rst_n(srst_n),
                .en(ring3_scrub || (trapping && exc_en) || (retire && !trapping && csr_write && imm8 == EPC)),
                .d(ring3_scrub ? '0 : epc_d_n), .q(epc_n)
            );
            qsag_ass2_cg_dff #(.W(PC_BITS + 1)) u_pc (
                .clk(clk), .rst_n(srst_n),
                .en((trapping && exc_en) || (!trapping && retire) || (phase == STOP && start)),
                .d({(|next_pc[63:PC_BITS]), next_pc[PC_BITS-1:0]}), .q(pc_n)
            );
        end

        if (ECAUSE_BITS == 64) begin : g_csr_ec64
            qsag_ass2_cg_dff #(.W(64)) u_ecause (
                .clk(clk), .rst_n(srst_n),
                .en(ring3_scrub || trapping || (retire && !trapping && csr_write && imm8 == ECAUSE)),
                .d(ring3_scrub ? 64'd0 : trapping ? 64'(trap_cause) : va_q), .q(ecause_o)
            );
        end else begin : g_csr_ec_narrow
            logic [ECAUSE_BITS-1:0] ecause_n;
            assign ecause_o = {{(64 - ECAUSE_BITS){1'b0}}, ecause_n};
            qsag_ass2_cg_dff #(.W(ECAUSE_BITS)) u_ecause (
                .clk(clk), .rst_n(srst_n),
                .en(ring3_scrub || trapping || (retire && !trapping && csr_write && imm8 == ECAUSE)),
                .d(ring3_scrub ? '0 : trapping ? ECAUSE_BITS'(trap_cause) : va_q[ECAUSE_BITS-1:0]), .q(ecause_n)
            );
        end
    endgenerate

    wire [63:0] instret_next, cyc_next;
    qsag_ass2_u8add64 u_add_instret (.x(instret_o), .inc(8'd1), .sum(instret_next));
    qsag_ass2_u8add64 u_add_cycles  (.x(cycles_o),  .inc(trapping ? 8'd1 : cost_q), .sum(cyc_next));

    qsag_ass2_cg_dff #(.W(64), .KEEP_EN(1'b1)) u_instret (
        .clk(clk), .rst_n(srst_n), .en(retire && !trapping),
        .d((csr_write && imm8 == INSTRET) ? va_q : instret_next), .q(instret_o)
    );
    qsag_ass2_cg_dff #(.W(64)) u_cycles (
        .clk(clk), .rst_n(srst_n), .en(trapping || retire),
        .d((!trapping && csr_write && imm8 == CYCLES) ? va_q : cyc_next),
        .q(cycles_o)
    );

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            phase <= STOP; mem_cause_q <= 3'd0; exc_en <= 1'b0;
            legal_q <= 1'b0; take_branch_q <= 1'b0; cost_q <= 8'd1;
            insn_retire_o <= 1'b0; dbg_we_o <= 1'b0; dbg_byte_o <= 8'd0;
            dbg_rd_o <= 1'b0; trap_o <= 1'b0; crypto_kicked_q <= 1'b0;
        end else begin
            insn_retire_o <= retire;
            trap_o        <= trapping;
            dbg_we_o      <= 1'b0;
            dbg_rd_o      <= 1'b0;

            if (phase == CAP_A) begin
                legal_q <= legal;
                cost_q  <= cost;
            end
            if (phase == CAP_D) take_branch_q <= take_branch_d;

            if (dbg_halt_i) begin
                phase <= STOP;
                exc_en <= 1'b0;
                crypto_kicked_q <= 1'b0;
            end else if (trapping) begin
                crypto_kicked_q <= 1'b0;
                if (exc_en) begin exc_en <= 1'b0; phase <= FETCH; end
                else phase <= STOP;
            end else if (retire) begin
                crypto_kicked_q <= 1'b0;
                phase <= FETCH;
                if (op == SYS && sub == 4'd1) exc_en <= 1'b1;
                if (op == SYS && sub == 4'd5) phase  <= STOP;
                if (csr_read && imm8 == DBG_IN && alu_q[8]) dbg_rd_o <= 1'b1;
                if (csr_write) case (imm8)
                    EXC_EN:  exc_en <= va_q[0];
                    POWER:   if (va_q[0]) phase <= STOP;
                    DBG_OUT: begin dbg_we_o <= 1'b1; dbg_byte_o <= va_q[7:0]; end
                    default: ;
                endcase
            end else case (phase)
                STOP:    if (start) begin
                    if (zeroize_first_i || ring3_enter_i) exc_en <= 1'b0;
                    phase <= FETCH;
                end
                FETCH:   if (dbg_halt_i) phase <= STOP;
                         else if (mem_ready_i) phase <= CAPTURE;
                CAPTURE: phase <= CAP_A;
                CAP_A:   phase <= CAP_B;
                CAP_B:   phase <= CAP_C;
                CAP_C:   phase <= CAP_D;
                CAP_D:   phase <= EXECUTE;
                EXECUTE: if (is_mem) begin
                             if (!mem_aligned || mem_fault_i || mem_ready_i) begin
                                 mem_cause_q <= (MPU_FAULT_FIRST && mem_fault_i) ? MEM_FAULT
                                              : !mem_aligned ? MIS_MEM
                                              : mem_fault_i  ? MEM_FAULT : 3'd0;
                                 phase       <= MEMORY;
                             end
                         end else if (is_crypto) begin
                             crypto_kicked_q <= 1'b1;
                             phase           <= CRYPTO;
                         end
                default: ;
            endcase
        end
    end
endmodule
