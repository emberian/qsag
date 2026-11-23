// Fixed-program sequencer. Only the immutable verifier ROM is executable.
// Scalar loads can cross a word boundary. Stores are restricted to the scratch
// interval above the proof and public descriptor. Both SRAM ports are synchronous.
`default_nettype none
module qsag_v2_auto_engine #(parameter int AW=16)(
    input wire clk, rst, start_i, input wire [23:0] desc_word,
    input wire [15:0] proof_word, window_words, input wire [31:0] proof_size,
    input wire page_continue, page_abort, output wire page_needed, page_write_ok,
    output logic [31:0] page_offset,
    input wire [2047:0] rf_lanes, output logic rf_write,
    output logic [4:0] rf_index, output logic [63:0] rf_value,
    output wire done, failed, output logic [31:0] checks,
    output logic ae, be, aw, bw, output logic [15:0] aa, ba,
    output logic [63:0] ad, bd, input wire [63:0] aq, bq,
    output wire [63:0] field_a, field_b, input wire [63:0] field_product, field_sum,
    output wire field_sub,
    input wire [767:0] p2_state, input wire p2_done, output wire p2_write, p2_start,
    output wire fp_start, fp_latch, fp_feedback, output wire [2:0] fp_lane,
    output wire fp_sumcheck, output wire [15:0] fp_coeff, output wire [31:0] fp_degree,
    input wire fp_done,fp_bad,fp_read, input wire [15:0] fp_addr,
    output logic k_we,k_xor,k_start,k_r12, output logic [4:0] k_lane,
    output logic [63:0] k_word, input wire [63:0] k_q, input wire k_busy,
    output wire [3:0] domain, output wire [4:0] domain_lane, input wire [63:0] domain_word
);
    localparam logic [63:0] CAPACITY = 64'd8 << AW;
    localparam logic [63:0] ROM = 64'h200000;
    `include "qsag_auto_rom_size.svh"
    localparam logic [63:0] ROM_BYTES = 64'd8 << ROM_AW;
    typedef enum logic [4:0] {IDLE,EXEC,LOAD,STORE,ROM_LOAD,DOMAIN_SET,PERMUTE,
        KWAIT,FP_READ,FP_LATCH,FP_GO,FP_WAIT,FP_STORE,PASS,FAIL,INDEX_READ,INDEX_WRITE,REFILL,BOOT,FETCH,ROM_REQ,P2_WAIT} state_t;
    state_t state;
    logic [23:0] desc_base;
    logic [18:0] pc;
    logic [31:0] saved;
    logic [4:0] lane;
    logic [63:0] lower;
    wire [63:0] rom_word;
    wire [31:0] fetch = pc[2] ? rom_word[63:32] : rom_word[31:0];
    wire [31:0] ins = state == EXEC ? fetch : saved;
    wire [4:0] rd = ins[11:7];
    wire [2:0] f3 = ins[14:12];
    wire [6:0] f7 = ins[31:25], op = ins[6:0];
    // Decode each index once and share its enable across all 64 bit lanes.
    function automatic [63:0] read_reg(input logic [4:0] index, input logic [2047:0] regs);
        logic [63:0] value;
        value = 0;
        for (int i=1; i<32; i++)
            value |= regs[64*i +: 64] & {64{index == 5'(i)}};
        read_reg = value;
    endfunction
    wire [63:0] x = read_reg(ins[19:15], rf_lanes);
    wire [63:0] y = read_reg(ins[24:20], rf_lanes);
    // The third source is always an SRAM pointer, possibly tagged in bit 0.
    // Saturate unrepresentable addresses before the bounds checks.
    wire [19:0] dest_addr [32];
    for (genvar i=0; i<32; i++) begin : g_dest
        assign dest_addr[i] = {|rf_lanes[64*i+19 +: 45], rf_lanes[64*i +: 19]};
    end
    wire [63:0] dst = {44'd0,dest_addr[rd]};
    wire [63:0] imm_i = {{52{ins[31]}},ins[31:20]};
    wire [63:0] imm_s = {{52{ins[31]}},ins[31:25],ins[11:7]};
    wire [63:0] addr = x + (op == 7'h23 ? imm_s : imm_i);
    wire [3:0] size = 4'd1 << f3[1:0];
    localparam logic [63:0] VPROOF=64'h10000000;
    logic [31:0] total_bytes, resident;
    logic [15:0] page_base, window;
    wire [31:0] offset=addr[31:0]-VPROOF[31:0];
    wire virtual_read=window!=0 && addr>=VPROOF && addr-VPROOF<64'(total_bytes);
    wire in_page=offset>=resident && {1'b0,offset}+33'(size)<={1'b0,resident}+{14'd0,window,3'd0};
    wire [15:0] in_window=16'((offset-resident)>>3);
    wire [16:0] end_word={1'b0,page_base}+{1'b0,window};
    assign page_write_ok=desc_word>=24'(page_base) && desc_word<24'(end_word);
    assign page_needed=state==REFILL;
    wire crossing = {1'b0,addr[2:0]} + size > 8;
    logic [ROM_AW-1:0] literal_addr;
    wire [ROM_AW-1:0] rom_addr = state == ROM_REQ ? literal_addr : pc[ROM_AW+2:3];
    qsag_auto_rom u_rom(.clk(clk),.addr(rom_addr),.word_o(rom_word));
    wire [127:0] pair_in = {bq,aq};
    wire [5:0] shift = {addr[2:0],3'b0};
    wire [63:0] loaded = state==ROM_LOAD ? rom_word >> shift : 64'(pair_in >> shift);
    wire [127:0] mask = ((128'd1 << {size,3'b0})-1'b1) << shift;
    wire [127:0] updated = (pair_in & ~mask) | (({64'b0,y} << shift) & mask);
    wire [63:0] arg = op[5] ? y : imm_i;
    wire word_op = op[3];
    logic [63:0] alu, load_result;
    logic branch_taken;
    always_comb begin
        case(f3)
          0: alu = op[5] && ins[30] ? x-arg : x+arg;
          1: alu = x << (word_op ? {1'b0,arg[4:0]} : arg[5:0]);
          2: alu = 64'($signed(x)<$signed(arg));
          3: alu = 64'(x<arg);
          4: alu = x^arg;
          5: begin
            if (word_op) begin
                if(ins[30]) alu = $signed({{32{x[31]}},x[31:0]}) >>> arg[4:0];
                else alu = {32'b0,x[31:0]} >> arg[4:0];
            end
            else if (ins[30]) alu = $signed(x) >>> arg[5:0];
            else alu = x >> arg[5:0];
          end
          6: alu = x|arg;
          default: alu = x&arg;
        endcase
        case (f3)
          0: branch_taken = x==y;
          1: branch_taken = x!=y;
          4: branch_taken = $signed(x)<$signed(y);
          5: branch_taken = $signed(x)>=$signed(y);
          6: branch_taken = x<y;
          default: branch_taken = x>=y;
        endcase
        case(f3)
          0: load_result = {{56{loaded[7]}},loaded[7:0]};
          1: load_result = {{48{loaded[15]}},loaded[15:0]};
          2: load_result = {{32{loaded[31]}},loaded[31:0]};
          4: load_result = {56'd0,loaded[7:0]};
          5: load_result = {48'd0,loaded[15:0]};
          6: load_result = {32'd0,loaded[31:0]};
          default: load_result = loaded;
        endcase
    end
    wire custom_exec = state == EXEC && op == 7'h0b;
    assign p2_start = custom_exec && f7 == 16;
    assign p2_write = custom_exec && f7 == 15 && x[3:0] < 12;
    assign done = state==PASS || state==FAIL;
    assign failed = state==FAIL;
    wire scalar = state==EXEC && op==7'h0b && (f7==3 || f7==4 || f7==5);
    assign field_a=scalar ? x : 0;
    assign field_b=scalar ? y : 0;
    assign field_sub=f7==4;
    assign domain=x[3:0];
    assign domain_lane=lane;
    assign fp_start=state==FP_GO;
    assign fp_latch=state==FP_LATCH;
    assign fp_lane=lane[2:0];
    assign fp_feedback=state==FP_WAIT;
    assign fp_sumcheck=f7==14;
    assign fp_coeff=dst[18:3];
    assign fp_degree=dst[0] ? 32'd9 : 32'd2;
    logic [31:0] carry;
    logic [8:0] index_pos;
    wire [15:0] index_addr=x[18:3]+16'(index_pos);
    wire append={23'd0,index_pos}==y[63:32];
    wire index_we,index_done,index_grow;
    wire [31:0] stored,next_carry,parent;
    wire pair_nodes,consume,swap,canopy_bad;
    wire [13:0] butterfly;
    qsag_auto_insert_step u_insert(.carry(carry),.item(aq[31:0]),.at_end(append),
      .write_item(index_we),.stop(index_done),.grow(index_grow),.stored(stored),.next_carry(next_carry));
    qsag_auto_canopy_step u_canopy(.node(x[31:0]),.next_node(y[31:0]),.remaining(y[32]),
      .parent(parent),.pair_nodes(pair_nodes),.consume(consume),.swap(swap),.bad(canopy_bad));
    qsag_auto_butterfly_step u_butterfly(.step(x[3:0]),.control(butterfly));
    always_comb begin
        ae=0; aw=0; be=0; bw=0; aa=virtual_read ? page_base+in_window : addr[18:3]; ba=aa+1'b1;
        ad=updated[63:0]; bd=updated[127:64];
        k_we=0; k_xor=0; k_start=0; k_r12=1; k_word=y; k_lane=x[4:0];
        case(state)
          EXEC: begin
            if ((op==7'h03 && virtual_read && in_page) ||
                ((op==7'h03 || op==7'h23) && addr<=CAPACITY-64'(size))) begin
                ae=1; be=crossing;
                if (op==7'h23 && size==8 && shift==0 && addr>=lower) begin aw=1; ad=y; end
            end
            if(op==7'h0b && f7==8) begin k_we=1; k_xor=1; end
          end
          STORE: begin ae=1; aw=1; be=crossing; bw=crossing; end
          DOMAIN_SET: begin k_we=1; k_lane=lane; k_word=domain_word; end
          PERMUTE: begin k_start=1; k_r12=!y[0]; end
          INDEX_READ: begin ae=!append; aa=index_addr; end
          INDEX_WRITE: begin ae=index_we; aw=index_we; aa=index_addr; ad={32'd0,stored}; end
          FP_READ: begin ae=1; be=1; aa=x[18:3]+16'(lane); ba=y[18:3]+16'(lane); end
          FP_WAIT: if(fp_sumcheck) begin ae=fp_read; aa=fp_addr; end
          FP_STORE: begin ae=1; aw=1; aa=(fp_sumcheck ? x[18:3] : dst[18:3])+16'(lane); ad=p2_state[64*lane[2:0] +: 64]; end
          default: ;
        endcase
    end
    // One write port into the already instantiated Poseidon context banks.
    // The permutation and scalar registers share a physical write port.
    always_comb begin
        rf_write=0; rf_index=rd; rf_value=0;
        case(state)
          BOOT: begin
            rf_write=1; rf_index=lane+5'd10;
            case(lane)
              0: rf_value=window==0 ? {45'b0,page_base,3'd0} : VPROOF;
              1: rf_value={32'd0,total_bytes};
              2: rf_value={37'd0,desc_base,3'd0};
              3: rf_value=CAPACITY;
              4: rf_value=window==0 ? 64'(total_bytes) : {45'd0,window,3'd0};
              default: rf_value={45'd0,page_base,3'd0};
            endcase
          end
          EXEC: case(op)
            7'h37: begin rf_write=1; rf_value={{32{ins[31]}},ins[31:12],12'b0}; end
            7'h17: begin rf_write=1; rf_value=ROM+64'(pc)+{{32{ins[31]}},ins[31:12],12'b0}; end
            7'h13,7'h33,7'h1b,7'h3b: begin rf_write=1; rf_value=word_op ? {{32{alu[31]}},alu[31:0]} : alu; end
            7'h6f,7'h67: begin rf_write=1; rf_value=ROM+64'(pc)+4; end
            7'h0b: case(f7)
              3,4: begin rf_write=1; rf_value=field_sum; end
              5: begin rf_write=1; rf_value=field_product; end
              10: begin rf_write=1; rf_value=k_q; end
              12: begin rf_write=1; rf_value={28'd0,parent,canopy_bad,swap,consume,pair_nodes}; end
              15: begin rf_index={1'b0,x[3:0]}; rf_value=y; end
              17: begin rf_write=x[3:0]<12; rf_value=p2_state[64*x[3:0] +: 64]; end
              13: begin rf_write=1; rf_value={50'd0,butterfly}; end
              default: ;
            endcase
            default: ;
          endcase
          LOAD,ROM_LOAD: begin rf_write=1; rf_value=load_result; end
          INDEX_WRITE: begin rf_write=index_done; rf_value={32'd0,y[63:32]}+64'(index_grow); end
          default: ;
        endcase
    end

    always_ff @(posedge clk) begin
        if(rst) begin
          state<=IDLE; checks<=0; page_offset<=0;
        end
        else case(state)
          IDLE: if(start_i) begin
            pc<=0; checks<=0; lower<=CAPACITY;
            page_base<=proof_word; window<=window_words; total_bytes<=proof_size; resident<=0;
            desc_base<=desc_word; lane<=0;
            state<=window_words==1 || (window_words!=0 && proof_size>32'he0000000) ? FAIL : BOOT;
          end
          BOOT: if(lane==5) state<=FETCH; else lane<=lane+1'b1;
          FETCH: state<=EXEC;
          EXEC: begin
            // The upper instruction remains on the registered output after a low-half retire.
            state<=pc[2] ? FETCH : EXEC;
            saved<=fetch; pc<=pc+4;
            case(op)
              7'h37,7'h17,7'h13,7'h33,7'h1b,7'h3b: ;
              7'h6f: begin pc<=pc+{ins[18:12],ins[20],ins[30:21],1'b0}; state<=FETCH; end
              7'h67: begin pc<=19'(x+imm_i) & ~19'd1; state<=FETCH; end
              7'h63: if(branch_taken) begin pc<=pc+{{7{ins[31]}},ins[7],ins[30:25],ins[11:8],1'b0}; state<=FETCH; end
              7'h03,7'h23: begin
                if(op==7'h03 && virtual_read) begin
                    if({1'b0,offset}+33'(size)>{1'b0,total_bytes}) state<=FAIL;
                    else if(in_page) state<=LOAD;
                    else begin page_offset<={offset[31:3],3'b0}; pc<=pc; state<=REFILL; end
                end else if(op==7'h03 && addr>=ROM && addr<ROM+ROM_BYTES && !crossing) begin literal_addr<=addr[ROM_AW+2:3]; state<=ROM_REQ; end
                else if(addr>CAPACITY-64'(size) || (op==7'h23 && addr<lower)) state<=FAIL;
                else if(op==7'h03) state<=LOAD;
                else if(size!=8 || shift!=0) state<=STORE;
              end
              7'h0b: case(f7)
                0: state<=x!=0 && checks!=0 ? PASS : FAIL;
                1: lower<=x;
                2: checks<=checks+1'b1;
                3,4: ;
                5: ;
                6,14: begin
                  lane<=0;
                  if(|{x[2:0],y[2:0],dst[2:1]} || x>CAPACITY-40 || y>CAPACITY-40 ||
                     dst<lower || (f7==6 && (dst[0] || dst>CAPACITY-40)) ||
                     (f7==14 && (x<lower || dst>CAPACITY-(dst[0]?401:120)))) state<=FAIL;
                  else state<=FP_READ;
                end
                7: begin lane<=0; state<=DOMAIN_SET; end
                8: ;
                9: state<=PERMUTE;
                10: ;
                11: begin
                    if(x<lower || x>CAPACITY-8 || x[2:0]!=0 || y[63:32]>=267 ||
                       {32'd0,y[63:32]}>=((CAPACITY-x)>>3)) state<=FAIL;
                    else begin carry<=y[31:0]; index_pos<=0; state<=INDEX_READ; end
                end
                12: ;
                13: ;
                15,17: if(x[3:0]>=12) state<=FAIL;
                16: state<=P2_WAIT;
                default: state<=FAIL;
              endcase
              default: state<=FAIL;
            endcase
          end
          REFILL: if(page_abort) state<=FAIL;
                  else if(page_continue) begin resident<=page_offset; state<=FETCH; end
          INDEX_READ: state<=INDEX_WRITE;
          INDEX_WRITE: if(index_done) begin
            state<=EXEC;
          end else begin carry<=next_carry; index_pos<=index_pos+1'b1; state<=INDEX_READ; end
          ROM_REQ: state<=ROM_LOAD;
          ROM_LOAD: state<=FETCH;
          // Other wait states have already presented the next PC to the ROM.
          P2_WAIT: if(p2_done) state<=EXEC;
          LOAD: state<=EXEC;
          STORE: state<=EXEC;
          DOMAIN_SET: if(lane==24) state<=PERMUTE; else lane<=lane+1'b1;
          PERMUTE: state<=KWAIT;
          KWAIT: if(!k_busy) state<=EXEC;
          FP_READ: state<=FP_LATCH;
          FP_LATCH: begin
            if(lane==4) state<=FP_GO;
            else begin lane<=lane+1'b1; state<=FP_READ; end
          end
          FP_GO: state<=FP_WAIT;
          FP_WAIT: begin
            if(fp_done) begin
                lane<=0;
                if(fp_sumcheck) checks<=checks+1'b1;
                state<=fp_sumcheck && fp_bad ? FAIL : FP_STORE;
            end
          end
          FP_STORE: if(lane==4) state<=EXEC; else lane<=lane+1'b1;
          default: state<=IDLE;
        endcase
    end
endmodule
`default_nettype wire
