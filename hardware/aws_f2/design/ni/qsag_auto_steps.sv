// One ordered insertion iteration. The carry is the candidate yet to be
// inserted into the unread suffix. A zero-length suffix appends it.
module qsag_auto_insert_step(input wire [31:0] carry,item,
    input wire at_end, output wire write_item,stop,grow,
    output wire [31:0] stored,next_carry);
  assign grow=at_end;
  assign stop=at_end || item==carry;
  assign write_item=at_end || carry<item;
  assign stored=carry;
  assign next_carry=write_item ? item : carry;
endmodule

// Sorted frontier indices are positive heap labels. Zero denotes end of level.
module qsag_auto_canopy_step(input wire [31:0] node,next_node,
    input wire remaining, output wire [31:0] parent,
    output wire pair_nodes,consume,swap,bad);
  assign parent=node>>1;
  assign pair_nodes=next_node!=0 && next_node==(node^1);
  assign consume=!pair_nodes;
  assign swap=node[0];
  assign bad=node<=1 || (next_node!=0 && next_node<=node) || (consume && !remaining);
endmodule

// Each control word selects an operation in the existing field datapath and
// three SRAM temporaries. Slots 0..7 hold a,b,theta,alpha,beta,x,x^-1,1/2.
module qsag_auto_butterfly_step(input wire [3:0] step, output logic [13:0] control);
  localparam logic [1:0] ADD=0,SUB=1,MUL=2,SCALE=3;
  always_comb case(step)
    0: control={ADD,  4'd8,4'd0,4'd1};   // a+b
    1: control={SCALE,4'd8,4'd8,4'd7};   // f
    2: control={SUB,  4'd9,4'd0,4'd1};   // a-b
    3: control={SCALE,4'd6,4'd6,4'd7};   // x^-1 / 2
    4: control={SCALE,4'd9,4'd9,4'd6};   // g
    5: control={SCALE,4'd5,4'd5,4'd5};   // x^2
    6: control={SCALE,4'd4,4'd4,4'd5};   // beta * x^2
    7: control={ADD,  4'd3,4'd3,4'd4};   // alpha + beta*x^2
    8: control={MUL,  4'd2,4'd2,4'd9};   // theta*g
    9: control={ADD,  4'd8,4'd8,4'd2};   // f+theta*g
    10:control={MUL,  4'd8,4'd3,4'd8};
    11:control={ADD,  4'd0,4'd9,4'd8};
    default: control='0;
  endcase
endmodule
