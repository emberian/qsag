// Load raw binary bytes by backdoor, then exercise only the public command port.
`timescale 1ns/1ps
module tb_auto_v2;
  bit clk,rst=1,cmd_valid;
  always #1 clk=~clk;
  wire cmd_ready,rsp_valid;
  logic [7:0] cmd_op;
  logic [4:0] cmd_idx;
  logic [23:0] cmd_addr;
  logic [63:0] cmd_data;
  wire [63:0] rsp_data;
  qsag_ni_asic_top dut(.*);
  int cycles,commands;
  always @(posedge clk) if(!rst) cycles<=cycles+1;
  task automatic cmd(input logic [7:0] op,input logic [4:0] idx,input logic [23:0] addr,input logic [63:0] data);
    if(!cmd_ready) $fatal(1,"not ready");
    cmd_op=op;cmd_idx=idx;cmd_addr=addr;cmd_data=data;cmd_valid=1;
    @(negedge clk);cmd_valid=0;commands++;
    while(!rsp_valid) begin
      @(negedge clk);
      if(cycles>500000000) $fatal(1,"timeout pc=%h",dut.u_auto.pc);
    end
  endtask
  task automatic preload(input string path,input int origin,input int flip,input int bitnum,input int offset_bytes,input int limit_bytes,output int length);
    int fd,c; logic [63:0] word_value;
    fd=$fopen(path,"rb");if(fd==0) $fatal(1,"missing %s",path);
    if($fseek(fd,offset_bytes,0)!=0) $fatal(1,"seek %s",path);
    length=0;word_value=0;
    for(;;) begin
      if(limit_bytes!=0 && length==limit_bytes) break;
      c=$fgetc(fd);
      if(c<0 && (length%8)==0) break;
      if(c>=0) begin
        if(offset_bytes+length==flip) c=c^(1<<bitnum);
        word_value[8*(length%8)+:8]=8'(c);length++;
      end
      if(c<0 || (length%8)==0) begin
        automatic int a=origin+((length-1)/8);
        if(a>=65536) $fatal(1,"fixture exceeds SRAM");
        case(a>>14)
          0:dut.u_sram.g_bank[0].u_bank.mem[a[13:0]]=word_value;
          1:dut.u_sram.g_bank[1].u_bank.mem[a[13:0]]=word_value;
          2:dut.u_sram.g_bank[2].u_bank.mem[a[13:0]]=word_value;
          3:dut.u_sram.g_bank[3].u_bank.mem[a[13:0]]=word_value;
          default:$fatal;
        endcase
        word_value=0;
      end
      if(c<0) break;
    end
    $fclose(fd);
  endtask
  task automatic toggle_bit(input int id);
    automatic int a=id/64;
    case(a>>14)
      0:dut.u_sram.g_bank[0].u_bank.mem[a[13:0]][id%64]^=1;
      1:dut.u_sram.g_bank[1].u_bank.mem[a[13:0]][id%64]^=1;
      2:dut.u_sram.g_bank[2].u_bank.mem[a[13:0]][id%64]^=1;
      3:dut.u_sram.g_bank[3].u_bank.mem[a[13:0]][id%64]^=1;
      default:$fatal;
    endcase
  endtask
  int changed;
`ifdef AUTO_CAMPAIGN
  bit campaign;
  import "DPI-C" function int d1_begin(string path,int workers,int length);
  import "DPI-C" function int d1_probe(int word_address);
  import "DPI-C" function int d1_finish(int good);
  initial forever begin
    @(negedge clk);
    if(campaign && changed<0) begin
      if(dut.a_en && !dut.a_we) changed=d1_probe(32'(dut.a_addr));
      if(changed<0 && dut.b_en && !dut.b_we) changed=d1_probe(32'(dut.b_addr));
      if(changed>=0) toggle_bit(changed);
    end
  end
`endif
  int last_pc;
  always @(posedge clk) if(dut.u_auto.state==1) last_pc<=32'(dut.u_auto.pc);
  initial begin
    string proof,desc; int flip,bitnum,delta,size,dsize,address,start_cycle,elapsed,expected,noncanonical;
    int page_words,loaded,refills,prior_offset;
    int desc_flip, expected_checks;
    logic [63:0] verify_result;
    changed=-1;
    if(!$value$plusargs("desc_flip=%d",desc_flip)) desc_flip=-1;
    if(!$value$plusargs("checks=%d",expected_checks)) expected_checks=107;
    if(!$value$plusargs("page=%d",page_words)) page_words=0;
    refills=0;prior_offset=0;
    if(!$value$plusargs("proof=%s",proof)) proof="vec/proof_v2.bin";
    if(!$value$plusargs("desc=%s",desc)) desc="vec/statement_v2.bin";
    if(!$value$plusargs("flip=%d",flip)) flip=-1;
    if(!$value$plusargs("bit=%d",bitnum)) bitnum=0;
    if(!$value$plusargs("delta=%d",delta)) delta=0;
    if(!$value$plusargs("noncanonical=%d",noncanonical)) noncanonical=-1;
    expected=int'(desc_flip<0 && flip<0 && delta==0 && noncanonical<0);
    begin
      int fd;fd=$fopen(proof,"rb");
      if(fd==0 || $fseek(fd,0,2)!=0) $fatal(1,"cannot size proof");
      size=$ftell(fd);$fclose(fd);
    end
    preload(proof,0,flip,bitnum,0,page_words*8,loaded);
`ifdef AUTO_CAMPAIGN
    begin
      string manifest;int workers;
      if($value$plusargs("campaign=%s",manifest)) begin
        if(!$value$plusargs("workers=%d",workers)) workers=2;
        campaign=d1_begin(manifest,workers,size)>0;
      end
    end
`endif
    if(noncanonical>=0) begin
      for(int i=0;i<8;i++) begin
        automatic int pos=noncanonical+i;
        if(pos<0 || pos>=131072) $fatal(1,"noncanonical test offset");
        dut.u_sram.g_bank[0].u_bank.mem[pos[16:3]][8*pos[2:0]+:8]=8'(64'hffffffff00000001>>(8*i));
      end
    end
    address=page_words!=0 ? page_words : (size+15)/8;
    preload(desc,address,desc_flip,bitnum,0,0,dsize);
    if(desc_flip>=dsize) $fatal(1,"descriptor flip outside payload");
    repeat(4) @(negedge clk);rst=0;
    cmd(8,1,0,0);start_cycle=cycles;
    cmd('h50,0,24'(address),{32'(size+delta),16'(page_words),16'd0});
    while(rsp_data[63:56]==8'h51) begin
      automatic int offset=int'(rsp_data[31:0]);
      if(page_words<2 || offset<=prior_offset || offset>=size || offset%8!=0) $fatal(1,"invalid page request");
      prior_offset=offset;
      preload(proof,0,flip,bitnum,offset,page_words*8,loaded);
      if(loaded==0) $fatal(1,"empty page");
      cmd('h51,0,0,64'(offset));refills++;
    end
    verify_result=rsp_data;
    elapsed=cycles-start_cycle;
    cmd('h0b,0,0,0);
    if(changed>=0) begin flip=changed/8;bitnum=changed%8;expected=0;end
    $display("AUTO verify_result=%0d verify_fail=%0d desc_flip=%0d",verify_result,dut.verify_fail,desc_flip);
    if(verify_result!=64'(expected) || dut.verify_fail==expected[0]) $fatal(1,"unexpected verify response");
    $display("AUTO proof=%s bytes=%0d desc=%0d flip=%0d bit=%0d delta=%0d commands=%0d refills=%0d cycles=%0d status=%h pc=%h",
              proof,size,dsize,flip,bitnum,delta,commands,refills,elapsed,rsp_data,last_pc);
`ifdef AUTO_CAMPAIGN
    if(campaign && d1_finish(int'(rsp_data[32]==expected[0] && (!expected[0] || rsp_data[31:0]==expected_checks)))==0)
      $fatal(1,"mutation campaign failed");
`endif
    if(rsp_data[32]!=expected[0] || (expected!=0 && rsp_data[31:0]!=expected_checks)) $fatal(1,"unexpected status");
    $display("AUTO PASS");$finish;
  end
endmodule
