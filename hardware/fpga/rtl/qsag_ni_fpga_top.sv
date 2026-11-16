// QSAG-NI FPGA accelerator top: AXI4-Lite command/register interface plus one 512-bit AXI4-Stream
// slave around the five QSAG-NI primitives and Steiner-Canopy / Sumcheck / Batch-MAC engines.
//
// Parameterized across three silicon profiles sharing the identical software-visible ISA:
//   1. VU9P_TURBO   : PROFILE_COMPACT=0, P2_UNROLLED=1, KECCAK_PIPE=1, CHAIN_SLOTW=8, FOLD_TAW=16
//   2. XCUP_RING    : PROFILE_COMPACT=0, P2_UNROLLED=0, KECCAK_PIPE=0, CHAIN_SLOTW=5, FOLD_TAW=16
//   3. ECP5_COMPACT : PROFILE_COMPACT=1, P2_UNROLLED=0, KECCAK_PIPE=0, CHAIN_SLOTW=5, FOLD_TAW=11,
//                     AW=16, BW=16 (fits one Lattice LFE5UM5G-85F: 80 MULT18X18D, lane-sliced Keccak)
//
// Register map (32-bit words, byte addresses):
//   0x000 CMD        W   [7:0] opcode, [15:8] arg0, [31:16] arg1
//   0x004 STATUS     R   [0] busy [1] done [2] ok [3] non-canonical stream limb [4] cmd err [5] active
//   0x008 OP_CYCLES  R   clocks of last operation
//   0x00C/0x010      R   TOTAL_CYCLES low/high
//   0x014 ARG32      RW  32-bit auxiliary argument (chain leaf heap idx / Canopy num_sibs)
//   0x018 CHAIN_DONE R, 0x01C CHAIN_OK R, 0x024 CHAIN_BUSY R (low 32 chain slots)
//   0x020 STREAM     RW  [31:28] destination (0=P2 chain, 1=TS Canopy frontier, 2=TS Canopy sibs,
//                        8=Ext4 fold table), [19:0] write pointer
//   0x028 ID         R   0x51534E49 ("QSNI")
//   0x02C P2_PERMS   R   Poseidon2 permutations completed
//   0x100 + 8*i      RW  operand bank X[i], i < 32
//   0x200 + 8*i      R   result bank  Y[i], i < 12
//
// Opcodes:
//   0x01 P2_PERM            Y[0..11] = poseidon2_perm12(X[0..11])
//   0x02 P2_JIVE            Y[0..3]  = weighted feed-forward node hash of X[0..11]
//   0x03 CHAIN_CFG          tree key = X[0..2], exp_root = X[4..7] (skip if arg0[1]), clr if arg0[0]
//   0x04 CHAIN_START        slot arg0, arg1[5:0] sponge steps, heap ARG32, init state X[0..11]
//   0x05 CHAIN_WAIT         waits for all chain slots; ok = all finished chains matched exp_root
//   0x06 CHAIN_READ         Y[0..11] = state of slot arg0
//   0x10 EXT4_MAC           Y[0..3]  = X[0..3] * X[4..7] + X[8..11]
//   0x11 SC_INIT            claim = X[0..3], clears sticky sumcheck failure
//   0x12 SC_ROUND           arg0==0: deg-3 in X[0..19]; arg0>=1: streamed deg=arg0 on AXI4-Stream
//                           (beat 0 = challenge, beats 1..deg+1 = c[deg]..c[0]); checks g(0)+g(1)==claim
//   0x13 FOLD_ROUND         single BRAM fold round with X[0..3]
//   0x14 FOLD_SETLEN        fold_log2n = arg0[5:0]
//   0x15 FOLD_MULTI         arg0[3:0] = m (1..8) back-to-back fold rounds with X[0..4m-1]
//   0x16 EXT4_BATCH         streams arg1 (1..65535) Ext4 MACs on AXI4-Stream (2 beats/MAC:
//                           {b, a}, {exp_y, c}), hardware-checking every mac_y == exp_y
//   0x20 KEC_LOAD           Keccak state = X[0..24]
//   0x21 KEC_PERMUTE        XOR X[0..16] unless arg0[1]; permute (12r if arg0[0] else 24r); Y=st[0..11]
//   0x22 KEC_STREAM_SPONGE  streams arg1 Keccak rate blocks on AXI4-Stream (3 beats/block: lanes 0..7,
//                           lanes 8..15, {exp_dig[255:0], flags[63:0], lane16[63:0]})
//   0x24 TS_CANOPY_VERIFY   Steiner-deduplicated TurboSHAKE256/cSHAKE256 Canopy MultiProof verify:
//                           arg0[0]=turbo, arg0[6:1]=log_leaves, arg1=num_leaves, ARG32=num_sibs,
//                           X[0..3]=expected_root; Y[0..3]=computed_root, ok=verified
//   0x30 GF_MAC             Y[0..1] = mul(X[0..1], X[2..3]) ^ X[4..5] (arg0[0]=0 poly, 1 tower128);
//                           ok = (Y[0..1] == X[6..7])
//   0x3F CLEAR              clears sticky errors and counters
module qsag_ni_fpga_top #(
    parameter bit PROFILE_COMPACT = 1'b0,
    parameter bit P2_UNROLLED     = 1'b0,
    parameter bit KECCAK_PIPE     = P2_UNROLLED,
    parameter int CHAIN_SLOTW     = P2_UNROLLED ? 8 : 5,
    parameter int FOLD_TAW        = PROFILE_COMPACT ? 11 : 16,
    parameter int KECCAK_RPC      = PROFILE_COMPACT ? 1 : 2,
    parameter int AW              = PROFILE_COMPACT ? 16 : 26,
    parameter int BW              = PROFILE_COMPACT ? 16 : 17
) (
    input  logic         clk,
    input  logic         rst,
    // AXI4-Lite slave
    input  logic [11:0]  s_axil_awaddr,
    input  logic         s_axil_awvalid,
    output logic         s_axil_awready,
    input  logic [31:0]  s_axil_wdata,
    input  logic [3:0]   s_axil_wstrb,
    input  logic         s_axil_wvalid,
    output logic         s_axil_wready,
    output logic [1:0]   s_axil_bresp,
    output logic         s_axil_bvalid,
    input  logic         s_axil_bready,
    input  logic [11:0]  s_axil_araddr,
    input  logic         s_axil_arvalid,
    output logic         s_axil_arready,
    output logic [31:0]  s_axil_rdata,
    output logic [1:0]   s_axil_rresp,
    output logic         s_axil_rvalid,
    input  logic         s_axil_rready,
    // AXI4-Stream slave
    input  logic [511:0] s_axis_tdata,
    input  logic         s_axis_tvalid,
    output logic         s_axis_tready
);
    localparam logic [65:0] NEG_1P66  = 66'h3_0000_0000_FFFF_FFFF;
    localparam int          GF128_LAT = qsag_ni_pkg::GF128_LAT;
    localparam int          EXT_LAT   = qsag_ni_pkg::EXT4_MAC_LAT;
    localparam int          SLOTW     = CHAIN_SLOTW;
    localparam int          SLOTS     = 1 << SLOTW;
    localparam int          STEPW     = 6;
    localparam int          TAGW      = SLOTW + 2;
    localparam int          TS_FAW    = PROFILE_COMPACT ? 8 : 9;
    localparam int          TS_SAW    = 11;

    // Static sponge midstate ROM (0=zero, 1=FS_MID, 2=TS_CANOPY_MID, 3=TS_POW_MID,
    // 4=CS_CANOPY_MID, 5=TS_FS_MID, 6=CS_POW_MID).
    function automatic logic [63:0] sponge_mid_rom(input logic [2:0] sel, input logic [4:0] lane);
        case (sel)
            3'd1: begin // FS_MIDSTATE ("QSAG.AGG.FS_TRANSCRIPT/v1")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'h3977c693fff5d3b5;
                    5'd1:  sponge_mid_rom = 64'h246ec0d2e44a2873;
                    5'd2:  sponge_mid_rom = 64'h365c52c274ca962d;
                    5'd3:  sponge_mid_rom = 64'he4c0940fe6fd66d4;
                    5'd4:  sponge_mid_rom = 64'hb1e4c392785511c9;
                    5'd5:  sponge_mid_rom = 64'h059cb6e43d871f0a;
                    5'd6:  sponge_mid_rom = 64'h90cf0bb4b0f87926;
                    5'd7:  sponge_mid_rom = 64'h748c2b6d5ec3eb4a;
                    5'd8:  sponge_mid_rom = 64'h21704f4eff4689b1;
                    5'd9:  sponge_mid_rom = 64'hada5e0392d80ff18;
                    5'd10: sponge_mid_rom = 64'h9f46820a99b7911c;
                    5'd11: sponge_mid_rom = 64'h82179d62d43b4832;
                    5'd12: sponge_mid_rom = 64'h62985ba50bb8c831;
                    5'd13: sponge_mid_rom = 64'h373719272b20bc28;
                    5'd14: sponge_mid_rom = 64'h68d0d91f23c98a74;
                    5'd15: sponge_mid_rom = 64'ha00b662de840548f;
                    5'd16: sponge_mid_rom = 64'h8c8f04fc14e393a9;
                    5'd17: sponge_mid_rom = 64'h47b4b6b3b7ce847f;
                    5'd18: sponge_mid_rom = 64'hce667e802a4096ba;
                    5'd19: sponge_mid_rom = 64'hc7f30bf9849ae9c6;
                    5'd20: sponge_mid_rom = 64'h47b55bcbfe7c2542;
                    5'd21: sponge_mid_rom = 64'h590c6116b1c143a0;
                    5'd22: sponge_mid_rom = 64'hfd8df4474c3cc6e6;
                    5'd23: sponge_mid_rom = 64'h9dab998b64eacbb6;
                    5'd24: sponge_mid_rom = 64'hd1fe4043d17675a6;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            3'd2: begin // TURBOSHAKE_CANOPY_MIDSTATE ("QSAG.PCS.TURBOCANOPY/v1")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'h460887f1cba4a839;
                    5'd1:  sponge_mid_rom = 64'h980803a3bfc02e65;
                    5'd2:  sponge_mid_rom = 64'h68bddb54ef8d20a8;
                    5'd3:  sponge_mid_rom = 64'h0b3372687f85bcaf;
                    5'd4:  sponge_mid_rom = 64'hcc2727c2077077df;
                    5'd5:  sponge_mid_rom = 64'hec41d86c9b5f8d09;
                    5'd6:  sponge_mid_rom = 64'hfb5f5d561424cae1;
                    5'd7:  sponge_mid_rom = 64'h3268a335444cad6d;
                    5'd8:  sponge_mid_rom = 64'h1946744824d4f99b;
                    5'd9:  sponge_mid_rom = 64'hf0cc17364abb8f7b;
                    5'd10: sponge_mid_rom = 64'h6555bd65801754f9;
                    5'd11: sponge_mid_rom = 64'hfb65ea5772915117;
                    5'd12: sponge_mid_rom = 64'h7abf03d078f82efa;
                    5'd13: sponge_mid_rom = 64'he40b7e6f749e0f48;
                    5'd14: sponge_mid_rom = 64'ha878894cf5a786fb;
                    5'd15: sponge_mid_rom = 64'haf50e05198f19f90;
                    5'd16: sponge_mid_rom = 64'he428425cb9274f77;
                    5'd17: sponge_mid_rom = 64'h7cc9afdb9d39179e;
                    5'd18: sponge_mid_rom = 64'h68eb6cd4b52d2c93;
                    5'd19: sponge_mid_rom = 64'h777f4fb40734c256;
                    5'd20: sponge_mid_rom = 64'hb61fe57e44cde167;
                    5'd21: sponge_mid_rom = 64'h1f19e1e1f1a15293;
                    5'd22: sponge_mid_rom = 64'h6ee7751ca38082bc;
                    5'd23: sponge_mid_rom = 64'h1790fc47c8fcf771;
                    5'd24: sponge_mid_rom = 64'hd6bf84556451e94d;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            3'd3: begin // TURBOSHAKE_POW_MIDSTATE ("QSAG.PCS.TURBOPOW/v1")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'h05c2a834d12f320b;
                    5'd1:  sponge_mid_rom = 64'h6e01f76fb298e055;
                    5'd2:  sponge_mid_rom = 64'hc375c2049cde73b1;
                    5'd3:  sponge_mid_rom = 64'h14679f4eadebc00b;
                    5'd4:  sponge_mid_rom = 64'h42c245e14e1d0612;
                    5'd5:  sponge_mid_rom = 64'haad978e09c60a94d;
                    5'd6:  sponge_mid_rom = 64'h97421bfa48a78a3d;
                    5'd7:  sponge_mid_rom = 64'h77731a35cbaaaec0;
                    5'd8:  sponge_mid_rom = 64'hd80e903986a24502;
                    5'd9:  sponge_mid_rom = 64'h56e5c86b0ad655c9;
                    5'd10: sponge_mid_rom = 64'hd0c677d357b05118;
                    5'd11: sponge_mid_rom = 64'hca8b39da2a172fea;
                    5'd12: sponge_mid_rom = 64'hf6722b33b1d71db7;
                    5'd13: sponge_mid_rom = 64'hcd992e2dafb9cc70;
                    5'd14: sponge_mid_rom = 64'ha71ff26148978892;
                    5'd15: sponge_mid_rom = 64'h0ba73ad03b4e7b42;
                    5'd16: sponge_mid_rom = 64'hf6edd8b825b1f4ad;
                    5'd17: sponge_mid_rom = 64'h5696402b81c97ac2;
                    5'd18: sponge_mid_rom = 64'h8f8cc5418a932adb;
                    5'd19: sponge_mid_rom = 64'hd329e076f57dd146;
                    5'd20: sponge_mid_rom = 64'hd485ee5d60978147;
                    5'd21: sponge_mid_rom = 64'h11831024d5468d79;
                    5'd22: sponge_mid_rom = 64'h881ae14ada384d82;
                    5'd23: sponge_mid_rom = 64'h0c8208237c8abcf0;
                    5'd24: sponge_mid_rom = 64'h21390810db15896a;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            3'd4: begin // CANOPY_MIDSTATE ("QSAG.PCS.CANOPY/v2")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'hec954fc7c2fc5381;
                    5'd1:  sponge_mid_rom = 64'h36020892bcb1e761;
                    5'd2:  sponge_mid_rom = 64'h748dc5bcea037dd5;
                    5'd3:  sponge_mid_rom = 64'hfc481597cf683315;
                    5'd4:  sponge_mid_rom = 64'h2ec2f3f44f0d3969;
                    5'd5:  sponge_mid_rom = 64'h9c0dfc53513c2627;
                    5'd6:  sponge_mid_rom = 64'h5415c0edffcd33b8;
                    5'd7:  sponge_mid_rom = 64'h403107f0fc877484;
                    5'd8:  sponge_mid_rom = 64'h798d84e67c6dafa6;
                    5'd9:  sponge_mid_rom = 64'h6e6ea3127d335e8e;
                    5'd10: sponge_mid_rom = 64'h5606ea8555392f99;
                    5'd11: sponge_mid_rom = 64'hd3bac257bbe1d044;
                    5'd12: sponge_mid_rom = 64'h1e5c61027d60223c;
                    5'd13: sponge_mid_rom = 64'h48c4972c4005a2de;
                    5'd14: sponge_mid_rom = 64'he62560e08ebdd299;
                    5'd15: sponge_mid_rom = 64'ha3c6ce028dff6b56;
                    5'd16: sponge_mid_rom = 64'h14e16d5699388c63;
                    5'd17: sponge_mid_rom = 64'h8d68335c54a43ae4;
                    5'd18: sponge_mid_rom = 64'h74a909e5002c19f7;
                    5'd19: sponge_mid_rom = 64'h48a12fac4eec8f3d;
                    5'd20: sponge_mid_rom = 64'h797c9923ea11dfb5;
                    5'd21: sponge_mid_rom = 64'h2121d5b260157781;
                    5'd22: sponge_mid_rom = 64'h704aa293b550c49a;
                    5'd23: sponge_mid_rom = 64'hddcb710a40908d75;
                    5'd24: sponge_mid_rom = 64'h856c96f5dc9851aa;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            3'd5: begin // TURBOSHAKE_FS_MIDSTATE ("QSAG.AGG.TURBO_FS/v1")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'h91d7c2b5d9c349d5;
                    5'd1:  sponge_mid_rom = 64'h0fe9e1320d052990;
                    5'd2:  sponge_mid_rom = 64'hbb49dcb163df0998;
                    5'd3:  sponge_mid_rom = 64'h41863aed68216b69;
                    5'd4:  sponge_mid_rom = 64'h9b36e33d0b572914;
                    5'd5:  sponge_mid_rom = 64'h47fd0269a80e1a2f;
                    5'd6:  sponge_mid_rom = 64'h0fd8d3b0bb052910;
                    5'd7:  sponge_mid_rom = 64'h777b25e68d3b55e4;
                    5'd8:  sponge_mid_rom = 64'hda8aea200595a598;
                    5'd9:  sponge_mid_rom = 64'h234b7b795b42b2f1;
                    5'd10: sponge_mid_rom = 64'h8931ca9d1d33d881;
                    5'd11: sponge_mid_rom = 64'h265565cd4ead330a;
                    5'd12: sponge_mid_rom = 64'heb457d90d1f36480;
                    5'd13: sponge_mid_rom = 64'hea2ba3d9236057ab;
                    5'd14: sponge_mid_rom = 64'h03572a55d68c5e72;
                    5'd15: sponge_mid_rom = 64'h997c789c6f5417f5;
                    5'd16: sponge_mid_rom = 64'hd8fa575d2aa329b2;
                    5'd17: sponge_mid_rom = 64'ha11c1a07edc22223;
                    5'd18: sponge_mid_rom = 64'hee86f4bac42c763f;
                    5'd19: sponge_mid_rom = 64'hf9d93986d50c63f5;
                    5'd20: sponge_mid_rom = 64'h1d88a5c7c867f955;
                    5'd21: sponge_mid_rom = 64'h394442877b64831d;
                    5'd22: sponge_mid_rom = 64'hcba53b397e6c7084;
                    5'd23: sponge_mid_rom = 64'h8ad61a49d597e2ad;
                    5'd24: sponge_mid_rom = 64'h4918107a763c890a;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            3'd6: begin // POW_MIDSTATE ("QSAG.PCS.POW.V2")
                case (lane)
                    5'd0:  sponge_mid_rom = 64'h912cd4369f324315;
                    5'd1:  sponge_mid_rom = 64'h999c04d88741d72f;
                    5'd2:  sponge_mid_rom = 64'h826e87f172a72886;
                    5'd3:  sponge_mid_rom = 64'h9ab34da963aec230;
                    5'd4:  sponge_mid_rom = 64'he59866a9c4dee082;
                    5'd5:  sponge_mid_rom = 64'h2e0d70596264312e;
                    5'd6:  sponge_mid_rom = 64'h1f62aa1e3894cb9e;
                    5'd7:  sponge_mid_rom = 64'h221e18927402f5dd;
                    5'd8:  sponge_mid_rom = 64'h52411767f8e30a27;
                    5'd9:  sponge_mid_rom = 64'h38ed890d9450b4bd;
                    5'd10: sponge_mid_rom = 64'ha7adc24cbbe0d095;
                    5'd11: sponge_mid_rom = 64'heb93ea9d288eb573;
                    5'd12: sponge_mid_rom = 64'ha8e1b8213cc6bf0a;
                    5'd13: sponge_mid_rom = 64'h4f30b691a18fb10d;
                    5'd14: sponge_mid_rom = 64'h07d90cb270b3a2ce;
                    5'd15: sponge_mid_rom = 64'hbc3100ec6f44ddea;
                    5'd16: sponge_mid_rom = 64'h36d8b62669667d1a;
                    5'd17: sponge_mid_rom = 64'h0cd9a4529023823c;
                    5'd18: sponge_mid_rom = 64'h7d70c6da8ff3dd83;
                    5'd19: sponge_mid_rom = 64'h10aad610c87ac7b3;
                    5'd20: sponge_mid_rom = 64'h288423a030b1eda5;
                    5'd21: sponge_mid_rom = 64'hdc8757b91cac4cc1;
                    5'd22: sponge_mid_rom = 64'h6fdc27bd98b433d0;
                    5'd23: sponge_mid_rom = 64'h33985abee9b9cc90;
                    5'd24: sponge_mid_rom = 64'h5f9bd4e625811719;
                    default: sponge_mid_rom = 64'd0;
                endcase
            end
            default: sponge_mid_rom = 64'd0;
        endcase
    endfunction

    // ------------------------------------------------------------------ registers & AXI4-Lite
    logic [31:0][63:0] x_q;
    logic [11:0][63:0] y_q;
    logic [31:0]       arg32_q, stream_q, op_cycles_q, perms_q, total_lo_q, total_hi_q;
    logic              total_cy_q;
    logic              op_busy, op_done, op_ok, err_noncanon, err_cmd;

    logic        wr_fire, rd_fire, cmd_fire;
    logic [9:0]  wr_word, rd_word;
    logic        aw_full, w_full;
    logic [9:0]  aw_word;
    logic [31:0] wr_data;
    logic [3:0]  wr_strb;
    logic        wr_error;

    assign s_axil_awready = !rst && !aw_full;
    assign s_axil_wready  = !rst && !w_full;
    assign s_axil_arready = !rst && !s_axil_rvalid && !(aw_full && w_full);
    assign wr_fire  = aw_full && w_full && !s_axil_bvalid && !rst;
    assign rd_fire  = s_axil_arvalid && s_axil_arready;
    assign wr_word  = aw_word;
    assign rd_word  = s_axil_araddr[11:2];
    assign wr_error = (|wr_strb) && ((wr_word == 10'h000 && (wr_strb != 4'hf || op_busy))
                                  || (op_busy && wr_word[9:6] == 4'h1));
    assign s_axil_rresp = 2'b00;
    assign cmd_fire = wr_fire && !wr_error && (&wr_strb) && (wr_word == 10'h000);

    always_ff @(posedge clk) begin
        if (rst) begin
            aw_full <= 1'b0;
            w_full  <= 1'b0;
        end else begin
            if (s_axil_awvalid && s_axil_awready) begin
                aw_full <= 1'b1;
                aw_word <= s_axil_awaddr[11:2];
            end
            if (s_axil_wvalid && s_axil_wready) begin
                w_full  <= 1'b1;
                wr_data <= s_axil_wdata;
                wr_strb <= s_axil_wstrb;
            end
            if (wr_fire) begin
                aw_full <= 1'b0;
                w_full  <= 1'b0;
            end
        end
    end

    logic [7:0]  cmd_op_q, cmd_a0_q;
    logic [15:0] cmd_a1_q;

    // ------------------------------------------------------------------ operation FSM states
    typedef enum logic [4:0] {
        O_IDLE, O_P2_OFFER, O_P2_WAIT, O_CH_START, O_CH_WAIT, O_CH_READ,
        O_MAC, O_SC_SUM, O_SC_H, O_SC_STR, O_SC_STR_S2, O_SC_STR_WAIT,
        O_FOLD, O_FOLD_NEXT, O_EBATCH, O_EBATCH_DRAIN,
        O_KEC, O_KCMP_LOAD, O_KCMP_XOR, O_KCMP_PERM, O_KCMP_WAIT, O_KCMP_RD,
        O_KSP_COLLECT, O_KSP_PERM, O_KSP_CMP_INIT, O_KSP_CMP_XOR, O_KSP_CMP_PERM,
        O_KSP_CMP_WAIT, O_KSP_CMP_RD,
        O_TS_CANOPY, O_GF, O_FIN
    } op_e;
    op_e op_st;

    // ------------------------------------------------------------------ Poseidon2 + Chain Engine
    logic             p2_in_valid, p2_in_ready, p2_in_jive, p2_out_valid, p2_busy;
    logic [767:0]     p2_in_state, p2_out_state;
    logic [TAGW-1:0]  p2_in_tag, p2_out_tag;
    /* verilator lint_off UNUSEDSIGNAL */
    logic             p2_out_jive;
    /* verilator lint_on UNUSEDSIGNAL */

    logic             op_job_valid, op_job_jive;
    logic             eng_job_valid, eng_job_jive, eng_job_last;
    logic [767:0]     eng_job_state;
    logic [SLOTW-1:0] eng_job_slot;
    logic             eng_start_valid, eng_start_ready, eng_rd_valid, eng_rd_done, eng_clr;
    logic [767:0]     eng_rd_state;
    logic [191:0]     tree_key_q;
    logic [255:0]     expect_q;
    logic [SLOTS-1:0] chain_busy, chain_done, chain_ok;
    wire  [31:0]      chain_busy32 = 32'(chain_busy);
    wire  [31:0]      chain_done32 = 32'(chain_done);
    wire  [31:0]      chain_ok32   = 32'(chain_ok);

    logic arb_locked, arb_owner, select_eng;
    assign select_eng = arb_locked ? arb_owner : eng_job_valid;
    always_ff @(posedge clk) begin
        if (rst) begin arb_locked <= 1'b0; arb_owner <= 1'b0; end
        else if (p2_in_valid) begin
            arb_locked <= !p2_in_ready;
            if (!p2_in_ready) arb_owner <= select_eng;
        end
    end
    assign p2_in_valid = select_eng ? eng_job_valid : op_job_valid;
    assign p2_in_state = select_eng ? eng_job_state : x_q[11:0];
    assign p2_in_jive  = select_eng ? eng_job_jive  : op_job_jive;
    assign p2_in_tag   = select_eng ? {1'b1, eng_job_last, eng_job_slot} : '0;

    if (PROFILE_COMPACT) begin : g_compact_p2
        qsag_p2_compact #(.TAGW(TAGW), .AW(AW), .BW(BW)) u_p2 (
            .clk(clk), .rst(rst),
            .in_valid(p2_in_valid), .in_ready(p2_in_ready), .in_state(p2_in_state),
            .in_jive(p2_in_jive), .in_tag(p2_in_tag),
            .out_valid(p2_out_valid), .out_state(p2_out_state), .out_jive(p2_out_jive),
            .out_tag(p2_out_tag), .busy(p2_busy));
    end else if (P2_UNROLLED) begin : g_pipe_p2
        qsag_poseidon2_12_pipe #(.TAGW(TAGW), .AW(AW), .BW(BW)) u_p2 (
            .clk(clk), .rst(rst), .in_valid(p2_in_valid && !rst), .in_state(p2_in_state),
            .in_jive(p2_in_jive), .in_tag(p2_in_tag), .out_valid(p2_out_valid),
            .out_state(p2_out_state), .out_jive(p2_out_jive), .out_tag(p2_out_tag));
        localparam int PW = $clog2(qsag_ni_pkg::P2_PIPE_LAT + 2);
        logic [PW-1:0] active;
        always_ff @(posedge clk) begin
            if (rst) active <= '0;
            else case ({p2_in_valid, p2_out_valid})
                2'b10: active <= active + PW'(1);
                2'b01: active <= active - PW'(1);
                default: ;
            endcase
        end
        assign p2_in_ready = !rst;
        assign p2_busy     = (active != '0) || p2_out_valid;
    end else begin : g_ring_p2
        qsag_poseidon2_12_fpga #(.TAGW(TAGW), .AW(AW), .BW(BW)) u_p2 (
            .clk(clk), .rst(rst),
            .in_valid(p2_in_valid), .in_ready(p2_in_ready), .in_state(p2_in_state),
            .in_jive(p2_in_jive), .in_tag(p2_in_tag),
            .out_valid(p2_out_valid), .out_state(p2_out_state), .out_jive(p2_out_jive),
            .out_tag(p2_out_tag), .busy(p2_busy));
    end

    // ------------------------------------------------------------------ AXI4-Stream routing
    wire [3:0] stream_dst = stream_q[31:28];
    wire       op_takes_stream = (op_st == O_SC_STR)
                              || (op_st == O_EBATCH)
                              || (op_st == O_KSP_COLLECT);
    logic      op_stream_ready;
    logic      ts_busy;
    logic      fold_start, fold_busy, fold_done;

    logic passive_ready;
    always_comb begin
        case (stream_dst)
            4'h0: passive_ready = !chain_busy[stream_q[SLOTW+STEPW-1:STEPW]];
            4'h1, 4'h2: passive_ready = !ts_busy;
            4'h8: passive_ready = !fold_busy && !fold_start;
            default: passive_ready = 1'b1;
        endcase
    end

    assign s_axis_tready = !rst && (op_takes_stream ? op_stream_ready : passive_ready);
    wire stream_fire     = s_axis_tvalid && s_axis_tready;
    wire passive_stream  = stream_fire && !op_takes_stream;

    // Zero-carry canonical limb range check: v >= 2^64 - 2^32 + 1 iff (&v[63:32]) && (|v[31:0])!
    logic [7:0] limb_bad;
    for (genvar i = 0; i < 8; i++) begin : g_canon
        wire [63:0] v = s_axis_tdata[64*i +: 64];
        assign limb_bad[i] = (&v[63:32]) && (|v[31:0]);
    end
    wire stream_check_en = passive_stream && (stream_dst == 4'h0 || stream_dst == 4'h8);
    wire stream_bad      = (stream_dst == 4'h8) ? (|limb_bad[3:0]) : (|limb_bad);

    qsag_p2_chain_engine #(.SLOTW(SLOTW), .STEPW(STEPW)) u_chain (
        .clk(clk), .rst(rst), .tree_key(tree_key_q), .exp_root(expect_q), .clr_maps(eng_clr),
        .bw_en(passive_stream && stream_dst == 4'h0),
        .bw_addr(stream_q[SLOTW+STEPW-1:0]),
        .bw_data(s_axis_tdata),
        .start_valid(eng_start_valid), .start_ready(eng_start_ready),
        .start_slot(cmd_a0_q[SLOTW-1:0]), .start_nsponge(cmd_a1_q[5:0]),
        .start_heap(arg32_q), .start_state(x_q[11:0]),
        .rd_valid(eng_rd_valid), .rd_slot(cmd_a0_q[SLOTW-1:0]),
        .rd_done(eng_rd_done), .rd_state(eng_rd_state),
        .job_valid(eng_job_valid), .job_ready(p2_in_ready && select_eng), .job_state(eng_job_state),
        .job_jive(eng_job_jive), .job_last(eng_job_last), .job_slot(eng_job_slot),
        .res_valid(p2_out_valid && p2_out_tag[TAGW-1]), .res_last(p2_out_tag[SLOTW]),
        .res_slot(p2_out_tag[SLOTW-1:0]), .res_state(p2_out_state),
        .busy_map(chain_busy), .done_map(chain_done), .ok_map(chain_ok));

    // ------------------------------------------------------------------ Ext4 MAC / Fold
    logic         mac_valid, mac_done, mac_valid_fsm;
    logic [255:0] fold_res, mac_a_fsm, mac_b_fsm, mac_c_fsm, mac_a, mac_b, mac_c, mac_y;
    logic [5:0]   fold_log2n_q;
    logic [2:0]   fold_idx;
    logic [3:0]   fold_left;

    // Streamed EXT4_BATCH state (inputs registered via mac_valid_fsm so s_axis_tready never drives u_ext4)
    logic         eb_half, eb_wait_cmp, eb_fail_q;
    logic [15:0]  eb_rem, eb_ret_rem;
    logic [255:0] eb_a_q, eb_b_q, eb_exp_cmp_q, eb_exp_cmp_val;
    if (PROFILE_COMPACT) begin : g_eb_cmp
        assign eb_exp_cmp_val = eb_exp_cmp_q;
    end else begin : g_eb_sr
        logic [(EXT_LAT+1)*256-1:0] eb_exp_sr;
        always_ff @(posedge clk)
            eb_exp_sr <= {eb_exp_sr[EXT_LAT*256-1:0], s_axis_tdata[511:256]};
        assign eb_exp_cmp_val = eb_exp_sr[EXT_LAT*256 +: 256];
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_eb = &{1'b0, eb_exp_cmp_q};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    assign mac_valid = mac_valid_fsm;
    assign mac_a     = mac_a_fsm;
    assign mac_b     = mac_b_fsm;
    assign mac_c     = mac_c_fsm;

    if (PROFILE_COMPACT) begin : g_compact_ext4
        qsag_ext4_compact_bfly #(.TAW(FOLD_TAW), .AW(AW), .BW(BW)) u_ext4 (
            .clk(clk), .rst(rst),
            .tw_en(passive_stream && stream_dst == 4'h8), .tw_idx(stream_q[FOLD_TAW-1:0]),
            .tw_data(s_axis_tdata[255:0]),
            .fold_start(fold_start), .fold_log2n(fold_log2n_q), .fold_r(x_q[{fold_idx, 2'b00} +: 4]),
            .fold_busy(fold_busy), .fold_done(fold_done), .fold_res(fold_res),
            .mac_valid(mac_valid), .mac_a(mac_a), .mac_b(mac_b), .mac_c(mac_c),
            .mac_done(mac_done), .mac_y(mac_y));
    end else begin : g_parallel_ext4
        qsag_ext4_mac_bfly #(.TAW(FOLD_TAW), .AW(AW), .BW(BW)) u_ext4 (
            .clk(clk), .rst(rst),
            .tw_en(passive_stream && stream_dst == 4'h8), .tw_idx(stream_q[FOLD_TAW-1:0]),
            .tw_data(s_axis_tdata[255:0]),
            .fold_start(fold_start), .fold_log2n(fold_log2n_q), .fold_r(x_q[{fold_idx, 2'b00} +: 4]),
            .fold_busy(fold_busy), .fold_done(fold_done), .fold_res(fold_res),
            .mac_valid(mac_valid), .mac_a(mac_a), .mac_b(mac_b), .mac_c(mac_c),
            .mac_done(mac_done), .mac_y(mac_y));
    end

    // ------------------------------------------------------------------ Unified 2-Stage Sumcheck Adder
    // Shared between `SC_ROUND` (arg0 == 0, stepping c3..c0 during Horner step 0 with 0 extra cycles)
    // and streamed `SC_ROUND` (arg0 >= 1, arbitrary degree 1..9+).
    // Stage 1: sc_raw_q <= a + b + (c0 ? b : 0) (< 3*2^64, <= 13 levels).
    // Stage 2: fold 2-bit hi = sc_raw_q[65:64] via lo + hi*(2^32 - 1) (< 2*GL_P for all 2^66 inputs,
    //          <= 15 levels) -> sc_sum_q.
    // PROFILE_COMPACT folds the 4 limbs onto ONE rotating 64-bit lane (-3,300 LUT4, <= 15 levels).
    localparam int          SC_LANES = PROFILE_COMPACT ? 1 : 4;
    logic [255:0]           claim_q, sc_sum_q, sc_chal_q, sc_horner_q, sc_vec_q;
    logic                   sc_fail_q, sc_s2_en, sc_is_c0_q, sc_c0_q;
    logic [7:0]             sc_idx, sc_deg;
    logic [3:0]             sc_h_sub;
    logic [2:0]             sc_k;
    logic [1:0]             sc_term;
    logic [SC_LANES*66-1:0] sc_raw_d, sc_raw_q;
    logic [SC_LANES*64-1:0] sc_can_d;
    logic [255:0]           sc_add_b;
    logic                   sc_add_c0;

    always_comb begin
        if (op_st == O_SC_SUM) begin
            sc_add_b  = x_q[15:12];
            sc_add_c0 = 1'b0;
        end else if (op_st == O_SC_H) begin
            case (sc_h_sub[2:1])
                2'd1:    begin sc_add_b = x_q[11:8]; sc_add_c0 = 1'b0; end
                2'd2:    begin sc_add_b = x_q[7:4];  sc_add_c0 = 1'b0; end
                default: begin sc_add_b = x_q[3:0];  sc_add_c0 = 1'b1; end
            endcase
        end else begin
            sc_add_b  = s_axis_tdata[255:0];
            sc_add_c0 = sc_is_c0_q;
        end
    end

    for (genvar i = 0; i < SC_LANES; i++) begin : g_sc_pipe
        wire [63:0] a_l = sc_sum_q[64*i +: 64];
        wire [63:0] b_l = PROFILE_COMPACT ? sc_vec_q[63:0] : sc_add_b[64*i +: 64];
        wire        c0l = PROFILE_COMPACT ? sc_c0_q        : sc_add_c0;
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(22)) u_s1 (
            .x({c0l ? {2'b0, b_l} : 66'd0, {2'b0, b_l}, {2'b0, a_l}}),
            .y(sc_raw_d[66*i +: 66]));

        wire [1:0]  hi = sc_raw_q[66*i + 64 +: 2];
        wire [63:0] lo = sc_raw_q[66*i      +: 64];
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] r0, r1;
        /* verilator lint_on UNUSEDSIGNAL */
        wire [4*66-1:0] tr0 = {66'd1,            ~{64'b0, hi}, {32'b0, hi, 32'b0}, {2'b0, lo}};
        wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{64'b0, hi}, {32'b0, hi, 32'b0}, {2'b0, lo}};
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(22)) u_r0 (.x(tr0), .y(r0));
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(22)) u_r1 (.x(tr1), .y(r1));
        assign sc_can_d[64*i +: 64] = r1[65] ? r0[63:0] : r1[63:0];
    end

    // ------------------------------------------------------------------ Keccak + TS Canopy Engine
    logic          ts_start, ts_done, ts_ok;
    logic [255:0]  ts_out_root;
    logic          ts_kec_start, ts_kec_nr12;
    logic [1599:0] ts_kec_state;
    logic          ts_kcmd_valid, ts_kcmd_nr12;
    logic [1:0]    ts_kcmd_op;
    logic [4:0]    ts_kcmd_idx;
    logic [63:0]   ts_kcmd_wdata;

    logic          kec_start_top, kec_busy, kec_done, kec_load, kec_nr12_top;
    logic          kcmd_ready, kcmd_done, kcmd_rd_valid;
    logic [63:0]   kcmd_rd_data;
    logic [4:0]    kcmp_idx;
    logic [255:0]  kec_dig_out;
    logic [767:0]  kec_y_out;

    // Streamed KEC_STREAM_SPONGE state
    logic [1:0]    ksp_beat;
    logic [15:0]   ksp_rem;
    logic [1023:0] ksp_buf_q;
    logic [63:0]   ksp_lane16_q, ksp_flags_q;
    logic [255:0]  ksp_exp_q;
    logic          ksp_fail_q;

    if (PROFILE_COMPACT) begin : g_kec_compact
        (* rom_style = "block" *) logic [63:0] mid_rom_mem [0:255];
        initial begin
            for (int s = 0; s < 8; s++)
                for (int l = 0; l < 32; l++)
                    mid_rom_mem[s * 32 + l] = (l < 25) ? sponge_mid_rom(3'(s), 5'(l)) : 64'd0;
        end
        logic [63:0] mid_rom_q;
        wire  [2:0]  mid_rom_sel = (op_st == O_KSP_COLLECT)
                                 ? {s_axis_tdata[69], s_axis_tdata[66:65]}
                                 : {ksp_flags_q[5], ksp_flags_q[2:1]};
        wire  [4:0]  mid_rom_idx = (op_st == O_KSP_COLLECT)
                                 ? 5'd0
                                 : (kcmd_ready ? (kcmp_idx + 5'd1) : kcmp_idx);
        always_ff @(posedge clk) begin
            mid_rom_q <= mid_rom_mem[{mid_rom_sel, mid_rom_idx}];
        end

        // Store the 1,024-bit KEC_STREAM_SPONGE rate buffer in DP16KD block RAM (AW=9 -> 0 LUTRAM).
        logic [511:0] ksp_bram_rd;
        wire          ksp_bram_ra = (op_st == O_KSP_CMP_XOR)
                                  ? (kcmp_idx[3] | (kcmd_ready && (kcmp_idx[2:0] == 3'd7)))
                                  : 1'b0;
        qsag_sdp_bram #(.AW(9), .DW(512)) u_ksp_bram (
            .clk(clk),
            .we((op_st == O_KSP_COLLECT) && stream_fire && (ksp_beat < 2'd2)),
            .wa({8'd0, ksp_beat[0]}),
            .wd(s_axis_tdata),
            .ra({8'd0, ksp_bram_ra}),
            .rd(ksp_bram_rd));

        logic        top_kcmd_valid, top_kcmd_nr12;
        logic [1:0]  top_kcmd_op;
        logic [4:0]  top_kcmd_idx;
        logic [63:0] top_kcmd_wdata;

        always_comb begin
            top_kcmd_valid = 1'b0;
            top_kcmd_op    = 2'd0;
            top_kcmd_nr12  = cmd_a0_q[0];
            top_kcmd_idx   = kcmp_idx;
            top_kcmd_wdata = x_q[kcmp_idx];
            case (op_st)
                O_KCMP_LOAD: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd0;
                end
                O_KCMP_XOR: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd1;
                end
                O_KCMP_PERM: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd2;
                end
                O_KCMP_RD: if (kcmp_idx < 5'd12) begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd3;
                end
                O_KSP_CMP_INIT: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd0;
                    top_kcmd_wdata = mid_rom_q;
                end
                O_KSP_CMP_XOR: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd1;
                    top_kcmd_wdata = (kcmp_idx < 5'd16) ? ksp_bram_rd[64*kcmp_idx[2:0] +: 64] : ksp_lane16_q;
                end
                O_KSP_CMP_PERM: begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd2;
                    top_kcmd_nr12  = ksp_flags_q[3];
                end
                O_KSP_CMP_RD: if (kcmp_idx < 5'd4) begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd3;
                end
                default: ;
            endcase
        end

        wire use_ts = (op_st == O_TS_CANOPY);
        qsag_keccak_compact u_keccak (
            .clk(clk), .rst(rst),
            .cmd_valid(use_ts ? ts_kcmd_valid : top_kcmd_valid),
            .cmd_ready(kcmd_ready),
            .cmd_op   (use_ts ? ts_kcmd_op    : top_kcmd_op),
            .cmd_nr12 (use_ts ? ts_kcmd_nr12  : top_kcmd_nr12),
            .cmd_idx  (use_ts ? ts_kcmd_idx   : top_kcmd_idx),
            .cmd_wdata(use_ts ? ts_kcmd_wdata : top_kcmd_wdata),
            .busy(kec_busy), .done(kcmd_done),
            .rd_valid(kcmd_rd_valid), .rd_data(kcmd_rd_data));
        assign kec_done    = 1'b0;
        assign kec_dig_out = '0;
        assign kec_y_out   = '0;
        logic unused_par_k;
        assign unused_par_k = &{1'b0, kec_start_top, kec_load, kec_nr12_top, ts_kec_start, ts_kec_nr12, ts_kec_state};
    end else begin : g_kec_parallel
        logic [1599:0] kec_hold_q, kec_in, kec_state, ksp_base;
        always_comb begin
            for (int l = 0; l < 25; l++)
                ksp_base[64*l +: 64] = ksp_flags_q[0]
                    ? sponge_mid_rom({ksp_flags_q[5], ksp_flags_q[2:1]}, 5'(l))
                    : kec_hold_q[64*l +: 64];
            if (op_st == O_TS_CANOPY) begin
                kec_in = ts_kec_state;
            end else if (op_st == O_KSP_PERM) begin
                kec_in = ksp_base;
                kec_in[1087:0] = ksp_base[1087:0] ^ {ksp_lane16_q, ksp_buf_q};
            end else begin
                kec_in = kec_hold_q;
                if (!cmd_a0_q[1]) kec_in[1087:0] = kec_hold_q[1087:0] ^ x_q[16:0];
            end
        end
        wire par_start = (op_st == O_TS_CANOPY) ? ts_kec_start : kec_start_top;
        wire par_nr12  = (op_st == O_TS_CANOPY) ? ts_kec_nr12  : kec_nr12_top;
        qsag_keccak_turboshake #(.RPC(KECCAK_RPC)) u_keccak (
            .clk(clk), .rst(rst), .start(par_start), .nr12(par_nr12), .state_i(kec_in),
            .busy(kec_busy), .done(kec_done), .state_o(kec_state));
        always_ff @(posedge clk) begin
            if (kec_load) kec_hold_q <= x_q[24:0];
            else if (kec_done && op_st != O_TS_CANOPY) kec_hold_q <= kec_state;
        end
        assign kec_dig_out   = kec_state[255:0];
        assign kec_y_out     = kec_state[767:0];
        assign kcmd_ready    = 1'b0;
        assign kcmd_done     = 1'b0;
        assign kcmd_rd_valid = 1'b0;
        assign kcmd_rd_data  = '0;
        logic unused_cmp_k;
        assign unused_cmp_k = &{1'b0, ts_kcmd_valid, ts_kcmd_nr12, ts_kcmd_op, ts_kcmd_idx, ts_kcmd_wdata};
    end

    qsag_ts_canopy_engine #(
        .PIPE_12(KECCAK_PIPE && !PROFILE_COMPACT),
        .COMPACT_KEC(PROFILE_COMPACT),
        .FRONT_AW(TS_FAW),
        .SIB_AW(TS_SAW)
    ) u_ts_canopy (
        .clk(clk), .rst(rst),
        .tw_front_en (passive_stream && stream_dst == 4'h1),
        .tw_front_idx(stream_q[TS_FAW-1:0]),
        .tw_front_u  (s_axis_tdata[287:256]),
        .tw_front_dig(s_axis_tdata[255:0]),
        .tw_sib_en   (passive_stream && stream_dst == 4'h2),
        .tw_sib_idx  (stream_q[TS_SAW-1:0]),
        .tw_sib_dig  (s_axis_tdata[255:0]),
        .start        (ts_start),
        .in_turbo     (cmd_a0_q[0]),
        .in_log_leaves(cmd_a0_q[6:1]),
        .in_num_leaves(cmd_a1_q[TS_FAW:0]),
        .in_num_sibs  (arg32_q[TS_SAW:0]),
        .in_exp_root  (x_q[3:0]),
        .busy(ts_busy), .done(ts_done), .ok(ts_ok), .out_root(ts_out_root),
        .kec_start(ts_kec_start), .kec_nr12(ts_kec_nr12), .kec_state_o(ts_kec_state),
        .kec_done(kec_done), .kec_digest_i(kec_dig_out),
        .kcmd_valid(ts_kcmd_valid), .kcmd_ready(kcmd_ready), .kcmd_op(ts_kcmd_op),
        .kcmd_nr12(ts_kcmd_nr12), .kcmd_idx(ts_kcmd_idx), .kcmd_wdata(ts_kcmd_wdata),
        .kcmd_done(kcmd_done), .kcmd_rd_valid(kcmd_rd_valid), .kcmd_rd_data(kcmd_rd_data));

    // ------------------------------------------------------------------ GF(2^128) + Wiedemann Tower
    logic         gf_start, gf_done;
    logic [127:0] gf_r;
    logic [2:0]   gf_cnt;
    if (PROFILE_COMPACT) begin : g_gf_cmp
        qsag_gf128_compact u_gf_cmp (
            .clk(clk), .rst(rst), .start(gf_start), .tower(cmd_a0_q[0]),
            .a(x_q[1:0]), .b(x_q[3:2]), .done(gf_done), .r(gf_r));
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_gf_cnt = &{1'b0, gf_cnt};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_gf_par
        logic [127:0] gf_pa, gf_pb, gf_in_a, gf_in_b, gf_raw_r, gf_tow_r;
        qsag_gf128_tower_map #(.INVERSE(0)) u_tow_a (.x(x_q[1:0]), .y(gf_pa));
        qsag_gf128_tower_map #(.INVERSE(0)) u_tow_b (.x(x_q[3:2]), .y(gf_pb));
        assign gf_in_a = cmd_a0_q[0] ? gf_pa : x_q[1:0];
        assign gf_in_b = cmd_a0_q[0] ? gf_pb : x_q[3:2];
        qsag_gf128_clmul u_gf (.clk(clk), .a(gf_in_a), .b(gf_in_b), .r(gf_raw_r));
        qsag_gf128_tower_map #(.INVERSE(1)) u_tow_r (.x(gf_raw_r), .y(gf_tow_r));
        assign gf_r    = cmd_a0_q[0] ? gf_tow_r : gf_raw_r;
        assign gf_done = (gf_cnt == 3'(GF128_LAT));
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_gf_st = gf_start;
        /* verilator lint_on UNUSEDSIGNAL */
    end

    // ------------------------------------------------------------------ Stream backpressure & FSM
    always_comb begin
        op_stream_ready = 1'b0;
        case (op_st)
            O_SC_STR:      op_stream_ready = 1'b1;
            O_EBATCH:      op_stream_ready = !eb_wait_cmp;
            O_KSP_COLLECT: op_stream_ready = 1'b1;
            default:       op_stream_ready = 1'b0;
        endcase
    end

    logic [1:0]   sc_step;
    logic [3:0]   rd_cnt;
    logic [191:0] ksp_dig_q;
    wire [255:0]  ksp_full_dig = {kcmd_rd_data, ksp_dig_q};

    assign op_job_valid    = (op_st == O_P2_OFFER);
    assign op_job_jive     = (cmd_op_q == 8'h02);
    assign eng_start_valid = (op_st == O_CH_START);
    assign eng_rd_valid    = (op_st == O_CH_READ) && !eng_rd_done;

    wire engines_busy = op_busy || p2_busy || (|chain_busy) || fold_busy || kec_busy || ts_busy;

    // Shared 64:1 read mux on `x_q` for both AXI4-Lite reads and partial-strobe writes.
    wire [5:0]  x_rw_idx = wr_fire ? wr_word[5:0] : rd_word[5:0];
    wire [31:0] x_rw_val = x_rw_idx[0] ? x_q[x_rw_idx[5:1]][63:32] : x_q[x_rw_idx[5:1]][31:0];
    logic [31:0] x_new32;
    always_comb begin
        for (int b = 0; b < 4; b++)
            x_new32[8*b +: 8] = wr_strb[b] ? wr_data[8*b +: 8] : x_rw_val[8*b +: 8];
    end
    always_ff @(posedge clk) begin
        if (wr_fire && !wr_error && (|wr_strb) && wr_word[9:6] == 4'h1) begin
            if (wr_word[0]) x_q[wr_word[5:1]][63:32] <= x_new32;
            else            x_q[wr_word[5:1]][31:0]  <= x_new32;
        end
    end

    always_ff @(posedge clk) begin
        fold_start    <= 1'b0;
        mac_valid_fsm <= 1'b0;
        kec_start_top <= 1'b0;
        kec_load      <= 1'b0;
        ts_start      <= 1'b0;
        gf_start      <= 1'b0;
        eng_clr       <= 1'b0;
        sc_s2_en      <= 1'b0;
        if (!PROFILE_COMPACT && sc_s2_en) sc_sum_q <= 256'(sc_can_d);

        if (rst) begin
            op_st         <= O_IDLE;
            op_busy       <= 1'b0;
            op_done       <= 1'b0;
            op_ok         <= 1'b0;
            err_noncanon  <= 1'b0;
            err_cmd       <= 1'b0;
            op_cycles_q   <= '0;
            total_lo_q    <= '0;
            total_hi_q    <= '0;
            total_cy_q    <= 1'b0;
            perms_q       <= '0;
            sc_fail_q     <= 1'b0;
            sc_s2_en      <= 1'b0;
            eb_fail_q     <= 1'b0;
            eb_wait_cmp   <= 1'b0;
            ksp_fail_q    <= 1'b0;
            fold_log2n_q  <= 6'd1;
            stream_q      <= '0;
            arg32_q       <= '0;
            s_axil_bvalid <= 1'b0;
            s_axil_bresp  <= 2'b00;
            s_axil_rvalid <= 1'b0;
        end else begin
            // ---- AXI4-Lite
            if (s_axil_bvalid && s_axil_bready) s_axil_bvalid <= 1'b0;
            if (s_axil_rvalid && s_axil_rready) s_axil_rvalid <= 1'b0;
            if (wr_fire) begin
                s_axil_bvalid <= 1'b1;
                s_axil_bresp  <= wr_error ? 2'b10 : 2'b00;
                if (wr_error) err_cmd <= 1'b1;
                if (!wr_error) begin
                    for (int byte_idx = 0; byte_idx < 4; byte_idx++) begin
                        if (wr_strb[byte_idx]) begin
                            if (wr_word == 10'h005) arg32_q[8*byte_idx +: 8] <= wr_data[8*byte_idx +: 8];
                            if (wr_word == 10'h008) stream_q[8*byte_idx +: 8] <= wr_data[8*byte_idx +: 8];
                        end
                    end
                end
            end
            if (rd_fire) begin
                s_axil_rvalid <= 1'b1;
                s_axil_rdata  <= 32'd0;
                case (rd_word)
                    10'h001: s_axil_rdata <= {26'd0, engines_busy, err_cmd, err_noncanon,
                                              op_ok, op_done, op_busy};
                    10'h002: s_axil_rdata <= op_cycles_q;
                    10'h003: s_axil_rdata <= total_lo_q;
                    10'h004: s_axil_rdata <= total_hi_q + {31'd0, total_cy_q};
                    10'h005: s_axil_rdata <= arg32_q;
                    10'h006: s_axil_rdata <= chain_done32;
                    10'h007: s_axil_rdata <= chain_ok32;
                    10'h008: s_axil_rdata <= stream_q;
                    10'h009: s_axil_rdata <= chain_busy32;
                    10'h00A: s_axil_rdata <= 32'h5153_4E49;
                    10'h00B: s_axil_rdata <= perms_q;
                    default: begin
                        if (rd_word[9:6] == 4'h1)
                            s_axil_rdata <= x_rw_val;
                        else if (rd_word[9:6] == 4'h2 && rd_word[5:1] < 5'd12)
                            s_axil_rdata <= rd_word[0] ? y_q[rd_word[4:1]][63:32]
                                                       : y_q[rd_word[4:1]][31:0];
                    end
                endcase
            end

            // ---- Passive stream pointer update
            if (passive_stream) begin
                stream_q[19:0] <= stream_q[19:0] + 20'd1;
                if (stream_check_en && stream_bad) err_noncanon <= 1'b1;
            end

            // ---- Counters (64-bit total counter pipelined into two 32-bit halves)
            total_cy_q <= engines_busy && (total_lo_q == 32'hFFFF_FFFF);
            if (total_cy_q)   total_hi_q   <= total_hi_q + 32'd1;
            if (engines_busy) total_lo_q   <= total_lo_q + 32'd1;
            if (op_busy)      op_cycles_q  <= op_cycles_q + 32'd1;
            if (p2_out_valid) perms_q      <= perms_q + 32'd1;
            if (fold_done)    fold_log2n_q <= fold_log2n_q - 6'd1;

            // ---- Background retirement for EXT4_BATCH
            if ((op_st == O_EBATCH || op_st == O_EBATCH_DRAIN) && mac_done) begin
                y_q[3:0]   <= mac_y;
                eb_ret_rem <= eb_ret_rem - 16'd1;
                if (PROFILE_COMPACT) eb_wait_cmp <= 1'b0;
                if (mac_y != eb_exp_cmp_val) eb_fail_q <= 1'b1;
            end

            // ---- Operations
            case (op_st)
                O_IDLE: begin
                    if (cmd_fire) begin
                        cmd_op_q    <= wr_data[7:0];
                        cmd_a0_q    <= wr_data[15:8];
                        cmd_a1_q    <= wr_data[31:16];
                        op_busy     <= 1'b1;
                        op_done     <= 1'b0;
                        op_ok       <= 1'b1;
                        op_cycles_q <= '0;
                        case (wr_data[7:0])
                            8'h01, 8'h02: op_st <= O_P2_OFFER;
                            8'h03: begin
                                if (|chain_busy) begin
                                    err_cmd <= 1'b1; op_ok <= 1'b0;
                                end else if (!wr_data[9]) begin
                                    tree_key_q <= x_q[2:0];
                                    expect_q   <= x_q[7:4];
                                end
                                eng_clr <= wr_data[8] && !(|chain_busy);
                                op_st   <= O_FIN;
                            end
                            8'h04: begin
                                if (chain_busy[wr_data[8 +: SLOTW]] ||
                                    (arg32_q <= 32'd1 && wr_data[21:16] == 6'd0)) begin
                                    err_cmd <= 1'b1; op_ok <= 1'b0; op_st <= O_FIN;
                                end else op_st <= O_CH_START;
                            end
                            8'h05: op_st <= O_CH_WAIT;
                            8'h06: op_st <= O_CH_READ;
                            8'h10: begin
                                mac_valid_fsm <= 1'b1;
                                mac_a_fsm     <= x_q[3:0];
                                mac_b_fsm     <= x_q[7:4];
                                mac_c_fsm     <= x_q[11:8];
                                op_st         <= O_MAC;
                            end
                            8'h11: begin
                                claim_q   <= x_q[3:0];
                                sc_fail_q <= 1'b0;
                                op_st     <= O_FIN;
                            end
                            8'h12: begin
                                sc_sum_q <= '0;
                                if (wr_data[15:8] == 8'd0) begin
                                    op_st <= O_SC_SUM;
                                end else begin
                                    sc_deg     <= wr_data[15:8];
                                    sc_idx     <= 8'd0;
                                    sc_is_c0_q <= 1'b0;
                                    op_st      <= O_SC_STR;
                                end
                            end
                            8'h13: begin
                                fold_start <= 1'b1;
                                fold_idx   <= 3'd0;
                                fold_left  <= 4'd1;
                                op_st      <= O_FOLD;
                            end
                            8'h14: begin
                                fold_log2n_q <= wr_data[13:8];
                                op_st        <= O_FIN;
                            end
                            8'h15: begin
                                if (wr_data[21:16] != 6'd0) fold_log2n_q <= wr_data[21:16];
                                fold_idx  <= 3'd0;
                                fold_left <= wr_data[11:8];
                                op_st     <= O_FOLD_NEXT;
                            end
                            8'h16: begin
                                if (wr_data[31:16] == 16'd0) begin
                                    op_st <= O_FIN;
                                end else begin
                                    eb_half     <= 1'b0;
                                    eb_wait_cmp <= 1'b0;
                                    eb_fail_q   <= 1'b0;
                                    eb_rem      <= wr_data[31:16];
                                    eb_ret_rem  <= wr_data[31:16];
                                    op_st       <= O_EBATCH;
                                end
                            end
                            8'h20: begin
                                if (PROFILE_COMPACT) begin
                                    kcmp_idx <= 5'd0;
                                    op_st    <= O_KCMP_LOAD;
                                end else begin
                                    kec_load <= 1'b1;
                                    op_st    <= O_FIN;
                                end
                            end
                            8'h21: begin
                                if (PROFILE_COMPACT) begin
                                    kcmp_idx <= 5'd0;
                                    op_st    <= wr_data[9] ? O_KCMP_PERM : O_KCMP_XOR;
                                end else begin
                                    kec_nr12_top  <= wr_data[8];
                                    kec_start_top <= 1'b1;
                                    op_st         <= O_KEC;
                                end
                            end
                            8'h22: begin
                                if (wr_data[31:16] == 16'd0) begin
                                    op_st <= O_FIN;
                                end else begin
                                    ksp_beat   <= 2'd0;
                                    ksp_rem    <= wr_data[31:16];
                                    ksp_fail_q <= 1'b0;
                                    op_st      <= O_KSP_COLLECT;
                                end
                            end
                            8'h24: begin
                                ts_start <= 1'b1;
                                op_st    <= O_TS_CANOPY;
                            end
                            8'h30: begin
                                gf_start <= 1'b1;
                                gf_cnt   <= 3'd0;
                                op_st    <= O_GF;
                            end
                            8'h3F: begin
                                err_noncanon <= 1'b0;
                                err_cmd      <= 1'b0;
                                total_lo_q   <= '0;
                                total_hi_q   <= '0;
                                total_cy_q   <= 1'b0;
                                perms_q      <= '0;
                                op_st        <= O_FIN;
                            end
                            default: begin
                                op_ok <= 1'b0;
                                op_st <= O_FIN;
                            end
                        endcase
                    end
                end
                O_P2_OFFER: if (p2_in_ready && !select_eng) op_st <= O_P2_WAIT;
                O_P2_WAIT: begin
                    if (p2_out_valid && !p2_out_tag[TAGW-1]) begin
                        y_q   <= p2_out_state;
                        op_st <= O_FIN;
                    end
                end
                O_CH_START: if (eng_start_ready) op_st <= O_FIN;
                O_CH_WAIT: begin
                    if (chain_busy == '0) begin
                        op_ok <= ((chain_done & ~chain_ok) == '0);
                        op_st <= O_FIN;
                    end
                end
                O_CH_READ: begin
                    if (eng_rd_done) begin
                        y_q   <= eng_rd_state;
                        op_st <= O_FIN;
                    end
                end
                O_MAC: begin
                    if (mac_done) begin
                        y_q[3:0] <= mac_y;
                        op_st    <= O_FIN;
                    end
                end
                O_SC_SUM: begin
                    if (PROFILE_COMPACT) begin
                        sc_vec_q <= x_q[15:12];
                        sc_c0_q  <= 1'b0;
                        sc_term  <= 2'd0;
                        sc_k     <= 3'd0;
                    end else begin
                        sc_raw_q <= sc_raw_d;
                        sc_s2_en <= 1'b1;
                    end
                    mac_valid_fsm <= 1'b1;
                    mac_a_fsm     <= x_q[15:12];
                    mac_b_fsm     <= x_q[19:16];
                    mac_c_fsm     <= x_q[11:8];
                    sc_step       <= 2'd0;
                    sc_h_sub      <= 4'd1;
                    op_st         <= O_SC_H;
                end
                O_SC_H: begin
                    if (PROFILE_COMPACT) begin
                        if (sc_k <= 3'd4) begin
                            sc_raw_q <= sc_raw_d;
                            sc_vec_q <= {64'd0, sc_vec_q[255:64]};
                            sc_sum_q <= (sc_k == 3'd0) ? {sc_sum_q[63:0], sc_sum_q[255:64]}
                                                       : {sc_can_d[63:0], sc_sum_q[255:64]};
                            if (sc_k == 3'd4) begin
                                case (sc_term)
                                    2'd0: begin sc_vec_q <= x_q[11:8]; sc_c0_q <= 1'b0; sc_term <= 2'd1; sc_k <= 3'd0; end
                                    2'd1: begin sc_vec_q <= x_q[7:4];  sc_c0_q <= 1'b0; sc_term <= 2'd2; sc_k <= 3'd0; end
                                    2'd2: begin sc_vec_q <= x_q[3:0];  sc_c0_q <= 1'b1; sc_term <= 2'd3; sc_k <= 3'd0; end
                                    default: sc_k <= 3'd5;
                                endcase
                            end else begin
                                sc_k <= sc_k + 3'd1;
                            end
                        end else if (sc_k == 3'd5) begin
                            sc_k <= 3'd6;
                            if (sc_sum_q != claim_q) sc_fail_q <= 1'b1;
                        end
                    end else if (sc_h_sub < 4'd8) begin
                        sc_h_sub <= sc_h_sub + 4'd1;
                        if (!sc_h_sub[0]) begin
                            sc_raw_q <= sc_raw_d;
                            sc_s2_en <= 1'b1;
                        end
                    end else if (sc_h_sub == 4'd8) begin
                        sc_h_sub <= 4'd9;
                        if (sc_sum_q != claim_q) sc_fail_q <= 1'b1;
                    end
                    if (mac_done) begin
                        if (sc_step == 2'd2) begin
                            claim_q  <= mac_y;
                            y_q[3:0] <= mac_y;
                            op_ok    <= !sc_fail_q;
                            op_st    <= O_FIN;
                        end else begin
                            mac_valid_fsm <= 1'b1;
                            mac_a_fsm     <= mac_y;
                            mac_b_fsm     <= x_q[19:16];
                            mac_c_fsm     <= (sc_step == 2'd0) ? x_q[7:4] : x_q[3:0];
                            sc_step       <= sc_step + 2'd1;
                        end
                    end
                end
                O_SC_STR: begin
                    if (stream_fire) begin
                        if (sc_idx == 8'd0) begin
                            sc_chal_q  <= s_axis_tdata[255:0];
                            sc_idx     <= 8'd1;
                            sc_is_c0_q <= 1'b0;
                        end else if (sc_idx == 8'd1) begin
                            sc_horner_q <= s_axis_tdata[255:0];
                            if (PROFILE_COMPACT) begin
                                sc_vec_q <= s_axis_tdata[255:0];
                                sc_c0_q  <= 1'b0;
                                sc_k     <= 3'd0;
                            end else begin
                                sc_raw_q <= sc_raw_d;
                                sc_s2_en <= 1'b1;
                            end
                            sc_idx     <= 8'd2;
                            sc_is_c0_q <= (sc_deg == 8'd1);
                            op_st      <= O_SC_STR_S2;
                        end else begin
                            if (PROFILE_COMPACT) begin
                                sc_vec_q <= s_axis_tdata[255:0];
                                sc_c0_q  <= sc_is_c0_q;
                                sc_k     <= 3'd0;
                            end else begin
                                sc_raw_q <= sc_raw_d;
                                sc_s2_en <= 1'b1;
                            end
                            mac_valid_fsm <= 1'b1;
                            mac_a_fsm     <= sc_horner_q;
                            mac_b_fsm     <= sc_chal_q;
                            mac_c_fsm     <= s_axis_tdata[255:0];
                            op_st         <= O_SC_STR_WAIT;
                        end
                    end
                end
                O_SC_STR_S2: begin
                    if (PROFILE_COMPACT) begin
                        sc_raw_q <= sc_raw_d;
                        sc_vec_q <= {64'd0, sc_vec_q[255:64]};
                        sc_sum_q <= (sc_k == 3'd0) ? {sc_sum_q[63:0], sc_sum_q[255:64]}
                                                   : {sc_can_d[63:0], sc_sum_q[255:64]};
                        if (sc_k == 3'd4) op_st <= O_SC_STR;
                        else              sc_k  <= sc_k + 3'd1;
                    end else begin
                        op_st <= O_SC_STR;
                    end
                end
                O_SC_STR_WAIT: begin
                    if (PROFILE_COMPACT && sc_k <= 3'd4) begin
                        sc_raw_q <= sc_raw_d;
                        sc_vec_q <= {64'd0, sc_vec_q[255:64]};
                        sc_sum_q <= (sc_k == 3'd0) ? {sc_sum_q[63:0], sc_sum_q[255:64]}
                                                   : {sc_can_d[63:0], sc_sum_q[255:64]};
                        sc_k <= sc_k + 3'd1;
                    end
                    if (mac_done) begin
                        sc_horner_q <= mac_y;
                        if (sc_is_c0_q) begin
                            if (sc_sum_q != claim_q) sc_fail_q <= 1'b1;
                            claim_q  <= mac_y;
                            y_q[3:0] <= mac_y;
                            op_ok    <= !sc_fail_q && (sc_sum_q == claim_q);
                            op_st    <= O_FIN;
                        end else begin
                            sc_idx     <= sc_idx + 8'd1;
                            sc_is_c0_q <= (sc_idx == sc_deg);
                            op_st      <= O_SC_STR;
                        end
                    end
                end
                O_FOLD: begin
                    if (fold_done) begin
                        y_q[3:0]  <= fold_res;
                        fold_left <= fold_left - 4'd1;
                        fold_idx  <= fold_idx + 3'd1;
                        op_st     <= (fold_left == 4'd1) ? O_FIN : O_FOLD_NEXT;
                    end
                end
                O_FOLD_NEXT: begin
                    if (!fold_busy && !fold_start) begin
                        fold_start <= 1'b1;
                        op_st      <= O_FOLD;
                    end
                end
                O_EBATCH: begin
                    if (stream_fire) begin
                        if (!eb_half) begin
                            if (PROFILE_COMPACT) begin
                                mac_a_fsm <= s_axis_tdata[255:0];
                                mac_b_fsm <= s_axis_tdata[511:256];
                            end else begin
                                eb_a_q <= s_axis_tdata[255:0];
                                eb_b_q <= s_axis_tdata[511:256];
                            end
                            eb_half <= 1'b1;
                        end else begin
                            eb_half       <= 1'b0;
                            eb_exp_cmp_q  <= s_axis_tdata[511:256];
                            mac_valid_fsm <= 1'b1;
                            if (!PROFILE_COMPACT) begin
                                mac_a_fsm <= eb_a_q;
                                mac_b_fsm <= eb_b_q;
                            end
                            mac_c_fsm     <= s_axis_tdata[255:0];
                            if (PROFILE_COMPACT) eb_wait_cmp <= 1'b1;
                            if (eb_rem == 16'd1) begin
                                eb_rem <= 16'd0;
                                op_st  <= O_EBATCH_DRAIN;
                            end else begin
                                eb_rem <= eb_rem - 16'd1;
                            end
                        end
                    end
                end
                O_EBATCH_DRAIN: begin
                    if (eb_ret_rem == 16'd0) begin
                        op_ok <= !eb_fail_q;
                        op_st <= O_FIN;
                    end
                end
                O_KEC: begin
                    if (kec_done) begin
                        y_q   <= kec_y_out;
                        op_st <= O_FIN;
                    end
                end
                O_KCMP_LOAD: begin
                    if (kcmd_ready) begin
                        if (kcmp_idx == 5'd24) op_st <= O_FIN;
                        else                   kcmp_idx <= kcmp_idx + 5'd1;
                    end
                end
                O_KCMP_XOR: begin
                    if (kcmd_ready) begin
                        if (kcmp_idx == 5'd16) op_st <= O_KCMP_PERM;
                        else                   kcmp_idx <= kcmp_idx + 5'd1;
                    end
                end
                O_KCMP_PERM: begin
                    if (kcmd_ready) op_st <= O_KCMP_WAIT;
                end
                O_KCMP_WAIT: begin
                    if (kcmd_done) begin
                        kcmp_idx <= 5'd0;
                        rd_cnt   <= 4'd0;
                        op_st    <= O_KCMP_RD;
                    end
                end
                O_KCMP_RD: begin
                    if (kcmd_ready && kcmp_idx < 5'd12) kcmp_idx <= kcmp_idx + 5'd1;
                    if (kcmd_rd_valid) begin
                        y_q <= {kcmd_rd_data, y_q[11:1]};
                        if (rd_cnt == 4'd11) op_st <= O_FIN;
                        else                 rd_cnt <= rd_cnt + 4'd1;
                    end
                end
                O_KSP_COLLECT: begin
                    if (stream_fire) begin
                        if (ksp_beat == 2'd0) begin
                            if (!PROFILE_COMPACT) ksp_buf_q[511:0] <= s_axis_tdata;
                            ksp_beat <= 2'd1;
                        end else if (ksp_beat == 2'd1) begin
                            if (!PROFILE_COMPACT) ksp_buf_q[1023:512] <= s_axis_tdata;
                            ksp_beat <= 2'd2;
                        end else begin
                            ksp_lane16_q <= s_axis_tdata[63:0];
                            ksp_flags_q  <= s_axis_tdata[127:64];
                            ksp_exp_q    <= s_axis_tdata[383:128];
                            ksp_beat     <= 2'd0;
                            if (PROFILE_COMPACT) begin
                                kcmp_idx <= 5'd0;
                                op_st    <= s_axis_tdata[64] ? O_KSP_CMP_INIT : O_KSP_CMP_XOR;
                            end else begin
                                kec_nr12_top  <= s_axis_tdata[67];
                                kec_start_top <= 1'b1;
                                op_st         <= O_KSP_PERM;
                            end
                        end
                    end
                end
                O_KSP_PERM: begin
                    if (kec_done) begin
                        y_q[3:0] <= kec_dig_out;
                        if (ksp_flags_q[4] && kec_dig_out != ksp_exp_q) ksp_fail_q <= 1'b1;
                        if (ksp_rem == 16'd1) begin
                            op_ok <= !(ksp_fail_q || (ksp_flags_q[4] && kec_dig_out != ksp_exp_q));
                            op_st <= O_FIN;
                        end else begin
                            ksp_rem <= ksp_rem - 16'd1;
                            op_st   <= O_KSP_COLLECT;
                        end
                    end
                end
                O_KSP_CMP_INIT: begin
                    if (kcmd_ready) begin
                        if (kcmp_idx == 5'd24) begin
                            kcmp_idx <= 5'd0;
                            op_st    <= O_KSP_CMP_XOR;
                        end else begin
                            kcmp_idx <= kcmp_idx + 5'd1;
                        end
                    end
                end
                O_KSP_CMP_XOR: begin
                    if (kcmd_ready) begin
                        if (kcmp_idx == 5'd16) op_st <= O_KSP_CMP_PERM;
                        else                   kcmp_idx <= kcmp_idx + 5'd1;
                    end
                end
                O_KSP_CMP_PERM: begin
                    if (kcmd_ready) op_st <= O_KSP_CMP_WAIT;
                end
                O_KSP_CMP_WAIT: begin
                    if (kcmd_done) begin
                        kcmp_idx <= 5'd0;
                        rd_cnt   <= 4'd0;
                        op_st    <= O_KSP_CMP_RD;
                    end
                end
                O_KSP_CMP_RD: begin
                    if (kcmd_ready && kcmp_idx < 5'd4) kcmp_idx <= kcmp_idx + 5'd1;
                    if (kcmd_rd_valid) begin
                        ksp_dig_q <= ksp_full_dig[255:64];
                        if (rd_cnt == 4'd3) begin
                            y_q[3:0] <= ksp_full_dig;
                            if (ksp_flags_q[4] && ksp_full_dig != ksp_exp_q) ksp_fail_q <= 1'b1;
                            if (ksp_rem == 16'd1) begin
                                op_ok <= !(ksp_fail_q || (ksp_flags_q[4] && ksp_full_dig != ksp_exp_q));
                                op_st <= O_FIN;
                            end else begin
                                ksp_rem <= ksp_rem - 16'd1;
                                op_st   <= O_KSP_COLLECT;
                            end
                        end else begin
                            rd_cnt <= rd_cnt + 4'd1;
                        end
                    end
                end
                O_TS_CANOPY: begin
                    if (ts_done) begin
                        y_q[3:0] <= ts_out_root;
                        op_ok    <= ts_ok;
                        op_st    <= O_FIN;
                    end
                end
                O_GF: begin
                    if (!PROFILE_COMPACT) gf_cnt <= gf_cnt + 3'd1;
                    if (gf_done) begin
                        y_q[1:0] <= gf_r ^ x_q[5:4];
                        op_ok    <= ((gf_r ^ x_q[5:4]) == x_q[7:6]);
                        op_st    <= O_FIN;
                    end
                end
                O_FIN: begin
                    op_busy <= 1'b0;
                    op_done <= 1'b1;
                    op_st   <= O_IDLE;
                end
                default: op_st <= O_IDLE;
            endcase
        end
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_top;
    assign unused_top = &{1'b0, s_axil_awaddr[1:0], s_axil_araddr[1:0],
                          stream_q[27:20], cmd_a0_q, cmd_a1_q, ksp_flags_q, sc_h_sub,
                          sc_s2_en, sc_add_b, sc_add_c0, sc_vec_q, sc_c0_q, sc_k, sc_term,
                          chain_busy, chain_done, chain_ok, kec_y_out,
                          eb_a_q, eb_b_q, ksp_buf_q};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
