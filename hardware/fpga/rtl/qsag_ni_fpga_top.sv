// QSAG-NI FPGA accelerator top: AXI4-Lite command/register interface plus one 512-bit AXI4-Stream
// slave around the five QSAG-NI primitives and Steiner-Canopy / Sumcheck / Batch-MAC engines.
//
// Parameterized across four silicon profiles sharing the identical software-visible ISA:
//   1. VU9P_TURBO    : PROFILE_COMPACT=0, P2_UNROLLED=1, KECCAK_PIPE=1, CHAIN_SLOTW=8, FOLD_TAW=16
//   2. XCUP_RING     : PROFILE_COMPACT=0, P2_UNROLLED=0, KECCAK_PIPE=0, CHAIN_SLOTW=5, FOLD_TAW=16
//   3. ECP5_FULLRATE : PROFILE_COMPACT=1, ECP5_FULLRATE=1, FOLD_TAW=11 (or CHAIN_SLOTW=2, FOLD_TAW=9,
//                      TS_SAW=9 in fmax_ecp5_fullrate_top), AW=16, BW=16
//                      (fits ONE $45 Lattice ECP5-85F: 81/156 MULT18X18D, five-lane Fp5 +
//                       1-Sbox/clk Poseidon2 + 30-clk/rnd 1-RAM Keccak + zk-Hem v2 F_{p^5})
//   4. ECP5_COMPACT  : PROFILE_COMPACT=1, ECP5_FULLRATE=0, FOLD_TAW=11 (or CHAIN_SLOTW=2, FOLD_TAW=9,
//                      TS_SAW=9 in fmax_compact_top), AW=16, BW=16
//                      (ultra-compact 18/156 MULT18X18D = 11.5%, fits ECP5-25F/45F/85F)
//
// Register map (32-bit words, byte addresses):
//   0x000 CMD        W   [7:0] opcode, [15:8] arg0, [31:16] arg1
//   0x004 STATUS     R   [0] busy [1] done [2] ok [3] non-canonical stream limb [4] cmd err [5] active
//   0x008 OP_CYCLES  R   clocks of last operation
//   0x00C/0x010      R   TOTAL_CYCLES low/high
//   0x014 ARG32      RW  32-bit auxiliary argument (chain leaf heap idx / Canopy num_sibs)
//   0x018 CHAIN_DONE R, 0x01C CHAIN_OK R, 0x024 CHAIN_BUSY R (low 32 chain slots)
//   0x020 STREAM     RW  [31:28] destination (0=P2 chain, 1=TS Canopy frontier, 2=TS Canopy sibs,
//                        8=Fp5 fold table), [19:0] write pointer
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
//   0x11 SC_INIT            claim = X[0..4], clears sticky sumcheck failure
//   0x12 SC_ROUND           arg0==0: deg-3 in X[0..24]; arg0>=1: streamed deg=arg0 on AXI4-Stream
//                           (beat 0 = challenge, beats 1..deg+1 = c[deg]..c[0]); checks g(0)+g(1)==claim
//   0x13 FOLD_ROUND         single BRAM fold round with X[0..4]
//   0x14 FOLD_SETLEN        fold_log2n = arg0[5:0]
//   0x15 FOLD_MULTI         arg0[3:0] = m (1..6) back-to-back fold rounds with X[0..5m-1]
//   0x16 EXT5_BATCH         streams arg1 (1..65535) Fp5 MACs on AXI4-Stream (4 beats/MAC:
//                           a, b, c, exp_y), hardware-checking every mac_y == exp_y
//   0x17 EXT5_MAC           zk-Hem v2 F_p[X]/(X^5 - 3): Y[0..4] = X[0..4] * X[5..9] + X[10..14]
//   0x18 EXT5_FROB          zk-Hem v2 Frobenius: Y[0..4] = phi^(arg0)(X[0..4]), X^p = zeta_5 * X
//   0x20 KEC_LOAD           Keccak state = X[0..24]
//   0x21 KEC_PERMUTE        XOR X[0..16] unless arg0[1]; permute (12r if arg0[0] else 24r); Y=st[0..11]
//   0x22 KEC_STREAM_SPONGE  streams arg1 Keccak rate blocks on AXI4-Stream (3 beats/block: lanes 0..7,
//                           lanes 8..15, {exp_dig[383:0], flags[63:0], lane16[63:0]} where flags[4]=chk256,
//                           flags[6]=chk400 with exp_dig[399:384]=flags[63:48] covering all 50B of zk-Hem v2)
//   0x24 TS_CANOPY_VERIFY   Steiner-deduplicated TurboSHAKE256/cSHAKE256 Canopy MultiProof verify:
//                           arg0[0]=turbo, arg0[6:1]=log_leaves, arg1=num_leaves, ARG32=num_sibs,
//                           X[0..3]=expected_root; Y[0..3]=computed_root, ok=verified
//   0x30 GF_MAC             Y[0..1] = mul(X[0..1], X[2..3]) ^ X[4..5] (arg0[0]=0 poly, 1 tower128);
//                           ok = (Y[0..1] == X[6..7])
//   0x3F CLEAR              clears sticky errors and counters
module qsag_ni_fpga_top #(
    parameter bit PROFILE_COMPACT = 1'b0,
    parameter bit ECP5_FULLRATE   = 1'b0,
    parameter bit P2_UNROLLED     = 1'b0,
    parameter bit KECCAK_PIPE     = P2_UNROLLED,
    parameter int CHAIN_SLOTW     = P2_UNROLLED ? 8 : 5,
    parameter int FOLD_TAW        = PROFILE_COMPACT ? 11 : 16,
    parameter int TS_SAW          = 11,
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
    localparam int          GF128_LAT    = qsag_ni_pkg::GF128_LAT;
    localparam int          SLOTW        = CHAIN_SLOTW;
    localparam int          SLOTS        = 1 << SLOTW;
    localparam int          STEPW        = 6;
    localparam int          TAGW         = SLOTW + 2;
    localparam int          TS_FAW       = PROFILE_COMPACT ? 8 : 9;

    // Primitive 5th root of unity zeta_5 = 3^((p-1)/5) mod p (`zk_hem/v2/field5.rs:FROBENIUS_ZETA5`).
    function automatic logic [63:0] zeta5_rom(input logic [2:0] idx);
        case (idx)
            3'd0:    zeta5_rom = 64'h0000_0000_0000_0001;
            3'd1:    zeta5_rom = 64'h0e73_6627_a0ae_b983;
            3'd2:    zeta5_rom = 64'hdb8e_dc80_2dc0_b266;
            3'd3:    zeta5_rom = 64'h02ef_b5c2_a6f3_5241;
            3'd4:    zeta5_rom = 64'h130e_0794_8a9d_41d6;
            default: zeta5_rom = 64'h0000_0000_0000_0001;
        endcase
    endfunction

    function automatic logic [2:0] mod5_u8(input logic [7:0] v);
        logic [4:0] s1;
        s1 = {1'b0, v[3:0]} + {1'b0, v[7:4]}; // 16 == 1 (mod 5) -> sum in 0..30
        if      (s1 >= 5'd25) mod5_u8 = 3'(s1 - 5'd25);
        else if (s1 >= 5'd20) mod5_u8 = 3'(s1 - 5'd20);
        else if (s1 >= 5'd15) mod5_u8 = 3'(s1 - 5'd15);
        else if (s1 >= 5'd10) mod5_u8 = 3'(s1 - 5'd10);
        else if (s1 >= 5'd5)  mod5_u8 = 3'(s1 - 5'd5);
        else                  mod5_u8 = s1[2:0];
    endfunction

    function automatic logic [2:0] mul_mod5(input logic [2:0] a, input logic [2:0] b);
        case ({a, b})
            6'o11, 6'o23, 6'o32, 6'o44: mul_mod5 = 3'd1;
            6'o12, 6'o21, 6'o34, 6'o43: mul_mod5 = 3'd2;
            6'o13, 6'o24, 6'o31, 6'o42: mul_mod5 = 3'd3;
            6'o14, 6'o22, 6'o33, 6'o41: mul_mod5 = 3'd4;
            default:                    mul_mod5 = 3'd0;
        endcase
    endfunction

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
    logic [3:0][63:0] x_a, x_b, x_c;
    logic [63:0] x_scalar;
    logic x_read_pending, y_read_pending;
    logic [1:0] y_wb_cnt, y_wb_idx;
    logic p2_wb_y;
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

    wire   y_wb_busy      = PROFILE_COMPACT && ((y_wb_cnt != 2'd0) || p2_wb_y);
    wire   cmd_wb_stall   = y_wb_busy && (s_axil_awaddr == 12'h000);
    assign s_axil_awready = !rst && !aw_full && !cmd_wb_stall;
    assign s_axil_wready  = !rst && !w_full;
    wire   y_wb_stall_ar  = y_wb_busy && (s_axil_araddr[11:8] == 4'h2);
    assign s_axil_arready = !rst && !s_axil_rvalid && !x_read_pending && !y_read_pending && !y_wb_stall_ar && !(aw_full && w_full);
    assign wr_fire  = aw_full && w_full && !s_axil_bvalid && !rst && !(y_wb_busy && (aw_word == 10'h000));
    assign rd_fire  = s_axil_arvalid && s_axil_arready;
    assign wr_word  = aw_word;
    assign rd_word  = s_axil_araddr[11:2];
    assign wr_error = (|wr_strb) && ((wr_word == 10'h000 && (wr_strb != 4'hf || op_busy))
                                  || (op_busy && (wr_word[9:6] == 4'h1 || wr_word == 10'h005 || wr_word == 10'h008)));
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
    typedef enum logic [5:0] {
        O_IDLE, O_P2_OFFER, O_P2_WAIT, O_CH_START, O_CH_WAIT, O_CH_READ,
        O_FIELD_REG, O_FIELD_BEAT, O_FIELD_LOAD, O_FIELD_WAIT,
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
    logic             p2_out_lane_valid;
    logic [3:0]       p2_out_lane_idx;
    logic [63:0]      p2_out_lane_data;
    /* verilator lint_off UNUSEDSIGNAL */
    logic             p2_out_jive;
    /* verilator lint_on UNUSEDSIGNAL */

    logic             op_job_valid, op_job_jive;
    logic             eng_job_valid, eng_job_jive, eng_job_last, eng_job_active;
    logic             eng_job_lane_valid, eng_job_lane_last;
    logic [63:0]      eng_job_lane_data;
    logic [767:0]     eng_job_state;
    logic [SLOTW-1:0] eng_job_slot;
    logic             eng_start_valid, eng_start_ready, eng_start_lane_ready, eng_rd_valid, eng_rd_done, eng_clr;
    logic             eng_rd_lane_valid;
    logic [3:0]       eng_rd_lane_idx;
    logic [63:0]      eng_rd_lane_data;
    logic [767:0]     eng_rd_state;
    logic [191:0]     tree_key_q;
    logic [255:0]     expect_q;
    logic [SLOTS-1:0] chain_busy, chain_done, chain_ok;
    wire  [31:0]      chain_busy32 = 32'(chain_busy);
    wire  [31:0]      chain_done32 = 32'(chain_done);
    wire  [31:0]      chain_ok32   = 32'(chain_ok);

    assign p2_wb_y = PROFILE_COMPACT && p2_out_lane_valid && !p2_out_tag[TAGW-1];
    wire p2_hold_wb = PROFILE_COMPACT && ((op_st == O_P2_WAIT) || p2_wb_y);
    logic arb_locked, arb_owner, select_eng;
    if (PROFILE_COMPACT) begin : g_p2_arb_cmp
        assign arb_locked  = 1'b0;
        assign arb_owner   = 1'b0;
        assign select_eng  = eng_job_active;
        assign p2_in_valid = !p2_hold_wb && !eng_job_active && op_job_valid;
        assign p2_in_state = {x_c, x_b, x_a};
        assign p2_in_jive  = eng_job_active ? eng_job_jive : op_job_jive;
        assign p2_in_tag   = eng_job_active ? {1'b1, eng_job_last, eng_job_slot} : '0;
    end else begin : g_p2_arb_par
        assign select_eng = arb_locked ? arb_owner : eng_job_valid;
        always_ff @(posedge clk) begin
            if (rst) begin arb_locked <= 1'b0; arb_owner <= 1'b0; end
            else if (p2_in_valid) begin
                arb_locked <= !p2_in_ready;
                if (!p2_in_ready) arb_owner <= select_eng;
            end
        end
        assign p2_in_valid = select_eng ? eng_job_valid : op_job_valid;
        assign p2_in_state = select_eng ? eng_job_state : {x_c, x_b, x_a};
        assign p2_in_jive  = select_eng ? eng_job_jive  : op_job_jive;
        assign p2_in_tag   = select_eng ? {1'b1, eng_job_last, eng_job_slot} : '0;
    end

    if (PROFILE_COMPACT) begin : g_compact_p2
        qsag_p2_compact #(.TAGW(TAGW), .AW(AW), .BW(BW), .USE_PIPE_SBOX(ECP5_FULLRATE)) u_p2 (
            .clk(clk), .rst(rst),
            .in_valid(p2_in_valid), .in_ready(p2_in_ready), .in_state(p2_in_state),
            .in_jive(p2_in_jive), .in_tag(p2_in_tag),
            .in_lane_valid(eng_job_lane_valid), .in_lane_last(eng_job_lane_last), .in_lane_data(eng_job_lane_data),
            .out_valid(p2_out_valid), .out_jive(p2_out_jive), .out_tag(p2_out_tag),
            .out_lane_valid(p2_out_lane_valid), .out_lane_idx(p2_out_lane_idx), .out_lane_data(p2_out_lane_data),
            .busy(p2_busy));
        assign p2_out_state = '0;
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
        assign p2_in_ready       = !rst;
        assign p2_busy           = (active != '0) || p2_out_valid;
        assign p2_out_lane_valid = 1'b0;
        assign p2_out_lane_idx   = 4'd0;
        assign p2_out_lane_data  = 64'd0;
    end else begin : g_ring_p2
        qsag_poseidon2_12_fpga #(.TAGW(TAGW), .AW(AW), .BW(BW)) u_p2 (
            .clk(clk), .rst(rst),
            .in_valid(p2_in_valid), .in_ready(p2_in_ready), .in_state(p2_in_state),
            .in_jive(p2_in_jive), .in_tag(p2_in_tag),
            .out_valid(p2_out_valid), .out_state(p2_out_state), .out_jive(p2_out_jive),
            .out_tag(p2_out_tag), .busy(p2_busy));
        assign p2_out_lane_valid = 1'b0;
        assign p2_out_lane_idx   = 4'd0;
        assign p2_out_lane_data  = 64'd0;
    end

    // ------------------------------------------------------------------ AXI4-Stream routing
    wire [3:0] stream_dst = stream_q[31:28];
    wire       op_takes_stream = ((op_st == O_FIELD_BEAT || op_st == O_FIELD_LOAD || op_st == O_FIELD_WAIT) &&
                                  (cmd_op_q == 8'h16 || (cmd_op_q == 8'h12 && cmd_a0_q != 0)))
                              || (op_st == O_KSP_COLLECT) || (op_st == O_KSP_PERM)
                              || (op_st == O_KSP_CMP_INIT) || (op_st == O_KSP_CMP_XOR)
                              || (op_st == O_KSP_CMP_PERM) || (op_st == O_KSP_CMP_WAIT)
                              || (op_st == O_KSP_CMP_RD);
    logic      op_stream_ready;
    logic      ts_busy;
    logic      fold_start, fold_busy, fold_done;

    logic passive_ready;
    always_comb begin
        case (stream_dst)
            4'h0: passive_ready = !chain_busy[stream_q[SLOTW+STEPW-1:STEPW]];
            4'h1, 4'h2: passive_ready = !ts_busy;
            4'h8: passive_ready = !fold_busy && !fold_start && !(op_busy && (cmd_op_q == 8'h13 || cmd_op_q == 8'h15));
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
    wire stream_bad      = (stream_dst == 4'h8) ? (|limb_bad[4:0]) : (|limb_bad);
    wire active_stream_bad = stream_fire && op_st == O_FIELD_BEAT && (|limb_bad[4:0]);

    logic [3:0] xa_bad, xb_bad, xc_bad;
    for (genvar i = 0; i < 4; i++) begin : g_xcanon
        assign xa_bad[i] = (&x_a[i][63:32]) && (|x_a[i][31:0]);
        assign xb_bad[i] = (&x_b[i][63:32]) && (|x_b[i][31:0]);
        assign xc_bad[i] = (&x_c[i][63:32]) && (|x_c[i][31:0]);
    end

    logic [3:0] rd_cnt;

    qsag_p2_chain_engine #(.SLOTW(SLOTW), .STEPW(STEPW), .AW(AW), .COMPACT_64(PROFILE_COMPACT)) u_chain (
        .clk(clk), .rst(rst), .tree_key(tree_key_q), .exp_root(expect_q), .clr_maps(eng_clr),
        .bw_en(passive_stream && stream_dst == 4'h0),
        .bw_addr(stream_q[SLOTW+STEPW-1:0]),
        .bw_data(s_axis_tdata),
        .start_valid(eng_start_valid), .start_ready(eng_start_ready),
        .start_slot(cmd_a0_q[SLOTW-1:0]), .start_nsponge(cmd_a1_q[5:0]),
        .start_heap(arg32_q), .start_state(PROFILE_COMPACT ? 768'd0 : {x_c, x_b, x_a}),
        .start_lane_valid(PROFILE_COMPACT && (op_st == O_CH_START)),
        .start_lane_ready(eng_start_lane_ready),
        .start_lane_idx(rd_cnt),
        .start_lane_data(x_scalar),
        .rd_valid(eng_rd_valid), .rd_slot(cmd_a0_q[SLOTW-1:0]),
        .rd_done(eng_rd_done), .rd_state(eng_rd_state),
        .rd_lane_valid(eng_rd_lane_valid), .rd_lane_idx(eng_rd_lane_idx), .rd_lane_data(eng_rd_lane_data),
        .job_valid(eng_job_valid),
        .job_ready(PROFILE_COMPACT ? (!p2_hold_wb && p2_in_ready && (op_st != O_P2_OFFER)) : (p2_in_ready && select_eng)),
        .job_state(eng_job_state),
        .job_jive(eng_job_jive), .job_last(eng_job_last), .job_slot(eng_job_slot),
        .job_active(eng_job_active),
        .job_lane_valid(eng_job_lane_valid), .job_lane_last(eng_job_lane_last), .job_lane_data(eng_job_lane_data),
        .res_valid(!PROFILE_COMPACT && p2_out_valid && p2_out_tag[TAGW-1]),
        .res_last(p2_out_tag[SLOTW]),
        .res_slot(p2_out_tag[SLOTW-1:0]),
        .res_state(PROFILE_COMPACT ? 768'd0 : p2_out_state),
        .res_lane_valid(PROFILE_COMPACT && p2_out_lane_valid && p2_out_tag[TAGW-1]),
        .res_lane_idx(p2_out_lane_idx),
        .res_lane_data(p2_out_lane_data),
        .busy_map(chain_busy), .done_map(chain_done), .ok_map(chain_ok));

    wire [3:0] x_we = (wr_fire && !wr_error && wr_word[9:6] == 4'h1) ? wr_strb : 4'd0;
    typedef enum logic [2:0] {F_A,F_B,F_C,F_R,F_EXPECT,F_CLAIM} field_input_t;
    field_input_t field_input;
    logic [2:0] field_lane, frob_lane, frob_k;
    logic [4:0] field_base;
    logic [7:0] coeff_left;
    logic [15:0] batch_left;
    logic [3:0] fold_left;
    logic [5:0] fold_log2n_q;
    logic [319:0] beat_q;
    logic [63:0] claim_q[5], sc_sum[5], expected[5];
    logic sc_fail_q, batch_fail;
    logic mac_valid, mac_done, lane_valid, direct_bad;
    logic [2:0] lane_idx;
    logic [63:0] lane_data;
    logic [319:0] wide_result;
    wire is_sc = cmd_op_q == 8'h12;
    wire is_batch = cmd_op_q == 8'h16;
    wire is_frob = cmd_op_q == 8'h18;
    wire from_stream = is_batch || (is_sc && cmd_a0_q != 0);
    wire direct_mac = !PROFILE_COMPACT && cmd_op_q == 8'h17;
    wire [63:0] field_word = from_stream ? beat_q[63:0] : x_scalar;
    logic [63:0] operand;
    always_comb begin
        operand = field_word;
        if (is_frob) begin
            operand = 0;
            if (field_lane == 0) case (field_input)
                F_A: operand = x_scalar;
                F_B: operand = zeta5_rom(mul_mod5(frob_lane,frob_k));
                default: ;
            endcase
        end
    end
    // A register write is forwarded after the synchronous X read has settled.
    // Track each working limb independently. Field commands that reuse the banks
    // invalidate them, so a later MAC with partially rewritten X reloads safely.
    wire x_update = PROFILE_COMPACT && (|x_we) && wr_word[5:1] < 15;
    logic x_pending, x_forward;
    logic [3:0] x_pending_idx, x_forward_idx;
    logic [14:0] loaded;
    wire [14:0] forward_mask = x_forward ? 15'b1 << x_forward_idx : 15'd0;
    wire operands_ready = &(loaded | forward_mask);
    always_ff @(posedge clk) begin
        x_pending <= x_update && !rst;
        x_forward <= x_pending && !rst;
        if (x_update) x_pending_idx <= wr_word[4:1];
        x_forward_idx <= x_pending_idx;
        if (rst || (cmd_fire && wr_data[7:0] >= 8'h11 && wr_data[7:0] <= 8'h18 &&
                    (wr_data[7:0] != 8'h17 || !operands_ready))) loaded <= 0;
        else loaded <= (loaded | forward_mask) & ~(x_update ? 15'b1 << wr_word[4:1] : 15'd0);
    end
    wire [1:0] forward_sel = x_forward_idx < 5 ? 0 : x_forward_idx < 10 ? 1 : 2;
    wire [2:0] forward_idx = x_forward_idx[2:0] - (forward_sel == 0 ? 0 : forward_sel == 1 ? 3'd5 : 3'd2);
    logic [14:0] forward_bad;
    always_ff @(posedge clk) if (x_forward) forward_bad[x_forward_idx] <= x_scalar >= qsag_ni_pkg::GL_P;
    wire cached_bad = |(forward_bad & ~forward_mask) || (x_forward && x_scalar >= qsag_ni_pkg::GL_P);
    wire feedback = is_sc && lane_valid && coeff_left != 0;
    wire lane_we = x_forward || feedback || (op_st == O_FIELD_LOAD && field_input <= F_R);
    wire [1:0] lane_sel = x_forward ? forward_sel : feedback ? 2'd0 : field_input[1:0];
    wire [2:0] lane_addr = x_forward ? forward_idx : feedback ? lane_idx : field_lane;
    wire [63:0] lane_in = x_forward ? x_scalar : feedback ? lane_data : operand;
    wire table_we = passive_stream && stream_dst == 4'h8;
    // Serial results feed both the Horner recurrence and the result window.
    wire field_y_we = lane_valid && (!is_frob || lane_idx == 0) &&
                      (!is_sc || coeff_left == 0) && (!is_batch || batch_left == 1);
    wire [2:0] field_y_idx = is_frob ? frob_lane : lane_idx;
    if (PROFILE_COMPACT) begin : g_compact_fp5
        qsag_fp5_compact_bfly #(.TAW(FOLD_TAW),.AW(AW),.BW(BW),.PARALLEL_5(ECP5_FULLRATE)) u_fp5 (
            .clk,.rst,.tw_en(table_we),.tw_idx(stream_q[FOLD_TAW-1:0]),.tw_data(s_axis_tdata[319:0]),
            .mac_valid,.mac_done,.fold_start,.fold_busy,.fold_done,.fold_log2n(fold_log2n_q),
            .in_lane_we(lane_we),.in_sel(lane_sel),.in_lane_idx(lane_addr),.in_lane_data(lane_in),
            .out_lane_valid(lane_valid),.out_lane_idx(lane_idx),.out_lane_data(lane_data));
        assign direct_bad = cached_bad;
        assign wide_result = '0;
    end else begin : g_parallel_fp5
        logic [319:0] a,b,c,r,raw_y,fold_y,result;
        logic raw_done,fold_raw_done,serializing,is_fold;
        logic [2:0] index;
        logic [1023:0] fast_words;
        qsag_x_window #(.LANE_BITS(4)) u_fast (.clk,.wa(wr_word[5:0]),.we(x_we),.wd(wr_data),.ra(1'b0),.rd(fast_words));
        logic [14:0] fast_bad;
        for (genvar n=0;n<15;n++) begin : g_fast_canon
            assign fast_bad[n] = fast_words[64*n+:64] >= qsag_ni_pkg::GL_P;
        end
        assign direct_bad = |fast_bad;
        always_ff @(posedge clk) if (lane_we) case (lane_sel)
            0: a[64*lane_addr+:64] <= lane_in;
            1: b[64*lane_addr+:64] <= lane_in;
            2: c[64*lane_addr+:64] <= lane_in;
            3: r[64*lane_addr+:64] <= lane_in;
        endcase
        /* verilator lint_off PINCONNECTEMPTY */
        qsag_ext5_mac_bfly #(.TAW(FOLD_TAW),.AW(AW),.BW(BW)) u_fp5 (
            .clk,.rst,.tw_en(table_we),.tw_idx(stream_q[FOLD_TAW-1:0]),.tw_data(s_axis_tdata[319:0]),
            .mac_valid,.mac_done(raw_done),.mac_a(direct_mac ? fast_words[319:0] : a),
            .mac_b(direct_mac ? fast_words[639:320] : b),.mac_c(direct_mac ? fast_words[959:640] : c),
            .mac_y(raw_y),.fold_start,.fold_busy,.fold_log2n(fold_log2n_q),.fold_r(r),
            .fold_done(fold_raw_done),.fold_wr_last(),.fold_res(fold_y));
        /* verilator lint_on PINCONNECTEMPTY */
        always_ff @(posedge clk) begin
            if (rst) serializing <= 0;
            else if ((raw_done && !direct_mac) || fold_raw_done) begin
                result <= fold_raw_done ? fold_y : raw_y;
                index <= 0;
                is_fold <= fold_raw_done;
                serializing <= 1;
            end else if (serializing) begin
                index <= index + 1'b1;
                result <= {64'd0,result[319:64]};
                if (index == 4) serializing <= 0;
            end
        end
        assign wide_result = raw_y;
        assign mac_done = direct_mac ? raw_done : serializing && !is_fold && index == 4;
        assign fold_done = serializing && is_fold && index == 4;
        assign lane_valid = serializing;
        assign lane_idx = index;
        assign lane_data = result[63:0];
        wire unused_fast = &{1'b0,fast_words[1023:960]};
    end

    function automatic logic [63:0] field_add(input logic [63:0] a,b);
        logic [64:0] s;
        s = {1'b0,a} + {1'b0,b};
        field_add = s >= {1'b0,qsag_ni_pkg::GL_P} ? s[63:0]-qsag_ni_pkg::GL_P : s[63:0];
    endfunction
    wire [64:0] claim_diff = {1'b0,claim_q[field_lane]} - {1'b0,operand};
    wire [63:0] field_sub_claim = claim_diff[64] ? claim_diff[63:0] + qsag_ni_pkg::GL_P : claim_diff[63:0];

    // ------------------------------------------------------------------ Keccak + TS Canopy Engine
    logic          ts_start, ts_done, ts_ok, ts_root_rd_phase;
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
    logic [63:0]   ksp_lane16_q, ksp_flags_q;
    logic [399:0]  ksp_exp_q;
    logic          ksp_fail_q, ksp_cmp_word_bad;
    logic [511:0]  ksp_par_we_data;
    logic [1:0]    ksp_par_we;

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

        // Store the 1,024-bit KEC_STREAM_SPONGE rate buffer (rows 0..1) and raw beat 2 (row 2).
        logic [511:0] ksp_bram_rd;
        wire  [3:0]   ksp_bram_ra4 = (op_st == O_KSP_CMP_WAIT || op_st == O_KSP_CMP_RD)
                                   ? 4'd2
                                   : ((op_st == O_KSP_CMP_XOR)
                                      ? {3'd0, kcmp_idx[3] | (kcmd_ready && (kcmp_idx[2:0] == 3'd7))}
                                      : 4'd0);
        qsag_sdp_bram #(.AW(4), .DW(512), .NO_RW_CHECK(1'b1)) u_ksp_bram (
            .clk(clk),
            .we((op_st == O_KSP_COLLECT) && stream_fire),
            .wa({2'd0, ksp_beat}),
            .wd(s_axis_tdata),
            .ra(ksp_bram_ra4),
            .rd(ksp_bram_rd));
        wire [2:0]  ksp_exp_idx  = rd_cnt[2:0] + 3'd2;
        wire [63:0] ksp_exp_lane = ksp_bram_rd[64*ksp_exp_idx +: 64];
        assign ksp_cmp_word_bad  = (rd_cnt < 4'd4)
                                 ? ((ksp_flags_q[4] || ksp_flags_q[6]) && (kcmd_rd_data != ksp_exp_lane))
                                 : ((rd_cnt < 4'd6)
                                    ? (ksp_flags_q[6] && (kcmd_rd_data != ksp_exp_lane))
                                    : ((rd_cnt == 4'd6)
                                       ? (ksp_flags_q[6] && (kcmd_rd_data[15:0] != ksp_bram_rd[127:112]))
                                       : 1'b0));

        logic        top_kcmd_valid, top_kcmd_nr12;
        logic [1:0]  top_kcmd_op;
        logic [4:0]  top_kcmd_idx;
        logic [63:0] top_kcmd_wdata;

        always_comb begin
            top_kcmd_valid = 1'b0;
            top_kcmd_op    = 2'd0;
            top_kcmd_nr12  = cmd_a0_q[0];
            top_kcmd_idx   = kcmp_idx;
            top_kcmd_wdata = x_scalar;
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
                O_KSP_CMP_RD: if (kcmp_idx < 5'd8) begin
                    top_kcmd_valid = 1'b1;
                    top_kcmd_op    = 2'd3;
                end
                default: ;
            endcase
        end

        wire use_ts = (op_st == O_TS_CANOPY);
        qsag_keccak_compact u_keccak (
            .clk(clk), .rst(rst), .bank_sel(use_ts),
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
        assign unused_par_k = &{1'b0, kec_start_top, kec_load, kec_nr12_top, ts_kec_start, ts_kec_nr12, ts_kec_state, ksp_par_we, ksp_par_we_data};
    end else begin : g_kec_parallel
        logic [1023:0] ksp_buf_q;
        logic [767:0] kec_x_low_q;
        always_ff @(posedge clk)
            if (cmd_fire && (wr_data[7:0] == 8'h20 || wr_data[7:0] == 8'h21))
                kec_x_low_q <= {x_c, x_b, x_a};

        logic [1599:0] kec_hold_q, kec_in, kec_state, ksp_base;
        always_ff @(posedge clk) begin
            if (ksp_par_we[0]) ksp_buf_q[511:0]   <= ksp_par_we_data;
            if (ksp_par_we[1]) ksp_buf_q[1023:512] <= ksp_par_we_data;
        end
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
                if (!cmd_a0_q[1]) kec_in[1087:0] = kec_hold_q[1087:0] ^ {x_b[0], x_a, kec_x_low_q};
            end
        end
        wire par_start = (op_st == O_TS_CANOPY) ? ts_kec_start : kec_start_top;
        wire par_nr12  = (op_st == O_TS_CANOPY) ? ts_kec_nr12  : kec_nr12_top;
        qsag_keccak_turboshake #(.RPC(KECCAK_RPC)) u_keccak (
            .clk(clk), .rst(rst), .start(par_start), .nr12(par_nr12), .state_i(kec_in),
            .busy(kec_busy), .done(kec_done), .state_o(kec_state));
        always_ff @(posedge clk) begin
            if (kec_load) kec_hold_q <= {x_scalar, x_c, x_b, x_a, kec_x_low_q};
            else if (kec_done && op_st != O_TS_CANOPY) kec_hold_q <= kec_state;
        end
        assign kec_dig_out   = kec_state[255:0];
        assign kec_y_out     = kec_state[767:0];
        assign kcmd_ready    = 1'b0;
        assign kcmd_done     = 1'b0;
        assign kcmd_rd_valid = 1'b0;
        assign kcmd_rd_data  = '0;
        assign ksp_cmp_word_bad = 1'b0;
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
        .in_exp_root  (x_a),
        .busy(ts_busy), .done(ts_done), .ok(ts_ok), .root_rd_phase(ts_root_rd_phase), .out_root(ts_out_root),
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
            .a(x_a[1:0]), .b(x_a[3:2]), .done(gf_done), .r(gf_r));
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_gf_cnt = &{1'b0, gf_cnt};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_gf_par
        logic [127:0] gf_pa, gf_pb, gf_in_a, gf_in_b, gf_raw_r, gf_tow_r;
        qsag_gf128_tower_map #(.INVERSE(0)) u_tow_a (.x(x_a[1:0]), .y(gf_pa));
        qsag_gf128_tower_map #(.INVERSE(0)) u_tow_b (.x(x_a[3:2]), .y(gf_pb));
        assign gf_in_a = cmd_a0_q[0] ? gf_pa : x_a[1:0];
        assign gf_in_b = cmd_a0_q[0] ? gf_pb : x_a[3:2];
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
            O_FIELD_BEAT:  op_stream_ready = 1'b1;
            O_KSP_COLLECT: op_stream_ready = 1'b1;
            default:       op_stream_ready = 1'b0;
        endcase
    end

    logic [63:0] gf_high;
    wire        ksp_par_bad = (ksp_flags_q[4] && (kec_dig_out != ksp_exp_q[255:0]))
                           || (ksp_flags_q[6] && (kec_y_out[399:0] != ksp_exp_q));

    assign op_job_valid    = (op_st == O_P2_OFFER);
    assign op_job_jive     = (cmd_op_q == 8'h02);
    assign eng_start_valid = (op_st == O_CH_START);
    assign eng_rd_valid    = (op_st == O_CH_READ) && !eng_rd_done;

    wire engines_busy = op_busy || p2_busy || (|chain_busy) || fold_busy || kec_busy || ts_busy;

    // Read addresses are issued one edge before consumption. In idle A/B/C
    // always present X[0..11], including the cycle a command commits. AXI
    // buffer refill leaves at least one read edge after the last X write.
    logic [2:0] xa_ra, xb_ra, xc_ra;
    logic [4:0] xs_ra;
    always_comb begin
        xa_ra = 3'd0;
        xb_ra = 3'd1;
        xc_ra = 3'd2;
        xs_ra = x_pending ? {1'b0,x_pending_idx} : 5'd0;
        if (!PROFILE_COMPACT && cmd_fire && (wr_data[7:0] == 8'h20 || wr_data[7:0] == 8'h21)) begin
            xa_ra = 3'd3;
            xb_ra = 3'd4;
            xc_ra = 3'd5;
            xs_ra = 5'd24;
        end
        case (op_st)
            O_CH_START: if (PROFILE_COMPACT) xs_ra = eng_start_lane_ready ? {1'b0, rd_cnt + 4'd1} : {1'b0, rd_cnt};
            O_FIELD_REG: xs_ra = field_base;
            O_FIELD_LOAD: xs_ra = is_frob ? field_base : field_base + {2'd0,field_lane} + 1'b1;
            O_KCMP_LOAD, O_KCMP_XOR: xs_ra = kcmd_ready ? kcmp_idx + 5'd1 : kcmp_idx;
            default: ;
        endcase
    end
    if (PROFILE_COMPACT) begin : g_fixed_x
        // Only the twelve fixed Poseidon lanes need simultaneous reads here.
        logic [767:0] words;
        for (genvar w=0; w<24; w++) begin : g_word
            for (genvar b=0; b<4; b++) begin : g_byte
                always_ff @(posedge clk)
                    if (wr_word[5:0] == 6'(w) && x_we[b])
                        words[32*w+8*b+:8] <= wr_data[8*b+:8];
            end
        end
        assign {x_c,x_b,x_a} = words;
    end else begin : g_wide_x
        qsag_x_window u_xa (.clk, .wa(wr_word[5:0]), .we(x_we), .wd(wr_data), .ra(xa_ra), .rd(x_a));
        qsag_x_window u_xb (.clk, .wa(wr_word[5:0]), .we(x_we), .wd(wr_data), .ra(xb_ra), .rd(x_b));
        qsag_x_window u_xc (.clk, .wa(wr_word[5:0]), .we(x_we), .wd(wr_data), .ra(xc_ra), .rd(x_c));
    end
    qsag_x_window #(.LANE_BITS(0)) u_xs (
        .clk, .wa(wr_word[5:0]), .we(x_we), .wd(wr_data), .ra(xs_ra), .rd(x_scalar));

    wire y_start_gf = PROFILE_COMPACT && (op_st == O_GF) && gf_done;

    logic [31:0] x_rw_val, y_rw_val;
    wire x_read = !PROFILE_COMPACT && rd_fire && rd_word[9:6] == 4'h1;
    wire y_read =  PROFILE_COMPACT && rd_fire && rd_word[9:6] == 4'h2 && rd_word[5:1] < 5'd12;
    if (!PROFILE_COMPACT) begin : g_x_rdback
        logic [63:0] limb;
        logic high_half;
        qsag_x_window #(.LANE_BITS(0)) u_xr (
            .clk, .wa(wr_word[5:0]), .we(x_we), .wd(wr_data), .ra(rd_word[5:1]), .rd(limb));
        always_ff @(posedge clk) if (x_read) high_half <= rd_word[0];
        assign x_rw_val = high_half ? limb[63:32] : limb[31:0];
        assign y_rw_val = 32'd0;
    end else begin : g_y_bram
        assign x_rw_val = 32'd0;
        logic        y_we_64, y_rd_hi_q;
        logic [3:0]  y_wa_64;
        logic [63:0] y_wd_64, y_rd_word64;
        always_comb begin
            y_we_64 = 1'b0;
            y_wa_64 = 4'd0;
            y_wd_64 = lane_data;
            if (!rst) begin
                if (field_y_we) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = {1'b0,field_y_idx};
                    y_wd_64 = lane_data;
                end else if (y_start_gf) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = 4'd0;
                    y_wd_64 = gf_r[63:0] ^ x_b[0];
                end else if (y_wb_cnt != 2'd0) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = {2'd0, y_wb_idx};
                    y_wd_64 = gf_high;
                end else if (p2_wb_y) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = p2_out_lane_idx;
                    y_wd_64 = p2_out_lane_data;
                end else if ((op_st == O_CH_READ) && eng_rd_lane_valid) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = eng_rd_lane_idx;
                    y_wd_64 = eng_rd_lane_data;
                end else if (((op_st == O_KCMP_RD) || (op_st == O_KSP_CMP_RD) ||
                              ((op_st == O_TS_CANOPY) && ts_root_rd_phase)) && kcmd_rd_valid) begin
                    y_we_64 = 1'b1;
                    y_wa_64 = rd_cnt;
                    y_wd_64 = kcmd_rd_data;
                end
            end
        end
        (* ram_style = "block", no_rw_check *) logic [63:0] y_mem [0:511];
        always_ff @(posedge clk) begin
            if (y_we_64) y_mem[{5'd0, y_wa_64}] <= y_wd_64;
            y_rd_word64 <= y_mem[{5'd0, rd_word[4:1]}];
            if (y_read) y_rd_hi_q <= rd_word[0];
        end
        assign y_rw_val = y_rd_hi_q ? y_rd_word64[63:32] : y_rd_word64[31:0];
    end
    always_ff @(posedge clk) begin
        x_read_pending <= !rst && x_read;
        y_read_pending <= !rst && y_read;
    end
    assign ksp_par_we_data = s_axis_tdata;
    assign ksp_par_we[0]   = !PROFILE_COMPACT && (op_st == O_KSP_COLLECT) && stream_fire && (ksp_beat == 2'd0);
    assign ksp_par_we[1]   = !PROFILE_COMPACT && (op_st == O_KSP_COLLECT) && stream_fire && (ksp_beat == 2'd1);

    always_ff @(posedge clk) begin
        fold_start    <= 1'b0;
        mac_valid <= 1'b0;
        kec_start_top <= 1'b0;
        kec_load      <= 1'b0;
        ts_start      <= 1'b0;
        gf_start      <= 1'b0;
        eng_clr       <= 1'b0;
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
            ksp_fail_q    <= 1'b0;
            fold_log2n_q  <= 6'd1;
            stream_q      <= '0;
            arg32_q       <= '0;
            s_axil_bvalid <= 1'b0;
            s_axil_bresp  <= 2'b00;
            s_axil_rvalid <= 1'b0;
            y_wb_cnt      <= 2'd0;
            y_wb_idx      <= 2'd0;
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
            if (x_read_pending) begin
                s_axil_rvalid <= 1'b1;
                s_axil_rdata  <= x_rw_val;
            end
            if (y_read_pending) begin
                s_axil_rvalid <= 1'b1;
                s_axil_rdata  <= y_rw_val;
            end
            if (rd_fire && !x_read && !y_read) begin
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
                        if (!PROFILE_COMPACT && rd_word[9:6] == 4'h2 && rd_word[5:1] < 5'd12)
                            s_axil_rdata <= rd_word[0] ? y_q[rd_word[4:1]][63:32]
                                                       : y_q[rd_word[4:1]][31:0];
                    end
                endcase
            end

            // ---- Passive & active stream canonicality update
            if (passive_stream) begin
                stream_q[19:0] <= stream_q[19:0] + 20'd1;
                if (stream_check_en && stream_bad) err_noncanon <= 1'b1;
            end
            if (active_stream_bad) err_noncanon <= 1'b1;
            // ---- Counters (64-bit total counter pipelined into two 32-bit halves)
            total_cy_q <= engines_busy && (total_lo_q == 32'hFFFF_FFFF);
            if (total_cy_q)   total_hi_q   <= total_hi_q + 32'd1;
            if (engines_busy) total_lo_q   <= total_lo_q + 32'd1;
            if (op_busy)      op_cycles_q  <= op_cycles_q + 32'd1;
            if (p2_out_valid) perms_q      <= perms_q + 32'd1;
            if (fold_done)    fold_log2n_q <= fold_log2n_q - 6'd1;

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
                            8'h01, 8'h02: begin
                                if (|xa_bad || |xb_bad || |xc_bad) err_noncanon <= 1'b1;
                                op_st <= O_P2_OFFER;
                            end
                            8'h03: begin
                                if (|chain_busy) begin
                                    err_cmd <= 1'b1; op_ok <= 1'b0;
                                end else if (!wr_data[9]) begin
                                    if (|xa_bad[2:0] || |xb_bad) err_noncanon <= 1'b1;
                                    tree_key_q <= x_a[2:0];
                                    expect_q   <= x_b;
                                end
                                eng_clr <= wr_data[8] && !(|chain_busy);
                                op_st   <= O_FIN;
                            end
                            8'h04: begin
                                if (chain_busy[wr_data[8 +: SLOTW]] ||
                                    (arg32_q <= 32'd1 && wr_data[21:16] == 6'd0)) begin
                                    err_cmd <= 1'b1; op_ok <= 1'b0; op_st <= O_FIN;
                                end else begin
                                    if (|xa_bad || |xb_bad || |xc_bad) err_noncanon <= 1'b1;
                                    rd_cnt <= 4'd0;
                                    op_st  <= O_CH_START;
                                end
                            end
                            8'h05: op_st <= O_CH_WAIT;
                            8'h06: op_st <= O_CH_READ;
                            8'h11: begin
                                field_input <= F_CLAIM;
                                field_base <= 0;
                                sc_fail_q <= 0;
                                op_st <= O_FIELD_REG;
                            end
                            8'h12: begin
                                field_input <= F_B;
                                field_base <= 20;
                                coeff_left <= wr_data[15:8] == 0 ? 8'd3 : wr_data[15:8];
                                op_st <= wr_data[15:8] == 0 ? O_FIELD_REG : O_FIELD_BEAT;
                            end
                            8'h13,8'h15: begin
                                logic [5:0] n;
                                logic [3:0] rounds;
                                n = wr_data[7:0] == 8'h15 && wr_data[21:16] != 0 ? wr_data[21:16] : fold_log2n_q;
                                rounds = wr_data[7:0] == 8'h13 ? 4'd1 : wr_data[11:8];
                                if (rounds == 0 || rounds > 6 || n < {2'd0,rounds} || n > 6'(FOLD_TAW)) begin
                                    err_cmd <= 1; op_ok <= 0; op_st <= O_FIN;
                                end else begin
                                    fold_log2n_q <= n;
                                    fold_left <= rounds;
                                    field_input <= F_R;
                                    field_base <= 0;
                                    op_st <= O_FIELD_REG;
                                end
                            end
                            8'h14: begin
                                if (wr_data[13:8] == 0 || wr_data[13:8] > 6'(FOLD_TAW)) begin
                                    err_cmd <= 1; op_ok <= 0;
                                end else fold_log2n_q <= wr_data[13:8];
                                op_st <= O_FIN;
                            end
                            8'h16: begin
                                field_input <= F_A;
                                batch_left <= wr_data[31:16];
                                batch_fail <= 0;
                                if (wr_data[31:16] == 0) begin
                                    err_cmd <= 1; op_ok <= 0; op_st <= O_FIN;
                                end else op_st <= O_FIELD_BEAT;
                            end
                            8'h17,8'h18: begin
                                field_input <= F_A;
                                field_base <= 0;
                                frob_lane <= 0;
                                frob_k <= mod5_u8(wr_data[15:8]);
                                if ((!PROFILE_COMPACT || operands_ready) && wr_data[7:0] == 8'h17) begin
                                    mac_valid <= 1;
                                    if (direct_bad) err_noncanon <= 1;
                                    op_st <= O_FIELD_WAIT;
                                end else op_st <= O_FIELD_REG;
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
                                rd_cnt   <= 4'd0;
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
                                err_cmd <= 1'b1;
                                op_ok <= 1'b0;
                                op_st <= O_FIN;
                            end
                        endcase
                    end
                end
                O_P2_OFFER: begin
                    if (PROFILE_COMPACT ? (p2_in_ready && !p2_hold_wb && !eng_job_active)
                                        : (p2_in_ready && !select_eng))
                        op_st <= O_P2_WAIT;
                end
                O_P2_WAIT: begin
                    if (p2_out_valid && !p2_out_tag[TAGW-1]) begin
                        if (!PROFILE_COMPACT) y_q <= p2_out_state;
                        op_st <= O_FIN;
                    end
                end
                O_CH_START: begin
                    if (PROFILE_COMPACT) begin
                        if (eng_start_lane_ready) begin
                            if (rd_cnt == 4'd11) op_st  <= O_FIN;
                            else                 rd_cnt <= rd_cnt + 4'd1;
                        end
                    end else if (eng_start_ready) begin
                        op_st <= O_FIN;
                    end
                end
                O_CH_WAIT: begin
                    if (chain_busy == '0) begin
                        op_ok <= ((chain_done & ~chain_ok) == '0);
                        op_st <= O_FIN;
                    end
                end
                O_CH_READ: begin
                    if (eng_rd_done) begin
                        if (!PROFILE_COMPACT) y_q <= eng_rd_state;
                        op_st <= O_FIN;
                    end
                end
                O_FIELD_REG: begin field_lane <= 0; op_st <= O_FIELD_LOAD; end
                O_FIELD_BEAT: if (stream_fire) begin
                    beat_q <= s_axis_tdata[319:0];
                    field_lane <= 0;
                    op_st <= O_FIELD_LOAD;
                end
                O_FIELD_LOAD: begin
                    if (from_stream) beat_q <= {64'd0,beat_q[319:64]};
                    if (operand >= qsag_ni_pkg::GL_P) err_noncanon <= 1;
                    if (field_input == F_CLAIM) claim_q[field_lane] <= operand;
                    if (field_input == F_EXPECT) expected[field_lane] <= operand;
                    if (is_sc && field_input == F_A) sc_sum[field_lane] <= operand;
                    if (is_sc && field_input == F_C) sc_sum[field_lane] <= field_add(sc_sum[field_lane],operand);
                    if (is_sc && field_input == F_C && coeff_left == 0 &&
                        field_add(sc_sum[field_lane],operand) != field_sub_claim)
                        sc_fail_q <= 1;
                    field_lane <= field_lane + 1'b1;
                    if (field_lane == 4) begin
                        field_lane <= 0;
                        op_st <= from_stream ? O_FIELD_BEAT : O_FIELD_REG;
                        case (field_input)
                            F_CLAIM: op_st <= O_FIN;
                            F_R: begin fold_start <= 1; op_st <= O_FIELD_WAIT; end
                            F_A: begin
                                field_input <= is_sc ? F_C : F_B;
                                if (is_sc) begin
                                    coeff_left <= coeff_left - 1'b1;
                                    field_base <= field_base - 5'd5;
                                end else if (!is_frob) field_base <= 5;
                            end
                            F_B: begin
                                field_input <= is_sc ? F_A : F_C;
                                if (!is_frob) field_base <= is_sc ? 5'd15 : 5'd10;
                            end
                            F_C: begin
                                if (is_batch) field_input <= F_EXPECT;
                                else begin mac_valid <= 1; op_st <= O_FIELD_WAIT; end
                            end
                            F_EXPECT: begin mac_valid <= 1; op_st <= O_FIELD_WAIT; end
                            default: op_st <= O_FIN;
                        endcase
                    end
                end
                O_FIELD_WAIT: begin
                    if (lane_valid) begin
                        if (is_sc && coeff_left == 0) claim_q[lane_idx] <= lane_data;
                        if (is_batch && expected[lane_idx] != lane_data) batch_fail <= 1;
                        if (!PROFILE_COMPACT && field_y_we) y_q[{1'b0,field_y_idx}] <= lane_data;
                    end
                    if (fold_done) begin
                        fold_left <= fold_left - 1'b1;
                        field_base <= field_base + 5'd5;
                        op_st <= fold_left == 1 ? O_FIN : O_FIELD_REG;
                    end else if (mac_done) begin
                        op_st <= O_FIN;
                        if (direct_mac) y_q[4:0] <= wide_result;
                        if (is_sc) begin
                            if (coeff_left == 0) op_ok <= !sc_fail_q;
                            else begin
                                coeff_left <= coeff_left - 1'b1;
                                field_base <= field_base - 5'd5;
                                op_st <= from_stream ? O_FIELD_BEAT : O_FIELD_REG;
                            end
                        end else if (is_batch) begin
                            if (batch_left == 1) op_ok <= !batch_fail && expected[lane_idx] == lane_data;
                            else begin
                                batch_left <= batch_left - 1'b1;
                                field_input <= F_A;
                                op_st <= O_FIELD_BEAT;
                            end
                        end else if (is_frob && frob_lane != 4) begin
                            frob_lane <= frob_lane + 1'b1;
                            field_base <= field_base + 1'b1;
                            field_input <= F_A;
                            op_st <= O_FIELD_REG;
                        end
                    end
                end
                O_KEC: begin
                    if (kec_done) begin
                        if (!PROFILE_COMPACT) y_q <= kec_y_out;
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
                        if (!PROFILE_COMPACT) y_q <= {kcmd_rd_data, y_q[11:1]};
                        if (rd_cnt == 4'd11) op_st <= O_FIN;
                        else                 rd_cnt <= rd_cnt + 4'd1;
                    end
                end
                O_KSP_COLLECT: begin
                    if (stream_fire) begin
                        if (ksp_beat == 2'd0) begin
                            ksp_beat <= 2'd1;
                        end else if (ksp_beat == 2'd1) begin
                            ksp_beat <= 2'd2;
                        end else begin
                            ksp_lane16_q <= s_axis_tdata[63:0];
                            ksp_flags_q  <= s_axis_tdata[127:64];
                            if (!PROFILE_COMPACT) ksp_exp_q <= {s_axis_tdata[127:112], s_axis_tdata[511:128]};
                            else                  ksp_exp_q <= '0;
                            ksp_beat <= 2'd0;
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
                        if (!PROFILE_COMPACT) y_q[7:0] <= kec_y_out[511:0];
                        if (ksp_par_bad) ksp_fail_q <= 1'b1;
                        if (ksp_rem == 16'd1) begin
                            op_ok <= !(ksp_fail_q || ksp_par_bad);
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
                    if (kcmd_ready && kcmp_idx < 5'd8) kcmp_idx <= kcmp_idx + 5'd1;
                    if (kcmd_rd_valid) begin
                        if (ksp_cmp_word_bad) ksp_fail_q <= 1'b1;
                        if (rd_cnt == 4'd7) begin
                            if (ksp_rem == 16'd1) begin
                                op_ok <= !ksp_fail_q;
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
                    if (PROFILE_COMPACT && ts_root_rd_phase && kcmd_rd_valid)
                        rd_cnt <= rd_cnt + 4'd1;
                    if (ts_done) begin
                        if (!PROFILE_COMPACT) y_q[3:0] <= ts_out_root;
                        op_ok <= ts_ok;
                        op_st <= O_FIN;
                    end
                end
                O_GF: begin
                    if (!PROFILE_COMPACT) gf_cnt <= gf_cnt + 3'd1;
                    if (gf_done) begin
                        if (!PROFILE_COMPACT) y_q[1:0] <= gf_r ^ x_b[1:0];
                        op_ok <= ((gf_r ^ x_b[1:0]) == x_b[3:2]);
                        op_st <= O_FIN;
                    end
                end
                O_FIN: begin
                    if (cmd_op_q != 8'h3F && err_noncanon) op_ok <= 1'b0;
                    op_busy <= 1'b0;
                    op_done <= 1'b1;
                    op_st   <= O_IDLE;
                end
                default: op_st <= O_IDLE;
            endcase

            if (PROFILE_COMPACT) begin
                if (y_start_gf) begin
                    gf_high      <= gf_r[127:64] ^ x_b[1];
                    y_wb_cnt     <= 2'd1;
                    y_wb_idx     <= 2'd1;
                end else if (y_wb_cnt != 2'd0) begin
                    y_wb_idx     <= y_wb_idx + 2'd1;
                    y_wb_cnt     <= y_wb_cnt - 2'd1;
                end
            end
        end
    end

    /* verilator lint_off UNUSEDSIGNAL */
    logic unused_top;
    assign unused_top = &{1'b0, s_axil_awaddr[1:0], s_axil_araddr[1:0],
                          stream_q[27:20], cmd_a0_q, cmd_a1_q, ksp_flags_q, gf_high, wide_result, cached_bad, xa_ra, xb_ra, xc_ra,
                          chain_busy, chain_done, chain_ok, kec_y_out, y_q, y_wb_cnt, y_wb_idx,
                          arb_locked, arb_owner, select_eng, p2_out_state, eng_start_ready,
                          eng_start_lane_ready, eng_rd_state, eng_rd_lane_valid, eng_rd_lane_idx,
                          eng_rd_lane_data, eng_job_valid, eng_job_state, eng_job_active,
                          eng_job_lane_valid, eng_job_lane_last, eng_job_lane_data,
                          p2_out_lane_valid, p2_out_lane_idx, p2_out_lane_data,
                          ts_root_rd_phase, ts_out_root, ksp_exp_q};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
