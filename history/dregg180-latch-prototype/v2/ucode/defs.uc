; Dregg-180 v2 microcode: shared definitions.

; error codes (QSAG-Wire; 1, 2, 4 and 14 are also issued by the dispatcher itself)
.equ E_MAGIC        1
.equ E_OPCODE       2
.equ E_LEN          3
.equ E_NOKEY        4
.equ E_MAC          5
.equ E_REUSE        8       ; one-time key already used: leaf below the use counter
.equ E_RECORD_IO    9       ; a lifecycle or helper record did not read back as written
.equ E_TRNG         11      ; the entropy source failed its start-up or health tests
.equ E_AUTH         12      ; a statement did not verify
.equ E_CLASS        13      ; request not allowed by this chip's mode or policy
.equ E_STATE        14      ; command not accepted in this lifecycle state
.equ E_LEASE        15      ; past the bound of this session's lease
.equ E_PUF          16      ; PUF reconstruction did not match the check tag
.equ E_RETIRED      17
.equ E_ARG          18      ; transition arguments refused

; hardwired address ranges (model/isa.py); the image is laid out to match
.equ KEY_END   80           ; key range is 1..79
.equ REC_END   288          ; record range is 80..287

; lifecycle states (model/isa.py LC)
.equ LC_BLANK  1
.equ LC_ORPHAN 2
.equ LC_LEASE  3
.equ LC_READY  4
.equ LC_LOCKED 5

; request opcodes that continuation code compares with
.equ OP_BOOT   0x44
.equ OP_COMMIT 0x46
.equ OP_REINIT 0x47
.equ OP_LEASE  0x48

; transition types
.equ T_LEASE   1
.equ T_EPOCH   2
.equ T_RETIRE  3
.equ T_ROTATE  4

; policy flags, as they sit in bits 55:48 of record word 0 and of the commit word
.equ F_VAT      1
.equ F_LEASED   2
.equ F_COUNTED  4
.equ F_MINTLOCK 8
.equ F_RETIRED  16

; WIPE masks
.equ W_LANES   3        ; lanes 0..24 and the Keccak work rows
.equ W_HI      2        ; lanes 8..24 and the Keccak work rows

; TurboSHAKE256 domain bytes
.equ D_FRAM    0x1F     ; lifecycle record tag
.equ D_REQ     0x21     ; request tag
.equ D_STMT    0x22     ; statement (transition, commit, re-initialisation)
.equ D_KDF     0x23     ; key derived on use from K_dev
.equ D_LEAF    0x24     ; committee leaf
.equ D_NODE    0x25     ; committee node
.equ D_CH      0x26     ; hash chain over chain ends (ARCHITECTURE.md 4.3)
.equ D_PT      0x27     ; fingerprint points
.equ D_NONCE   0x28     ; nonce conditioning
.equ D_PUFCHK  0x29     ; PUF check tag
.equ D_KDEV    0x2A     ; device key

; TRNG flags (model/units.py) and thresholds (ARCHITECTURE.md 6.5), over 256 counts
.equ TF_BAD     0x0F    ; time-out, short count, repetition, proportion
.equ TF_ARMED   0x10
.equ T_PAIRS    28
.equ T_VSEL     1020    ; selection: V >= 2.0, i.e. sum of squared differences >= 2.0 * 510
.equ T_VMIN     638     ; H1: V >= 1.25
.equ T_MEANLO   400
.equ T_MEANHI   3601

; 64-bit constants
.const C_CHIPID "QSAGNI18"
.const C_PAD    0x8000000000000000      ; last byte of the rate
.const C_NODE   0x50324E4400000000      ; Canopy node domain (configuration L)
.const C_LTR    "DREGG.TR"
.const C_LCM    "DREGG.CM"
.const C_LRI    "DREGG.RI"
.const C_LREC   "DREGGREC"
.const C_LHOST  "DREGGKHO"
.const C_LSEED  "DREGGSKS"
.const C_LPRF   "DREGGSKP"
.const C_LPCK   "DREGGPCK"
.const C_LKDV   "DREGGKDV"

; state rows: kept between commands, written only in the record range
.equ REC0    st0        ; seq [31:0] | gen [47:32] | flags [55:48] | threshold k [63:56]
.equ REC1    st1        ; use counter u [31:0] | epoch [63:32]
.equ REC2    st2        ; spend and NFC counters (stage 5)
.equ ROOT0   st3        ; authority: committee root (16 bytes)
.equ ROOT1   st4
.equ TAG0    st5        ; PUF check tag; word 0 is the chip identifier
.equ TAG1    st6
.equ NONCE0  st7        ; session nonce (enrolment, re-initialisation, lease); before boot the enrolment nonce
.equ NONCE1  st8
.equ LEASE   st9        ; bound on u for this power session [31:0]

; scratch rows
.equ S0    t0           ; signer: request word 0, later ADRS bytes 0..7. Verifier: ADRS bytes 0..7 (layer)
.equ PK0   t1           ; PK.seed
.equ PK1   t2
.equ TREE  t3           ; ADRS bytes 8..15
.equ KP    t4           ; ADRS bytes 16..23 with the type field cleared
.equ MW0   t5           ; signer: message / leaf-index words. Verifier: digit queue
.equ MW1   t6
.equ MW2   t7
.equ MW3   t8
.equ CNT   t8           ; gate: members still to come [63:32] | lowest index allowed next [31:0]
.equ A0    t9           ; work
.equ A1    t10
.equ TMP   t11
.equ NODE0 t12          ; verifier: current node / message of the next layer
.equ NODE1 t13
.equ FR0   t14          ; fingerprint points
.equ FR1   t15
.equ FA0   t16          ; fingerprint accumulators
.equ FA1   t17
.equ FD0   t18          ; hash chain over the computed values; then the accumulators of pass 2a
.equ FD1   t19
.equ ARG0  t20          ; statement arguments
.equ ARG1  t21
.equ ARG2  t22
.equ ARG3  t23          ; current member: index [31:0] | path length [63:32]
