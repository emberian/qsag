; Dregg-180 v2 microcode: shared definitions.

; error codes (QSAG-Wire; 1, 2, 4 and 10 are also issued by the dispatcher itself)
.equ E_MAGIC        1
.equ E_OPCODE       2
.equ E_LEN          3
.equ E_NOKEY        4
.equ E_MAC          5
.equ E_ANCHOR_EMPTY 6
.equ E_ROLLBACK     7
.equ E_REUSE        8
.equ E_ANCHOR_IO    9
.equ E_KEYSET       10
.equ E_TRNG         11
.equ E_AUTH         12      ; provisioning not authorised by the owner root
.equ E_CLASS        13      ; request not allowed for this key's class (counted / uncounted)

; hardwired address ranges (model/isa.py); the image is laid out to match
.equ KEY_END   64           ; provisioning range is 1..63
.equ REC_END   128          ; record range is 64..127

; WIPE masks
.equ W_LANES   3        ; lanes 0..24 and the Keccak work rows
.equ W_HI      2        ; lanes 8..24 and the Keccak work rows

; TurboSHAKE256 domain bytes
.equ D_FRAM    0x1F     ; anchor record tag
.equ D_REQ     0x21     ; request tag
.equ D_PROV    0x22     ; provisioning statement

; key attribute bits (stored with the key by CTL SETKV)
.equ KA_COUNTED 1       ; WOTS signing with this key always goes through the anchor counter

; 64-bit constants
.const C_CHIPID "QSAGNI18"
.const C_PAD    0x8000000000000000      ; last byte of the rate
.const C_FRAM   "QSAGNIFR"
.const C_NODE   0x50324E4400000000      ; Canopy node domain (configuration L)

; state rows
.equ ST_HWM  st0        ; high-water mark of the anchor counter | valid << 32 (volatile)

; scratch rows of the signer
.equ S0    t0           ; request word 0: leaf counter | layer << 32; later ADRS bytes 0..7
.equ PK0   t1           ; PK.seed
.equ PK1   t2
.equ TREE  t3           ; ADRS bytes 8..15
.equ KP    t4           ; ADRS bytes 16..23 with the type field cleared
.equ MW0   t5           ; message / leaf-index words
.equ MW1   t6
.equ MW2   t7
.equ MW3   t8
.equ A0    t9           ; anchor record counter: the one scratch row FRAM WWORD may send
.equ A1    t10
.equ TMP   t11
