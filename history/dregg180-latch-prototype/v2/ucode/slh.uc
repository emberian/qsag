; SLH-DSA-SHAKE (n = 16) signature verification, public computation (ARCHITECTURE.md 4.3).
;
; sv: in   lanes 0..3 = the 32-byte message; PK0, PK1 = PK.seed; NODE0, NODE1 = PK.root as the host
;          states it (the caller has checked the stated key against its pin);
;          payload = the package: R; per FORS tree the secret value and a values of path; the k roots
;          twice; per layer 35 signature values, the 35 chain ends twice, hp values of path.
;     out  NODE0, NODE1 = the root the signature leads to (the caller checks it against its pin);
;          Z is set if a stated value was not the computed one. Z is never cleared here.
; Scratch: S0, TREE, KP (ADRS), MW0..MW2 (digest, digit queue), A0, A1, TMP, FR, FA, FD. X, C0, C1.
sv:         WIPE #W_HI
            LD   l2 > l8             ; H_msg = SHAKE256(R || PK.seed || PK.root || M)[0..29]
            LD   l3 > l9
            LD   l0 > l6
            LD   l1 > l7
            DIN  > l0
            DIN  > l1
            LD   PK0 > l2
            LD   PK1 > l3
            LD   NODE0 > l4
            LD   NODE1 > l5
            LD   #0x1F
            ST   l10
            LDC  C_PAD
            ST   l16
            KEC  24
            LD   l0                  ; digest bytes 0..20: the FORS indices, as a queue of nibbles
            UN   NIB > MW0
            LD   l1
            UN   NIB > MW1
            LD   l2
            UN   NIB > MW2
            LD   l2                  ; bytes 21..27, big-endian: the tree index, kept as ADRS bytes 8..15
            UN   SHR16
            UN   SHR16
            UN   SHR8
            UN   SHL8 > TREE
            LD   l3
            UN   LO32
            UN   HSWAP
            OR   TREE > TREE
            LDC  C_TREEM
            AND  TREE > TREE
            LD   l3                  ; bytes 28, 29, big-endian: the leaf index, kept as ADRS bytes 20..23
            UN   HSWAP
            AND  #0xFFFF
            UN   BE32
            UN   SHR16
            AND  #SLH_LEAFM
            UN   BE32
            UN   HSWAP > KP
            LD   #0
            ST   S0                  ; layer 0

; --- FORS: k trees of height a. Pass 1: each root from its secret value and path.
            LD   #3                  ; FORS_TREE
            UN   BE32
            XOR  KP
            ST   NODE0
            LD   #0
            ST   FD0
            ST   FD1
            SETX #0
            SETC 0 #SLH_K
sv_ftree:   LD   #0
            ST   A0
            SETC 1 #SLH_ANIB
sv_fnib:    LD   A0                  ; the next a bits of the digest, most significant first
            UN   SHL4 > A0
            CALL md_nib
            OR   A0 > A0
            DBNZ 1 sv_fnib
            LDF  X                   ; index of the leaf among all leaves: tree * 2^a + index
            SETC 1 #SLH_ANIB
sv_fsh:     UN   SHL4
            DBNZ 1 sv_fsh
            OR   A0 > A0
            WIPE #W_LANES
            DIN  > l6
            DIN  > l7
            LD   NODE0 > l4
            LD   A0
            UN   BE32
            UN   HSWAP > l5
            CALL ctx_kec
            LD   #0
            ST   TMP
            SETC 1 #SLH_A
sv_flev:    CALL path_level
            DBNZ 1 sv_flev
            CALL dchain
            INCX
            DBNZ 0 sv_ftree
            LD   #4                  ; FORS_ROOTS
            UN   BE32
            XOR  KP
            ST   NODE0
            LD   #SLH_K
            CALL stated              ; lanes 0, 1 = the FORS public key

; --- hypertree: d layers. The node in lanes 0, 1 is the message of the layer.
sv_layer:   LD   l0
            UN   NIB > MW0
            LD   l1
            UN   NIB > MW1
            LD   #0
            ST   MW2
            ST   FD0
            ST   FD1
            SETX #0
            SETC 0 #35
sv_chain:   CALL next_digit          ; pass 1: chain X from its digit to the end
            WIPE #W_LANES
            DIN  > l0
            DIN  > l1
            LD   A1 > TMP
            LD   #15
            SUB  A1
            BR   HZ sv_cend
            SETC 1 H
sv_cstep:   CALL wots_fstep
            DBNZ 1 sv_cstep
sv_cend:    CALL dchain
            INCX
            DBNZ 0 sv_chain
            LD   #1                  ; WOTS_PK
            UN   BE32
            XOR  KP
            ST   NODE0
            LD   #35
            CALL stated              ; lanes 0, 1 = the WOTS public key, a leaf of this layer's tree
            LD   #2                  ; TREE
            UN   BE32
            ST   NODE0
            LD   KP
            UN   HSWAP
            UN   BE32
            ST   A0
            LD   #0
            ST   TMP
            SETC 1 #SLH_HP
sv_xlev:    CALL path_level
            DBNZ 1 sv_xlev
            LD   S0                  ; next layer
            UN   BE32
            ADD  #1
            ST   A1
            XOR  #SLH_D
            BR   HZ sv_done
            LD   A1
            UN   BE32 > S0
            LD   TREE                ; the low bits of the tree index are the leaf of the next layer
            UN   BE32
            UN   HSWAP
            ST   A0
            AND  #SLH_LEAFM
            UN   BE32
            UN   HSWAP > KP
            LD   A0
            SETC 1 #SLH_HP
sv_tsh:     UN   SHR1
            DBNZ 1 sv_tsh
            UN   BE32
            UN   HSWAP > TREE
            BR   sv_layer
sv_done:    LD   l0 > NODE0
            LD   l1 > NODE1 ret

; md_nib: H <- the next nibble of the 42-nibble digest queue MW0..MW2.
md_nib:     LD   MW1
            AND  #15
            CALL shl60
            ST   A1
            LD   MW0
            AND  #15
            ST   TMP
            LD   MW0
            UN   SHR4
            OR   A1 > MW0
            LD   MW2
            AND  #15
            CALL shl60
            ST   A1
            LD   MW1
            UN   SHR4
            OR   A1 > MW1
            LD   MW2
            UN   SHR4 > MW2
            LD   TMP ret
shl60:      UN   SHL4
            UN   SHL8
            UN   SHL8
            UN   SHL8
            UN   SHL8
            UN   SHL8
            UN   SHL8
            UN   SHL8 ret

; path_level: one level of a Merkle path. Node in lanes 0, 1; A0 = its index at this height; TMP = the
; height; NODE0 = ADRS bytes 16..23 (type, key pair); the sibling is the next payload value.
path_level: WIPE #W_HI
            LD   A0
            AND  #1
            BR   HNZ pl_right
            LD   l0 > l6
            LD   l1 > l7
            DIN  > l8
            DIN  > l9
            BR   pl_go
pl_right:   LD   l0 > l8
            LD   l1 > l9
            DIN  > l6
            DIN  > l7
pl_go:      LD   A0
            UN   SHR1 > A0
            UN   BE32
            UN   HSWAP > l5
            LD   TMP
            ADD  #1
            ST   TMP
            UN   BE32
            XOR  l5 > l5
            LD   NODE0 > l4
            BR   h_step

; dchain: extend the hash chain FD over the value in lanes 0, 1:
;   FD <- TurboSHAKE256(FD || value, D = 0x26)[0..15].
dchain:     LD   l0 > l2
            LD   l1 > l3
            LD   FD0 > l0
            LD   FD1 > l1
            LD   #D_CH
            CALL dom_kec
            LD   l0 > FD0
            LD   l1 > FD1 ret

; stated: the passes over values the host states. H = their number; NODE0 = ADRS bytes 16..23 of the
; hash T that absorbs them; FD = the hash chain over the values the chip computed.
;   points  FR = TurboSHAKE256(FD, D = 0x27)[0..15]: fixed only after every computed value is
;   pass 2a the stated values, hashed into a chain that must end in FD, and folded into FA
;   pass 2b the stated values again, absorbed into T and folded; the two folds must agree
; Out: lanes 0, 1 = T(PK.seed, ADRS, values). Z collects the two comparisons.
stated:     ST   NODE1
            WIPE #W_LANES
            LD   FD0 > l0
            LD   FD1 > l1
            LD   #D_PT
            ST   l2
            LDC  C_PAD
            ST   l16
            KEC  12
            LD   l0 > FR0
            LD   l1 > FR1
            LD   #0
            ST   FA0
            ST   FA1
            WIPE #W_LANES
            LD   NODE1
            SETC 0 H
st_a:       DIN  > l2
            CALL fold_w
            DIN  > l3
            CALL fold_w
            LD   #D_CH
            CALL dom_kec
            DBNZ 0 st_a
            LD   FD0
            CMP  l0
            LD   FD1
            CMP  l1
            LD   FA0 > FD0
            LD   FA1 > FD1
            LD   #0
            ST   FA0
            ST   FA1
            WIPE #W_LANES
            LD   PK0 > l0
            LD   PK1 > l1
            LD   S0 > l2
            LD   TREE > l3
            LD   NODE0 > l4
            SETX #6
            LD   NODE1
            SETC 0 H
st_b:       DIN
            CALL fold_w
            LD   A0
            XOR  l0+X > l0+X x+
            BXNE #17 st_b1
            KEC  24
            SETX #0
st_b1:      DIN
            CALL fold_w
            LD   A0
            XOR  l0+X > l0+X x+
            BXNE #17 st_b2
            KEC  24
            SETX #0
st_b2:      DBNZ 0 st_b
            LD   #0x1F
            XOR  l0+X > l0+X
            LDC  C_PAD
            XOR  l16 > l16
            KEC  24
            LD   FA0
            CMP  FD0
            LD   FA1
            CMP  FD1 ret

; fold_w: FA_j <- (FA_j xor w) * FR_j in GF(2^64) for j = 0, 1; w in H, left in A0.
; The product is shift-and-xor over the bits of the point, most significant first. Uses A1, TMP, C1.
fold_w:     ST   A0
            XOR  FA0 > FA0
            LD   FR0 > A1
            LD   #0
            ST   TMP
            SETC 1 #64
fw_0:       LD   A1
            UN   SHL1C > A1
            LD   TMP
            UN   XT > TMP
            BR   NC fw_0n
            XOR  FA0 > TMP
fw_0n:      DBNZ 1 fw_0
            LD   TMP > FA0
            LD   A0
            XOR  FA1 > FA1
            LD   FR1 > A1
            LD   #0
            ST   TMP
            SETC 1 #64
fw_1:       LD   A1
            UN   SHL1C > A1
            LD   TMP
            UN   XT > TMP
            BR   NC fw_1n
            XOR  FA1 > TMP
fw_1n:      DBNZ 1 fw_1
            LD   TMP > FA1 ret
