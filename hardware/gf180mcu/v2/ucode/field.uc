; Configuration L: Poseidon2 (0x10) and Canopy Merkle path (0x11) on the field unit.
.entry 0x10 p2 diag
.entry 0x11 merkle diag

; ---------------------------------------------------------------------------------------------
; P2, flags bit 0 = 1: raw permutation of 12 words (reduced mod p). Else: sponge hash,
;   payload domain, cap[4], limbs[n]; frame [domain, n] ++ limbs, rate 8; result 4 words.
p2:         LDF  FLAGS
            AND  #1
            BR   HZ p2_hash
            LDF  LEN
            XOR  #96
            BR   HNZ e_len
            SETX #0
p2r_in:     DIN
            FLD  RED > l0+X x+
            BXNE #12 p2r_in
            FLD  PERM
            LD   #12
            HDR  #12
            SETX #0
p2r_out:    PUSH l0+X x+
            BXNE #12 p2r_out
            END
p2_hash:    LDF  LEN
            AND  #7
            BR   HNZ e_len
            LDF  NWORDS
            SUB  #5
            BR   CY e_len
            DIN
            FLD  RED > l0
            SETX #8
p2h_cap:    DIN
            FLD  RED > l0+X x+
            BXNE #12 p2h_cap
            LDF  NWORDS
            ST   l1
            SETX #2
p2h_loop:   BR   NOMORE p2h_fin
            DIN
            FLD  RED
            FADD l0+X > l0+X x+
            BXNE #8 p2h_loop
            FLD  PERM
            SETX #0
            BR   MORE p2h_loop
            BR   p2h_out
p2h_fin:    FLD  PERM
p2h_out:    LD   #4
            HDR  #4
            PUSH l0
            PUSH l1
            PUSH l2
            PUSH l3
            END

; ---------------------------------------------------------------------------------------------
; MERKLE: arg [7:0] = depth 1..62; payload key[3], leaf index, leaf[4], depth x sibling[4], root[4].
;   Response: ok word and the computed root; header ok flag and VERIFY_OK = (computed == root mod p).
.equ MC0   l12          ; node constants: domain | parent index, key[3]
.equ MKEY  l13
.equ MCUR  l16          ; current node
.equ MSIB  l20          ; sibling
.equ MIDX  l24          ; heap index of the current node

merkle:     LDF  ARGLO
            BR   HZ e_len
            SUB  #63
            BR   NC e_len
            LDF  ARGLO              ; payload is 12 + 4 depth words
            ST   t0
            ADD  t0
            ST   t0
            ADD  t0
            ADD  #12
            ST   t0
            LDF  NWORDS
            XOR  t0
            BR   HNZ e_len
            LDF  LEN
            AND  #7
            BR   HNZ e_len
            SETX #0
mk_key:     DIN
            FLD  RED > MKEY+X x+
            BXNE #3 mk_key
            LDF  ARGLO
            SETC 0 H
            LD   #1
mk_sh:      UN   SHL1
            DBNZ 0 mk_sh
            ST   MIDX
            DIN
            OR   MIDX > MIDX        ; 2^depth | leaf index
            SETX #0
mk_leaf:    DIN
            FLD  RED > MCUR+X x+
            BXNE #4 mk_leaf
            LDF  ARGLO
            SETC 0 H
mk_level:   SETX #0
mk_sib:     DIN
            FLD  RED > MSIB+X x+
            BXNE #4 mk_sib
            LD   MIDX
            AND  #1
            ST   t1                 ; 1: the current node is the right child
            LD   MIDX
            UN   SHR1 > MIDX        ; parent
            UN   LO32
            ST   t0
            LDC  C_NODE
            OR   t0
            FLD  RED > MC0
            SETX #0
mk_c:       LD   MC0+X
            ST   l8+X x+
            BXNE #4 mk_c
            SETX #0
            LD   t1
            BR   HNZ mk_r
mk_l:       LD   MCUR+X             ; left = current, right = sibling
            ST   l0+X
            LD   MSIB+X
            ST   l4+X x+
            BXNE #4 mk_l
            FLD  PERM
            SETX #0
mk_lf:      LD   l0+X               ; out = state + left + 2 right + 4 constants
            FADD MCUR+X
            FADD MSIB+X
            FADD MSIB+X
            FADD MC0+X
            FADD MC0+X
            FADD MC0+X
            FADD MC0+X > MCUR+X x+
            BXNE #4 mk_lf
            BR   mk_next
mk_r:       LD   MSIB+X             ; left = sibling, right = current
            ST   l0+X
            LD   MCUR+X
            ST   l4+X x+
            BXNE #4 mk_r
            FLD  PERM
            SETX #0
mk_rf:      LD   l0+X
            FADD MSIB+X
            FADD MCUR+X
            FADD MCUR+X
            FADD MC0+X
            FADD MC0+X
            FADD MC0+X
            FADD MC0+X > MCUR+X x+
            BXNE #4 mk_rf
mk_next:    DBNZ 0 mk_level
            SETX #0
mk_root:    DIN
            FLD  RED
            CMP  MCUR+X x+
            BXNE #4 mk_root
            CTL  VOK
            LD   #5
            HDR  #5 okz
            BR   Z mk_no
            LD   #1
            BR   mk_out
mk_no:      LD   #0
mk_out:     PUSH H
            PUSH l16
            PUSH l17
            PUSH l18
            PUSH l19
            END
