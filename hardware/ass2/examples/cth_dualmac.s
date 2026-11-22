; Cut-the-Hash dual-MAC check over GF(2^128) = F_2[x]/(x^128 + x^7 + x^2 + x + 1).
; Every value z_k carries a second ("dual") copy m_k = r * z_k under the MAC key r.  With public
; coefficients a_k the batch is accepted iff
;   T = sum_k a_k * m_k  +  r * sum_k a_k * z_k  ==  0.
; In : P0 = r (S[0..1], secret, loaded by the caller)
;      A0 -> n records { a_k, z_k, m_k }, 2 words each, low word first (48 bytes a record)
;      A1 =  n (public, >= 1)
; Out: A0 = 1 if T == 0, else 0.  No branch, address or cycle count depends on r, z_k or m_k.
; Cycles: 13 + 25 n.
cth_dualmac:
    GF128.XOR P4, P4, P4        ; w <- 0   (S[8..9])
    GF128.XOR P5, P5, P5        ; u <- 0   (S[10..11])
mac_loop:
    SLD64   S[2], [A0+0]        ; P1 <- a_k
    SLD64   S[3], [A0+8]
    SLD64   S[4], [A0+16]       ; P2 <- z_k
    SLD64   S[5], [A0+24]
    SLD64   S[6], [A0+32]       ; P3 <- m_k
    SLD64   S[7], [A0+40]
    GF128.MUL P2, P1, P2        ; a_k * z_k               4 cycles
    GF128.MUL P3, P1, P3        ; a_k * m_k               4 cycles
    GF128.XOR P4, P4, P2        ; w <- w + a_k * z_k
    GF128.XOR P5, P5, P3        ; u <- u + a_k * m_k
    ADDI    A0, A0, 48
    ADDI    A1, A1, -1
    BNEZ    A1, mac_loop        ; the record count is public
    GF128.MUL P4, P0, P4        ; r * w
    GF128.XOR P5, P5, P4        ; T <- u + r * w
    SGET    A1, S[10]
    SGET    A2, S[11]
    OR      A1, A1, A2          ; T == 0  <=>  (T.lo | T.hi) == 0
    CMP     A0, A1, ZERO, EQ    ; verdict as a 0/1 word, never as a branch
    SZERO                       ; scrub r, w, u
    RET
