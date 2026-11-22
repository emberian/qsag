; zk-Hem v2 challenge-field Horner evaluation over F_p[u]/(u^5 - 3).
;   acc = c[d];  for i = d-1 .. 0:  acc = acc * r + c[i]
; In : A0 -> c[d], the top coefficient. Coefficients are stored ascending, 5 limbs (40 bytes) each.
;      A1 =  d, the degree (public, >= 0)
;      E1 =  r, the evaluation point (S[5..9], loaded by the caller)
; Out: E0 =  p(r) (S[0..4], canonical limbs).  Clobbers E2, A0, A1.
; Cycles: 12 + 122 d.
fp5_horner:
    SLD64   S[0], [A0+0]        ; E0 <- c[d]
    SLD64   S[1], [A0+8]
    SLD64   S[2], [A0+16]
    SLD64   S[3], [A0+24]
    SLD64   S[4], [A0+32]
    BEQZ    A1, horner_done     ; degree zero returns the leading coefficient
horner_step:
    ADDI    A0, A0, -40         ; step down to c[i]
    SLD64   S[10], [A0+0]       ; E2 <- c[i]
    SLD64   S[11], [A0+8]
    SLD64   S[12], [A0+16]
    SLD64   S[13], [A0+24]
    SLD64   S[14], [A0+32]
    FP5.MUL E0, E0, E1          ; acc <- acc * r        104 cycles, in place
    FP5.ADD E0, E0, E2          ; acc <- acc + c[i]       5 cycles
    ADDI    A1, A1, -1
    BNEZ    A1, horner_step     ; the loop count is public
horner_done:
    RET
