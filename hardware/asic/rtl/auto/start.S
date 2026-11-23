.section .text.start,"ax"
.global _start
_start:
    # a0 proof pointer, a1 length, a2 descriptor, a3 SRAM size.
    # Validate the descriptor interval before the first stack store.
    lwu t0, 0(a2)
    li t1, 16
    bltu t0,t1, .Lbad
    add t0,t0,a2
    bgtu t0,a3,.Lbad
    add t1,a5,a4
    bgtu t1,a3,.Lbad
    bleu t0,a5,.Lordered
    bgtu t1,a2,.Lbad
.Lordered:
    bgeu t0,t1,.Lguard
    mv t0,t1
.Lguard:
    .insn r 0x0b,0,1,x0,t0,x0
    mv sp,a3
    call verify
    .insn r 0x0b,0,0,x0,a0,x0
.Lbad:
    .insn r 0x0b,0,0,x0,x0,x0
