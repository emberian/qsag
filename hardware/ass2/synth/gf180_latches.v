// Map the transparent latch inferred by the asynchronous tamper flag.
module \$_DLATCH_P_ (input D, E, output Q);
    gf180mcu_fd_sc_mcu7t5v0__latq_1 _TECHMAP_REPLACE_ (.D(D), .E(E), .Q(Q));
endmodule
module \$_DLATCH_N_ (input D, E, output Q);
    gf180mcu_fd_sc_mcu7t5v0__latq_1 _TECHMAP_REPLACE_ (.D(D), .E(~E), .Q(Q));
endmodule
