// Preserve each mapped LUT truth table as one Yosys combinational cell.
// Expanding LUT6 to a tree of 63 muxes wastes memory during graph analysis.
module LUT1 #(parameter [1:0] INIT = 0) (input I0, output O);
  \$lut #(.WIDTH(1), .LUT(INIT)) table_cell (.A({I0}), .Y(O));
endmodule
module LUT2 #(parameter [3:0] INIT = 0) (input I0, I1, output O);
  \$lut #(.WIDTH(2), .LUT(INIT)) table_cell (.A({I1, I0}), .Y(O));
endmodule
module LUT3 #(parameter [7:0] INIT = 0) (input I0, I1, I2, output O);
  \$lut #(.WIDTH(3), .LUT(INIT)) table_cell (.A({I2, I1, I0}), .Y(O));
endmodule
module LUT4 #(parameter [15:0] INIT = 0) (input I0, I1, I2, I3, output O);
  \$lut #(.WIDTH(4), .LUT(INIT)) table_cell (.A({I3, I2, I1, I0}), .Y(O));
endmodule
module LUT5 #(parameter [31:0] INIT = 0) (input I0, I1, I2, I3, I4, output O);
  \$lut #(.WIDTH(5), .LUT(INIT)) table_cell (.A({I4, I3, I2, I1, I0}), .Y(O));
endmodule
module LUT6 #(parameter [63:0] INIT = 0) (input I0, I1, I2, I3, I4, I5, output O);
  \$lut #(.WIDTH(6), .LUT(INIT)) table_cell (.A({I5, I4, I3, I2, I1, I0}), .Y(O));
endmodule
