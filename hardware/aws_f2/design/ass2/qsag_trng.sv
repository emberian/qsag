// One held word per vat. An unpublished generation is never consumed twice.
module qsag_trng (
    input wire clk, rst_n, en, take,
    input wire [63:0] cloud_word,
    input wire cloud_epoch, cloud_ok, cloud_rct, cloud_apt,
    output logic [63:0] word,
    output logic valid,
    output wire ok, rct_fail, apt_fail, raw_bit
);
    logic seen;
    assign {ok,rct_fail,apt_fail} = {cloud_ok,cloud_rct,cloud_apt};
    assign raw_bit = word[0];
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin word <= 0; valid <= 0; seen <= 0; end
        else if (!ok) begin word <= 0; valid <= 0; seen <= cloud_epoch; end
        else if (en) begin
            if (take) valid <= 0;
            if (seen != cloud_epoch) begin
                seen <= cloud_epoch;
                if (!valid || take) begin word <= cloud_word; valid <= 1; end
            end
        end
    end
endmodule
