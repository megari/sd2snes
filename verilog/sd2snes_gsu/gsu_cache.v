`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: N/A
// Engineer: Ari Sundholm <megari@iki.fi>
//
// Create Date:    02:43:51 07/14/2017
// Design Name:
// Module Name:    gsu_cache
// Project Name:
// Target Devices:
// Tool versions:
// Description:
//
// Dependencies:
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////
module gsu_cache(
  output reg [7:0] douta,
  input [7:0] dina,
  input [8:0] addra,
  input wea,

  output reg [7:0] doutb,
  input [8:0] addrb,

  input clk
);

reg [7:0] mem [511:0];

always @(posedge clk) begin
  douta <= mem[addra];
  if (wea) begin
    douta <= dina;
    mem[addra] <= dina;
  end
end

always @(posedge clk) begin
  doutb <= mem[addrb];
end

endmodule
