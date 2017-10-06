`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: N/A
// Engineer: Ari Sundholm <megari@iki.fi>
// 
// Create Date:    23:24:07 02/01/2015 
// Design Name: 
// Module Name:    gsu 
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
module gsu(
	input clkin,
	input [7:0] DI,
	output [7:0] DO,
	input [23:0] ADDR,
	input CS,
	input reg_we_rising
);

reg [2:0] clk_counter;
reg clk;

reg [15:0] regs [0:13]; // General purpose registers R0~R13
reg [15:0] rap;         // Game Pak ROM address pointer: R14
reg [15:0] pc;          // Program counter: R15

// Status/flag register flags
reg z;    // Zero
reg cy;   // Carry
reg s;    // Sign
reg ov;   // Overflow
reg g;    // Go
reg r;    // Reading ROM using R14
reg alt1; // Mode flag for next insn
reg alt2; // Mode flag for next insn
reg il;   // Immediate lower
reg ih;   // Immediate higher
reg b;    // Instruction executed with WITH
reg irq;  // Interrupt

reg [7:0] pbr;   // Program bank register
reg [7:0] rombr; // Game Pak ROM bank register
reg rambr;       // Game Pak RAM bank register
reg [15:0] cbr;  // Cache base register. [3:0] are always 0.
                 // TODO: why not make the register only 12 bits wide?
reg [7:0] scbr;  // Screen base register
reg [5:0] scmr;  // Screen mode register
reg [7:0] colr;  // Color register
reg [4:0] por;   // Plot option register
reg bramr;       // Back-up RAM register
reg [7:0] vcr;   // Version code register
reg [7:0] cfgr;  // Config register
reg clsr;        // Clock select register

reg [7:0] curr_insn [0:2];
reg [1:0] insn_idx;
reg [1:0] fetches_left;
reg [7:0] pipeline;

reg [3:0] imm;
reg [3:0] src_reg;
reg [3:0] dst_reg;

reg [7:0] cache [511:0];

reg [8:0] cache_addra;
reg [7:0] cache_dina;
reg [0:0] cache_wea;
wire [7:0] cache_douta;

reg fetch_cached_insn;

reg[0:0] state;
/*
parameter STATE_FETCHNLOAD = 2'b01;
parameter STATE_EXEC       = 2'b10;
*/
parameter STATE_BEGIN = 1'b0;
parameter STATE_FETCH = 1'b1; // This is somewhat misleadingly named.

parameter OP_ALT1 = 8'b00111101;
parameter OP_ALT2 = 8'b00111110;
parameter OP_ALT3 = 8'b00111111;
parameter OP_ADX  = 8'b0101zzzz;
parameter OP_BEQ  = 8'b00001001;
parameter OP_NOP  = 8'b00000001;

initial begin: initial_blk
	reg[1:0] i;
	clk = 1'b0;
	clk_counter = 3'h0;
	insn_idx = 2'b00;

	for (i = 0; i < 2'h3; i = i+1) begin
		curr_insn[i] = OP_NOP;
	end
	fetches_left = 2'b00;
	state = STATE_BEGIN;
end

always @(posedge clkin) begin
	if (clk_counter == 3'h0) begin
		clk = !clk;
	end
	clk_counter = clk_counter + 3'h1;

	// The upper limit depends on the frequency desired.
	if ((clsr == 1'b0 && clk_counter >= 3'h2) ||
	    (clsr == 1'b1 && clk_counter == 3'h4)) begin
		clk_counter = 3'h0;
	end
end

always @(posedge clk) begin
	if (fetch_cached_insn) begin
		pipeline = cache_douta;
	end
end

always @(posedge clk) begin // Should probably use clock in divided by 4 or 8

	// First, copy instruction from cache
	// TODO: reading from RAM & ROM
	curr_insn[insn_idx] = cache_douta;
	fetches_left = fetches_left - 2'b01;

	// If we are beginning a new instruction, determine the number of fetches needed.
	if (state == STATE_BEGIN) begin

		casez (curr_insn[insn_idx])
			OP_NOP:
			begin
				fetches_left = 2'b00;
			end
			OP_ADX:
			begin
				if (!alt1 && !alt2) begin
					// ADD Rn
					fetches_left = 2'b00;
				end
				else begin
					// ADC Rn
					// ADD #n
					// ADC #n
					fetches_left = 2'b01;
				end
			end
			OP_BEQ:
			begin
				fetches_left = 2'b01;
			end
		endcase
		state = STATE_FETCH;
	end

	// Fetch phase. This is always done.
	if (state == STATE_FETCH) begin
		// Start fetching next instruction from cache.
		// It will be ready next cycle.
		cache_addra = pc - cbr;
	end

`define NONE 1
`ifdef NONE
	// Exec phase. This is only done once the instruction's been read in full.
	if (fetches_left == 2'b00) begin
		//imm = curr_insn[insn_idx][3:0]; // Causes internal error in the compiler!?
		imm = curr_insn[insn_idx] & 8'h0f;

		casez (curr_insn[0])
			OP_NOP:
			begin
				// Just reset regs.
				b    = 1'b0;
				alt1 = 1'b0;
				alt2 = 1'b0;
				src_reg = 3'h0;
				dst_reg = 3'h0;
			end
`define NONE2 1
`ifdef NONE2
			OP_ADX:
			begin: op_adx_blk
				reg [16:0] tmp;

				if (!alt1 && !alt2) begin
					// ADD Rn
					tmp = regs[src_reg] + regs[imm];
				end
				else if (alt1 && !alt2) begin
					// ADC Rn
					tmp = regs[src_reg] + regs[imm] + cy;
				end
				else if (!alt1 && alt2) begin
					// ADD #n
					tmp = regs[src_reg] + imm;
				end
				else /* if (alt1 && alt2) */ begin
					// ADC #n
					tmp = regs[src_reg] + imm + cy;
				end

				// Set flags
				ov  <= (~(regs[src_reg] ^ regs[imm])
							& (regs[imm] ^ tmp)
							& 16'h8000) != 0;
				s   <= (tmp & 16'h8000) != 0;
				cy  <= tmp >= 17'h10000;
				z   <= (tmp & 16'hffff) == 0;

				// Set result
				regs[dst_reg] = tmp;

				// Register reset
				b    = 1'b0;
				alt1 = 1'b0;
				alt2 = 1'b0;
				src_reg = 3'h0;
				dst_reg = 3'h0;
			end
			OP_BEQ:
			begin: op_beq_blk
				reg signed [7:0] tmp;
				tmp = pipeline;
				pc = pc + 1'b1;
				//pipeline = 8'b1; // XXX: NOP for now. Should read.
				//fetch_next_cached_insn;
				if (z) begin
					// XXX this is ugly!
					pc = $unsigned($signed(pc) + tmp);
				end
			end
`endif
		endcase

		state = STATE_BEGIN;
		insn_idx = 2'b00;
	end
`endif
end

wire mmio_enable = CS & !ADDR[22] & (ADDR[15:12] == 4'b0011) & (ADDR[15:0] < 16'h3300);
wire MMIO_WR_EN = mmio_enable & reg_we_rising;

reg  [7:0] MMIO_DOr;
wire [7:0] MMIO_DO;
assign MMIO_DO = MMIO_DOr;

assign DO = mmio_enable ? MMIO_DO
            : 8'h00;

always @(posedge clkin) begin
	casex (ADDR[9:0])
		10'h000: MMIO_DOr <= regs[0][7:0];
		10'h001: MMIO_DOr <= regs[0][15:8];
		10'h002: MMIO_DOr <= regs[1][7:0];
		10'h003: MMIO_DOr <= regs[1][15:8];
		10'h004: MMIO_DOr <= regs[2][7:0];
		10'h005: MMIO_DOr <= regs[2][15:8];
		10'h006: MMIO_DOr <= regs[3][7:0];
		10'h007: MMIO_DOr <= regs[3][15:8];
		10'h008: MMIO_DOr <= regs[4][7:0];
		10'h009: MMIO_DOr <= regs[4][15:8];
		10'h00a: MMIO_DOr <= regs[5][7:0];
		10'h00b: MMIO_DOr <= regs[5][15:8];
		10'h00c: MMIO_DOr <= regs[6][7:0];
		10'h00d: MMIO_DOr <= regs[6][15:8];
		10'h00e: MMIO_DOr <= regs[7][7:0];
		10'h00f: MMIO_DOr <= regs[7][15:8];
		10'h010: MMIO_DOr <= regs[8][7:0];
		10'h011: MMIO_DOr <= regs[8][15:8];
		10'h012: MMIO_DOr <= regs[9][7:0];
		10'h013: MMIO_DOr <= regs[9][15:8];
		10'h014: MMIO_DOr <= regs[10][7:0];
		10'h015: MMIO_DOr <= regs[10][15:8];
		10'h016: MMIO_DOr <= regs[11][7:0];
		10'h017: MMIO_DOr <= regs[11][15:8];
		10'h018: MMIO_DOr <= regs[12][7:0];
		10'h019: MMIO_DOr <= regs[12][15:8];
		10'h01a: MMIO_DOr <= regs[13][7:0];
		10'h01b: MMIO_DOr <= regs[13][15:8];
		10'h01c: MMIO_DOr <= rap[7:0];
		10'h01d: MMIO_DOr <= rap[15:8];
		10'h01e: MMIO_DOr <= pc[7:0];
		10'h01f: MMIO_DOr <= pc[15:8];

		// Status flag register
		10'h030: MMIO_DOr <= {irq, 1'b0, 1'b0, b, ih, il, alt2, alt1};
		10'h031: MMIO_DOr <= {1'b0, r, g, ov, s, cy, z, 1'b0};

		//10'h032: Unused

		// Back-up RAM register: write only
		//10'h033: MMIO_DOr <= {7'b0000000, bramr};

		// Program bank register
		10'h034: MMIO_DOr <= pbr;

		// Game Pak ROM bank register
		10'h036: MMIO_DOr <= rombr;

		// Config register: write only
		//10'h037: MMIO_DOr <= cfgr;

		// Screen base register: write only
		//10'h038: MMIO_DOr <= scbr;

		// Clock select register: write only
		10'h039: MMIO_DOr <= {7'b0000000, clsr};

		// Screen mode register: write only
		//10'h03a: MMIO_DOr <= {2'b00, scmr};

		// Version code register
		10'h03b: MMIO_DOr <= vcr;

		// Game Pak RAM bank register
		10'h03c: MMIO_DOr <= {7'b0000000, rambr};

		//10'h03d: Unused

		// Cache base register
		10'h03e: MMIO_DOr <= cbr[7:0];
		10'h03f: MMIO_DOr <= cbr[15:8];

		// Color register: no access from SNES CPU
		// Plot option register: no access from SNES CPU

		// Cache RAM
		//10'h1xx, 10'h2xx:

		default: MMIO_DOr <= 8'hff;
	endcase
end

always @(posedge clkin) begin
	if (MMIO_WR_EN) begin
		//case (ADDR[9:0])
		//endcase
	end
end

endmodule
