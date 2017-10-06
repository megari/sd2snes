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
  input reg_we_rising,
  output ron,
  output ran
);

wire mmio_enable = CS & !ADDR[22] & (ADDR[15:12] == 4'b0011) & (ADDR[15:0] < 16'h3040);
wire MMIO_WR_EN = mmio_enable & reg_we_rising;

reg  [7:0] MMIO_DOr;
wire [7:0] MMIO_DO;
assign MMIO_DO = MMIO_DOr;

wire cache_enable = CS & !ADDR[22] & (ADDR[15:12] == 4'b0011) & (ADDR[9] ^ ADDR[8]) & (ADDR[15:0] < 16'h3300);
wire CACHE_WR_EN = cache_enable & reg_we_rising;

reg  [7:0] CACHE_DOr;
wire [7:0] CACHE_DO;
assign CACHE_DO = CACHE_DOr;

assign DO = mmio_enable ? MMIO_DO
            : cache_enable ? CACHE_DO
            : 8'h00;

reg [15:0] regs [0:15]; // General purpose registers R0~R15
parameter
  RAP = 4'd14,
  PC  = 4'd15
;

// Status/flag register flags
reg [15:0] sfr;
wire z = sfr[1];    // Zero
wire cy = sfr[2];   // Carry
wire s = sfr[3];    // Sign
wire ov = sfr[4];   // Overflow
wire g = sfr[5];    // Go
wire r = sfr[6];    // Reading ROM using R14
wire alt1 = sfr[8]; // Mode flag for next insn
wire alt2 = sfr[9]; // Mode flag for next insn
wire il = sfr[10];  // Immediate lower
wire ih = sfr[11];  // Immediate higher
wire b = sfr[12];   // Instruction executed with WITH
wire irq = sfr[15]; // Interrupt
parameter
  Z    = 4'd1,
  CY   = 4'd2,
  S    = 4'd3,
  OV   = 4'd4,
  G    = 4'd5,
  R    = 4'd6,
  ALT1 = 4'd8,
  ALT2 = 4'd9,
  IL   = 4'd10,
  IH   = 4'd11,
  B    = 4'd12,
  IRQ  = 4'd15
;

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

reg [7:0] pipeline;

reg [3:0] src_reg;
reg [3:0] dst_reg;

reg [16:0] res17;

/* ROM/RAM bus access flags */
assign ron = scmr[4];
assign ran = scmr[3];

/* Cache RAM and cache flags */
reg [7:0] cache [511:0];
reg [31:0] cache_flags;
wire [8:0] RESOLVED_CACHE_ADDR = (ADDR[9:0] + cbr) & 9'h1ff;
wire [8:0] RESOLVED_CACHE_PC = (regs[PC][9:0] + cbr) & 9'h1ff;

/* Byte in cache pointed to by the program counter */
reg [7:0] cache_byte;
always @(posedge clkin) begin
  cache_byte = cache[RESOLVED_CACHE_PC];
end

/* Cache flag of byte in cache pointed to by the program counter */
reg cache_flag;
always @(posedge clkin) begin
  cache_flag = cache_flags[RESOLVED_CACHE_PC[8:4]];
end

/* Immediate parts of current instruction */
wire [3:0] imm = cache_byte[3:0];
reg [3:0] immr4;
reg [7:0] immr8 [1:0];

/* For plotting, two pixel caches. */
reg[7:0] primary_pcache [7:0];
reg[7:0] primary_pcache_flags;
reg[7:0] secondary_pcache [7:0];
reg[7:0] secondary_pcache_flags;

reg fetch_cached_insn;

reg[7:0] state;
parameter STATE_IDLE    = 8'b00000001;
//parameter STATE_ROMWAIT = 8'b00000010;
//parameter STATE_RAMWAIT = 8'b00000100;
parameter STATE_FETCH1  = 8'b00001000;
parameter STATE_FETCH2  = 8'b00010000;
parameter STATE_FETCH3  = 8'b00100000;
parameter STATE_EXEC    = 8'b01000000;
parameter STATE_WBACK   = 8'b10000000;

parameter OP_ALT1 = 8'b00111101;
parameter OP_ALT2 = 8'b00111110;
parameter OP_ALT3 = 8'b00111111;
parameter OP_ADX  = 8'b0101xxxx;
parameter OP_BEQ  = 8'b00001001;
parameter OP_NOP  = 8'b00000001;
parameter OP_IWT  = 8'b1111xxxx; // Also LM, SM
reg [7:0] curr_op;

initial begin: initial_blk
  reg [4:0] i;
  state = STATE_IDLE;
  for (i = 5'h0; i <= PC; i = i + 5'h1) begin
    regs[i] = 16'h0000;
  end
  curr_op = OP_NOP;
end

always @(posedge clkin) begin
  if (CACHE_WR_EN) begin
    casex (ADDR[9:0])
      // Cache RAM
      // XXX: this probably won't do as the cache can
      //      also be written to by internal processes
      10'h1xx, 10'h2xx: begin
        cache[RESOLVED_CACHE_ADDR] = DI;
        if (&ADDR[3:0]) begin
          cache_flags[RESOLVED_CACHE_ADDR[8:4]] = 1'b1;
        end
      end
    endcase
  end
end

always @(posedge clkin) begin
  case (state)
    STATE_IDLE: begin
      if (MMIO_WR_EN) begin
        casex (ADDR[9:0])
          /* GPRs R0~R15 */
          10'b00000xxxxx: begin
            regs[ADDR[4:1]] <= ADDR[0]
                               ? {DI, regs[ADDR[4:1]][7:0]}
                               : {regs[ADDR[4:1]][15:8], DI};

            if (ADDR[4:1] == RAP) begin
              // TODO: should update ROM buffer
            end
            else if (ADDR[4:0] == {PC, 1'b1}) begin
              sfr[G] <= 1'b1;
              state <= STATE_FETCH1;
            end
          end

          // Status flag register
          10'h030: begin
            sfr[7:0] <= {1'b0, DI[6:1], 1'b0};
            if (DI[G]) begin
              state <= STATE_FETCH1;
            end
          end
          10'h031: sfr[15:8] <= {DI[7], 2'b00, DI[4:0]};

          //10'h032: Unused

          // Back-up RAM register
          10'h033: bramr <= DI[0];

          // Program bank register
          10'h034: pbr <= DI;

          // Game Pak ROM bank register: read only
          //10'h036: rombr <= DI;

          // Config register:
          10'h037: cfgr <= {DI[7], 1'b0, DI[5], 5'b00000};

          // Screen base register
          10'h038: scbr <= DI;

          // Clock select register
          10'h039: clsr <= DI[0];

          // Screen mode register
          10'h03a: scmr <= DI[5:0];

          // Version code register: read only
          //10'h03b: vcr <= DI;

          // Game Pak RAM bank register: read only
          //10'h03c: rambr <= DI[0];

          //10'h03d: Unused

          // Cache base register: read only
          //10'h03e: cbr[7:0] <= {DI[7:4], 4'b0000};
          //10'h03f: cbr[15:8] <= DI;

          // Color register: no access from SNES CPU
          // Plot option register: no access from SNES CPU

        endcase
      end
    end
    STATE_FETCH1: begin
      if (cache_flag) begin
        // First, read first byte of instruction from cache
        curr_op <= cache_byte;
        casex (cache_byte)
          OP_ALT1: begin
            sfr[ALT1] <= 1'b1;
            sfr[ALT2] <= 1'b0;
            state <= STATE_FETCH2;
            regs[PC] <= regs[PC] + 1;
          end
          OP_ALT2: begin
            sfr[ALT1] <= 1'b0;
            sfr[ALT2] <= 1'b1;
            state <= STATE_FETCH2;
            regs[PC] <= regs[PC] + 1;
          end
          OP_ALT3: begin
            sfr[ALT1] <= 1'b1;
            sfr[ALT2] <= 1'b1;
            state <= STATE_FETCH2;
            regs[PC] <= regs[PC] + 1;
          end
          OP_IWT: begin
            state <= STATE_FETCH2;
            immr4 <= imm;
            regs[PC] <= regs[PC] + 1;
          end
          default: state <= STATE_EXEC;
        endcase
      end
    end
    STATE_FETCH2: begin
      // Wait until the second byte of the instruction is in the cache
      if (cache_flag) begin
        casex (curr_op)
          OP_IWT: begin
            state <= STATE_FETCH3;
            immr8[0] <= cache_byte;
            regs[PC] <= regs[PC] + 1;
          end
          default: begin
            // The normal case, after a prefix instruction
            curr_op <= cache_byte;
            state <= STATE_EXEC;
          end
        endcase
      end
    end
    STATE_FETCH3: begin
      // Wait until the third byte of the instruction is in the cache
      if (cache_flag) begin
        casex (curr_op)
          OP_IWT: begin
            immr8[1] <= cache_byte;
            state <= STATE_WBACK;
          end
          default: state <= STATE_EXEC;
        endcase
      end
    end
    STATE_EXEC: begin
      casex (curr_op)
        OP_NOP:  begin
          // Just reset regs.
          sfr[B] <= 1'b0;
          sfr[ALT1] <= 1'b0;
          sfr[ALT2] <= 1'b0;
          src_reg <= 4'h0;
          dst_reg <= 4'h0;
        end
        OP_ADX: begin
          if (!alt1 && !alt2) begin
            // ADD Rn
            res17 <= regs[src_reg] + regs[imm];
          end
          else if (alt1 && !alt2) begin
            // ADC Rn
            res17 <= regs[src_reg] + regs[imm] + cy;
          end
          else if (!alt1 && alt2) begin
            // ADD #n
            res17 <= regs[src_reg] + imm;
          end
          else /* if (alt1 && alt2) */ begin
            // ADC #n
            res17 <= regs[src_reg] + imm + cy;
          end
        end
        /*
        OP_BEQ:
        begin: op_beq_blk
          reg signed [7:0] tmp;
          tmp = pipeline;
          regs[PC] <= regs[PC] + 1'b1;
          //pipeline = 8'b1; // XXX: NOP for now. Should read.
          //fetch_next_cached_insn;
          if (z) begin
            // XXX this is ugly!
            regs[PC] <= $unsigned($signed(regs[PC]) + tmp);
          end
        end
        */
      endcase
      state <= STATE_WBACK;
    end
    STATE_WBACK: begin
      casex (curr_op)
        OP_ADX: begin
          // Set flags
          sfr[OV] <= (~(regs[src_reg] ^ (alt2 ? regs[imm] : imm))
                & ((alt2 ? regs[imm] : imm) ^ res17)
                & 16'h8000) != 0;
          sfr[S]  <= (res17 & 16'h8000) != 0;
          sfr[CY] <= res17 >= 17'h10000;
          sfr[Z]  <= (res17 & 16'hffff) == 0;

          // Set result
          regs[dst_reg] <= res17;
          if (dst_reg != PC) begin
            regs[PC] <= regs[PC] + 1;
          end

          // Register reset
          sfr[B]    <= 1'b0;
          sfr[ALT1] <= 1'b0;
          sfr[ALT2] <= 1'b0;
          src_reg  <= 4'h0;
          dst_reg  <= 4'h0;
        end
        OP_IWT: begin
          regs[immr4] <= {immr8[0], immr8[1]};
          if (immr4 != PC) begin
            regs[PC] <= regs[PC] + 1;
          end

          // Register reset
          sfr[B]    <= 1'b0;
          sfr[ALT1] <= 1'b0;
          sfr[ALT2] <= 1'b0;
          src_reg  <= 4'h0;
          dst_reg  <= 4'h0;
        end
        default: regs[PC] <= regs[PC] + 1;
      endcase
      state <= sfr[G] ? STATE_FETCH1 : STATE_IDLE;
    end
  endcase
end

/* MMIO read process */
always @(posedge clkin) begin
  casex (ADDR[9:0])
    /* GPRs R0~R15 */
    10'b00000xxxx0: MMIO_DOr <= regs[ADDR[4:1]][7:0];
    10'b00000xxxx1: MMIO_DOr <= regs[ADDR[4:1]][15:8];

    // Status flag register
    10'h030: MMIO_DOr <= sfr[7:0];
    10'h031: MMIO_DOr <= sfr[15:8]; // TODO: should reset IRQ flag

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
    //10'h039: MMIO_DOr <= {7'b0000000, clsr};

    // Screen mode register: write only
    //10'h03a: MMIO_DOr <= {2'b00, scmr};

    // Version code register
    10'h03b: MMIO_DOr <= vcr;

    // Game Pak RAM bank register
    10'h03c: MMIO_DOr <= {7'b0000000, rambr};

    //10'h03d: Unused

    // Cache base register
    10'h03e: MMIO_DOr <= {cbr[7:4], 4'b0000};
    10'h03f: MMIO_DOr <= cbr[15:8];

    // Color register: no access from SNES CPU
    // Plot option register: no access from SNES CPU

    default: MMIO_DOr <= 8'hff;
  endcase
end

always @(posedge clkin) begin
  casex (ADDR[9:0])
    // Cache RAM
    10'h1xx, 10'h2xx: CACHE_DOr = cache[RESOLVED_CACHE_ADDR];
  endcase
end

endmodule
