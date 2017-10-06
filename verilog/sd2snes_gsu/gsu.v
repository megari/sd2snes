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
// Dependencies: gsu_cache
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
  input [7:0] ROM_BUS_DI,
  output [23:0] ROM_BUS_ADDR,
  output ROM_BUS_RRQ,
  input ROM_BUS_RDY,
  input [7:0] RAM_BUS_DI,
  input [7:0] RAM_BUS_DO,
  output [23:0] RAM_BUS_ADDR,
  output RAM_BUS_RRQ,
  output RAM_BUS_WRQ,
  input RAM_BUS_RDY,
  output gsu_active,
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

reg [15:0] regs [15:0]; // General purpose registers R0~R15
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

/* ROM/RAM bus access flags */
assign ron = scmr[4];
assign ran = scmr[3];

/* Cache RAM and cache flags */
reg [31:0] cache_flags;
initial cache_flags = 32'h00000000;

wire [7:0] cache_out;
wire [7:0] cache_in;
wire [8:0] cache_addr;
wire cache_we;
wire [7:0] cache_byte;

gsu_cache cache (
  .douta(cache_out),
  .dina(cache_in),
  .addra(cache_addr),
  .wea(cache_we),
  .doutb(cache_byte),
  .clk(clkin)
);

wire [8:0] RESOLVED_CACHE_ADDR = (ADDR[9:0] + cbr) & 9'h1ff;
wire [8:0] RESOLVED_CACHE_PC = (regs[PC][9:0] + cbr) & 9'h1ff;

/* Cache flag of byte in cache pointed to by the program counter */
wire cache_flag = cache_flags[RESOLVED_CACHE_PC[8:4]];

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
parameter STATE_IDLE = 8'b00000001;
parameter STATE_CPU1 = 8'b00000010;
parameter STATE_CPU2 = 8'b00000100;
parameter STATE_CPU3 = 8'b00001000;
parameter STATE_CPU4 = 8'b00010000;

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

reg [2:0] gsu_busy;
parameter BUSY_CACHE  = 2'b00;
parameter BUSY_CACHE2 = 2'b01;
parameter BUSY_CPU    = 2'b10;
//assign gsu_busy_out = gsu_busy;
assign gsu_active = |gsu_busy;

reg [7:0] saved_di_r;
initial saved_di_r = 8'h00;

reg [8:0] gsu_cache_addr;
initial gsu_cache_addr = 9'h000;

reg [8:0] scpu_cache_addr;
initial scpu_cache_addr = 9'h000;

reg gsu_cache_we;
initial gsu_cache_we = 1'b0;

reg scpu_cache_we;
initial scpu_cache_we = 1'b0;

assign cache_in = gsu_busy[BUSY_CACHE]  ? ROM_BUS_DI
                : gsu_busy[BUSY_CACHE2] ? saved_di_r
                : 8'h00;
assign cache_addr = gsu_busy[BUSY_CACHE]  ? gsu_cache_addr
                  : gsu_busy[BUSY_CACHE2] ? scpu_cache_addr
                  : 9'h000;
assign cache_we = gsu_busy[BUSY_CACHE]  ? gsu_cache_we
                : gsu_busy[BUSY_CACHE2] ? scpu_cache_we
                : 1'b0;

reg [23:0] CACHE_SRC_ADDRr;
wire [22:0] MAPPED_CACHE_ROM_ADDR = (~|CACHE_SRC_ADDRr[23:22] & CACHE_SRC_ADDRr[15])
                                    ? /* Bank 0x00-0x3f, Offset 8000-ffff */
                                      ({3'b000, CACHE_SRC_ADDRr[21:16], CACHE_SRC_ADDRr[14:0]})
                                    : /* Bank 0x40-0x5f, Offset 0000-ffff */
                                      ({3'b000, CACHE_SRC_ADDRr[20:0]});

reg CACHE_ROM_BUS_RRQr;
initial CACHE_ROM_BUS_RRQr = 1'b0;

/* CPU ROM bus access related flags and registers */
reg cpu_rom_bus_rq;
reg [7:0] cpu_rombusdata;

reg [23:0] cpu_rombusaddr;
assign MAPPED_CPU_ROM_ADDR = (~|cpu_rombusaddr[23:22] & cpu_rombusaddr[15])
                              ? /* Bank 0x00-0x3f, Offset 8000-ffff */
                                ({3'b000, cpu_rombusaddr[21:16], cpu_rombusaddr[14:0]})
                              : /* Bank 0x40-0x5f, Offset 0000-ffff */
                                ({3'b000, cpu_rombusaddr[20:0]});

assign ROM_BUS_RRQ = CACHE_ROM_BUS_RRQr | cpu_rom_bus_rq;
assign ROM_BUS_ADDR = gsu_busy[BUSY_CACHE] ? MAPPED_CACHE_ROM_ADDR
                      : MAPPED_CPU_ROM_ADDR;


reg [4:0] CACHE_ST;
parameter ST_CACHE_IDLE  = 5'b00001;
parameter ST_CACHE_START = 5'b00010;
parameter ST_CACHE_WAIT  = 5'b00100;
parameter ST_CACHE_ADDR  = 5'b01000;
parameter ST_CACHE_END   = 5'b10000;
initial CACHE_ST = ST_CACHE_IDLE;

reg [4:0] CACHE2_ST;
parameter ST_CACHE2_IDLE  = 5'b00001;
parameter ST_CACHE2_START = 5'b00010;
parameter ST_CACHE2_WAIT  = 5'b00100;
parameter ST_CACHE2_ADDR  = 5'b01000;
parameter ST_CACHE2_END   = 5'b10000;
initial CACHE2_ST = ST_CACHE2_IDLE;

reg CACHE_TRIG_ENr;
reg CACHE_TRIG_EN2r;
reg cpu_cache_en;
initial begin
  CACHE_TRIG_ENr = 1'b0;
  CACHE_TRIG_EN2r = 1'b0;
  cpu_cache_en = 1'b0;
end
always @(posedge clkin) CACHE_TRIG_EN2r <= CACHE_TRIG_ENr;
wire CACHE_TRIG_EN = CACHE_TRIG_EN2r;

/* FSM for writing to cache from the S-CPU */
always @(posedge clkin) begin
  case (CACHE2_ST)
    ST_CACHE2_IDLE: begin
      CACHE2_ST <= ST_CACHE2_IDLE;
      if (CACHE_WR_EN && CACHE_ST == ST_CACHE_IDLE && ~gsu_busy[BUSY_CACHE]) begin
        CACHE2_ST <= ST_CACHE2_START;
        scpu_cache_addr <= RESOLVED_CACHE_ADDR;
        saved_di_r <= DI;
        gsu_busy[BUSY_CACHE2] <= 1'b1;
      end
    end
    ST_CACHE2_START: begin
      CACHE2_ST <= ST_CACHE2_WAIT;
    end
    ST_CACHE2_WAIT: begin
      CACHE2_ST <= ST_CACHE2_ADDR;
      scpu_cache_we <= 1'b1;
    end
    ST_CACHE2_ADDR: begin
      CACHE2_ST <= ST_CACHE2_IDLE;
      gsu_busy[BUSY_CACHE2] <= 1'b0;
      scpu_cache_we <= 1'b0;
      // the write will have hit the cache by the next cycle
    end
  endcase
end

/* FSM for filling a cache block through internal operation */
reg [3:0] cache_count;
initial cache_count = 4'b0;
always @(posedge clkin) begin
  case(CACHE_ST)
    ST_CACHE_IDLE: begin
      if(~CACHE_WR_EN & ~gsu_busy[BUSY_CACHE2] & CACHE_TRIG_EN & ~cache_flags[RESOLVED_CACHE_PC[8:4] /* XXX */]) begin
        CACHE_ST <= ST_CACHE_START;
        gsu_busy[BUSY_CACHE] <= 1'b1;
      end else if(~CACHE_WR_EN & ~gsu_busy[BUSY_CACHE2] & cpu_cache_en & ~cache_flags[RESOLVED_CACHE_PC[8:4] /* XXX */]) begin
        CACHE_ST <= ST_CACHE_START;
        gsu_busy[BUSY_CACHE] <= 1'b1;
      end
      else CACHE_ST <= ST_CACHE_IDLE;
    end
    ST_CACHE_START: begin
      gsu_busy[BUSY_CACHE] <= 1'b1;
      CACHE_SRC_ADDRr <= cbr + 1'b0/* XXX */;
      gsu_cache_addr <= {RESOLVED_CACHE_PC[8:4], 4'h0} /* XXX */;
      CACHE_ST <= ST_CACHE_WAIT;
      cache_count <= 4'b0;
      CACHE_ROM_BUS_RRQr <= 1'b1;
    end
    ST_CACHE_WAIT: begin
      CACHE_ROM_BUS_RRQr <= 1'b0;
      if(~CACHE_ROM_BUS_RRQr & ROM_BUS_RDY) begin
        CACHE_ST <= ST_CACHE_ADDR;
        gsu_cache_we <= 1'b1;
        cache_count <= cache_count + 1;
      end else CACHE_ST <= ST_CACHE_WAIT;
    end
    ST_CACHE_ADDR: begin
      gsu_cache_we <= 1'b0;
      CACHE_SRC_ADDRr <= CACHE_SRC_ADDRr + 1;
      gsu_cache_addr <= (gsu_cache_addr + 10'b1) & 9'h1ff;
      if (cache_count == 4'hf) begin
        gsu_busy[BUSY_CACHE] <= 1'b0;
        CACHE_ST <= ST_CACHE_IDLE;
      end else begin
        CACHE_ROM_BUS_RRQr <= 1'b1;
        CACHE_ST <= ST_CACHE_WAIT;
      end
    end
  endcase
end

/* Cache flag management */
always @(posedge clkin) begin
  if (CACHE_ST == ST_CACHE_ADDR) begin
    if (&gsu_cache_addr[3:0]) begin
      cache_flags[gsu_cache_addr[8:4]] <= 1'b1;
    end
  end
  else if (CACHE2_ST == ST_CACHE2_ADDR) begin
    if (&scpu_cache_addr[3:0]) begin
      cache_flags[scpu_cache_addr[8:4]] <= 1'b1;
    end
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
              state <= STATE_CPU1;
            end
          end

          // Status flag register
          10'h030: begin
            sfr[7:0] <= {1'b0, DI[6:1], 1'b0};
            if (DI[G]) begin
              state <= STATE_CPU1;
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
    STATE_CPU1: begin
      state <= STATE_CPU2;

      if (cache_flag) begin
        // First, read first byte of instruction from cache
        curr_op <= cache_byte;
        casex (cache_byte)
          OP_ALT1: begin
            sfr[ALT1] <= 1'b1;
            sfr[ALT2] <= 1'b0;
            regs[PC] <= regs[PC] + 16'h1;
          end
          OP_ALT2: begin
            sfr[ALT1] <= 1'b0;
            sfr[ALT2] <= 1'b1;
            regs[PC] <= regs[PC] + 16'h1;
          end
          OP_ALT3: begin
            sfr[ALT1] <= 1'b1;
            sfr[ALT2] <= 1'b1;
            regs[PC] <= regs[PC] + 16'h1;
          end
          OP_ADX: begin: adx_blk
            reg [15:0] res;

            if (!alt1 && !alt2) begin
              // ADD Rn
              res = regs[src_reg] + regs[imm];
            end
            else if (alt1 && !alt2) begin
              // ADC Rn
              res = regs[src_reg] + regs[imm] + cy;
            end
            else if (!alt1 && alt2) begin
              // ADD #n
              res = regs[src_reg] + imm;
            end
            else /* if (alt1 && alt2) */ begin
              // ADC #n
              res = regs[src_reg] + imm + cy;
            end

            // Set flags
            sfr[OV] <= (~(regs[src_reg] ^ (alt2 ? regs[imm] : imm))
                  & ((alt2 ? regs[imm] : imm) ^ res)
                  & 16'h8000) != 0;
            sfr[S]  <= (res & 16'h8000) != 0;
            sfr[CY] <= res >= 17'h10000;
            sfr[Z]  <= (res & 16'hffff) == 0;

            // Write the result
            regs[dst_reg] <= res;

            // Increment program counter if it was not set above
            if (dst_reg != PC) begin
              regs[PC] <= regs[PC] + 16'h1;
            end

            // Register reset
            sfr[B]    <= 1'b0;
            sfr[ALT1] <= 1'b0;
            sfr[ALT2] <= 1'b0;
            src_reg  <= 4'h0;
            dst_reg  <= 4'h0;
          end
          OP_IWT: begin
            immr4 <= imm;
            regs[PC] <= regs[PC] + 16'h1;
          end
          OP_NOP:  begin
            // Just reset regs.
            sfr[B] <= 1'b0;
            sfr[ALT1] <= 1'b0;
            sfr[ALT2] <= 1'b0;
            src_reg <= 4'h0;
            dst_reg <= 4'h0;

            regs[PC] <= regs[PC] + 16'h1;
          end
        endcase
      end
    end
    STATE_CPU2: begin
      state <= STATE_CPU3;

      // Wait until the second byte of the instruction is in the cache
      if (cache_flag) begin
        casex (curr_op)
          OP_BEQ:
          begin: op_beq_blk
            /*
            reg signed [7:0] tmp;
            tmp = pipeline;
            regs[PC] <= regs[PC] + 16'h1;
            //pipeline = 8'b1; // XXX: NOP for now. Should read.
            //fetch_next_cached_insn;
            if (z) begin
              // XXX this is ugly!
              regs[PC] <= $unsigned($signed(regs[PC]) + tmp);
            end
            */
          end
          OP_IWT: begin
            immr8[0] <= cache_byte;
            regs[PC] <= regs[PC] + 16'h1;
          end
        endcase
      end
    end
    STATE_CPU3: begin
      state <= STATE_CPU4;

      // Wait until the third byte of the instruction is in the cache
      if (cache_flag) begin
        casex (curr_op)
          OP_IWT: begin
            regs[immr4] <= {immr8[0], cache_byte};
            if (immr4 != PC) begin
              regs[PC] <= regs[PC] + 16'h1;
            end

            // Register reset
            sfr[B]    <= 1'b0;
            sfr[ALT1] <= 1'b0;
            sfr[ALT2] <= 1'b0;
            src_reg  <= 4'h0;
            dst_reg  <= 4'h0;
          end
        endcase
      end
    end
    STATE_CPU4: state <= sfr[G] ? STATE_CPU1 : STATE_IDLE;
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

/*
always @(posedge clkin) begin
  casex (ADDR[9:0])
    // Cache RAM
    10'h1xx, 10'h2xx: CACHE_DOr = cache[RESOLVED_CACHE_ADDR];
  endcase
end
*/

/* State machine for reading the gamepak ROM to CPU */
reg[2:0] ROMBUSRD_STATE;
parameter ST_ROMBUSRD_IDLE = 3'b001;
parameter ST_ROMBUSRD_WAIT = 3'b010;
parameter ST_ROMBUSRD_END  = 3'b100;
initial ROMBUSRD_STATE = ST_ROMBUSRD_IDLE;

/* This is just cpu_rom_bus_rq delayed by one cycle. */
reg cpu_rom_bus_rq2;
always @(posedge clkin) cpu_rom_bus_rq2 <= cpu_rom_bus_rq;

always @(posedge clkin) begin
  case(ROMBUSRD_STATE)
    ST_ROMBUSRD_IDLE: begin
      if(cpu_rom_bus_rq2) begin
        ROMBUSRD_STATE <= ST_ROMBUSRD_WAIT;
      end
    end
    ST_ROMBUSRD_WAIT: begin
      if(ROM_BUS_RDY) ROMBUSRD_STATE <= ST_ROMBUSRD_END;
      else ROMBUSRD_STATE <= ST_ROMBUSRD_WAIT;
    end
    ST_ROMBUSRD_END: begin
      /*
      if(~cpu_rombusaddr[22]) cpu_rombusdata <= ROM_BUS_DI;
      else cpu_rombusdata <= 8'h00;
      */
      cpu_rombusdata <= ROM_BUS_DI;

      /* XXX: Should we have a transition out of this state?
              Note that the CX4 core has no such transition. */
      ROMBUSRD_STATE <= ST_ROMBUSRD_IDLE;
    end
  endcase
end

endmodule
