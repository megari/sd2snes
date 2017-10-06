`timescale 1 ns / 1 ns
//////////////////////////////////////////////////////////////////////////////////
// Company: Rehkopf
// Engineer: Rehkopf
//
// Create Date:    01:13:46 05/09/2009
// Design Name:
// Module Name:    address
// Project Name:
// Target Devices:
// Tool versions:
// Description: Address logic w/ SaveRAM masking
//
// Dependencies:
//
// Revision:
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////
module address(
  input CLK,
  input [7:0] featurebits,  // peripheral enable/disable
  input [2:0] MAPPER,       // MCU detected mapper
  input [23:0] SNES_ADDR,   // requested address from SNES
  input [7:0] SNES_PA,      // peripheral address from SNES
  input SNES_ROMSEL,        // ROMSEL from SNES
  output [23:0] ROM_ADDR,   // Address to request from SRAM0
  output ROM_HIT,           // enable SRAM0
  output IS_SAVERAM,        // address/CS mapped as SRAM?
  output IS_ROM,            // address mapped as ROM?
  output IS_WRITABLE,       // address somehow mapped as writable area?
  input [23:0] SAVERAM_MASK,
  input [23:0] ROM_MASK,
  output msu_enable,
  output gsu_enable,
  output r213f_enable,
  output snescmd_enable,
  output nmicmd_enable,
  output return_vector_enable,
  output branch1_enable,
  output branch2_enable,
);

parameter [2:0]
  FEAT_MSU1 = 3,
  FEAT_213F = 4
;

wire [23:0] SRAM_SNES_ADDR;

/* ROM (max. 2 MB) at:
      Bank 0x00-0x3f, Offset 8000-ffff
      Bank 0x40-0x5f, Offset 0000-ffff */

assign IS_ROM = ((&~SNES_ADDR[23:22] & SNES_ADDR[15])
                 |(!SNES_ADDR[23] & SNES_ADDR[22] & !SNES_ADDR[21]));

/* Save RAM (max. 128 kB) at:
       Bank 0x78-0x79, Offset 0000-ffff */
assign IS_SAVERAM = SAVERAM_MASK[0] & (!SNES_ADDR[23] & &SNES_ADDR[22:20] & SNES_ADDR[19] & &~SNES_ADDR[18:17]);

/* Gamepak RAM (max. 128 kB) at:
       Bank 0x00-0x3f, Offset 6000-7fff
       Bank 0x70-0x71, Offset 0000-ffff
       Bank 0x80-0xbf, Offset 6000-7fff

   XXX: Hmm, this doesn't seem to be making much sense. Two of the areas are
        512 kB in size! Only 16 banks of 8 kB are needed for 128 kB.

   Using these instead:
       Bank 0x00-0x0f, Offset 6000-7fff
       Bank 0x70-0x71, Offset 0000-ffff
       Bank 0x80-0x8f, Offset 6000-7fff
*/
wire IS_GAMEPAKRAM = ((&~SNES_ADDR[22:20] & (SNES_ADDR[15:13] == 3'b011))
                      |(&SNES_ADDR[22:20] & &~SNES_ADDR[19:17]));

assign IS_WRITABLE = IS_SAVERAM;

/* The Save RAM, ROM and gamepak RAM are laid out in the physical RAM as follows:
   Save RAM address aaaa bbbc xxxx xxxx xxxx xxxx mapped to:
       1110 000c xxxx xxxx xxxx xxxx, max. 2^17 B = 128 kB
   ROM addresses:
       Bank 0x00-0x3f: address 00aa bbbb 1xxx xxxx xxxx xxxx mapped to:
           000a abbb bxxx xxxx xxxx xxxx
       Bank 0x40-0x5f: address 010a bbbb xxxx xxxx xxxx xxxx mapped to:
           000a bbbb xxxx xxxx xxxx xxxx
   Gamepak RAM addresses:
       Bank 0x00-0x0f: address 0000 aaaa 011x xxxx xxxx xxxx mapped to:
           1100 000a aaax xxxx xxxx xxxx
       Bank 0x70-0x71: address 0111 000a xxxx xxxx xxxx xxxx mapped to:
           1100 000a xxxx xxxx xxxx xxxx
       Bank 0x80-0x8f: address 1000 aaaa 011x xxxx xxxx xxxx mapped to:
           1100 000a aaax xxxx xxxx xxxx
*/

assign SRAM_SNES_ADDR = IS_SAVERAM
                        ? (24'hE00000 | SNES_ADDR[16:0] & SAVERAM_MASK)
                        : (IS_ROM
                           ? (&~SNES_ADDR[23:22] & SNES_ADDR[15])
                              ? /* Bank 0x00-0x3f, Offset 8000-ffff */
                                ({3'b000, SNES_ADDR[21:16], SNES_ADDR[14:0]} & ROM_MASK)
                              : /* Bank 0x40-0x5f, Offset 0000-ffff */
                                ({3'b000, SNES_ADDR[20:0]} & ROM_MASK)
                           : (IS_GAMEPAKRAM
                              ? (&~SNES_ADDR[22:20] & (SNES_ADDR[15:13] == 3'b011))
                                 ? /* Banks 0x00-0x0f and 0x80-0x8f */
                                   ({7'b1100000, SNES_ADDR[19:16], SNES_ADDR[12:0]})
                                 : /* Banks 0x70-0x71 */
                                   ({7'b1100000, SNES_ADDR[16:0]})
                              : SNES_ADDR));

assign ROM_ADDR = SRAM_SNES_ADDR;

assign ROM_HIT = IS_ROM | IS_WRITABLE;

assign msu_enable = featurebits[FEAT_MSU1] & (!SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hfff8) == 16'h2000));

/* Something similar to this for the GSU:
wire cx4_enable_w = (!SNES_ADDR[22] && (SNES_ADDR[15:13] == 3'b011));
assign cx4_enable = cx4_enable_w;
*/

assign r213f_enable = featurebits[FEAT_213F] & (SNES_PA == 8'h3f);

assign snescmd_enable = ({SNES_ADDR[22], SNES_ADDR[15:9]} == 8'b0_0010101);
assign nmicmd_enable = (SNES_ADDR == 24'h002BF2);
assign return_vector_enable = (SNES_ADDR == 24'h002A5A);
assign branch1_enable = (SNES_ADDR == 24'h002A13);
assign branch2_enable = (SNES_ADDR == 24'h002A4D);
endmodule
