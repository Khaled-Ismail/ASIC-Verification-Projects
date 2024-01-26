// Schematic: https://vlsitutorialscom.files.wordpress.com/2020/01/glitch-free-clock-mux-double-sync.png

`timescale 1ns/1ps

module glitchless_clock_mux_2dd (input clk1,
                                 input clk2,
                                 input sel,
                                 output clk_out
                                );
  
  wire clk1;
  wire clk2;
  wire sel;
  wire clk_out;
  
  wire i_and1;
  wire i_and2;
  
  reg i_sync1;
  reg o_sync1;
  reg i_sync2;
  reg o_sync2;
  
  wire o_and1;
  wire o_and2;
  
  assign i_and1 = ~sel && ~o_sync2;
  assign i_and2 = sel && ~o_sync1;
  
  
  always_ff @(posedge clk1) begin
    i_sync1 <= i_and1;
    o_sync1 <= i_sync1;
  end

  always_ff @(posedge clk2) begin
    i_sync2 <= i_and2;
    o_sync2 <= i_sync2;
  end
  
  assign o_and1 = o_sync1 && clk1;
  assign o_and2 = o_sync2 && clk2;
  
  assign clk_out = o_and1 || o_and2;
  
  
endmodule

module tb;
  
  logic clk1 = 0;
  logic clk2 = 0;
  logic sel = 0;
  logic clk_out;
  
  glitchless_clock_mux_2dd dut(
    .clk1(clk1),
    .clk2(clk2),
    .sel(sel),
    .clk_out(clk_out)
  );
  
  initial
    forever
      #5 clk1 =~ clk1;      
  
  initial
    forever
      #17 clk2 =~ clk2;
  
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    
    sel = 0;
    #150ns;
    
    sel = 1;
    #(1ns * $urandom_range(300,100));
    
    sel = 0;
    #(1ns * $urandom_range(300,100));
    $finish();
    
    
  end
    
  
endmodule

  
