// Description of PERST_n deassertion timing: https://e2e.ti.com/resized-image/__size/1230x0/__key/communityserver-discussions-components-files/138/7462.Capture2.PNG
`timescale 1ns/1ns
module test;
  
  bit ref_clk;
  real F = 1e9;
  bit ref_clk_en;
  bit VDD_1_5, VDD_3_3;
  bit PERST_n; // Should deassert after at least 100ms from the deassertion of GRST_n. and after at least 100us from the enabling of ref_clk.
  bit GRST_n;
  real T_ns = 1.0/F * 1e9; 	// Clock period in ns;

  real GRST_n_assert_time;
  real ref_clk_en_assert_time;
  
  // Generate a clock:
  initial begin
    forever begin
      #(T_ns) ref_clk =~ ref_clk;
    end
  end
  
  // Control generated clock:
  always@(ref_clk_en) begin
    if (ref_clk_en == 0) begin
      force ref_clk = 0;
    end
    else begin
      release ref_clk;

    end
  end
  
  // At least 100ms from the deassertion of GRST_n. At least 100us from the enabling of ref_clk:
  property p_PERST_deassert_timing;
    real ref_clk_en_assert_time, PERST_n_deassert_time;
    @(posedge ref_clk_en)
    (1, ref_clk_en_assert_time = $realtime)
    |->
    @(PERST_n == 1)
    ##0 (1, PERST_n_deassert_time = $realtime)
    ##0 (PERST_n_deassert_time - GRST_n_assert_time >= 100e6) // 100e6 since converting 100ms to ns scale.
    ##0 (PERST_n_deassert_time - ref_clk_en_assert_time >= 100e3); // 100e3 since converting 100us to ns scale.
  endproperty

  property_PERST_deassert_timing: assert property (p_PERST_deassert_timing);
  
    // Helper thread for tracking the assertion time of the power lines (done before the deassertion of GRST_n):
  always @(GRST_n) begin
    if (GRST_n == 1)
      GRST_n_assert_time = $realtime;
  end
  
  // Input stimulus
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #10ns;
    
    // Enable power-rails:
    VDD_1_5 = 1; VDD_3_3 = 1;
    #10ns;
    
    // Deassert GRST_n:
    GRST_n = 1;
    
    #10ns;    
    // Enable ref_clk:  
    ref_clk_en = 1;
    #20ns;
    
    // Deassert PERST_n:
    PERST_n = 1;
    
    #10ns;
    $finish;
  end
  
endmodule
