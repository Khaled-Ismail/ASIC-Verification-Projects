`timescale 1ns/1ps

module jittery_clock_gen (output clk);
  
  reg clk;
  
  parameter F = 1; // Clock frequency in Hz.
  parameter D = 50; // Clock duty-cycle in percentage. 
  parameter J = 0; // Clock jitter in percentage.
  
  real T_ns = 1.0/F * 1e9; 	// Clock period in ns;
  real clk_on = D/100.0 * T_ns;
  real clk_off = (100.0 - D)/100.0 * T_ns;
   
  always begin
    clk <= 0;
    #(clk_off + ($random % int'((J/100.0 * T_ns)+1)));
    clk <= 1;
    #(clk_on + ($random % int'((J/100.0 * T_ns)+1)));
  end
  
  
endmodule

`timescale 1ns/1ps

module tb;

  parameter F = 100e6;
  parameter D = 50;
  parameter J = 10;
  parameter max_allowed_J = 20; // Maximum allowed clock jitter in percentage.

  logic clk; 

  jittery_clock_gen #(.F(F), .D(D), .J(J)) DUT(.clk(clk));

  real T_ns = 1.0/F * 1e9;
  real clk_on = D/100.0 * T_ns;
  real clk_off = (100.0 - D)/100.0 * T_ns; 

  property p_clock_period;
    real T_start;
    real T_end;
    @(posedge clk)    
    (1, T_start = $realtime)
    ##1 (1, T_end = $realtime)
    ##0 (1, $display($sformatf("Expected Period: %0.3f. Actual Period: %0.3f", T_ns, (T_end-T_start))))
    ##0 (T_end - T_start == T_ns); 
  endproperty
  property_clock_period: assert property(p_clock_period);

  property p_duty_cycle;
    real T_high_start, T_high_end;
    @(posedge clk)
    (1, T_high_start = $realtime)
    |->
    @(negedge clk) (1, T_high_end = $realtime)
    ##0 (1, $display($sformatf("Expected Duty-Cycle: %0.3f. Actual Duty-Cycle: %0.3f", D, ((T_high_end-T_high_start)*100.0/T_ns))))
    ##0 (D == ((T_high_end-T_high_start)/T_ns * 100.0));
  endproperty
  property_duty_cycle: assert property (p_duty_cycle);
  
  property p_max_allowed_jitter;
    // Note that the DUT can inject jitter for both the high and low levels, which in the worst case adds the following latency to the original clock period: (largest possible random value resulting in positive high-level jitter) + (largest possible random value resulting in low-level jitter).
    // In this case, the assertion will pass if: (max_allowed_J <= 2 * J); where the 2 stems from the two instances of largest possible random values for both high and low levels combined.
    real T_start, T_end;
    real actual_T;
    real actual_J_abs;
    @(posedge clk)    
    (1, T_start = $realtime)
    ##1 (1, T_end = $realtime)
    ##0 (1, actual_T = T_end-T_start)
    ##0 (1, actual_J_abs = actual_T-T_ns)
    ##0 ((actual_J_abs < 0, actual_J_abs = -1 * actual_J_abs) or (1, actual_J_abs = actual_J_abs)) // Get the absolute value of of the jitter in case of a negative value, or keep it the same if it is positive.
    //##0 (1, actual_J_abs = actual_J_abs * 100.0 / T_ns, $display($sformatf("actual_J_abs = %0.3f", actual_J_abs))) // Convert to percentage. // This line is a logical duplicate of the one below it, which is used for debugging by adding a "$display()" statement.
    ##0 (1, actual_J_abs = actual_J_abs * 100.0 / T_ns) // Convert to percentage.
    ##0 (1, $display($sformatf("Max. allowed abs. jitter: %0.3f %%. Actual abs. jitter: %0.3f%%", max_allowed_J, actual_J_abs)))
    ##0 (actual_J_abs <= max_allowed_J);
  endproperty
  property_max_allowed_jitter: assert property (p_max_allowed_jitter);

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    #500ns;
    $finish;
  end

endmodule


