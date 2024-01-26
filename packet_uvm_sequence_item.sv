class packet_base extends uvm_sequence_item;
  
  // Source, Destination and Payload:
   
  rand bit [2:0] src;
  rand bit [2:0] dst;
  rand bit [7:0] payload;
  
  `uvm_object_utils_begin(packet_base)
  	`uvm_field_int(src, UVM_ALL_ON)
  	`uvm_field_int(dst, UVM_ALL_ON)
  	`uvm_field_int(payload, UVM_ALL_ON)
  `uvm_object_utils_end
  
  function new(string name = "packet_base");
    super.new(name);
  endfunction
  
  constraint src_c {};
  constraint dst_c {};
  constraint payload_c {};
  
endclass

class packet_rand_payload_quarter extends packet_base;
  `uvm_object_utils(packet_rand_payload_quarter)
  
  function new(string name = "packet_rand_payload_quarter");
    super.new(name);
  endfunction
  
  constraint payload_c {
    payload dist {[0:$clog2(8)/4]:=25,
                  [$clog2(8)/4+1:$clog2(8)/2]:=25,
                  [$clog2(8)/2+1:(($clog2(8)/4)+($clog2(8)))]:=25,
                  [(($clog2(8)/4)+($clog2(8)))+1:$clog2(8)-1]:=25
                 };
    
  };
  
endclass

class packet_rand_payload_bathtub extends packet_base;
  
  int seed;
  
  `uvm_object_utils(packet_rand_payload_bathtub)
  
  function new(string name = "packet_rand_payload_bathtub");
    super.new(name);
    seed = $urandom();
  endfunction
  
  constraint payload_c;
  
  function void prerandomize();
    payload = $dist_exponential(seed, 1); // Seed, Mean   

    // Favor placing the value at the tails of the solution-space:
    // Half the time will use the inverted exponential distribution, i.e. when $urandom_range(1) is true.
    // Otherwise use the original exponential distribution.
    if($urandom_range(1)) begin
      payload = ((2**8) - 1) - payload;
    end
    
  endfunction
  
endclass
