// Description: Scoreboard for an input double data rate IDDR, where the input is divided into two seperate outputs sequentially.

// Forward declaration of a DDR packet:
typedef class packet;

  // Channels for receiving Q1 and Q2 packets from the monitor:
  uvm_tlm_analysis_fifo #(packet) q1_fifo, q2_fifo;
  uvm_tlm_analysis_fifo #(packet) iddr_fifo;

  packet q1[$], q2[$];      
  packet tmp_q1, tmp_q2;
  packet iddr[$];
  packet tmp_iddr;

  class sb extends uvm_scoreboard;
    `uvm_component_utils(sb)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      q1_fifo = new("q1_fifo", this);
      q2_fifo = new("q2_fifo", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);

      // Whenever the monitor samples Q1 and Q2 data, save them to queues:
      fork
        begin
          forever begin
            q1_fifo.analysis_export.get(tmp_q1);
            q1.push_front(tmp_q1);
          end            
        end
        begin
          forever begin
            q2_fifo.analysis_export.get(tmp_q2);
            q2.push_front(tmp_q2);
          end
        end
        begin
          forever begin
            iddr_fifo.analysis_export.get(tmp_iddr);
            iddr.push_front(tmp_iddr);
          end
        end
      join_none      

    endtask

    virtual function void check_phase(uvm_phase phase);               
      super.check_phase(phase);
      /* Pass Criteria:
         * 1- q1 and q2 queues' sizes are equal.
         * 2- q1 and q2 queues' size are half the size of iddr queue.
         * 3- iddr[i*2] = q1[i] and iddr[i*2+1] = q2[i]; where "i" if from 0 to size of q1/q2 - 1.
        */

      // 1st Criterion:
      if (q1.size() != q2.size()) begin
        `uvm_error("SB_IDDR", $sformatf("Output queues do not have equal sizes."))
      end

      // 2nd Criterion:
      if ((iddr.size() != q1.size() / 2) || (iddr.size() != q2.size() / 2)) begin
        `uvm_error("SB_IDDR", $sformatf("Output queue(s) are not half the input size."))
      end

      // 3rd Criterion:
      for (int i = 0; i < iddr.size() - 1; i++) begin
        packet chk_q1, chk_q2, chk_iddr;
        // Check Q1:
        chk_q1 = q1.pop_back();
        chk_iddr = iddr.pop_back();
        if (chk_q1.payload != chk_iddr.payload) begin
          `uvm_error("SB_IDDR", $sformatf("Q1[%0d] = %0h, iddr[%0d] = %0h. Not equal", i*2, chk_q1.payload, i, chk_iddr.payload))
        end

        // Check Q2:
        chk_q2 = q2.pop_back();
        chk_iddr = iddr.pop_back();
        if(chk_q2.payload != chk_iddr.payload) begin
          `uvm_error("SB_IDDR", $sformatf("Q2[%0d] = %0h, iddr[%0d] = %0h. Not equal", i*2+1, chk_q2.payload, i, chk_iddr.payload))
        end
      end

    endfunction

  endclass

  // Empty declaration for DDR packets:
  class packet extends uvm_sequence_item;
    bit [7:0] payload;

    `uvm_object_utils_begin(packet)
    `uvm_field_int(payload, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "packet");
      super.new(name);
    endfunction
  endclass
