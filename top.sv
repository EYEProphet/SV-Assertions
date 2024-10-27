// T'sairus Beasley
// tbeasley
// top.sv
`default_nettype none

`ifndef STRUCTS
`define STRUCTS

  typedef enum logic [3:0] {START    = 4'h1,
                            ENTER    = 4'h2,
                            ARITH_OP = 4'h4,
                            DONE     = 4'h8} oper_t;

  typedef struct packed { // what appears at the data input
    oper_t       op;
    logic [15:0] payload;
    } keyIn_t;

`endif


//////////////////////
////             ////
////    top     ////
////           ////
//////////////////

module top();

    //inputs to calculator
    logic    clock, reset_N;
    keyIn_t  data;

    //outputs from calculator
    logic [15:0]  result;
    logic         stackOverflow, unexpectedDone, protocolError, dataOverflow,
                correct, finished;

    logic [7:0][15:0] stackOut;
    logic startStackOverflow, startDoneEarly, startAddOverflow, 
          startSubOverflow;

    //calculator instantiation
    TA_calc  brokenCalc(.*);

    //the system clock
    initial begin
        clock = 1'b0;
        forever #5 clock = ~clock;
    end

    class calculatorInputs;
      rand bit [15:0] calcPayload;
      rand bit [15:0] calcOperation;
      rand bit [15:0] tooManyEntries;
      rand bit [15:0] numOfEntries;

      constraint operation {calcOperation inside {16'h1, 16'h2, 16'h4, 16'h8, 
                                                  16'h10, 16'h20};}
      constraint manyEntries {tooManyEntries inside {[9:20]};}
      constraint numEntries {numOfEntries inside {[1:7]};}

    endclass: calculatorInputs

    calculatorInputs calc = new;

    // Resets the memory controller and all TB signals
    task doReset;
      reset_N <= 0;
      @(posedge clock);
      reset_N <= 1;
      startStackOverflow <= 0;
      startDoneEarly <= 0;
    endtask: doReset

    // Task to push more than 8 entries onto the stack
    task pushManyEntriesOntoStack;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload; // Random payload
      startStackOverflow <= 1;
      for (int num = 0; num < calc.tooManyEntries; num++) begin
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= calc.calcPayload; // Random payload
        startStackOverflow <= 0;
      end
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1; // done
    endtask: pushManyEntriesOntoStack

    task giveDoneTooEarly;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload; // Random payload
      startDoneEarly <= 1;
      for (int num = 0; num < calc.numOfEntries; num++) begin
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= calc.calcPayload; // Random payload
      end
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      @(posedge clock);
      startDoneEarly <= 0;

    endtask: giveDoneTooEarly

    task performAddOverflow
      @(posedge clock);
      data.op <= START;
      data.payload <= 16'hFFFF;
      startAddOverflow <= 1;
      @(posedge clock);
      data.op <= ENTER;
      data.payload <= 16'h1;
      @(posedge clock);
      data.op <= ARITH_OP;
      data.payload <= 16'h1;
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      startAddOverflow <= 0;
    endtask: performSubtractOverflow

    task performSubOverflow
      @(posedge clock);
      data.op <= START;
      data.payload <= 16'h1;
      startSubOverflow <= 1;
      @(posedge clock);
      data.op <= ENTER;
      data.payload <= 16'h0;
      @(posedge clock);
      data.op <= ARITH_OP;
      data.payload <= 16'h2;
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      startSubOverflow <= 0;
    endtask: performSubOverflow

    //this task should contain your testbench
    task runTestbench(input int phase);
      begin
        /* * * * * * * * * * * *
         * YOUR TESTBENCH HERE *
         * * * * * * * * * * * */
        doReset();
        // Test for stackOverflow signal
        pushManyEntriesOntoStack();
        doReset();

        // Test for unexpectedDone signal
        giveDoneTooEarly();
        doReset();

        // Test for dataOverflow signal
        performAddOverflow();
        doReset();
        performSubOverflow();
        doReset();

        //test for functional "correct", "finished", and ADD
        @(posedge clock);
        data.op <= START;
        data.payload <= 16'h0005; // stack: 5
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= 16'h0003; // stack: 3 5
        @(posedge clock);
        data.op <= ARITH_OP;
        data.payload <= 16'h1; // add
        @(posedge clock);
        data.op <= DONE;
        data.payload <= 16'h1; // done
        @(posedge clock);
        assert(correct);
        assert(finished);
        assert(result == 8)
          else $display("result is %d", result);
      end
    endtask

    /* * * * * * * * * * * * *
     * YOUR ASSERTIONS HERE  *
     * * * * * * * * * * * * */

    /* Concurrent assertions and properties to check that the stackOverflow 
    signal is asserted when the stack has too many entries put on it and makes
    sure that it is asserted until the DONE command */
    property checkStackOverflow;
      @(posedge clock) startStackOverflow |-> ~stackOverflow [*8] ##1 
                                              stackOverflow;
    endproperty: checkStackOverflow

    property checkStackOverflowUntilDone;
      @(posedge clock) (stackOverflow and (data.op == DONE)) |=> ~stackOverflow;
    endproperty: checkStackOverflowUntilDone

    correctStackOverflow: assert property (checkStackOverflow)
            else
              $error("Expected stackOverflow to be asserted now\n");

    correctStackOverflowUntilDone: assert property (checkStackOverflowUntilDone)
            else
              $error("Expected stackOverflow to be asserted until done\n");


    /* Concurrent assertions and properties to check that the unexpectedDone 
    signal is asserted when the DONE command is used earlier than expected and
    the signal should only be asserted for one cycle and is not asserted when it
    should not be */
    property checkUnexpectedDoneOneCycle;
      @(posedge clock) (startDoneEarly and (data.op == DONE)) |-> unexpectedDone
                        ##1 ~unexpectedDone;
    endproperty: checkUnexpectedDoneOneCycle

    property checkUnexpectedDone;
      @(posedge clock) (data.op != DONE) |-> ~unexpectedDone;
    endproperty: checkUnexpectedDone

    correctUnexpectedDoneOneCycle: assert property (checkUnexpectedDoneOneCycle)
            else
              $error("Expected unexpectedDone to be asserted and for only one", 
                     " clock cycle\n");
    
    correctUnexpectedDone: assert property (checkUnexpectedDone)
            else
              $error("Expected unexpectedDone to not be asserted unless DONE", 
                     " was given early\n");
    
    
    property checkAddOverflow;
      @(posedge clock) (checkAddOverflow) |=> dataOverflow

    endproperty: checkAddOverflow

    property checkAddOverflow;
      @(posedge clock) (checkSubOverflow) |=>

    endproperty: checkAddOverflow

endmodule: top
