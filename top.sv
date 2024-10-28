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

    // Output of stack
    logic [7:0][15:0] stackOut;

    // TB signals
    logic startStackOverflow, startDoneEarly, startAddOverflow, twoStarts,
          startSubOverflow, startOp;
    logic [15:0] topEntry, secondEntry, answer;

    // Calculator instantiation
    TA_calc  brokenCalc(.*);

    // The system clock
    initial begin
        clock = 1'b0;
        forever #5 clock = ~clock;
    end

    /* Class that is used to give the caculator random numbers or operations 
    from time to time to ensure that it works even with random conditions */
    class calculatorInputs;
      rand bit [15:0] calcPayload;
      rand bit [15:0] calcOperation;
      rand bit [15:0] tooManyEntries;
      rand bit [15:0] numOfEntries;
      rand bit [15:0] notOperation;
      rand bit [15:0] num1NoOverflow;
      rand bit [15:0] num2NoOverflow;

      constraint operation {calcOperation inside {16'h1, 16'h2, 16'h4, 16'h8, 
                                                  16'h10, 16'h20};}
      constraint manyEntries {tooManyEntries inside {[9:20]};}
      constraint numEntries {numOfEntries inside {[1:7]};}
      /* https://www.chipverify.com/systemverilog/systemverilog-constraint-
         examples*/
      constraint invalidOp {!(notOperation inside {16'h1, 16'h2, 16'h4, 16'h8, 
                                                  16'h10, 16'h20});}
      constraint noAddOverflow { 
        if (num1NoOverflow[15] == 0 && num2NoOverflow[15] == 0) 
          num1NoOverflow + num2NoOverflow <= 16'h7FFF;
        else if (num1NoOverflow[15] == 1 && num2NoOverflow[15] == 1)
          num1NoOverflow + num2NoOverflow >= 16'h8000;
      }

      constraint noSubOverflow { 
        if (num1NoOverflow[15] == 0 && num2NoOverflow[15] == 1) 
          num1NoOverflow - num2NoOverflow <= 16'h7FFF;
        else if (num1NoOverflow[15] == 1 && num2NoOverflow[15] == 0)
          num1NoOverflow - num2NoOverflow >= 16'h8000;
      }

    endclass: calculatorInputs

    // Defines new class
    calculatorInputs calc = new;

    // Resets the memory controller and all TB signals
    task doReset;
      reset_N <= 0;
      @(posedge clock);
      reset_N <= 1;
      startStackOverflow <= 0;
      startDoneEarly <= 0;
      startAddOverflow <= 0;
      twoStarts <= 0;
      startSubOverflow <= 0;
      topEntry <= 0;
      secondEntry <= 0;
      answer <= 0;
    endtask: doReset

    // Task that uses ENTER command to add to the stack
    task enterEntries (logic [15:0] amount);
      for (int num = 0; num < amount; num++) begin
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= calc.calcPayload; // Random payload
      end
    endtask: enterEntries

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

    /* Task that gives the caculator the DONE command even though there is more 
    than one element on the stack */
    task giveDoneTooEarly;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload; // Random payload
      startDoneEarly <= 1;
      enterEntries(calc.numOfEntries);
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      @(posedge clock);
      startDoneEarly <= 0;
      @(posedge clock);

    endtask: giveDoneTooEarly

    // Task that adds to numbers that will cause an overflow
    task performAddOverflow;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= 16'h8000;
      startAddOverflow <= 1;
      @(posedge clock);
      data.op <= ENTER;
      data.payload <= 16'h8000;
      @(posedge clock);
      data.op <= ARITH_OP;
      data.payload <= 16'h1;
      enterEntries(calc.numOfEntries);
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      startAddOverflow <= 0;
    endtask: performAddOverflow

    // Task that subtracts to numbers that will cause an overflow
    task performSubOverflow;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= 16'h1;
      startSubOverflow <= 1;
      @(posedge clock);
      data.op <= ENTER;
      data.payload <= 16'h8000;
      @(posedge clock);
      data.op <= ARITH_OP;
      data.payload <= 16'h2;
      enterEntries(calc.numOfEntries);
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      startSubOverflow <= 0;
    endtask: performSubOverflow
 
    // Function that checks for addition and subtraction overflow
    function checkNumOverflow(logic [15:0] num1, logic [15:0] num2, 
                               logic add, logic [15:0] result);
      if (add && num1[15] == num2[15] && result[15] != num1[15])
        return 1;
      else if (~add && ((num1[15] == 0 && num2[15] == 1 && result[15] == 0) ||
               (num1[15] == 1 && num2[15] == 0 && result[15] == 1)))
        return 1;
        
      return 0;

    endfunction: checkNumOverflow

    /* Task that gives the caculator only one entry then tries to perform an 
    operation */
    task giveOnlyOneEntry (input logic [15:0] oper);
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload;
      @(posedge clock);
      data.op <= ARITH_OP;
      data.payload <= oper;
      enterEntries(calc.numOfEntries);
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
    endtask
    
    // Task that gives the start command twice
    task giveStartAgain;
      if (!calc.randomize()) $display("oops");
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload;
      @(posedge clock);
      data.op <= START;
      data.payload <= calc.calcPayload;
      twoStarts <= 1;
      enterEntries(calc.numOfEntries);
      @(posedge clock);
      data.op <= DONE;
      data.payload <= 16'h1;
      twoStarts <= 0;
    endtask: giveStartAgain

    // Tasks that tries to do muliple arthimetic commands in one cycle
    task tryMultipleCommands;
      if (!calc.randomize()) $display("oops");
      for (int command1 = 1; command1 < 16'h21; command1 *= 2) begin
        for (int command2 = command1*2; command2 < 16'h21; command2 *= 2) begin
          @(posedge clock);
          data.op <= START;
          data.payload <= calc.calcPayload;
          enterEntries(calc.numOfEntries);
          @(posedge clock);
          data.op <= ARITH_OP;
          data.payload <= (command1 | command2);
          @(posedge clock);
          data.op <= DONE;
          data.payload <= 16'h1;
          doReset();
        end
      end
    endtask: tryMultipleCommands

    // Function to check if the payload is a valid one or not for ARITH_OP
    function checkPayload (logic [15:0] payload);
      if (payload != 16'h1 && payload != 16'h2 && payload != 16'h4 && 
          payload != 16'h8 && payload != 16'h10 && payload != 16'h20) begin
        return 0;
      end
      return 1;
    endfunction: checkPayload

    /* Task to send a sequence to the calculator to check the correct and 
    finished signals */
    task sendCorrectSequence;
      @(posedge clock);
        data.op <= START;
        data.payload <= 16'h0005;
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= 16'h0003;
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
    endtask: sendCorrectSequence

    // Task to perform all the operations to make sure they work properly
    task performOps;
      if (!calc.randomize()) $display("oops");
      for (int command1 = 1; command1 < 16'h21; command1 *= 2) begin
        data.op <= START;
        data.payload <= calc.num1NoOverflow; // Random payload
        secondEntry <= calc.num1NoOverflow;
        startOp <= 1;
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= calc.num2NoOverflow; // Random payload
        topEntry <= calc.num2NoOverflow;
        @(posedge clock);
        data.op <= ARITH_OP;
        data.payload <= command1;
        @(posedge clock);
        data.op <= DONE;
        data.payload <= 16'h1;
        @(posedge clock);
        answer <= result;
        doReset();
      end
      startOp <= 0;
    endtask: performOps

    // This task should contain your testbench
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

        // Test for protocolError signal
        // <Not enough items on the stack to do operation>
        giveOnlyOneEntry(16'h1);
        doReset();
        giveOnlyOneEntry(16'h2);
        doReset();
        giveOnlyOneEntry(16'h4);
        doReset();
        giveOnlyOneEntry(16'h8);
        doReset();
        // <START appears again before DONE>
        giveStartAgain();
        doReset();
        // <Never 0 entries on stack between START and DONE>
        giveOnlyOneEntry(16'h20);
        doReset();
        // <The command is invalid>
        giveOnlyOneEntry(calc.notOperation);
        doReset();
        tryMultipleCommands();
        doReset();

        // Test for functional "correct", "finished", and ADD
        sendCorrectSequence();
        doReset();

        // Test for all operations
        performOps();
        doReset();

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

    property stackOverflowUntilDone;
      @(posedge clock) stackOverflow ##1 (data.op != DONE) |-> stackOverflow;
    endproperty: stackOverflowUntilDone

    property stackOverflowAfterDone;
      @(posedge clock) (data.op == DONE) |-> (~stackOverflow) throughout 
                                             (data.op == DONE);
    endproperty: stackOverflowAfterDone

    correctStackOverflow: assert property (checkStackOverflow)
            else
              $error("StackOverflow was not asserted or was asserted too early",
                     "\n");

    checkStackOverflowUntilDone: assert property (stackOverflowUntilDone)
            else
              $error("StackOverflow was not asserted until done\n");

    checkStackOverflowAfterDone: assert property (stackOverflowAfterDone)
            else
              $error("StackOverflow was still asserted even though done", 
                     " happened\n");


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
    

    /* Concurrent assertions and properties to check that the dataOverflow 
       signal is asserted when add or subtract causes the result to overflow
       and is not asserted when those two operations do not cause anything to
       overflow. Also making sure that dataOverflow is asserted until DONE */
    sequence addOperation;
      (data.op == ARITH_OP) and (data.payload == 8'h1);
    endsequence: addOperation

    sequence addOverflow;
      addOperation and (checkNumOverflow(stackOut[0], stackOut[1], 1, 
                                        (stackOut[1] + stackOut[0])));
    endsequence: addOverflow

    sequence subOperation;
      (data.op == ARITH_OP) and (data.payload == 8'h2);
    endsequence: subOperation

    sequence subOverflow;
      subOperation and (checkNumOverflow(stackOut[0], stackOut[1], 0, 
                                        (stackOut[1] - stackOut[0])));
    endsequence: subOverflow

    sequence notAddOverflow;
      addOperation and (!checkNumOverflow(stackOut[0], stackOut[1], 1, 
                                        (stackOut[1] + stackOut[0])));
    endsequence: notAddOverflow

    sequence notSubOverflow;
      subOperation and (!checkNumOverflow(stackOut[0], stackOut[1], 0, 
                                        (stackOut[1] - stackOut[0])));
    endsequence: notSubOverflow

    property checkOverflow;
      @(posedge clock) (addOverflow or subOverflow) |-> dataOverflow;
    endproperty: checkOverflow

    property checkNotOverflow;
      @(posedge clock) (notAddOverflow or notSubOverflow) |-> ~dataOverflow;
    endproperty: checkNotOverflow

    property dataOverflowUntilDone;
      @(posedge clock) dataOverflow ##1 (data.op != DONE) |-> dataOverflow;
    endproperty: dataOverflowUntilDone

    property dataOverflowAfterDone;
      @(posedge clock) (data.op == DONE) |-> (~dataOverflow) throughout 
                                             (data.op == DONE);
    endproperty: dataOverflowAfterDone

    correctOverflow: assert property (checkOverflow)
            else
              $error("Expected dataOverflow to be asserted\n");

    correctNotOverflow: assert property (checkNotOverflow)
            else
              $error("Expected dataOverflow to not be asserted\n");
    
    checkDataOverflowUntilDone: assert property (dataOverflowUntilDone)
            else
              $error("Expected dataOverflow to be asserted until done\n");

    checkDataOverflowAfterDone: assert property (dataOverflowAfterDone)
            else
              $error("Expected dataOverflow to be unasserted after done\n");


    /* Concurrent assertions and properties to check that the protocol error is
       asserted correctly for all 4 cases that can happen. Also checks that
       protocol error is not asserted when it should not be */
    sequence notValidArithOp;
      (data.op == ARITH_OP) and ((data.payload != 16'h10) and 
                                 (data.payload != 16'h20));
    endsequence: notValidArithOp
    
    property notEnoughItems;
      @(posedge clock) (data.op == START) ##1 notValidArithOp |-> protocolError; 
    endproperty: notEnoughItems

    property startAgain;
      @(posedge clock) (twoStarts and (data.op == START)) |-> protocolError;
    endproperty: startAgain

    property zeroItemsOnStack;
      @(posedge clock) (data.op == START) ##1 
                       ((data.op == ARITH_OP) and (data.payload == 16'h20))
                       |-> protocolError; 
    endproperty: zeroItemsOnStack

    property cannotUseCommand;
      @(posedge clock) ((data.op == ARITH_OP) and (!checkPayload(data.payload)))
                        |-> protocolError;
    endproperty: cannotUseCommand

    property protocolErrorUntilDone;
      @(posedge clock) protocolError ##1 (data.op != DONE) |-> protocolError;
    endproperty: protocolErrorUntilDone

    property protocolErrorAfterDone;
      @(posedge clock) (data.op == DONE) |-> (~protocolError) throughout 
                                             (data.op == DONE);
    endproperty: protocolErrorAfterDone

    correctProtocolCase1: assert property (notEnoughItems)
            else
              $error("Expected protocolError to be asserted due to not enough", 
                      " items on stack to perform operation\n");

    correctProtocolCase2: assert property (startAgain)
            else
              $error("Expected protocolError to be asserted due to start being", 
                      " asserted again before done\n");

    correctProtocolCase3: assert property (zeroItemsOnStack)
            else
              $error("Expected protocolError to be asserted due zero items on", 
                      " stack between START and DONE\n");

    correctProtocolCase4: assert property (cannotUseCommand)
            else
              $error("Expected protocolError to be asserted due to invalid", 
                      " command\n");

    correctProtocolUntilDone: assert property (protocolErrorUntilDone)
            else
              $error("Expected protocolError to be asserted until done\n");

    correctProtocolAfterDone: assert property (protocolErrorAfterDone)
            else
              $error("Expected protocolError to be unasserted after done\n");
    

    /* Concurrent assertions and properties to check that the operations that
    can be performed are producing the correct result */
    property checkAdd;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h1)) |=> 
                       ((secondEntry + topEntry) == result);
    endproperty: checkAdd

    property checkSub;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h2)) |=> 
                       ((secondEntry - topEntry) == result);
    endproperty: checkSub

    property checkAnd;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h4)) |=> 
                       ((secondEntry & topEntry) == result);
    endproperty: checkAnd

    property checkSwap;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h8)) |=> 
                       ((topEntry == stackOut[1]) and (secondEntry == 
                        stackOut[0]));
    endproperty: checkSwap

    property checkNegate;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h10)) |=> 
                       (((~topEntry) + 16'h1) == result);
    endproperty: checkNegate

    property checkPop;
      @(posedge clock) (startOp and 
                       (data.op == ARITH_OP and data.payload == 16'h20)) |=> 
                       (topEntry != stackOut[0]);
    endproperty: checkPop

    correctAdd: assert property (checkAdd)
            else
              $error("From addition,  Expected: %h  Got %h\n", 
                     (secondEntry + topEntry), answer);
    
    correctSub: assert property (checkSub)
            else
              $error("From subtraction,  Expected: %h  Got %h\n", 
                     (secondEntry - topEntry), answer);

    correctAnd: assert property (checkAnd)
            else
              $error("From AND,  Expected: %h  Got: %h\n", 
                     (secondEntry & topEntry), answer);

    correctSwap: assert property (checkSwap)
            else
              $error("From swap,  Expected: top = %h second entry = %h\n", 
                     secondEntry, topEntry, 
                     "Got: top = %h second entry = %h\n",  
                     stackOut[0], stackOut[1]);

    correctNegate: assert property (checkNegate)
            else
              $error("From negate,  Expected: %h  Got: %h\n", ((~topEntry)+1), 
                     answer);

    correctPop: assert property (checkPop)
            else
              $error("From pop,  Expected: top != %h\n", topEntry);

endmodule: top
