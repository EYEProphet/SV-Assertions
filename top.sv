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
    logic startStackOverflow, startDoneEarly, startAddOverflow, twoStarts,
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
      rand bit [15:0] notOperation;

      constraint operation {calcOperation inside {16'h1, 16'h2, 16'h4, 16'h8, 
                                                  16'h10, 16'h20};}
      constraint manyEntries {tooManyEntries inside {[9:20]};}
      constraint numEntries {numOfEntries inside {[1:7]};}
      /* https://www.chipverify.com/systemverilog/systemverilog-constraint-
         examples*/
      constraint invalidOp {!(notOperation inside {16'h1, 16'h2, 16'h4, 16'h8, 
                                                  16'h10, 16'h20});}

    endclass: calculatorInputs

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
    endtask: doReset

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

    task performAddOverflow;
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

    task performSubOverflow;
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

    function checkNumOverflow(logic [15:0] num1, logic [15:0] num2, 
                               logic add, logic [15:0] result);
      if (add && num1[15] == num2[15] && result[15] != num1[15])
        return 1;
      else if (~add && ((num1[15] == 0 && num2[15] == 1 && result[15] == 0) ||
               (num1[15] == 1 && num2[15] == 0 && result[15] == 1)))
        return 1;
        
      return 0;

    endfunction: checkNumOverflow

    task giveOnlyOneEntry (input logic [15:0] oper);
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

    task giveStartAgain;
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

    task tryMultipleCommands;
      for (int command1 = 1; command1 < 16'h20; command1 *= 2) begin
        for (int command2 = command1*2; command2 < 16'h20; command2 *= 2) begin
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

    function checkPayload (logic [15:0] payload);
      if (payload != 16'h1 && payload != 16'h2 && payload != 16'h4 && 
          payload != 16'h8 && payload != 16'h10 && payload != 16'h20) begin
        return 0;
      end
      return 1;
    endfunction: checkPayload

    task sendCorrectSequence;
      @(posedge clock);
        data.op <= START;
        data.payload <= 16'h0005; // stack: 5
        @(posedge clock);
        enterEntries(3);
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

    task performOps;
      for (int command1 = 1; command1 < 16'h20; command1 *= 2) begin
        data.op <= START;
        data.payload <= calc.calcPayload; // Random payload
        @(posedge clock);
        data.op <= ENTER;
        data.payload <= calc.calcPayload; // Random payload
        @(posedge clock);
        data.op <= ARITH_OP;
        data.payload <= command1;
        @(posedge clock);
        data.op <= DONE;
        data.payload <= 16'h1;
        doReset();
      end
    endtask: performOps

    //this task should contain your testbench
    task runTestbench(input int phase);
      begin
        /* * * * * * * * * * * *
         * YOUR TESTBENCH HERE *
         * * * * * * * * * * * */
        doReset();
        // Test for stackOverflow signal
        // pushManyEntriesOntoStack();
        // doReset();

        // // Test for unexpectedDone signal
        // giveDoneTooEarly();
        // doReset();

        // // Test for dataOverflow signal
        // performAddOverflow();
        // doReset();
        // performSubOverflow();
        // doReset();

        // Test for protocolError signal
        // <Not enough items on the stack to do operation>
        // giveOnlyOneEntry(16'h1);
        // doReset();
        // giveOnlyOneEntry(16'h2);
        // doReset();
        // giveOnlyOneEntry(16'h4);
        // doReset();
        // giveOnlyOneEntry(16'h8);
        // doReset();
        // <START appears again before DONE>
        // giveStartAgain();
        // doReset();
        // <Never 0 entries on stack between START and DONE>
        // giveOnlyOneEntry(16'h20);
        // doReset();
        // <The command is invalid>
        // giveOnlyOneEntry(calc.notOperation);
        // doReset();
        // tryMultipleCommands();
        // doReset();

        // Test for functional "correct", "finished", and ADD
        // sendCorrectSequence();
        // doReset();

        // Test for all operations
        performOps();


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

    property stackOverflowBeforeDone;
      @(posedge clock) stackOverflow |-> (stackOverflow) throughout 
                                         (data.op != DONE);
    endproperty: stackOverflowBeforeDone

    property stackOverflowAfterDone;
      @(posedge clock) (data.op == DONE) |-> (~stackOverflow) throughout 
                                             (data.op == DONE);
    endproperty: stackOverflowAfterDone

    correctStackOverflow: assert property (checkStackOverflow)
            else
              $error("StackOverflow was not asserted or was asserted too early",
                     "\n");

    checkStackOverflowBeforeDone: assert property (stackOverflowBeforeDone)
            else
              $error("StackOverflow was not asserted until done\n");

    checkStackOverflowAfterDone: assert property (stackOverflowAfterDone)
            else
              $error("StackOverflow was asserted even though done happened\n");


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
      @(posedge clock) dataOverflow |-> (dataOverflow) throughout 
                                         (data.op != DONE);
    endproperty: dataOverflowUntilDone

    correctOverflow: assert property (checkOverflow)
            else
              $error("Expected dataOverflow to be asserted\n");

    correctNotOverflow: assert property (checkNotOverflow)
            else
              $error("Expected dataOverflow to not be asserted\n");
    
    checkDataOverflowUntilDone: assert property (dataOverflowUntilDone)
            else
              $error("DataOverflow was not asserted until done\n");


    /* Concurrent assertions and properties to check that the protocol error is
       asserted correctly for all 4 cases that can happen. */
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
    
    property checkAdd;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h1) |-> 
                       ((stackOut[1] + stackOut[0]) == result);
    endproperty: checkAdd

    property checkSub;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h2) |-> 
                       ((stackOut[1] - stackOut[0]) == result);
    endproperty: checkSub

    property checkAnd;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h4) |-> 
                       ((stackOut[1] + stackOut[0]) == result);
    endproperty: checkAnd

    property checkSwap;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h8) |-> 
                       ((stackOut[1] + stackOut[0]) == result);
    endproperty: checkSwap

    property checkNegate;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h10) |-> 
                       ((stackOut[1] + stackOut[0]) == result);
    endproperty: checkNegate

    property checkPop;
      @(posedge clock) (data.op == ARITH_OP and data.payload == 16'h20) |-> 
                       ((stackOut[1] + stackOut[0]) == result);
    endproperty: checkPop

    correctAdd: assert property (checkAdd)
            else
              $error("From addition Expected: %h  Got %h", 
                     (stackOut[1] + stackOut[0]), result);


    // function checkForErrors();
    //   if ((stackOverflow == 1) || (unexpectedDone == 1) || (protocolError == 1) 
    //        || (dataOverflow == 1))
    //     return 1;
    //   return 0;
    // endfunction: checkForErrors

    // property checkCorrect;
    //   @(posedge clock) ((data.op == START) ##1 
    //                     (!checkForErrors() throughout (data.op != DONE))) 
    //                     |=> data.op != DONE ##1 correct;
    // endproperty: checkCorrect

    // property checkFinish;
    //   @(posedge clock) (data.op == START) ##[1:$] 
    //                    ((data.op == DONE) and finished);
    // endproperty: checkFinish

    // rightCorrectSignal: assert property (checkCorrect)
    //         else
    //           $error("Expected correct signal to be asserted");

    // correctFinishSignal: assert property (checkCorrect)
    //         else
    //           $error("Expected correct signal to be asserted");

endmodule: top
