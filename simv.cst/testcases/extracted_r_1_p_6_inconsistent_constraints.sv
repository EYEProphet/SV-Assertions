class c_1_6;
    bit[0:0] fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ = 1'h1;

    constraint cannotOverflow_this    // (constraint_mode = ON) (top.sv:70)
    {
       (fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ != 1);
    }
endclass

program p_1_6;
    c_1_6 obj;
    string randState;

    initial
        begin
            obj = new;
            randState = "xz11z11zzx01z00000101zxx111zz111xzzxzxxxzzzxzzxzxxxzzzxzzxxxxxxz";
            obj.set_randstate(randState);
            obj.randomize();
        end
endprogram
