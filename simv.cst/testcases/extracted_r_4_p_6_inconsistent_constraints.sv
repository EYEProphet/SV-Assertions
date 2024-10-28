class c_4_6;
    bit[0:0] fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ = 1'h1;

    constraint cannotOverflow_this    // (constraint_mode = ON) (top.sv:70)
    {
       (fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ != 1);
    }
endclass

program p_4_6;
    c_4_6 obj;
    string randState;

    initial
        begin
            obj = new;
            randState = "1z0z0zz1xx0xxz0xx0x0zxzxz1zx0zxzxxzxxxxzzxxzzzxzxxzzxxxxzzzzzzzx";
            obj.set_randstate(randState);
            obj.randomize();
        end
endprogram
