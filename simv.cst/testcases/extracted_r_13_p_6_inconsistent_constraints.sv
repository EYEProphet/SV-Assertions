class c_13_6;
    bit[0:0] fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ = 1'h1;

    constraint cannotOverflow_this    // (constraint_mode = ON) (top.sv:70)
    {
       (fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ != 1);
    }
endclass

program p_13_6;
    c_13_6 obj;
    string randState;

    initial
        begin
            obj = new;
            randState = "0z1x10x000zz0z1z11z0z0z1z1xx1xzzxxxzxzzxxxzxzzzxzxzxxzzzzxxxzzxx";
            obj.set_randstate(randState);
            obj.randomize();
        end
endprogram
