class c_9_6;
    bit[0:0] fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ = 1'h1;

    constraint cannotOverflow_this    // (constraint_mode = ON) (top.sv:70)
    {
       (fv_7 /*checkNumOverflow(num1NoOverflow, num2NoOverflow, 0, (num2NoOverflow - num1NoOverflow))*/ != 1);
    }
endclass

program p_9_6;
    c_9_6 obj;
    string randState;

    initial
        begin
            obj = new;
            randState = "z1x01z0z00x00111zzxxzxxxx1x01z11zxzzxzzzxxxxxzxzxxzxxxxxzzxzzxzz";
            obj.set_randstate(randState);
            obj.randomize();
        end
endprogram
