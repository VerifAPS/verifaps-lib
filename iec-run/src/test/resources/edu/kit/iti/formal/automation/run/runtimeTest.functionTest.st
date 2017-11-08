FUNCTION FuncAdd : REAL
VAR_INPUT
    a: REAL;
    b: REAL;
END_VAR


FuncAdd := 2*a - 22*b;
END_FUNCTION


PROGRAM my_sth
    VAR_INPUT
        Var1 : REAL := 2;
        x : REAL := 7;
        y : REAL := 8;
    END_VAR


   Var1 := FuncAdd(x, y);
END_PROGRAM

