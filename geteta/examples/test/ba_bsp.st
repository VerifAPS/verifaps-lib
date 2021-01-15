PROGRAM ba_bsp

VAR_INPUT
    A : INT;
    B : INT;
    C : INT;
END_VAR

VAR_OUTPUT
    X : INT := 0;
    Y : INT := 0;
    Z : INT := 0;
END_VAR

IF A = 1 AND B = 1 AND C = 2 AND Z = 0 THEN
    Z := 1;

ELSIF B = C THEN
    X := 2*B;
    Y := 2*B;

ELSE
    X := 0;
    Y := Y + 1;
    Z := Y;
    
END_IF


END_PROGRAM
