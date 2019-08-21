TYPE
    S : (A ,B , C);
END_TYPE

FUNCTION SEL : BOOL
    VAR_INPUT a,b,c : BOOL; END_VAR
    IF a THEN SEL := b; ELSE SEL := c; END_IF
END_FUNCTION

PROGRAM ABC
    VAR_INPUT
        tick, tock : BOOL;
    END_VAR

    VAR_OUTPUT
        x, y, z : BOOL;
        w : INT;
    END_VAR

    VAR state : S; END_VAR

    CASE state OF
        S#A:
            x := NOT y;
            y := x;
            z := x AND x OR y;
            state := S#B;
        S#B:
            x := TRUE;
            state := S#C;
        S#C:
            z := FALSE;
            state := S#A;
    END_CASE
    w := SEL(x, 0, w+1);
    x := NOT x;

    IF tick and NOT tock THEN
      x := x AND x;
    END_IF

END_PROGRAM
