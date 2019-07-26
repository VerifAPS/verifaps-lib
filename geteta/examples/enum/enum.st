TYPE
    abc : (a, b, c);
END_TYPE

FUNCTION SEL : INT
    VAR_INPUT
        a : BOOL;
        b,c : INT;
    END_VAR

    IF a THEN
        SEL := b;
    ELSE
        SEL := c;
    END_IF
END_FUNCTION

PROGRAM ppp
    VAR i : INT; END_VAR
    VAR_OUTPUT o : abc; END_VAR

    o := SEL(i = 0, abc#a,
                SEL(i = 1, abc#b, abc#c));
    i := i + 1;
    i := SEL(i>2, 0, i);
END_PROGRAM