PROGRAM abc
    VAR_INPUT
        i : INT;
    END_VAR
    VAR_OUTPUT
        o : INT;
    END_VAR
    VAR
        s: INT;
    END_VAR

    ACTION up
        s := s + i;
    END_ACTION

    ACTION down
        s := s - i;
    END_ACTION

    IF i < 0 THEN
        down();
    ELSE
        up();
    END_IF
    o:=s;
END_PROGRAM