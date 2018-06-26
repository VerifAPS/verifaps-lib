TYPE Point: STRUCT
                x: INT; y: INT;
            END_STRUCT;
END_TYPE

PROGRAM my_sth
    VAR
        Var1 : Point;
        Var2 : INT;
        Var3 : Point := (x:= 1, y:=2);
    END_VAR

    Var2 := 7;
    Var1.x := 1;
    Var1.y := 2;
    Var3.y := 100;
    Var3.y := -70000;


END_PROGRAM

