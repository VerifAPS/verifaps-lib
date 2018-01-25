
PROGRAM my_sth
    VAR_INPUT
        b : BOOL := True;
        b2 : BOOL;
        number : INT := 1;
        n2 : INT;
        n3 : INT := 4;
        n4 : INT;
        n5 : INT := 3;
        n6 : INT := 13;
        n7 : INT := 3;
        n8, n9, n10 : BOOL;
    END_VAR

    b2 := NOT FALSE;
    number := (- 19);
    n2 := (- 3)+ 2;
    b := NOT b;
    n5 := n5 * 2;
    n6 := n6 MOD 7;
    n7 := n7 - 4;
    n8 := 3 <> 4;
    n9 := 3 < 4 AND 3 <= 3 AND -4 < 5 AND 4 <= 7;
    n10 := 4 < 3 OR 4 <= 3 OR 6 < -5;
END_PROGRAM

