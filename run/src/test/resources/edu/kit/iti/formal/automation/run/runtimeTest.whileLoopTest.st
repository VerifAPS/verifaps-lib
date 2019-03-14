PROGRAM my_sth
    VAR_INPUT
        Var1 : INT := 2;
        counter : INT := 4;
    END_VAR


   WHILE counter<>0 DO
       Var1 := Var1*2;
       counter := counter-1;
   END_WHILE
END_PROGRAM

