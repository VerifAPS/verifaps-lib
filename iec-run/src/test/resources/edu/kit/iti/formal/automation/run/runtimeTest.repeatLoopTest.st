PROGRAM my_sth
    VAR_INPUT
        Var1 : INT := 2;
        counter : INT := 4;
    END_VAR


   REPEAT
       Var1 := Var1*2;
       counter := counter-1;
   UNTIL
       counter=0
   END_REPEAT
END_PROGRAM

