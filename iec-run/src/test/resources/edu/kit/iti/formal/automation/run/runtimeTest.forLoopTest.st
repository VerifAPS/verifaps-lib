PROGRAM my_sth
    VAR_INPUT
        Var1 : INT := 2;
        Var2 : INT := 0;
        counter2 : INT := 0;
    END_VAR

   FOR counter:=1 TO 5 BY 1 DO
       Var1:=Var1*2;
   END_FOR


   FOR counter2:=1 TO 5 BY 1 DO
      Var2:=Var2+1;
      counter2:=counter2+3;
   END_FOR
END_PROGRAM

