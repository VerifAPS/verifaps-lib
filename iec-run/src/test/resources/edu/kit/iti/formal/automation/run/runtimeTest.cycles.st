PROGRAM my_sth
    VAR_INPUT
        I : INT;
    END_VAR

    VAR
        counter : INT := 0;
    END_VAR

   counter := counter + I;

   IF counter > 1000 THEN
        counter := 0;
   END_IF

END_PROGRAM

