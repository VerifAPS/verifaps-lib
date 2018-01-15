PROGRAM my_sth
    VAR_INPUT
        number : INT := 1;
        n2 : INT;
        active : BOOL := True;
    END_VAR

   number := 3;

   if number = 3 THEN
    number :=300;
   END_IF

   if active THEN
    n2 := 4;
    END_IF
END_PROGRAM

