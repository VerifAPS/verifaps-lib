CLASS Student
  VAR
    id : INT;
    name : STRING;
  END_VAR
END_CLASS

CLASS Verifier
  METHOD verify : BOOL
    VAR_INPUT
      id : INT;
    END_VAR

    IF (ID > 9) THEN
      Verifier := TRUE;
    ELSE
      Verifier := FALSE;
    END_IF
  END_METHOD
END_CLASS


PROGRAM MyProgram
  VAR
    student : Student := (id := 42, name := "Toby");
    no_student : Student := (id := 0, name := "Victor");
    verif : Verifier;
  END_VAR

  verif.verify(student.id); // TRUE
  verif.verify(no_student.id); // FALSE
END_PROGRAM
