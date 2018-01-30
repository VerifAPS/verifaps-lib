CLASS ID_Card
  VAR
    id : INT;
  END_VAR
END_CLASS

CLASS Student
  VAR
    id_card : ID_Card;
    name : STRING;
  END_VAR
END_CLASS

CLASS Verifier
  METHOD verify : BOOL
    VAR_INPUT
      id_card : ID_Card;
    END_VAR

    (* Super-secure verification *)
    IF (id_card.id > 9) THEN
      Verifier := TRUE;
    ELSE
      Verifier := FALSE;
    END_IF
  END_METHOD
END_CLASS


PROGRAM MyProgram
  VAR
    student_id_card : ID_Card := (id := 42);
    student : Student := (id := student_id_card, name := "Toby");
    fake_student : Student := (id_card := null, name := "Victor");
    verif : Verifier;
  END_VAR

  verif.verify(student.id); // TRUE
  verif.verify(fake_student.id); // FALSE
END_PROGRAM
