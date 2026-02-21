CLASS C
  VAR PUBLIC
    a : INT := 42;
    b : INT := 33;
  END_VAR
END_CLASS

CLASS Util
  METHOD PUBLIC modify_c
    VAR_INPUT
      c : REF_TO C;
    END_VAR

    c^.a := c^.a + c^.b;
  END_METHOD
END_CLASS

PROGRAM A
  VAR
    c1 : C;
    c2 : C := (a := 10, b := 10);
    u : Util;
  END_VAR

  u.modify_c(c := c1);  // c1.a == 75
  u.modify_c(c := c2);  // c1.b == 20
  u.modify_c(c := c2);  // c1.b == 30
END_PROGRAM
