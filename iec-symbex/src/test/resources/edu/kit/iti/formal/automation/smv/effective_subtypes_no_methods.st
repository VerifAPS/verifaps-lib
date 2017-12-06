CLASS A
  VAR
    c1 : C;
    c2 : C;
  END_VAR
END_CLASS

CLASS A1 EXTENDS A
END_CLASS

CLASS A2 EXTENDS A
END_CLASS

CLASS C
  VAR
    z : INT;
  END_VAR
END_CLASS

PROGRAM MY_PROGRAM
  VAR_INPUT
    switch : BOOL;
    x : INT;
  END_VAR
  VAR
    a : A;
    a1 : A1;
    r : REF_TO A;
  END_VAR
  VAR_OUTPUT
    y : INT;
  END_VAR

  IF (switch) THEN
    r := REF(a);
  ELSE
    r := REF(a1);
  END_IF

  r^.c1.z := x;
  r^.c2.z := x + 2;

  IF (switch) THEN
    y := r^.c1.z;
  ELSE
    y := r^.c2.z;
  END_IF

  y := y + x;
END_PROGRAM
