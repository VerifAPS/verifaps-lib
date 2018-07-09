INTERFACE ITF
  METHOD f : INT
    VAR_INPUT
      x : INT;
    END_VAR
  END_METHOD
END_INTERFACE

CLASS A IMPLEMENTS ITF
  VAR
    b1 : B;
    b2 : B;
    c1 : C;
    c2 : C;
  END_VAR

  METHOD f : INT
    VAR_INPUT
      x : INT;
    END_VAR

    b1.c1.z := FALSE;
    f := 42;
  END_METHOD
END_CLASS

CLASS A1 EXTENDS A
  METHOD f : INT
    VAR_INPUT
      x : INT;
    END_VAR

    f := 24;
  END_METHOD
END_CLASS

CLASS A2 EXTENDS A
  METHOD f : INT
    VAR_INPUT
      x : INT;
    END_VAR

    f := 33;
  END_METHOD
END_CLASS

CLASS B IMPLEMENTS ITF
  VAR
    c1 : C;
    c2 : C;
  END_VAR
END_CLASS

CLASS C
  VAR
    z : BOOL;
  END_VAR
END_CLASS

PROGRAM MY_PROGRAM
  VAR_INPUT
    switch : BOOL;
    x : INT;
  END_VAR
  VAR
    i : ITF;
    a : A;
    a1 : A1;
    b : B;
    r : REF_TO A;
  END_VAR
  VAR_OUTPUT
    y : INT;
  END_VAR

  r := REF(a1);

  IF (switch) THEN
    i := a;
  ELSE
    i := b;
  END_IF

  y := r^.f(x);

  r^.c1 := a.b1.c1;
  r^.c2 := a.b2.c2;

  r^.b1.c2 := r^.c2;
END_PROGRAM
