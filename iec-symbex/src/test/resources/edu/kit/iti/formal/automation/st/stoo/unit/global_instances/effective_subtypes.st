INTERFACE ITF
END_INTERFACE

CLASS A IMPLEMENTS ITF
  VAR
    b1 : B;
    b2 : B;
    c1 : C;
    c2 : C;
  END_VAR
END_CLASS

CLASS A1 EXTENDS A
END_CLASS

CLASS A2 EXTENDS A
END_CLASS

CLASS B IMPLEMENTS ITF
  VAR
    c1 : C;
    c2 : C;
  END_VAR
END_CLASS

CLASS C
END_CLASS

PROGRAM MY_PROGRAM
  VAR_INPUT
    switch : BOOL;
  END_VAR
  VAR
    i : ITF;
    a : A;
    a1 : A1;
    b : B;
    r : REF_TO A;
  END_VAR

  r := REF(a);

  IF (switch) THEN
    i := a;
  ELSE
    i := b;
  END_IF

  r^.c1 := a.b1.c1;
  r^.c2 := a.b2.c2;

  r^.b1.c2 := r^.c2;
END_PROGRAM
