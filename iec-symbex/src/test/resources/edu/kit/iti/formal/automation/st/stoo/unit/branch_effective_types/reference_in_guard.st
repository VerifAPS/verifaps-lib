TYPE
  _INSTANCE_ID_TYPE : INT(-1..2) := -1;
END_TYPE

CLASS A
  VAR
    _INSTANCE_ID : _INSTANCE_ID_TYPE := -1;
    x : INT := 0;
  END_VAR
END_CLASS

CLASS B EXTENDS A
  VAR
    _INSTANCE_ID : _INSTANCE_ID_TYPE := -1;
  END_VAR
END_CLASS

PROGRAM MY_PROGRAM
  VAR_INPUT
    switch : BOOL;
  END_VAR
  VAR
    r : REF_TO A;
    a1 : A := (x := 1);
    a2 : A := (x := 2);
    b : B;
  END_VAR

  IF (switch) THEN
    r := REF(a1);
  ELSE
    r := REF(b);
  END_IF

  IF (r^.x = 0) THEN
    r := REF(a1);
    r^.x := 1;
  ELSEIF (r^.x = 1) THEN
    r := REF(a2);
    r^.x := 2;
  ELSE
    r := REF(b);
    r^.x := 0;
  END_IF

  WHILE (r^.x = 1) DO
    r^.x := 2;
    r := REF(a1);
  END_WHILE
END_PROGRAM
