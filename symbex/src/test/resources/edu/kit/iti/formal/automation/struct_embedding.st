TYPE
  A: STRUCT
    x : INT;
    y : INT;
  END_STRUCT;
END_TYPE

FUNCTION g : INT
  VAR_INPUT
    a : A;
  END_VAR

  g := a.x + a.y;
END_FUNCTION

FUNCTION A_f : INT
  VAR_INPUT
    _SELF : A;
    z : INT;
  END_VAR

  IF (_SELF.x > z) THEN
    A_f := _SELF.y;
  ELSE
    A_f := z;
  END_IF
END_FUNCTION

PROGRAM MY_PROGRAM
  VAR_INPUT
    z : INT;
  END_VAR
  VAR
    a : A := (x := 42, y := 333);
  END_VAR
  VAR_OUTPUT
    new_z : INT;
  END_VAR

  new_z := A_f(_SELF := a, z := z) + g(a);
END_PROGRAM
