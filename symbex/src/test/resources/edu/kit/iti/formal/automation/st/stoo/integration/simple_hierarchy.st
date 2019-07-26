CLASS A
  VAR
    x : INT;
    y : INT;
  END_VAR

  METHOD f : INT
    f := x + y;
  END_METHOD

  METHOD g : INT
    g := x * y;
  END_METHOD
END_CLASS

CLASS B EXTENDS A
  VAR
    z : INT;
  END_VAR

  METHOD OVERRIDE f : INT
    f := SUPER.f() + z;
  END_METHOD

  METHOD OVERRIDE g : INT
    g := x * y * z;
  END_METHOD
END_CLASS

CLASS C EXTENDS B
  VAR
    r : INT;
  END_VAR

  METHOD OVERRIDE g : INT
    g := r * x * y * z;
  END_METHOD
END_CLASS

PROGRAM MY_PROGRAM
  VAR
    a : A := (x := 42, y := 24);
    b : B := (x := 33, y := 44, z := 55);
    c : C := (x := 1, y := 2, z := 3, r := 4);
  END_VAR
  VAR_OUTPUT
    x : INT;
    y : INT;
  END_VAR

  y := c.f();
  x := c.x;
END_PROGRAM
