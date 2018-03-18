CLASS A
  VAR
    x : INT;
    y : INT;
  END_VAR
END_CLASS

FUNCTION_BLOCK FB
  VAR_INPUT
    x : INT;
  END_VAR
  VAR
    state : INT;
    active : BOOL;
  END_VAR
  VAR_OUTPUT
    y : INT;
  END_VAR

  IF active THEN
    y := x + state;
  ELSE
    y := x;
  END_IF
END_FUNCTION_BLOCK

PROGRAM MY_PROGRAM
  VAR
    a : A;
    functionBlocks : FB;
  END_VAR
END_PROGRAM
