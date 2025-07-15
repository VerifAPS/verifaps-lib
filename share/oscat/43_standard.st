// Maximum of three

PROGRAM standard
  VAR
    a, b, c, max1, max2, init : INT;
  END_VAR


  ACTION act_Init
    max1 := a if a > b else b;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Max2
    max2 := max1 if max1 > c else c;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Max2
    : act_Max2(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Max2
    := True;
  END_TRANSITION
  TRANSITION FROM Max2 TO End
    := True;
  END_TRANSITION
END_PROGRAM