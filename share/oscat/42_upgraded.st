// Minimum of three (Upgraded)

PROGRAM upgraded
  VAR
    a, b, c, min1, min2, init : INT;
  END_VAR


  ACTION act_Init
    min1 := min(a, b);
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Min2
    min2 := min(min1, c);
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Min2
    : act_Min2(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Min2
    := True;
  END_TRANSITION
  TRANSITION FROM Min2 TO End
    := True;
  END_TRANSITION
END_PROGRAM