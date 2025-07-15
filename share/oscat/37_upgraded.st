// Comparator GE (>=) (Upgraded)

PROGRAM upgraded
  VAR
    a, b, out, init : INT;
  END_VAR


  ACTION act_Init
    out := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Set
    out := a + b;
  END_ACTION

  ACTION act_Reset
    out := 0;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Set
    : act_Set(N);
  END_STEP

  STEP Reset
    : act_Reset(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Set
    := a >= b;
  END_TRANSITION
  TRANSITION FROM Check TO Reset
    := a < b;
  END_TRANSITION
  TRANSITION FROM Set TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Reset TO End
    := True;
  END_TRANSITION
END_PROGRAM