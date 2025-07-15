// Set value if condition (Upgraded)

PROGRAM upgraded
  VAR
    cond, val, out, init : INT;
  END_VAR


  ACTION act_Init
    out := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Set
    out := val * 2;
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

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Set
    := cond == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := cond == 0;
  END_TRANSITION
  TRANSITION FROM Set TO End
    := True;
  END_TRANSITION
END_PROGRAM