// Reset to default if condition

PROGRAM standard
  VAR
    cond, val, defval, out, init : INT;
  END_VAR


  ACTION act_Init
    out := val;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Reset
    out := defval;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
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
  TRANSITION FROM Check TO Reset
    := cond == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := cond == 0;
  END_TRANSITION
  TRANSITION FROM Reset TO End
    := True;
  END_TRANSITION
END_PROGRAM