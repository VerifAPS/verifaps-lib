// Limit Lower Bound

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    lower, out, init : INT;
  END_VAR


  ACTION act_Init
    out := input;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Clamp
    out := lower;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Clamp
    : act_Clamp(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Clamp
    := input < lower;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input >= lower;
  END_TRANSITION
  TRANSITION FROM Clamp TO End
    := True;
  END_TRANSITION
END_PROGRAM