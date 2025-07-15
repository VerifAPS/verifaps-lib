// Set to Min if Below (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    minval, out, init : INT;
  END_VAR


  ACTION act_Init
    out := input;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_SetMin
    out := minval - 1;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP SetMin
    : act_SetMin(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO SetMin
    := input < minval;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input >= minval;
  END_TRANSITION
  TRANSITION FROM SetMin TO End
    := True;
  END_TRANSITION
END_PROGRAM