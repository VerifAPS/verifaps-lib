// Invert (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    out, init : INT;
  END_VAR


  ACTION act_Init
    out := -input * 2;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO End
    := init;
  END_TRANSITION
END_PROGRAM