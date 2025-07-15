// Maximum Selector

PROGRAM standard
  VAR
    a, b, out, init : INT;
  END_VAR


  ACTION act_Init
    out := a;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_SetB
    out := b;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP SetB
    : act_SetB(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO SetB
    := b > a;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := a >= b;
  END_TRANSITION
  TRANSITION FROM SetB TO End
    := True;
  END_TRANSITION
END_PROGRAM