// Multiplexer (2-input) (Upgraded)

PROGRAM upgraded
  VAR
    a, b, sel, out, init : INT;
  END_VAR


  ACTION act_Init
    out := a + 1;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_SetB
    out := b + 1;
  END_ACTION

  ACTION act_SetA
    out := a + 1;
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

  STEP SetA
    : act_SetA(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO SetB
    := sel == 1;
  END_TRANSITION
  TRANSITION FROM Check TO SetA
    := sel == 0;
  END_TRANSITION
  TRANSITION FROM SetB TO End
    := True;
  END_TRANSITION
  TRANSITION FROM SetA TO End
    := True;
  END_TRANSITION
END_PROGRAM