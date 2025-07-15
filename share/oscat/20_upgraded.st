// Absolute Value (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    out, init : INT;
  END_VAR


  ACTION act_Init
    out := abs(input);
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Negate
    out := -input;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Negate
    : act_Negate(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Negate
    := input < 0;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input >= 0;
  END_TRANSITION
  TRANSITION FROM Negate TO End
    := True;
  END_TRANSITION
END_PROGRAM