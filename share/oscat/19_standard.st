// Deadband

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    upper, lower, out, init : INT;
  END_VAR


  ACTION act_Init
    out := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Pass
    out := input;
  END_ACTION

  ACTION act_Block
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

  STEP Pass
    : act_Pass(N);
  END_STEP

  STEP Block
    : act_Block(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Pass
    := input > upper or input < lower;
  END_TRANSITION
  TRANSITION FROM Check TO Block
    := input <= upper and input >= lower;
  END_TRANSITION
  TRANSITION FROM Pass TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Block TO End
    := True;
  END_TRANSITION
END_PROGRAM