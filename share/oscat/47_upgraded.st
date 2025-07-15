// Reset If Negative (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    out, init : INT;
  END_VAR


  ACTION act_Init
    out := input * 2;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Reset
    out := input + 1;
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
    := input < 0;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input >= 0;
  END_TRANSITION
  TRANSITION FROM Reset TO End
    := True;
  END_TRANSITION
END_PROGRAM