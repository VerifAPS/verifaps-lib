// Sign Flip If Condition (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    cond, out, init : INT;
  END_VAR


  ACTION act_Init
    out := input;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Flip
    out := -input * 2;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Flip
    : act_Flip(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Flip
    := cond == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := cond == 0;
  END_TRANSITION
  TRANSITION FROM Flip TO End
    := True;
  END_TRANSITION
END_PROGRAM