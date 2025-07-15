// Signum

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    sgn, init : INT;
  END_VAR


  ACTION act_Init
    sgn := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_SetPos
    sgn := 1;
  END_ACTION

  ACTION act_SetNeg
    sgn := -1;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP SetPos
    : act_SetPos(N);
  END_STEP

  STEP SetNeg
    : act_SetNeg(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO SetPos
    := input > 0;
  END_TRANSITION
  TRANSITION FROM Check TO SetNeg
    := input < 0;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input == 0;
  END_TRANSITION
  TRANSITION FROM SetPos TO End
    := True;
  END_TRANSITION
  TRANSITION FROM SetNeg TO End
    := True;
  END_TRANSITION
END_PROGRAM