// Falling Edge Detection

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    last, edge, init : INT;
  END_VAR


  ACTION act_Init
    last := 1; edge := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Detect
    edge := 1;
  END_ACTION

  ACTION act_End
    last := input; edge := 0;
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Detect
    : act_Detect(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Detect
    := input == 0 and last == 1;
  END_TRANSITION
  TRANSITION FROM Detect TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input == 1 or last == 0;
  END_TRANSITION
END_PROGRAM