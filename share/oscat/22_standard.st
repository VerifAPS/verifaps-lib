// Sample and Hold

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    sample, hold, init : INT;
  END_VAR


  ACTION act_Init
    hold := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Sample
    hold := input;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Sample
    : act_Sample(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Sample
    := sample == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := sample == 0;
  END_TRANSITION
  TRANSITION FROM Sample TO End
    := True;
  END_TRANSITION
END_PROGRAM