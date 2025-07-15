// Hold Last Value

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    enable, hold, init : INT;
  END_VAR


  ACTION act_Init
    hold := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Hold
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

  STEP Hold
    : act_Hold(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Hold
    := enable == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := enable == 0;
  END_TRANSITION
  TRANSITION FROM Hold TO End
    := True;
  END_TRANSITION
END_PROGRAM