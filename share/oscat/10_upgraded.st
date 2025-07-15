// Down Counter (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    reset, cnt, max, init : INT;
  END_VAR


  ACTION act_Init
    cnt := max;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Count
    cnt := cnt - 2;
  END_ACTION

  ACTION act_Reset
    cnt := max;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Count
    : act_Count(N);
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
  TRANSITION FROM Check TO Count
    := input == 1 and cnt > 0;
  END_TRANSITION
  TRANSITION FROM Count TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO Reset
    := reset == 1;
  END_TRANSITION
  TRANSITION FROM Reset TO Check
    := True;
  END_TRANSITION
END_PROGRAM