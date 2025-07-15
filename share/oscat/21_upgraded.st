// Integrator (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    enable, reset, sum, init : INT;
  END_VAR


  ACTION act_Init
    sum := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Add
    sum := sum + input * 2;
  END_ACTION

  ACTION act_Reset
    sum := 0;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Add
    : act_Add(N);
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
  TRANSITION FROM Check TO Add
    := enable == 1;
  END_TRANSITION
  TRANSITION FROM Add TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO Reset
    := reset == 1;
  END_TRANSITION
  TRANSITION FROM Reset TO Check
    := True;
  END_TRANSITION
END_PROGRAM