// Delay Off Timer

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR_OUTPUT
    output : INT;
  END_VAR
  VAR
    timer, delay, init : INT;
  END_VAR


  ACTION act_Init
    timer := 0; output := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Set
    output := 1;
  END_ACTION

  ACTION act_Count
    timer := timer + 1;
  END_ACTION

  ACTION act_Reset
    timer := 0; output := 0;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Set
    : act_Set(N);
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
  TRANSITION FROM Check TO Set
    := input == 1;
  END_TRANSITION
  TRANSITION FROM Set TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO Count
    := input == 0 and timer < delay;
  END_TRANSITION
  TRANSITION FROM Count TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO Reset
    := input == 0 and timer >= delay;
  END_TRANSITION
  TRANSITION FROM Reset TO Check
    := True;
  END_TRANSITION
END_PROGRAM