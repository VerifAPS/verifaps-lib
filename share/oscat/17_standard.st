// Range Check

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    low, high, in_range, init : INT;
  END_VAR


  ACTION act_Init
    in_range := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Set
    in_range := 1;
  END_ACTION

  ACTION act_Reset
    in_range := 0;
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
    := input >= low and input <= high;
  END_TRANSITION
  TRANSITION FROM Check TO Reset
    := input < low or input > high;
  END_TRANSITION
  TRANSITION FROM Set TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Reset TO End
    := True;
  END_TRANSITION
END_PROGRAM