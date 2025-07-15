// Clamp in Range (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    low, high, out, init : INT;
  END_VAR


  ACTION act_Init
    out := input * 2;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_ClampLow
    out := low;
  END_ACTION

  ACTION act_ClampHigh
    out := high;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP ClampLow
    : act_ClampLow(N);
  END_STEP

  STEP ClampHigh
    : act_ClampHigh(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO ClampLow
    := input < low;
  END_TRANSITION
  TRANSITION FROM Check TO ClampHigh
    := input > high;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input >= low and input <= high;
  END_TRANSITION
  TRANSITION FROM ClampLow TO End
    := True;
  END_TRANSITION
  TRANSITION FROM ClampHigh TO End
    := True;
  END_TRANSITION
END_PROGRAM