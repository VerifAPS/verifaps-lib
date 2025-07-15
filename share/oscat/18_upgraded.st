// Rate Limiter (Ramp) (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR
    out, rate, init : INT;
  END_VAR


  ACTION act_Init
    out := input;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Inc
    out := out + 2*rate;
  END_ACTION

  ACTION act_Dec
    out := out - 2*rate;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Inc
    : act_Inc(N);
  END_STEP

  STEP Dec
    : act_Dec(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Inc
    := out < input;
  END_TRANSITION
  TRANSITION FROM Check TO Dec
    := out > input;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := out == input;
  END_TRANSITION
  TRANSITION FROM Inc TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Dec TO Check
    := True;
  END_TRANSITION
END_PROGRAM