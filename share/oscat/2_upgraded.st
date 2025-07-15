// Hysteresis Switch (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR_OUTPUT
    output : INT;
  END_VAR
  VAR
    on_threshold, off_threshold, scale, init : INT;
  END_VAR


  ACTION act_Init
    output := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_On
    output := input * scale;
  END_ACTION

  ACTION act_Off
    output := 0;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP On
    : act_On(N);
  END_STEP

  STEP Off
    : act_Off(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO On
    := input > on_threshold;
  END_TRANSITION
  TRANSITION FROM Check TO Off
    := input < off_threshold;
  END_TRANSITION
  TRANSITION FROM On TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Off TO Check
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := False;
  END_TRANSITION
END_PROGRAM