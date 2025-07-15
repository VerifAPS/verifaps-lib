// Simple On-Off Control

PROGRAM standard
  VAR_INPUT
    input : INT;
  END_VAR
  VAR_OUTPUT
    output : INT;
  END_VAR
  VAR
    threshold, init : INT;
  END_VAR


  ACTION act_Init
    output := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_On
    output := 1;
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
    := input > threshold;
  END_TRANSITION
  TRANSITION FROM Check TO Off
    := input <= threshold;
  END_TRANSITION
  TRANSITION FROM On TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Off TO End
    := True;
  END_TRANSITION
END_PROGRAM