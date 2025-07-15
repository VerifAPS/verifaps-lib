// Modulo Counter

PROGRAM standard
  VAR
    enable, mod, count, init : INT;
  END_VAR


  ACTION act_Init
    count := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Inc
    count := (count + 1) % mod;
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

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Inc
    := enable == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := enable == 0;
  END_TRANSITION
  TRANSITION FROM Inc TO End
    := True;
  END_TRANSITION
END_PROGRAM