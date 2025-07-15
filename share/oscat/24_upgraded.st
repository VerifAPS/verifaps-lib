// D Latch (Upgraded)

PROGRAM upgraded
  VAR
    d, enable, q, init : INT;
  END_VAR


  ACTION act_Init
    q := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Latch
    q := d + 1;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Latch
    : act_Latch(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Latch
    := enable == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := enable == 0;
  END_TRANSITION
  TRANSITION FROM Latch TO End
    := True;
  END_TRANSITION
END_PROGRAM