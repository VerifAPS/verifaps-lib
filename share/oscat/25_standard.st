// Up-Down Counter

PROGRAM standard
  VAR
    up, down, cnt, init : INT;
  END_VAR


  ACTION act_Init
    cnt := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Up
    cnt := cnt + 1;
  END_ACTION

  ACTION act_Down
    cnt := cnt - 1;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Up
    : act_Up(N);
  END_STEP

  STEP Down
    : act_Down(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Up
    := up == 1;
  END_TRANSITION
  TRANSITION FROM Check TO Down
    := down == 1;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := up == 0 and down == 0;
  END_TRANSITION
  TRANSITION FROM Up TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Down TO End
    := True;
  END_TRANSITION
END_PROGRAM