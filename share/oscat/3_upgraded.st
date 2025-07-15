// Toggle by Rising Edge (T Flip-Flop) (Upgraded)

PROGRAM upgraded
  VAR_INPUT
    input : INT;
  END_VAR
  VAR_OUTPUT
    output : INT;
  END_VAR
  VAR
    last, toggle_count, init : INT;
  END_VAR


  ACTION act_Init
    output := 0; last := 0; toggle_count := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_Toggle
    output := 1 - output; toggle_count := toggle_count + 1;
  END_ACTION

  ACTION act_End
    last := input;
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP Toggle
    : act_Toggle(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO Toggle
    := input == 1 and last == 0;
  END_TRANSITION
  TRANSITION FROM Toggle TO End
    := True;
  END_TRANSITION
  TRANSITION FROM Check TO End
    := input == 0 or last == 1;
  END_TRANSITION
END_PROGRAM