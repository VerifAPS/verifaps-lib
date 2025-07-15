// Pulse Generator (fixed width)

PROGRAM standard
  VAR
    trigger, timer, width, pulse, init : INT;
  END_VAR


  ACTION act_Init
    timer := 0; pulse := 0;
  END_ACTION

  ACTION act_Check
  END_ACTION

  ACTION act_StartPulse
    pulse := 1; timer := 1;
  END_ACTION

  ACTION act_Pulse
    timer := timer + 1;
  END_ACTION

  ACTION act_StopPulse
    pulse := 0; timer := 0;
  END_ACTION

  ACTION act_End
  END_ACTION

  INITIAL_STEP Init
    : act_Init(N);
  END_STEP

  STEP Check
    : act_Check(N);
  END_STEP

  STEP StartPulse
    : act_StartPulse(N);
  END_STEP

  STEP Pulse
    : act_Pulse(N);
  END_STEP

  STEP StopPulse
    : act_StopPulse(N);
  END_STEP

  STEP End
    : act_End(N);
  END_STEP


  TRANSITION FROM Init TO Check
    := init;
  END_TRANSITION
  TRANSITION FROM Check TO StartPulse
    := trigger == 1;
  END_TRANSITION
  TRANSITION FROM StartPulse TO Pulse
    := True;
  END_TRANSITION
  TRANSITION FROM Pulse TO Pulse
    := timer < width;
  END_TRANSITION
  TRANSITION FROM Pulse TO StopPulse
    := timer >= width;
  END_TRANSITION
  TRANSITION FROM StopPulse TO Check
    := True;
  END_TRANSITION
END_PROGRAM