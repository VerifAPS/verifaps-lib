/* author: Suhyun Cha */
PROGRAM p

VAR_INPUT   EN : BOOL;    END_VAR
VAR_OUTPUT	Ready : BOOL; END_VAR

VAR         oldEN : BOOL := FALSE;
            counter :INT := 0;
END_VAR

VAR CONSTANT
    MINIMUM_EN_SIG : INT := 3; 
END_VAR

  Ready := FALSE;
  IF counter < MINIMUM_EN_SIG AND EN THEN
    counter := counter + 1;
  ELSIF counter >= MINIMUM_EN_SIG AND EN THEN
    Ready := TRUE;
  ELSIF NOT EN THEN
    counter := 0;
  ELSE
  END_IF

END_PROGRAM