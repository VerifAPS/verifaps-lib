FUNCTION_BLOCK SlidingMean_A
  VAR_INPUT  start, end, value : INT; END_VAR
  VAR mean : INT := 0; weight  : INT := 1; END_VAR
  VAR_OUTPUT Q : INT; END_VAR

  IF start < end THEN
    mean := (end - start) / weight * value + mean;
    weight := end - start + weight;
  END_IF
  Q := mean;
END_FUNCTION_BLOCK

PROGRAM WARN_ABOVE
  VAR sensor, threshold : INT; END_VAR
  VAR sm : SlidingMean_A; END_VAR
  VAR_OUTPUT critical : BOOL; END_VAR
  sm(start := 0, end := 7, value := sensor);
  critical :=  sm.Q > threshold;
END_PROGRAM

PROGRAM WARN_BELOW
  VAR sensor, threshold : INT; END_VAR
  VAR sm : SlidingMean_A; END_VAR
  VAR_OUTPUT critical : BOOL; END_VAR
  sm(start := 0, end := 7, value := sensor);
  critical :=  sm.Q <= threshold;
END_PROGRAM


FUNCTION_BLOCK SlidingMean_B
  VAR_INPUT  start, end, value : INT;
             reset : BOOL;
  END_VAR
  VAR mean :INT := 0; weight  : INT := 1; END_VAR
  VAR_OUTPUT Q : INT; END_VAR

  IF reset THEN
    weight := 1; mean := 0;
  ELSIF start < end THEN
    mean := (end - start) * value + weight * mean;
    weight := end - start + weight;
  END_IF

END_FUNCTION_BLOCK