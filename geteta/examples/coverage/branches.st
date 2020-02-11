PROGRAM main
VAR s : INT; END_VAR
VAR_INPUT i : INT; END_VAR
VAR_OUTPUT o : INT; END_VAR

IF s = 0 AND i >= 2 THEN
  s := 1;
  IF i >= 100 THEN
  o := i + 1;
  ELSEIF i >= 50 THEN
    o := -7;
  ELSEIF i < 0 THEN
    o := -11;
  ELSEIF i >= 25 THEN
    o := -5;
  ELSE
    o := -3;
  END_IF
ELSEIF NOT (s = 0) AND i > 0 THEN
  s := 3;
  o := i - 1 * 2;
ELSEIF i < 10 THEN
  s := 5;
  o := i - 1 * 2;
ELSE
  s := 0;
  o := -1*i+o;
END_IF

END_PROGRAM
