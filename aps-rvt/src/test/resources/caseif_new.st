PROGRAM abc
VAR_INPUT  i : INT; END_VAR
VAR_OUTPUT o : INT; END_VAR

CASE i OF
  0:        o := 0;
  1..5:     o := i * i;
  5..10:    o := i+(i*2);
  ELSE      o := -1;
END_CASE

END_PROGRAM