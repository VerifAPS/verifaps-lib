PROGRAM main
  VAR_INPUT i : INT; END_VAR
  VAR s : INT; END_VAR
  VAR_OUTPUT o : INT; END_VAR

  //# assume i>0
  IF i > 0 THEN
    s := s + i;
  END_IF

  IF s = 42 THEN
    //# havoc s
  END_IF

  IF s < 0 THEN
    o := 0;
  ELSE
    o := s;
  END_IF;

  //#assert o > 0
END_PROGRAM