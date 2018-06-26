PROGRAM var_ints

VAR_INPUT
    var_FLAG : BOOL;
END_VAR

VAR_OUTPUT
    var_I : INT;
    var_J : INT;
    var_SUM : INT;
END_VAR

var_SUM := 0 ;
FOR var_I := 1 TO 3 DO
  FOR var_J := 1 TO 2 DO
    var_SUM := var_SUM + var_J ;
  END_FOR ;	
  var_SUM := var_SUM + var_I ;
END_FOR;
IF var_FLAG THEN var_SUM := 0; END_IF

END_PROGRAM