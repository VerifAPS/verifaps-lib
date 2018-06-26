TYPE
  var_TrafficLight : (var_Red, var_Green);
END_TYPE

PROGRAM var_PedestrianTrafficLight

  VAR_INPUT
    var_pedBtnPress : BOOL := FALSE;
  END_VAR

  VAR_OUTPUT
    var_carLight : BOOL := TRUE;
    var_pedLight : BOOL := FALSE;
    var_counter  : INT  := 0;
  END_VAR

  VAR
    var_buttonPressedBefore : BOOL;
    var_green : BOOL := TRUE;
    var_red   : BOOL := FALSE;
  END_VAR

  IF (NOT var_buttonPressedBefore) AND var_pedBtnPress THEN
    var_carLight := var_red;
  END_IF

  IF var_counter = 10 THEN
    var_pedLight := var_green;
  ELSIF var_counter = 40 THEN
    var_pedLight := var_red;
  ELSIF var_counter = 50 THEN
    var_carLight := var_green;
  END_IF

  IF var_carLight = var_red THEN
    var_counter := var_counter + 1;
  ELSE
    var_counter := 0;
  END_IF

  var_buttonPressedBefore := var_pedBtnPress;

END_PROGRAM