TYPE
  var_MOTOR_STATE : (var_GoDown, var_Stationary, var_GoUp);
  var_DOOR_STATE : (var_Open, var_Closed);
END_TYPE

PROGRAM var_Elevator
  
  VAR_INPUT
    var_CurrentPos : INT;
    var_RequestedPos : INT;
    var_ButtonPressed : BOOL;
  END_VAR

  VAR_OUTPUT
    var_Motor : var_MOTOR_STATE := var_MOTOR_STATE#var_Stationary;
    var_Door : var_DOOR_STATE := var_DOOR_STATE#var_Closed;
  END_VAR

  IF var_ButtonPressed THEN

    var_Door := var_DOOR_STATE#var_Closed;

    IF var_RequestedPos > var_CurrentPos THEN
      var_Motor := var_MOTOR_STATE#var_GoUp;
      var_CurrentPos := var_CurrentPos + 1;
    ELSEIF var_RequestedPos < var_CurrentPos THEN
      var_Motor := var_MOTOR_STATE#var_GoDown;
      var_CurrentPos := var_CurrentPos - 1;
    ELSE
      var_Motor := var_MOTOR_STATE#var_Stationary;
      var_ButtonPressed := false;
    END_IF
  
  ELSE
    var_Motor := var_MOTOT_STATE#var_Stationary;
    var_RequestedPos := var_CurrentPos;
    var_Door := var_DOORSTATE#var_Open;
  END_IF

END_PROGRAM