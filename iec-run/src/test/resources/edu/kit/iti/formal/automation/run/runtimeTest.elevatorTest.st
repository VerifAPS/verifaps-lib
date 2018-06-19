
TYPE
  MOTOR_STATE : (GoDown, Stationary, GoUp);
  DOOR_STATE : (Open, Closed);
END_TYPE

PROGRAM Elevator

  VAR_INPUT
    CurrentPos : INT := 3;
    RequestedPos : INT := 5;
    ButtonPressed : BOOL;
  END_VAR

  VAR_OUTPUT
    Motor : MOTOR_STATE := MOTOR_STATE#Stationary;
    Door : DOOR_STATE := DOOR_STATE#Open;
  END_VAR

  IF ButtonPressed THEN

    Door := DOOR_STATE#Closed;

    IF RequestedPos > CurrentPos THEN
      Motor := MOTOR_STATE#GoUp;
    ELSEIF RequestedPos < CurrentPos THEN
      Motor := MOTOR_STATE#GoDown;
    END_IF

  END_IF

  IF RequestedPos = CurrentPos THEN
    Motor := MOTOR_STATE#Stationary;
    Door := DOOR_STATE#Open;
  END_IF

END_PROGRAM
