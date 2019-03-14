TYPE
  OpMode : (Op , Teach);
  TeachStatus :  (Ok, NoTeachPoints, Teaching, InvalidTeachPoints, InvalidInputValue);
END_TYPE


FUNCTION_BLOCK TON

VAR_INPUT
    IN : BOOL;
    PT : INT;
END_VAR

VAR_OUTPUT
    Q  : BOOL;
    ET : INT;
END_VAR

IF IN THEN
    Q:= ET = INT#0;
    IF ET > INT#0 THEN
        ET := ET - INT#1;
    ELSE
        ET := INT#0;
    END_IF
ELSE
    Q  := FALSE;
    ET := PT;
END_IF;

END_FUNCTION_BLOCK


PROGRAM  Analogsensor

VAR CONSTANT
  SENSORINPUT_MIN : INT := 0;
  SENSORINPUT_MAX : INT := 4095;
  TEACHTIMEOUT : TIME := TIME#20s0ms;
  ICONST : INT := 1000;
END_VAR

VAR_INPUT
  TPSet : BOOL;
  SensorInput, TPy  : INT;
  OperationMode : OpMode;
END_VAR

VAR_OUTPUT
  SensorOutput : INT;
END_VAR

VAR
  initial          : BOOL;
  lastmode         : OpMode;
  Status           : TeachStatus;
  teachstep        : INT;
  x_temp, y_temp, t, m, x1, y1, x2, y2 : INT;
  timeout          : TON;
END_VAR

IF NOT initial THEN
  x1 := 0;
  y1 := 0;
  x2 := 0;
  y2 := 0;
  Status := TeachStatus#NoTeachPoints;
  initial := TRUE;
ELSE
  IF OperationMode = OpMode#Op THEN
    IF Status = TeachStatus#Ok AND SensorInput >= SENSORINPUT_MIN AND SensorInput <= SENSORINPUT_MAX THEN
      SensorOutput := m * SensorInput / ICONST + t;
    ELSE
      SensorOutput := 0;
    END_IF;
  ELSIF OperationMode = OpMode#Teach THEN
    IF lastmode <> OperationMode THEN
      teachstep := 0;
      timeout(IN := FALSE);
    END_IF;

    CASE teachstep OF
      0:
         Status := TeachStatus#Teaching;
         timeout(IN := TRUE, PT:=TEACHTIMEOUT);
         IF timeout.Q THEN
           OperationMode := OpMode#Op;
         END_IF;

         IF TPSet AND SensorInput >= SENSORINPUT_MIN AND SensorInput <= SENSORINPUT_MAX THEN
           y1 := TPy;
           x1 := SensorInput;
           teachstep := 1;
           timeout(IN := FALSE);
         END_IF;
      1:
         IF TPSet = FALSE THEN
           teachstep := 2;
         END_IF
      2:
         timeout(IN := TRUE, PT:=TEACHTIMEOUT);

         IF timeout.Q THEN
           OperationMode := OpMode#Op;
         END_IF;

         IF TPSet AND SensorInput >= SENSORINPUT_MIN
             AND SensorInput <= SENSORINPUT_MAX THEN
           y2 := TPy;
           x2 := SensorInput;
           teachstep := 3;
           timeout(IN := FALSE);
         END_IF;
       3:
        IF x1 > x2 THEN
           x_temp := x1;
	   y_temp := y1;
	   x1 := x2;
	   y1 := y2;
	   x2 := x_temp;
	   y2 := y_temp;
         END_IF;

         IF x2 - x1 <> 0 THEN
           m   := (y1 - y2) * ICONST / (x2 - x1);
           t   := m * x1 / ICONST - y1;
           Status := TeachStatus#Ok;
	 ELSE
           Status := TeachStatus#InvalidTeachPoints;
	   OperationMode := OpMode#Op;
         END_IF
       END_CASE
  END_IF
END_IF
lastmode := OperationMode;
END_PROGRAM
        
        
