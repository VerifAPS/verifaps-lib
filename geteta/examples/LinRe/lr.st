TYPE
  var_OpMode : (var_Op , var_Teach);
  var_TeachStatus :  (var_Ok, var_NoTeachPoints, var_Teaching, var_InvalidTeachPoints, var_InvalidInputValue);
END_TYPE


FUNCTION_BLOCK var_TON

VAR_INPUT
    var_IN : BOOL;
    var_PT : USINT;
END_VAR

VAR_OUTPUT
    var_Q  : BOOL;
    var_ET : USINT;
END_VAR

IF var_IN THEN
    var_Q:= var_ET = USINT#0;
    IF var_ET > USINT#0 THEN
        var_ET := var_ET - USINT#1;
    ELSE
        var_ET := USINT#0;
    END_IF
ELSE
    var_Q  := FALSE;
    var_ET := var_PT;
END_IF;

END_FUNCTION_BLOCK


PROGRAM  var_Analogsensor

VAR CONSTANT
  var_SENSORINPUT_MIN : INT := 0;
  var_SENSORINPUT_MAX : INT := 4095;
  var_TEACHTIMEOUT : TIME := TIME#20s0ms;
  var_ICONST : INT := 1000;
END_VAR

VAR_INPUT
  var_TPSet : BOOL;
  var_SensorInput, var_TPy  : INT;
  var_OperationMode : var_OpMode;
END_VAR

VAR_OUTPUT
  var_SensorOutput : INT;
END_VAR

VAR
  var_initial          : BOOL;
  var_lastmode         : var_OpMode;
  var_Status           : var_TeachStatus;
  var_teachstep        : INT;
  var_x_temp, var_y_temp, var_t, var_m, var_x1, var_y1, var_x2, var_y2 : INT;
  var_timeout          	: var_TON;
END_VAR

IF NOT var_initial THEN
  var_x1 := 0;
  var_y1 := 0;
  var_x2 := 0;
  var_y2 := 0;
  var_Status := var_TeachStatus#var_NoTeachPoints;
  var_initial := TRUE;
ELSE
  IF var_OperationMode = var_OpMode#var_Op THEN
    IF var_Status = var_TeachStatus#var_Ok AND var_SensorInput >= var_SENSORINPUT_MIN AND var_SensorInput <= var_SENSORINPUT_MAX THEN
      var_SensorOutput := var_m * var_SensorInput / var_ICONST + var_t;
    ELSE
      var_SensorOutput := 0;
    END_IF;
  ELSIF var_OperationMode = var_OpMode#var_Teach THEN
    IF var_lastmode <> var_OperationMode THEN
      var_teachstep := 0;
      var_timeout(var_IN := FALSE);
    END_IF;

    CASE var_teachstep OF
      0:
         var_Status := var_TeachStatus#var_Teaching;
         var_timeout(var_IN := TRUE, var_PT:=var_TEACHTIMEOUT);
         IF var_timeout.var_Q THEN
           var_OperationMode := var_OpMode#var_Op;
         END_IF;

         IF var_TPSet AND var_SensorInput >= var_SENSORINPUT_MIN AND var_SensorInput <= var_SENSORINPUT_MAX THEN
           var_y1 := var_TPy;
           var_x1 := var_SensorInput;
           var_teachstep := 1;
           var_timeout(var_IN := FALSE);
         END_IF;
      1:
         IF var_TPSet = FALSE THEN
           var_teachstep := 2;
         END_IF
      2:
         var_timeout(var_IN := TRUE, var_PT:=var_TEACHTIMEOUT);

         IF var_timeout.var_Q THEN
           var_OperationMode := var_OpMode#var_Op;
         END_IF;

         IF var_TPSet AND var_SensorInput >= var_SENSORINPUT_MIN
             AND var_SensorInput <= var_SENSORINPUT_MAX THEN
           var_y2 := var_TPy;
           var_x2 := var_SensorInput;
           var_teachstep := 3;
           var_timeout(var_IN := FALSE);
         END_IF;
       3:
        IF var_x1 > var_x2 THEN
           var_x_temp := var_x1;
	   var_y_temp := var_y1;
	   var_x1 := var_x2;
	   var_y1 := var_y2;
	   var_x2 := var_x_temp;
	   var_y2 := var_y_temp;
         END_IF;

         IF var_x2 - var_x1 <> 0 THEN
           var_m   := (var_y2 - var_y1) * var_ICONST / (var_x2 - var_x1);
           var_t   := var_y1 - var_m * var_x1 / var_ICONST;
           var_Status := var_TeachStatus#var_Ok;
	 ELSE
           var_Status := var_TeachStatus#var_InvalidTeachPoints;
	   var_OperationMode := var_OpMode#var_Op;
         END_IF
       END_CASE
  END_IF
END_IF
  var_lastmode := var_OperationMode;
END_PROGRAM
        
        