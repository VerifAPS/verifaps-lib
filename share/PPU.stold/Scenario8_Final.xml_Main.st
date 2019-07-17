PROGRAM Main

VAR  Actuator_AnalogCranePressure : INT; END_VAR {*Lrwxp*}
VAR  Actuator_CraneLower : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_CraneTurnClockwise : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_CraneTurnCounterclockwise : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_MagazinGreenLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_MagazinSlider : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_MagazinVacuumOff : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_MagazinVacuumOn : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_MagazinWhiteLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampGreenLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampPusher : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampSliderMovedIn : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampSliderMovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampWhiteLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Crane : Crane; END_VAR {*Lrwxp*}
VAR  Mag : Magazin; END_VAR {*Lrwxp*}
VAR  Sensor_CraneDown : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CraneOnConveyor : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CraneOnMagazin : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CranePosition : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CranePositionStamp : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CraneSucked : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_CraneUp : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_MagazinCapacitiveSensor : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_MagazinEmergencyStop : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_MagazinOpticalSensor : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_MagazinSwitchManuellAutomatic : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SliderMovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SliderNotMovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampEmergencyStop : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampLowered : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampSliderFilled : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampSliderSensorMovedIn : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampSliderSensorMovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampStartButton : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampSwitchManuellAutomatic : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StampUp : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_StartButtonMagazin : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_WorkpieceReady : BOOL; END_VAR {*Lrwxp*}
VAR  Stamp : Stamp; END_VAR {*Lrwxp*}
Mag.SliderNotMovedOut := Sensor_SliderNotMovedOut;
Mag.SliderMovedOut := Sensor_SliderMovedOut;
Mag.CraneOnMagazin := Sensor_CraneOnMagazin;
Mag.CraneDown := Sensor_CraneDown;
Mag.CraneUp := Sensor_CraneUp;
Mag.CraneOnConveyor := Sensor_CraneOnConveyor;
Mag.WorkpieceReady := Sensor_WorkpieceReady;
Mag.StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_MagazinSlider := Mag.MagazinSlider;
Actuator_MagazinGreenLamp := Mag.MagazinGreenLamp;
Crane.CraneUp := Sensor_CraneUp;
Crane.CraneOnConveyor := Sensor_CraneOnConveyor;
Crane.CraneDown := Sensor_CraneDown;
Crane.CraneSucked := Sensor_CraneSucked;
Crane.CraneOnMagazin := Sensor_CraneOnMagazin;
Crane.MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane.CranePositionStamp := Sensor_CranePositionStamp;
Crane.SliderMovedOut := Sensor_SliderMovedOut;
Crane.WorkpieceReady := Sensor_WorkpieceReady;
Crane.MagazinOpticalSensor := Sensor_MagazinOpticalSensor;
Crane.StampSliderFilled := Sensor_StampSliderFilled;
Crane.StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Crane.StampLowered := Sensor_StampLowered;
Crane.StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_CraneTurnCounterclockwise := Crane.CraneTurnCounterclockwise;
Actuator_CraneTurnClockwise := Crane.CraneTurnClockwise;
Actuator_CraneLower := Crane.CraneLower;
Actuator_MagazinVacuumOff := Crane.MagazinVacuumOff;
Actuator_MagazinVacuumOn := Crane.MagazinVacuumOn;
Actuator_AnalogCranePressure := Crane.AnalogCranePressure;
Stamp.StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Stamp.StampSliderSensorMovedIn := Sensor_StampSliderSensorMovedIn;
Stamp.StampSliderFilled := Sensor_StampSliderFilled;
Stamp.StampUp := Sensor_StampUp;
Stamp.StampLowered := Sensor_StampLowered;
Stamp.CraneDown := Sensor_CraneDown;
Stamp.CraneUp := Sensor_CraneUp;
Stamp.CraneSucked := Sensor_CraneSucked;
Stamp.CranePositionStamp := Sensor_CranePositionStamp;
Stamp.CraneOnConveyor := Sensor_CraneOnConveyor;
Stamp.StampStartButton := Sensor_StampStartButton;
Actuator_StampSliderMovedOut := Stamp.StampSliderMovedOut;
Actuator_StampSliderMovedIn := Stamp.StampSliderMovedIn;
Actuator_StampWhiteLamp := Stamp.StampWhiteLamp;
Actuator_StampPusher := Stamp.StampPusher;
Actuator_StampGreenLamp := Stamp.StampGreenLamp;
IF (Sensor_StampEmergencyStop AND Sensor_MagazinEmergencyStop) THEN
    Mag();
    Crane();
    Stamp();
    IF (Actuator_MagazinGreenLamp AND Actuator_StampGreenLamp) THEN
        IF ((Stamp.StartCommandStamp AND Crane.StartCommandCrane) AND Mag.StartCommandMagazin) THEN
            Crane.StartVar := TRUE;
            Mag.StartVar := TRUE;
            Stamp.StartVar := TRUE;
        END_IF;
    END_IF;
    Crane.SFCReset := FALSE;
    Mag.SFCReset := FALSE;
    Stamp.SFCReset := FALSE;
ELSEIF (NOT Sensor_StampEmergencyStop OR NOT Sensor_MagazinEmergencyStop) THEN
    Actuator_MagazinSlider := FALSE;
    Actuator_CraneLower := FALSE;
    Actuator_MagazinVacuumOn := FALSE;
    Actuator_MagazinVacuumOff := TRUE;
    Actuator_MagazinGreenLamp := FALSE;
    Actuator_CraneTurnCounterclockwise := FALSE;
    Actuator_CraneTurnClockwise := FALSE;
    Actuator_StampSliderMovedOut := TRUE;
    Actuator_StampSliderMovedIn := FALSE;
    Actuator_StampGreenLamp := FALSE;
    Actuator_StampPusher := FALSE;
    Actuator_AnalogCranePressure := INT#0;
    Crane.SFCReset := TRUE;
    Mag.SFCReset := TRUE;
    Stamp.SFCReset := TRUE;
    Crane.StartVar := FALSE;
    Mag.StartVar := FALSE;
    Stamp.StartVar := FALSE;
END_IF;
END_PROGRAM
