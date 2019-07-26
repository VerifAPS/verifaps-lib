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
VAR  Actuator_PusherY1 : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_PusherY2 : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_SorterConveyorTowardsCrane : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_SorterConveyorTowardsStacker : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_SorterGreenLampConveyor : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_SorterWhiteLampConveyor : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampGreenLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampPusher : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampSliderMovedIn : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampSliderMovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Actuator_StampWhiteLamp : BOOL; END_VAR {*Lrwxp*}
VAR  Conveyor : Conveyor; END_VAR {*Lrwxp*}
VAR  Crane : Crane; END_VAR {*Lrwxp*}
VAR  Mag : Magazin; END_VAR {*Lrwxp*}
VAR  Pusher : Pusher; END_VAR {*Lrwxp*}
VAR  Sensor_AnalogCranePosition : INT; END_VAR {*Lrwxp*}
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
VAR  Sensor_SorterCapacitiveSensorPusher1 : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterCapacitiveSensorPusher2 : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterEmergencyStop : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterLightbarrierCraneInterface : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterLightnessSensorPusher1 : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterLightnessSensorPusher2 : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterLightnessSensorPusher3 : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterLightnesssensorCraneInterfaceInverse : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterPusher1MovedIn : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterPusher1MovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterPusher2MovedIn : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterPusher2MovedOut : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterStartButton : BOOL; END_VAR {*Lrwxp*}
VAR  Sensor_SorterSwitchManuellAutomatic : BOOL; END_VAR {*Lrwxp*}
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
Mag.AnalogCranePosition := Sensor_AnalogCranePosition;
Mag.StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_MagazinSlider := Mag.MagazinSlider;
Actuator_MagazinGreenLamp := Mag.MagazinGreenLamp;
Crane.CraneUp := Sensor_CraneUp;
Crane.CraneDown := Sensor_CraneDown;
Crane.CraneSucked := Sensor_CraneSucked;
Crane.MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane.SliderMovedOut := Sensor_SliderMovedOut;
Crane.WorkpieceReady := Sensor_WorkpieceReady;
Crane.MagazinOpticalSensor := Sensor_MagazinOpticalSensor;
Crane.StampSliderFilled := Sensor_StampSliderFilled;
Crane.StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Crane.StampLowered := Sensor_StampLowered;
Crane.AnalogCranePosition := Sensor_AnalogCranePosition;
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
Stamp.AnalogCranePosition := Sensor_AnalogCranePosition;
Stamp.StampStartButton := Sensor_StampStartButton;
Actuator_StampSliderMovedOut := Stamp.StampSliderMovedOut;
Actuator_StampSliderMovedIn := Stamp.StampSliderMovedIn;
Actuator_StampWhiteLamp := Stamp.StampWhiteLamp;
Actuator_StampPusher := Stamp.StampPusher;
Actuator_StampGreenLamp := Stamp.StampGreenLamp;
Conveyor.SorterStartButton := Sensor_SorterStartButton;
Conveyor.SorterSwitchManuellAutomatic := Sensor_SorterSwitchManuellAutomatic;
Conveyor.SorterLightbarrierCraneInterface := Sensor_SorterLightbarrierCraneInterface;
Actuator_SorterConveyorTowardsStacker := Conveyor.SorterConveyorTowardsStacker;
Actuator_SorterConveyorTowardsCrane := Conveyor.SorterConveyorTowardsCrane;
Actuator_SorterGreenLampConveyor := Conveyor.SorterGreenLampConveyor;
Actuator_SorterWhiteLampConveyor := Conveyor.SorterWhiteLampConveyor;
Pusher.SorterLightnesssensorCraneInterfaceInverse := Sensor_SorterLightnesssensorCraneInterfaceInverse;
Pusher.SorterLightbarrierCraneInterface := Sensor_SorterLightbarrierCraneInterface;
Pusher.SorterCapacitiveSensorPusher1 := Sensor_SorterCapacitiveSensorPusher1;
Pusher.SorterLightnessSensorPusher1 := Sensor_SorterLightnessSensorPusher1;
Pusher.SorterCapacitiveSensorPusher2 := Sensor_SorterCapacitiveSensorPusher2;
Pusher.SorterLightnessSensorPusher2 := Sensor_SorterLightnessSensorPusher2;
Pusher.SorterLightnessSensorPusher3 := Sensor_SorterLightnessSensorPusher3;
Pusher.SorterPusher1MovedOut := Sensor_SorterPusher1MovedOut;
Pusher.SorterPusher1MovedIn := Sensor_SorterPusher1MovedIn;
Pusher.SorterPusher2MovedOut := Sensor_SorterPusher2MovedOut;
Pusher.SorterPusher2MovedIn := Sensor_SorterPusher2MovedIn;
Pusher.SorterStartButton := Sensor_SorterStartButton;
Actuator_PusherY1 := Pusher.PusherY1;
Actuator_PusherY2 := Pusher.PusherY2;
IF ((Sensor_SorterEmergencyStop AND Sensor_StampEmergencyStop) AND Sensor_MagazinEmergencyStop) THEN
    Mag();
    Crane();
    Stamp();
    Conveyor();
    Pusher();
    IF ((Actuator_SorterGreenLampConveyor AND Actuator_MagazinGreenLamp) AND Actuator_StampGreenLamp) THEN
        IF (((Stamp.StartCommandStamp AND Crane.StartCommandCrane) AND Conveyor.StartCommandConveyor) AND Mag.StartCommandMagazin) THEN
            Crane.StartVar := TRUE;
            Conveyor.StartVar := TRUE;
            Mag.StartVar := TRUE;
            Pusher.StartVar := TRUE;
            Stamp.StartVar := TRUE;
        END_IF;
    END_IF;
    Crane.SFCReset := FALSE;
    Conveyor.SFCReset := FALSE;
    Mag.SFCReset := FALSE;
    Pusher.SFCReset := FALSE;
    Stamp.SFCReset := FALSE;
ELSEIF ((NOT Sensor_SorterEmergencyStop OR NOT Sensor_StampEmergencyStop) OR NOT Sensor_MagazinEmergencyStop) THEN
    Actuator_MagazinSlider := FALSE;
    Actuator_CraneLower := FALSE;
    Actuator_MagazinVacuumOn := FALSE;
    Actuator_MagazinVacuumOff := TRUE;
    Actuator_MagazinGreenLamp := FALSE;
    Actuator_CraneTurnCounterclockwise := FALSE;
    Actuator_CraneTurnClockwise := FALSE;
    Actuator_SorterConveyorTowardsStacker := FALSE;
    Actuator_SorterConveyorTowardsCrane := FALSE;
    Actuator_SorterGreenLampConveyor := FALSE;
    Actuator_PusherY1 := FALSE;
    Actuator_PusherY2 := FALSE;
    Actuator_StampSliderMovedOut := TRUE;
    Actuator_StampSliderMovedIn := FALSE;
    Actuator_StampGreenLamp := FALSE;
    Actuator_StampPusher := FALSE;
    Actuator_AnalogCranePressure := INT#0;
    Crane.SFCReset := TRUE;
    Conveyor.SFCReset := TRUE;
    Mag.SFCReset := TRUE;
    Pusher.SFCReset := TRUE;
    Stamp.SFCReset := TRUE;
    Crane.StartVar := FALSE;
    Conveyor.StartVar := FALSE;
    Mag.StartVar := FALSE;
    Pusher.StartVar := FALSE;
    Stamp.StartVar := FALSE;
END_IF;
END_PROGRAM
