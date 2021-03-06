TYPE
    Stamp_states_t : (Green_Lamp , Init , Interstep , Interstep_2 , StampProcess , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 , Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Crane_states_t : (Crane_Go_Up , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_Conveyor , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Stamp_Metallic , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_NOT_Metallic , Init , Interstep , Interstep_2 , Interstep_Check_Workpiece , Lower_Crane , Reset_interconnect , Start_Crane , Step0 , Step2 , Suck_At_Stamp , TimeDelay , Turn_Right , Wait_At_Stamp , pause , release , release_Workpiece);
END_TYPE

PROGRAM Main

VAR  Actuator_AnalogCranePressure : INT; END_VAR 
VAR  Actuator_CraneLower : BOOL; END_VAR 
VAR  Actuator_CraneTurnClockwise : BOOL; END_VAR 
VAR  Actuator_CraneTurnCounterclockwise : BOOL; END_VAR 
VAR  Actuator_MagazinGreenLamp : BOOL; END_VAR 
VAR  Actuator_MagazinSlider : BOOL; END_VAR 
VAR  Actuator_MagazinVacuumOff : BOOL; END_VAR 
VAR  Actuator_MagazinVacuumOn : BOOL; END_VAR 
VAR  Actuator_MagazinWhiteLamp : BOOL; END_VAR 
VAR  Actuator_SomeActuator : BOOL; END_VAR 
VAR  Actuator_StampGreenLamp : BOOL; END_VAR 
VAR  Actuator_StampPusher : BOOL; END_VAR 
VAR  Actuator_StampSliderMovedIn : BOOL; END_VAR 
VAR  Actuator_StampSliderMovedOut : BOOL; END_VAR 
VAR  Actuator_StampWhiteLamp : BOOL; END_VAR 
VAR_INPUT  Crane$CraneDown : BOOL; END_VAR 
VAR_OUTPUT  Crane$CraneLower : BOOL; END_VAR 
VAR_INPUT  Crane$CraneOnConveyor : BOOL; END_VAR 
VAR_INPUT  Crane$CraneOnMagazin : BOOL; END_VAR 
VAR_INPUT  Crane$CranePositionStamp : BOOL; END_VAR 
VAR_INPUT  Crane$CraneSucked : BOOL; END_VAR 
VAR_OUTPUT  Crane$CraneTurnClockwise : BOOL; END_VAR 
VAR_OUTPUT  Crane$CraneTurnCounterclockwise : BOOL; END_VAR 
VAR_INPUT  Crane$CraneUp : BOOL; END_VAR 
VAR  Crane$Duration1 : UINT := UINT#375; END_VAR 
VAR_INPUT  Crane$MagazinCapacitiveSensor : BOOL; END_VAR 
VAR_OUTPUT  Crane$MagazinVacuumOff : BOOL; END_VAR 
VAR_OUTPUT  Crane$MagazinVacuumOn : BOOL; END_VAR 
VAR  Crane$SFCInit : BOOL; END_VAR 
VAR_INPUT  Crane$SFCReset : BOOL; END_VAR 
VAR_INPUT  Crane$SliderMovedOut : BOOL; END_VAR 
VAR_INPUT  Crane$SliderNotMovedOut : BOOL; END_VAR 
VAR_INPUT  Crane$StampLowered : BOOL; END_VAR 
VAR_INPUT  Crane$StampSliderFilled : BOOL; END_VAR 
VAR_INPUT  Crane$StartButtonMagazin : BOOL; END_VAR 
VAR_OUTPUT  Crane$StartCommandCrane : BOOL; END_VAR 
VAR_INPUT  Crane$StartVar : BOOL; END_VAR 
VAR_OUTPUT  Crane$TimeDelay_Timer$ET : USINT; END_VAR 
VAR_INPUT  Crane$TimeDelay_Timer$IN : BOOL; END_VAR 
VAR_INPUT  Crane$TimeDelay_Timer$PT : USINT; END_VAR 
VAR_OUTPUT  Crane$TimeDelay_Timer$Q : BOOL; END_VAR 
VAR  Crane$TimeDelay_Timer_Duration : UINT := UINT#12; END_VAR 
VAR  Crane$TimeDelay_Timer_interconnect : BOOL; END_VAR 
VAR_OUTPUT  Crane$Timer1$ET : USINT; END_VAR 
VAR_INPUT  Crane$Timer1$IN : BOOL; END_VAR 
VAR_INPUT  Crane$Timer1$PT : USINT; END_VAR 
VAR_OUTPUT  Crane$Timer1$Q : BOOL; END_VAR 
VAR_INPUT  Crane$WorkpieceReady : BOOL; END_VAR 
VAR  Crane$_state : Crane_states_t; END_VAR 
VAR  Crane$_transit : BOOL; END_VAR 
VAR  Crane$actualtime1 : INT; END_VAR 
VAR  Crane$interconnect : BOOL; END_VAR 
VAR  Crane$interconnectCraneStartCommand : BOOL; END_VAR 
VAR_INPUT  Mag$CraneDown : BOOL; END_VAR 
VAR_OUTPUT  Mag$CraneLower : BOOL; END_VAR 
VAR_INPUT  Mag$CraneOnConveyor : BOOL; END_VAR 
VAR_INPUT  Mag$CraneOnMagazin : BOOL; END_VAR 
VAR_INPUT  Mag$CraneSucked : BOOL; END_VAR 
VAR_OUTPUT  Mag$CraneTurnClockwise : BOOL; END_VAR 
VAR_OUTPUT  Mag$CraneTurnCounterclockwise : BOOL; END_VAR 
VAR_INPUT  Mag$CraneUp : BOOL; END_VAR 
VAR_OUTPUT  Mag$MagazinGreenLamp : BOOL; END_VAR 
VAR_OUTPUT  Mag$MagazinSlider : BOOL; END_VAR 
VAR_OUTPUT  Mag$MagazinVacuumOff : BOOL; END_VAR 
VAR_OUTPUT  Mag$MagazinVacuumOn : BOOL; END_VAR 
VAR_OUTPUT  Mag$MagazinWhiteLamp : BOOL; END_VAR 
VAR  Mag$SFCInit : BOOL; END_VAR 
VAR_INPUT  Mag$SFCReset : BOOL; END_VAR 
VAR_INPUT  Mag$SliderMovedOut : BOOL; END_VAR 
VAR_INPUT  Mag$SliderNotMovedOut : BOOL; END_VAR 
VAR_INPUT  Mag$StartButtonMagazin : BOOL; END_VAR 
VAR_OUTPUT  Mag$StartCommandMagazin : BOOL; END_VAR 
VAR_INPUT  Mag$StartVar : BOOL; END_VAR 
VAR_INPUT  Mag$WorkpieceReady : BOOL; END_VAR 
VAR  Mag$_state : Magazin_states_t; END_VAR 
VAR  Mag$_transit : BOOL; END_VAR 
VAR  Mag$interconnectMagazinStartCommand : BOOL; END_VAR 
VAR  Sensor_CraneDown : BOOL; END_VAR 
VAR  Sensor_CraneOnConveyor : BOOL; END_VAR 
VAR  Sensor_CraneOnMagazin : BOOL; END_VAR 
VAR  Sensor_CranePosition : BOOL; END_VAR 
VAR  Sensor_CranePositionStamp : BOOL; END_VAR 
VAR  Sensor_CraneSucked : BOOL; END_VAR 
VAR  Sensor_CraneUp : BOOL; END_VAR 
VAR  Sensor_MagazinCapacitiveSensor : BOOL; END_VAR 
VAR  Sensor_MagazinEmergencyStop : BOOL; END_VAR 
VAR  Sensor_MagazinOpticalSensor : BOOL; END_VAR 
VAR  Sensor_MagazinSwitchManuellAutomatic : BOOL; END_VAR 
VAR  Sensor_SliderMovedOut : BOOL; END_VAR 
VAR  Sensor_SliderNotMovedOut : BOOL; END_VAR 
VAR  Sensor_StampEmergencyStop : BOOL; END_VAR 
VAR  Sensor_StampLowered : BOOL; END_VAR 
VAR  Sensor_StampSliderFilled : BOOL; END_VAR 
VAR  Sensor_StampSliderSensorMovedIn : BOOL; END_VAR 
VAR  Sensor_StampSliderSensorMovedOut : BOOL; END_VAR 
VAR  Sensor_StampStartButton : BOOL; END_VAR 
VAR  Sensor_StampSwitchManuellAutomatic : BOOL; END_VAR 
VAR  Sensor_StampUp : BOOL; END_VAR 
VAR  Sensor_StartButtonMagazin : BOOL; END_VAR 
VAR  Sensor_WorkpieceReady : BOOL; END_VAR 
VAR_INPUT  Stamp$CraneDown : BOOL; END_VAR 
VAR_INPUT  Stamp$CraneOnConveyor : BOOL; END_VAR 
VAR_INPUT  Stamp$CranePositionStamp : BOOL; END_VAR 
VAR_INPUT  Stamp$CraneSucked : BOOL; END_VAR 
VAR_INPUT  Stamp$CraneUp : BOOL; END_VAR 
VAR  Stamp$Duration : UINT := UINT#125; END_VAR 
VAR  Stamp$SFCInit : BOOL; END_VAR 
VAR_INPUT  Stamp$SFCReset : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampGreenLamp : BOOL; END_VAR 
VAR_INPUT  Stamp$StampLowered : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampPressure : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampPusher : BOOL; END_VAR 
VAR_INPUT  Stamp$StampSliderFilled : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampSliderMovedIn : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampSliderMovedOut : BOOL; END_VAR 
VAR_INPUT  Stamp$StampSliderSensorMovedIn : BOOL; END_VAR 
VAR_INPUT  Stamp$StampSliderSensorMovedOut : BOOL; END_VAR 
VAR_INPUT  Stamp$StampStartButton : BOOL; END_VAR 
VAR_INPUT  Stamp$StampUp : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StampWhiteLamp : BOOL; END_VAR 
VAR_OUTPUT  Stamp$StartCommandStamp : BOOL; END_VAR 
VAR_INPUT  Stamp$StartVar : BOOL; END_VAR 
VAR_OUTPUT  Stamp$Timer$ET : USINT; END_VAR 
VAR_INPUT  Stamp$Timer$IN : BOOL; END_VAR 
VAR_INPUT  Stamp$Timer$PT : USINT; END_VAR 
VAR_OUTPUT  Stamp$Timer$Q : BOOL; END_VAR 
VAR  Stamp$_state : Stamp_states_t; END_VAR 
VAR  Stamp$_transit : BOOL; END_VAR 
VAR  Stamp$interconnect : BOOL; END_VAR 
VAR  Stamp$interconnectStampStartCommand : BOOL; END_VAR 
Mag$SliderNotMovedOut := Sensor_SliderNotMovedOut;
Mag$SliderMovedOut := Sensor_SliderMovedOut;
Mag$CraneOnMagazin := Sensor_CraneOnMagazin;
Mag$CraneDown := Sensor_CraneDown;
Mag$CraneUp := Sensor_CraneUp;
Mag$CraneOnConveyor := Sensor_CraneOnConveyor;
Mag$WorkpieceReady := Sensor_WorkpieceReady;
Mag$StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_MagazinSlider := Mag$MagazinSlider;
Actuator_MagazinGreenLamp := Mag$MagazinGreenLamp;
Crane$CraneUp := Sensor_CraneUp;
Crane$CraneOnConveyor := Sensor_CraneOnConveyor;
Crane$CraneDown := Sensor_CraneDown;
Crane$CraneSucked := Sensor_CraneSucked;
Crane$CraneOnMagazin := Sensor_CraneOnMagazin;
Crane$MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane$CranePositionStamp := Sensor_CranePositionStamp;
Crane$SliderMovedOut := Sensor_SliderMovedOut;
Crane$WorkpieceReady := Sensor_WorkpieceReady;
Crane$StampSliderFilled := Sensor_StampSliderFilled;
Crane$SliderMovedOut := Sensor_SliderMovedOut;
Crane$StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_CraneTurnCounterclockwise := Crane$CraneTurnCounterclockwise;
Actuator_CraneTurnClockwise := Crane$CraneTurnClockwise;
Actuator_CraneLower := Crane$CraneLower;
Actuator_MagazinVacuumOff := Crane$MagazinVacuumOff;
Actuator_MagazinVacuumOn := Crane$MagazinVacuumOn;
Stamp$StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Stamp$StampSliderSensorMovedIn := Sensor_StampSliderSensorMovedIn;
Stamp$StampSliderFilled := Sensor_StampSliderFilled;
Stamp$StampUp := Sensor_StampUp;
Stamp$StampLowered := Sensor_StampLowered;
Stamp$CraneDown := Sensor_CraneDown;
Stamp$CraneUp := Sensor_CraneUp;
Stamp$CraneSucked := Sensor_CraneSucked;
Stamp$CranePositionStamp := Sensor_CranePositionStamp;
Stamp$CraneOnConveyor := Sensor_CraneOnConveyor;
Stamp$StampStartButton := Sensor_StampStartButton;
Actuator_StampSliderMovedOut := Stamp$StampSliderMovedOut;
Actuator_StampSliderMovedIn := Stamp$StampSliderMovedIn;
Actuator_StampWhiteLamp := Stamp$StampWhiteLamp;
Actuator_StampPusher := Stamp$StampPusher;
Actuator_StampGreenLamp := Stamp$StampGreenLamp;
Actuator_AnalogCranePressure := INT#6000;
IF (Sensor_StampEmergencyStop AND Sensor_MagazinEmergencyStop) THEN
    CASE Mag$_state OF 
        Magazin_states_t#Green_Lamp:
            
            
            Mag$_transit := FALSE;
            
            
            Mag$MagazinGreenLamp := TRUE;
            Mag$interconnectMagazinStartCommand := FALSE;
            
            
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init;
            END_IF
            
            
            
            
        
        Magazin_states_t#Init:
            
            
            Mag$_transit := FALSE;
            
            
            
            
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Start_Magazin;
            END_IF
            
            
            
            
        
        Magazin_states_t#Interstep:
            
            
            Mag$_transit := FALSE;
            
            
            Mag$StartCommandMagazin := TRUE;
            
            
            IF Mag$StartVar THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#convey;
            END_IF
            
            
            
            
        
        Magazin_states_t#Magazin_Init:
            
            
            Mag$_transit := FALSE;
            
            
            Mag$MagazinSlider := TRUE;
            
            
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init_2;
            END_IF
            
            
            
            
        
        Magazin_states_t#Magazin_Init_2:
            
            
            Mag$_transit := FALSE;
            
            
            Mag$MagazinSlider := FALSE;
            
            
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF
            
            
            
            
        
        Magazin_states_t#Slider_Move_Back:
            
            
            Mag$_transit := FALSE;
            
            
            IF ((Mag$SliderMovedOut = TRUE) AND (Mag$SliderNotMovedOut = FALSE)) THEN
                Mag$MagazinSlider := FALSE;
            END_IF
            
            
            IF Mag$CraneUp THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step1;
            END_IF
            
            
            
            
        
        Magazin_states_t#Start_Magazin:
            
            
            Mag$_transit := FALSE;
            
            
            Mag$MagazinSlider := FALSE;
            Mag$MagazinGreenLamp := FALSE;
            Mag$StartVar := FALSE;
            Mag$StartCommandMagazin := FALSE;
            IF (Mag$StartButtonMagazin = TRUE) THEN
                Mag$interconnectMagazinStartCommand := TRUE;
            END_IF
            
            
            IF Mag$interconnectMagazinStartCommand THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Green_Lamp;
            END_IF
            
            
            
            
        
        Magazin_states_t#Step0:
            
            
            Mag$_transit := FALSE;
            
            
            
            
            IF Mag$CraneDown THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Slider_Move_Back;
            END_IF
            
            
            
            
        
        Magazin_states_t#Step1:
            
            
            Mag$_transit := FALSE;
            
            
            
            
            IF Mag$CraneOnConveyor THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF
            
            
            
            
        
        Magazin_states_t#convey:
            
            
            Mag$_transit := FALSE;
            
            
            IF Mag$SliderNotMovedOut THEN
                Mag$MagazinSlider := TRUE;
            END_IF
            
            
            IF Mag$CraneOnMagazin THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step0;
            END_IF
            
            
            
            
        
            END_CASE
    CASE Crane$_state OF 
        Crane_states_t#Crane_Go_Up:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#pause;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Init:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := TRUE;
            Crane$interconnectCraneStartCommand := FALSE;
            
            
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init_2;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Init_2:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Lift_At_Stamp:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Lift_Conveyor:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Lift_Magazin:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Lift_Magazin_Metallic:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            
            
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Lower:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := TRUE;
            
            
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step0;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_On_Conveyor:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            
            
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_On_Conveyor_Metallic:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            
            
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_On_Stamp_Metallic:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            
            
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release_Workpiece;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Turn_Left_From_Stamp:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            
            
            IF Crane$CraneOnConveyor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Turn_Left_Metallic:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            
            
            IF Crane$CranePositionStamp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF
            
            
            
            
        
        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            
            
            IF Crane$CraneOnConveyor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor;
            END_IF
            
            
            
            
        
        Crane_states_t#Init:
            
            
            Crane$_transit := FALSE;
            
            
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF
            
            
            
            
        
        Crane_states_t#Interstep:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$StartCommandCrane := TRUE;
            
            
            IF Crane$StartVar THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_2;
            END_IF
            
            
            
            
        
        Crane_states_t#Interstep_2:
            
            
            Crane$_transit := FALSE;
            
            
            
            
            IF Crane$SliderMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#TimeDelay;
            END_IF
            
            
            
            
        
        Crane_states_t#Interstep_Check_Workpiece:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterClockwise := FALSE;
            
            
            IF Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lower;
            ELSEIF (NOT Crane$WorkpieceReady AND NOT Crane$StampSliderFilled) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step2;
            ELSEIF (NOT Crane$WorkpieceReady AND Crane$StampSliderFilled) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Wait_At_Stamp;
            END_IF
            
            
            
            
        
        Crane_states_t#Lower_Crane:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := TRUE;
            
            
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Suck_At_Stamp;
            END_IF
            
            
            
            
        
        Crane_states_t#Reset_interconnect:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$interconnect := FALSE;
            Crane$Timer1$IN := FALSE;
            Crane$Timer1$PT := USINT#0;
            IF Crane$Timer1$IN THEN
                Crane$Timer1$Q := (Crane$Timer1$ET = USINT#0);
                IF (Crane$Timer1$ET > USINT#0) THEN
                    Crane$Timer1$ET := (Crane$Timer1$ET - USINT#1);
                ELSE
                    Crane$Timer1$ET := USINT#0;
                END_IF
            ELSE
                Crane$Timer1$Q := FALSE;
                Crane$Timer1$ET := Crane$Timer1$PT;
            END_IF
            
            
            IF Crane$SliderMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Lower_Crane;
            END_IF
            
            
            
            
        
        Crane_states_t#Start_Crane:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneLower := FALSE;
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$StartVar := FALSE;
            Crane$StartCommandCrane := FALSE;
            IF (Crane$StartButtonMagazin = TRUE) THEN
                Crane$interconnectCraneStartCommand := TRUE;
            END_IF
            
            
            IF Crane$interconnectCraneStartCommand THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init;
            END_IF
            
            
            
            
        
        Crane_states_t#Step0:
            
            
            Crane$_transit := FALSE;
            
            
            
            
            IF NOT Crane$MagazinCapacitiveSensor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazin;
            ELSEIF Crane$MagazinCapacitiveSensor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF
            
            
            
            
        
        Crane_states_t#Step2:
            
            
            Crane$_transit := FALSE;
            
            
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF
            
            
            
            
        
        Crane_states_t#Suck_At_Stamp:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            
            
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF
            
            
            
            
        
        Crane_states_t#TimeDelay:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$TimeDelay_Timer$IN := TRUE;
            Crane$TimeDelay_Timer$PT := Crane$TimeDelay_Timer_Duration;
            IF Crane$TimeDelay_Timer$IN THEN
                Crane$TimeDelay_Timer$Q := (Crane$TimeDelay_Timer$ET = USINT#0);
                IF (Crane$TimeDelay_Timer$ET > USINT#0) THEN
                    Crane$TimeDelay_Timer$ET := (Crane$TimeDelay_Timer$ET - USINT#1);
                ELSE
                    Crane$TimeDelay_Timer$ET := USINT#0;
                END_IF
            ELSE
                Crane$TimeDelay_Timer$Q := FALSE;
                Crane$TimeDelay_Timer$ET := Crane$TimeDelay_Timer$PT;
            END_IF
            Crane$TimeDelay_Timer_interconnect := Crane$TimeDelay_Timer$Q;
            
            
            IF Crane$TimeDelay_Timer_interconnect THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Turn_Right;
            END_IF
            
            
            
            
        
        Crane_states_t#Turn_Right:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            
            
            IF Crane$CraneOnMagazin THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_Check_Workpiece;
            END_IF
            
            
            
            
        
        Crane_states_t#Wait_At_Stamp:
            
            
            Crane$_transit := FALSE;
            
            
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#pause;
            END_IF
            
            
            
            
        
        Crane_states_t#pause:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$Timer1$IN := Crane$CraneUp;
            Crane$Timer1$PT := Crane$Duration1;
            IF Crane$Timer1$IN THEN
                Crane$Timer1$Q := (Crane$Timer1$ET = USINT#0);
                IF (Crane$Timer1$ET > USINT#0) THEN
                    Crane$Timer1$ET := (Crane$Timer1$ET - USINT#1);
                ELSE
                    Crane$Timer1$ET := USINT#0;
                END_IF
            ELSE
                Crane$Timer1$Q := FALSE;
                Crane$Timer1$ET := Crane$Timer1$PT;
            END_IF
            Crane$interconnect := Crane$Timer1$Q;
            
            
            IF Crane$interconnect THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Reset_interconnect;
            END_IF
            
            
            
            
        
        Crane_states_t#release:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Conveyor;
            END_IF
            
            
            
            
        
        Crane_states_t#release_Workpiece:
            
            
            Crane$_transit := FALSE;
            
            
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            
            
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Go_Up;
            END_IF
            
            
            
            
        
            END_CASE
    CASE Stamp$_state OF 
        Stamp_states_t#Green_Lamp:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampGreenLamp := TRUE;
            Stamp$interconnectStampStartCommand := FALSE;
            
            
            IF TRUE THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_1;
            END_IF
            
            
            
            
        
        Stamp_states_t#Init:
            
            
            Stamp$_transit := FALSE;
            
            
            
            
            IF TRUE THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Start_Stamp;
            END_IF
            
            
            
            
        
        Stamp_states_t#Interstep:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StartCommandStamp := TRUE;
            
            
            IF Stamp$StartVar THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Interstep_2;
            END_IF
            
            
            
            
        
        Stamp_states_t#Interstep_2:
            
            
            Stamp$_transit := FALSE;
            
            
            
            
            IF Stamp$StampSliderFilled THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step0;
            END_IF
            
            
            
            
        
        Stamp_states_t#StampProcess:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampPusher := TRUE;
            
            
            IF Stamp$StampLowered THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step1;
            END_IF
            
            
            
            
        
        Stamp_states_t#StampSliderBack:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampSliderMovedIn := TRUE;
            Stamp$StampSliderMovedOut := FALSE;
            
            
            IF Stamp$StampSliderSensorMovedIn THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampProcess;
            END_IF
            
            
            
            
        
        Stamp_states_t#StampSliderForward:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampPusher := FALSE;
            Stamp$StampSliderMovedOut := TRUE;
            IF ((Stamp$StampLowered = FALSE) AND (Stamp$StampUp = TRUE)) THEN
                Stamp$interconnect := FALSE;
            END_IF
            Stamp$Timer$IN := FALSE;
            Stamp$Timer$PT := USINT#0;
            IF Stamp$Timer$IN THEN
                Stamp$Timer$Q := (Stamp$Timer$ET = USINT#0);
                IF (Stamp$Timer$ET > USINT#0) THEN
                    Stamp$Timer$ET := (Stamp$Timer$ET - USINT#1);
                ELSE
                    Stamp$Timer$ET := USINT#0;
                END_IF
            ELSE
                Stamp$Timer$Q := FALSE;
                Stamp$Timer$ET := Stamp$Timer$PT;
            END_IF
            
            
            IF Stamp$StampSliderMovedOut THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step2;
            END_IF
            
            
            
            
        
        Stamp_states_t#Stamp_Init_1:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampSliderMovedIn := TRUE;
            Stamp$StampSliderMovedOut := FALSE;
            
            
            IF Stamp$StampSliderSensorMovedIn THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_2;
            END_IF
            
            
            
            
        
        Stamp_states_t#Stamp_Init_2:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampSliderMovedOut := TRUE;
            
            
            IF Stamp$StampSliderSensorMovedOut THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_3;
            END_IF
            
            
            
            
        
        Stamp_states_t#Stamp_Init_3:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampPusher := TRUE;
            
            
            IF Stamp$StampLowered THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_4;
            END_IF
            
            
            
            
        
        Stamp_states_t#Stamp_Init_4:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampPusher := FALSE;
            
            
            IF Stamp$StampUp THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Interstep;
            END_IF
            
            
            
            
        
        Stamp_states_t#Start_Stamp:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$StampSliderMovedOut := FALSE;
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampPusher := FALSE;
            Stamp$StampGreenLamp := FALSE;
            Stamp$StampPressure := FALSE;
            Stamp$StartCommandStamp := FALSE;
            IF (Stamp$StampStartButton = TRUE) THEN
                Stamp$interconnectStampStartCommand := TRUE;
            END_IF
            
            
            IF Stamp$interconnectStampStartCommand THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Green_Lamp;
            END_IF
            
            
            
            
        
        Stamp_states_t#Step0:
            
            
            Stamp$_transit := FALSE;
            
            
            
            
            IF Stamp$CraneUp THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampSliderBack;
            END_IF
            
            
            
            
        
        Stamp_states_t#Step1:
            
            
            Stamp$_transit := FALSE;
            
            
            Stamp$Timer$IN := Stamp$StampLowered;
            Stamp$Timer$PT := USINT#0;
            IF Stamp$Timer$IN THEN
                Stamp$Timer$Q := (Stamp$Timer$ET = USINT#0);
                IF (Stamp$Timer$ET > USINT#0) THEN
                    Stamp$Timer$ET := (Stamp$Timer$ET - USINT#1);
                ELSE
                    Stamp$Timer$ET := USINT#0;
                END_IF
            ELSE
                Stamp$Timer$Q := FALSE;
                Stamp$Timer$ET := Stamp$Timer$PT;
            END_IF
            Stamp$interconnect := Stamp$Timer$Q;
            
            
            IF Stamp$interconnect THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampSliderForward;
            END_IF
            
            
            
            
        
        Stamp_states_t#Step2:
            
            
            Stamp$_transit := FALSE;
            
            
            
            
            IF Stamp$CraneOnConveyor THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Interstep;
            END_IF
            
            
            
            
        
            END_CASE
    IF (Actuator_MagazinGreenLamp AND Actuator_StampGreenLamp) THEN
        IF ((Stamp$StartCommandStamp AND Crane$StartCommandCrane) AND Mag$StartCommandMagazin) THEN
            Crane$StartVar := TRUE;
            Mag$StartVar := TRUE;
            Stamp$StartVar := TRUE;
        END_IF
    END_IF
    Crane$SFCReset := FALSE;
    Mag$SFCReset := FALSE;
    Stamp$SFCReset := FALSE;
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
    Crane$SFCReset := TRUE;
    Mag$SFCReset := TRUE;
    Stamp$SFCReset := TRUE;
    Crane$StartVar := FALSE;
    Mag$StartVar := FALSE;
    Stamp$StartVar := FALSE;
END_IF
END_PROGRAM
