TYPE
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Stamp_states_t : (Green_Lamp , Init , Interstep , Interstep_2 , StampProcess , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 , Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);
    Crane_states_t : (Crane_Go_Up , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_Conveyor , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic , Crane_On_Stamp_Stop_Black , Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Init , Interstep , Interstep_2 , Last_Workpiece_At_Stamp , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , No_Workpiece_ready , Reset_interconnect , Start_Crane , Step0 , Suck_At_Stamp , TimeDelay , Turn_Right , Turn_Right_Black , pause , release , release_Black , release_Workpiece);
END_TYPE



PROGRAM product 
 
VAR_OUTPUT   a_Actuator_AnalogCranePressure  : INT; END_VAR
VAR_OUTPUT   a_Actuator_CraneLower  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_CraneTurnClockwise  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_CraneTurnCounterclockwise  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_MagazinGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_MagazinSlider  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_MagazinVacuumOff  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_MagazinVacuumOn  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_MagazinWhiteLamp  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampPusher  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampSliderMovedIn  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampSliderMovedOut  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampWhiteLamp  : BOOL; END_VAR
VAR   a_Crane$CranTurnClockwise  : BOOL; END_VAR
VAR   a_Crane$CraneDown  : BOOL; END_VAR
VAR   a_Crane$CraneLower  : BOOL; END_VAR
VAR   a_Crane$CraneOnConveyor  : BOOL; END_VAR
VAR   a_Crane$CraneOnMagazin  : BOOL; END_VAR
VAR   a_Crane$CranePositionStamp  : BOOL; END_VAR
VAR   a_Crane$CraneSucked  : BOOL; END_VAR
VAR   a_Crane$CraneTurnClockwise  : BOOL; END_VAR
VAR   a_Crane$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   a_Crane$CraneUp  : BOOL; END_VAR
VAR   a_Crane$Duration1  : UINT := UINT#5; END_VAR
VAR   a_Crane$MagazinCapacitiveSensor  : BOOL; END_VAR
VAR   a_Crane$MagazinSlider  : BOOL; END_VAR
VAR   a_Crane$MagazinVacuumOff  : BOOL; END_VAR
VAR   a_Crane$MagazinVacuumOn  : BOOL; END_VAR
VAR   a_Crane$SFCInit  : BOOL; END_VAR
VAR   a_Crane$SFCReset  : BOOL; END_VAR
VAR   a_Crane$SliderMovedOut  : BOOL; END_VAR
VAR   a_Crane$SliderNotMovedOut  : BOOL; END_VAR
VAR   a_Crane$StampLowered  : BOOL; END_VAR
VAR   a_Crane$StampSliderFilled  : BOOL; END_VAR
VAR   a_Crane$StartButtonMagazin  : BOOL; END_VAR
VAR   a_Crane$StartCommandCrane  : BOOL; END_VAR
VAR   a_Crane$StartVar  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer$ET  : USINT; END_VAR
VAR   a_Crane$TimeDelay_Timer$IN  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer$PT  : USINT; END_VAR
VAR   a_Crane$TimeDelay_Timer$Q  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer_Duration  : USINT  := USINT#12; END_VAR
VAR   a_Crane$TimeDelay_Timer_interconnect  : BOOL; END_VAR
VAR   a_Crane$Timer1$ET  : USINT; END_VAR
VAR   a_Crane$Timer1$IN  : BOOL; END_VAR
VAR   a_Crane$Timer1$PT  : USINT; END_VAR
VAR   a_Crane$Timer1$Q  : BOOL; END_VAR
VAR   a_Crane$WorkpieceReady  : BOOL; END_VAR
VAR   a_Crane$_state  : Crane_states_t; END_VAR
VAR   a_Crane$_transit  : BOOL; END_VAR
VAR   a_Crane$actualtime1  : INT; END_VAR
VAR   a_Crane$interconnect  : BOOL; END_VAR
VAR   a_Crane$interconnectCraneStartCommand  : BOOL; END_VAR
VAR   a_Mag$CraneDown  : BOOL; END_VAR
VAR   a_Mag$CraneLower  : BOOL; END_VAR
VAR   a_Mag$CraneOnConveyor  : BOOL; END_VAR
VAR   a_Mag$CraneOnMagazin  : BOOL; END_VAR
VAR   a_Mag$CraneSucked  : BOOL; END_VAR
VAR   a_Mag$CraneTurnClockwise  : BOOL; END_VAR
VAR   a_Mag$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   a_Mag$CraneUp  : BOOL; END_VAR
VAR   a_Mag$MagazinGreenLamp  : BOOL; END_VAR
VAR   a_Mag$MagazinSlider  : BOOL; END_VAR
VAR   a_Mag$MagazinVacuumOff  : BOOL; END_VAR
VAR   a_Mag$MagazinVacuumOn  : BOOL; END_VAR
VAR   a_Mag$MagazinWhiteLamp  : BOOL; END_VAR
VAR   a_Mag$SFCInit  : BOOL; END_VAR
VAR   a_Mag$SFCReset  : BOOL; END_VAR
VAR   a_Mag$SliderMovedOut  : BOOL; END_VAR
VAR   a_Mag$SliderNotMovedOut  : BOOL; END_VAR
VAR   a_Mag$StartButtonMagazin  : BOOL; END_VAR
VAR   a_Mag$StartCommandMagazin  : BOOL; END_VAR
VAR   a_Mag$StartVar  : BOOL; END_VAR
VAR   a_Mag$WorkpieceReady  : BOOL; END_VAR
VAR   a_Mag$_state  : Magazin_states_t; END_VAR
VAR   a_Mag$_transit  : BOOL; END_VAR
VAR   a_Mag$interconnectMagazinStartCommand  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CraneDown  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CraneOnConveyor  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CraneOnMagazin  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CranePosition  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CranePositionStamp  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CraneSucked  : BOOL; END_VAR
VAR_INPUT   a_Sensor_CraneUp  : BOOL; END_VAR
VAR_INPUT   a_Sensor_MagazinCapacitiveSensor  : BOOL; END_VAR
VAR_INPUT   a_Sensor_MagazinEmergencyStop  : BOOL; END_VAR
VAR_INPUT   a_Sensor_MagazinOpticalSensor  : BOOL; END_VAR
VAR_INPUT   a_Sensor_MagazinSwitchManuellAutomatic  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SliderMovedOut  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SliderNotMovedOut  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampEmergencyStop  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampLowered  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampSliderFilled  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampSliderSensorMovedIn  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampSliderSensorMovedOut  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampStartButton  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampSwitchManuellAutomatic  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StampUp  : BOOL; END_VAR
VAR_INPUT   a_Sensor_StartButtonMagazin  : BOOL; END_VAR
VAR_INPUT   a_Sensor_WorkpieceReady  : BOOL; END_VAR
VAR   a_Stamp$CraneDown  : BOOL; END_VAR
VAR   a_Stamp$CraneOnConveyor  : BOOL; END_VAR
VAR   a_Stamp$CranePositionStamp  : BOOL; END_VAR
VAR   a_Stamp$CraneSucked  : BOOL; END_VAR
VAR   a_Stamp$CraneUp  : BOOL; END_VAR
VAR   a_Stamp$Duration  : USINT  := USINT#15; END_VAR
VAR   a_Stamp$SFCInit  : BOOL; END_VAR
VAR   a_Stamp$SFCReset  : BOOL; END_VAR
VAR   a_Stamp$StampGreenLamp  : BOOL; END_VAR
VAR   a_Stamp$StampLowered  : BOOL; END_VAR
VAR   a_Stamp$StampPressure  : BOOL; END_VAR
VAR   a_Stamp$StampPusher  : BOOL; END_VAR
VAR   a_Stamp$StampSliderFilled  : BOOL; END_VAR
VAR   a_Stamp$StampSliderMovedIn  : BOOL; END_VAR
VAR   a_Stamp$StampSliderMovedOut  : BOOL; END_VAR
VAR   a_Stamp$StampSliderSensorMovedIn  : BOOL; END_VAR
VAR   a_Stamp$StampSliderSensorMovedOut  : BOOL; END_VAR
VAR   a_Stamp$StampStartButton  : BOOL; END_VAR
VAR   a_Stamp$StampUp  : BOOL; END_VAR
VAR   a_Stamp$StampWhiteLamp  : BOOL; END_VAR
VAR   a_Stamp$StartCommandStamp  : BOOL; END_VAR
VAR   a_Stamp$StartVar  : BOOL; END_VAR
VAR   a_Stamp$Timer$ET  : USINT; END_VAR
VAR   a_Stamp$Timer$IN  : BOOL; END_VAR
VAR   a_Stamp$Timer$PT  : USINT; END_VAR
VAR   a_Stamp$Timer$Q  : BOOL; END_VAR
VAR   a_Stamp$_state  : Stamp_states_t; END_VAR
VAR   a_Stamp$_transit  : BOOL; END_VAR
VAR   a_Stamp$interconnect  : BOOL; END_VAR
VAR   a_Stamp$interconnectStampStartCommand  : BOOL; END_VAR

VAR   a_DIAGNOSIS_ACTIVE  : BOOL; END_VAR
VAR_INPUT  a_PARAMETER_CRANE_PRESSURE  : INT := INT#6000; END_VAR



//--------------------------------------------------------------------------------


VAR_OUTPUT   b_Actuator_AnalogCranePressure  : INT; END_VAR
VAR_OUTPUT   b_Actuator_CraneLower  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_CraneTurnClockwise  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_CraneTurnCounterclockwise  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_MagazinGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_MagazinSlider  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_MagazinVacuumOff  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_MagazinVacuumOn  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_MagazinWhiteLamp  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampPusher  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampSliderMovedIn  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampSliderMovedOut  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampWhiteLamp  : BOOL; END_VAR
VAR   b_Crane$CranTurnClockwise  : BOOL; END_VAR
VAR   b_Crane$CraneDown  : BOOL; END_VAR
VAR   b_Crane$CraneLower  : BOOL; END_VAR
VAR   b_Crane$CraneOnConveyor  : BOOL; END_VAR
VAR   b_Crane$CraneOnMagazin  : BOOL; END_VAR
VAR   b_Crane$CranePositionStamp  : BOOL; END_VAR
VAR   b_Crane$CraneSucked  : BOOL; END_VAR
VAR   b_Crane$CraneTurnClockwise  : BOOL; END_VAR
VAR   b_Crane$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   b_Crane$CraneUp  : BOOL; END_VAR
VAR   b_Crane$Duration1  : UINT := UINT#5; END_VAR
VAR   b_Crane$MagazinCapacitiveSensor  : BOOL; END_VAR
VAR   b_Crane$MagazinSlider  : BOOL; END_VAR
VAR   b_Crane$MagazinVacuumOff  : BOOL; END_VAR
VAR   b_Crane$MagazinVacuumOn  : BOOL; END_VAR
VAR   b_Crane$SFCInit  : BOOL; END_VAR
VAR   b_Crane$SFCReset  : BOOL; END_VAR
VAR   b_Crane$SliderMovedOut  : BOOL; END_VAR
VAR   b_Crane$SliderNotMovedOut  : BOOL; END_VAR
VAR   b_Crane$StampLowered  : BOOL; END_VAR
VAR   b_Crane$StampSliderFilled  : BOOL; END_VAR
VAR   b_Crane$StartButtonMagazin  : BOOL; END_VAR
VAR   b_Crane$StartCommandCrane  : BOOL; END_VAR
VAR   b_Crane$StartVar  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer$ET  : USINT; END_VAR
VAR   b_Crane$TimeDelay_Timer$IN  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer$PT  : USINT; END_VAR
VAR   b_Crane$TimeDelay_Timer$Q  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer_Duration  : USINT  := USINT#12; END_VAR
VAR   b_Crane$TimeDelay_Timer_interconnect  : BOOL; END_VAR
VAR   b_Crane$Timer1$ET  : USINT; END_VAR
VAR   b_Crane$Timer1$IN  : BOOL; END_VAR
VAR   b_Crane$Timer1$PT  : USINT; END_VAR
VAR   b_Crane$Timer1$Q  : BOOL; END_VAR
VAR   b_Crane$WorkpieceReady  : BOOL; END_VAR
VAR   b_Crane$_state  : Crane_states_t; END_VAR
VAR   b_Crane$_transit  : BOOL; END_VAR
VAR   b_Crane$actualtime1  : INT; END_VAR
VAR   b_Crane$interconnect  : BOOL; END_VAR
VAR   b_Crane$interconnectCraneStartCommand  : BOOL; END_VAR
VAR   b_Mag$CraneDown  : BOOL; END_VAR
VAR   b_Mag$CraneLower  : BOOL; END_VAR
VAR   b_Mag$CraneOnConveyor  : BOOL; END_VAR
VAR   b_Mag$CraneOnMagazin  : BOOL; END_VAR
VAR   b_Mag$CraneSucked  : BOOL; END_VAR
VAR   b_Mag$CraneTurnClockwise  : BOOL; END_VAR
VAR   b_Mag$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   b_Mag$CraneUp  : BOOL; END_VAR
VAR   b_Mag$MagazinGreenLamp  : BOOL; END_VAR
VAR   b_Mag$MagazinSlider  : BOOL; END_VAR
VAR   b_Mag$MagazinVacuumOff  : BOOL; END_VAR
VAR   b_Mag$MagazinVacuumOn  : BOOL; END_VAR
VAR   b_Mag$MagazinWhiteLamp  : BOOL; END_VAR
VAR   b_Mag$SFCInit  : BOOL; END_VAR
VAR   b_Mag$SFCReset  : BOOL; END_VAR
VAR   b_Mag$SliderMovedOut  : BOOL; END_VAR
VAR   b_Mag$SliderNotMovedOut  : BOOL; END_VAR
VAR   b_Mag$StartButtonMagazin  : BOOL; END_VAR
VAR   b_Mag$StartCommandMagazin  : BOOL; END_VAR
VAR   b_Mag$StartVar  : BOOL; END_VAR
VAR   b_Mag$WorkpieceReady  : BOOL; END_VAR
VAR   b_Mag$_state  : Magazin_states_t; END_VAR
VAR   b_Mag$_transit  : BOOL; END_VAR
VAR   b_Mag$interconnectMagazinStartCommand  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CraneDown  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CraneOnConveyor  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CraneOnMagazin  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CranePosition  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CranePositionStamp  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CraneSucked  : BOOL; END_VAR
VAR_INPUT   b_Sensor_CraneUp  : BOOL; END_VAR
VAR_INPUT   b_Sensor_MagazinCapacitiveSensor  : BOOL; END_VAR
VAR_INPUT   b_Sensor_MagazinEmergencyStop  : BOOL; END_VAR
VAR_INPUT   b_Sensor_MagazinOpticalSensor  : BOOL; END_VAR
VAR_INPUT   b_Sensor_MagazinSwitchManuellAutomatic  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SliderMovedOut  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SliderNotMovedOut  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampEmergencyStop  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampLowered  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampSliderFilled  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampSliderSensorMovedIn  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampSliderSensorMovedOut  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampStartButton  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampSwitchManuellAutomatic  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StampUp  : BOOL; END_VAR
VAR_INPUT   b_Sensor_StartButtonMagazin  : BOOL; END_VAR
VAR_INPUT   b_Sensor_WorkpieceReady  : BOOL; END_VAR
VAR   b_Stamp$CraneDown  : BOOL; END_VAR
VAR   b_Stamp$CraneOnConveyor  : BOOL; END_VAR
VAR   b_Stamp$CranePositionStamp  : BOOL; END_VAR
VAR   b_Stamp$CraneSucked  : BOOL; END_VAR
VAR   b_Stamp$CraneUp  : BOOL; END_VAR
VAR   b_Stamp$Duration  : USINT  := USINT#15; END_VAR
VAR   b_Stamp$SFCInit  : BOOL; END_VAR
VAR   b_Stamp$SFCReset  : BOOL; END_VAR
VAR   b_Stamp$StampGreenLamp  : BOOL; END_VAR
VAR   b_Stamp$StampLowered  : BOOL; END_VAR
VAR   b_Stamp$StampPressure  : BOOL; END_VAR
VAR   b_Stamp$StampPusher  : BOOL; END_VAR
VAR   b_Stamp$StampSliderFilled  : BOOL; END_VAR
VAR   b_Stamp$StampSliderMovedIn  : BOOL; END_VAR
VAR   b_Stamp$StampSliderMovedOut  : BOOL; END_VAR
VAR   b_Stamp$StampSliderSensorMovedIn  : BOOL; END_VAR
VAR   b_Stamp$StampSliderSensorMovedOut  : BOOL; END_VAR
VAR   b_Stamp$StampStartButton  : BOOL; END_VAR
VAR   b_Stamp$StampUp  : BOOL; END_VAR
VAR   b_Stamp$StampWhiteLamp  : BOOL; END_VAR
VAR   b_Stamp$StartCommandStamp  : BOOL; END_VAR
VAR   b_Stamp$StartVar  : BOOL; END_VAR
VAR   b_Stamp$Timer$ET  : USINT; END_VAR
VAR   b_Stamp$Timer$IN  : BOOL; END_VAR
VAR   b_Stamp$Timer$PT  : USINT; END_VAR
VAR   b_Stamp$Timer$Q  : BOOL; END_VAR
VAR   b_Stamp$_state  : Stamp_states_t; END_VAR
VAR   b_Stamp$_transit  : BOOL; END_VAR
VAR   b_Stamp$interconnect  : BOOL; END_VAR
VAR   b_Stamp$interconnectStampStartCommand  : BOOL; END_VAR

VAR   b_DIAGNOSIS_ACTIVE  : BOOL; END_VAR
VAR_INPUT  b_PARAMETER_CRANE_PRESSURE  : INT := INT#6000; END_VAR

 
 a_Mag$SliderNotMovedOut  :=  a_Sensor_SliderNotMovedOut ;
 a_Mag$SliderMovedOut  :=  a_Sensor_SliderMovedOut ;
 a_Mag$CraneOnMagazin  :=  a_Sensor_CraneOnMagazin ;
 a_Mag$CraneDown  :=  a_Sensor_CraneDown ;
 a_Mag$CraneUp  :=  a_Sensor_CraneUp ;
 a_Mag$CraneOnConveyor  :=  a_Sensor_CraneOnConveyor ;
 a_Mag$WorkpieceReady  :=  a_Sensor_WorkpieceReady ;
 a_Mag$StartButtonMagazin  :=  a_Sensor_StartButtonMagazin ;
 a_Actuator_MagazinSlider  :=  a_Mag$MagazinSlider ;
 a_Actuator_MagazinGreenLamp  :=  a_Mag$MagazinGreenLamp ;
 a_Crane$CraneUp  :=  a_Sensor_CraneUp ;
 a_Crane$CraneOnConveyor  :=  a_Sensor_CraneOnConveyor ;
 a_Crane$CraneDown  :=  a_Sensor_CraneDown ;
 a_Crane$CraneSucked  :=  a_Sensor_CraneSucked ;
 a_Crane$CraneOnMagazin  :=  a_Sensor_CraneOnMagazin ;
 a_Crane$MagazinCapacitiveSensor  :=  a_Sensor_MagazinCapacitiveSensor ;
 a_Crane$CranePositionStamp  :=  a_Sensor_CranePositionStamp ;
 a_Crane$SliderMovedOut  :=  a_Sensor_SliderMovedOut ;
 a_Crane$WorkpieceReady  :=  a_Sensor_WorkpieceReady ;
 a_Crane$StampSliderFilled  :=  a_Sensor_StampSliderFilled ;
 a_Crane$StartButtonMagazin  :=  a_Sensor_StartButtonMagazin ;
 a_Actuator_CraneTurnCounterclockwise  :=  a_Crane$CraneTurnCounterclockwise ;
 a_Actuator_CraneTurnClockwise  :=  a_Crane$CraneTurnClockwise ;
 a_Actuator_CraneLower  :=  a_Crane$CraneLower ;
 a_Actuator_MagazinVacuumOff  :=  a_Crane$MagazinVacuumOff ;
 a_Actuator_MagazinVacuumOn  :=  a_Crane$MagazinVacuumOn ;
 a_Stamp$StampSliderSensorMovedOut  :=  a_Sensor_StampSliderSensorMovedOut ;
 a_Stamp$StampSliderSensorMovedIn  :=  a_Sensor_StampSliderSensorMovedIn ;
 a_Stamp$StampSliderFilled  :=  a_Sensor_StampSliderFilled ;
 a_Stamp$StampUp  :=  a_Sensor_StampUp ;
 a_Stamp$StampLowered  :=  a_Sensor_StampLowered ;
 a_Stamp$CraneDown  :=  a_Sensor_CraneDown ;
 a_Stamp$CraneUp  :=  a_Sensor_CraneUp ;
 a_Stamp$CraneSucked  :=  a_Sensor_CraneSucked ;
 a_Stamp$CranePositionStamp  :=  a_Sensor_CranePositionStamp ;
 a_Stamp$CraneOnConveyor  :=  a_Sensor_CraneOnConveyor ;
 a_Stamp$StampStartButton  :=  a_Sensor_StampStartButton ;
 a_Actuator_StampSliderMovedOut  :=  a_Stamp$StampSliderMovedOut ;
 a_Actuator_StampSliderMovedIn  :=  a_Stamp$StampSliderMovedIn ;
 a_Actuator_StampWhiteLamp  :=  a_Stamp$StampWhiteLamp ;
 a_Actuator_StampPusher  :=  a_Stamp$StampPusher ;
 a_Actuator_StampGreenLamp  :=  a_Stamp$StampGreenLamp ;
 a_Actuator_AnalogCranePressure  :=  a_PARAMETER_CRANE_PRESSURE ;

IF  a_DIAGNOSIS_ACTIVE  AND  a_Sensor_CraneSucked  AND
             ( a_Actuator_AnalogCranePressure  <= 0 OR  a_Actuator_AnalogCranePressure  > 10000) THEN
         a_Actuator_CraneTurnCounterclockwise  := FALSE;
         a_Actuator_CraneTurnClockwise  := FALSE;
END_IF



IF ( a_Sensor_StampEmergencyStop  AND  a_Sensor_MagazinEmergencyStop ) THEN
    CASE  a_Mag$_state  OF
        Magazin_states_t#Green_Lamp:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinGreenLamp  := TRUE;
             a_Mag$interconnectMagazinStartCommand  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Magazin_Init;
            END_IF;

        Magazin_states_t#Init:
             a_Mag$_transit  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Start_Magazin;
            END_IF;

        Magazin_states_t#Interstep:
             a_Mag$_transit  := FALSE;
             a_Mag$StartCommandMagazin  := TRUE;
            IF  a_Mag$StartVar  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#convey;
            END_IF;

        Magazin_states_t#Magazin_Init:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := TRUE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Magazin_Init_2;
            END_IF;

        Magazin_states_t#Magazin_Init_2:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Interstep;
            END_IF;

        Magazin_states_t#Slider_Move_Back:
             a_Mag$_transit  := FALSE;
            IF (( a_Mag$SliderMovedOut  = TRUE) AND ( a_Mag$SliderNotMovedOut  = FALSE)) THEN
                 a_Mag$MagazinSlider  := FALSE;
            END_IF;
            IF  a_Mag$CraneUp  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Step1;
            END_IF;

        Magazin_states_t#Start_Magazin:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := FALSE;
             a_Mag$MagazinGreenLamp  := FALSE;
             a_Mag$StartVar  := FALSE;
             a_Mag$StartCommandMagazin  := FALSE;
            IF ( a_Mag$StartButtonMagazin  = TRUE) THEN
                 a_Mag$interconnectMagazinStartCommand  := TRUE;
            END_IF;
            IF  a_Mag$interconnectMagazinStartCommand  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Green_Lamp;
            END_IF;

        Magazin_states_t#Step0:
             a_Mag$_transit  := FALSE;
            IF  a_Mag$CraneDown  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Slider_Move_Back;
            END_IF;

        Magazin_states_t#Step1:
             a_Mag$_transit  := FALSE;
            IF  a_Mag$CraneOnConveyor  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Interstep;
            END_IF;

        Magazin_states_t#convey:
             a_Mag$_transit  := FALSE;
            IF  a_Mag$SliderNotMovedOut  THEN
                 a_Mag$MagazinSlider  := TRUE;
            END_IF;
            IF  a_Mag$CraneOnMagazin  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Step0;
            END_IF;

            END_CASE
    CASE  a_Crane$_state  OF
        Crane_states_t#Crane_Go_Up:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF ( a_Crane$CraneUp  AND ( a_Crane$MagazinCapacitiveSensor  OR NOT  a_Crane$WorkpieceReady )) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#pause;
            ELSEIF (( a_Crane$CraneUp  AND NOT  a_Crane$MagazinCapacitiveSensor ) AND  a_Crane$WorkpieceReady ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Turn_Right_Black;
            END_IF;

        Crane_states_t#Crane_Init:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := TRUE;
             a_Crane$interconnectCraneStartCommand  := FALSE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Init_2;
            END_IF;

        Crane_states_t#Crane_Init_2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF;

        Crane_states_t#Crane_Lift_At_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF;

        Crane_states_t#Crane_Lift_Conveyor:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF;

        Crane_states_t#Crane_Lift_Conveyor_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF;

        Crane_states_t#Crane_Lift_Magazin:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF;

        Crane_states_t#Crane_Lift_Magazin_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF;

        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF;

        Crane_states_t#Crane_Lower:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step0;
            END_IF;

        Crane_states_t#Crane_On_Conveyor:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release;
            END_IF;

        Crane_states_t#Crane_On_Conveyor_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release;
            END_IF;

        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release_Black;
            END_IF;

        Crane_states_t#Crane_On_Stamp_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release_Workpiece;
            END_IF;

        Crane_states_t#Crane_On_Stamp_Stop_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF;

        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF  a_Crane$CranePositionStamp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF;

        Crane_states_t#Crane_Turn_Left_From_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  a_Crane$CraneOnConveyor  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF;

        Crane_states_t#Crane_Turn_Left_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF  a_Crane$CranePositionStamp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF;

        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF  a_Crane$CraneOnConveyor  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor;
            END_IF;

        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF  a_Crane$CraneOnConveyor  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF;

        Crane_states_t#Init:
             a_Crane$_transit  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF;

        Crane_states_t#Interstep:
             a_Crane$_transit  := FALSE;
             a_Crane$StartCommandCrane  := TRUE;
            IF  a_Crane$StartVar  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep_2;
            END_IF;

        Crane_states_t#Interstep_2:
             a_Crane$_transit  := FALSE;
            IF  a_Crane$SliderMovedOut  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#TimeDelay;
            END_IF;

        Crane_states_t#Last_Workpiece_At_Stamp:
             a_Crane$_transit  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#pause;
            END_IF;

        Crane_states_t#Lower_Crane:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Suck_At_Stamp;
            END_IF;

        Crane_states_t#Magazin_Stop:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  a_Crane$WorkpieceReady  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lower;
            ELSEIF (NOT  a_Crane$WorkpieceReady  AND NOT  a_Crane$StampSliderFilled ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#No_Workpiece_ready;
            ELSEIF (NOT  a_Crane$WorkpieceReady  AND  a_Crane$StampSliderFilled ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Last_Workpiece_At_Stamp;
            END_IF;

        Crane_states_t#Magazin_Stop_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_NOT_Metallic_Black;
            END_IF;

        Crane_states_t#No_Workpiece_ready:
             a_Crane$_transit  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF;

        Crane_states_t#Reset_interconnect:
             a_Crane$_transit  := FALSE;
             a_Crane$interconnect  := FALSE;
             a_Crane$Timer1$IN  := FALSE;
             a_Crane$Timer1$PT  := USINT#0;
            IF  a_Crane$Timer1$IN  THEN
                 a_Crane$Timer1$Q  := ( a_Crane$Timer1$ET  = USINT#0);
                IF ( a_Crane$Timer1$ET  > USINT#0) THEN
                     a_Crane$Timer1$ET  := ( a_Crane$Timer1$ET  - USINT#1);
                ELSE
                     a_Crane$Timer1$ET  := USINT#0;
                END_IF;
            ELSE
                 a_Crane$Timer1$Q  := FALSE;
                 a_Crane$Timer1$ET  :=  a_Crane$Timer1$PT ;
            END_IF;
            IF  a_Crane$SliderMovedOut  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Lower_Crane;
            END_IF;

        Crane_states_t#Start_Crane:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$StartVar  := FALSE;
             a_Crane$StartCommandCrane  := FALSE;
            IF ( a_Crane$StartButtonMagazin  = TRUE) THEN
                 a_Crane$interconnectCraneStartCommand  := TRUE;
            END_IF;
            IF  a_Crane$interconnectCraneStartCommand  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Init;
            END_IF;

        Crane_states_t#Step0:
             a_Crane$_transit  := FALSE;
            IF NOT  a_Crane$MagazinCapacitiveSensor  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Magazin;
            ELSEIF  a_Crane$MagazinCapacitiveSensor  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF;

        Crane_states_t#Suck_At_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF;

        Crane_states_t#TimeDelay:
             a_Crane$_transit  := FALSE;
             a_Crane$TimeDelay_Timer$IN  := TRUE;
             a_Crane$TimeDelay_Timer$PT  :=  a_Crane$TimeDelay_Timer_Duration ;
            IF  a_Crane$TimeDelay_Timer$IN  THEN
                 a_Crane$TimeDelay_Timer$Q  := ( a_Crane$TimeDelay_Timer$ET  = USINT#0);
                IF ( a_Crane$TimeDelay_Timer$ET  > USINT#0) THEN
                     a_Crane$TimeDelay_Timer$ET  := ( a_Crane$TimeDelay_Timer$ET  - USINT#1);
                ELSE
                     a_Crane$TimeDelay_Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 a_Crane$TimeDelay_Timer$Q  := FALSE;
                 a_Crane$TimeDelay_Timer$ET  :=  a_Crane$TimeDelay_Timer$PT ;
            END_IF;
             a_Crane$TimeDelay_Timer_interconnect  :=  a_Crane$TimeDelay_Timer$Q ;
            IF  a_Crane$TimeDelay_Timer_interconnect  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Turn_Right;
            END_IF;

        Crane_states_t#Turn_Right:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  a_Crane$CraneOnMagazin  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Magazin_Stop;
            END_IF;

        Crane_states_t#Turn_Right_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  a_Crane$CraneOnMagazin  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Magazin_Stop_Black;
            END_IF;

        Crane_states_t#pause:
             a_Crane$_transit  := FALSE;
             a_Crane$Timer1$IN  :=  a_Crane$CraneUp ;
             a_Crane$Timer1$PT  :=  a_Crane$Duration1 ;
            IF  a_Crane$Timer1$IN  THEN
                 a_Crane$Timer1$Q  := ( a_Crane$Timer1$ET  = USINT#0);
                IF ( a_Crane$Timer1$ET  > USINT#0) THEN
                     a_Crane$Timer1$ET  := ( a_Crane$Timer1$ET  - USINT#1);
                ELSE
                     a_Crane$Timer1$ET  := USINT#0;
                END_IF;
            ELSE
                 a_Crane$Timer1$Q  := FALSE;
                 a_Crane$Timer1$ET  :=  a_Crane$Timer1$PT ;
            END_IF;
             a_Crane$interconnect  :=  a_Crane$Timer1$Q ;
            IF  a_Crane$interconnect  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF;

        Crane_states_t#release:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor;
            END_IF;

        Crane_states_t#release_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF;

        Crane_states_t#release_Workpiece:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Go_Up;
            END_IF;

            END_CASE
    CASE  a_Stamp$_state  OF
        Stamp_states_t#Green_Lamp:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampGreenLamp  := TRUE;
             a_Stamp$interconnectStampStartCommand  := FALSE;
            IF TRUE THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_1;
            END_IF;

        Stamp_states_t#Init:
             a_Stamp$_transit  := FALSE;
            IF TRUE THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Start_Stamp;
            END_IF;

        Stamp_states_t#Interstep:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StartCommandStamp  := TRUE;
            IF  a_Stamp$StartVar  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Interstep_2;
            END_IF;

        Stamp_states_t#Interstep_2:
             a_Stamp$_transit  := FALSE;
            IF  a_Stamp$StampSliderFilled  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step0;
            END_IF;

        Stamp_states_t#StampProcess:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := FALSE;
             a_Stamp$StampPusher  := TRUE;
            IF  a_Stamp$StampLowered  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step1;
            END_IF;

        Stamp_states_t#StampSliderBack:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := TRUE;
             a_Stamp$StampSliderMovedOut  := FALSE;
            IF  a_Stamp$StampSliderSensorMovedIn  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampProcess;
            END_IF;

        Stamp_states_t#StampSliderForward:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := FALSE;
             a_Stamp$StampSliderMovedOut  := TRUE;
            IF (( a_Stamp$StampLowered  = FALSE) AND ( a_Stamp$StampUp  = TRUE)) THEN
                 a_Stamp$interconnect  := FALSE;
            END_IF;
             a_Stamp$Timer$IN  := FALSE;
             a_Stamp$Timer$PT  := USINT#0;
            IF  a_Stamp$Timer$IN  THEN
                 a_Stamp$Timer$Q  := ( a_Stamp$Timer$ET  = USINT#0);
                IF ( a_Stamp$Timer$ET  > USINT#0) THEN
                     a_Stamp$Timer$ET  := ( a_Stamp$Timer$ET  - USINT#1);
                ELSE
                     a_Stamp$Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 a_Stamp$Timer$Q  := FALSE;
                 a_Stamp$Timer$ET  :=  a_Stamp$Timer$PT ;
            END_IF;
            IF  a_Stamp$StampSliderMovedOut  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step2;
            END_IF;

        Stamp_states_t#Stamp_Init_1:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := TRUE;
             a_Stamp$StampSliderMovedOut  := FALSE;
            IF  a_Stamp$StampSliderSensorMovedIn  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_2;
            END_IF;

        Stamp_states_t#Stamp_Init_2:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := FALSE;
             a_Stamp$StampSliderMovedOut  := TRUE;
            IF  a_Stamp$StampSliderSensorMovedOut  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_3;
            END_IF;

        Stamp_states_t#Stamp_Init_3:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := TRUE;
            IF  a_Stamp$StampLowered  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_4;
            END_IF;

        Stamp_states_t#Stamp_Init_4:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := FALSE;
            IF  a_Stamp$StampUp  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF;

        Stamp_states_t#Start_Stamp:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedOut  := FALSE;
             a_Stamp$StampSliderMovedIn  := FALSE;
             a_Stamp$StampPusher  := FALSE;
             a_Stamp$StampGreenLamp  := FALSE;
             a_Stamp$StampPressure  := FALSE;
             a_Stamp$StartCommandStamp  := FALSE;
            IF ( a_Stamp$StampStartButton  = TRUE) THEN
                 a_Stamp$interconnectStampStartCommand  := TRUE;
            END_IF;
            IF  a_Stamp$interconnectStampStartCommand  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Green_Lamp;
            END_IF;

        Stamp_states_t#Step0:
             a_Stamp$_transit  := FALSE;
            IF  a_Stamp$CraneUp  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampSliderBack;
            END_IF;

        Stamp_states_t#Step1:
             a_Stamp$_transit  := FALSE;
             a_Stamp$Timer$IN  :=  a_Stamp$StampLowered ;
             a_Stamp$Timer$PT  := USINT#0;
            IF  a_Stamp$Timer$IN  THEN
                 a_Stamp$Timer$Q  := ( a_Stamp$Timer$ET  = USINT#0);
                IF ( a_Stamp$Timer$ET  > USINT#0) THEN
                     a_Stamp$Timer$ET  := ( a_Stamp$Timer$ET  - USINT#1);
                ELSE
                     a_Stamp$Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 a_Stamp$Timer$Q  := FALSE;
                 a_Stamp$Timer$ET  :=  a_Stamp$Timer$PT ;
            END_IF;
             a_Stamp$interconnect  :=  a_Stamp$Timer$Q ;
            IF  a_Stamp$interconnect  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampSliderForward;
            END_IF;

        Stamp_states_t#Step2:
             a_Stamp$_transit  := FALSE;
            IF ( a_Stamp$CraneOnConveyor  AND NOT  a_Stamp$StampSliderFilled ) THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF;

            END_CASE
    IF ( a_Actuator_MagazinGreenLamp  AND  a_Actuator_StampGreenLamp ) THEN
        IF (( a_Stamp$StartCommandStamp  AND  a_Crane$StartCommandCrane ) AND  a_Mag$StartCommandMagazin ) THEN
             a_Crane$StartVar  := TRUE;
             a_Mag$StartVar  := TRUE;
             a_Stamp$StartVar  := TRUE;
             a_DIAGNOSIS_ACTIVE  := TRUE;
        END_IF;
    END_IF;
     a_Crane$SFCReset  := FALSE;
     a_Mag$SFCReset  := FALSE;
     a_Stamp$SFCReset  := FALSE;
ELSEIF (NOT  a_Sensor_StampEmergencyStop  OR NOT  a_Sensor_MagazinEmergencyStop ) THEN
     a_Actuator_MagazinSlider  := FALSE;
     a_Actuator_CraneLower  := FALSE;
     a_Actuator_MagazinVacuumOn  := FALSE;
     a_Actuator_MagazinVacuumOff  := TRUE;
     a_Actuator_MagazinGreenLamp  := FALSE;
     a_Actuator_CraneTurnCounterclockwise  := FALSE;
     a_Actuator_CraneTurnClockwise  := FALSE;
     a_Actuator_StampSliderMovedOut  := TRUE;
     a_Actuator_StampSliderMovedIn  := FALSE;
     a_Actuator_StampGreenLamp  := FALSE;
     a_Actuator_StampPusher  := FALSE;
     a_Actuator_AnalogCranePressure  := INT#0;
     a_Crane$SFCReset  := TRUE;
     a_Mag$SFCReset  := TRUE;
     a_Stamp$SFCReset  := TRUE;
     a_Crane$StartVar  := FALSE;
     a_Mag$StartVar  := FALSE;
     a_Stamp$StartVar  := FALSE;
END_IF



//--------------------------------------------------------------------------------


 b_Mag$SliderNotMovedOut  :=  b_Sensor_SliderNotMovedOut ;
 b_Mag$SliderMovedOut  :=  b_Sensor_SliderMovedOut ;
 b_Mag$CraneOnMagazin  :=  b_Sensor_CraneOnMagazin ;
 b_Mag$CraneDown  :=  b_Sensor_CraneDown ;
 b_Mag$CraneUp  :=  b_Sensor_CraneUp ;
 b_Mag$CraneOnConveyor  :=  b_Sensor_CraneOnConveyor ;
 b_Mag$WorkpieceReady  :=  b_Sensor_WorkpieceReady ;
 b_Mag$StartButtonMagazin  :=  b_Sensor_StartButtonMagazin ;
 b_Actuator_MagazinSlider  :=  b_Mag$MagazinSlider ;
 b_Actuator_MagazinGreenLamp  :=  b_Mag$MagazinGreenLamp ;
 b_Crane$CraneUp  :=  b_Sensor_CraneUp ;
 b_Crane$CraneOnConveyor  :=  b_Sensor_CraneOnConveyor ;
 b_Crane$CraneDown  :=  b_Sensor_CraneDown ;
 b_Crane$CraneSucked  :=  b_Sensor_CraneSucked ;
 b_Crane$CraneOnMagazin  :=  b_Sensor_CraneOnMagazin ;
 b_Crane$MagazinCapacitiveSensor  :=  b_Sensor_MagazinCapacitiveSensor ;
 b_Crane$CranePositionStamp  :=  b_Sensor_CranePositionStamp ;
 b_Crane$SliderMovedOut  :=  b_Sensor_SliderMovedOut ;
 b_Crane$WorkpieceReady  :=  b_Sensor_WorkpieceReady ;
 b_Crane$StampSliderFilled  :=  b_Sensor_StampSliderFilled ;
 b_Crane$StartButtonMagazin  :=  b_Sensor_StartButtonMagazin ;
 b_Actuator_CraneTurnCounterclockwise  :=  b_Crane$CraneTurnCounterclockwise ;
 b_Actuator_CraneTurnClockwise  :=  b_Crane$CraneTurnClockwise ;
 b_Actuator_CraneLower  :=  b_Crane$CraneLower ;
 b_Actuator_MagazinVacuumOff  :=  b_Crane$MagazinVacuumOff ;
 b_Actuator_MagazinVacuumOn  :=  b_Crane$MagazinVacuumOn ;
 b_Stamp$StampSliderSensorMovedOut  :=  b_Sensor_StampSliderSensorMovedOut ;
 b_Stamp$StampSliderSensorMovedIn  :=  b_Sensor_StampSliderSensorMovedIn ;
 b_Stamp$StampSliderFilled  :=  b_Sensor_StampSliderFilled ;
 b_Stamp$StampUp  :=  b_Sensor_StampUp ;
 b_Stamp$StampLowered  :=  b_Sensor_StampLowered ;
 b_Stamp$CraneDown  :=  b_Sensor_CraneDown ;
 b_Stamp$CraneUp  :=  b_Sensor_CraneUp ;
 b_Stamp$CraneSucked  :=  b_Sensor_CraneSucked ;
 b_Stamp$CranePositionStamp  :=  b_Sensor_CranePositionStamp ;
 b_Stamp$CraneOnConveyor  :=  b_Sensor_CraneOnConveyor ;
 b_Stamp$StampStartButton  :=  b_Sensor_StampStartButton ;
 b_Actuator_StampSliderMovedOut  :=  b_Stamp$StampSliderMovedOut ;
 b_Actuator_StampSliderMovedIn  :=  b_Stamp$StampSliderMovedIn ;
 b_Actuator_StampWhiteLamp  :=  b_Stamp$StampWhiteLamp ;
 b_Actuator_StampPusher  :=  b_Stamp$StampPusher ;
 b_Actuator_StampGreenLamp  :=  b_Stamp$StampGreenLamp ;
 b_Actuator_AnalogCranePressure  :=  b_PARAMETER_CRANE_PRESSURE ;

IF  b_DIAGNOSIS_ACTIVE  AND  b_Sensor_CraneSucked  AND
             ( b_Actuator_AnalogCranePressure  <= 0 OR  b_Actuator_AnalogCranePressure  > 10000) THEN
         b_Actuator_CraneTurnCounterclockwise  := FALSE;
         b_Actuator_CraneTurnClockwise  := FALSE;
END_IF



IF ( b_Sensor_StampEmergencyStop  AND  b_Sensor_MagazinEmergencyStop ) THEN
    CASE  b_Mag$_state  OF
        Magazin_states_t#Green_Lamp:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinGreenLamp  := TRUE;
             b_Mag$interconnectMagazinStartCommand  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Magazin_Init;
            END_IF;

        Magazin_states_t#Init:
             b_Mag$_transit  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Start_Magazin;
            END_IF;

        Magazin_states_t#Interstep:
             b_Mag$_transit  := FALSE;
             b_Mag$StartCommandMagazin  := TRUE;
            IF  b_Mag$StartVar  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#convey;
            END_IF;

        Magazin_states_t#Magazin_Init:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := TRUE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Magazin_Init_2;
            END_IF;

        Magazin_states_t#Magazin_Init_2:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Interstep;
            END_IF;

        Magazin_states_t#Slider_Move_Back:
             b_Mag$_transit  := FALSE;
            IF (( b_Mag$SliderMovedOut  = TRUE) AND ( b_Mag$SliderNotMovedOut  = FALSE)) THEN
                 b_Mag$MagazinSlider  := FALSE;
            END_IF;
            IF  b_Mag$CraneUp  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Step1;
            END_IF;

        Magazin_states_t#Start_Magazin:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := FALSE;
             b_Mag$MagazinGreenLamp  := FALSE;
             b_Mag$StartVar  := FALSE;
             b_Mag$StartCommandMagazin  := FALSE;
            IF ( b_Mag$StartButtonMagazin  = TRUE) THEN
                 b_Mag$interconnectMagazinStartCommand  := TRUE;
            END_IF;
            IF  b_Mag$interconnectMagazinStartCommand  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Green_Lamp;
            END_IF;

        Magazin_states_t#Step0:
             b_Mag$_transit  := FALSE;
            IF  b_Mag$CraneDown  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Slider_Move_Back;
            END_IF;

        Magazin_states_t#Step1:
             b_Mag$_transit  := FALSE;
            IF  b_Mag$CraneOnConveyor  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Interstep;
            END_IF;

        Magazin_states_t#convey:
             b_Mag$_transit  := FALSE;
            IF  b_Mag$SliderNotMovedOut  THEN
                 b_Mag$MagazinSlider  := TRUE;
            END_IF;
            IF  b_Mag$CraneOnMagazin  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Step0;
            END_IF;

            END_CASE
    CASE  b_Crane$_state  OF
        Crane_states_t#Crane_Go_Up:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF ( b_Crane$CraneUp  AND ( b_Crane$MagazinCapacitiveSensor  OR NOT  b_Crane$WorkpieceReady )) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#pause;
            ELSEIF (( b_Crane$CraneUp  AND NOT  b_Crane$MagazinCapacitiveSensor ) AND  b_Crane$WorkpieceReady ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Turn_Right_Black;
            END_IF;

        Crane_states_t#Crane_Init:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := TRUE;
             b_Crane$interconnectCraneStartCommand  := FALSE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Init_2;
            END_IF;

        Crane_states_t#Crane_Init_2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF;

        Crane_states_t#Crane_Lift_At_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF;

        Crane_states_t#Crane_Lift_Conveyor:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF;

        Crane_states_t#Crane_Lift_Conveyor_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF;

        Crane_states_t#Crane_Lift_Magazin:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF;

        Crane_states_t#Crane_Lift_Magazin_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF;

        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF;

        Crane_states_t#Crane_Lower:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step0;
            END_IF;

        Crane_states_t#Crane_On_Conveyor:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release;
            END_IF;

        Crane_states_t#Crane_On_Conveyor_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release;
            END_IF;

        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release_Black;
            END_IF;

        Crane_states_t#Crane_On_Stamp_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release_Workpiece;
            END_IF;

        Crane_states_t#Crane_On_Stamp_Stop_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF;

        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF  b_Crane$CranePositionStamp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF;

        Crane_states_t#Crane_Turn_Left_From_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  b_Crane$CraneOnConveyor  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF;

        Crane_states_t#Crane_Turn_Left_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF  b_Crane$CranePositionStamp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF;

        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF  b_Crane$CraneOnConveyor  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor;
            END_IF;

        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF  b_Crane$CraneOnConveyor  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF;

        Crane_states_t#Init:
             b_Crane$_transit  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF;

        Crane_states_t#Interstep:
             b_Crane$_transit  := FALSE;
             b_Crane$StartCommandCrane  := TRUE;
            IF  b_Crane$StartVar  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep_2;
            END_IF;

        Crane_states_t#Interstep_2:
             b_Crane$_transit  := FALSE;
            IF  b_Crane$SliderMovedOut  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#TimeDelay;
            END_IF;

        Crane_states_t#Last_Workpiece_At_Stamp:
             b_Crane$_transit  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#pause;
            END_IF;

        Crane_states_t#Lower_Crane:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Suck_At_Stamp;
            END_IF;

        Crane_states_t#Magazin_Stop:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  b_Crane$WorkpieceReady  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lower;
            ELSEIF (NOT  b_Crane$WorkpieceReady  AND NOT  b_Crane$StampSliderFilled ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#No_Workpiece_ready;
            ELSEIF (NOT  b_Crane$WorkpieceReady  AND  b_Crane$StampSliderFilled ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Last_Workpiece_At_Stamp;
            END_IF;

        Crane_states_t#Magazin_Stop_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_NOT_Metallic_Black;
            END_IF;

        Crane_states_t#No_Workpiece_ready:
             b_Crane$_transit  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF;

        Crane_states_t#Reset_interconnect:
             b_Crane$_transit  := FALSE;
             b_Crane$interconnect  := FALSE;
             b_Crane$Timer1$IN  := FALSE;
             b_Crane$Timer1$PT  := USINT#0;
            IF  b_Crane$Timer1$IN  THEN
                 b_Crane$Timer1$Q  := ( b_Crane$Timer1$ET  = USINT#0);
                IF ( b_Crane$Timer1$ET  > USINT#0) THEN
                     b_Crane$Timer1$ET  := ( b_Crane$Timer1$ET  - USINT#1);
                ELSE
                     b_Crane$Timer1$ET  := USINT#0;
                END_IF;
            ELSE
                 b_Crane$Timer1$Q  := FALSE;
                 b_Crane$Timer1$ET  :=  b_Crane$Timer1$PT ;
            END_IF;
            IF  b_Crane$SliderMovedOut  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Lower_Crane;
            END_IF;

        Crane_states_t#Start_Crane:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$StartVar  := FALSE;
             b_Crane$StartCommandCrane  := FALSE;
            IF ( b_Crane$StartButtonMagazin  = TRUE) THEN
                 b_Crane$interconnectCraneStartCommand  := TRUE;
            END_IF;
            IF  b_Crane$interconnectCraneStartCommand  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Init;
            END_IF;

        Crane_states_t#Step0:
             b_Crane$_transit  := FALSE;
            IF NOT  b_Crane$MagazinCapacitiveSensor  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Magazin;
            ELSEIF  b_Crane$MagazinCapacitiveSensor  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF;

        Crane_states_t#Suck_At_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF;

        Crane_states_t#TimeDelay:
             b_Crane$_transit  := FALSE;
             b_Crane$TimeDelay_Timer$IN  := TRUE;
             b_Crane$TimeDelay_Timer$PT  :=  b_Crane$TimeDelay_Timer_Duration ;
            IF  b_Crane$TimeDelay_Timer$IN  THEN
                 b_Crane$TimeDelay_Timer$Q  := ( b_Crane$TimeDelay_Timer$ET  = USINT#0);
                IF ( b_Crane$TimeDelay_Timer$ET  > USINT#0) THEN
                     b_Crane$TimeDelay_Timer$ET  := ( b_Crane$TimeDelay_Timer$ET  - USINT#1);
                ELSE
                     b_Crane$TimeDelay_Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 b_Crane$TimeDelay_Timer$Q  := FALSE;
                 b_Crane$TimeDelay_Timer$ET  :=  b_Crane$TimeDelay_Timer$PT ;
            END_IF;
             b_Crane$TimeDelay_Timer_interconnect  :=  b_Crane$TimeDelay_Timer$Q ;
            IF  b_Crane$TimeDelay_Timer_interconnect  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Turn_Right;
            END_IF;

        Crane_states_t#Turn_Right:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  b_Crane$CraneOnMagazin  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Magazin_Stop;
            END_IF;

        Crane_states_t#Turn_Right_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF  b_Crane$CraneOnMagazin  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Magazin_Stop_Black;
            END_IF;

        Crane_states_t#pause:
             b_Crane$_transit  := FALSE;
             b_Crane$Timer1$IN  :=  b_Crane$CraneUp ;
             b_Crane$Timer1$PT  :=  b_Crane$Duration1 ;
            IF  b_Crane$Timer1$IN  THEN
                 b_Crane$Timer1$Q  := ( b_Crane$Timer1$ET  = USINT#0);
                IF ( b_Crane$Timer1$ET  > USINT#0) THEN
                     b_Crane$Timer1$ET  := ( b_Crane$Timer1$ET  - USINT#1);
                ELSE
                     b_Crane$Timer1$ET  := USINT#0;
                END_IF;
            ELSE
                 b_Crane$Timer1$Q  := FALSE;
                 b_Crane$Timer1$ET  :=  b_Crane$Timer1$PT ;
            END_IF;
             b_Crane$interconnect  :=  b_Crane$Timer1$Q ;
            IF  b_Crane$interconnect  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF;

        Crane_states_t#release:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor;
            END_IF;

        Crane_states_t#release_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF;

        Crane_states_t#release_Workpiece:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Go_Up;
            END_IF;

            END_CASE
    CASE  b_Stamp$_state  OF
        Stamp_states_t#Green_Lamp:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampGreenLamp  := TRUE;
             b_Stamp$interconnectStampStartCommand  := FALSE;
            IF TRUE THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_1;
            END_IF;

        Stamp_states_t#Init:
             b_Stamp$_transit  := FALSE;
            IF TRUE THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Start_Stamp;
            END_IF;

        Stamp_states_t#Interstep:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StartCommandStamp  := TRUE;
            IF  b_Stamp$StartVar  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Interstep_2;
            END_IF;

        Stamp_states_t#Interstep_2:
             b_Stamp$_transit  := FALSE;
            IF  b_Stamp$StampSliderFilled  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step0;
            END_IF;

        Stamp_states_t#StampProcess:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := FALSE;
             b_Stamp$StampPusher  := TRUE;
            IF  b_Stamp$StampLowered  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step1;
            END_IF;

        Stamp_states_t#StampSliderBack:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := TRUE;
             b_Stamp$StampSliderMovedOut  := FALSE;
            IF  b_Stamp$StampSliderSensorMovedIn  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampProcess;
            END_IF;

        Stamp_states_t#StampSliderForward:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := FALSE;
             b_Stamp$StampSliderMovedOut  := TRUE;
            IF (( b_Stamp$StampLowered  = FALSE) AND ( b_Stamp$StampUp  = TRUE)) THEN
                 b_Stamp$interconnect  := FALSE;
            END_IF;
             b_Stamp$Timer$IN  := FALSE;
             b_Stamp$Timer$PT  := USINT#0;
            IF  b_Stamp$Timer$IN  THEN
                 b_Stamp$Timer$Q  := ( b_Stamp$Timer$ET  = USINT#0);
                IF ( b_Stamp$Timer$ET  > USINT#0) THEN
                     b_Stamp$Timer$ET  := ( b_Stamp$Timer$ET  - USINT#1);
                ELSE
                     b_Stamp$Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 b_Stamp$Timer$Q  := FALSE;
                 b_Stamp$Timer$ET  :=  b_Stamp$Timer$PT ;
            END_IF;
            IF  b_Stamp$StampSliderMovedOut  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step2;
            END_IF;

        Stamp_states_t#Stamp_Init_1:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := TRUE;
             b_Stamp$StampSliderMovedOut  := FALSE;
            IF  b_Stamp$StampSliderSensorMovedIn  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_2;
            END_IF;

        Stamp_states_t#Stamp_Init_2:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := FALSE;
             b_Stamp$StampSliderMovedOut  := TRUE;
            IF  b_Stamp$StampSliderSensorMovedOut  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_3;
            END_IF;

        Stamp_states_t#Stamp_Init_3:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := TRUE;
            IF  b_Stamp$StampLowered  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_4;
            END_IF;

        Stamp_states_t#Stamp_Init_4:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := FALSE;
            IF  b_Stamp$StampUp  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF;

        Stamp_states_t#Start_Stamp:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedOut  := FALSE;
             b_Stamp$StampSliderMovedIn  := FALSE;
             b_Stamp$StampPusher  := FALSE;
             b_Stamp$StampGreenLamp  := FALSE;
             b_Stamp$StampPressure  := FALSE;
             b_Stamp$StartCommandStamp  := FALSE;
            IF ( b_Stamp$StampStartButton  = TRUE) THEN
                 b_Stamp$interconnectStampStartCommand  := TRUE;
            END_IF;
            IF  b_Stamp$interconnectStampStartCommand  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Green_Lamp;
            END_IF;

        Stamp_states_t#Step0:
             b_Stamp$_transit  := FALSE;
            IF  b_Stamp$CraneUp  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampSliderBack;
            END_IF;

        Stamp_states_t#Step1:
             b_Stamp$_transit  := FALSE;
             b_Stamp$Timer$IN  :=  b_Stamp$StampLowered ;
             b_Stamp$Timer$PT  := USINT#0;
            IF  b_Stamp$Timer$IN  THEN
                 b_Stamp$Timer$Q  := ( b_Stamp$Timer$ET  = USINT#0);
                IF ( b_Stamp$Timer$ET  > USINT#0) THEN
                     b_Stamp$Timer$ET  := ( b_Stamp$Timer$ET  - USINT#1);
                ELSE
                     b_Stamp$Timer$ET  := USINT#0;
                END_IF;
            ELSE
                 b_Stamp$Timer$Q  := FALSE;
                 b_Stamp$Timer$ET  :=  b_Stamp$Timer$PT ;
            END_IF;
             b_Stamp$interconnect  :=  b_Stamp$Timer$Q ;
            IF  b_Stamp$interconnect  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampSliderForward;
            END_IF;

        Stamp_states_t#Step2:
             b_Stamp$_transit  := FALSE;
            IF ( b_Stamp$CraneOnConveyor  AND NOT  b_Stamp$StampSliderFilled ) THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF;

            END_CASE
    IF ( b_Actuator_MagazinGreenLamp  AND  b_Actuator_StampGreenLamp ) THEN
        IF (( b_Stamp$StartCommandStamp  AND  b_Crane$StartCommandCrane ) AND  b_Mag$StartCommandMagazin ) THEN
             b_Crane$StartVar  := TRUE;
             b_Mag$StartVar  := TRUE;
             b_Stamp$StartVar  := TRUE;
             b_DIAGNOSIS_ACTIVE  := TRUE;
        END_IF;
    END_IF;
     b_Crane$SFCReset  := FALSE;
     b_Mag$SFCReset  := FALSE;
     b_Stamp$SFCReset  := FALSE;
ELSEIF (NOT  b_Sensor_StampEmergencyStop  OR NOT  b_Sensor_MagazinEmergencyStop ) THEN
     b_Actuator_MagazinSlider  := FALSE;
     b_Actuator_CraneLower  := FALSE;
     b_Actuator_MagazinVacuumOn  := FALSE;
     b_Actuator_MagazinVacuumOff  := TRUE;
     b_Actuator_MagazinGreenLamp  := FALSE;
     b_Actuator_CraneTurnCounterclockwise  := FALSE;
     b_Actuator_CraneTurnClockwise  := FALSE;
     b_Actuator_StampSliderMovedOut  := TRUE;
     b_Actuator_StampSliderMovedIn  := FALSE;
     b_Actuator_StampGreenLamp  := FALSE;
     b_Actuator_StampPusher  := FALSE;
     b_Actuator_AnalogCranePressure  := INT#0;
     b_Crane$SFCReset  := TRUE;
     b_Mag$SFCReset  := TRUE;
     b_Stamp$SFCReset  := TRUE;
     b_Crane$StartVar  := FALSE;
     b_Mag$StartVar  := FALSE;
     b_Stamp$StartVar  := FALSE;
END_IF

 
 END_PROGRAM