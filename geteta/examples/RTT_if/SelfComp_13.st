TYPE

Crane_states_t : (Crane_Go_Up , Crane_Go_Up_White , Crane_Init , Crane_Init_2 ,
Crane_Lift_At_Stamp , Crane_Lift_At_Stamp2 , Crane_Lift_Conveyor ,
Crane_Lift_Conveyor2 , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin ,
Crane_Lift_Magazin_Metallic , Crane_Lift_Magazin_White ,
Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor ,
Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Metallic2 ,
Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic ,
Crane_On_Stamp_Metallic2 , Crane_On_Stamp_Metallic2_Lower ,
Crane_On_Stamp_Stop_Black , Crane_On_Stamp_White , Crane_Turn_Left_Back_To_Stamp
, Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic ,
Crane_Turn_Left_Metallic2 , Crane_Turn_Left_NOT_Metallic ,
Crane_Turn_Left_NOT_Metallic_Black , Crane_Turn_Left_White ,
Crane_Turn_Right_From_Stamp , Init , Interstep , Interstep_2 , Interstep_3 ,
Interstep_4 , Lower_Crane , Magazin_Stop , Magazin_Stop_Black ,
Magazin_Stop_Final , No_Workpiece_ready , Reset_interconnect ,
Stamp_Pressure_Profile_Set_Metallic , Stamp_Pressure_Profile_Set_White ,
Start_Crane , Step0 , Step2 , Step3 , Step4 , Suck_At_Stamp , Suck_At_Stamp2 ,
TimeDelay , Turn_Right , Turn_Right_Black , Turn_Right_Final , pause , release ,
release2 , release_Black , release_Workpiece , release_Workpiece_White);

    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init ,
    Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);

Conveyor_states_t : (Conveyor_Init , Conveyor_Stop_Empty_Magazin ,
    Conveyor_Towards_Stacker , Conveyor_init_2 , Conveyor_pause , Green_Lamp ,
    Init , Interstep , Runtime_Conveyor , Start_Conveyor , Step0);
    Stamp_states_t : (Green_Lamp , Init , Interstep , Intertsep_2 , StampProcess
    , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 ,
    Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);

Pusher_states_t : (Check_For_Black , Check_For_Metal , Check_For_White ,
First_Slide_Timer_Black , First_Slide_Timer_Metal , First_Slide_Timer_White ,
First_Slide_black_workpieces , First_Slide_metal_workpieces ,
First_Slide_white_workpieces , Init , Interstep , Interstep_2 ,
PusherY1_Move_In_Black , PusherY1_Move_In_Metal , PusherY1_Move_In_White ,
PusherY1_Move_Out_Black , PusherY1_Move_Out_Metal , PusherY1_Move_Out_White ,
PusherY2_Move_In_Black , PusherY2_Move_In_Metal , PusherY2_Move_In_White ,
PusherY2_Move_Out_Black , PusherY2_Move_Out_Metal , PusherY2_Move_Out_White ,
Reset_interconnect3 , Reset_interconnect_Slide1_Black ,
Reset_interconnect_Slide1_Metal , Reset_interconnect_Slide1_White ,
Reset_interconnect_Slide2_Black , Reset_interconnect_Slide2_Metal ,
Reset_interconnect_Slide2_White , Reset_interconnect_Slide3_Metal ,
Reset_interconnect_Slide3_White , Second_Slide_Timer_Black ,
Second_Slide_Timer_Metal , Second_Slide_Timer_White ,
Second_Slide_black_workpieces , Second_Slide_metal_workpieces ,
Second_Slide_white_workpieces , Second_Test_For_Metal , Second_Test_For_White ,
Third_Slide_black_workpieces , Third_Slide_metal_workpieces ,
Third_Slide_white_workpieces , Wait_Black , Wait_Metal , Wait_White ,
Wait_Y1_Black , Wait_Y1_Metal , Wait_Y1_White , Wait_Y2_Black , Wait_Y2_Metal ,
Wait_Y2_White);

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
VAR_OUTPUT   a_Actuator_PusherY1  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_PusherY2  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_SorterConveyorTowardsCrane  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_SorterConveyorTowardsStacker  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_SorterGreenLampConveyor  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_SorterWhiteLampConveyor  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampPusher  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampSliderMovedIn  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampSliderMovedOut  : BOOL; END_VAR
VAR_OUTPUT   a_Actuator_StampWhiteLamp  : BOOL; END_VAR
VAR   a_Conveyor$Duration_Conveyor_Runtime  : UINT := UINT#1125; END_VAR
VAR   a_Conveyor$Duration_Conveyor_Test  : UINT := UINT#250; END_VAR
VAR   a_Conveyor$SFCInit  : BOOL; END_VAR
VAR   a_Conveyor$SFCReset  : BOOL; END_VAR
VAR   a_Conveyor$SorterConveyorTowardsCrane  : BOOL; END_VAR
VAR   a_Conveyor$SorterConveyorTowardsStacker  : BOOL; END_VAR
VAR   a_Conveyor$SorterGreenLampConveyor  : BOOL; END_VAR
VAR   a_Conveyor$SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR   a_Conveyor$SorterStartButton  : BOOL; END_VAR
VAR   a_Conveyor$SorterSwitchManuellAutomatic  : BOOL; END_VAR
VAR   a_Conveyor$SorterWhiteLampConveyor  : BOOL; END_VAR
VAR   a_Conveyor$StartCommandConveyor  : BOOL; END_VAR
VAR   a_Conveyor$StartVar  : BOOL; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Runtime$ET  : USINT; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Runtime$IN  : BOOL; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Runtime$PT  : USINT; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Runtime$Q  : BOOL; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Test$ET  : USINT; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Test$IN  : BOOL; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Test$PT  : USINT; END_VAR
VAR   a_Conveyor$Timer_Conveyor_Test$Q  : BOOL; END_VAR
VAR   a_Conveyor$_state  : Conveyor_states_t; END_VAR
VAR   a_Conveyor$_transit  : BOOL; END_VAR
VAR   a_Conveyor$interconnectConveyorStartCommand  : BOOL; END_VAR
VAR   a_Conveyor$interconnectConveyorTerminationCommand  : BOOL; END_VAR
VAR   a_Conveyor$interconnect_Conveyor_Runtime  : BOOL; END_VAR
VAR   a_Conveyor$interconnect_Conveyor_Test  : BOOL; END_VAR
VAR   a_Crane$AnalogCranePosition  : INT; END_VAR
VAR   a_Crane$AnalogCranePressure  : INT; END_VAR
VAR   a_Crane$CraneDown  : BOOL; END_VAR
VAR   a_Crane$CraneLower  : BOOL; END_VAR
VAR   a_Crane$CraneSucked  : BOOL; END_VAR
VAR   a_Crane$CraneTurnClockwise  : BOOL; END_VAR
VAR   a_Crane$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   a_Crane$CraneUp  : BOOL; END_VAR
VAR   a_Crane$Duration1  : UINT := UINT#375; END_VAR
VAR   a_Crane$MagazinCapacitiveSensor  : BOOL; END_VAR
VAR   a_Crane$MagazinOpticalSensor  : BOOL; END_VAR
VAR   a_Crane$MagazinSlider  : BOOL; END_VAR
VAR   a_Crane$MagazinVacuumOff  : BOOL; END_VAR
VAR   a_Crane$MagazinVacuumOn  : BOOL; END_VAR
VAR   a_Crane$SFCInit  : BOOL; END_VAR
VAR   a_Crane$SFCReset  : BOOL; END_VAR
VAR   a_Crane$SliderMovedOut  : BOOL; END_VAR
VAR   a_Crane$SliderNotMovedOut  : BOOL; END_VAR
VAR   a_Crane$StampLowered  : BOOL; END_VAR
VAR   a_Crane$StampSliderFilled  : BOOL; END_VAR
VAR   a_Crane$StampSliderSensorMovedOut  : BOOL; END_VAR
VAR   a_Crane$StartButtonMagazin  : BOOL; END_VAR
VAR   a_Crane$StartCommandCrane  : BOOL; END_VAR
VAR   a_Crane$StartVar  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer$ET  : USINT; END_VAR
VAR   a_Crane$TimeDelay_Timer$IN  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer$PT  : USINT; END_VAR
VAR   a_Crane$TimeDelay_Timer$Q  : BOOL; END_VAR
VAR   a_Crane$TimeDelay_Timer_Duration  : UINT := UINT#12; END_VAR
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
VAR   a_Mag$AnalogCranePosition  : INT; END_VAR
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
VAR   a_Pusher$Duration2  : UINT := UINT#500; END_VAR
VAR   a_Pusher$Duration3  : UINT := UINT#50; END_VAR
VAR   a_Pusher$Duration_Slide1_Black  : UINT := UINT#237; END_VAR
VAR   a_Pusher$Duration_Slide1_Metal  : UINT := UINT#75; END_VAR
VAR   a_Pusher$Duration_Slide1_White  : UINT := UINT#75; END_VAR
VAR   a_Pusher$Duration_Slide2_Black  : UINT := UINT#500; END_VAR
VAR   a_Pusher$Duration_Slide2_Metal  : UINT := UINT#92; END_VAR
VAR   a_Pusher$Duration_Slide2_White  : UINT := UINT#92; END_VAR
VAR   a_Pusher$Priority_Var_Black  : INT := INT#3; END_VAR
VAR   a_Pusher$Priority_Var_Metal  : INT := INT#3; END_VAR
VAR   a_Pusher$Priority_Var_White  : INT := INT#3; END_VAR
VAR   a_Pusher$PusherY1  : BOOL; END_VAR
VAR   a_Pusher$PusherY2  : BOOL; END_VAR
VAR   a_Pusher$SFCInit  : BOOL; END_VAR
VAR   a_Pusher$SFCReset  : BOOL; END_VAR
VAR   a_Pusher$Slide1_black  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide1_metal  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide1_white  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide2_black  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide2_metal  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide2_white  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide3_black  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide3_metal  : INT := INT#1; END_VAR
VAR   a_Pusher$Slide3_white  : INT := INT#1; END_VAR
VAR   a_Pusher$SorterCapacitiveSensorPusher1  : BOOL; END_VAR
VAR   a_Pusher$SorterCapacitiveSensorPusher2  : BOOL; END_VAR
VAR   a_Pusher$SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR   a_Pusher$SorterLightnessSensorPusher1  : BOOL; END_VAR
VAR   a_Pusher$SorterLightnessSensorPusher2  : BOOL; END_VAR
VAR   a_Pusher$SorterLightnessSensorPusher3  : BOOL; END_VAR
VAR   a_Pusher$SorterLightnesssensorCraneInterfaceInverse  : BOOL; END_VAR
VAR   a_Pusher$SorterPusher1MovedIn  : BOOL; END_VAR
VAR   a_Pusher$SorterPusher1MovedOut  : BOOL; END_VAR
VAR   a_Pusher$SorterPusher2MovedIn  : BOOL; END_VAR
VAR   a_Pusher$SorterPusher2MovedOut  : BOOL; END_VAR
VAR   a_Pusher$SorterStartButton  : BOOL; END_VAR
VAR   a_Pusher$StartVar  : BOOL; END_VAR
VAR   a_Pusher$Timer2$ET  : USINT; END_VAR
VAR   a_Pusher$Timer2$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer2$PT  : USINT; END_VAR
VAR   a_Pusher$Timer2$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer3$ET  : USINT; END_VAR
VAR   a_Pusher$Timer3$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer3$PT  : USINT; END_VAR
VAR   a_Pusher$Timer3$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_Black$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_Black$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_Black$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_Black$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_Metal$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_Metal$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_Metal$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_Metal$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_White$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_White$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide1_White$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide1_White$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_Black$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_Black$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_Black$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_Black$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_Metal$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_Metal$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_Metal$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_Metal$Q  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_White$ET  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_White$IN  : BOOL; END_VAR
VAR   a_Pusher$Timer_Slide2_White$PT  : USINT; END_VAR
VAR   a_Pusher$Timer_Slide2_White$Q  : BOOL; END_VAR
VAR   a_Pusher$_state  : Pusher_states_t; END_VAR
VAR   a_Pusher$_transit  : BOOL; END_VAR
VAR   a_Pusher$interconnect2  : BOOL; END_VAR
VAR   a_Pusher$interconnect3  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide1_Black  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide1_Metal  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide1_White  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide2_Black  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide2_Metal  : BOOL; END_VAR
VAR   a_Pusher$interconnect_Slide2_White  : BOOL; END_VAR
VAR_INPUT   a_Sensor_AnalogCranePosition  : INT; END_VAR
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
VAR_INPUT   a_Sensor_SorterCapacitiveSensorPusher1  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterCapacitiveSensorPusher2  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterEmergencyStop  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterLightnessSensorPusher1  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterLightnessSensorPusher2  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterLightnessSensorPusher3  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterLightnesssensorCraneInterfaceInverse  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterPusher1MovedIn  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterPusher1MovedOut  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterPusher2MovedIn  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterPusher2MovedOut  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterStartButton  : BOOL; END_VAR
VAR_INPUT   a_Sensor_SorterSwitchManuellAutomatic  : BOOL; END_VAR
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
VAR   a_Stamp$AnalogCranePosition  : INT; END_VAR
VAR   a_Stamp$CraneDown  : BOOL; END_VAR
VAR   a_Stamp$CraneOnConveyor  : BOOL; END_VAR
VAR   a_Stamp$CranePositionStamp  : BOOL; END_VAR
VAR   a_Stamp$CraneSucked  : BOOL; END_VAR
VAR   a_Stamp$CraneUp  : BOOL; END_VAR
        VAR   a_Stamp$Duration  : UINT := UINT#125; END_VAR

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

VAR_INPUT  a_PARAMETER_CRANE_PRESSURE_METALLIC  : INT := INT#6000; END_VAR
VAR_INPUT  a_PARAMETER_CRANE_PRESSURE_WHITE  : INT := INT#7000; END_VAR




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
VAR_OUTPUT   b_Actuator_PusherY1  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_PusherY2  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_SorterConveyorTowardsCrane  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_SorterConveyorTowardsStacker  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_SorterGreenLampConveyor  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_SorterWhiteLampConveyor  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampGreenLamp  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampPusher  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampSliderMovedIn  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampSliderMovedOut  : BOOL; END_VAR
VAR_OUTPUT   b_Actuator_StampWhiteLamp  : BOOL; END_VAR
VAR   b_Conveyor$Duration_Conveyor_Runtime  : UINT := UINT#1125; END_VAR
VAR   b_Conveyor$Duration_Conveyor_Test  : UINT := UINT#250; END_VAR
VAR   b_Conveyor$SFCInit  : BOOL; END_VAR
VAR   b_Conveyor$SFCReset  : BOOL; END_VAR
VAR   b_Conveyor$SorterConveyorTowardsCrane  : BOOL; END_VAR
VAR   b_Conveyor$SorterConveyorTowardsStacker  : BOOL; END_VAR
VAR   b_Conveyor$SorterGreenLampConveyor  : BOOL; END_VAR
VAR   b_Conveyor$SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR   b_Conveyor$SorterStartButton  : BOOL; END_VAR
VAR   b_Conveyor$SorterSwitchManuellAutomatic  : BOOL; END_VAR
VAR   b_Conveyor$SorterWhiteLampConveyor  : BOOL; END_VAR
VAR   b_Conveyor$StartCommandConveyor  : BOOL; END_VAR
VAR   b_Conveyor$StartVar  : BOOL; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Runtime$ET  : USINT; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Runtime$IN  : BOOL; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Runtime$PT  : USINT; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Runtime$Q  : BOOL; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Test$ET  : USINT; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Test$IN  : BOOL; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Test$PT  : USINT; END_VAR
VAR   b_Conveyor$Timer_Conveyor_Test$Q  : BOOL; END_VAR
VAR   b_Conveyor$_state  : Conveyor_states_t; END_VAR
VAR   b_Conveyor$_transit  : BOOL; END_VAR
VAR   b_Conveyor$interconnectConveyorStartCommand  : BOOL; END_VAR
VAR   b_Conveyor$interconnectConveyorTerminationCommand  : BOOL; END_VAR
VAR   b_Conveyor$interconnect_Conveyor_Runtime  : BOOL; END_VAR
VAR   b_Conveyor$interconnect_Conveyor_Test  : BOOL; END_VAR
VAR   b_Crane$AnalogCranePosition  : INT; END_VAR
VAR   b_Crane$AnalogCranePressure  : INT; END_VAR
VAR   b_Crane$CraneDown  : BOOL; END_VAR
VAR   b_Crane$CraneLower  : BOOL; END_VAR
VAR   b_Crane$CraneSucked  : BOOL; END_VAR
VAR   b_Crane$CraneTurnClockwise  : BOOL; END_VAR
VAR   b_Crane$CraneTurnCounterclockwise  : BOOL; END_VAR
VAR   b_Crane$CraneUp  : BOOL; END_VAR
VAR   b_Crane$Duration1  : UINT := UINT#375; END_VAR
VAR   b_Crane$MagazinCapacitiveSensor  : BOOL; END_VAR
VAR   b_Crane$MagazinOpticalSensor  : BOOL; END_VAR
VAR   b_Crane$MagazinSlider  : BOOL; END_VAR
VAR   b_Crane$MagazinVacuumOff  : BOOL; END_VAR
VAR   b_Crane$MagazinVacuumOn  : BOOL; END_VAR
VAR   b_Crane$SFCInit  : BOOL; END_VAR
VAR   b_Crane$SFCReset  : BOOL; END_VAR
VAR   b_Crane$SliderMovedOut  : BOOL; END_VAR
VAR   b_Crane$SliderNotMovedOut  : BOOL; END_VAR
VAR   b_Crane$StampLowered  : BOOL; END_VAR
VAR   b_Crane$StampSliderFilled  : BOOL; END_VAR
VAR   b_Crane$StampSliderSensorMovedOut  : BOOL; END_VAR
VAR   b_Crane$StartButtonMagazin  : BOOL; END_VAR
VAR   b_Crane$StartCommandCrane  : BOOL; END_VAR
VAR   b_Crane$StartVar  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer$ET  : USINT; END_VAR
VAR   b_Crane$TimeDelay_Timer$IN  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer$PT  : USINT; END_VAR
VAR   b_Crane$TimeDelay_Timer$Q  : BOOL; END_VAR
VAR   b_Crane$TimeDelay_Timer_Duration  : UINT := UINT#12; END_VAR
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
VAR   b_Mag$AnalogCranePosition  : INT; END_VAR
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
VAR   b_Pusher$Duration2  : UINT := UINT#500; END_VAR
VAR   b_Pusher$Duration3  : UINT := UINT#50; END_VAR
VAR   b_Pusher$Duration_Slide1_Black  : UINT := UINT#237; END_VAR
VAR   b_Pusher$Duration_Slide1_Metal  : UINT := UINT#75; END_VAR
VAR   b_Pusher$Duration_Slide1_White  : UINT := UINT#75; END_VAR
VAR   b_Pusher$Duration_Slide2_Black  : UINT := UINT#500; END_VAR
VAR   b_Pusher$Duration_Slide2_Metal  : UINT := UINT#92; END_VAR
VAR   b_Pusher$Duration_Slide2_White  : UINT := UINT#92; END_VAR
VAR   b_Pusher$Priority_Var_Black  : INT := INT#3; END_VAR
VAR   b_Pusher$Priority_Var_Metal  : INT := INT#3; END_VAR
VAR   b_Pusher$Priority_Var_White  : INT := INT#3; END_VAR
VAR   b_Pusher$PusherY1  : BOOL; END_VAR
VAR   b_Pusher$PusherY2  : BOOL; END_VAR
VAR   b_Pusher$SFCInit  : BOOL; END_VAR
VAR   b_Pusher$SFCReset  : BOOL; END_VAR
VAR   b_Pusher$Slide1_black  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide1_metal  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide1_white  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide2_black  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide2_metal  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide2_white  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide3_black  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide3_metal  : INT := INT#1; END_VAR
VAR   b_Pusher$Slide3_white  : INT := INT#1; END_VAR
VAR   b_Pusher$SorterCapacitiveSensorPusher1  : BOOL; END_VAR
VAR   b_Pusher$SorterCapacitiveSensorPusher2  : BOOL; END_VAR
VAR   b_Pusher$SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR   b_Pusher$SorterLightnessSensorPusher1  : BOOL; END_VAR
VAR   b_Pusher$SorterLightnessSensorPusher2  : BOOL; END_VAR
VAR   b_Pusher$SorterLightnessSensorPusher3  : BOOL; END_VAR
VAR   b_Pusher$SorterLightnesssensorCraneInterfaceInverse  : BOOL; END_VAR
VAR   b_Pusher$SorterPusher1MovedIn  : BOOL; END_VAR
VAR   b_Pusher$SorterPusher1MovedOut  : BOOL; END_VAR
VAR   b_Pusher$SorterPusher2MovedIn  : BOOL; END_VAR
VAR   b_Pusher$SorterPusher2MovedOut  : BOOL; END_VAR
VAR   b_Pusher$SorterStartButton  : BOOL; END_VAR
VAR   b_Pusher$StartVar  : BOOL; END_VAR
VAR   b_Pusher$Timer2$ET  : USINT; END_VAR
VAR   b_Pusher$Timer2$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer2$PT  : USINT; END_VAR
VAR   b_Pusher$Timer2$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer3$ET  : USINT; END_VAR
VAR   b_Pusher$Timer3$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer3$PT  : USINT; END_VAR
VAR   b_Pusher$Timer3$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_Black$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_Black$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_Black$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_Black$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_Metal$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_Metal$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_Metal$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_Metal$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_White$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_White$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide1_White$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide1_White$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_Black$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_Black$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_Black$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_Black$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_Metal$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_Metal$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_Metal$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_Metal$Q  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_White$ET  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_White$IN  : BOOL; END_VAR
VAR   b_Pusher$Timer_Slide2_White$PT  : USINT; END_VAR
VAR   b_Pusher$Timer_Slide2_White$Q  : BOOL; END_VAR
VAR   b_Pusher$_state  : Pusher_states_t; END_VAR
VAR   b_Pusher$_transit  : BOOL; END_VAR
VAR   b_Pusher$interconnect2  : BOOL; END_VAR
VAR   b_Pusher$interconnect3  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide1_Black  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide1_Metal  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide1_White  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide2_Black  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide2_Metal  : BOOL; END_VAR
VAR   b_Pusher$interconnect_Slide2_White  : BOOL; END_VAR
VAR_INPUT   b_Sensor_AnalogCranePosition  : INT; END_VAR
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
VAR_INPUT   b_Sensor_SorterCapacitiveSensorPusher1  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterCapacitiveSensorPusher2  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterEmergencyStop  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterLightbarrierCraneInterface  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterLightnessSensorPusher1  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterLightnessSensorPusher2  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterLightnessSensorPusher3  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterLightnesssensorCraneInterfaceInverse  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterPusher1MovedIn  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterPusher1MovedOut  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterPusher2MovedIn  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterPusher2MovedOut  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterStartButton  : BOOL; END_VAR
VAR_INPUT   b_Sensor_SorterSwitchManuellAutomatic  : BOOL; END_VAR
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
VAR   b_Stamp$AnalogCranePosition  : INT; END_VAR
VAR   b_Stamp$CraneDown  : BOOL; END_VAR
VAR   b_Stamp$CraneOnConveyor  : BOOL; END_VAR
VAR   b_Stamp$CranePositionStamp  : BOOL; END_VAR
VAR   b_Stamp$CraneSucked  : BOOL; END_VAR
VAR   b_Stamp$CraneUp  : BOOL; END_VAR
        VAR   b_Stamp$Duration  : UINT := UINT#125; END_VAR

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

VAR_INPUT  b_PARAMETER_CRANE_PRESSURE_METALLIC  : INT := INT#6000; END_VAR
VAR_INPUT  b_PARAMETER_CRANE_PRESSURE_WHITE  : INT := INT#7000; END_VAR


 
 a_Mag$SliderNotMovedOut  :=  a_Sensor_SliderNotMovedOut ;
 a_Mag$SliderMovedOut  :=  a_Sensor_SliderMovedOut ;
 a_Mag$CraneOnMagazin  :=  a_Sensor_CraneOnMagazin ;
 a_Mag$CraneDown  :=  a_Sensor_CraneDown ;
 a_Mag$CraneUp  :=  a_Sensor_CraneUp ;
 a_Mag$CraneOnConveyor  :=  a_Sensor_CraneOnConveyor ;
 a_Mag$WorkpieceReady  :=  a_Sensor_WorkpieceReady ;
 a_Mag$AnalogCranePosition  :=  a_Sensor_AnalogCranePosition ;
 a_Mag$StartButtonMagazin  :=  a_Sensor_StartButtonMagazin ;
 a_Actuator_MagazinSlider  :=  a_Mag$MagazinSlider ;
 a_Actuator_MagazinGreenLamp  :=  a_Mag$MagazinGreenLamp ;
 a_Crane$CraneUp  :=  a_Sensor_CraneUp ;
 a_Crane$CraneDown  :=  a_Sensor_CraneDown ;
 a_Crane$CraneSucked  :=  a_Sensor_CraneSucked ;
 a_Crane$MagazinCapacitiveSensor  :=  a_Sensor_MagazinCapacitiveSensor ;
 a_Crane$SliderMovedOut  :=  a_Sensor_SliderMovedOut ;
 a_Crane$WorkpieceReady  :=  a_Sensor_WorkpieceReady ;
 a_Crane$MagazinOpticalSensor  :=  a_Sensor_MagazinOpticalSensor ;
 a_Crane$StampSliderFilled  :=  a_Sensor_StampSliderFilled ;
 a_Crane$StampSliderSensorMovedOut  :=  a_Sensor_StampSliderSensorMovedOut ;
 a_Crane$StampLowered  :=  a_Sensor_StampLowered ;
 a_Crane$AnalogCranePosition  :=  a_Sensor_AnalogCranePosition ;
 a_Crane$StartButtonMagazin  :=  a_Sensor_StartButtonMagazin ;

//Diagnosis
// old:  a_Actuator_AnalogCranePressure 
// new:  a_Crane$AnalogCranePressure ;
 a_Actuator_CraneTurnCounterclockwise  :=  a_Crane$CraneTurnCounterclockwise ;
 a_Actuator_CraneTurnClockwise  :=  a_Crane$CraneTurnClockwise ;

IF  a_DIAGNOSIS_ACTIVE  THEN
        IF  a_Sensor_CraneSucked  AND ( a_Crane$AnalogCranePressure  <= 0 OR  a_Crane$AnalogCranePressure  > 10000) THEN
                 a_Actuator_CraneTurnCounterclockwise  := FALSE;
                 a_Actuator_CraneTurnClockwise  := FALSE;
        END_IF
END_IF

//End of Diagnosis

 a_Actuator_CraneLower  :=  a_Crane$CraneLower ;
 a_Actuator_MagazinVacuumOff  :=  a_Crane$MagazinVacuumOff ;
 a_Actuator_MagazinVacuumOn  :=  a_Crane$MagazinVacuumOn ;
 a_Actuator_AnalogCranePressure  :=  a_Crane$AnalogCranePressure ;
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
 a_Stamp$AnalogCranePosition  :=  a_Sensor_AnalogCranePosition ;
 a_Stamp$StampStartButton  :=  a_Sensor_StampStartButton ;
 a_Actuator_StampSliderMovedOut  :=  a_Stamp$StampSliderMovedOut ;
 a_Actuator_StampSliderMovedIn  :=  a_Stamp$StampSliderMovedIn ;
 a_Actuator_StampWhiteLamp  :=  a_Stamp$StampWhiteLamp ;
 a_Actuator_StampPusher  :=  a_Stamp$StampPusher ;
 a_Actuator_StampGreenLamp  :=  a_Stamp$StampGreenLamp ;
 a_Conveyor$SorterStartButton  :=  a_Sensor_SorterStartButton ;
 a_Conveyor$SorterSwitchManuellAutomatic  :=  a_Sensor_SorterSwitchManuellAutomatic ;
 a_Conveyor$SorterLightbarrierCraneInterface  :=  a_Sensor_SorterLightbarrierCraneInterface ;
 a_Actuator_SorterConveyorTowardsStacker  :=  a_Conveyor$SorterConveyorTowardsStacker ;
 a_Actuator_SorterConveyorTowardsCrane  :=  a_Conveyor$SorterConveyorTowardsCrane ;
 a_Actuator_SorterGreenLampConveyor  :=  a_Conveyor$SorterGreenLampConveyor ;
 a_Actuator_SorterWhiteLampConveyor  :=  a_Conveyor$SorterWhiteLampConveyor ;
 a_Pusher$SorterLightnesssensorCraneInterfaceInverse  :=  a_Sensor_SorterLightnesssensorCraneInterfaceInverse ;
 a_Pusher$SorterLightbarrierCraneInterface  :=  a_Sensor_SorterLightbarrierCraneInterface ;
 a_Pusher$SorterCapacitiveSensorPusher1  :=  a_Sensor_SorterCapacitiveSensorPusher1 ;
 a_Pusher$SorterLightnessSensorPusher1  :=  a_Sensor_SorterLightnessSensorPusher1 ;
 a_Pusher$SorterCapacitiveSensorPusher2  :=  a_Sensor_SorterCapacitiveSensorPusher2 ;
 a_Pusher$SorterLightnessSensorPusher2  :=  a_Sensor_SorterLightnessSensorPusher2 ;
 a_Pusher$SorterLightnessSensorPusher3  :=  a_Sensor_SorterLightnessSensorPusher3 ;
 a_Pusher$SorterPusher1MovedOut  :=  a_Sensor_SorterPusher1MovedOut ;
 a_Pusher$SorterPusher1MovedIn  :=  a_Sensor_SorterPusher1MovedIn ;
 a_Pusher$SorterPusher2MovedOut  :=  a_Sensor_SorterPusher2MovedOut ;
 a_Pusher$SorterPusher2MovedIn  :=  a_Sensor_SorterPusher2MovedIn ;
 a_Pusher$SorterStartButton  :=  a_Sensor_SorterStartButton ;
 a_Actuator_PusherY1  :=  a_Pusher$PusherY1 ;
 a_Actuator_PusherY2  :=  a_Pusher$PusherY2 ;

IF (( a_Sensor_SorterEmergencyStop  AND  a_Sensor_StampEmergencyStop ) AND  a_Sensor_MagazinEmergencyStop ) THEN
    CASE  a_Mag$_state  OF
        Magazin_states_t#Green_Lamp:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinGreenLamp  := TRUE;
             a_Mag$interconnectMagazinStartCommand  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Magazin_Init;
            END_IF

        Magazin_states_t#Init:
             a_Mag$_transit  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Start_Magazin;
            END_IF

        Magazin_states_t#Interstep:
             a_Mag$_transit  := FALSE;
             a_Mag$StartCommandMagazin  := TRUE;
            IF  a_Mag$StartVar  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#convey;
            END_IF

        Magazin_states_t#Magazin_Init:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := TRUE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Magazin_Init_2;
            END_IF

        Magazin_states_t#Magazin_Init_2:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := FALSE;
            IF TRUE THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#Slider_Move_Back:
             a_Mag$_transit  := FALSE;
            IF (( a_Mag$SliderMovedOut  = TRUE) AND ( a_Mag$SliderNotMovedOut  = FALSE)) THEN
                 a_Mag$MagazinSlider  := FALSE;
            END_IF
            IF  a_Mag$CraneUp  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Step1;
            END_IF

        Magazin_states_t#Start_Magazin:
             a_Mag$_transit  := FALSE;
             a_Mag$MagazinSlider  := FALSE;
             a_Mag$MagazinGreenLamp  := FALSE;
             a_Mag$StartVar  := FALSE;
             a_Mag$StartCommandMagazin  := FALSE;
            IF ( a_Mag$StartButtonMagazin  = TRUE) THEN
                 a_Mag$interconnectMagazinStartCommand  := TRUE;
            END_IF
            IF  a_Mag$interconnectMagazinStartCommand  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Green_Lamp;
            END_IF

        Magazin_states_t#Step0:
             a_Mag$_transit  := FALSE;
            IF  a_Mag$CraneDown  THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Slider_Move_Back;
            END_IF

        Magazin_states_t#Step1:
             a_Mag$_transit  := FALSE;
            IF (( a_Mag$AnalogCranePosition  > INT#16160) AND ( a_Mag$AnalogCranePosition  < INT#16260)) THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#convey:
             a_Mag$_transit  := FALSE;
            IF  a_Mag$SliderNotMovedOut  THEN
                 a_Mag$MagazinSlider  := TRUE;
            END_IF
            IF (( a_Mag$AnalogCranePosition  > INT#24290) AND ( a_Mag$AnalogCranePosition  < INT#24390)) THEN
                 a_Mag$_transit  := TRUE;
                 a_Mag$_state  := Magazin_states_t#Step0;
            END_IF

            END_CASE
    CASE  a_Crane$_state  OF
        Crane_states_t#Crane_Go_Up:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step3;
            END_IF

        Crane_states_t#Crane_Go_Up_White:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step3;
            END_IF

        Crane_states_t#Crane_Init:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := TRUE;
             a_Crane$interconnectCraneStartCommand  := FALSE;
             a_Crane$AnalogCranePressure  :=  a_PARAMETER_CRANE_PRESSURE_METALLIC ;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Init_2;
            END_IF

        Crane_states_t#Crane_Init_2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_At_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_At_Stamp2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
             a_Crane$AnalogCranePressure  := INT#0;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Right_From_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Magazin:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_Magazin_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_Magazin_White:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_White;
            END_IF

        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$CraneUp  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF

        Crane_states_t#Crane_Lower:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
             a_Crane$CraneLower  := TRUE;
             a_Crane$AnalogCranePressure  := INT#0;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step0;
            END_IF

        Crane_states_t#Crane_On_Conveyor:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Metallic2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release2;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release_Black;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release_Workpiece;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF  a_Crane$StampLowered  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep_4;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic2_Lower:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Suck_At_Stamp2;
            END_IF

        Crane_states_t#Crane_On_Stamp_Stop_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#Crane_On_Stamp_White:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#release_Workpiece_White;
            END_IF

        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#8160) AND ( a_Crane$AnalogCranePosition  < INT#8260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF

        Crane_states_t#Crane_Turn_Left_From_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#16060) AND ( a_Crane$AnalogCranePosition  < INT#16160)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#8160) AND ( a_Crane$AnalogCranePosition  < INT#8260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_Metallic2:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#8160) AND ( a_Crane$AnalogCranePosition  < INT#8260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic2;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#16160) AND ( a_Crane$AnalogCranePosition  < INT#16260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#16160) AND ( a_Crane$AnalogCranePosition  < INT#16260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF

        Crane_states_t#Crane_Turn_Left_White:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := TRUE;
             a_Crane$CraneTurnClockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#8160) AND ( a_Crane$AnalogCranePosition  < INT#8260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_White;
            END_IF

        Crane_states_t#Crane_Turn_Right_From_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#16160) AND ( a_Crane$AnalogCranePosition  < INT#16260)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic2;
            END_IF

        Crane_states_t#Init:
             a_Crane$_transit  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#Interstep:
             a_Crane$_transit  := FALSE;
             a_Crane$StartCommandCrane  := TRUE;
            IF  a_Crane$StartVar  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep_2;
            END_IF

        Crane_states_t#Interstep_2:
             a_Crane$_transit  := FALSE;
            IF  a_Crane$SliderMovedOut  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#TimeDelay;
            END_IF

        Crane_states_t#Interstep_3:
             a_Crane$_transit  := FALSE;
            IF NOT  a_Crane$WorkpieceReady  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#No_Workpiece_ready;
            ELSEIF  a_Crane$WorkpieceReady  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Turn_Right;
            END_IF

        Crane_states_t#Interstep_4:
             a_Crane$_transit  := FALSE;
            IF  a_Crane$StampSliderSensorMovedOut  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic2_Lower;
            END_IF

        Crane_states_t#Lower_Crane:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := TRUE;
            IF  a_Crane$CraneDown  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Suck_At_Stamp;
            END_IF

        Crane_states_t#Magazin_Stop:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lower;
            END_IF

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
            END_IF

        Crane_states_t#Magazin_Stop_Final:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#No_Workpiece_ready:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := FALSE;
             a_Crane$MagazinVacuumOff  := FALSE;
             a_Crane$CraneLower  := FALSE;
            IF  a_Crane$StampSliderFilled  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic2;
            ELSEIF NOT  a_Crane$StampSliderFilled  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Turn_Right_Final;
            END_IF

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
                END_IF
            ELSE
                 a_Crane$Timer1$Q  := FALSE;
                 a_Crane$Timer1$ET  :=  a_Crane$Timer1$PT ;
            END_IF
            IF  a_Crane$SliderMovedOut  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Lower_Crane;
            END_IF

        Crane_states_t#Stamp_Pressure_Profile_Set_Metallic:
             a_Crane$_transit  := FALSE;
             a_Crane$AnalogCranePressure  :=  a_PARAMETER_CRANE_PRESSURE_METALLIC ;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF

        Crane_states_t#Stamp_Pressure_Profile_Set_White:
             a_Crane$_transit  := FALSE;
             a_Crane$AnalogCranePressure  :=  a_PARAMETER_CRANE_PRESSURE_WHITE ;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_White;
            END_IF

        Crane_states_t#Start_Crane:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneLower  := FALSE;
             a_Crane$MagazinVacuumOff  := FALSE;
             a_Crane$MagazinVacuumOn  := FALSE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$CraneTurnClockwise  := FALSE;
             a_Crane$AnalogCranePressure  := INT#0;
             a_Crane$StartVar  := FALSE;
             a_Crane$StartCommandCrane  := FALSE;
            IF ( a_Crane$StartButtonMagazin  = TRUE) THEN
                 a_Crane$interconnectCraneStartCommand  := TRUE;
            END_IF
            IF  a_Crane$interconnectCraneStartCommand  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Init;
            END_IF

        Crane_states_t#Step0:
             a_Crane$_transit  := FALSE;
            IF ( a_Crane$MagazinCapacitiveSensor  AND  a_Crane$MagazinOpticalSensor ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Stamp_Pressure_Profile_Set_Metallic;
            ELSEIF (NOT  a_Crane$MagazinCapacitiveSensor  AND  a_Crane$MagazinOpticalSensor ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Stamp_Pressure_Profile_Set_White;
            ELSEIF (NOT  a_Crane$MagazinCapacitiveSensor  AND NOT  a_Crane$MagazinOpticalSensor ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Magazin;
            END_IF

        Crane_states_t#Step2:
             a_Crane$_transit  := FALSE;
            IF ( a_Crane$MagazinCapacitiveSensor  OR  a_Crane$MagazinOpticalSensor ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#pause;
            ELSEIF (NOT  a_Crane$MagazinCapacitiveSensor  AND NOT  a_Crane$MagazinOpticalSensor ) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Turn_Right_Black;
            END_IF

        Crane_states_t#Step3:
             a_Crane$_transit  := FALSE;
            IF NOT  a_Crane$WorkpieceReady  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step4;
            ELSEIF  a_Crane$WorkpieceReady  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Step2;
            END_IF

        Crane_states_t#Step4:
             a_Crane$_transit  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Suck_At_Stamp:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF

        Crane_states_t#Suck_At_Stamp2:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := TRUE;
             a_Crane$MagazinVacuumOff  := FALSE;
            IF  a_Crane$CraneSucked  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp2;
            END_IF

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
                END_IF
            ELSE
                 a_Crane$TimeDelay_Timer$Q  := FALSE;
                 a_Crane$TimeDelay_Timer$ET  :=  a_Crane$TimeDelay_Timer$PT ;
            END_IF
             a_Crane$TimeDelay_Timer_interconnect  :=  a_Crane$TimeDelay_Timer$Q ;
            IF  a_Crane$TimeDelay_Timer_interconnect  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Interstep_3;
            END_IF

        Crane_states_t#Turn_Right:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#24290) AND ( a_Crane$AnalogCranePosition  < INT#24390)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Magazin_Stop;
            END_IF

        Crane_states_t#Turn_Right_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( a_Crane$AnalogCranePosition  > INT#24290) AND ( a_Crane$AnalogCranePosition  < INT#24390)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Magazin_Stop_Black;
            END_IF

        Crane_states_t#Turn_Right_Final:
             a_Crane$_transit  := FALSE;
             a_Crane$CraneTurnClockwise  := TRUE;
             a_Crane$CraneTurnCounterclockwise  := FALSE;
             a_Crane$AnalogCranePressure  := INT#0;
            IF (( a_Crane$AnalogCranePosition  > INT#24290) AND ( a_Crane$AnalogCranePosition  < INT#24390)) THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Magazin_Stop_Final;
            END_IF

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
                END_IF
            ELSE
                 a_Crane$Timer1$Q  := FALSE;
                 a_Crane$Timer1$ET  :=  a_Crane$Timer1$PT ;
            END_IF
             a_Crane$interconnect  :=  a_Crane$Timer1$Q ;
            IF  a_Crane$interconnect  THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#release:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor;
            END_IF

        Crane_states_t#release2:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor2;
            END_IF

        Crane_states_t#release_Black:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOn  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF

        Crane_states_t#release_Workpiece:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Go_Up;
            END_IF

        Crane_states_t#release_Workpiece_White:
             a_Crane$_transit  := FALSE;
             a_Crane$MagazinVacuumOff  := TRUE;
             a_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 a_Crane$_transit  := TRUE;
                 a_Crane$_state  := Crane_states_t#Crane_Go_Up_White;
            END_IF

            END_CASE
    CASE  a_Stamp$_state  OF
        Stamp_states_t#Green_Lamp:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampGreenLamp  := TRUE;
             a_Stamp$interconnectStampStartCommand  := FALSE;
            IF TRUE THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_1;
            END_IF

        Stamp_states_t#Init:
             a_Stamp$_transit  := FALSE;
            IF TRUE THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Start_Stamp;
            END_IF

        Stamp_states_t#Interstep:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StartCommandStamp  := TRUE;
            IF  a_Stamp$StartVar  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Intertsep_2;
            END_IF

        Stamp_states_t#Intertsep_2:
             a_Stamp$_transit  := FALSE;
            IF  a_Stamp$StampSliderFilled  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step0;
            END_IF

        Stamp_states_t#StampProcess:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := FALSE;
             a_Stamp$StampPusher  := TRUE;
            IF  a_Stamp$StampLowered  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step1;
            END_IF

        Stamp_states_t#StampSliderBack:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := TRUE;
             a_Stamp$StampSliderMovedOut  := FALSE;
            IF  a_Stamp$StampSliderSensorMovedIn  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampProcess;
            END_IF

        Stamp_states_t#StampSliderForward:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := FALSE;
             a_Stamp$StampSliderMovedOut  := TRUE;
            IF (( a_Stamp$StampLowered  = FALSE) AND ( a_Stamp$StampUp  = TRUE)) THEN
                 a_Stamp$interconnect  := FALSE;
            END_IF
             a_Stamp$Timer$IN  := FALSE;
             a_Stamp$Timer$PT  := USINT#0;
            IF  a_Stamp$Timer$IN  THEN
                 a_Stamp$Timer$Q  := ( a_Stamp$Timer$ET  = USINT#0);
                IF ( a_Stamp$Timer$ET  > USINT#0) THEN
                     a_Stamp$Timer$ET  := ( a_Stamp$Timer$ET  - USINT#1);
                ELSE
                     a_Stamp$Timer$ET  := USINT#0;
                END_IF
            ELSE
                 a_Stamp$Timer$Q  := FALSE;
                 a_Stamp$Timer$ET  :=  a_Stamp$Timer$PT ;
            END_IF
            IF  a_Stamp$StampSliderMovedOut  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Step2;
            END_IF

        Stamp_states_t#Stamp_Init_1:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := TRUE;
             a_Stamp$StampSliderMovedOut  := FALSE;
            IF  a_Stamp$StampSliderSensorMovedIn  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_2;
            END_IF

        Stamp_states_t#Stamp_Init_2:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampSliderMovedIn  := FALSE;
             a_Stamp$StampSliderMovedOut  := TRUE;
            IF  a_Stamp$StampSliderSensorMovedOut  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_3;
            END_IF

        Stamp_states_t#Stamp_Init_3:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := TRUE;
            IF  a_Stamp$StampLowered  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Stamp_Init_4;
            END_IF

        Stamp_states_t#Stamp_Init_4:
             a_Stamp$_transit  := FALSE;
             a_Stamp$StampPusher  := FALSE;
            IF  a_Stamp$StampUp  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF

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
            END_IF
            IF  a_Stamp$interconnectStampStartCommand  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Green_Lamp;
            END_IF

        Stamp_states_t#Step0:
             a_Stamp$_transit  := FALSE;
            IF  a_Stamp$CraneUp  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampSliderBack;
            END_IF

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
                END_IF
            ELSE
                 a_Stamp$Timer$Q  := FALSE;
                 a_Stamp$Timer$ET  :=  a_Stamp$Timer$PT ;
            END_IF
             a_Stamp$interconnect  :=  a_Stamp$Timer$Q ;
            IF  a_Stamp$interconnect  THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#StampSliderForward;
            END_IF

        Stamp_states_t#Step2:
             a_Stamp$_transit  := FALSE;
            IF ((( a_Stamp$AnalogCranePosition  > INT#16160) AND ( a_Stamp$AnalogCranePosition  < INT#16260)) AND NOT  a_Stamp$StampSliderFilled ) THEN
                 a_Stamp$_transit  := TRUE;
                 a_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF

            END_CASE
    CASE  a_Conveyor$_state  OF
        Conveyor_states_t#Conveyor_Init:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := TRUE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             a_Conveyor$Timer_Conveyor_Test$IN  := TRUE;
             a_Conveyor$Timer_Conveyor_Test$PT  :=  a_Conveyor$Duration_Conveyor_Test ;
            IF  a_Conveyor$Timer_Conveyor_Test$IN  THEN
                 a_Conveyor$Timer_Conveyor_Test$Q  := ( a_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Test$ET  := ( a_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Test$ET  :=  a_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
             a_Conveyor$interconnect_Conveyor_Test  :=  a_Conveyor$Timer_Conveyor_Test$Q ;
            IF  a_Conveyor$interconnect_Conveyor_Test  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Conveyor_init_2;
            END_IF

        Conveyor_states_t#Conveyor_Stop_Empty_Magazin:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             a_Conveyor$interconnectConveyorStartCommand  := FALSE;
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Conveyor_Towards_Stacker:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := TRUE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Runtime_Conveyor;
            END_IF

        Conveyor_states_t#Conveyor_init_2:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             a_Conveyor$interconnect_Conveyor_Test  := FALSE;
             a_Conveyor$Timer_Conveyor_Test$IN  := FALSE;
             a_Conveyor$Timer_Conveyor_Test$PT  := USINT#0;
            IF  a_Conveyor$Timer_Conveyor_Test$IN  THEN
                 a_Conveyor$Timer_Conveyor_Test$Q  := ( a_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Test$ET  := ( a_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Test$ET  :=  a_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Conveyor_pause:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             a_Conveyor$interconnect_Conveyor_Runtime  := FALSE;
             a_Conveyor$Timer_Conveyor_Runtime$IN  := FALSE;
             a_Conveyor$Timer_Conveyor_Runtime$PT  := USINT#0;
            IF  a_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Runtime$ET  :=  a_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Green_Lamp:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$SorterGreenLampConveyor  := TRUE;
             a_Conveyor$interconnectConveyorStartCommand  := FALSE;
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Conveyor_Init;
            END_IF

        Conveyor_states_t#Init:
             a_Conveyor$_transit  := FALSE;
            IF TRUE THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Start_Conveyor;
            END_IF

        Conveyor_states_t#Interstep:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$StartCommandConveyor  := TRUE;
            IF  a_Conveyor$StartVar  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Step0;
            END_IF

        Conveyor_states_t#Runtime_Conveyor:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$Timer_Conveyor_Runtime$IN  := TRUE;
             a_Conveyor$Timer_Conveyor_Runtime$PT  :=  a_Conveyor$Duration_Conveyor_Runtime ;
            IF  a_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Runtime$ET  :=  a_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
             a_Conveyor$interconnect_Conveyor_Runtime  :=  a_Conveyor$Timer_Conveyor_Runtime$Q ;
            IF  a_Conveyor$interconnect_Conveyor_Runtime  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Conveyor_pause;
            END_IF

        Conveyor_states_t#Start_Conveyor:
             a_Conveyor$_transit  := FALSE;
             a_Conveyor$interconnectConveyorTerminationCommand  := FALSE;
             a_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             a_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             a_Conveyor$SorterGreenLampConveyor  := FALSE;
             a_Conveyor$interconnect_Conveyor_Runtime  := FALSE;
             a_Conveyor$interconnect_Conveyor_Test  := FALSE;
             a_Conveyor$Timer_Conveyor_Test$IN  := FALSE;
             a_Conveyor$Timer_Conveyor_Test$PT  := USINT#0;
            IF  a_Conveyor$Timer_Conveyor_Test$IN  THEN
                 a_Conveyor$Timer_Conveyor_Test$Q  := ( a_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Test$ET  := ( a_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Test$ET  :=  a_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
             a_Conveyor$Timer_Conveyor_Runtime$IN  := FALSE;
             a_Conveyor$Timer_Conveyor_Runtime$PT  := USINT#0;
            IF  a_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( a_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := ( a_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     a_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 a_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 a_Conveyor$Timer_Conveyor_Runtime$ET  :=  a_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
             a_Conveyor$StartVar  := FALSE;
             a_Conveyor$StartCommandConveyor  := FALSE;
            IF ( a_Conveyor$SorterStartButton  = TRUE) THEN
                 a_Conveyor$interconnectConveyorStartCommand  := TRUE;
            END_IF
            IF  a_Conveyor$interconnectConveyorStartCommand  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Green_Lamp;
            END_IF

        Conveyor_states_t#Step0:
             a_Conveyor$_transit  := FALSE;
            IF  a_Conveyor$SorterLightbarrierCraneInterface  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Conveyor_Towards_Stacker;
            ELSEIF NOT  a_Conveyor$SorterLightbarrierCraneInterface  THEN
                 a_Conveyor$_transit  := TRUE;
                 a_Conveyor$_state  := Conveyor_states_t#Conveyor_Stop_Empty_Magazin;
            END_IF

            END_CASE
    CASE  a_Pusher$_state  OF
        Pusher_states_t#Check_For_Black:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$Slide2_black  = INT#1) AND ( a_Pusher$Priority_Var_Black  = INT#2)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_black_workpieces;
            ELSEIF (( a_Pusher$Slide3_black  = INT#1) AND ( a_Pusher$Priority_Var_Black  = INT#3)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Third_Slide_black_workpieces;
            ELSEIF (( a_Pusher$Slide1_black  = INT#1) AND ( a_Pusher$Priority_Var_Black  = INT#1)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_black_workpieces;
            END_IF

        Pusher_states_t#Check_For_Metal:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$Slide3_metal  = INT#1) AND ( a_Pusher$Priority_Var_Metal  = INT#3)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Third_Slide_metal_workpieces;
            ELSEIF (( a_Pusher$Slide2_metal  = INT#1) AND ( a_Pusher$Priority_Var_Metal  = INT#2)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_metal_workpieces;
            ELSEIF (( a_Pusher$Slide1_metal  = INT#1) AND ( a_Pusher$Priority_Var_Metal  = INT#1)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_metal_workpieces;
            END_IF

        Pusher_states_t#Check_For_White:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$Slide1_white  = INT#1) AND ( a_Pusher$Priority_Var_White  = INT#1)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_white_workpieces;
            ELSEIF (( a_Pusher$Slide3_white  = INT#1) AND ( a_Pusher$Priority_Var_White  = INT#3)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Third_Slide_white_workpieces;
            ELSEIF (( a_Pusher$Slide2_white  = INT#1) AND ( a_Pusher$Priority_Var_White  = INT#2)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_white_workpieces;
            END_IF

        Pusher_states_t#First_Slide_Timer_Black:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnesssensorCraneInterfaceInverse  = TRUE) THEN
                 a_Pusher$Timer_Slide1_Black$IN  :=  a_Pusher$SorterLightnesssensorCraneInterfaceInverse ;
                 a_Pusher$Timer_Slide1_Black$PT  :=  a_Pusher$Duration_Slide1_Black ;
                IF  a_Pusher$Timer_Slide1_Black$IN  THEN
                     a_Pusher$Timer_Slide1_Black$Q  := ( a_Pusher$Timer_Slide1_Black$ET  = USINT#0);
                    IF ( a_Pusher$Timer_Slide1_Black$ET  > USINT#0) THEN
                         a_Pusher$Timer_Slide1_Black$ET  := ( a_Pusher$Timer_Slide1_Black$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer_Slide1_Black$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer_Slide1_Black$Q  := FALSE;
                     a_Pusher$Timer_Slide1_Black$ET  :=  a_Pusher$Timer_Slide1_Black$PT ;
                END_IF
                 a_Pusher$interconnect_Slide1_Black  :=  a_Pusher$Timer_Slide1_Black$Q ;
            END_IF
            IF  a_Pusher$interconnect_Slide1_Black  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_Black;
            END_IF

        Pusher_states_t#First_Slide_Timer_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer_Slide1_Metal$IN  := TRUE;
             a_Pusher$Timer_Slide1_Metal$PT  :=  a_Pusher$Duration_Slide1_Metal ;
            IF  a_Pusher$Timer_Slide1_Metal$IN  THEN
                 a_Pusher$Timer_Slide1_Metal$Q  := ( a_Pusher$Timer_Slide1_Metal$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide1_Metal$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide1_Metal$ET  := ( a_Pusher$Timer_Slide1_Metal$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide1_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide1_Metal$Q  := FALSE;
                 a_Pusher$Timer_Slide1_Metal$ET  :=  a_Pusher$Timer_Slide1_Metal$PT ;
            END_IF
             a_Pusher$interconnect_Slide1_Metal  :=  a_Pusher$Timer_Slide1_Metal$Q ;
            IF  a_Pusher$interconnect_Slide1_Metal  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_Metal;
            END_IF

        Pusher_states_t#First_Slide_Timer_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer_Slide1_White$IN  := TRUE;
             a_Pusher$Timer_Slide1_White$PT  :=  a_Pusher$Duration_Slide1_White ;
            IF  a_Pusher$Timer_Slide1_White$IN  THEN
                 a_Pusher$Timer_Slide1_White$Q  := ( a_Pusher$Timer_Slide1_White$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide1_White$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide1_White$ET  := ( a_Pusher$Timer_Slide1_White$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide1_White$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide1_White$Q  := FALSE;
                 a_Pusher$Timer_Slide1_White$ET  :=  a_Pusher$Timer_Slide1_White$PT ;
            END_IF
             a_Pusher$interconnect_Slide1_White  :=  a_Pusher$Timer_Slide1_White$Q ;
            IF  a_Pusher$interconnect_Slide1_White  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_White;
            END_IF

        Pusher_states_t#First_Slide_black_workpieces:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_Timer_Black;
            END_IF

        Pusher_states_t#First_Slide_metal_workpieces:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_Timer_Metal;
            END_IF

        Pusher_states_t#First_Slide_white_workpieces:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#First_Slide_Timer_White;
            END_IF

        Pusher_states_t#Init:
             a_Pusher$_transit  := FALSE;
            IF  a_Pusher$StartVar  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep;
            END_IF

        Pusher_states_t#Interstep:
             a_Pusher$_transit  := FALSE;
             a_Pusher$PusherY1  := FALSE;
             a_Pusher$PusherY2  := FALSE;
             a_Pusher$interconnect2  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$StartVar  := FALSE;
             a_Pusher$interconnect_Slide1_Black  := FALSE;
             a_Pusher$interconnect_Slide2_Black  := FALSE;
             a_Pusher$interconnect_Slide1_White  := FALSE;
             a_Pusher$interconnect_Slide2_White  := FALSE;
             a_Pusher$interconnect_Slide1_Metal  := FALSE;
             a_Pusher$interconnect_Slide2_Metal  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Interstep_2:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterLightnessSensorPusher1  AND  a_Pusher$SorterCapacitiveSensorPusher1 ) AND ( a_Pusher$Priority_Var_Metal  > INT#0)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Check_For_Metal;
            ELSEIF ((NOT  a_Pusher$SorterLightnesssensorCraneInterfaceInverse  AND  a_Pusher$SorterLightbarrierCraneInterface ) AND ( a_Pusher$Priority_Var_Black  > INT#0)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Check_For_Black;
            ELSEIF (( a_Pusher$SorterLightnessSensorPusher1  AND NOT  a_Pusher$SorterCapacitiveSensorPusher1 ) AND ( a_Pusher$Priority_Var_White  > INT#0)) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Check_For_White;
            END_IF

        Pusher_states_t#PusherY1_Move_In_Black:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = TRUE) AND ( a_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY1  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_Black;
            END_IF

        Pusher_states_t#PusherY1_Move_In_Metal:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = TRUE) AND ( a_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY1  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_Metal;
            END_IF

        Pusher_states_t#PusherY1_Move_In_White:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = TRUE) AND ( a_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY1  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_White;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_Black:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = FALSE) AND ( a_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY1  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y1_Black;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_Metal:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = FALSE) AND ( a_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY1  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y1_Metal;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_White:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher1MovedOut  = FALSE) AND ( a_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY1  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher1MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y1_White;
            END_IF

        Pusher_states_t#PusherY2_Move_In_Black:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = TRUE) AND ( a_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY2  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_Black;
            END_IF

        Pusher_states_t#PusherY2_Move_In_Metal:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = TRUE) AND ( a_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY2  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_Metal;
            END_IF

        Pusher_states_t#PusherY2_Move_In_White:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = TRUE) AND ( a_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 a_Pusher$PusherY2  := FALSE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedIn  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_White;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_Black:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = FALSE) AND ( a_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY2  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y2_Black;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_Metal:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = FALSE) AND ( a_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY2  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y2_Metal;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_White:
             a_Pusher$_transit  := FALSE;
            IF (( a_Pusher$SorterPusher2MovedOut  = FALSE) AND ( a_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 a_Pusher$PusherY2  := TRUE;
            END_IF
            IF  a_Pusher$SorterPusher2MovedOut  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Y2_White;
            END_IF

        Pusher_states_t#Reset_interconnect3:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect2  := FALSE;
             a_Pusher$Timer2$IN  := FALSE;
             a_Pusher$Timer2$PT  := USINT#0;
            IF  a_Pusher$Timer2$IN  THEN
                 a_Pusher$Timer2$Q  := ( a_Pusher$Timer2$ET  = USINT#0);
                IF ( a_Pusher$Timer2$ET  > USINT#0) THEN
                     a_Pusher$Timer2$ET  := ( a_Pusher$Timer2$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer2$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer2$Q  := FALSE;
                 a_Pusher$Timer2$ET  :=  a_Pusher$Timer2$PT ;
            END_IF
             a_Pusher$Slide3_black  := ( a_Pusher$Slide3_black  - INT#1);
             a_Pusher$Priority_Var_Black  := ( a_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_Black:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide1_Black  := FALSE;
             a_Pusher$Timer_Slide1_Black$IN  := FALSE;
             a_Pusher$Timer_Slide1_Black$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide1_Black$IN  THEN
                 a_Pusher$Timer_Slide1_Black$Q  := ( a_Pusher$Timer_Slide1_Black$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide1_Black$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide1_Black$ET  := ( a_Pusher$Timer_Slide1_Black$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide1_Black$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide1_Black$Q  := FALSE;
                 a_Pusher$Timer_Slide1_Black$ET  :=  a_Pusher$Timer_Slide1_Black$PT ;
            END_IF
             a_Pusher$Slide1_black  := ( a_Pusher$Slide1_black  - INT#1);
             a_Pusher$Priority_Var_Black  := ( a_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide1_Metal  := FALSE;
             a_Pusher$Timer_Slide1_Metal$IN  := FALSE;
             a_Pusher$Timer_Slide1_Metal$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide1_Metal$IN  THEN
                 a_Pusher$Timer_Slide1_Metal$Q  := ( a_Pusher$Timer_Slide1_Metal$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide1_Metal$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide1_Metal$ET  := ( a_Pusher$Timer_Slide1_Metal$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide1_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide1_Metal$Q  := FALSE;
                 a_Pusher$Timer_Slide1_Metal$ET  :=  a_Pusher$Timer_Slide1_Metal$PT ;
            END_IF
             a_Pusher$Slide1_metal  := ( a_Pusher$Slide1_metal  - INT#1);
             a_Pusher$Priority_Var_Metal  := ( a_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide1_White  := FALSE;
             a_Pusher$Timer_Slide1_White$IN  := FALSE;
             a_Pusher$Timer_Slide1_White$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide1_White$IN  THEN
                 a_Pusher$Timer_Slide1_White$Q  := ( a_Pusher$Timer_Slide1_White$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide1_White$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide1_White$ET  := ( a_Pusher$Timer_Slide1_White$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide1_White$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide1_White$Q  := FALSE;
                 a_Pusher$Timer_Slide1_White$ET  :=  a_Pusher$Timer_Slide1_White$PT ;
            END_IF
             a_Pusher$Slide1_white  := ( a_Pusher$Slide1_white  - INT#1);
             a_Pusher$Priority_Var_White  := ( a_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_Black:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide2_Black  := FALSE;
             a_Pusher$Timer_Slide2_Black$IN  := FALSE;
             a_Pusher$Timer_Slide2_Black$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide2_Black$IN  THEN
                 a_Pusher$Timer_Slide2_Black$Q  := ( a_Pusher$Timer_Slide2_Black$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide2_Black$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide2_Black$ET  := ( a_Pusher$Timer_Slide2_Black$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide2_Black$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide2_Black$Q  := FALSE;
                 a_Pusher$Timer_Slide2_Black$ET  :=  a_Pusher$Timer_Slide2_Black$PT ;
            END_IF
             a_Pusher$Slide2_black  := ( a_Pusher$Slide2_black  - INT#1);
             a_Pusher$Priority_Var_Black  := ( a_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide2_Metal  := FALSE;
             a_Pusher$Timer_Slide2_Metal$IN  := FALSE;
             a_Pusher$Timer_Slide2_Metal$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide2_Metal$IN  THEN
                 a_Pusher$Timer_Slide2_Metal$Q  := ( a_Pusher$Timer_Slide2_Metal$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide2_Metal$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide2_Metal$ET  := ( a_Pusher$Timer_Slide2_Metal$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide2_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide2_Metal$Q  := FALSE;
                 a_Pusher$Timer_Slide2_Metal$ET  :=  a_Pusher$Timer_Slide2_Metal$PT ;
            END_IF
             a_Pusher$Slide2_metal  := ( a_Pusher$Slide2_metal  - INT#1);
             a_Pusher$Priority_Var_Metal  := ( a_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect_Slide2_White  := FALSE;
             a_Pusher$Timer_Slide2_White$IN  := FALSE;
             a_Pusher$Timer_Slide2_White$PT  := USINT#0;
            IF  a_Pusher$Timer_Slide2_White$IN  THEN
                 a_Pusher$Timer_Slide2_White$Q  := ( a_Pusher$Timer_Slide2_White$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide2_White$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide2_White$ET  := ( a_Pusher$Timer_Slide2_White$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide2_White$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide2_White$Q  := FALSE;
                 a_Pusher$Timer_Slide2_White$ET  :=  a_Pusher$Timer_Slide2_White$PT ;
            END_IF
             a_Pusher$Slide2_white  := ( a_Pusher$Slide2_white  - INT#1);
             a_Pusher$Priority_Var_White  := ( a_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide3_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$Slide3_metal  := ( a_Pusher$Slide3_metal  - INT#1);
             a_Pusher$Priority_Var_Metal  := ( a_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide3_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$interconnect3  := FALSE;
             a_Pusher$Timer3$IN  := FALSE;
             a_Pusher$Timer3$PT  := USINT#0;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$Slide3_white  := ( a_Pusher$Slide3_white  - INT#1);
             a_Pusher$Priority_Var_White  := ( a_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Second_Slide_Timer_Black:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnesssensorCraneInterfaceInverse  = TRUE) THEN
                 a_Pusher$Timer_Slide2_Black$IN  :=  a_Pusher$SorterLightnesssensorCraneInterfaceInverse ;
                 a_Pusher$Timer_Slide2_Black$PT  :=  a_Pusher$Duration_Slide2_Black ;
                IF  a_Pusher$Timer_Slide2_Black$IN  THEN
                     a_Pusher$Timer_Slide2_Black$Q  := ( a_Pusher$Timer_Slide2_Black$ET  = USINT#0);
                    IF ( a_Pusher$Timer_Slide2_Black$ET  > USINT#0) THEN
                         a_Pusher$Timer_Slide2_Black$ET  := ( a_Pusher$Timer_Slide2_Black$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer_Slide2_Black$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer_Slide2_Black$Q  := FALSE;
                     a_Pusher$Timer_Slide2_Black$ET  :=  a_Pusher$Timer_Slide2_Black$PT ;
                END_IF
                 a_Pusher$interconnect_Slide2_Black  :=  a_Pusher$Timer_Slide2_Black$Q ;
            END_IF
            IF  a_Pusher$interconnect_Slide2_Black  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_Black;
            END_IF

        Pusher_states_t#Second_Slide_Timer_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer_Slide2_Metal$IN  := TRUE;
             a_Pusher$Timer_Slide2_Metal$PT  :=  a_Pusher$Duration_Slide2_Metal ;
            IF  a_Pusher$Timer_Slide2_Metal$IN  THEN
                 a_Pusher$Timer_Slide2_Metal$Q  := ( a_Pusher$Timer_Slide2_Metal$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide2_Metal$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide2_Metal$ET  := ( a_Pusher$Timer_Slide2_Metal$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide2_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide2_Metal$Q  := FALSE;
                 a_Pusher$Timer_Slide2_Metal$ET  :=  a_Pusher$Timer_Slide2_Metal$PT ;
            END_IF
             a_Pusher$interconnect_Slide2_Metal  :=  a_Pusher$Timer_Slide2_Metal$Q ;
            IF  a_Pusher$interconnect_Slide2_Metal  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_Metal;
            END_IF

        Pusher_states_t#Second_Slide_Timer_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer_Slide2_White$IN  := TRUE;
             a_Pusher$Timer_Slide2_White$PT  :=  a_Pusher$Duration_Slide2_White ;
            IF  a_Pusher$Timer_Slide2_White$IN  THEN
                 a_Pusher$Timer_Slide2_White$Q  := ( a_Pusher$Timer_Slide2_White$ET  = USINT#0);
                IF ( a_Pusher$Timer_Slide2_White$ET  > USINT#0) THEN
                     a_Pusher$Timer_Slide2_White$ET  := ( a_Pusher$Timer_Slide2_White$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer_Slide2_White$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer_Slide2_White$Q  := FALSE;
                 a_Pusher$Timer_Slide2_White$ET  :=  a_Pusher$Timer_Slide2_White$PT ;
            END_IF
             a_Pusher$interconnect_Slide2_White  :=  a_Pusher$Timer_Slide2_White$Q ;
            IF  a_Pusher$interconnect_Slide2_White  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_White;
            END_IF

        Pusher_states_t#Second_Slide_black_workpieces:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_Black;
            END_IF

        Pusher_states_t#Second_Slide_metal_workpieces:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnessSensorPusher2  AND  a_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Test_For_Metal;
            END_IF

        Pusher_states_t#Second_Slide_white_workpieces:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnessSensorPusher2  AND NOT  a_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Test_For_White;
            END_IF

        Pusher_states_t#Second_Test_For_Metal:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_Metal;
            END_IF

        Pusher_states_t#Second_Test_For_White:
             a_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_White;
            END_IF

        Pusher_states_t#Third_Slide_black_workpieces:
             a_Pusher$_transit  := FALSE;
            IF (NOT  a_Pusher$SorterLightnessSensorPusher2  AND NOT  a_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Black;
            END_IF

        Pusher_states_t#Third_Slide_metal_workpieces:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnessSensorPusher2  AND  a_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_Metal;
            END_IF

        Pusher_states_t#Third_Slide_white_workpieces:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$SorterLightnessSensorPusher2  AND NOT  a_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Wait_White;
            END_IF

        Pusher_states_t#Wait_Black:
             a_Pusher$_transit  := FALSE;
            IF ((NOT  a_Pusher$SorterLightnessSensorPusher2  AND NOT  a_Pusher$SorterCapacitiveSensorPusher2 ) = TRUE) THEN
                 a_Pusher$Timer2$IN  := (NOT  a_Pusher$SorterLightnessSensorPusher2  AND NOT  a_Pusher$SorterCapacitiveSensorPusher2 );
                 a_Pusher$Timer2$PT  :=  a_Pusher$Duration2 ;
                IF  a_Pusher$Timer2$IN  THEN
                     a_Pusher$Timer2$Q  := ( a_Pusher$Timer2$ET  = USINT#0);
                    IF ( a_Pusher$Timer2$ET  > USINT#0) THEN
                         a_Pusher$Timer2$ET  := ( a_Pusher$Timer2$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer2$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer2$Q  := FALSE;
                     a_Pusher$Timer2$ET  :=  a_Pusher$Timer2$PT ;
                END_IF
                 a_Pusher$interconnect2  :=  a_Pusher$Timer2$Q ;
            END_IF
            IF  a_Pusher$interconnect2  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect3;
            END_IF

        Pusher_states_t#Wait_Metal:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer3$IN  := TRUE;
             a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide3_Metal;
            END_IF

        Pusher_states_t#Wait_White:
             a_Pusher$_transit  := FALSE;
             a_Pusher$Timer3$IN  := TRUE;
             a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
            IF  a_Pusher$Timer3$IN  THEN
                 a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                     a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     a_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 a_Pusher$Timer3$Q  := FALSE;
                 a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
            END_IF
             a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide3_White;
            END_IF

        Pusher_states_t#Wait_Y1_Black:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY1  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY1 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_Black;
            END_IF

        Pusher_states_t#Wait_Y1_Metal:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY1  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY1 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_Metal;
            END_IF

        Pusher_states_t#Wait_Y1_White:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY1  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY1 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_White;
            END_IF

        Pusher_states_t#Wait_Y2_Black:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY2  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY2 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_Black;
            END_IF

        Pusher_states_t#Wait_Y2_Metal:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY2  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY2 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_Metal;
            END_IF

        Pusher_states_t#Wait_Y2_White:
             a_Pusher$_transit  := FALSE;
            IF ( a_Pusher$PusherY2  = TRUE) THEN
                 a_Pusher$Timer3$IN  :=  a_Pusher$PusherY2 ;
                 a_Pusher$Timer3$PT  :=  a_Pusher$Duration3 ;
                IF  a_Pusher$Timer3$IN  THEN
                     a_Pusher$Timer3$Q  := ( a_Pusher$Timer3$ET  = USINT#0);
                    IF ( a_Pusher$Timer3$ET  > USINT#0) THEN
                         a_Pusher$Timer3$ET  := ( a_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         a_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     a_Pusher$Timer3$Q  := FALSE;
                     a_Pusher$Timer3$ET  :=  a_Pusher$Timer3$PT ;
                END_IF
                 a_Pusher$interconnect3  :=  a_Pusher$Timer3$Q ;
            END_IF
            IF  a_Pusher$interconnect3  THEN
                 a_Pusher$_transit  := TRUE;
                 a_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_White;
            END_IF

            END_CASE
    IF (( a_Actuator_SorterGreenLampConveyor  AND  a_Actuator_MagazinGreenLamp ) AND  a_Actuator_StampGreenLamp ) THEN
        IF ((( a_Stamp$StartCommandStamp  AND  a_Crane$StartCommandCrane ) AND  a_Conveyor$StartCommandConveyor ) AND  a_Mag$StartCommandMagazin ) THEN
             a_Crane$StartVar  := TRUE;
             a_Conveyor$StartVar  := TRUE;
             a_Mag$StartVar  := TRUE;
             a_Pusher$StartVar  := TRUE;
             a_Stamp$StartVar  := TRUE;
             a_DIAGNOSIS_ACTIVE  := TRUE;
        END_IF
    END_IF
     a_Crane$SFCReset  := FALSE;
     a_Conveyor$SFCReset  := FALSE;
     a_Mag$SFCReset  := FALSE;
     a_Pusher$SFCReset  := FALSE;
     a_Stamp$SFCReset  := FALSE;

     a_Crane$AnalogCranePressure  :=  a_PARAMETER_CRANE_PRESSURE_METALLIC ;


ELSEIF ((NOT  a_Sensor_SorterEmergencyStop  OR NOT  a_Sensor_StampEmergencyStop ) OR NOT  a_Sensor_MagazinEmergencyStop ) THEN
     a_Actuator_MagazinSlider  := FALSE;
     a_Actuator_CraneLower  := FALSE;
     a_Actuator_MagazinVacuumOn  := FALSE;
     a_Actuator_MagazinVacuumOff  := TRUE;
     a_Actuator_MagazinGreenLamp  := FALSE;
     a_Actuator_CraneTurnCounterclockwise  := FALSE;
     a_Actuator_CraneTurnClockwise  := FALSE;
     a_Actuator_SorterConveyorTowardsStacker  := FALSE;
     a_Actuator_SorterConveyorTowardsCrane  := FALSE;
     a_Actuator_SorterGreenLampConveyor  := FALSE;
     a_Actuator_PusherY1  := FALSE;
     a_Actuator_PusherY2  := FALSE;
     a_Actuator_StampSliderMovedOut  := TRUE;
     a_Actuator_StampSliderMovedIn  := FALSE;
     a_Actuator_StampGreenLamp  := FALSE;
     a_Actuator_StampPusher  := FALSE;
     a_Actuator_AnalogCranePressure  := INT#0;
     a_Crane$SFCReset  := TRUE;
     a_Conveyor$SFCReset  := TRUE;
     a_Mag$SFCReset  := TRUE;
     a_Pusher$SFCReset  := TRUE;
     a_Stamp$SFCReset  := TRUE;
     a_Crane$StartVar  := FALSE;
     a_Conveyor$StartVar  := FALSE;
     a_Mag$StartVar  := FALSE;
     a_Pusher$StartVar  := FALSE;
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
 b_Mag$AnalogCranePosition  :=  b_Sensor_AnalogCranePosition ;
 b_Mag$StartButtonMagazin  :=  b_Sensor_StartButtonMagazin ;
 b_Actuator_MagazinSlider  :=  b_Mag$MagazinSlider ;
 b_Actuator_MagazinGreenLamp  :=  b_Mag$MagazinGreenLamp ;
 b_Crane$CraneUp  :=  b_Sensor_CraneUp ;
 b_Crane$CraneDown  :=  b_Sensor_CraneDown ;
 b_Crane$CraneSucked  :=  b_Sensor_CraneSucked ;
 b_Crane$MagazinCapacitiveSensor  :=  b_Sensor_MagazinCapacitiveSensor ;
 b_Crane$SliderMovedOut  :=  b_Sensor_SliderMovedOut ;
 b_Crane$WorkpieceReady  :=  b_Sensor_WorkpieceReady ;
 b_Crane$MagazinOpticalSensor  :=  b_Sensor_MagazinOpticalSensor ;
 b_Crane$StampSliderFilled  :=  b_Sensor_StampSliderFilled ;
 b_Crane$StampSliderSensorMovedOut  :=  b_Sensor_StampSliderSensorMovedOut ;
 b_Crane$StampLowered  :=  b_Sensor_StampLowered ;
 b_Crane$AnalogCranePosition  :=  b_Sensor_AnalogCranePosition ;
 b_Crane$StartButtonMagazin  :=  b_Sensor_StartButtonMagazin ;

//Diagnosis
// old:  b_Actuator_AnalogCranePressure 
// new:  b_Crane$AnalogCranePressure ;
 b_Actuator_CraneTurnCounterclockwise  :=  b_Crane$CraneTurnCounterclockwise ;
 b_Actuator_CraneTurnClockwise  :=  b_Crane$CraneTurnClockwise ;

IF  b_DIAGNOSIS_ACTIVE  THEN
        IF  b_Sensor_CraneSucked  AND ( b_Crane$AnalogCranePressure  <= 0 OR  b_Crane$AnalogCranePressure  > 10000) THEN
                 b_Actuator_CraneTurnCounterclockwise  := FALSE;
                 b_Actuator_CraneTurnClockwise  := FALSE;
        END_IF
END_IF

//End of Diagnosis

 b_Actuator_CraneLower  :=  b_Crane$CraneLower ;
 b_Actuator_MagazinVacuumOff  :=  b_Crane$MagazinVacuumOff ;
 b_Actuator_MagazinVacuumOn  :=  b_Crane$MagazinVacuumOn ;
 b_Actuator_AnalogCranePressure  :=  b_Crane$AnalogCranePressure ;
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
 b_Stamp$AnalogCranePosition  :=  b_Sensor_AnalogCranePosition ;
 b_Stamp$StampStartButton  :=  b_Sensor_StampStartButton ;
 b_Actuator_StampSliderMovedOut  :=  b_Stamp$StampSliderMovedOut ;
 b_Actuator_StampSliderMovedIn  :=  b_Stamp$StampSliderMovedIn ;
 b_Actuator_StampWhiteLamp  :=  b_Stamp$StampWhiteLamp ;
 b_Actuator_StampPusher  :=  b_Stamp$StampPusher ;
 b_Actuator_StampGreenLamp  :=  b_Stamp$StampGreenLamp ;
 b_Conveyor$SorterStartButton  :=  b_Sensor_SorterStartButton ;
 b_Conveyor$SorterSwitchManuellAutomatic  :=  b_Sensor_SorterSwitchManuellAutomatic ;
 b_Conveyor$SorterLightbarrierCraneInterface  :=  b_Sensor_SorterLightbarrierCraneInterface ;
 b_Actuator_SorterConveyorTowardsStacker  :=  b_Conveyor$SorterConveyorTowardsStacker ;
 b_Actuator_SorterConveyorTowardsCrane  :=  b_Conveyor$SorterConveyorTowardsCrane ;
 b_Actuator_SorterGreenLampConveyor  :=  b_Conveyor$SorterGreenLampConveyor ;
 b_Actuator_SorterWhiteLampConveyor  :=  b_Conveyor$SorterWhiteLampConveyor ;
 b_Pusher$SorterLightnesssensorCraneInterfaceInverse  :=  b_Sensor_SorterLightnesssensorCraneInterfaceInverse ;
 b_Pusher$SorterLightbarrierCraneInterface  :=  b_Sensor_SorterLightbarrierCraneInterface ;
 b_Pusher$SorterCapacitiveSensorPusher1  :=  b_Sensor_SorterCapacitiveSensorPusher1 ;
 b_Pusher$SorterLightnessSensorPusher1  :=  b_Sensor_SorterLightnessSensorPusher1 ;
 b_Pusher$SorterCapacitiveSensorPusher2  :=  b_Sensor_SorterCapacitiveSensorPusher2 ;
 b_Pusher$SorterLightnessSensorPusher2  :=  b_Sensor_SorterLightnessSensorPusher2 ;
 b_Pusher$SorterLightnessSensorPusher3  :=  b_Sensor_SorterLightnessSensorPusher3 ;
 b_Pusher$SorterPusher1MovedOut  :=  b_Sensor_SorterPusher1MovedOut ;
 b_Pusher$SorterPusher1MovedIn  :=  b_Sensor_SorterPusher1MovedIn ;
 b_Pusher$SorterPusher2MovedOut  :=  b_Sensor_SorterPusher2MovedOut ;
 b_Pusher$SorterPusher2MovedIn  :=  b_Sensor_SorterPusher2MovedIn ;
 b_Pusher$SorterStartButton  :=  b_Sensor_SorterStartButton ;
 b_Actuator_PusherY1  :=  b_Pusher$PusherY1 ;
 b_Actuator_PusherY2  :=  b_Pusher$PusherY2 ;

IF (( b_Sensor_SorterEmergencyStop  AND  b_Sensor_StampEmergencyStop ) AND  b_Sensor_MagazinEmergencyStop ) THEN
    CASE  b_Mag$_state  OF
        Magazin_states_t#Green_Lamp:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinGreenLamp  := TRUE;
             b_Mag$interconnectMagazinStartCommand  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Magazin_Init;
            END_IF

        Magazin_states_t#Init:
             b_Mag$_transit  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Start_Magazin;
            END_IF

        Magazin_states_t#Interstep:
             b_Mag$_transit  := FALSE;
             b_Mag$StartCommandMagazin  := TRUE;
            IF  b_Mag$StartVar  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#convey;
            END_IF

        Magazin_states_t#Magazin_Init:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := TRUE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Magazin_Init_2;
            END_IF

        Magazin_states_t#Magazin_Init_2:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := FALSE;
            IF TRUE THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#Slider_Move_Back:
             b_Mag$_transit  := FALSE;
            IF (( b_Mag$SliderMovedOut  = TRUE) AND ( b_Mag$SliderNotMovedOut  = FALSE)) THEN
                 b_Mag$MagazinSlider  := FALSE;
            END_IF
            IF  b_Mag$CraneUp  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Step1;
            END_IF

        Magazin_states_t#Start_Magazin:
             b_Mag$_transit  := FALSE;
             b_Mag$MagazinSlider  := FALSE;
             b_Mag$MagazinGreenLamp  := FALSE;
             b_Mag$StartVar  := FALSE;
             b_Mag$StartCommandMagazin  := FALSE;
            IF ( b_Mag$StartButtonMagazin  = TRUE) THEN
                 b_Mag$interconnectMagazinStartCommand  := TRUE;
            END_IF
            IF  b_Mag$interconnectMagazinStartCommand  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Green_Lamp;
            END_IF

        Magazin_states_t#Step0:
             b_Mag$_transit  := FALSE;
            IF  b_Mag$CraneDown  THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Slider_Move_Back;
            END_IF

        Magazin_states_t#Step1:
             b_Mag$_transit  := FALSE;
            IF (( b_Mag$AnalogCranePosition  > INT#16160) AND ( b_Mag$AnalogCranePosition  < INT#16260)) THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Interstep;
            END_IF

        Magazin_states_t#convey:
             b_Mag$_transit  := FALSE;
            IF  b_Mag$SliderNotMovedOut  THEN
                 b_Mag$MagazinSlider  := TRUE;
            END_IF
            IF (( b_Mag$AnalogCranePosition  > INT#24290) AND ( b_Mag$AnalogCranePosition  < INT#24390)) THEN
                 b_Mag$_transit  := TRUE;
                 b_Mag$_state  := Magazin_states_t#Step0;
            END_IF

            END_CASE
    CASE  b_Crane$_state  OF
        Crane_states_t#Crane_Go_Up:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step3;
            END_IF

        Crane_states_t#Crane_Go_Up_White:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step3;
            END_IF

        Crane_states_t#Crane_Init:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := TRUE;
             b_Crane$interconnectCraneStartCommand  := FALSE;
             b_Crane$AnalogCranePressure  :=  b_PARAMETER_CRANE_PRESSURE_METALLIC ;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Init_2;
            END_IF

        Crane_states_t#Crane_Init_2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_At_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_At_Stamp2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
             b_Crane$AnalogCranePressure  := INT#0;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Right_From_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Magazin:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_Magazin_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_Magazin_White:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_White;
            END_IF

        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$CraneUp  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF

        Crane_states_t#Crane_Lower:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
             b_Crane$CraneLower  := TRUE;
             b_Crane$AnalogCranePressure  := INT#0;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step0;
            END_IF

        Crane_states_t#Crane_On_Conveyor:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Metallic2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release2;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release_Black;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release_Workpiece;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF  b_Crane$StampLowered  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep_4;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic2_Lower:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Suck_At_Stamp2;
            END_IF

        Crane_states_t#Crane_On_Stamp_Stop_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#Crane_On_Stamp_White:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#release_Workpiece_White;
            END_IF

        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#8160) AND ( b_Crane$AnalogCranePosition  < INT#8260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF

        Crane_states_t#Crane_Turn_Left_From_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#16060) AND ( b_Crane$AnalogCranePosition  < INT#16160)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#8160) AND ( b_Crane$AnalogCranePosition  < INT#8260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_Metallic2:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#8160) AND ( b_Crane$AnalogCranePosition  < INT#8260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic2;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#16160) AND ( b_Crane$AnalogCranePosition  < INT#16260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#16160) AND ( b_Crane$AnalogCranePosition  < INT#16260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF

        Crane_states_t#Crane_Turn_Left_White:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := TRUE;
             b_Crane$CraneTurnClockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#8160) AND ( b_Crane$AnalogCranePosition  < INT#8260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_White;
            END_IF

        Crane_states_t#Crane_Turn_Right_From_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#16160) AND ( b_Crane$AnalogCranePosition  < INT#16260)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Conveyor_Metallic2;
            END_IF

        Crane_states_t#Init:
             b_Crane$_transit  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#Interstep:
             b_Crane$_transit  := FALSE;
             b_Crane$StartCommandCrane  := TRUE;
            IF  b_Crane$StartVar  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep_2;
            END_IF

        Crane_states_t#Interstep_2:
             b_Crane$_transit  := FALSE;
            IF  b_Crane$SliderMovedOut  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#TimeDelay;
            END_IF

        Crane_states_t#Interstep_3:
             b_Crane$_transit  := FALSE;
            IF NOT  b_Crane$WorkpieceReady  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#No_Workpiece_ready;
            ELSEIF  b_Crane$WorkpieceReady  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Turn_Right;
            END_IF

        Crane_states_t#Interstep_4:
             b_Crane$_transit  := FALSE;
            IF  b_Crane$StampSliderSensorMovedOut  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_On_Stamp_Metallic2_Lower;
            END_IF

        Crane_states_t#Lower_Crane:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := TRUE;
            IF  b_Crane$CraneDown  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Suck_At_Stamp;
            END_IF

        Crane_states_t#Magazin_Stop:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lower;
            END_IF

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
            END_IF

        Crane_states_t#Magazin_Stop_Final:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#No_Workpiece_ready:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := FALSE;
             b_Crane$MagazinVacuumOff  := FALSE;
             b_Crane$CraneLower  := FALSE;
            IF  b_Crane$StampSliderFilled  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Turn_Left_Metallic2;
            ELSEIF NOT  b_Crane$StampSliderFilled  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Turn_Right_Final;
            END_IF

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
                END_IF
            ELSE
                 b_Crane$Timer1$Q  := FALSE;
                 b_Crane$Timer1$ET  :=  b_Crane$Timer1$PT ;
            END_IF
            IF  b_Crane$SliderMovedOut  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Lower_Crane;
            END_IF

        Crane_states_t#Stamp_Pressure_Profile_Set_Metallic:
             b_Crane$_transit  := FALSE;
             b_Crane$AnalogCranePressure  :=  b_PARAMETER_CRANE_PRESSURE_METALLIC ;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF

        Crane_states_t#Stamp_Pressure_Profile_Set_White:
             b_Crane$_transit  := FALSE;
             b_Crane$AnalogCranePressure  :=  b_PARAMETER_CRANE_PRESSURE_WHITE ;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Magazin_White;
            END_IF

        Crane_states_t#Start_Crane:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneLower  := FALSE;
             b_Crane$MagazinVacuumOff  := FALSE;
             b_Crane$MagazinVacuumOn  := FALSE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$CraneTurnClockwise  := FALSE;
             b_Crane$AnalogCranePressure  := INT#0;
             b_Crane$StartVar  := FALSE;
             b_Crane$StartCommandCrane  := FALSE;
            IF ( b_Crane$StartButtonMagazin  = TRUE) THEN
                 b_Crane$interconnectCraneStartCommand  := TRUE;
            END_IF
            IF  b_Crane$interconnectCraneStartCommand  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Init;
            END_IF

        Crane_states_t#Step0:
             b_Crane$_transit  := FALSE;
            IF ( b_Crane$MagazinCapacitiveSensor  AND  b_Crane$MagazinOpticalSensor ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Stamp_Pressure_Profile_Set_Metallic;
            ELSEIF (NOT  b_Crane$MagazinCapacitiveSensor  AND  b_Crane$MagazinOpticalSensor ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Stamp_Pressure_Profile_Set_White;
            ELSEIF (NOT  b_Crane$MagazinCapacitiveSensor  AND NOT  b_Crane$MagazinOpticalSensor ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Magazin;
            END_IF

        Crane_states_t#Step2:
             b_Crane$_transit  := FALSE;
            IF ( b_Crane$MagazinCapacitiveSensor  OR  b_Crane$MagazinOpticalSensor ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#pause;
            ELSEIF (NOT  b_Crane$MagazinCapacitiveSensor  AND NOT  b_Crane$MagazinOpticalSensor ) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Turn_Right_Black;
            END_IF

        Crane_states_t#Step3:
             b_Crane$_transit  := FALSE;
            IF NOT  b_Crane$WorkpieceReady  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step4;
            ELSEIF  b_Crane$WorkpieceReady  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Step2;
            END_IF

        Crane_states_t#Step4:
             b_Crane$_transit  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Suck_At_Stamp:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF

        Crane_states_t#Suck_At_Stamp2:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := TRUE;
             b_Crane$MagazinVacuumOff  := FALSE;
            IF  b_Crane$CraneSucked  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_At_Stamp2;
            END_IF

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
                END_IF
            ELSE
                 b_Crane$TimeDelay_Timer$Q  := FALSE;
                 b_Crane$TimeDelay_Timer$ET  :=  b_Crane$TimeDelay_Timer$PT ;
            END_IF
             b_Crane$TimeDelay_Timer_interconnect  :=  b_Crane$TimeDelay_Timer$Q ;
            IF  b_Crane$TimeDelay_Timer_interconnect  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Interstep_3;
            END_IF

        Crane_states_t#Turn_Right:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#24290) AND ( b_Crane$AnalogCranePosition  < INT#24390)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Magazin_Stop;
            END_IF

        Crane_states_t#Turn_Right_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
            IF (( b_Crane$AnalogCranePosition  > INT#24290) AND ( b_Crane$AnalogCranePosition  < INT#24390)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Magazin_Stop_Black;
            END_IF

        Crane_states_t#Turn_Right_Final:
             b_Crane$_transit  := FALSE;
             b_Crane$CraneTurnClockwise  := TRUE;
             b_Crane$CraneTurnCounterclockwise  := FALSE;
             b_Crane$AnalogCranePressure  := INT#0;
            IF (( b_Crane$AnalogCranePosition  > INT#24290) AND ( b_Crane$AnalogCranePosition  < INT#24390)) THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Magazin_Stop_Final;
            END_IF

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
                END_IF
            ELSE
                 b_Crane$Timer1$Q  := FALSE;
                 b_Crane$Timer1$ET  :=  b_Crane$Timer1$PT ;
            END_IF
             b_Crane$interconnect  :=  b_Crane$Timer1$Q ;
            IF  b_Crane$interconnect  THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#release:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor;
            END_IF

        Crane_states_t#release2:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor2;
            END_IF

        Crane_states_t#release_Black:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOn  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF

        Crane_states_t#release_Workpiece:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Go_Up;
            END_IF

        Crane_states_t#release_Workpiece_White:
             b_Crane$_transit  := FALSE;
             b_Crane$MagazinVacuumOff  := TRUE;
             b_Crane$MagazinVacuumOn  := FALSE;
            IF TRUE THEN
                 b_Crane$_transit  := TRUE;
                 b_Crane$_state  := Crane_states_t#Crane_Go_Up_White;
            END_IF

            END_CASE
    CASE  b_Stamp$_state  OF
        Stamp_states_t#Green_Lamp:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampGreenLamp  := TRUE;
             b_Stamp$interconnectStampStartCommand  := FALSE;
            IF TRUE THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_1;
            END_IF

        Stamp_states_t#Init:
             b_Stamp$_transit  := FALSE;
            IF TRUE THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Start_Stamp;
            END_IF

        Stamp_states_t#Interstep:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StartCommandStamp  := TRUE;
            IF  b_Stamp$StartVar  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Intertsep_2;
            END_IF

        Stamp_states_t#Intertsep_2:
             b_Stamp$_transit  := FALSE;
            IF  b_Stamp$StampSliderFilled  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step0;
            END_IF

        Stamp_states_t#StampProcess:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := FALSE;
             b_Stamp$StampPusher  := TRUE;
            IF  b_Stamp$StampLowered  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step1;
            END_IF

        Stamp_states_t#StampSliderBack:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := TRUE;
             b_Stamp$StampSliderMovedOut  := FALSE;
            IF  b_Stamp$StampSliderSensorMovedIn  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampProcess;
            END_IF

        Stamp_states_t#StampSliderForward:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := FALSE;
             b_Stamp$StampSliderMovedOut  := TRUE;
            IF (( b_Stamp$StampLowered  = FALSE) AND ( b_Stamp$StampUp  = TRUE)) THEN
                 b_Stamp$interconnect  := FALSE;
            END_IF
             b_Stamp$Timer$IN  := FALSE;
             b_Stamp$Timer$PT  := USINT#0;
            IF  b_Stamp$Timer$IN  THEN
                 b_Stamp$Timer$Q  := ( b_Stamp$Timer$ET  = USINT#0);
                IF ( b_Stamp$Timer$ET  > USINT#0) THEN
                     b_Stamp$Timer$ET  := ( b_Stamp$Timer$ET  - USINT#1);
                ELSE
                     b_Stamp$Timer$ET  := USINT#0;
                END_IF
            ELSE
                 b_Stamp$Timer$Q  := FALSE;
                 b_Stamp$Timer$ET  :=  b_Stamp$Timer$PT ;
            END_IF
            IF  b_Stamp$StampSliderMovedOut  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Step2;
            END_IF

        Stamp_states_t#Stamp_Init_1:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := TRUE;
             b_Stamp$StampSliderMovedOut  := FALSE;
            IF  b_Stamp$StampSliderSensorMovedIn  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_2;
            END_IF

        Stamp_states_t#Stamp_Init_2:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampSliderMovedIn  := FALSE;
             b_Stamp$StampSliderMovedOut  := TRUE;
            IF  b_Stamp$StampSliderSensorMovedOut  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_3;
            END_IF

        Stamp_states_t#Stamp_Init_3:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := TRUE;
            IF  b_Stamp$StampLowered  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Stamp_Init_4;
            END_IF

        Stamp_states_t#Stamp_Init_4:
             b_Stamp$_transit  := FALSE;
             b_Stamp$StampPusher  := FALSE;
            IF  b_Stamp$StampUp  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF

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
            END_IF
            IF  b_Stamp$interconnectStampStartCommand  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Green_Lamp;
            END_IF

        Stamp_states_t#Step0:
             b_Stamp$_transit  := FALSE;
            IF  b_Stamp$CraneUp  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampSliderBack;
            END_IF

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
                END_IF
            ELSE
                 b_Stamp$Timer$Q  := FALSE;
                 b_Stamp$Timer$ET  :=  b_Stamp$Timer$PT ;
            END_IF
             b_Stamp$interconnect  :=  b_Stamp$Timer$Q ;
            IF  b_Stamp$interconnect  THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#StampSliderForward;
            END_IF

        Stamp_states_t#Step2:
             b_Stamp$_transit  := FALSE;
            IF ((( b_Stamp$AnalogCranePosition  > INT#16160) AND ( b_Stamp$AnalogCranePosition  < INT#16260)) AND NOT  b_Stamp$StampSliderFilled ) THEN
                 b_Stamp$_transit  := TRUE;
                 b_Stamp$_state  := Stamp_states_t#Interstep;
            END_IF

            END_CASE
    CASE  b_Conveyor$_state  OF
        Conveyor_states_t#Conveyor_Init:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := TRUE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             b_Conveyor$Timer_Conveyor_Test$IN  := TRUE;
             b_Conveyor$Timer_Conveyor_Test$PT  :=  b_Conveyor$Duration_Conveyor_Test ;
            IF  b_Conveyor$Timer_Conveyor_Test$IN  THEN
                 b_Conveyor$Timer_Conveyor_Test$Q  := ( b_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Test$ET  := ( b_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Test$ET  :=  b_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
             b_Conveyor$interconnect_Conveyor_Test  :=  b_Conveyor$Timer_Conveyor_Test$Q ;
            IF  b_Conveyor$interconnect_Conveyor_Test  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Conveyor_init_2;
            END_IF

        Conveyor_states_t#Conveyor_Stop_Empty_Magazin:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             b_Conveyor$interconnectConveyorStartCommand  := FALSE;
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Conveyor_Towards_Stacker:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := TRUE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Runtime_Conveyor;
            END_IF

        Conveyor_states_t#Conveyor_init_2:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             b_Conveyor$interconnect_Conveyor_Test  := FALSE;
             b_Conveyor$Timer_Conveyor_Test$IN  := FALSE;
             b_Conveyor$Timer_Conveyor_Test$PT  := USINT#0;
            IF  b_Conveyor$Timer_Conveyor_Test$IN  THEN
                 b_Conveyor$Timer_Conveyor_Test$Q  := ( b_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Test$ET  := ( b_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Test$ET  :=  b_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Conveyor_pause:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             b_Conveyor$interconnect_Conveyor_Runtime  := FALSE;
             b_Conveyor$Timer_Conveyor_Runtime$IN  := FALSE;
             b_Conveyor$Timer_Conveyor_Runtime$PT  := USINT#0;
            IF  b_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Runtime$ET  :=  b_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Interstep;
            END_IF

        Conveyor_states_t#Green_Lamp:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$SorterGreenLampConveyor  := TRUE;
             b_Conveyor$interconnectConveyorStartCommand  := FALSE;
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Conveyor_Init;
            END_IF

        Conveyor_states_t#Init:
             b_Conveyor$_transit  := FALSE;
            IF TRUE THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Start_Conveyor;
            END_IF

        Conveyor_states_t#Interstep:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$StartCommandConveyor  := TRUE;
            IF  b_Conveyor$StartVar  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Step0;
            END_IF

        Conveyor_states_t#Runtime_Conveyor:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$Timer_Conveyor_Runtime$IN  := TRUE;
             b_Conveyor$Timer_Conveyor_Runtime$PT  :=  b_Conveyor$Duration_Conveyor_Runtime ;
            IF  b_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Runtime$ET  :=  b_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
             b_Conveyor$interconnect_Conveyor_Runtime  :=  b_Conveyor$Timer_Conveyor_Runtime$Q ;
            IF  b_Conveyor$interconnect_Conveyor_Runtime  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Conveyor_pause;
            END_IF

        Conveyor_states_t#Start_Conveyor:
             b_Conveyor$_transit  := FALSE;
             b_Conveyor$interconnectConveyorTerminationCommand  := FALSE;
             b_Conveyor$SorterConveyorTowardsStacker  := FALSE;
             b_Conveyor$SorterConveyorTowardsCrane  := FALSE;
             b_Conveyor$SorterGreenLampConveyor  := FALSE;
             b_Conveyor$interconnect_Conveyor_Runtime  := FALSE;
             b_Conveyor$interconnect_Conveyor_Test  := FALSE;
             b_Conveyor$Timer_Conveyor_Test$IN  := FALSE;
             b_Conveyor$Timer_Conveyor_Test$PT  := USINT#0;
            IF  b_Conveyor$Timer_Conveyor_Test$IN  THEN
                 b_Conveyor$Timer_Conveyor_Test$Q  := ( b_Conveyor$Timer_Conveyor_Test$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Test$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Test$ET  := ( b_Conveyor$Timer_Conveyor_Test$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Test$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Test$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Test$ET  :=  b_Conveyor$Timer_Conveyor_Test$PT ;
            END_IF
             b_Conveyor$Timer_Conveyor_Runtime$IN  := FALSE;
             b_Conveyor$Timer_Conveyor_Runtime$PT  := USINT#0;
            IF  b_Conveyor$Timer_Conveyor_Runtime$IN  THEN
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  = USINT#0);
                IF ( b_Conveyor$Timer_Conveyor_Runtime$ET  > USINT#0) THEN
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := ( b_Conveyor$Timer_Conveyor_Runtime$ET  - USINT#1);
                ELSE
                     b_Conveyor$Timer_Conveyor_Runtime$ET  := USINT#0;
                END_IF
            ELSE
                 b_Conveyor$Timer_Conveyor_Runtime$Q  := FALSE;
                 b_Conveyor$Timer_Conveyor_Runtime$ET  :=  b_Conveyor$Timer_Conveyor_Runtime$PT ;
            END_IF
             b_Conveyor$StartVar  := FALSE;
             b_Conveyor$StartCommandConveyor  := FALSE;
            IF ( b_Conveyor$SorterStartButton  = TRUE) THEN
                 b_Conveyor$interconnectConveyorStartCommand  := TRUE;
            END_IF
            IF  b_Conveyor$interconnectConveyorStartCommand  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Green_Lamp;
            END_IF

        Conveyor_states_t#Step0:
             b_Conveyor$_transit  := FALSE;
            IF  b_Conveyor$SorterLightbarrierCraneInterface  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Conveyor_Towards_Stacker;
            ELSEIF NOT  b_Conveyor$SorterLightbarrierCraneInterface  THEN
                 b_Conveyor$_transit  := TRUE;
                 b_Conveyor$_state  := Conveyor_states_t#Conveyor_Stop_Empty_Magazin;
            END_IF

            END_CASE
    CASE  b_Pusher$_state  OF
        Pusher_states_t#Check_For_Black:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$Slide2_black  = INT#1) AND ( b_Pusher$Priority_Var_Black  = INT#2)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_black_workpieces;
            ELSEIF (( b_Pusher$Slide3_black  = INT#1) AND ( b_Pusher$Priority_Var_Black  = INT#3)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Third_Slide_black_workpieces;
            ELSEIF (( b_Pusher$Slide1_black  = INT#1) AND ( b_Pusher$Priority_Var_Black  = INT#1)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_black_workpieces;
            END_IF

        Pusher_states_t#Check_For_Metal:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$Slide3_metal  = INT#1) AND ( b_Pusher$Priority_Var_Metal  = INT#3)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Third_Slide_metal_workpieces;
            ELSEIF (( b_Pusher$Slide2_metal  = INT#1) AND ( b_Pusher$Priority_Var_Metal  = INT#2)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_metal_workpieces;
            ELSEIF (( b_Pusher$Slide1_metal  = INT#1) AND ( b_Pusher$Priority_Var_Metal  = INT#1)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_metal_workpieces;
            END_IF

        Pusher_states_t#Check_For_White:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$Slide1_white  = INT#1) AND ( b_Pusher$Priority_Var_White  = INT#1)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_white_workpieces;
            ELSEIF (( b_Pusher$Slide3_white  = INT#1) AND ( b_Pusher$Priority_Var_White  = INT#3)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Third_Slide_white_workpieces;
            ELSEIF (( b_Pusher$Slide2_white  = INT#1) AND ( b_Pusher$Priority_Var_White  = INT#2)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_white_workpieces;
            END_IF

        Pusher_states_t#First_Slide_Timer_Black:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnesssensorCraneInterfaceInverse  = TRUE) THEN
                 b_Pusher$Timer_Slide1_Black$IN  :=  b_Pusher$SorterLightnesssensorCraneInterfaceInverse ;
                 b_Pusher$Timer_Slide1_Black$PT  :=  b_Pusher$Duration_Slide1_Black ;
                IF  b_Pusher$Timer_Slide1_Black$IN  THEN
                     b_Pusher$Timer_Slide1_Black$Q  := ( b_Pusher$Timer_Slide1_Black$ET  = USINT#0);
                    IF ( b_Pusher$Timer_Slide1_Black$ET  > USINT#0) THEN
                         b_Pusher$Timer_Slide1_Black$ET  := ( b_Pusher$Timer_Slide1_Black$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer_Slide1_Black$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer_Slide1_Black$Q  := FALSE;
                     b_Pusher$Timer_Slide1_Black$ET  :=  b_Pusher$Timer_Slide1_Black$PT ;
                END_IF
                 b_Pusher$interconnect_Slide1_Black  :=  b_Pusher$Timer_Slide1_Black$Q ;
            END_IF
            IF  b_Pusher$interconnect_Slide1_Black  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_Black;
            END_IF

        Pusher_states_t#First_Slide_Timer_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer_Slide1_Metal$IN  := TRUE;
             b_Pusher$Timer_Slide1_Metal$PT  :=  b_Pusher$Duration_Slide1_Metal ;
            IF  b_Pusher$Timer_Slide1_Metal$IN  THEN
                 b_Pusher$Timer_Slide1_Metal$Q  := ( b_Pusher$Timer_Slide1_Metal$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide1_Metal$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide1_Metal$ET  := ( b_Pusher$Timer_Slide1_Metal$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide1_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide1_Metal$Q  := FALSE;
                 b_Pusher$Timer_Slide1_Metal$ET  :=  b_Pusher$Timer_Slide1_Metal$PT ;
            END_IF
             b_Pusher$interconnect_Slide1_Metal  :=  b_Pusher$Timer_Slide1_Metal$Q ;
            IF  b_Pusher$interconnect_Slide1_Metal  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_Metal;
            END_IF

        Pusher_states_t#First_Slide_Timer_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer_Slide1_White$IN  := TRUE;
             b_Pusher$Timer_Slide1_White$PT  :=  b_Pusher$Duration_Slide1_White ;
            IF  b_Pusher$Timer_Slide1_White$IN  THEN
                 b_Pusher$Timer_Slide1_White$Q  := ( b_Pusher$Timer_Slide1_White$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide1_White$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide1_White$ET  := ( b_Pusher$Timer_Slide1_White$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide1_White$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide1_White$Q  := FALSE;
                 b_Pusher$Timer_Slide1_White$ET  :=  b_Pusher$Timer_Slide1_White$PT ;
            END_IF
             b_Pusher$interconnect_Slide1_White  :=  b_Pusher$Timer_Slide1_White$Q ;
            IF  b_Pusher$interconnect_Slide1_White  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_Out_White;
            END_IF

        Pusher_states_t#First_Slide_black_workpieces:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_Timer_Black;
            END_IF

        Pusher_states_t#First_Slide_metal_workpieces:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_Timer_Metal;
            END_IF

        Pusher_states_t#First_Slide_white_workpieces:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#First_Slide_Timer_White;
            END_IF

        Pusher_states_t#Init:
             b_Pusher$_transit  := FALSE;
            IF  b_Pusher$StartVar  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep;
            END_IF

        Pusher_states_t#Interstep:
             b_Pusher$_transit  := FALSE;
             b_Pusher$PusherY1  := FALSE;
             b_Pusher$PusherY2  := FALSE;
             b_Pusher$interconnect2  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$StartVar  := FALSE;
             b_Pusher$interconnect_Slide1_Black  := FALSE;
             b_Pusher$interconnect_Slide2_Black  := FALSE;
             b_Pusher$interconnect_Slide1_White  := FALSE;
             b_Pusher$interconnect_Slide2_White  := FALSE;
             b_Pusher$interconnect_Slide1_Metal  := FALSE;
             b_Pusher$interconnect_Slide2_Metal  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Interstep_2:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterLightnessSensorPusher1  AND  b_Pusher$SorterCapacitiveSensorPusher1 ) AND ( b_Pusher$Priority_Var_Metal  > INT#0)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Check_For_Metal;
            ELSEIF ((NOT  b_Pusher$SorterLightnesssensorCraneInterfaceInverse  AND  b_Pusher$SorterLightbarrierCraneInterface ) AND ( b_Pusher$Priority_Var_Black  > INT#0)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Check_For_Black;
            ELSEIF (( b_Pusher$SorterLightnessSensorPusher1  AND NOT  b_Pusher$SorterCapacitiveSensorPusher1 ) AND ( b_Pusher$Priority_Var_White  > INT#0)) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Check_For_White;
            END_IF

        Pusher_states_t#PusherY1_Move_In_Black:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = TRUE) AND ( b_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY1  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_Black;
            END_IF

        Pusher_states_t#PusherY1_Move_In_Metal:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = TRUE) AND ( b_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY1  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_Metal;
            END_IF

        Pusher_states_t#PusherY1_Move_In_White:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = TRUE) AND ( b_Pusher$SorterPusher1MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY1  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide1_White;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_Black:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = FALSE) AND ( b_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY1  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y1_Black;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_Metal:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = FALSE) AND ( b_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY1  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y1_Metal;
            END_IF

        Pusher_states_t#PusherY1_Move_Out_White:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher1MovedOut  = FALSE) AND ( b_Pusher$SorterPusher1MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY1  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher1MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y1_White;
            END_IF

        Pusher_states_t#PusherY2_Move_In_Black:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = TRUE) AND ( b_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY2  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_Black;
            END_IF

        Pusher_states_t#PusherY2_Move_In_Metal:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = TRUE) AND ( b_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY2  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_Metal;
            END_IF

        Pusher_states_t#PusherY2_Move_In_White:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = TRUE) AND ( b_Pusher$SorterPusher2MovedIn  = FALSE)) THEN
                 b_Pusher$PusherY2  := FALSE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedIn  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide2_White;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_Black:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = FALSE) AND ( b_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY2  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y2_Black;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_Metal:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = FALSE) AND ( b_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY2  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y2_Metal;
            END_IF

        Pusher_states_t#PusherY2_Move_Out_White:
             b_Pusher$_transit  := FALSE;
            IF (( b_Pusher$SorterPusher2MovedOut  = FALSE) AND ( b_Pusher$SorterPusher2MovedIn  = TRUE)) THEN
                 b_Pusher$PusherY2  := TRUE;
            END_IF
            IF  b_Pusher$SorterPusher2MovedOut  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Y2_White;
            END_IF

        Pusher_states_t#Reset_interconnect3:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect2  := FALSE;
             b_Pusher$Timer2$IN  := FALSE;
             b_Pusher$Timer2$PT  := USINT#0;
            IF  b_Pusher$Timer2$IN  THEN
                 b_Pusher$Timer2$Q  := ( b_Pusher$Timer2$ET  = USINT#0);
                IF ( b_Pusher$Timer2$ET  > USINT#0) THEN
                     b_Pusher$Timer2$ET  := ( b_Pusher$Timer2$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer2$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer2$Q  := FALSE;
                 b_Pusher$Timer2$ET  :=  b_Pusher$Timer2$PT ;
            END_IF
             b_Pusher$Slide3_black  := ( b_Pusher$Slide3_black  - INT#1);
             b_Pusher$Priority_Var_Black  := ( b_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_Black:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide1_Black  := FALSE;
             b_Pusher$Timer_Slide1_Black$IN  := FALSE;
             b_Pusher$Timer_Slide1_Black$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide1_Black$IN  THEN
                 b_Pusher$Timer_Slide1_Black$Q  := ( b_Pusher$Timer_Slide1_Black$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide1_Black$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide1_Black$ET  := ( b_Pusher$Timer_Slide1_Black$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide1_Black$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide1_Black$Q  := FALSE;
                 b_Pusher$Timer_Slide1_Black$ET  :=  b_Pusher$Timer_Slide1_Black$PT ;
            END_IF
             b_Pusher$Slide1_black  := ( b_Pusher$Slide1_black  - INT#1);
             b_Pusher$Priority_Var_Black  := ( b_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide1_Metal  := FALSE;
             b_Pusher$Timer_Slide1_Metal$IN  := FALSE;
             b_Pusher$Timer_Slide1_Metal$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide1_Metal$IN  THEN
                 b_Pusher$Timer_Slide1_Metal$Q  := ( b_Pusher$Timer_Slide1_Metal$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide1_Metal$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide1_Metal$ET  := ( b_Pusher$Timer_Slide1_Metal$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide1_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide1_Metal$Q  := FALSE;
                 b_Pusher$Timer_Slide1_Metal$ET  :=  b_Pusher$Timer_Slide1_Metal$PT ;
            END_IF
             b_Pusher$Slide1_metal  := ( b_Pusher$Slide1_metal  - INT#1);
             b_Pusher$Priority_Var_Metal  := ( b_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide1_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide1_White  := FALSE;
             b_Pusher$Timer_Slide1_White$IN  := FALSE;
             b_Pusher$Timer_Slide1_White$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide1_White$IN  THEN
                 b_Pusher$Timer_Slide1_White$Q  := ( b_Pusher$Timer_Slide1_White$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide1_White$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide1_White$ET  := ( b_Pusher$Timer_Slide1_White$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide1_White$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide1_White$Q  := FALSE;
                 b_Pusher$Timer_Slide1_White$ET  :=  b_Pusher$Timer_Slide1_White$PT ;
            END_IF
             b_Pusher$Slide1_white  := ( b_Pusher$Slide1_white  - INT#1);
             b_Pusher$Priority_Var_White  := ( b_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_Black:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide2_Black  := FALSE;
             b_Pusher$Timer_Slide2_Black$IN  := FALSE;
             b_Pusher$Timer_Slide2_Black$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide2_Black$IN  THEN
                 b_Pusher$Timer_Slide2_Black$Q  := ( b_Pusher$Timer_Slide2_Black$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide2_Black$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide2_Black$ET  := ( b_Pusher$Timer_Slide2_Black$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide2_Black$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide2_Black$Q  := FALSE;
                 b_Pusher$Timer_Slide2_Black$ET  :=  b_Pusher$Timer_Slide2_Black$PT ;
            END_IF
             b_Pusher$Slide2_black  := ( b_Pusher$Slide2_black  - INT#1);
             b_Pusher$Priority_Var_Black  := ( b_Pusher$Priority_Var_Black  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide2_Metal  := FALSE;
             b_Pusher$Timer_Slide2_Metal$IN  := FALSE;
             b_Pusher$Timer_Slide2_Metal$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide2_Metal$IN  THEN
                 b_Pusher$Timer_Slide2_Metal$Q  := ( b_Pusher$Timer_Slide2_Metal$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide2_Metal$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide2_Metal$ET  := ( b_Pusher$Timer_Slide2_Metal$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide2_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide2_Metal$Q  := FALSE;
                 b_Pusher$Timer_Slide2_Metal$ET  :=  b_Pusher$Timer_Slide2_Metal$PT ;
            END_IF
             b_Pusher$Slide2_metal  := ( b_Pusher$Slide2_metal  - INT#1);
             b_Pusher$Priority_Var_Metal  := ( b_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide2_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect_Slide2_White  := FALSE;
             b_Pusher$Timer_Slide2_White$IN  := FALSE;
             b_Pusher$Timer_Slide2_White$PT  := USINT#0;
            IF  b_Pusher$Timer_Slide2_White$IN  THEN
                 b_Pusher$Timer_Slide2_White$Q  := ( b_Pusher$Timer_Slide2_White$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide2_White$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide2_White$ET  := ( b_Pusher$Timer_Slide2_White$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide2_White$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide2_White$Q  := FALSE;
                 b_Pusher$Timer_Slide2_White$ET  :=  b_Pusher$Timer_Slide2_White$PT ;
            END_IF
             b_Pusher$Slide2_white  := ( b_Pusher$Slide2_white  - INT#1);
             b_Pusher$Priority_Var_White  := ( b_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide3_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$Slide3_metal  := ( b_Pusher$Slide3_metal  - INT#1);
             b_Pusher$Priority_Var_Metal  := ( b_Pusher$Priority_Var_Metal  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Reset_interconnect_Slide3_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$interconnect3  := FALSE;
             b_Pusher$Timer3$IN  := FALSE;
             b_Pusher$Timer3$PT  := USINT#0;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$Slide3_white  := ( b_Pusher$Slide3_white  - INT#1);
             b_Pusher$Priority_Var_White  := ( b_Pusher$Priority_Var_White  - INT#1);
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Interstep_2;
            END_IF

        Pusher_states_t#Second_Slide_Timer_Black:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnesssensorCraneInterfaceInverse  = TRUE) THEN
                 b_Pusher$Timer_Slide2_Black$IN  :=  b_Pusher$SorterLightnesssensorCraneInterfaceInverse ;
                 b_Pusher$Timer_Slide2_Black$PT  :=  b_Pusher$Duration_Slide2_Black ;
                IF  b_Pusher$Timer_Slide2_Black$IN  THEN
                     b_Pusher$Timer_Slide2_Black$Q  := ( b_Pusher$Timer_Slide2_Black$ET  = USINT#0);
                    IF ( b_Pusher$Timer_Slide2_Black$ET  > USINT#0) THEN
                         b_Pusher$Timer_Slide2_Black$ET  := ( b_Pusher$Timer_Slide2_Black$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer_Slide2_Black$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer_Slide2_Black$Q  := FALSE;
                     b_Pusher$Timer_Slide2_Black$ET  :=  b_Pusher$Timer_Slide2_Black$PT ;
                END_IF
                 b_Pusher$interconnect_Slide2_Black  :=  b_Pusher$Timer_Slide2_Black$Q ;
            END_IF
            IF  b_Pusher$interconnect_Slide2_Black  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_Black;
            END_IF

        Pusher_states_t#Second_Slide_Timer_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer_Slide2_Metal$IN  := TRUE;
             b_Pusher$Timer_Slide2_Metal$PT  :=  b_Pusher$Duration_Slide2_Metal ;
            IF  b_Pusher$Timer_Slide2_Metal$IN  THEN
                 b_Pusher$Timer_Slide2_Metal$Q  := ( b_Pusher$Timer_Slide2_Metal$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide2_Metal$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide2_Metal$ET  := ( b_Pusher$Timer_Slide2_Metal$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide2_Metal$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide2_Metal$Q  := FALSE;
                 b_Pusher$Timer_Slide2_Metal$ET  :=  b_Pusher$Timer_Slide2_Metal$PT ;
            END_IF
             b_Pusher$interconnect_Slide2_Metal  :=  b_Pusher$Timer_Slide2_Metal$Q ;
            IF  b_Pusher$interconnect_Slide2_Metal  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_Metal;
            END_IF

        Pusher_states_t#Second_Slide_Timer_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer_Slide2_White$IN  := TRUE;
             b_Pusher$Timer_Slide2_White$PT  :=  b_Pusher$Duration_Slide2_White ;
            IF  b_Pusher$Timer_Slide2_White$IN  THEN
                 b_Pusher$Timer_Slide2_White$Q  := ( b_Pusher$Timer_Slide2_White$ET  = USINT#0);
                IF ( b_Pusher$Timer_Slide2_White$ET  > USINT#0) THEN
                     b_Pusher$Timer_Slide2_White$ET  := ( b_Pusher$Timer_Slide2_White$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer_Slide2_White$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer_Slide2_White$Q  := FALSE;
                 b_Pusher$Timer_Slide2_White$ET  :=  b_Pusher$Timer_Slide2_White$PT ;
            END_IF
             b_Pusher$interconnect_Slide2_White  :=  b_Pusher$Timer_Slide2_White$Q ;
            IF  b_Pusher$interconnect_Slide2_White  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_Out_White;
            END_IF

        Pusher_states_t#Second_Slide_black_workpieces:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_Black;
            END_IF

        Pusher_states_t#Second_Slide_metal_workpieces:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnessSensorPusher2  AND  b_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Test_For_Metal;
            END_IF

        Pusher_states_t#Second_Slide_white_workpieces:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnessSensorPusher2  AND NOT  b_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Test_For_White;
            END_IF

        Pusher_states_t#Second_Test_For_Metal:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_Metal;
            END_IF

        Pusher_states_t#Second_Test_For_White:
             b_Pusher$_transit  := FALSE;
            IF TRUE THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Second_Slide_Timer_White;
            END_IF

        Pusher_states_t#Third_Slide_black_workpieces:
             b_Pusher$_transit  := FALSE;
            IF (NOT  b_Pusher$SorterLightnessSensorPusher2  AND NOT  b_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Black;
            END_IF

        Pusher_states_t#Third_Slide_metal_workpieces:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnessSensorPusher2  AND  b_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_Metal;
            END_IF

        Pusher_states_t#Third_Slide_white_workpieces:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$SorterLightnessSensorPusher2  AND NOT  b_Pusher$SorterCapacitiveSensorPusher2 ) THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Wait_White;
            END_IF

        Pusher_states_t#Wait_Black:
             b_Pusher$_transit  := FALSE;
            IF ((NOT  b_Pusher$SorterLightnessSensorPusher2  AND NOT  b_Pusher$SorterCapacitiveSensorPusher2 ) = TRUE) THEN
                 b_Pusher$Timer2$IN  := (NOT  b_Pusher$SorterLightnessSensorPusher2  AND NOT  b_Pusher$SorterCapacitiveSensorPusher2 );
                 b_Pusher$Timer2$PT  :=  b_Pusher$Duration2 ;
                IF  b_Pusher$Timer2$IN  THEN
                     b_Pusher$Timer2$Q  := ( b_Pusher$Timer2$ET  = USINT#0);
                    IF ( b_Pusher$Timer2$ET  > USINT#0) THEN
                         b_Pusher$Timer2$ET  := ( b_Pusher$Timer2$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer2$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer2$Q  := FALSE;
                     b_Pusher$Timer2$ET  :=  b_Pusher$Timer2$PT ;
                END_IF
                 b_Pusher$interconnect2  :=  b_Pusher$Timer2$Q ;
            END_IF
            IF  b_Pusher$interconnect2  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect3;
            END_IF

        Pusher_states_t#Wait_Metal:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer3$IN  := TRUE;
             b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide3_Metal;
            END_IF

        Pusher_states_t#Wait_White:
             b_Pusher$_transit  := FALSE;
             b_Pusher$Timer3$IN  := TRUE;
             b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
            IF  b_Pusher$Timer3$IN  THEN
                 b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                     b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                ELSE
                     b_Pusher$Timer3$ET  := USINT#0;
                END_IF
            ELSE
                 b_Pusher$Timer3$Q  := FALSE;
                 b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
            END_IF
             b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#Reset_interconnect_Slide3_White;
            END_IF

        Pusher_states_t#Wait_Y1_Black:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY1  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY1 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_Black;
            END_IF

        Pusher_states_t#Wait_Y1_Metal:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY1  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY1 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_Metal;
            END_IF

        Pusher_states_t#Wait_Y1_White:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY1  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY1 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY1_Move_In_White;
            END_IF

        Pusher_states_t#Wait_Y2_Black:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY2  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY2 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_Black;
            END_IF

        Pusher_states_t#Wait_Y2_Metal:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY2  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY2 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_Metal;
            END_IF

        Pusher_states_t#Wait_Y2_White:
             b_Pusher$_transit  := FALSE;
            IF ( b_Pusher$PusherY2  = TRUE) THEN
                 b_Pusher$Timer3$IN  :=  b_Pusher$PusherY2 ;
                 b_Pusher$Timer3$PT  :=  b_Pusher$Duration3 ;
                IF  b_Pusher$Timer3$IN  THEN
                     b_Pusher$Timer3$Q  := ( b_Pusher$Timer3$ET  = USINT#0);
                    IF ( b_Pusher$Timer3$ET  > USINT#0) THEN
                         b_Pusher$Timer3$ET  := ( b_Pusher$Timer3$ET  - USINT#1);
                    ELSE
                         b_Pusher$Timer3$ET  := USINT#0;
                    END_IF
                ELSE
                     b_Pusher$Timer3$Q  := FALSE;
                     b_Pusher$Timer3$ET  :=  b_Pusher$Timer3$PT ;
                END_IF
                 b_Pusher$interconnect3  :=  b_Pusher$Timer3$Q ;
            END_IF
            IF  b_Pusher$interconnect3  THEN
                 b_Pusher$_transit  := TRUE;
                 b_Pusher$_state  := Pusher_states_t#PusherY2_Move_In_White;
            END_IF

            END_CASE
    IF (( b_Actuator_SorterGreenLampConveyor  AND  b_Actuator_MagazinGreenLamp ) AND  b_Actuator_StampGreenLamp ) THEN
        IF ((( b_Stamp$StartCommandStamp  AND  b_Crane$StartCommandCrane ) AND  b_Conveyor$StartCommandConveyor ) AND  b_Mag$StartCommandMagazin ) THEN
             b_Crane$StartVar  := TRUE;
             b_Conveyor$StartVar  := TRUE;
             b_Mag$StartVar  := TRUE;
             b_Pusher$StartVar  := TRUE;
             b_Stamp$StartVar  := TRUE;
             b_DIAGNOSIS_ACTIVE  := TRUE;
        END_IF
    END_IF
     b_Crane$SFCReset  := FALSE;
     b_Conveyor$SFCReset  := FALSE;
     b_Mag$SFCReset  := FALSE;
     b_Pusher$SFCReset  := FALSE;
     b_Stamp$SFCReset  := FALSE;

     b_Crane$AnalogCranePressure  :=  b_PARAMETER_CRANE_PRESSURE_METALLIC ;


ELSEIF ((NOT  b_Sensor_SorterEmergencyStop  OR NOT  b_Sensor_StampEmergencyStop ) OR NOT  b_Sensor_MagazinEmergencyStop ) THEN
     b_Actuator_MagazinSlider  := FALSE;
     b_Actuator_CraneLower  := FALSE;
     b_Actuator_MagazinVacuumOn  := FALSE;
     b_Actuator_MagazinVacuumOff  := TRUE;
     b_Actuator_MagazinGreenLamp  := FALSE;
     b_Actuator_CraneTurnCounterclockwise  := FALSE;
     b_Actuator_CraneTurnClockwise  := FALSE;
     b_Actuator_SorterConveyorTowardsStacker  := FALSE;
     b_Actuator_SorterConveyorTowardsCrane  := FALSE;
     b_Actuator_SorterGreenLampConveyor  := FALSE;
     b_Actuator_PusherY1  := FALSE;
     b_Actuator_PusherY2  := FALSE;
     b_Actuator_StampSliderMovedOut  := TRUE;
     b_Actuator_StampSliderMovedIn  := FALSE;
     b_Actuator_StampGreenLamp  := FALSE;
     b_Actuator_StampPusher  := FALSE;
     b_Actuator_AnalogCranePressure  := INT#0;
     b_Crane$SFCReset  := TRUE;
     b_Conveyor$SFCReset  := TRUE;
     b_Mag$SFCReset  := TRUE;
     b_Pusher$SFCReset  := TRUE;
     b_Stamp$SFCReset  := TRUE;
     b_Crane$StartVar  := FALSE;
     b_Conveyor$StartVar  := FALSE;
     b_Mag$StartVar  := FALSE;
     b_Pusher$StartVar  := FALSE;
     b_Stamp$StartVar  := FALSE;
END_IF

 
 END_PROGRAM