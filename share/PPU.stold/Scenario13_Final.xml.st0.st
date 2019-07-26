TYPE
    Crane_states_t : (Crane_Go_Up , Crane_Go_Up_White , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_At_Stamp2 , Crane_Lift_Conveyor , Crane_Lift_Conveyor2 , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_Magazin_White , Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Metallic2 , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic , Crane_On_Stamp_Metallic2 , Crane_On_Stamp_Metallic2_Lower , Crane_On_Stamp_Stop_Black , Crane_On_Stamp_White , Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_Metallic2 , Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Crane_Turn_Left_White , Crane_Turn_Right_From_Stamp , Init , Interstep , Interstep_2 , Interstep_3 , Interstep_4 , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , Magazin_Stop_Final , No_Workpiece_ready , Reset_interconnect , Stamp_Pressure_Profile_Set_Metallic , Stamp_Pressure_Profile_Set_White , Start_Crane , Step0 , Step2 , Step3 , Step4 , Suck_At_Stamp , Suck_At_Stamp2 , TimeDelay , Turn_Right , Turn_Right_Black , Turn_Right_Final , pause , release , release2 , release_Black , release_Workpiece , release_Workpiece_White);
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Conveyor_states_t : (Conveyor_Init , Conveyor_Stop_Empty_Magazin , Conveyor_Towards_Stacker , Conveyor_init_2 , Conveyor_pause , Green_Lamp , Init , Interstep , Runtime_Conveyor , Start_Conveyor , Step0);
    Stamp_states_t : (Green_Lamp , Init , Interstep , Intertsep_2 , StampProcess , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 , Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);
    Pusher_states_t : (Check_For_Black , Check_For_Metal , Check_For_White , First_Slide_Timer_Black , First_Slide_Timer_Metal , First_Slide_Timer_White , First_Slide_black_workpieces , First_Slide_metal_workpieces , First_Slide_white_workpieces , Init , Interstep , Interstep_2 , PusherY1_Move_In_Black , PusherY1_Move_In_Metal , PusherY1_Move_In_White , PusherY1_Move_Out_Black , PusherY1_Move_Out_Metal , PusherY1_Move_Out_White , PusherY2_Move_In_Black , PusherY2_Move_In_Metal , PusherY2_Move_In_White , PusherY2_Move_Out_Black , PusherY2_Move_Out_Metal , PusherY2_Move_Out_White , Reset_interconnect3 , Reset_interconnect_Slide1_Black , Reset_interconnect_Slide1_Metal , Reset_interconnect_Slide1_White , Reset_interconnect_Slide2_Black , Reset_interconnect_Slide2_Metal , Reset_interconnect_Slide2_White , Reset_interconnect_Slide3_Metal , Reset_interconnect_Slide3_White , Second_Slide_Timer_Black , Second_Slide_Timer_Metal , Second_Slide_Timer_White , Second_Slide_black_workpieces , Second_Slide_metal_workpieces , Second_Slide_white_workpieces , Second_Test_For_Metal , Second_Test_For_White , Third_Slide_black_workpieces , Third_Slide_metal_workpieces , Third_Slide_white_workpieces , Wait_Black , Wait_Metal , Wait_White , Wait_Y1_Black , Wait_Y1_Metal , Wait_Y1_White , Wait_Y2_Black , Wait_Y2_Metal , Wait_Y2_White);
END_TYPE

PROGRAM Main

VAR  Actuator_AnalogCranePressure : INT; END_VAR {*LrWXP*}
VAR  Actuator_CraneLower : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_CraneTurnClockwise : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_CraneTurnCounterclockwise : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinGreenLamp : BOOL; END_VAR {*LRWXP*}
VAR  Actuator_MagazinSlider : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinVacuumOff : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinVacuumOn : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinWhiteLamp : BOOL; END_VAR {*LrwxP*}
VAR  Actuator_PusherY1 : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_PusherY2 : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_SorterConveyorTowardsCrane : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_SorterConveyorTowardsStacker : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_SorterGreenLampConveyor : BOOL; END_VAR {*LRWXP*}
VAR  Actuator_SorterWhiteLampConveyor : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_StampGreenLamp : BOOL; END_VAR {*LRWXP*}
VAR  Actuator_StampPusher : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_StampSliderMovedIn : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_StampSliderMovedOut : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_StampWhiteLamp : BOOL; END_VAR {*LrWXP*}
VAR  Conveyor$Duration_Conveyor_Runtime : UINT := #1125; END_VAR {*LRwxp*}
VAR  Conveyor$Duration_Conveyor_Test : UINT := #250; END_VAR {*LRwxp*}
VAR  Conveyor$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Conveyor$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR_OUTPUT  Conveyor$SorterConveyorTowardsCrane : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Conveyor$SorterConveyorTowardsStacker : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Conveyor$SorterGreenLampConveyor : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Conveyor$SorterLightbarrierCraneInterface : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Conveyor$SorterStartButton : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Conveyor$SorterSwitchManuellAutomatic : BOOL; END_VAR {*IrWXp*}
VAR_OUTPUT  Conveyor$SorterWhiteLampConveyor : BOOL; END_VAR {*ORwxp*}
VAR_OUTPUT  Conveyor$StartCommandConveyor : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Conveyor$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_OUTPUT  Conveyor$Timer_Conveyor_Runtime$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Conveyor$Timer_Conveyor_Runtime$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Conveyor$Timer_Conveyor_Runtime$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Conveyor$Timer_Conveyor_Runtime$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Conveyor$Timer_Conveyor_Test$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Conveyor$Timer_Conveyor_Test$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Conveyor$Timer_Conveyor_Test$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Conveyor$Timer_Conveyor_Test$Q : BOOL; END_VAR {*ORWxp*}
VAR  Conveyor$_state : Conveyor_states_t; END_VAR {*LRWxp*}
VAR  Conveyor$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Conveyor$interconnectConveyorStartCommand : BOOL; END_VAR {*LRWxp*}
VAR  Conveyor$interconnectConveyorTerminationCommand : BOOL; END_VAR {*LrWxp*}
VAR  Conveyor$interconnect_Conveyor_Runtime : BOOL; END_VAR {*LRWxp*}
VAR  Conveyor$interconnect_Conveyor_Test : BOOL; END_VAR {*LRWxp*}
VAR_INPUT  Crane$AnalogCranePosition : INT; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$AnalogCranePressure : INT; END_VAR {*ORWxp*}
VAR_INPUT  Crane$CraneDown : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$CraneLower : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$CraneSucked : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$CraneTurnClockwise : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Crane$CraneTurnCounterclockwise : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$CraneUp : BOOL; END_VAR {*IRWXp*}
VAR  Crane$Duration1 : UINT := #375; END_VAR {*LRwxp*}
VAR_INPUT  Crane$MagazinCapacitiveSensor : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$MagazinOpticalSensor : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$MagazinSlider : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  Crane$MagazinVacuumOff : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Crane$MagazinVacuumOn : BOOL; END_VAR {*ORWxp*}
VAR  Crane$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Crane$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Crane$SliderMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  Crane$StampLowered : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$StampSliderFilled : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$StampSliderSensorMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$StartButtonMagazin : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$StartCommandCrane : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_OUTPUT  Crane$TimeDelay_Timer$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Crane$TimeDelay_Timer$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Crane$TimeDelay_Timer$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Crane$TimeDelay_Timer$Q : BOOL; END_VAR {*ORWxp*}
VAR  Crane$TimeDelay_Timer_Duration : UINT := #12; END_VAR {*LRwxp*}
VAR  Crane$TimeDelay_Timer_interconnect : BOOL; END_VAR {*LRWxp*}
VAR_OUTPUT  Crane$Timer1$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Crane$Timer1$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Crane$Timer1$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Crane$Timer1$Q : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$WorkpieceReady : BOOL; END_VAR {*IRWXp*}
VAR  Crane$_state : Crane_states_t; END_VAR {*LRWxp*}
VAR  Crane$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Crane$actualtime1 : INT; END_VAR {*Lrwxp*}
VAR  Crane$interconnect : BOOL; END_VAR {*LRWxp*}
VAR  Crane$interconnectCraneStartCommand : BOOL; END_VAR {*LRWxp*}
VAR_INPUT  Mag$AnalogCranePosition : INT; END_VAR {*IRWXp*}
VAR_INPUT  Mag$CraneDown : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Mag$CraneLower : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  Mag$CraneOnConveyor : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Mag$CraneOnMagazin : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Mag$CraneSucked : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  Mag$CraneTurnClockwise : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  Mag$CraneTurnCounterclockwise : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  Mag$CraneUp : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Mag$MagazinGreenLamp : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Mag$MagazinSlider : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Mag$MagazinVacuumOff : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  Mag$MagazinVacuumOn : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  Mag$MagazinWhiteLamp : BOOL; END_VAR {*Orwxp*}
VAR  Mag$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Mag$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Mag$SliderMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Mag$SliderNotMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Mag$StartButtonMagazin : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Mag$StartCommandMagazin : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Mag$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Mag$WorkpieceReady : BOOL; END_VAR {*IrWXp*}
VAR  Mag$_state : Magazin_states_t; END_VAR {*LRWxp*}
VAR  Mag$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Mag$interconnectMagazinStartCommand : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$Duration2 : UINT := #500; END_VAR {*LRwxp*}
VAR  Pusher$Duration3 : UINT := #50; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide1_Black : UINT := #237; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide1_Metal : UINT := #75; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide1_White : UINT := #75; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide2_Black : UINT := #500; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide2_Metal : UINT := #92; END_VAR {*LRwxp*}
VAR  Pusher$Duration_Slide2_White : UINT := #92; END_VAR {*LRwxp*}
VAR  Pusher$Priority_Var_Black : INT := INT#3; END_VAR {*LRWxp*}
VAR  Pusher$Priority_Var_Metal : INT := INT#3; END_VAR {*LRWxp*}
VAR  Pusher$Priority_Var_White : INT := INT#3; END_VAR {*LRWxp*}
VAR_OUTPUT  Pusher$PusherY1 : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$PusherY2 : BOOL; END_VAR {*ORWxp*}
VAR  Pusher$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Pusher$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR  Pusher$Slide1_black : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide1_metal : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide1_white : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide2_black : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide2_metal : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide2_white : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide3_black : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide3_metal : INT := INT#1; END_VAR {*LRWxp*}
VAR  Pusher$Slide3_white : INT := INT#1; END_VAR {*LRWxp*}
VAR_INPUT  Pusher$SorterCapacitiveSensorPusher1 : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterCapacitiveSensorPusher2 : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterLightbarrierCraneInterface : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterLightnessSensorPusher1 : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterLightnessSensorPusher2 : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterLightnessSensorPusher3 : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Pusher$SorterLightnesssensorCraneInterfaceInverse : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterPusher1MovedIn : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterPusher1MovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterPusher2MovedIn : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterPusher2MovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Pusher$SorterStartButton : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Pusher$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer2$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer2$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer2$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer2$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer3$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer3$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer3$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer3$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_Black$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide1_Black$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide1_Black$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_Black$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_Metal$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide1_Metal$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide1_Metal$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_Metal$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_White$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide1_White$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide1_White$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide1_White$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_Black$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide2_Black$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide2_Black$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_Black$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_Metal$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide2_Metal$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide2_Metal$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_Metal$Q : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_White$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Pusher$Timer_Slide2_White$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Pusher$Timer_Slide2_White$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Pusher$Timer_Slide2_White$Q : BOOL; END_VAR {*ORWxp*}
VAR  Pusher$_state : Pusher_states_t; END_VAR {*LRWxp*}
VAR  Pusher$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Pusher$interconnect2 : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect3 : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide1_Black : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide1_Metal : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide1_White : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide2_Black : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide2_Metal : BOOL; END_VAR {*LRWxp*}
VAR  Pusher$interconnect_Slide2_White : BOOL; END_VAR {*LRWxp*}
VAR  Sensor_AnalogCranePosition : INT; END_VAR {*LRwxP*}
VAR  Sensor_CraneDown : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneOnConveyor : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneOnMagazin : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CranePosition : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_CranePositionStamp : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneSucked : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneUp : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinCapacitiveSensor : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinEmergencyStop : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinOpticalSensor : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinSwitchManuellAutomatic : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_SliderMovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SliderNotMovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterCapacitiveSensorPusher1 : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterCapacitiveSensorPusher2 : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterEmergencyStop : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterLightbarrierCraneInterface : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterLightnessSensorPusher1 : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterLightnessSensorPusher2 : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterLightnessSensorPusher3 : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterLightnesssensorCraneInterfaceInverse : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterPusher1MovedIn : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterPusher1MovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterPusher2MovedIn : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterPusher2MovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterStartButton : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SorterSwitchManuellAutomatic : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampEmergencyStop : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampLowered : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampSliderFilled : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampSliderSensorMovedIn : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampSliderSensorMovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampStartButton : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StampSwitchManuellAutomatic : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_StampUp : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StartButtonMagazin : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_WorkpieceReady : BOOL; END_VAR {*LRwxP*}
VAR_INPUT  Stamp$AnalogCranePosition : INT; END_VAR {*IRWXp*}
VAR_INPUT  Stamp$CraneDown : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Stamp$CraneOnConveyor : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Stamp$CranePositionStamp : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Stamp$CraneSucked : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Stamp$CraneUp : BOOL; END_VAR {*IRWXp*}
VAR  Stamp$Duration : UINT := #125; END_VAR {*Lrwxp*}
VAR  Stamp$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Stamp$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR_OUTPUT  Stamp$StampGreenLamp : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Stamp$StampLowered : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Stamp$StampPressure : BOOL; END_VAR {*OrWxp*}
VAR_OUTPUT  Stamp$StampPusher : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Stamp$StampSliderFilled : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Stamp$StampSliderMovedIn : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Stamp$StampSliderMovedOut : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Stamp$StampSliderSensorMovedIn : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Stamp$StampSliderSensorMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Stamp$StampStartButton : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Stamp$StampUp : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Stamp$StampWhiteLamp : BOOL; END_VAR {*ORwxp*}
VAR_OUTPUT  Stamp$StartCommandStamp : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Stamp$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_OUTPUT  Stamp$Timer$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Stamp$Timer$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Stamp$Timer$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Stamp$Timer$Q : BOOL; END_VAR {*ORWxp*}
VAR  Stamp$_state : Stamp_states_t; END_VAR {*LRWxp*}
VAR  Stamp$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Stamp$interconnect : BOOL; END_VAR {*LRWxp*}
VAR  Stamp$interconnectStampStartCommand : BOOL; END_VAR {*LRWxp*}
Mag$SliderNotMovedOut := Sensor_SliderNotMovedOut;
Mag$SliderMovedOut := Sensor_SliderMovedOut;
Mag$CraneOnMagazin := Sensor_CraneOnMagazin;
Mag$CraneDown := Sensor_CraneDown;
Mag$CraneUp := Sensor_CraneUp;
Mag$CraneOnConveyor := Sensor_CraneOnConveyor;
Mag$WorkpieceReady := Sensor_WorkpieceReady;
Mag$AnalogCranePosition := Sensor_AnalogCranePosition;
Mag$StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_MagazinSlider := Mag$MagazinSlider;
Actuator_MagazinGreenLamp := Mag$MagazinGreenLamp;
Crane$CraneUp := Sensor_CraneUp;
Crane$CraneDown := Sensor_CraneDown;
Crane$CraneSucked := Sensor_CraneSucked;
Crane$MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane$SliderMovedOut := Sensor_SliderMovedOut;
Crane$WorkpieceReady := Sensor_WorkpieceReady;
Crane$MagazinOpticalSensor := Sensor_MagazinOpticalSensor;
Crane$StampSliderFilled := Sensor_StampSliderFilled;
Crane$StampSliderSensorMovedOut := Sensor_StampSliderSensorMovedOut;
Crane$StampLowered := Sensor_StampLowered;
Crane$AnalogCranePosition := Sensor_AnalogCranePosition;
Crane$StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_CraneTurnCounterclockwise := Crane$CraneTurnCounterclockwise;
Actuator_CraneTurnClockwise := Crane$CraneTurnClockwise;
Actuator_CraneLower := Crane$CraneLower;
Actuator_MagazinVacuumOff := Crane$MagazinVacuumOff;
Actuator_MagazinVacuumOn := Crane$MagazinVacuumOn;
Actuator_AnalogCranePressure := Crane$AnalogCranePressure;
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
Stamp$AnalogCranePosition := Sensor_AnalogCranePosition;
Stamp$StampStartButton := Sensor_StampStartButton;
Actuator_StampSliderMovedOut := Stamp$StampSliderMovedOut;
Actuator_StampSliderMovedIn := Stamp$StampSliderMovedIn;
Actuator_StampWhiteLamp := Stamp$StampWhiteLamp;
Actuator_StampPusher := Stamp$StampPusher;
Actuator_StampGreenLamp := Stamp$StampGreenLamp;
Conveyor$SorterStartButton := Sensor_SorterStartButton;
Conveyor$SorterSwitchManuellAutomatic := Sensor_SorterSwitchManuellAutomatic;
Conveyor$SorterLightbarrierCraneInterface := Sensor_SorterLightbarrierCraneInterface;
Actuator_SorterConveyorTowardsStacker := Conveyor$SorterConveyorTowardsStacker;
Actuator_SorterConveyorTowardsCrane := Conveyor$SorterConveyorTowardsCrane;
Actuator_SorterGreenLampConveyor := Conveyor$SorterGreenLampConveyor;
Actuator_SorterWhiteLampConveyor := Conveyor$SorterWhiteLampConveyor;
Pusher$SorterLightnesssensorCraneInterfaceInverse := Sensor_SorterLightnesssensorCraneInterfaceInverse;
Pusher$SorterLightbarrierCraneInterface := Sensor_SorterLightbarrierCraneInterface;
Pusher$SorterCapacitiveSensorPusher1 := Sensor_SorterCapacitiveSensorPusher1;
Pusher$SorterLightnessSensorPusher1 := Sensor_SorterLightnessSensorPusher1;
Pusher$SorterCapacitiveSensorPusher2 := Sensor_SorterCapacitiveSensorPusher2;
Pusher$SorterLightnessSensorPusher2 := Sensor_SorterLightnessSensorPusher2;
Pusher$SorterLightnessSensorPusher3 := Sensor_SorterLightnessSensorPusher3;
Pusher$SorterPusher1MovedOut := Sensor_SorterPusher1MovedOut;
Pusher$SorterPusher1MovedIn := Sensor_SorterPusher1MovedIn;
Pusher$SorterPusher2MovedOut := Sensor_SorterPusher2MovedOut;
Pusher$SorterPusher2MovedIn := Sensor_SorterPusher2MovedIn;
Pusher$SorterStartButton := Sensor_SorterStartButton;
Actuator_PusherY1 := Pusher$PusherY1;
Actuator_PusherY2 := Pusher$PusherY2;
IF ((Sensor_SorterEmergencyStop AND Sensor_StampEmergencyStop) AND Sensor_MagazinEmergencyStop) THEN
    CASE Mag$_state OF 
        Magazin_states_t#Green_Lamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Mag$MagazinGreenLamp := TRUE;
            Mag$interconnectMagazinStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Start_Magazin;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Mag$StartCommandMagazin := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Mag$StartVar THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#convey;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Magazin_Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Mag$MagazinSlider := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Magazin_Init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Mag$MagazinSlider := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Slider_Move_Back:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Mag$SliderMovedOut = TRUE) AND (Mag$SliderNotMovedOut = FALSE)) THEN
                Mag$MagazinSlider := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Mag$CraneUp THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step1;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Start_Magazin:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Mag$MagazinSlider := FALSE;
            Mag$MagazinGreenLamp := FALSE;
            Mag$StartVar := FALSE;
            Mag$StartCommandMagazin := FALSE;
            IF (Mag$StartButtonMagazin = TRUE) THEN
                Mag$interconnectMagazinStartCommand := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Mag$interconnectMagazinStartCommand THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Green_Lamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Mag$CraneDown THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Slider_Move_Back;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Step1:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Mag$AnalogCranePosition > INT#16160) AND (Mag$AnalogCranePosition < INT#16260)) THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#convey:
            {* begin(State) *}
            {* begin(onEntry) *}
            Mag$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF Mag$SliderNotMovedOut THEN
                Mag$MagazinSlider := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Mag$AnalogCranePosition > INT#24290) AND (Mag$AnalogCranePosition < INT#24390)) THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    CASE Crane$_state OF 
        Crane_states_t#Crane_Go_Up:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step3;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Go_Up_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step3;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := TRUE;
            Crane$interconnectCraneStartCommand := FALSE;
            Crane$AnalogCranePressure := INT#6000;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_At_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_At_Stamp2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            Crane$AnalogCranePressure := INT#0;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Right_From_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Conveyor2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Conveyor_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Magazin:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Magazin_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_Magazin_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Lower:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := TRUE;
            Crane$AnalogCranePressure := INT#0;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Conveyor_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Conveyor_Metallic2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Stamp_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release_Workpiece;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Stamp_Metallic2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$StampLowered THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_4;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Stamp_Metallic2_Lower:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Suck_At_Stamp2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Stamp_Stop_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Reset_interconnect;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_On_Stamp_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release_Workpiece_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#8160) AND (Crane$AnalogCranePosition < INT#8260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_From_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#16060) AND (Crane$AnalogCranePosition < INT#16160)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#8160) AND (Crane$AnalogCranePosition < INT#8260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_Metallic2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#8160) AND (Crane$AnalogCranePosition < INT#8260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_Metallic2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#16160) AND (Crane$AnalogCranePosition < INT#16260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#16160) AND (Crane$AnalogCranePosition < INT#16260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Left_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#8160) AND (Crane$AnalogCranePosition < INT#8260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Crane_Turn_Right_From_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#16160) AND (Crane$AnalogCranePosition < INT#16260)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor_Metallic2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$StartCommandCrane := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$StartVar THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Interstep_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$SliderMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#TimeDelay;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Interstep_3:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF NOT Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#No_Workpiece_ready;
            ELSEIF Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Turn_Right;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Interstep_4:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$StampSliderSensorMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Stamp_Metallic2_Lower;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Lower_Crane:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Suck_At_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Magazin_Stop:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lower;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Magazin_Stop_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_NOT_Metallic_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Magazin_Stop_Final:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#No_Workpiece_ready:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOn := FALSE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$StampSliderFilled THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_Metallic2;
            ELSEIF NOT Crane$StampSliderFilled THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Turn_Right_Final;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Reset_interconnect:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$interconnect := FALSE;
            Crane$Timer1$IN := FALSE;
            Crane$Timer1$PT := USINT#0;
            IF Crane$Timer1$IN THEN
                Crane$Timer1$Q := (Crane$Timer1$ET = USINT#0);
                IF (Crane$Timer1$ET > USINT#0) THEN
                    Crane$Timer1$ET := (Crane$Timer1$ET - USINT#1);
                ELSE
                    Crane$Timer1$ET := USINT#0;
                END_IF;
            ELSE
                Crane$Timer1$Q := FALSE;
                Crane$Timer1$ET := Crane$Timer1$PT;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$SliderMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Lower_Crane;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Stamp_Pressure_Profile_Set_Metallic:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$AnalogCranePressure := INT#7000;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Stamp_Pressure_Profile_Set_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$AnalogCranePressure := INT#6000;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazin_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Start_Crane:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$MagazinVacuumOn := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$AnalogCranePressure := INT#0;
            Crane$StartVar := FALSE;
            Crane$StartCommandCrane := FALSE;
            IF (Crane$StartButtonMagazin = TRUE) THEN
                Crane$interconnectCraneStartCommand := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$interconnectCraneStartCommand THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Crane$MagazinCapacitiveSensor AND Crane$MagazinOpticalSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Stamp_Pressure_Profile_Set_Metallic;
            ELSEIF (NOT Crane$MagazinCapacitiveSensor AND Crane$MagazinOpticalSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Stamp_Pressure_Profile_Set_White;
            ELSEIF (NOT Crane$MagazinCapacitiveSensor AND NOT Crane$MagazinOpticalSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazin;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Step2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Crane$MagazinCapacitiveSensor OR Crane$MagazinOpticalSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#pause;
            ELSEIF (NOT Crane$MagazinCapacitiveSensor AND NOT Crane$MagazinOpticalSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Turn_Right_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Step3:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF NOT Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step4;
            ELSEIF Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Step2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Step4:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Suck_At_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Suck_At_Stamp2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_At_Stamp2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#TimeDelay:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$TimeDelay_Timer$IN := TRUE;
            Crane$TimeDelay_Timer$PT := Crane$TimeDelay_Timer_Duration;
            IF Crane$TimeDelay_Timer$IN THEN
                Crane$TimeDelay_Timer$Q := (Crane$TimeDelay_Timer$ET = USINT#0);
                IF (Crane$TimeDelay_Timer$ET > USINT#0) THEN
                    Crane$TimeDelay_Timer$ET := (Crane$TimeDelay_Timer$ET - USINT#1);
                ELSE
                    Crane$TimeDelay_Timer$ET := USINT#0;
                END_IF;
            ELSE
                Crane$TimeDelay_Timer$Q := FALSE;
                Crane$TimeDelay_Timer$ET := Crane$TimeDelay_Timer$PT;
            END_IF;
            Crane$TimeDelay_Timer_interconnect := Crane$TimeDelay_Timer$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$TimeDelay_Timer_interconnect THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_3;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Turn_Right:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#24290) AND (Crane$AnalogCranePosition < INT#24390)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Magazin_Stop;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Turn_Right_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#24290) AND (Crane$AnalogCranePosition < INT#24390)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Magazin_Stop_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#Turn_Right_Final:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$AnalogCranePressure := INT#0;
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Crane$AnalogCranePosition > INT#24290) AND (Crane$AnalogCranePosition < INT#24390)) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Magazin_Stop_Final;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#pause:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$Timer1$IN := Crane$CraneUp;
            Crane$Timer1$PT := Crane$Duration1;
            IF Crane$Timer1$IN THEN
                Crane$Timer1$Q := (Crane$Timer1$ET = USINT#0);
                IF (Crane$Timer1$ET > USINT#0) THEN
                    Crane$Timer1$ET := (Crane$Timer1$ET - USINT#1);
                ELSE
                    Crane$Timer1$ET := USINT#0;
                END_IF;
            ELSE
                Crane$Timer1$Q := FALSE;
                Crane$Timer1$ET := Crane$Timer1$PT;
            END_IF;
            Crane$interconnect := Crane$Timer1$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$interconnect THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Reset_interconnect;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#release:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#release2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Conveyor2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#release_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOn := FALSE;
            Crane$MagazinVacuumOff := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#release_Workpiece:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Go_Up;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Crane_states_t#release_Workpiece_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Go_Up_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    CASE Stamp$_state OF 
        Stamp_states_t#Green_Lamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampGreenLamp := TRUE;
            Stamp$interconnectStampStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_1;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Start_Stamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StartCommandStamp := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StartVar THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Intertsep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Intertsep_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampSliderFilled THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#StampProcess:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampPusher := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampLowered THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step1;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#StampSliderBack:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampSliderMovedIn := TRUE;
            Stamp$StampSliderMovedOut := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampSliderSensorMovedIn THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampProcess;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#StampSliderForward:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampPusher := FALSE;
            Stamp$StampSliderMovedOut := TRUE;
            IF ((Stamp$StampLowered = FALSE) AND (Stamp$StampUp = TRUE)) THEN
                Stamp$interconnect := FALSE;
            END_IF;
            Stamp$Timer$IN := FALSE;
            Stamp$Timer$PT := USINT#0;
            IF Stamp$Timer$IN THEN
                Stamp$Timer$Q := (Stamp$Timer$ET = USINT#0);
                IF (Stamp$Timer$ET > USINT#0) THEN
                    Stamp$Timer$ET := (Stamp$Timer$ET - USINT#1);
                ELSE
                    Stamp$Timer$ET := USINT#0;
                END_IF;
            ELSE
                Stamp$Timer$Q := FALSE;
                Stamp$Timer$ET := Stamp$Timer$PT;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampSliderMovedOut THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Step2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Stamp_Init_1:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampSliderMovedIn := TRUE;
            Stamp$StampSliderMovedOut := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampSliderSensorMovedIn THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Stamp_Init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampSliderMovedOut := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampSliderSensorMovedOut THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_3;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Stamp_Init_3:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampPusher := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampLowered THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Stamp_Init_4;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Stamp_Init_4:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampPusher := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$StampUp THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Start_Stamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$StampSliderMovedOut := FALSE;
            Stamp$StampSliderMovedIn := FALSE;
            Stamp$StampPusher := FALSE;
            Stamp$StampGreenLamp := FALSE;
            Stamp$StampPressure := FALSE;
            Stamp$StartCommandStamp := FALSE;
            IF (Stamp$StampStartButton = TRUE) THEN
                Stamp$interconnectStampStartCommand := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$interconnectStampStartCommand THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Green_Lamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$CraneUp THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampSliderBack;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Step1:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Stamp$Timer$IN := Stamp$StampLowered;
            Stamp$Timer$PT := USINT#0;
            IF Stamp$Timer$IN THEN
                Stamp$Timer$Q := (Stamp$Timer$ET = USINT#0);
                IF (Stamp$Timer$ET > USINT#0) THEN
                    Stamp$Timer$ET := (Stamp$Timer$ET - USINT#1);
                ELSE
                    Stamp$Timer$ET := USINT#0;
                END_IF;
            ELSE
                Stamp$Timer$Q := FALSE;
                Stamp$Timer$ET := Stamp$Timer$PT;
            END_IF;
            Stamp$interconnect := Stamp$Timer$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Stamp$interconnect THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#StampSliderForward;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Stamp_states_t#Step2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Stamp$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (((Stamp$AnalogCranePosition > INT#16160) AND (Stamp$AnalogCranePosition < INT#16260)) AND NOT Stamp$StampSliderFilled) THEN
                Stamp$_transit := TRUE;
                Stamp$_state := Stamp_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    CASE Conveyor$_state OF 
        Conveyor_states_t#Conveyor_Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterConveyorTowardsStacker := TRUE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            Conveyor$Timer_Conveyor_Test$IN := TRUE;
            Conveyor$Timer_Conveyor_Test$PT := Conveyor$Duration_Conveyor_Test;
            IF Conveyor$Timer_Conveyor_Test$IN THEN
                Conveyor$Timer_Conveyor_Test$Q := (Conveyor$Timer_Conveyor_Test$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Test$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Test$ET := (Conveyor$Timer_Conveyor_Test$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Test$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Test$Q := FALSE;
                Conveyor$Timer_Conveyor_Test$ET := Conveyor$Timer_Conveyor_Test$PT;
            END_IF;
            Conveyor$interconnect_Conveyor_Test := Conveyor$Timer_Conveyor_Test$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Conveyor$interconnect_Conveyor_Test THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Conveyor_init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_Stop_Empty_Magazin:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterConveyorTowardsStacker := FALSE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            Conveyor$interconnectConveyorStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_Towards_Stacker:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterConveyorTowardsStacker := TRUE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Runtime_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterConveyorTowardsStacker := FALSE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            Conveyor$interconnect_Conveyor_Test := FALSE;
            Conveyor$Timer_Conveyor_Test$IN := FALSE;
            Conveyor$Timer_Conveyor_Test$PT := USINT#0;
            IF Conveyor$Timer_Conveyor_Test$IN THEN
                Conveyor$Timer_Conveyor_Test$Q := (Conveyor$Timer_Conveyor_Test$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Test$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Test$ET := (Conveyor$Timer_Conveyor_Test$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Test$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Test$Q := FALSE;
                Conveyor$Timer_Conveyor_Test$ET := Conveyor$Timer_Conveyor_Test$PT;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_pause:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterConveyorTowardsStacker := FALSE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            Conveyor$interconnect_Conveyor_Runtime := FALSE;
            Conveyor$Timer_Conveyor_Runtime$IN := FALSE;
            Conveyor$Timer_Conveyor_Runtime$PT := USINT#0;
            IF Conveyor$Timer_Conveyor_Runtime$IN THEN
                Conveyor$Timer_Conveyor_Runtime$Q := (Conveyor$Timer_Conveyor_Runtime$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Runtime$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Runtime$ET := (Conveyor$Timer_Conveyor_Runtime$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Runtime$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Runtime$Q := FALSE;
                Conveyor$Timer_Conveyor_Runtime$ET := Conveyor$Timer_Conveyor_Runtime$PT;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Green_Lamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$SorterGreenLampConveyor := TRUE;
            Conveyor$interconnectConveyorStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Conveyor_Init;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Start_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$StartCommandConveyor := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Conveyor$StartVar THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Runtime_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$Timer_Conveyor_Runtime$IN := TRUE;
            Conveyor$Timer_Conveyor_Runtime$PT := Conveyor$Duration_Conveyor_Runtime;
            IF Conveyor$Timer_Conveyor_Runtime$IN THEN
                Conveyor$Timer_Conveyor_Runtime$Q := (Conveyor$Timer_Conveyor_Runtime$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Runtime$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Runtime$ET := (Conveyor$Timer_Conveyor_Runtime$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Runtime$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Runtime$Q := FALSE;
                Conveyor$Timer_Conveyor_Runtime$ET := Conveyor$Timer_Conveyor_Runtime$PT;
            END_IF;
            Conveyor$interconnect_Conveyor_Runtime := Conveyor$Timer_Conveyor_Runtime$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Conveyor$interconnect_Conveyor_Runtime THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Conveyor_pause;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Start_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Conveyor$interconnectConveyorTerminationCommand := FALSE;
            Conveyor$SorterConveyorTowardsStacker := FALSE;
            Conveyor$SorterConveyorTowardsCrane := FALSE;
            Conveyor$SorterGreenLampConveyor := FALSE;
            Conveyor$interconnect_Conveyor_Runtime := FALSE;
            Conveyor$interconnect_Conveyor_Test := FALSE;
            Conveyor$Timer_Conveyor_Test$IN := FALSE;
            Conveyor$Timer_Conveyor_Test$PT := USINT#0;
            IF Conveyor$Timer_Conveyor_Test$IN THEN
                Conveyor$Timer_Conveyor_Test$Q := (Conveyor$Timer_Conveyor_Test$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Test$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Test$ET := (Conveyor$Timer_Conveyor_Test$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Test$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Test$Q := FALSE;
                Conveyor$Timer_Conveyor_Test$ET := Conveyor$Timer_Conveyor_Test$PT;
            END_IF;
            Conveyor$Timer_Conveyor_Runtime$IN := FALSE;
            Conveyor$Timer_Conveyor_Runtime$PT := USINT#0;
            IF Conveyor$Timer_Conveyor_Runtime$IN THEN
                Conveyor$Timer_Conveyor_Runtime$Q := (Conveyor$Timer_Conveyor_Runtime$ET = USINT#0);
                IF (Conveyor$Timer_Conveyor_Runtime$ET > USINT#0) THEN
                    Conveyor$Timer_Conveyor_Runtime$ET := (Conveyor$Timer_Conveyor_Runtime$ET - USINT#1);
                ELSE
                    Conveyor$Timer_Conveyor_Runtime$ET := USINT#0;
                END_IF;
            ELSE
                Conveyor$Timer_Conveyor_Runtime$Q := FALSE;
                Conveyor$Timer_Conveyor_Runtime$ET := Conveyor$Timer_Conveyor_Runtime$PT;
            END_IF;
            Conveyor$StartVar := FALSE;
            Conveyor$StartCommandConveyor := FALSE;
            IF (Conveyor$SorterStartButton = TRUE) THEN
                Conveyor$interconnectConveyorStartCommand := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Conveyor$interconnectConveyorStartCommand THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Green_Lamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            Conveyor$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Conveyor$SorterLightbarrierCraneInterface THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Conveyor_Towards_Stacker;
            ELSEIF NOT Conveyor$SorterLightbarrierCraneInterface THEN
                Conveyor$_transit := TRUE;
                Conveyor$_state := Conveyor_states_t#Conveyor_Stop_Empty_Magazin;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    CASE Pusher$_state OF 
        Pusher_states_t#Check_For_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Pusher$Slide2_black = INT#1) AND (Pusher$Priority_Var_Black = INT#2)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_black_workpieces;
            ELSEIF ((Pusher$Slide3_black = INT#1) AND (Pusher$Priority_Var_Black = INT#3)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Third_Slide_black_workpieces;
            ELSEIF ((Pusher$Slide1_black = INT#1) AND (Pusher$Priority_Var_Black = INT#1)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_black_workpieces;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Check_For_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Pusher$Slide3_metal = INT#1) AND (Pusher$Priority_Var_Metal = INT#3)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Third_Slide_metal_workpieces;
            ELSEIF ((Pusher$Slide2_metal = INT#1) AND (Pusher$Priority_Var_Metal = INT#2)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_metal_workpieces;
            ELSEIF ((Pusher$Slide1_metal = INT#1) AND (Pusher$Priority_Var_Metal = INT#1)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_metal_workpieces;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Check_For_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Pusher$Slide1_white = INT#1) AND (Pusher$Priority_Var_White = INT#1)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_white_workpieces;
            ELSEIF ((Pusher$Slide3_white = INT#1) AND (Pusher$Priority_Var_White = INT#3)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Third_Slide_white_workpieces;
            ELSEIF ((Pusher$Slide2_white = INT#1) AND (Pusher$Priority_Var_White = INT#2)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_white_workpieces;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_Timer_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
                Pusher$Timer_Slide1_Black$IN := Pusher$SorterLightnesssensorCraneInterfaceInverse;
                Pusher$Timer_Slide1_Black$PT := Pusher$Duration_Slide1_Black;
                IF Pusher$Timer_Slide1_Black$IN THEN
                    Pusher$Timer_Slide1_Black$Q := (Pusher$Timer_Slide1_Black$ET = USINT#0);
                    IF (Pusher$Timer_Slide1_Black$ET > USINT#0) THEN
                        Pusher$Timer_Slide1_Black$ET := (Pusher$Timer_Slide1_Black$ET - USINT#1);
                    ELSE
                        Pusher$Timer_Slide1_Black$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer_Slide1_Black$Q := FALSE;
                    Pusher$Timer_Slide1_Black$ET := Pusher$Timer_Slide1_Black$PT;
                END_IF;
                Pusher$interconnect_Slide1_Black := Pusher$Timer_Slide1_Black$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide1_Black THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_Out_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_Timer_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer_Slide1_Metal$IN := TRUE;
            Pusher$Timer_Slide1_Metal$PT := Pusher$Duration_Slide1_Metal;
            IF Pusher$Timer_Slide1_Metal$IN THEN
                Pusher$Timer_Slide1_Metal$Q := (Pusher$Timer_Slide1_Metal$ET = USINT#0);
                IF (Pusher$Timer_Slide1_Metal$ET > USINT#0) THEN
                    Pusher$Timer_Slide1_Metal$ET := (Pusher$Timer_Slide1_Metal$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide1_Metal$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide1_Metal$Q := FALSE;
                Pusher$Timer_Slide1_Metal$ET := Pusher$Timer_Slide1_Metal$PT;
            END_IF;
            Pusher$interconnect_Slide1_Metal := Pusher$Timer_Slide1_Metal$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide1_Metal THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_Out_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_Timer_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer_Slide1_White$IN := TRUE;
            Pusher$Timer_Slide1_White$PT := Pusher$Duration_Slide1_White;
            IF Pusher$Timer_Slide1_White$IN THEN
                Pusher$Timer_Slide1_White$Q := (Pusher$Timer_Slide1_White$ET = USINT#0);
                IF (Pusher$Timer_Slide1_White$ET > USINT#0) THEN
                    Pusher$Timer_Slide1_White$ET := (Pusher$Timer_Slide1_White$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide1_White$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide1_White$Q := FALSE;
                Pusher$Timer_Slide1_White$ET := Pusher$Timer_Slide1_White$PT;
            END_IF;
            Pusher$interconnect_Slide1_White := Pusher$Timer_Slide1_White$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide1_White THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_Out_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_black_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_Timer_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_metal_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_Timer_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#First_Slide_white_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#First_Slide_Timer_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$StartVar THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$PusherY1 := FALSE;
            Pusher$PusherY2 := FALSE;
            Pusher$interconnect2 := FALSE;
            Pusher$interconnect3 := FALSE;
            Pusher$StartVar := FALSE;
            Pusher$interconnect_Slide1_Black := FALSE;
            Pusher$interconnect_Slide2_Black := FALSE;
            Pusher$interconnect_Slide1_White := FALSE;
            Pusher$interconnect_Slide2_White := FALSE;
            Pusher$interconnect_Slide1_Metal := FALSE;
            Pusher$interconnect_Slide2_Metal := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Interstep_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF ((Pusher$SorterLightnessSensorPusher1 AND Pusher$SorterCapacitiveSensorPusher1) AND (Pusher$Priority_Var_Metal > INT#0)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Check_For_Metal;
            ELSEIF ((NOT Pusher$SorterLightnesssensorCraneInterfaceInverse AND Pusher$SorterLightbarrierCraneInterface) AND (Pusher$Priority_Var_Black > INT#0)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Check_For_Black;
            ELSEIF ((Pusher$SorterLightnessSensorPusher1 AND NOT Pusher$SorterCapacitiveSensorPusher1) AND (Pusher$Priority_Var_White > INT#0)) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Check_For_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_In_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = TRUE) AND (Pusher$SorterPusher1MovedIn = FALSE)) THEN
                Pusher$PusherY1 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide1_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_In_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = TRUE) AND (Pusher$SorterPusher1MovedIn = FALSE)) THEN
                Pusher$PusherY1 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide1_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_In_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = TRUE) AND (Pusher$SorterPusher1MovedIn = FALSE)) THEN
                Pusher$PusherY1 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide1_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_Out_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = FALSE) AND (Pusher$SorterPusher1MovedIn = TRUE)) THEN
                Pusher$PusherY1 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y1_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_Out_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = FALSE) AND (Pusher$SorterPusher1MovedIn = TRUE)) THEN
                Pusher$PusherY1 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y1_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY1_Move_Out_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher1MovedOut = FALSE) AND (Pusher$SorterPusher1MovedIn = TRUE)) THEN
                Pusher$PusherY1 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher1MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y1_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_In_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = TRUE) AND (Pusher$SorterPusher2MovedIn = FALSE)) THEN
                Pusher$PusherY2 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide2_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_In_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = TRUE) AND (Pusher$SorterPusher2MovedIn = FALSE)) THEN
                Pusher$PusherY2 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide2_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_In_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = TRUE) AND (Pusher$SorterPusher2MovedIn = FALSE)) THEN
                Pusher$PusherY2 := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedIn THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide2_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_Out_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = FALSE) AND (Pusher$SorterPusher2MovedIn = TRUE)) THEN
                Pusher$PusherY2 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y2_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_Out_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = FALSE) AND (Pusher$SorterPusher2MovedIn = TRUE)) THEN
                Pusher$PusherY2 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y2_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#PusherY2_Move_Out_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((Pusher$SorterPusher2MovedOut = FALSE) AND (Pusher$SorterPusher2MovedIn = TRUE)) THEN
                Pusher$PusherY2 := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$SorterPusher2MovedOut THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Y2_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect3:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect2 := FALSE;
            Pusher$Timer2$IN := FALSE;
            Pusher$Timer2$PT := USINT#0;
            IF Pusher$Timer2$IN THEN
                Pusher$Timer2$Q := (Pusher$Timer2$ET = USINT#0);
                IF (Pusher$Timer2$ET > USINT#0) THEN
                    Pusher$Timer2$ET := (Pusher$Timer2$ET - USINT#1);
                ELSE
                    Pusher$Timer2$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer2$Q := FALSE;
                Pusher$Timer2$ET := Pusher$Timer2$PT;
            END_IF;
            Pusher$Slide3_black := (Pusher$Slide3_black - INT#1);
            Pusher$Priority_Var_Black := (Pusher$Priority_Var_Black - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide1_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide1_Black := FALSE;
            Pusher$Timer_Slide1_Black$IN := FALSE;
            Pusher$Timer_Slide1_Black$PT := USINT#0;
            IF Pusher$Timer_Slide1_Black$IN THEN
                Pusher$Timer_Slide1_Black$Q := (Pusher$Timer_Slide1_Black$ET = USINT#0);
                IF (Pusher$Timer_Slide1_Black$ET > USINT#0) THEN
                    Pusher$Timer_Slide1_Black$ET := (Pusher$Timer_Slide1_Black$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide1_Black$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide1_Black$Q := FALSE;
                Pusher$Timer_Slide1_Black$ET := Pusher$Timer_Slide1_Black$PT;
            END_IF;
            Pusher$Slide1_black := (Pusher$Slide1_black - INT#1);
            Pusher$Priority_Var_Black := (Pusher$Priority_Var_Black - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide1_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide1_Metal := FALSE;
            Pusher$Timer_Slide1_Metal$IN := FALSE;
            Pusher$Timer_Slide1_Metal$PT := USINT#0;
            IF Pusher$Timer_Slide1_Metal$IN THEN
                Pusher$Timer_Slide1_Metal$Q := (Pusher$Timer_Slide1_Metal$ET = USINT#0);
                IF (Pusher$Timer_Slide1_Metal$ET > USINT#0) THEN
                    Pusher$Timer_Slide1_Metal$ET := (Pusher$Timer_Slide1_Metal$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide1_Metal$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide1_Metal$Q := FALSE;
                Pusher$Timer_Slide1_Metal$ET := Pusher$Timer_Slide1_Metal$PT;
            END_IF;
            Pusher$Slide1_metal := (Pusher$Slide1_metal - INT#1);
            Pusher$Priority_Var_Metal := (Pusher$Priority_Var_Metal - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide1_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide1_White := FALSE;
            Pusher$Timer_Slide1_White$IN := FALSE;
            Pusher$Timer_Slide1_White$PT := USINT#0;
            IF Pusher$Timer_Slide1_White$IN THEN
                Pusher$Timer_Slide1_White$Q := (Pusher$Timer_Slide1_White$ET = USINT#0);
                IF (Pusher$Timer_Slide1_White$ET > USINT#0) THEN
                    Pusher$Timer_Slide1_White$ET := (Pusher$Timer_Slide1_White$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide1_White$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide1_White$Q := FALSE;
                Pusher$Timer_Slide1_White$ET := Pusher$Timer_Slide1_White$PT;
            END_IF;
            Pusher$Slide1_white := (Pusher$Slide1_white - INT#1);
            Pusher$Priority_Var_White := (Pusher$Priority_Var_White - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide2_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide2_Black := FALSE;
            Pusher$Timer_Slide2_Black$IN := FALSE;
            Pusher$Timer_Slide2_Black$PT := USINT#0;
            IF Pusher$Timer_Slide2_Black$IN THEN
                Pusher$Timer_Slide2_Black$Q := (Pusher$Timer_Slide2_Black$ET = USINT#0);
                IF (Pusher$Timer_Slide2_Black$ET > USINT#0) THEN
                    Pusher$Timer_Slide2_Black$ET := (Pusher$Timer_Slide2_Black$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide2_Black$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide2_Black$Q := FALSE;
                Pusher$Timer_Slide2_Black$ET := Pusher$Timer_Slide2_Black$PT;
            END_IF;
            Pusher$Slide2_black := (Pusher$Slide2_black - INT#1);
            Pusher$Priority_Var_Black := (Pusher$Priority_Var_Black - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide2_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide2_Metal := FALSE;
            Pusher$Timer_Slide2_Metal$IN := FALSE;
            Pusher$Timer_Slide2_Metal$PT := USINT#0;
            IF Pusher$Timer_Slide2_Metal$IN THEN
                Pusher$Timer_Slide2_Metal$Q := (Pusher$Timer_Slide2_Metal$ET = USINT#0);
                IF (Pusher$Timer_Slide2_Metal$ET > USINT#0) THEN
                    Pusher$Timer_Slide2_Metal$ET := (Pusher$Timer_Slide2_Metal$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide2_Metal$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide2_Metal$Q := FALSE;
                Pusher$Timer_Slide2_Metal$ET := Pusher$Timer_Slide2_Metal$PT;
            END_IF;
            Pusher$Slide2_metal := (Pusher$Slide2_metal - INT#1);
            Pusher$Priority_Var_Metal := (Pusher$Priority_Var_Metal - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide2_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect_Slide2_White := FALSE;
            Pusher$Timer_Slide2_White$IN := FALSE;
            Pusher$Timer_Slide2_White$PT := USINT#0;
            IF Pusher$Timer_Slide2_White$IN THEN
                Pusher$Timer_Slide2_White$Q := (Pusher$Timer_Slide2_White$ET = USINT#0);
                IF (Pusher$Timer_Slide2_White$ET > USINT#0) THEN
                    Pusher$Timer_Slide2_White$ET := (Pusher$Timer_Slide2_White$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide2_White$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide2_White$Q := FALSE;
                Pusher$Timer_Slide2_White$ET := Pusher$Timer_Slide2_White$PT;
            END_IF;
            Pusher$Slide2_white := (Pusher$Slide2_white - INT#1);
            Pusher$Priority_Var_White := (Pusher$Priority_Var_White - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide3_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$Slide3_metal := (Pusher$Slide3_metal - INT#1);
            Pusher$Priority_Var_Metal := (Pusher$Priority_Var_Metal - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Reset_interconnect_Slide3_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$interconnect3 := FALSE;
            Pusher$Timer3$IN := FALSE;
            Pusher$Timer3$PT := USINT#0;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$Slide3_white := (Pusher$Slide3_white - INT#1);
            Pusher$Priority_Var_White := (Pusher$Priority_Var_White - INT#1);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Interstep_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_Timer_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
                Pusher$Timer_Slide2_Black$IN := Pusher$SorterLightnesssensorCraneInterfaceInverse;
                Pusher$Timer_Slide2_Black$PT := Pusher$Duration_Slide2_Black;
                IF Pusher$Timer_Slide2_Black$IN THEN
                    Pusher$Timer_Slide2_Black$Q := (Pusher$Timer_Slide2_Black$ET = USINT#0);
                    IF (Pusher$Timer_Slide2_Black$ET > USINT#0) THEN
                        Pusher$Timer_Slide2_Black$ET := (Pusher$Timer_Slide2_Black$ET - USINT#1);
                    ELSE
                        Pusher$Timer_Slide2_Black$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer_Slide2_Black$Q := FALSE;
                    Pusher$Timer_Slide2_Black$ET := Pusher$Timer_Slide2_Black$PT;
                END_IF;
                Pusher$interconnect_Slide2_Black := Pusher$Timer_Slide2_Black$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide2_Black THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_Out_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_Timer_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer_Slide2_Metal$IN := TRUE;
            Pusher$Timer_Slide2_Metal$PT := Pusher$Duration_Slide2_Metal;
            IF Pusher$Timer_Slide2_Metal$IN THEN
                Pusher$Timer_Slide2_Metal$Q := (Pusher$Timer_Slide2_Metal$ET = USINT#0);
                IF (Pusher$Timer_Slide2_Metal$ET > USINT#0) THEN
                    Pusher$Timer_Slide2_Metal$ET := (Pusher$Timer_Slide2_Metal$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide2_Metal$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide2_Metal$Q := FALSE;
                Pusher$Timer_Slide2_Metal$ET := Pusher$Timer_Slide2_Metal$PT;
            END_IF;
            Pusher$interconnect_Slide2_Metal := Pusher$Timer_Slide2_Metal$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide2_Metal THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_Out_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_Timer_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer_Slide2_White$IN := TRUE;
            Pusher$Timer_Slide2_White$PT := Pusher$Duration_Slide2_White;
            IF Pusher$Timer_Slide2_White$IN THEN
                Pusher$Timer_Slide2_White$Q := (Pusher$Timer_Slide2_White$ET = USINT#0);
                IF (Pusher$Timer_Slide2_White$ET > USINT#0) THEN
                    Pusher$Timer_Slide2_White$ET := (Pusher$Timer_Slide2_White$ET - USINT#1);
                ELSE
                    Pusher$Timer_Slide2_White$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer_Slide2_White$Q := FALSE;
                Pusher$Timer_Slide2_White$ET := Pusher$Timer_Slide2_White$PT;
            END_IF;
            Pusher$interconnect_Slide2_White := Pusher$Timer_Slide2_White$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect_Slide2_White THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_Out_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_black_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_Timer_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_metal_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Pusher$SorterLightnessSensorPusher2 AND Pusher$SorterCapacitiveSensorPusher2) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Test_For_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Slide_white_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Pusher$SorterLightnessSensorPusher2 AND NOT Pusher$SorterCapacitiveSensorPusher2) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Test_For_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Test_For_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_Timer_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Second_Test_For_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Second_Slide_Timer_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Third_Slide_black_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (NOT Pusher$SorterLightnessSensorPusher2 AND NOT Pusher$SorterCapacitiveSensorPusher2) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Third_Slide_metal_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Pusher$SorterLightnessSensorPusher2 AND Pusher$SorterCapacitiveSensorPusher2) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Third_Slide_white_workpieces:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Pusher$SorterLightnessSensorPusher2 AND NOT Pusher$SorterCapacitiveSensorPusher2) THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Wait_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((NOT Pusher$SorterLightnessSensorPusher2 AND NOT Pusher$SorterCapacitiveSensorPusher2) = TRUE) THEN
                Pusher$Timer2$IN := (NOT Pusher$SorterLightnessSensorPusher2 AND NOT Pusher$SorterCapacitiveSensorPusher2);
                Pusher$Timer2$PT := Pusher$Duration2;
                IF Pusher$Timer2$IN THEN
                    Pusher$Timer2$Q := (Pusher$Timer2$ET = USINT#0);
                    IF (Pusher$Timer2$ET > USINT#0) THEN
                        Pusher$Timer2$ET := (Pusher$Timer2$ET - USINT#1);
                    ELSE
                        Pusher$Timer2$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer2$Q := FALSE;
                    Pusher$Timer2$ET := Pusher$Timer2$PT;
                END_IF;
                Pusher$interconnect2 := Pusher$Timer2$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect2 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect3;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer3$IN := TRUE;
            Pusher$Timer3$PT := Pusher$Duration3;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect3 := Pusher$Timer3$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide3_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Pusher$Timer3$IN := TRUE;
            Pusher$Timer3$PT := Pusher$Duration3;
            IF Pusher$Timer3$IN THEN
                Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                IF (Pusher$Timer3$ET > USINT#0) THEN
                    Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                ELSE
                    Pusher$Timer3$ET := USINT#0;
                END_IF;
            ELSE
                Pusher$Timer3$Q := FALSE;
                Pusher$Timer3$ET := Pusher$Timer3$PT;
            END_IF;
            Pusher$interconnect3 := Pusher$Timer3$Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#Reset_interconnect_Slide3_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y1_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY1 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY1;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_In_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y1_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY1 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY1;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_In_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y1_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY1 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY1;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY1_Move_In_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y2_Black:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY2 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY2;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_In_Black;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y2_Metal:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY2 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY2;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_In_Metal;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Pusher_states_t#Wait_Y2_White:
            {* begin(State) *}
            {* begin(onEntry) *}
            Pusher$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF (Pusher$PusherY2 = TRUE) THEN
                Pusher$Timer3$IN := Pusher$PusherY2;
                Pusher$Timer3$PT := Pusher$Duration3;
                IF Pusher$Timer3$IN THEN
                    Pusher$Timer3$Q := (Pusher$Timer3$ET = USINT#0);
                    IF (Pusher$Timer3$ET > USINT#0) THEN
                        Pusher$Timer3$ET := (Pusher$Timer3$ET - USINT#1);
                    ELSE
                        Pusher$Timer3$ET := USINT#0;
                    END_IF;
                ELSE
                    Pusher$Timer3$Q := FALSE;
                    Pusher$Timer3$ET := Pusher$Timer3$PT;
                END_IF;
                Pusher$interconnect3 := Pusher$Timer3$Q;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF Pusher$interconnect3 THEN
                Pusher$_transit := TRUE;
                Pusher$_state := Pusher_states_t#PusherY2_Move_In_White;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    IF ((Actuator_SorterGreenLampConveyor AND Actuator_MagazinGreenLamp) AND Actuator_StampGreenLamp) THEN
        IF (((Stamp$StartCommandStamp AND Crane$StartCommandCrane) AND Conveyor$StartCommandConveyor) AND Mag$StartCommandMagazin) THEN
            Crane$StartVar := TRUE;
            Conveyor$StartVar := TRUE;
            Mag$StartVar := TRUE;
            Pusher$StartVar := TRUE;
            Stamp$StartVar := TRUE;
        END_IF;
    END_IF;
    Crane$SFCReset := FALSE;
    Conveyor$SFCReset := FALSE;
    Mag$SFCReset := FALSE;
    Pusher$SFCReset := FALSE;
    Stamp$SFCReset := FALSE;
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
    Crane$SFCReset := TRUE;
    Conveyor$SFCReset := TRUE;
    Mag$SFCReset := TRUE;
    Pusher$SFCReset := TRUE;
    Stamp$SFCReset := TRUE;
    Crane$StartVar := FALSE;
    Conveyor$StartVar := FALSE;
    Mag$StartVar := FALSE;
    Pusher$StartVar := FALSE;
    Stamp$StartVar := FALSE;
END_IF;
END_PROGRAM
