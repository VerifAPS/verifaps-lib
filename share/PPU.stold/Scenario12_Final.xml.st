TYPE
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Conveyor_states_t : (Conveyor_Init , Conveyor_Stop_Empty_Magazin , Conveyor_Towards_Stacker , Conveyor_init_2 , Conveyor_pause , Green_Lamp , Init , Interstep , Runtime_Conveyor , Start_Conveyor , Step0);
    Crane_states_t : (Crane_Go_Up , Crane_Go_Up_White , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_At_Stamp2 , Crane_Lift_Conveyor , Crane_Lift_Conveyor2 , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_Magazin_White , Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Metallic2 , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic , Crane_On_Stamp_Metallic2 , Crane_On_Stamp_Metallic2_Lower , Crane_On_Stamp_Stop_Black , Crane_On_Stamp_White , Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_Metallic2 , Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Crane_Turn_Left_White , Crane_Turn_Right_From_Stamp , Init , Interstep , Interstep_2 , Interstep_3 , Interstep_4 , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , Magazin_Stop_Final , No_Workpiece_ready , Reset_interconnect , Stamp_Pressure_Profile_Set_Metallic , Stamp_Pressure_Profile_Set_White , Start_Crane , Step0 , Step2 , Step3 , Step4 , Suck_At_Stamp , Suck_At_Stamp2 , TimeDelay , Turn_Right , Turn_Right_Black , Turn_Right_Final , pause , release , release2 , release_Black , release_Workpiece , release_Workpiece_White);
    Stamp_states_t : (Green_Lamp , Init , Interstep , Intertsep_2 , StampProcess , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 , Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);
    Pusher_states_t : (Check_For_Black , Check_For_Metal , Check_For_White , First_Slide_Timer_Black , First_Slide_Timer_Metal , First_Slide_Timer_White , First_Slide_black_workpieces , First_Slide_metal_workpieces , First_Slide_white_workpieces , Init , Interstep , Interstep_2 , PusherY1_Move_In_Black , PusherY1_Move_In_Metal , PusherY1_Move_In_White , PusherY1_Move_Out_Black , PusherY1_Move_Out_Metal , PusherY1_Move_Out_White , PusherY2_Move_In_Black , PusherY2_Move_In_Metal , PusherY2_Move_In_White , PusherY2_Move_Out_Black , PusherY2_Move_Out_Metal , PusherY2_Move_Out_White , Reset_interconnect3 , Reset_interconnect_Slide1_Black , Reset_interconnect_Slide1_Metal , Reset_interconnect_Slide1_White , Reset_interconnect_Slide2_Black , Reset_interconnect_Slide2_Metal , Reset_interconnect_Slide2_White , Reset_interconnect_Slide3_Metal , Reset_interconnect_Slide3_White , Second_Slide_Timer_Black , Second_Slide_Timer_Metal , Second_Slide_Timer_White , Second_Slide_black_workpieces , Second_Slide_metal_workpieces , Second_Slide_white_workpieces , Second_Test_For_Metal , Second_Test_For_White , Third_Slide_black_workpieces , Third_Slide_metal_workpieces , Third_Slide_white_workpieces , Wait_Black , Wait_Metal , Wait_White , Wait_Y1_Black , Wait_Y1_Metal , Wait_Y1_White , Wait_Y2_Black , Wait_Y2_Metal , Wait_Y2_White);
END_TYPE

FUNCTION_BLOCK Magazin
    VAR_INPUT  CraneDown : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  CraneLower : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  CraneOnConveyor : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneOnMagazin : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  CraneSucked : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  CraneTurnClockwise : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  CraneTurnCounterclockwise : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  CraneUp : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  MagazinGreenLamp : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  MagazinSlider : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  MagazinWhiteLamp : BOOL; END_VAR {*Orwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SliderMovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  StartButtonMagazin : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  StartCommandMagazin : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  WorkpieceReady : BOOL; END_VAR {*Irwxp*}
    VAR  _state : Magazin_states_t; END_VAR {*Lrwxp*}
    VAR  _transit : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnectMagazinStartCommand : BOOL; END_VAR {*Lrwxp*}
    
    CASE _state OF 
        Magazin_states_t#Green_Lamp:
            _transit := FALSE;
            MagazinGreenLamp := TRUE;
            interconnectMagazinStartCommand := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init;
            END_IF;
        
        Magazin_states_t#Init:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Start_Magazin;
            END_IF;
        
        Magazin_states_t#Interstep:
            _transit := FALSE;
            StartCommandMagazin := TRUE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Magazin_states_t#convey;
            END_IF;
        
        Magazin_states_t#Magazin_Init:
            _transit := FALSE;
            MagazinSlider := TRUE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init_2;
            END_IF;
        
        Magazin_states_t#Magazin_Init_2:
            _transit := FALSE;
            MagazinSlider := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#Slider_Move_Back:
            _transit := FALSE;
            IF ((SliderMovedOut = TRUE) AND (SliderNotMovedOut = FALSE)) THEN
                MagazinSlider := FALSE;
            END_IF;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step1;
            END_IF;
        
        Magazin_states_t#Start_Magazin:
            _transit := FALSE;
            MagazinSlider := FALSE;
            MagazinGreenLamp := FALSE;
            StartVar := FALSE;
            StartCommandMagazin := FALSE;
            IF (StartButtonMagazin = TRUE) THEN
                interconnectMagazinStartCommand := TRUE;
            END_IF;
            IF interconnectMagazinStartCommand THEN
                _transit := TRUE;
                _state := Magazin_states_t#Green_Lamp;
            END_IF;
        
        Magazin_states_t#Step0:
            _transit := FALSE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Magazin_states_t#Slider_Move_Back;
            END_IF;
        
        Magazin_states_t#Step1:
            _transit := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#convey:
            _transit := FALSE;
            IF SliderNotMovedOut THEN
                MagazinSlider := TRUE;
            END_IF;
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step0;
            END_IF;
        
            END_CASE;
END_FUNCTION_BLOCK

FUNCTION_BLOCK Conveyor
    VAR  Duration_Conveyor_Runtime : TIME := TIME#4.0s500.0ms; END_VAR {*Lrwxp*}
    VAR  Duration_Conveyor_Test : TIME := TIME#1.0s; END_VAR {*Lrwxp*}
    VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
    VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  SorterConveyorTowardsCrane : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  SorterConveyorTowardsStacker : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  SorterGreenLampConveyor : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  SorterLightbarrierCraneInterface : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterStartButton : BOOL; END_VAR {*Irwxp*}
    VAR_INPUT  SorterSwitchManuellAutomatic : BOOL; END_VAR {*Irwxp*}
    VAR_OUTPUT  SorterWhiteLampConveyor : BOOL; END_VAR {*Orwxp*}
    VAR_OUTPUT  StartCommandConveyor : BOOL; END_VAR {*Orwxp*}
    VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
    VAR  Timer_Conveyor_Runtime : TON; END_VAR {*Lrwxp*}
    VAR  Timer_Conveyor_Test : TON; END_VAR {*Lrwxp*}
    VAR  _state : Conveyor_states_t; END_VAR {*Lrwxp*}
    VAR  _transit : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnectConveyorStartCommand : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnectConveyorTerminationCommand : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Conveyor_Runtime : BOOL; END_VAR {*Lrwxp*}
    VAR  interconnect_Conveyor_Test : BOOL; END_VAR {*Lrwxp*}
    
    CASE _state OF 
        Conveyor_states_t#Conveyor_Init:
            _transit := FALSE;
            SorterConveyorTowardsStacker := TRUE;
            SorterConveyorTowardsCrane := FALSE;
            Timer_Conveyor_Test(IN := TRUE, PT := Duration_Conveyor_Test);
            interconnect_Conveyor_Test := Timer_Conveyor_Test.Q;
            IF interconnect_Conveyor_Test THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_init_2;
            END_IF;
        
        Conveyor_states_t#Conveyor_Stop_Empty_Magazin:
            _transit := FALSE;
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnectConveyorStartCommand := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
        
        Conveyor_states_t#Conveyor_Towards_Stacker:
            _transit := FALSE;
            SorterConveyorTowardsStacker := TRUE;
            SorterConveyorTowardsCrane := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Runtime_Conveyor;
            END_IF;
        
        Conveyor_states_t#Conveyor_init_2:
            _transit := FALSE;
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnect_Conveyor_Test := FALSE;
            Timer_Conveyor_Test(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
        
        Conveyor_states_t#Conveyor_pause:
            _transit := FALSE;
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnect_Conveyor_Runtime := FALSE;
            Timer_Conveyor_Runtime(IN := FALSE, PT := TIME#);
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
        
        Conveyor_states_t#Green_Lamp:
            _transit := FALSE;
            SorterGreenLampConveyor := TRUE;
            interconnectConveyorStartCommand := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Init;
            END_IF;
        
        Conveyor_states_t#Init:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Start_Conveyor;
            END_IF;
        
        Conveyor_states_t#Interstep:
            _transit := FALSE;
            StartCommandConveyor := TRUE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Step0;
            END_IF;
        
        Conveyor_states_t#Runtime_Conveyor:
            _transit := FALSE;
            Timer_Conveyor_Runtime(IN := TRUE, PT := Duration_Conveyor_Runtime);
            interconnect_Conveyor_Runtime := Timer_Conveyor_Runtime.Q;
            IF interconnect_Conveyor_Runtime THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_pause;
            END_IF;
        
        Conveyor_states_t#Start_Conveyor:
            _transit := FALSE;
            interconnectConveyorTerminationCommand := FALSE;
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            SorterGreenLampConveyor := FALSE;
            interconnect_Conveyor_Runtime := FALSE;
            interconnect_Conveyor_Test := FALSE;
            Timer_Conveyor_Test(IN := FALSE, PT := TIME#);
            Timer_Conveyor_Runtime(IN := FALSE, PT := TIME#);
            StartVar := FALSE;
            StartCommandConveyor := FALSE;
            IF (SorterStartButton = TRUE) THEN
                interconnectConveyorStartCommand := TRUE;
            END_IF;
            IF interconnectConveyorStartCommand THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Green_Lamp;
            END_IF;
        
        Conveyor_states_t#Step0:
            _transit := FALSE;
            IF SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Towards_Stacker;
            ELSEIF NOT SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Stop_Empty_Magazin;
            END_IF;
        
            END_CASE;
END_FUNCTION_BLOCK

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
FUNCTION_BLOCK Crane
VAR_OUTPUT  AnalogCranePressure : INT; END_VAR {*Orwxp*}
VAR_INPUT  CraneDown : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  CraneLower : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  CraneOnConveyor : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CraneOnMagazin : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CranePositionStamp : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CraneSucked : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  CraneTurnClockwise : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  CraneTurnCounterclockwise : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  CraneUp : BOOL; END_VAR {*Irwxp*}
VAR  Duration1 : TIME := TIME#1.0s500.0ms; END_VAR {*Lrwxp*}
VAR_INPUT  MagazinCapacitiveSensor : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  MagazinOpticalSensor : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR {*Orwxp*}
VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SliderMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampLowered : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampSliderFilled : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampSliderSensorMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StartButtonMagazin : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  StartCommandCrane : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
VAR  TimeDelay_Timer : TON; END_VAR {*Lrwxp*}
VAR  TimeDelay_Timer_Duration : TIME := TIME#50.0ms; END_VAR {*Lrwxp*}
VAR  TimeDelay_Timer_interconnect : BOOL; END_VAR {*Lrwxp*}
VAR  Timer1 : TON; END_VAR {*Lrwxp*}
VAR_INPUT  WorkpieceReady : BOOL; END_VAR {*Irwxp*}
VAR  _state : Crane_states_t; END_VAR {*Lrwxp*}
VAR  _transit : BOOL; END_VAR {*Lrwxp*}
VAR  actualtime1 : TIME; END_VAR {*Lrwxp*}
VAR  interconnect : BOOL; END_VAR {*Lrwxp*}
VAR  interconnectCraneStartCommand : BOOL; END_VAR {*Lrwxp*}

CASE _state OF 
    Crane_states_t#Crane_Go_Up:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Step3;
        END_IF;
    
    Crane_states_t#Crane_Go_Up_White:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Step3;
        END_IF;
    
    Crane_states_t#Crane_Init:
        _transit := FALSE;
        CraneLower := TRUE;
        interconnectCraneStartCommand := FALSE;
        AnalogCranePressure := INT#6000;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Init_2;
        END_IF;
    
    Crane_states_t#Crane_Init_2:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
    
    Crane_states_t#Crane_Lift_At_Stamp:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_From_Stamp;
        END_IF;
    
    Crane_states_t#Crane_Lift_At_Stamp2:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Right_From_Stamp;
        END_IF;
    
    Crane_states_t#Crane_Lift_Conveyor:
        _transit := FALSE;
        CraneLower := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
    
    Crane_states_t#Crane_Lift_Conveyor2:
        _transit := FALSE;
        CraneLower := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
    
    Crane_states_t#Crane_Lift_Conveyor_Black:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
        END_IF;
    
    Crane_states_t#Crane_Lift_Magazin:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
        END_IF;
    
    Crane_states_t#Crane_Lift_Magazin_Metallic:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_Metallic;
        END_IF;
    
    Crane_states_t#Crane_Lift_Magazin_White:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_White;
        END_IF;
    
    Crane_states_t#Crane_Lift_NOT_Metallic_Black:
        _transit := FALSE;
        CraneLower := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
        END_IF;
    
    Crane_states_t#Crane_Lower:
        _transit := FALSE;
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        CraneLower := TRUE;
        AnalogCranePressure := INT#0;
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Step0;
        END_IF;
    
    Crane_states_t#Crane_On_Conveyor:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release;
        END_IF;
    
    Crane_states_t#Crane_On_Conveyor_Metallic:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release;
        END_IF;
    
    Crane_states_t#Crane_On_Conveyor_Metallic2:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release2;
        END_IF;
    
    Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release_Black;
        END_IF;
    
    Crane_states_t#Crane_On_Stamp_Metallic:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release_Workpiece;
        END_IF;
    
    Crane_states_t#Crane_On_Stamp_Metallic2:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        IF StampLowered THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep_4;
        END_IF;
    
    Crane_states_t#Crane_On_Stamp_Metallic2_Lower:
        _transit := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#Suck_At_Stamp2;
        END_IF;
    
    Crane_states_t#Crane_On_Stamp_Stop_Black:
        _transit := FALSE;
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Reset_interconnect;
        END_IF;
    
    Crane_states_t#Crane_On_Stamp_White:
        _transit := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release_Workpiece_White;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Stop_Black;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_From_Stamp:
        _transit := FALSE;
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor_Metallic;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_Metallic:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Metallic;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_Metallic2:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Metallic2;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_NOT_Metallic:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
        END_IF;
    
    Crane_states_t#Crane_Turn_Left_White:
        _transit := FALSE;
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_White;
        END_IF;
    
    Crane_states_t#Crane_Turn_Right_From_Stamp:
        _transit := FALSE;
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor_Metallic2;
        END_IF;
    
    Crane_states_t#Init:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Start_Crane;
        END_IF;
    
    Crane_states_t#Interstep:
        _transit := FALSE;
        StartCommandCrane := TRUE;
        IF StartVar THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep_2;
        END_IF;
    
    Crane_states_t#Interstep_2:
        _transit := FALSE;
        IF SliderMovedOut THEN
            _transit := TRUE;
            _state := Crane_states_t#TimeDelay;
        END_IF;
    
    Crane_states_t#Interstep_3:
        _transit := FALSE;
        IF NOT WorkpieceReady THEN
            _transit := TRUE;
            _state := Crane_states_t#No_Workpiece_ready;
        ELSEIF WorkpieceReady THEN
            _transit := TRUE;
            _state := Crane_states_t#Turn_Right;
        END_IF;
    
    Crane_states_t#Interstep_4:
        _transit := FALSE;
        IF StampSliderSensorMovedOut THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Metallic2_Lower;
        END_IF;
    
    Crane_states_t#Lower_Crane:
        _transit := FALSE;
        CraneLower := TRUE;
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#Suck_At_Stamp;
        END_IF;
    
    Crane_states_t#Magazin_Stop:
        _transit := FALSE;
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lower;
        END_IF;
    
    Crane_states_t#Magazin_Stop_Black:
        _transit := FALSE;
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        CraneLower := TRUE;
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_NOT_Metallic_Black;
        END_IF;
    
    Crane_states_t#Magazin_Stop_Final:
        _transit := FALSE;
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Start_Crane;
        END_IF;
    
    Crane_states_t#No_Workpiece_ready:
        _transit := FALSE;
        MagazinVacuumOn := FALSE;
        MagazinVacuumOff := FALSE;
        CraneLower := FALSE;
        IF StampSliderFilled THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_Metallic2;
        ELSEIF NOT StampSliderFilled THEN
            _transit := TRUE;
            _state := Crane_states_t#Turn_Right_Final;
        END_IF;
    
    Crane_states_t#Reset_interconnect:
        _transit := FALSE;
        interconnect := FALSE;
        Timer1(IN := FALSE, PT := TIME#1.0ms);
        IF SliderMovedOut THEN
            _transit := TRUE;
            _state := Crane_states_t#Lower_Crane;
        END_IF;
    
    Crane_states_t#Stamp_Pressure_Profile_Set_Metallic:
        _transit := FALSE;
        AnalogCranePressure := INT#7000;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Magazin_Metallic;
        END_IF;
    
    Crane_states_t#Stamp_Pressure_Profile_Set_White:
        _transit := FALSE;
        AnalogCranePressure := INT#6000;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Magazin_White;
        END_IF;
    
    Crane_states_t#Start_Crane:
        _transit := FALSE;
        CraneLower := FALSE;
        MagazinVacuumOff := FALSE;
        MagazinVacuumOn := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        AnalogCranePressure := INT#0;
        StartVar := FALSE;
        StartCommandCrane := FALSE;
        IF (StartButtonMagazin = TRUE) THEN
            interconnectCraneStartCommand := TRUE;
        END_IF;
        IF interconnectCraneStartCommand THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Init;
        END_IF;
    
    Crane_states_t#Step0:
        _transit := FALSE;
        IF (NOT MagazinCapacitiveSensor AND MagazinOpticalSensor) THEN
            _transit := TRUE;
            _state := Crane_states_t#Stamp_Pressure_Profile_Set_White;
        ELSEIF (MagazinCapacitiveSensor AND MagazinOpticalSensor) THEN
            _transit := TRUE;
            _state := Crane_states_t#Stamp_Pressure_Profile_Set_Metallic;
        ELSEIF (NOT MagazinCapacitiveSensor AND NOT MagazinOpticalSensor) THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Magazin;
        END_IF;
    
    Crane_states_t#Step2:
        _transit := FALSE;
        IF (NOT MagazinCapacitiveSensor AND NOT MagazinOpticalSensor) THEN
            _transit := TRUE;
            _state := Crane_states_t#Turn_Right_Black;
        ELSEIF (MagazinCapacitiveSensor OR MagazinOpticalSensor) THEN
            _transit := TRUE;
            _state := Crane_states_t#pause;
        END_IF;
    
    Crane_states_t#Step3:
        _transit := FALSE;
        IF NOT WorkpieceReady THEN
            _transit := TRUE;
            _state := Crane_states_t#Step4;
        ELSEIF WorkpieceReady THEN
            _transit := TRUE;
            _state := Crane_states_t#Step2;
        END_IF;
    
    Crane_states_t#Step4:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
    
    Crane_states_t#Suck_At_Stamp:
        _transit := FALSE;
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_At_Stamp;
        END_IF;
    
    Crane_states_t#Suck_At_Stamp2:
        _transit := FALSE;
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_At_Stamp2;
        END_IF;
    
    Crane_states_t#TimeDelay:
        _transit := FALSE;
        TimeDelay_Timer(IN := TRUE, PT := TimeDelay_Timer_Duration);
        TimeDelay_Timer_interconnect := TimeDelay_Timer.Q;
        IF TimeDelay_Timer_interconnect THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep_3;
        END_IF;
    
    Crane_states_t#Turn_Right:
        _transit := FALSE;
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        IF CraneOnMagazin THEN
            _transit := TRUE;
            _state := Crane_states_t#Magazin_Stop;
        END_IF;
    
    Crane_states_t#Turn_Right_Black:
        _transit := FALSE;
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        IF CraneOnMagazin THEN
            _transit := TRUE;
            _state := Crane_states_t#Magazin_Stop_Black;
        END_IF;
    
    Crane_states_t#Turn_Right_Final:
        _transit := FALSE;
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        AnalogCranePressure := INT#0;
        IF CraneOnMagazin THEN
            _transit := TRUE;
            _state := Crane_states_t#Magazin_Stop_Final;
        END_IF;
    
    Crane_states_t#pause:
        _transit := FALSE;
        Timer1(IN := CraneUp, PT := Duration1);
        interconnect := Timer1.Q;
        IF interconnect THEN
            _transit := TRUE;
            _state := Crane_states_t#Reset_interconnect;
        END_IF;
    
    Crane_states_t#release:
        _transit := FALSE;
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Conveyor;
        END_IF;
    
    Crane_states_t#release2:
        _transit := FALSE;
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Conveyor2;
        END_IF;
    
    Crane_states_t#release_Black:
        _transit := FALSE;
        MagazinVacuumOn := FALSE;
        MagazinVacuumOff := TRUE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Conveyor_Black;
        END_IF;
    
    Crane_states_t#release_Workpiece:
        _transit := FALSE;
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Go_Up;
        END_IF;
    
    Crane_states_t#release_Workpiece_White:
        _transit := FALSE;
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Go_Up_White;
        END_IF;
    
    END_CASE;
END_FUNCTION_BLOCK

FUNCTION_BLOCK Stamp
VAR_INPUT  CraneDown : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CraneOnConveyor : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CranePositionStamp : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CraneSucked : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  CraneUp : BOOL; END_VAR {*Irwxp*}
VAR  Duration : TIME := TIME#500.0ms; END_VAR {*Lrwxp*}
VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  StampGreenLamp : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  StampLowered : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  StampPressure : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  StampPusher : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  StampSliderFilled : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  StampSliderMovedIn : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  StampSliderMovedOut : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  StampSliderSensorMovedIn : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampSliderSensorMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampStartButton : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampUp : BOOL; END_VAR {*Irwxp*}
VAR_OUTPUT  StampWhiteLamp : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  StartCommandStamp : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
VAR  Timer : TON; END_VAR {*Lrwxp*}
VAR  _state : Stamp_states_t; END_VAR {*Lrwxp*}
VAR  _transit : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect : BOOL; END_VAR {*Lrwxp*}
VAR  interconnectStampStartCommand : BOOL; END_VAR {*Lrwxp*}

CASE _state OF 
    Stamp_states_t#Green_Lamp:
        _transit := FALSE;
        StampGreenLamp := TRUE;
        interconnectStampStartCommand := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_1;
        END_IF;
    
    Stamp_states_t#Init:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Start_Stamp;
        END_IF;
    
    Stamp_states_t#Interstep:
        _transit := FALSE;
        StartCommandStamp := TRUE;
        IF StartVar THEN
            _transit := TRUE;
            _state := Stamp_states_t#Intertsep_2;
        END_IF;
    
    Stamp_states_t#Intertsep_2:
        _transit := FALSE;
        IF StampSliderFilled THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step0;
        END_IF;
    
    Stamp_states_t#StampProcess:
        _transit := FALSE;
        StampSliderMovedIn := FALSE;
        StampPusher := TRUE;
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step1;
        END_IF;
    
    Stamp_states_t#StampSliderBack:
        _transit := FALSE;
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampProcess;
        END_IF;
    
    Stamp_states_t#StampSliderForward:
        _transit := FALSE;
        StampPusher := FALSE;
        StampSliderMovedOut := TRUE;
        IF ((StampLowered = FALSE) AND (StampUp = TRUE)) THEN
            interconnect := FALSE;
        END_IF;
        Timer(IN := FALSE, PT := TIME#1.0ms);
        IF StampSliderMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step2;
        END_IF;
    
    Stamp_states_t#Stamp_Init_1:
        _transit := FALSE;
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_2;
        END_IF;
    
    Stamp_states_t#Stamp_Init_2:
        _transit := FALSE;
        StampSliderMovedIn := FALSE;
        StampSliderMovedOut := TRUE;
        IF StampSliderSensorMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_3;
        END_IF;
    
    Stamp_states_t#Stamp_Init_3:
        _transit := FALSE;
        StampPusher := TRUE;
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_4;
        END_IF;
    
    Stamp_states_t#Stamp_Init_4:
        _transit := FALSE;
        StampPusher := FALSE;
        IF StampUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF;
    
    Stamp_states_t#Start_Stamp:
        _transit := FALSE;
        StampSliderMovedOut := FALSE;
        StampSliderMovedIn := FALSE;
        StampPusher := FALSE;
        StampGreenLamp := FALSE;
        StampPressure := FALSE;
        StartCommandStamp := FALSE;
        IF (StampStartButton = TRUE) THEN
            interconnectStampStartCommand := TRUE;
        END_IF;
        IF interconnectStampStartCommand THEN
            _transit := TRUE;
            _state := Stamp_states_t#Green_Lamp;
        END_IF;
    
    Stamp_states_t#Step0:
        _transit := FALSE;
        IF CraneUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderBack;
        END_IF;
    
    Stamp_states_t#Step1:
        _transit := FALSE;
        Timer(IN := StampLowered, PT := TIME#);
        interconnect := Timer.Q;
        IF interconnect THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderForward;
        END_IF;
    
    Stamp_states_t#Step2:
        _transit := FALSE;
        IF (CraneOnConveyor AND NOT StampSliderFilled) THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF;
    
    END_CASE;
END_FUNCTION_BLOCK

FUNCTION_BLOCK Pusher
VAR  Duration2 : TIME := TIME#2.0s; END_VAR {*Lrwxp*}
VAR  Duration3 : TIME := TIME#200.0ms; END_VAR {*Lrwxp*}
VAR  Duration_Slide1_Black : TIME := TIME#900.0ms; END_VAR {*Lrwxp*}
VAR  Duration_Slide1_Metal : TIME := TIME#320.0ms; END_VAR {*Lrwxp*}
VAR  Duration_Slide1_White : TIME := TIME#320.0ms; END_VAR {*Lrwxp*}
VAR  Duration_Slide2_Black : TIME := TIME#2.0s; END_VAR {*Lrwxp*}
VAR  Duration_Slide2_Metal : TIME := TIME#390.0ms; END_VAR {*Lrwxp*}
VAR  Duration_Slide2_White : TIME := TIME#390.0ms; END_VAR {*Lrwxp*}
VAR  Priority_Var_Black : INT := INT#3; END_VAR {*Lrwxp*}
VAR  Priority_Var_Metal : INT := INT#3; END_VAR {*Lrwxp*}
VAR  Priority_Var_White : INT := INT#3; END_VAR {*Lrwxp*}
VAR_OUTPUT  PusherY1 : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  PusherY2 : BOOL; END_VAR {*Orwxp*}
VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
VAR  Slide1_black : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide1_metal : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide1_white : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide2_black : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide2_metal : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide2_white : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide3_black : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide3_metal : INT := INT#1; END_VAR {*Lrwxp*}
VAR  Slide3_white : INT := INT#1; END_VAR {*Lrwxp*}
VAR_INPUT  SorterCapacitiveSensorPusher1 : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterCapacitiveSensorPusher2 : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterLightbarrierCraneInterface : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterLightnessSensorPusher1 : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterLightnessSensorPusher2 : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterLightnessSensorPusher3 : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterLightnesssensorCraneInterfaceInverse : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterPusher1MovedIn : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterPusher1MovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterPusher2MovedIn : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterPusher2MovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SorterStartButton : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StartVar : BOOL; END_VAR {*Irwxp*}
VAR  Timer2 : TON; END_VAR {*Lrwxp*}
VAR  Timer3 : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide1_Black : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide1_Metal : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide1_White : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide2_Black : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide2_Metal : TON; END_VAR {*Lrwxp*}
VAR  Timer_Slide2_White : TON; END_VAR {*Lrwxp*}
VAR  _state : Pusher_states_t; END_VAR {*Lrwxp*}
VAR  _transit : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect2 : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect3 : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide1_Black : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide1_Metal : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide1_White : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide2_Black : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide2_Metal : BOOL; END_VAR {*Lrwxp*}
VAR  interconnect_Slide2_White : BOOL; END_VAR {*Lrwxp*}

CASE _state OF 
    Pusher_states_t#Check_For_Black:
        _transit := FALSE;
        IF ((Slide3_black = INT#1) AND (Priority_Var_Black = INT#3)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Third_Slide_black_workpieces;
        ELSEIF ((Slide2_black = INT#1) AND (Priority_Var_Black = INT#2)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_black_workpieces;
        ELSEIF ((Slide1_black = INT#1) AND (Priority_Var_Black = INT#1)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_black_workpieces;
        END_IF;
    
    Pusher_states_t#Check_For_Metal:
        _transit := FALSE;
        IF ((Slide3_metal = INT#1) AND (Priority_Var_Metal = INT#3)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Third_Slide_metal_workpieces;
        ELSEIF ((Slide2_metal = INT#1) AND (Priority_Var_Metal = INT#2)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_metal_workpieces;
        ELSEIF ((Slide1_metal = INT#1) AND (Priority_Var_Metal = INT#1)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_metal_workpieces;
        END_IF;
    
    Pusher_states_t#Check_For_White:
        _transit := FALSE;
        IF ((Slide1_white = INT#1) AND (Priority_Var_White = INT#1)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_white_workpieces;
        ELSEIF ((Slide2_white = INT#1) AND (Priority_Var_White = INT#2)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_white_workpieces;
        ELSEIF ((Slide3_white = INT#1) AND (Priority_Var_White = INT#3)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Third_Slide_white_workpieces;
        END_IF;
    
    Pusher_states_t#First_Slide_Timer_Black:
        _transit := FALSE;
        IF (SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
            Timer_Slide1_Black(IN := SorterLightnesssensorCraneInterfaceInverse, PT := Duration_Slide1_Black);
            interconnect_Slide1_Black := Timer_Slide1_Black.Q;
        END_IF;
        IF interconnect_Slide1_Black THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_Out_Black;
        END_IF;
    
    Pusher_states_t#First_Slide_Timer_Metal:
        _transit := FALSE;
        Timer_Slide1_Metal(IN := TRUE, PT := Duration_Slide1_Metal);
        interconnect_Slide1_Metal := Timer_Slide1_Metal.Q;
        IF interconnect_Slide1_Metal THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_Out_Metal;
        END_IF;
    
    Pusher_states_t#First_Slide_Timer_White:
        _transit := FALSE;
        Timer_Slide1_White(IN := TRUE, PT := Duration_Slide1_White);
        interconnect_Slide1_White := Timer_Slide1_White.Q;
        IF interconnect_Slide1_White THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_Out_White;
        END_IF;
    
    Pusher_states_t#First_Slide_black_workpieces:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_Timer_Black;
        END_IF;
    
    Pusher_states_t#First_Slide_metal_workpieces:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_Timer_Metal;
        END_IF;
    
    Pusher_states_t#First_Slide_white_workpieces:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#First_Slide_Timer_White;
        END_IF;
    
    Pusher_states_t#Init:
        _transit := FALSE;
        IF StartVar THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep;
        END_IF;
    
    Pusher_states_t#Interstep:
        _transit := FALSE;
        PusherY1 := FALSE;
        PusherY2 := FALSE;
        interconnect2 := FALSE;
        interconnect3 := FALSE;
        StartVar := FALSE;
        interconnect_Slide1_Black := FALSE;
        interconnect_Slide2_Black := FALSE;
        interconnect_Slide1_White := FALSE;
        interconnect_Slide2_White := FALSE;
        interconnect_Slide1_Metal := FALSE;
        interconnect_Slide2_Metal := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Interstep_2:
        _transit := FALSE;
        IF ((SorterLightnessSensorPusher1 AND NOT SorterCapacitiveSensorPusher1) AND (Priority_Var_White > INT#0)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Check_For_White;
        ELSEIF ((SorterLightnessSensorPusher1 AND SorterCapacitiveSensorPusher1) AND (Priority_Var_Metal > INT#0)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Check_For_Metal;
        ELSEIF ((NOT SorterLightnesssensorCraneInterfaceInverse AND SorterLightbarrierCraneInterface) AND (Priority_Var_Black > INT#0)) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Check_For_Black;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_In_Black:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
            PusherY1 := FALSE;
        END_IF;
        IF SorterPusher1MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide1_Black;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_In_Metal:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
            PusherY1 := FALSE;
        END_IF;
        IF SorterPusher1MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide1_Metal;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_In_White:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = TRUE) AND (SorterPusher1MovedIn = FALSE)) THEN
            PusherY1 := FALSE;
        END_IF;
        IF SorterPusher1MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide1_White;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_Out_Black:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
            PusherY1 := TRUE;
        END_IF;
        IF SorterPusher1MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y1_Black;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_Out_Metal:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
            PusherY1 := TRUE;
        END_IF;
        IF SorterPusher1MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y1_Metal;
        END_IF;
    
    Pusher_states_t#PusherY1_Move_Out_White:
        _transit := FALSE;
        IF ((SorterPusher1MovedOut = FALSE) AND (SorterPusher1MovedIn = TRUE)) THEN
            PusherY1 := TRUE;
        END_IF;
        IF SorterPusher1MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y1_White;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_In_Black:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
            PusherY2 := FALSE;
        END_IF;
        IF SorterPusher2MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide2_Black;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_In_Metal:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
            PusherY2 := FALSE;
        END_IF;
        IF SorterPusher2MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide2_Metal;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_In_White:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = TRUE) AND (SorterPusher2MovedIn = FALSE)) THEN
            PusherY2 := FALSE;
        END_IF;
        IF SorterPusher2MovedIn THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide2_White;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_Out_Black:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
            PusherY2 := TRUE;
        END_IF;
        IF SorterPusher2MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y2_Black;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_Out_Metal:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
            PusherY2 := TRUE;
        END_IF;
        IF SorterPusher2MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y2_Metal;
        END_IF;
    
    Pusher_states_t#PusherY2_Move_Out_White:
        _transit := FALSE;
        IF ((SorterPusher2MovedOut = FALSE) AND (SorterPusher2MovedIn = TRUE)) THEN
            PusherY2 := TRUE;
        END_IF;
        IF SorterPusher2MovedOut THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Y2_White;
        END_IF;
    
    Pusher_states_t#Reset_interconnect3:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        Slide3_black := (Slide3_black - INT#1);
        Priority_Var_Black := (Priority_Var_Black - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide1_Black:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide1_Black := FALSE;
        Timer_Slide1_Black(IN := FALSE, PT := TIME#);
        Slide1_black := (Slide1_black - INT#1);
        Priority_Var_Black := (Priority_Var_Black - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide1_Metal:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide1_Metal := FALSE;
        Timer_Slide1_Metal(IN := FALSE, PT := TIME#);
        Slide1_metal := (Slide1_metal - INT#1);
        Priority_Var_Metal := (Priority_Var_Metal - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide1_White:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide1_White := FALSE;
        Timer_Slide1_White(IN := FALSE, PT := TIME#);
        Slide1_white := (Slide1_white - INT#1);
        Priority_Var_White := (Priority_Var_White - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide2_Black:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide2_Black := FALSE;
        Timer_Slide2_Black(IN := FALSE, PT := TIME#);
        Slide2_black := (Slide2_black - INT#1);
        Priority_Var_Black := (Priority_Var_Black - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide2_Metal:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide2_Metal := FALSE;
        Timer_Slide2_Metal(IN := FALSE, PT := TIME#);
        Slide2_metal := (Slide2_metal - INT#1);
        Priority_Var_Metal := (Priority_Var_Metal - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide2_White:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        interconnect_Slide2_White := FALSE;
        Timer_Slide2_White(IN := FALSE, PT := TIME#);
        Slide2_white := (Slide2_white - INT#1);
        Priority_Var_White := (Priority_Var_White - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide3_Metal:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        Slide3_metal := (Slide3_metal - INT#1);
        Priority_Var_Metal := (Priority_Var_Metal - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Reset_interconnect_Slide3_White:
        _transit := FALSE;
        interconnect3 := FALSE;
        Timer3(IN := FALSE, PT := TIME#);
        Slide3_white := (Slide3_white - INT#1);
        Priority_Var_White := (Priority_Var_White - INT#1);
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Interstep_2;
        END_IF;
    
    Pusher_states_t#Second_Slide_Timer_Black:
        _transit := FALSE;
        IF (SorterLightnesssensorCraneInterfaceInverse = TRUE) THEN
            Timer_Slide2_Black(IN := SorterLightnesssensorCraneInterfaceInverse, PT := Duration_Slide2_Black);
            interconnect_Slide2_Black := Timer_Slide2_Black.Q;
        END_IF;
        IF interconnect_Slide2_Black THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_Out_Black;
        END_IF;
    
    Pusher_states_t#Second_Slide_Timer_Metal:
        _transit := FALSE;
        Timer_Slide2_Metal(IN := TRUE, PT := Duration_Slide2_Metal);
        interconnect_Slide2_Metal := Timer_Slide2_Metal.Q;
        IF interconnect_Slide2_Metal THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_Out_Metal;
        END_IF;
    
    Pusher_states_t#Second_Slide_Timer_White:
        _transit := FALSE;
        Timer_Slide2_White(IN := TRUE, PT := Duration_Slide2_White);
        interconnect_Slide2_White := Timer_Slide2_White.Q;
        IF interconnect_Slide2_White THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_Out_White;
        END_IF;
    
    Pusher_states_t#Second_Slide_black_workpieces:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_Timer_Black;
        END_IF;
    
    Pusher_states_t#Second_Slide_metal_workpieces:
        _transit := FALSE;
        IF (SorterLightnessSensorPusher2 AND SorterCapacitiveSensorPusher2) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Test_For_Metal;
        END_IF;
    
    Pusher_states_t#Second_Slide_white_workpieces:
        _transit := FALSE;
        IF (SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Test_For_White;
        END_IF;
    
    Pusher_states_t#Second_Test_For_Metal:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_Timer_Metal;
        END_IF;
    
    Pusher_states_t#Second_Test_For_White:
        _transit := FALSE;
        IF TRUE THEN
            _transit := TRUE;
            _state := Pusher_states_t#Second_Slide_Timer_White;
        END_IF;
    
    Pusher_states_t#Third_Slide_black_workpieces:
        _transit := FALSE;
        IF (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Black;
        END_IF;
    
    Pusher_states_t#Third_Slide_metal_workpieces:
        _transit := FALSE;
        IF (SorterLightnessSensorPusher2 AND SorterCapacitiveSensorPusher2) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_Metal;
        END_IF;
    
    Pusher_states_t#Third_Slide_white_workpieces:
        _transit := FALSE;
        IF (SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) THEN
            _transit := TRUE;
            _state := Pusher_states_t#Wait_White;
        END_IF;
    
    Pusher_states_t#Wait_Black:
        _transit := FALSE;
        IF ((NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2) = TRUE) THEN
            Timer2(IN := (NOT SorterLightnessSensorPusher2 AND NOT SorterCapacitiveSensorPusher2), PT := Duration2);
            interconnect2 := Timer2.Q;
        END_IF;
        IF interconnect2 THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect3;
        END_IF;
    
    Pusher_states_t#Wait_Metal:
        _transit := FALSE;
        Timer3(IN := TRUE, PT := Duration3);
        interconnect3 := Timer3.Q;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide3_Metal;
        END_IF;
    
    Pusher_states_t#Wait_White:
        _transit := FALSE;
        Timer3(IN := TRUE, PT := Duration3);
        interconnect3 := Timer3.Q;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#Reset_interconnect_Slide3_White;
        END_IF;
    
    Pusher_states_t#Wait_Y1_Black:
        _transit := FALSE;
        IF (PusherY1 = TRUE) THEN
            Timer3(IN := PusherY1, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_In_Black;
        END_IF;
    
    Pusher_states_t#Wait_Y1_Metal:
        _transit := FALSE;
        IF (PusherY1 = TRUE) THEN
            Timer3(IN := PusherY1, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_In_Metal;
        END_IF;
    
    Pusher_states_t#Wait_Y1_White:
        _transit := FALSE;
        IF (PusherY1 = TRUE) THEN
            Timer3(IN := PusherY1, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY1_Move_In_White;
        END_IF;
    
    Pusher_states_t#Wait_Y2_Black:
        _transit := FALSE;
        IF (PusherY2 = TRUE) THEN
            Timer3(IN := PusherY2, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_In_Black;
        END_IF;
    
    Pusher_states_t#Wait_Y2_Metal:
        _transit := FALSE;
        IF (PusherY2 = TRUE) THEN
            Timer3(IN := PusherY2, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_In_Metal;
        END_IF;
    
    Pusher_states_t#Wait_Y2_White:
        _transit := FALSE;
        IF (PusherY2 = TRUE) THEN
            Timer3(IN := PusherY2, PT := Duration3);
            interconnect3 := Timer3.Q;
        END_IF;
        IF interconnect3 THEN
            _transit := TRUE;
            _state := Pusher_states_t#PusherY2_Move_In_White;
        END_IF;
    
    END_CASE;
END_FUNCTION_BLOCK

