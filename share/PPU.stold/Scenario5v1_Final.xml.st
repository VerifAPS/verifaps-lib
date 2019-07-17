TYPE
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Stamp_states_t : (Green_Lamp , Init , Interstep , Interstep_2 , StampProcess , StampSliderBack , StampSliderForward , Stamp_Init_1 , Stamp_Init_2 , Stamp_Init_3 , Stamp_Init_4 , Start_Stamp , Step0 , Step1 , Step2);
    Crane_states_t : (Crane_Go_Up , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_Conveyor , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic , Crane_On_Stamp_Stop_Black , Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Init , Interstep , Interstep_2 , Last_Workpiece_At_Stamp , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , No_Workpiece_ready , Reset_interconnect , Start_Crane , Step0 , Suck_At_Stamp , TimeDelay , Turn_Right , Turn_Right_Black , pause , release , release_Black , release_Workpiece);
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
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            MagazinGreenLamp := TRUE;
            interconnectMagazinStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Start_Magazin;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            StartCommandMagazin := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF StartVar THEN
                _transit := TRUE;
                _state := Magazin_states_t#convey;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Magazin_Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            MagazinSlider := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Magazin_Init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Magazin_Init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            MagazinSlider := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Slider_Move_Back:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF ((SliderMovedOut = TRUE) AND (SliderNotMovedOut = FALSE)) THEN
                MagazinSlider := FALSE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF CraneUp THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step1;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Start_Magazin:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            MagazinSlider := FALSE;
            MagazinGreenLamp := FALSE;
            StartVar := FALSE;
            StartCommandMagazin := FALSE;
            IF (StartButtonMagazin = TRUE) THEN
                interconnectMagazinStartCommand := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF interconnectMagazinStartCommand THEN
                _transit := TRUE;
                _state := Magazin_states_t#Green_Lamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF CraneDown THEN
                _transit := TRUE;
                _state := Magazin_states_t#Slider_Move_Back;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#Step1:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Magazin_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Magazin_states_t#convey:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            IF SliderNotMovedOut THEN
                MagazinSlider := TRUE;
            END_IF;
            {* end(onActive) *}
            {* begin(transition) *}
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Magazin_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
END_FUNCTION_BLOCK;

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
Crane.StampSliderFilled := Sensor_StampSliderFilled;
Crane.StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_CraneTurnCounterclockwise := Crane.CraneTurnCounterclockwise;
Actuator_CraneTurnClockwise := Crane.CraneTurnClockwise;
Actuator_CraneLower := Crane.CraneLower;
Actuator_MagazinVacuumOff := Crane.MagazinVacuumOff;
Actuator_MagazinVacuumOn := Crane.MagazinVacuumOn;
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
Actuator_AnalogCranePressure := INT#6000;
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
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampGreenLamp := TRUE;
        interconnectStampStartCommand := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_1;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Init:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Stamp_states_t#Start_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Interstep:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StartCommandStamp := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StartVar THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep_2;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Interstep_2:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampSliderFilled THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step0;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#StampProcess:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampSliderMovedIn := FALSE;
        StampPusher := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step1;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#StampSliderBack:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampProcess;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#StampSliderForward:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampPusher := FALSE;
        StampSliderMovedOut := TRUE;
        IF ((StampLowered = FALSE) AND (StampUp = TRUE)) THEN
            interconnect := FALSE;
        END_IF;
        Timer(IN := FALSE, PT := TIME#1.0ms);
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampSliderMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Step2;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Stamp_Init_1:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampSliderMovedIn := TRUE;
        StampSliderMovedOut := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampSliderSensorMovedIn THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_2;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Stamp_Init_2:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampSliderMovedIn := FALSE;
        StampSliderMovedOut := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampSliderSensorMovedOut THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_3;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Stamp_Init_3:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampPusher := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampLowered THEN
            _transit := TRUE;
            _state := Stamp_states_t#Stamp_Init_4;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Stamp_Init_4:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampPusher := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StampUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Start_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StampSliderMovedOut := FALSE;
        StampSliderMovedIn := FALSE;
        StampPusher := FALSE;
        StampGreenLamp := FALSE;
        StampPressure := FALSE;
        StartCommandStamp := FALSE;
        IF (StampStartButton = TRUE) THEN
            interconnectStampStartCommand := TRUE;
        END_IF;
        {* end(onActive) *}
        {* begin(transition) *}
        IF interconnectStampStartCommand THEN
            _transit := TRUE;
            _state := Stamp_states_t#Green_Lamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Step0:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderBack;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Step1:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        Timer(IN := StampLowered, PT := TIME#);
        interconnect := Timer.Q;
        {* end(onActive) *}
        {* begin(transition) *}
        IF interconnect THEN
            _transit := TRUE;
            _state := Stamp_states_t#StampSliderForward;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Stamp_states_t#Step2:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF (CraneOnConveyor AND NOT StampSliderFilled) THEN
            _transit := TRUE;
            _state := Stamp_states_t#Interstep;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    END_CASE;
END_FUNCTION_BLOCK;

FUNCTION_BLOCK Crane
VAR  CranTurnClockwise : BOOL; END_VAR {*Lrwxp*}
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
VAR_OUTPUT  MagazinSlider : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR {*Orwxp*}
VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR {*Orwxp*}
VAR  SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  SFCReset : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SliderMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampLowered : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  StampSliderFilled : BOOL; END_VAR {*Irwxp*}
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
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF (CraneUp AND (MagazinCapacitiveSensor OR NOT WorkpieceReady)) THEN
            _transit := TRUE;
            _state := Crane_states_t#pause;
        ELSEIF ((CraneUp AND NOT MagazinCapacitiveSensor) AND WorkpieceReady) THEN
            _transit := TRUE;
            _state := Crane_states_t#Turn_Right_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Init:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := TRUE;
        interconnectCraneStartCommand := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Init_2;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Init_2:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_At_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_From_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_Conveyor:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_Conveyor_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_Magazin:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_Magazin_Metallic:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_Metallic;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lift_NOT_Metallic_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneUp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Lower:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Step0;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_On_Conveyor:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_On_Conveyor_Metallic:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_On_Stamp_Metallic:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#release_Workpiece;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_On_Stamp_Stop_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Reset_interconnect;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Stop_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Turn_Left_From_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor_Metallic;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Turn_Left_Metallic:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CranePositionStamp THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Stamp_Metallic;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Turn_Left_NOT_Metallic:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnCounterclockwise := TRUE;
        CraneTurnClockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneOnConveyor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Init:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Start_Crane;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Interstep:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        StartCommandCrane := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF StartVar THEN
            _transit := TRUE;
            _state := Crane_states_t#Interstep_2;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Interstep_2:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF SliderMovedOut THEN
            _transit := TRUE;
            _state := Crane_states_t#TimeDelay;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Last_Workpiece_At_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#pause;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Lower_Crane:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneDown THEN
            _transit := TRUE;
            _state := Crane_states_t#Suck_At_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Magazin_Stop:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := FALSE;
        CraneTurnCounterClockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF WorkpieceReady THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lower;
        ELSEIF (NOT WorkpieceReady AND NOT StampSliderFilled) THEN
            _transit := TRUE;
            _state := Crane_states_t#No_Workpiece_ready;
        ELSEIF (NOT WorkpieceReady AND StampSliderFilled) THEN
            _transit := TRUE;
            _state := Crane_states_t#Last_Workpiece_At_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Magazin_Stop_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := FALSE;
        CraneTurnCounterclockwise := FALSE;
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        CraneLower := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_NOT_Metallic_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#No_Workpiece_ready:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Start_Crane;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Reset_interconnect:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        interconnect := FALSE;
        Timer1(IN := FALSE, PT := TIME#1.0ms);
        {* end(onActive) *}
        {* begin(transition) *}
        IF SliderMovedOut THEN
            _transit := TRUE;
            _state := Crane_states_t#Lower_Crane;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Start_Crane:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneLower := FALSE;
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        CraneTurnCounterclockwise := FALSE;
        CraneTurnClockwise := FALSE;
        StartVar := FALSE;
        StartCommandCrane := FALSE;
        IF (StartButtonMagazin = TRUE) THEN
            interconnectCraneStartCommand := TRUE;
        END_IF;
        {* end(onActive) *}
        {* begin(transition) *}
        IF interconnectCraneStartCommand THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Init;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Step0:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        {* end(onActive) *}
        {* begin(transition) *}
        IF NOT MagazinCapacitiveSensor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Magazin;
        ELSEIF MagazinCapacitiveSensor THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Magazin_Metallic;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Suck_At_Stamp:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        MagazinVacuumOn := TRUE;
        MagazinVacuumOff := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneSucked THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_At_Stamp;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#TimeDelay:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        TimeDelay_Timer(IN := TRUE, PT := TimeDelay_Timer_Duration);
        TimeDelay_Timer_interconnect := TimeDelay_Timer.Q;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TimeDelay_Timer_interconnect THEN
            _transit := TRUE;
            _state := Crane_states_t#Turn_Right;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Turn_Right:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneOnMagazin THEN
            _transit := TRUE;
            _state := Crane_states_t#Magazin_Stop;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#Turn_Right_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        CraneTurnClockwise := TRUE;
        CraneTurnCounterclockwise := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF CraneOnMagazin THEN
            _transit := TRUE;
            _state := Crane_states_t#Magazin_Stop_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#pause:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        Timer1(IN := CraneUp, PT := Duration1);
        interconnect := Timer1.Q;
        {* end(onActive) *}
        {* begin(transition) *}
        IF interconnect THEN
            _transit := TRUE;
            _state := Crane_states_t#Reset_interconnect;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#release:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Conveyor;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#release_Black:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        MagazinVacuumOn := FALSE;
        MagazinVacuumOff := TRUE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Lift_Conveyor_Black;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    Crane_states_t#release_Workpiece:
        {* begin(State) *}
        {* begin(onEntry) *}
        _transit := FALSE;
        {* end(onEntry) *}
        {* begin(onActive) *}
        MagazinVacuumOff := TRUE;
        MagazinVacuumOn := FALSE;
        {* end(onActive) *}
        {* begin(transition) *}
        IF TRUE THEN
            _transit := TRUE;
            _state := Crane_states_t#Crane_Go_Up;
        END_IF;
        {* end(transition) *}
        {* begin(onExit) *}
        {* end(onExit) *}
        {* end(State) *}
    
    END_CASE;
END_FUNCTION_BLOCK;

