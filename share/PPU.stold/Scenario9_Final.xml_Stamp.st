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
                _state := Stamp_states_t#Interstep_2;
            END_IF;
        
        Stamp_states_t#Interstep_2:
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

