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
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Stamp_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
END_FUNCTION_BLOCK

