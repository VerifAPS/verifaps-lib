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

