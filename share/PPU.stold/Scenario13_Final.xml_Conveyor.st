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
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterConveyorTowardsStacker := TRUE;
            SorterConveyorTowardsCrane := FALSE;
            Timer_Conveyor_Test(IN := TRUE, PT := Duration_Conveyor_Test);
            interconnect_Conveyor_Test := Timer_Conveyor_Test.Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF interconnect_Conveyor_Test THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_init_2;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_Stop_Empty_Magazin:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnectConveyorStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_Towards_Stacker:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterConveyorTowardsStacker := TRUE;
            SorterConveyorTowardsCrane := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Runtime_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_init_2:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnect_Conveyor_Test := FALSE;
            Timer_Conveyor_Test(IN := FALSE, PT := TIME#);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Conveyor_pause:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterConveyorTowardsStacker := FALSE;
            SorterConveyorTowardsCrane := FALSE;
            interconnect_Conveyor_Runtime := FALSE;
            Timer_Conveyor_Runtime(IN := FALSE, PT := TIME#);
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Interstep;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Green_Lamp:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            SorterGreenLampConveyor := TRUE;
            interconnectConveyorStartCommand := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Init;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF TRUE THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Start_Conveyor;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Interstep:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            StartCommandConveyor := TRUE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF StartVar THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Runtime_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Timer_Conveyor_Runtime(IN := TRUE, PT := Duration_Conveyor_Runtime);
            interconnect_Conveyor_Runtime := Timer_Conveyor_Runtime.Q;
            {* end(onActive) *}
            {* begin(transition) *}
            IF interconnect_Conveyor_Runtime THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_pause;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Start_Conveyor:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
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
            {* end(onActive) *}
            {* begin(transition) *}
            IF interconnectConveyorStartCommand THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Green_Lamp;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
        Conveyor_states_t#Step0:
            {* begin(State) *}
            {* begin(onEntry) *}
            _transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Towards_Stacker;
            ELSEIF NOT SorterLightbarrierCraneInterface THEN
                _transit := TRUE;
                _state := Conveyor_states_t#Conveyor_Stop_Empty_Magazin;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
END_FUNCTION_BLOCK

