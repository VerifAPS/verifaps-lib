TYPE
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Crane_states_t : (Crane_Init , Crane_Init_2 , Crane_Lift_Conveyor , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_Stop , Crane_Turn_Left_Metallic , Crane_Turn_Left_NOT_Metallic , Init , Interstep , Interstep_2 , Interstep_Check_Workpiece , Magazin_Stop , Start_Crane , Step0 , TimeDelay , Turn_Right , release);
END_TYPE

PROGRAM Main

VAR  Actuator_CraneLower : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_CraneTurnClockwise : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_CraneTurnCounterclockwise : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinGreenLamp : BOOL; END_VAR {*LRWXP*}
VAR  Actuator_MagazinSlider : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinVacuumOff : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinVacuumOn : BOOL; END_VAR {*LrWXP*}
VAR  Actuator_MagazinWhiteLamp : BOOL; END_VAR {*LrwxP*}
VAR_INPUT  Crane$CraneDown : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$CraneLower : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$CraneOnConveyor : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$CraneOnMagazin : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$CraneSucked : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$CraneTurnClockwise : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Crane$CraneTurnCounterclockwise : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$CraneUp : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$MagazinCapacitiveSensor : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$MagazinVacuumOff : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Crane$MagazinVacuumOn : BOOL; END_VAR {*ORWxp*}
VAR  Crane$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Crane$SFCReset : BOOL; END_VAR {*IrWXp*}
VAR_INPUT  Crane$SliderMovedOut : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Crane$SliderNotMovedOut : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  Crane$StartButtonMagazin : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Crane$StartCommandCrane : BOOL; END_VAR {*ORWxp*}
VAR_INPUT  Crane$StartVar : BOOL; END_VAR {*IRWxp*}
VAR_OUTPUT  Crane$TimeDelay_Timer$ET : USINT; END_VAR {*ORWxp*}
VAR_INPUT  Crane$TimeDelay_Timer$IN : BOOL; END_VAR {*IRWxp*}
VAR_INPUT  Crane$TimeDelay_Timer$PT : USINT; END_VAR {*IRWxp*}
VAR_OUTPUT  Crane$TimeDelay_Timer$Q : BOOL; END_VAR {*ORWxp*}
VAR  Crane$TimeDelay_Timer_Duration : UINT := #12; END_VAR {*LRwxp*}
VAR  Crane$TimeDelay_Timer_interconnect : BOOL; END_VAR {*LRWxp*}
VAR_INPUT  Crane$WorkpieceReady : BOOL; END_VAR {*IRWXp*}
VAR  Crane$_state : Crane_states_t; END_VAR {*LRWxp*}
VAR  Crane$_transit : BOOL; END_VAR {*LrWxp*}
VAR  Crane$interconnectCraneStartCommand : BOOL; END_VAR {*LRWxp*}
VAR_INPUT  Mag$CraneDown : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Mag$CraneLower : BOOL; END_VAR {*Orwxp*}
VAR_INPUT  Mag$CraneOnConveyor : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Mag$CraneOnMagazin : BOOL; END_VAR {*IRWXp*}
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
VAR  Sensor_CraneDown : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneOnConveyor : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneOnMagazin : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CranePosition : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_CranePositionStamp : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_CraneSucked : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneUp : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinCapacitiveSensor : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinEmergencyStop : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinOpticalSensor : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_MagazinSwitchManuellAutomatic : BOOL; END_VAR {*LrwxP*}
VAR  Sensor_SliderMovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_SliderNotMovedOut : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_StartButtonMagazin : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_WorkpieceReady : BOOL; END_VAR {*LRwxP*}
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
Crane$WorkpieceReady := Sensor_WorkpieceReady;
Crane$CraneUp := Sensor_CraneUp;
Crane$CraneOnConveyor := Sensor_CraneOnConveyor;
Crane$CraneDown := Sensor_CraneDown;
Crane$CraneSucked := Sensor_CraneSucked;
Crane$CraneOnMagazin := Sensor_CraneOnMagazin;
Crane$MagazinCapacitiveSensor := Sensor_MagazinCapacitiveSensor;
Crane$SliderMovedOut := Sensor_SliderMovedOut;
Crane$StartButtonMagazin := Sensor_StartButtonMagazin;
Actuator_CraneTurnCounterclockwise := Crane$CraneTurnCounterclockwise;
Actuator_CraneTurnClockwise := Crane$CraneTurnClockwise;
Actuator_CraneLower := Crane$CraneLower;
Actuator_MagazinVacuumOff := Crane$MagazinVacuumOff;
Actuator_MagazinVacuumOn := Crane$MagazinVacuumOn;
IF Sensor_MagazinEmergencyStop THEN
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
            IF Mag$CraneOnConveyor THEN
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
            IF Mag$CraneOnMagazin THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step0;
            END_IF;
            {* end(transition) *}
            {* begin(onExit) *}
            {* end(onExit) *}
            {* end(State) *}
        
            END_CASE;
    CASE Crane$_state OF 
        Crane_states_t#Crane_Init:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := TRUE;
            Crane$interconnectCraneStartCommand := FALSE;
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
        
        Crane_states_t#Crane_Stop:
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
            IF Crane$CraneOnConveyor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor_Metallic;
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
            IF Crane$CraneOnConveyor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor;
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
        
        Crane_states_t#Interstep_Check_Workpiece:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            {* end(onActive) *}
            {* begin(transition) *}
            IF Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Magazin_Stop;
            ELSEIF NOT Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Stop;
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
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := TRUE;
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
        
        Crane_states_t#Start_Crane:
            {* begin(State) *}
            {* begin(onEntry) *}
            Crane$_transit := FALSE;
            {* end(onEntry) *}
            {* begin(onActive) *}
            Crane$CraneLower := FALSE;
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
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
            Crane$CraneLower := FALSE;
            {* end(onActive) *}
            {* begin(transition) *}
            IF (Crane$CraneUp AND Crane$MagazinCapacitiveSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_Metallic;
            ELSEIF (Crane$CraneUp AND NOT Crane$MagazinCapacitiveSensor) THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
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
                Crane$_state := Crane_states_t#Turn_Right;
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
            IF Crane$CraneOnMagazin THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_Check_Workpiece;
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
        
            END_CASE;
    IF Actuator_MagazinGreenLamp THEN
        IF (Crane$StartCommandCrane AND Mag$StartCommandMagazin) THEN
            Crane$StartVar := TRUE;
            Mag$StartVar := TRUE;
        END_IF;
    END_IF;
    Crane$SFCReset := FALSE;
    Mag$SFCReset := FALSE;
ELSEIF NOT Sensor_MagazinEmergencyStop THEN
    Actuator_MagazinSlider := FALSE;
    Actuator_CraneLower := FALSE;
    Actuator_MagazinVacuumOn := FALSE;
    Actuator_MagazinVacuumOff := TRUE;
    Actuator_MagazinGreenLamp := FALSE;
    Actuator_CraneTurnCounterclockwise := FALSE;
    Actuator_CraneTurnClockwise := FALSE;
    Crane$SFCReset := TRUE;
    Mag$SFCReset := TRUE;
    Crane$StartVar := FALSE;
    Mag$StartVar := FALSE;
END_IF;
END_PROGRAM
