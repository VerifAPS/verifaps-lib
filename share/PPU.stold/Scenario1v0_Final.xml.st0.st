TYPE
    Magazin_states_t : (Green_Lamp , Init , Interstep , Magazin_Init , Magazin_Init_2 , Slider_Move_Back , Start_Magazin , Step0 , Step1 , convey);
    Crane_states_t : (Crane_Init , Crane_Init_2 , Crane_Lift_Conveyor , Crane_Lift_Magazine , Crane_On_Conveyor , Crane_Stop , Crane_Turn_Left , Init , Interstep , Interstep_2 , Interstep_Check_Workpiece , Magazin_Stop , Start_Crane , TimeDelay , Turn_Right , release);
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
VAR_OUTPUT  Crane$MagazinVacuumOff : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Crane$MagazinVacuumOn : BOOL; END_VAR {*ORWxp*}
VAR  Crane$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Crane$SFCReset : BOOL; END_VAR {*IrWxp*}
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
VAR_INPUT  Mag$CraneOnConveyor : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Mag$CraneOnMagazin : BOOL; END_VAR {*IRWXp*}
VAR_INPUT  Mag$CraneSucked : BOOL; END_VAR {*Irwxp*}
VAR_INPUT  Mag$CraneUp : BOOL; END_VAR {*IRWXp*}
VAR_OUTPUT  Mag$MagazinGreenLamp : BOOL; END_VAR {*ORWxp*}
VAR_OUTPUT  Mag$MagazinSlider : BOOL; END_VAR {*ORWxp*}
VAR  Mag$SFCInit : BOOL; END_VAR {*Lrwxp*}
VAR_INPUT  Mag$SFCReset : BOOL; END_VAR {*IrWxp*}
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
VAR  Sensor_CraneSucked : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_CraneUp : BOOL; END_VAR {*LRwxP*}
VAR  Sensor_MagazinEmergencyStop : BOOL; END_VAR {*LRwxP*}
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
            Mag$_transit := FALSE;
            Mag$MagazinGreenLamp := TRUE;
            Mag$interconnectMagazinStartCommand := FALSE;
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init;
            END_IF;
        
        Magazin_states_t#Init:
            Mag$_transit := FALSE;
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Start_Magazin;
            END_IF;
        
        Magazin_states_t#Interstep:
            Mag$_transit := FALSE;
            Mag$StartCommandMagazin := TRUE;
            IF Mag$StartVar THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#convey;
            END_IF;
        
        Magazin_states_t#Magazin_Init:
            Mag$_transit := FALSE;
            Mag$MagazinSlider := TRUE;
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Magazin_Init_2;
            END_IF;
        
        Magazin_states_t#Magazin_Init_2:
            Mag$_transit := FALSE;
            Mag$MagazinSlider := FALSE;
            IF TRUE THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#Slider_Move_Back:
            Mag$_transit := FALSE;
            IF ((Mag$SliderMovedOut = TRUE) AND (Mag$SliderNotMovedOut = FALSE)) THEN
                Mag$MagazinSlider := FALSE;
            END_IF;
            IF Mag$CraneUp THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step1;
            END_IF;
        
        Magazin_states_t#Start_Magazin:
            Mag$_transit := FALSE;
            Mag$MagazinSlider := FALSE;
            Mag$MagazinGreenLamp := FALSE;
            Mag$StartVar := FALSE;
            Mag$StartCommandMagazin := FALSE;
            IF (Mag$StartButtonMagazin = TRUE) THEN
                Mag$interconnectMagazinStartCommand := TRUE;
            END_IF;
            IF Mag$interconnectMagazinStartCommand THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Green_Lamp;
            END_IF;
        
        Magazin_states_t#Step0:
            Mag$_transit := FALSE;
            IF Mag$CraneDown THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Slider_Move_Back;
            END_IF;
        
        Magazin_states_t#Step1:
            Mag$_transit := FALSE;
            IF Mag$CraneOnConveyor THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Interstep;
            END_IF;
        
        Magazin_states_t#convey:
            Mag$_transit := FALSE;
            IF Mag$SliderNotMovedOut THEN
                Mag$MagazinSlider := TRUE;
            END_IF;
            IF Mag$CraneOnMagazin THEN
                Mag$_transit := TRUE;
                Mag$_state := Magazin_states_t#Step0;
            END_IF;
        
            END_CASE;
    CASE Crane$_state OF 
        Crane_states_t#Crane_Init:
            Crane$_transit := FALSE;
            Crane$CraneLower := TRUE;
            Crane$interconnectCraneStartCommand := FALSE;
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init_2;
            END_IF;
        
        Crane_states_t#Crane_Init_2:
            Crane$_transit := FALSE;
            Crane$CraneLower := FALSE;
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
        
        Crane_states_t#Crane_Lift_Conveyor:
            Crane$_transit := FALSE;
            Crane$CraneLower := FALSE;
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep;
            END_IF;
        
        Crane_states_t#Crane_Lift_Magazine:
            Crane$_transit := FALSE;
            Crane$CraneLower := FALSE;
            IF Crane$CraneUp THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Turn_Left;
            END_IF;
        
        Crane_states_t#Crane_On_Conveyor:
            Crane$_transit := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneLower := TRUE;
            IF Crane$CraneDown THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#release;
            END_IF;
        
        Crane_states_t#Crane_Stop:
            Crane$_transit := FALSE;
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF;
        
        Crane_states_t#Crane_Turn_Left:
            Crane$_transit := FALSE;
            Crane$CraneTurnCounterclockwise := TRUE;
            Crane$CraneTurnClockwise := FALSE;
            IF Crane$CraneOnConveyor THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_On_Conveyor;
            END_IF;
        
        Crane_states_t#Init:
            Crane$_transit := FALSE;
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Start_Crane;
            END_IF;
        
        Crane_states_t#Interstep:
            Crane$_transit := FALSE;
            Crane$StartCommandCrane := TRUE;
            IF Crane$StartVar THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_2;
            END_IF;
        
        Crane_states_t#Interstep_2:
            Crane$_transit := FALSE;
            IF Crane$SliderMovedOut THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#TimeDelay;
            END_IF;
        
        Crane_states_t#Interstep_Check_Workpiece:
            Crane$_transit := FALSE;
            IF Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Magazin_Stop;
            ELSEIF NOT Crane$WorkpieceReady THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Stop;
            END_IF;
        
        Crane_states_t#Magazin_Stop:
            Crane$_transit := FALSE;
            Crane$CraneTurnClockwise := FALSE;
            Crane$CraneTurnCounterclockwise := FALSE;
            Crane$MagazinVacuumOn := TRUE;
            Crane$MagazinVacuumOff := FALSE;
            Crane$CraneLower := TRUE;
            IF Crane$CraneSucked THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Magazine;
            END_IF;
        
        Crane_states_t#Start_Crane:
            Crane$_transit := FALSE;
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
            IF Crane$interconnectCraneStartCommand THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Init;
            END_IF;
        
        Crane_states_t#TimeDelay:
            Crane$_transit := FALSE;
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
            IF Crane$TimeDelay_Timer_interconnect THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Turn_Right;
            END_IF;
        
        Crane_states_t#Turn_Right:
            Crane$_transit := FALSE;
            Crane$CraneTurnClockwise := TRUE;
            Crane$CraneTurnCounterclockwise := FALSE;
            IF Crane$CraneOnMagazin THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Interstep_Check_Workpiece;
            END_IF;
        
        Crane_states_t#release:
            Crane$_transit := FALSE;
            Crane$MagazinVacuumOff := TRUE;
            Crane$MagazinVacuumOn := FALSE;
            IF TRUE THEN
                Crane$_transit := TRUE;
                Crane$_state := Crane_states_t#Crane_Lift_Conveyor;
            END_IF;
        
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
    Crane$_state := Init;
    Mag$_state := Init;
    Crane$StartVar := FALSE;
    Mag$StartVar := FALSE;
END_IF;
END_PROGRAM
