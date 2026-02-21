TYPE
    Crane_states_t : (Crane_Go_Up , Crane_Init , Crane_Init_2 , Crane_Lift_At_Stamp , Crane_Lift_Conveyor , Crane_Lift_Conveyor_Black , Crane_Lift_Magazin , Crane_Lift_Magazin_Metallic , Crane_Lift_NOT_Metallic_Black , Crane_Lower , Crane_On_Conveyor , Crane_On_Conveyor_Metallic , Crane_On_Conveyor_Not_Metallica_Black , Crane_On_Stamp_Metallic , Crane_On_Stamp_Stop_Black , Crane_Turn_Left_Back_To_Stamp , Crane_Turn_Left_From_Stamp , Crane_Turn_Left_Metallic , Crane_Turn_Left_NOT_Metallic , Crane_Turn_Left_NOT_Metallic_Black , Init , Interstep , Interstep_2 , Last_Workpiece_At_Stamp , Lower_Crane , Magazin_Stop , Magazin_Stop_Black , No_Workpiece_ready , Reset_interconnect , Start_Crane , Step0 , Suck_At_Stamp , TimeDelay , Turn_Right , Turn_Right_Black , pause , release , release_Black , release_Workpiece);
END_TYPE

FUNCTION_BLOCK TON

VAR_INPUT
    IN : BOOL;
    PT : USINT;
END_VAR

VAR_OUTPUT
    Q  : BOOL;
    ET : USINT;
END_VAR

IF IN THEN
    Q:= ET = USINT#0;
    IF ET > USINT#0 THEN
        ET := ET - USINT#1;
    ELSE
        ET := USINT#0;
    END_IF
ELSE
    Q  := FALSE;
    ET := PT;
END_IF

END_FUNCTION_BLOCK

PROGRAM Crane
    VAR  CranTurnClockwise : BOOL; END_VAR
    VAR_INPUT  CraneDown : BOOL; END_VAR
    VAR_OUTPUT  CraneLower : BOOL; END_VAR
    VAR_INPUT  CraneOnConveyor : BOOL; END_VAR
    VAR_INPUT  CraneOnMagazin : BOOL; END_VAR
    VAR_INPUT  CranePositionStamp : BOOL; END_VAR
    VAR_INPUT  CraneSucked : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnClockwise : BOOL; END_VAR
    VAR_OUTPUT  CraneTurnCounterclockwise : BOOL; END_VAR
    VAR_INPUT  CraneUp : BOOL; END_VAR
    VAR  Duration1 : TIME := TIME#1.0s500.0ms; END_VAR
    VAR_INPUT  MagazinCapacitiveSensor : BOOL; END_VAR
    VAR_OUTPUT  MagazinSlider : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOff : BOOL; END_VAR
    VAR_OUTPUT  MagazinVacuumOn : BOOL; END_VAR
    VAR  SFCInit : BOOL; END_VAR
    VAR_INPUT  SFCReset : BOOL; END_VAR
    VAR_INPUT  SliderMovedOut : BOOL; END_VAR
    VAR_INPUT  SliderNotMovedOut : BOOL; END_VAR
    VAR_INPUT  StampLowered : BOOL; END_VAR
    VAR_INPUT  StampSliderFilled : BOOL; END_VAR
    VAR_INPUT  StartButtonMagazin : BOOL; END_VAR
    VAR_OUTPUT  StartCommandCrane : BOOL; END_VAR
    VAR_INPUT  StartVar : BOOL; END_VAR
    VAR  TimeDelay_Timer : TON; END_VAR
    VAR  TimeDelay_Timer_Duration : TIME := TIME#50.0ms; END_VAR
    VAR  TimeDelay_Timer_interconnect : BOOL; END_VAR
    VAR  Timer1 : TON; END_VAR
    VAR_INPUT  WorkpieceReady : BOOL; END_VAR
    VAR  _state : Crane_states_t; END_VAR
    VAR  _transit : BOOL; END_VAR
    VAR  actualtime1 : TIME; END_VAR
    VAR  interconnect : BOOL; END_VAR
    VAR  interconnectCraneStartCommand : BOOL; END_VAR

    CASE _state OF
        Crane_states_t#Crane_Go_Up:
            _transit := FALSE;
            CraneLower := FALSE;
            IF (CraneUp AND (MagazinCapacitiveSensor OR NOT WorkpieceReady)) THEN
                _transit := TRUE;
                _state := Crane_states_t#pause;
            ELSEIF ((CraneUp AND NOT MagazinCapacitiveSensor) AND WorkpieceReady) THEN
                _transit := TRUE;
                _state := Crane_states_t#Turn_Right_Black;
            END_IF

        Crane_states_t#Crane_Init:
            _transit := FALSE;
            CraneLower := TRUE;
            interconnectCraneStartCommand := FALSE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Init_2;
            END_IF

        Crane_states_t#Crane_Init_2:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_At_Stamp:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Turn_Left_From_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor:
            _transit := FALSE;
            CraneLower := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Interstep;
            END_IF

        Crane_states_t#Crane_Lift_Conveyor_Black:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Turn_Left_Back_To_Stamp;
            END_IF

        Crane_states_t#Crane_Lift_Magazin:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_Magazin_Metallic:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Turn_Left_Metallic;
            END_IF

        Crane_states_t#Crane_Lift_NOT_Metallic_Black:
            _transit := FALSE;
            CraneLower := FALSE;
            IF CraneUp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black;
            END_IF

        Crane_states_t#Crane_Lower:
            _transit := FALSE;
            MagazinVacuumOn := TRUE;
            MagazinVacuumOff := FALSE;
            CraneLower := TRUE;
            IF CraneSucked THEN
                _transit := TRUE;
                _state := Crane_states_t#Step0;
            END_IF

        Crane_states_t#Crane_On_Conveyor:
            _transit := FALSE;
            CraneTurnCounterclockwise := FALSE;
            CraneTurnClockwise := FALSE;
            CraneLower := TRUE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Metallic:
            _transit := FALSE;
            CraneTurnCounterclockwise := FALSE;
            CraneTurnClockwise := FALSE;
            CraneLower := TRUE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#release;
            END_IF

        Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black:
            _transit := FALSE;
            CraneTurnCounterclockwise := FALSE;
            CraneTurnClockwise := FALSE;
            CraneLower := TRUE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#release_Black;
            END_IF

        Crane_states_t#Crane_On_Stamp_Metallic:
            _transit := FALSE;
            CraneTurnCounterclockwise := FALSE;
            CraneTurnClockwise := FALSE;
            CraneLower := TRUE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#release_Workpiece;
            END_IF

        Crane_states_t#Crane_On_Stamp_Stop_Black:
            _transit := FALSE;
            CraneTurnClockwise := FALSE;
            CraneTurnCounterclockwise := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#Crane_Turn_Left_Back_To_Stamp:
            _transit := FALSE;
            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;
            IF CranePositionStamp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_Stop_Black;
            END_IF

        Crane_states_t#Crane_Turn_Left_From_Stamp:
            _transit := FALSE;
            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_Metallic:
            _transit := FALSE;
            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;
            IF CranePositionStamp THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Stamp_Metallic;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic:
            _transit := FALSE;
            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor;
            END_IF

        Crane_states_t#Crane_Turn_Left_NOT_Metallic_Black:
            _transit := FALSE;
            CraneTurnCounterclockwise := TRUE;
            CraneTurnClockwise := FALSE;
            IF CraneOnConveyor THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_On_Conveyor_Not_Metallica_Black;
            END_IF

        Crane_states_t#Init:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#Interstep:
            _transit := FALSE;
            StartCommandCrane := TRUE;
            IF StartVar THEN
                _transit := TRUE;
                _state := Crane_states_t#Interstep_2;
            END_IF

        Crane_states_t#Interstep_2:
            _transit := FALSE;
            IF SliderMovedOut THEN
                _transit := TRUE;
                _state := Crane_states_t#TimeDelay;
            END_IF

        Crane_states_t#Last_Workpiece_At_Stamp:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#pause;
            END_IF

        Crane_states_t#Lower_Crane:
            _transit := FALSE;
            CraneLower := TRUE;
            IF CraneDown THEN
                _transit := TRUE;
                _state := Crane_states_t#Suck_At_Stamp;
            END_IF

        Crane_states_t#Magazin_Stop:
            _transit := FALSE;
            CraneTurnClockwise := FALSE;
            CraneTurnCounterclockwise := FALSE;
            IF (NOT WorkpieceReady AND NOT StampSliderFilled) THEN
                _transit := TRUE;
                _state := Crane_states_t#No_Workpiece_ready;
            ELSEIF WorkpieceReady THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lower;
            ELSEIF (NOT WorkpieceReady AND StampSliderFilled) THEN
                _transit := TRUE;
                _state := Crane_states_t#Last_Workpiece_At_Stamp;
            END_IF

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
            END_IF

        Crane_states_t#No_Workpiece_ready:
            _transit := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Start_Crane;
            END_IF

        Crane_states_t#Reset_interconnect:
            _transit := FALSE;
            interconnect := FALSE;
            Timer1(IN := FALSE, PT := TIME#1.0ms);
            IF SliderMovedOut THEN
                _transit := TRUE;
                _state := Crane_states_t#Lower_Crane;
            END_IF

        Crane_states_t#Start_Crane:
            _transit := FALSE;
            CraneLower := FALSE;
            MagazinVacuumOff := TRUE;
            MagazinVacuumOn := FALSE;
            CraneTurnCounterclockwise := FALSE;
            CraneTurnClockwise := FALSE;
            StartVar := FALSE;
            StartCommandCrane := FALSE;
            IF (StartButtonMagazin = TRUE) THEN
                interconnectCraneStartCommand := TRUE;
            END_IF
            IF interconnectCraneStartCommand THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Init;
            END_IF

        Crane_states_t#Step0:
            _transit := FALSE;
            IF NOT MagazinCapacitiveSensor THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_Magazin;
            ELSEIF MagazinCapacitiveSensor THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_Magazin_Metallic;
            END_IF

        Crane_states_t#Suck_At_Stamp:
            _transit := FALSE;
            MagazinVacuumOn := TRUE;
            MagazinVacuumOff := FALSE;
            IF CraneSucked THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_At_Stamp;
            END_IF

        Crane_states_t#TimeDelay:
            _transit := FALSE;
            TimeDelay_Timer(IN := TRUE, PT := TimeDelay_Timer_Duration);
            TimeDelay_Timer_interconnect := TimeDelay_Timer.Q;
            IF TimeDelay_Timer_interconnect THEN
                _transit := TRUE;
                _state := Crane_states_t#Turn_Right;
            END_IF

        Crane_states_t#Turn_Right:
            _transit := FALSE;
            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Crane_states_t#Magazin_Stop;
            END_IF

        Crane_states_t#Turn_Right_Black:
            _transit := FALSE;
            CraneTurnClockwise := TRUE;
            CraneTurnCounterclockwise := FALSE;
            IF CraneOnMagazin THEN
                _transit := TRUE;
                _state := Crane_states_t#Magazin_Stop_Black;
            END_IF

        Crane_states_t#pause:
            _transit := FALSE;
            Timer1(IN := CraneUp, PT := Duration1);
            interconnect := Timer1.Q;
            IF interconnect THEN
                _transit := TRUE;
                _state := Crane_states_t#Reset_interconnect;
            END_IF

        Crane_states_t#release:
            _transit := FALSE;
            MagazinVacuumOff := TRUE;
            MagazinVacuumOn := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_Conveyor;
            END_IF

        Crane_states_t#release_Black:
            _transit := FALSE;
            MagazinVacuumOn := FALSE;
            MagazinVacuumOff := TRUE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Lift_Conveyor_Black;
            END_IF

        Crane_states_t#release_Workpiece:
            _transit := FALSE;
            MagazinVacuumOff := TRUE;
            MagazinVacuumOn := FALSE;
            IF TRUE THEN
                _transit := TRUE;
                _state := Crane_states_t#Crane_Go_Up;
            END_IF

            END_CASE
END_PROGRAM
